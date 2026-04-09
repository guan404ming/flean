import Flean.Apps.EFT.TwoSum

/-!
# Flean.Apps.EFT.ExpansionSum

A case study in error-free transformed summation via floating-point expansions.

This file lifts the single-step `fast2Sum` proof to an entire summation pipeline.
Given a radix-2 format and a magnitude-ordered stream of representable inputs,
we repeatedly apply `fast2Sum` to obtain:

- a final rounded head term
- a list of residual terms

whose exact real sum equals the exact sum of the original inputs.

This is the core invariant behind compensated summation, floating-point
expansions, and robust geometric predicates in the style of Priest/Shewchuk.
It is a more substantial "paper case study" than a single local rounding lemma:
the proof composes a verified EFT kernel across an unbounded list computation.
-/

namespace Flean

/-- Repeatedly distill a stream of addends into a leading term plus residuals.

At each step we apply `fast2Sum` to the current leading term `s` and the next
input `x`, keep the new leading term, and append the residual to the expansion.
-/
noncomputable def distill (fmt : FloatFormat) : ℝ → List ℝ → ℝ × List ℝ
  | s, [] => (s, [])
  | s, x :: xs =>
      let p := fast2Sum fmt s x
      let q := distill fmt p.1 xs
      (q.1, p.2 :: q.2)

/-- The real value carried by an expansion `(head, residuals)`. -/
def expansionValue (p : ℝ × List ℝ) : ℝ :=
  p.1 + p.2.sum

/-- Local side condition needed to iterate `fast2Sum`:
each next addend is representable, no larger in magnitude than the current head,
and the tail satisfies the same condition after one `fast2Sum` step. -/
def DistillChain (fmt : FloatFormat) : ℝ → List ℝ → Prop
  | _, [] => True
  | s, x :: xs =>
      isRepresentable fmt x ∧
      |x| ≤ |s| ∧
      DistillChain fmt (fast2Sum fmt s x).1 xs

/-- Well-formed inputs for expansion distillation:
the first term is representable and every subsequent term satisfies the
`fast2Sum` side condition relative to the running head. -/
def ExpansionInput (fmt : FloatFormat) : List ℝ → Prop
  | [] => True
  | x :: xs => isRepresentable fmt x ∧ DistillChain fmt x xs

/-- Distillation starting from the first list element.
The empty list is represented by the zero expansion. -/
noncomputable def distillList (fmt : FloatFormat) : List ℝ → ℝ × List ℝ
  | [] => (0, [])
  | x :: xs => distill fmt x xs

theorem fast2Sum_fst_repr (fmt : FloatFormat) (a b : ℝ) :
    isRepresentable fmt (fast2Sum fmt a b).1 := by
  simp [fast2Sum]
  exact roundNNE_isRepresentable fmt (a + b)

theorem fast2Sum_snd_repr (fmt : FloatFormat) (a b : ℝ) :
    isRepresentable fmt (fast2Sum fmt a b).2 := by
  simp [fast2Sum]
  exact roundNNE_isRepresentable fmt (b - roundNNE fmt (roundNNE fmt (a + b) - a))

/-- The running head produced by distillation is always representable. -/
theorem distill_head_repr {fmt : FloatFormat} {s : ℝ} {xs : List ℝ}
    (hs : isRepresentable fmt s) (hchain : DistillChain fmt s xs) :
    isRepresentable fmt (distill fmt s xs).1 := by
  induction xs generalizing s with
  | nil =>
      simp [distill]
      exact hs
  | cons x xs ih =>
      rcases hchain with ⟨_, _, htail⟩
      let p := fast2Sum fmt s x
      have hp : isRepresentable fmt p.1 := by
        dsimp [p]
        exact fast2Sum_fst_repr fmt s x
      simpa [distill, p] using ih hp htail

/-- Every residual produced by distillation is representable. -/
theorem distill_residuals_repr {fmt : FloatFormat} {s : ℝ} {xs : List ℝ}
    (hs : isRepresentable fmt s) (hchain : DistillChain fmt s xs) :
    List.Forall (isRepresentable fmt) (distill fmt s xs).2 := by
  induction xs generalizing s with
  | nil =>
      simp [distill]
  | cons x xs ih =>
      rcases hchain with ⟨_, _, htail⟩
      let p := fast2Sum fmt s x
      have hp : isRepresentable fmt p.1 := by
        dsimp [p]
        exact fast2Sum_fst_repr fmt s x
      have htail_repr : List.Forall (isRepresentable fmt) (distill fmt p.1 xs).2 := by
        simpa [p] using ih hp htail
      have hsnd : isRepresentable fmt p.2 := by
        dsimp [p]
        exact fast2Sum_snd_repr fmt s x
      simpa [List.Forall, distill, p] using And.intro hsnd htail_repr

/-- Main case-study theorem:
distillation preserves the exact real sum of the inputs. -/
theorem distill_exact {fmt : FloatFormat} (hβ : fmt.β = 2) {s : ℝ} {xs : List ℝ}
    (hs : isRepresentable fmt s) (hchain : DistillChain fmt s xs) :
    expansionValue (distill fmt s xs) = s + xs.sum := by
  induction xs generalizing s with
  | nil =>
      simp [distill, expansionValue]
  | cons x xs ih =>
      rcases hchain with ⟨hx, hmag, htail⟩
      let p := fast2Sum fmt s x
      have hp_exact : s + x = p.1 + p.2 := by
        dsimp [p]
        simpa using fast2Sum_exact hβ hs hx hmag
      have hp_repr : isRepresentable fmt p.1 := by
        dsimp [p]
        exact fast2Sum_fst_repr fmt s x
      have hq_exact : expansionValue (distill fmt p.1 xs) = p.1 + xs.sum := by
        simpa [p] using ih hp_repr htail
      have hdist : expansionValue (distill fmt s (x :: xs)) =
          p.2 + expansionValue (distill fmt p.1 xs) := by
        simp [distill, expansionValue, p]
        ring
      calc
        expansionValue (distill fmt s (x :: xs))
            = p.2 + expansionValue (distill fmt p.1 xs) := hdist
        _ = p.2 + (p.1 + xs.sum) := by rw [hq_exact]
        _ = p.1 + p.2 + xs.sum := by ring
        _ = s + x + xs.sum := by linarith [hp_exact]
        _ = s + (x :: xs).sum := by
            simp
            ring

/-- List-level formulation of `distill_exact`. -/
theorem distillList_exact {fmt : FloatFormat} (hβ : fmt.β = 2) {xs : List ℝ}
    (hin : ExpansionInput fmt xs) :
    expansionValue (distillList fmt xs) = xs.sum := by
  cases xs with
  | nil =>
      simp [distillList, expansionValue]
  | cons x xs =>
      rcases hin with ⟨hx, hchain⟩
      simpa [distillList, expansionValue] using distill_exact hβ hx hchain

/-- Every term of the distillation output is representable. -/
theorem distillList_all_repr {fmt : FloatFormat} {xs : List ℝ}
    (hin : ExpansionInput fmt xs) :
    match distillList fmt xs with
    | (h, es) => isRepresentable fmt h ∧ List.Forall (isRepresentable fmt) es := by
  cases xs with
  | nil =>
      simpa [distillList, List.Forall] using
        (show isRepresentable fmt 0 ∧ True from ⟨zero_isRepresentable fmt, trivial⟩)
  | cons x xs =>
      rcases hin with ⟨hx, hchain⟩
      simp [distillList]
      exact ⟨distill_head_repr hx hchain, distill_residuals_repr hx hchain⟩

/-! ## Concrete binary64 corollaries -/

abbrev distillList_exact_binary64 {xs : List ℝ}
    (hin : ExpansionInput binary64 xs) :
    expansionValue (distillList binary64 xs) = xs.sum :=
  distillList_exact (fmt := binary64) (by rfl) hin

abbrev distillList_exact_binary32 {xs : List ℝ}
    (hin : ExpansionInput binary32 xs) :
    expansionValue (distillList binary32 xs) = xs.sum :=
  distillList_exact (fmt := binary32) (by rfl) hin

end Flean
