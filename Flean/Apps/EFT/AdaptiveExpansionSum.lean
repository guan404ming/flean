import Flean.Apps.Common.List
import Flean.Apps.EFT.ExpansionSum

/-!
# Flean.Apps.EFT.AdaptiveExpansionSum

Adaptive expansion distillation for arbitrary radix-2 inputs.

`fast2Sum` is exact only when the larger-magnitude operand is provided first.
This file removes the ordering precondition from `ExpansionSum` by performing
that local magnitude choice at every step.

The result is a stronger case study:

- no global sortedness assumption
- exactness for arbitrary representable input streams
- a verified backbone for Neumaier-style compensated accumulation and
  floating-point expansion arithmetic
-/

namespace Flean

/-- Choose the larger-magnitude operand as the leading term before applying
`fast2Sum`. This preserves exactness on arbitrary representable inputs. -/
noncomputable def adaptiveFast2Sum (fmt : FloatFormat) (a b : ℝ) : ℝ × ℝ :=
  if |b| ≤ |a| then fast2Sum fmt a b else fast2Sum fmt b a

/-- Repeated adaptive distillation over a list of inputs. -/
noncomputable def adaptiveDistill (fmt : FloatFormat) : ℝ → List ℝ → ℝ × List ℝ
  | s, [] => (s, [])
  | s, x :: xs =>
      let p := adaptiveFast2Sum fmt s x
      let q := adaptiveDistill fmt p.1 xs
      (q.1, p.2 :: q.2)

/-- Distillation from a whole list, starting at the first element. -/
noncomputable def adaptiveDistillList (fmt : FloatFormat) : List ℝ → ℝ × List ℝ
  | [] => (0, [])
  | x :: xs => adaptiveDistill fmt x xs

/-- Representability-only input condition for adaptive distillation. -/
def AdaptiveExpansionInput (fmt : FloatFormat) : List ℝ → Prop
  | [] => True
  | x :: xs => isRepresentable fmt x ∧ List.Forall (isRepresentable fmt) xs

theorem adaptiveFast2Sum_fst_repr (fmt : FloatFormat) (a b : ℝ) :
    isRepresentable fmt (adaptiveFast2Sum fmt a b).1 := by
  unfold adaptiveFast2Sum
  split_ifs <;> simp [fast2Sum_fst_repr]

theorem adaptiveFast2Sum_snd_repr (fmt : FloatFormat) (a b : ℝ) :
    isRepresentable fmt (adaptiveFast2Sum fmt a b).2 := by
  unfold adaptiveFast2Sum
  split_ifs <;> simp [fast2Sum_snd_repr]

/-- `adaptiveFast2Sum` is exact on arbitrary representable radix-2 inputs. -/
theorem adaptiveFast2Sum_exact {fmt : FloatFormat} (hβ : fmt.β = 2) {a b : ℝ}
    (ha : isRepresentable fmt a) (hb : isRepresentable fmt b) :
    let ⟨s, t⟩ := adaptiveFast2Sum fmt a b
    a + b = s + t := by
  unfold adaptiveFast2Sum
  by_cases hab : |b| ≤ |a|
  · simp [hab]
    simpa [add_comm] using fast2Sum_exact hβ ha hb hab
  · simp [hab]
    have hba : |a| ≤ |b| := by linarith
    simpa [add_comm] using fast2Sum_exact hβ hb ha hba

/-- The running head of adaptive distillation is representable. -/
theorem adaptiveDistill_head_repr {fmt : FloatFormat} {s : ℝ} {xs : List ℝ}
    (hs : isRepresentable fmt s) (hxs : List.Forall (isRepresentable fmt) xs) :
    isRepresentable fmt (adaptiveDistill fmt s xs).1 := by
  induction xs generalizing s with
  | nil =>
      simp [adaptiveDistill]
      exact hs
  | cons x xs ih =>
      have hsplit := listForall_cons hxs
      rcases hsplit with ⟨hx, htail⟩
      let p := adaptiveFast2Sum fmt s x
      have hp : isRepresentable fmt p.1 := by
        dsimp [p]
        exact adaptiveFast2Sum_fst_repr fmt s x
      simpa [adaptiveDistill, p] using ih hp htail

/-- Every residual emitted by adaptive distillation is representable. -/
theorem adaptiveDistill_residuals_repr {fmt : FloatFormat} {s : ℝ} {xs : List ℝ}
    (hs : isRepresentable fmt s) (hxs : List.Forall (isRepresentable fmt) xs) :
    List.Forall (isRepresentable fmt) (adaptiveDistill fmt s xs).2 := by
  induction xs generalizing s with
  | nil =>
      simp [adaptiveDistill]
  | cons x xs ih =>
      have hsplit := listForall_cons hxs
      rcases hsplit with ⟨hx, htail⟩
      let p := adaptiveFast2Sum fmt s x
      have hp : isRepresentable fmt p.1 := by
        dsimp [p]
        exact adaptiveFast2Sum_fst_repr fmt s x
      have hsnd : isRepresentable fmt p.2 := by
        dsimp [p]
        exact adaptiveFast2Sum_snd_repr fmt s x
      have hrest : List.Forall (isRepresentable fmt) (adaptiveDistill fmt p.1 xs).2 := by
        simpa [p] using ih hp htail
      simpa [List.Forall, adaptiveDistill, p] using And.intro hsnd hrest

/-- Main theorem: adaptive distillation preserves the exact sum of an arbitrary
representable input stream in radix 2. -/
theorem adaptiveDistill_exact {fmt : FloatFormat} (hβ : fmt.β = 2) {s : ℝ} {xs : List ℝ}
    (hs : isRepresentable fmt s) (hxs : List.Forall (isRepresentable fmt) xs) :
    expansionValue (adaptiveDistill fmt s xs) = s + xs.sum := by
  induction xs generalizing s with
  | nil =>
      simp [adaptiveDistill, expansionValue]
  | cons x xs ih =>
      have hsplit := listForall_cons hxs
      rcases hsplit with ⟨hx, htail⟩
      let p := adaptiveFast2Sum fmt s x
      have hp_exact : s + x = p.1 + p.2 := by
        dsimp [p]
        simpa using adaptiveFast2Sum_exact hβ hs hx
      have hp_repr : isRepresentable fmt p.1 := by
        dsimp [p]
        exact adaptiveFast2Sum_fst_repr fmt s x
      have hq_exact : expansionValue (adaptiveDistill fmt p.1 xs) = p.1 + xs.sum := by
        simpa [p] using ih hp_repr htail
      have hdist : expansionValue (adaptiveDistill fmt s (x :: xs)) =
          p.2 + expansionValue (adaptiveDistill fmt p.1 xs) := by
        simp [adaptiveDistill, expansionValue, p]
        ring
      calc
        expansionValue (adaptiveDistill fmt s (x :: xs))
            = p.2 + expansionValue (adaptiveDistill fmt p.1 xs) := hdist
        _ = p.2 + (p.1 + xs.sum) := by rw [hq_exact]
        _ = p.1 + p.2 + xs.sum := by ring
        _ = s + x + xs.sum := by linarith [hp_exact]
        _ = s + (x :: xs).sum := by
            simp
            ring

/-- List-level exactness theorem for arbitrary representable inputs. -/
theorem adaptiveDistillList_exact {fmt : FloatFormat} (hβ : fmt.β = 2) {xs : List ℝ}
    (hin : AdaptiveExpansionInput fmt xs) :
    expansionValue (adaptiveDistillList fmt xs) = xs.sum := by
  cases xs with
  | nil =>
      simp [adaptiveDistillList, expansionValue]
  | cons x xs =>
      rcases hin with ⟨hx, hxs⟩
      simpa [adaptiveDistillList, expansionValue] using adaptiveDistill_exact hβ hx hxs

/-- The adaptive expansion output is fully representable term-by-term. -/
theorem adaptiveDistillList_all_repr {fmt : FloatFormat} {xs : List ℝ}
    (hin : AdaptiveExpansionInput fmt xs) :
    match adaptiveDistillList fmt xs with
    | (h, es) => isRepresentable fmt h ∧ List.Forall (isRepresentable fmt) es := by
  cases xs with
  | nil =>
      simpa [adaptiveDistillList, List.Forall] using
        (show isRepresentable fmt 0 ∧ True from ⟨zero_isRepresentable fmt, trivial⟩)
  | cons x xs =>
      rcases hin with ⟨hx, hxs⟩
      simp [adaptiveDistillList]
      exact ⟨adaptiveDistill_head_repr hx hxs, adaptiveDistill_residuals_repr hx hxs⟩

theorem adaptiveDistillList_exact_binary64 {xs : List ℝ}
    (hin : AdaptiveExpansionInput binary64 xs) :
    expansionValue (adaptiveDistillList binary64 xs) = xs.sum :=
  adaptiveDistillList_exact (fmt := binary64) (by rfl) hin

theorem adaptiveDistillList_exact_binary32 {xs : List ℝ}
    (hin : AdaptiveExpansionInput binary32 xs) :
    expansionValue (adaptiveDistillList binary32 xs) = xs.sum :=
  adaptiveDistillList_exact (fmt := binary32) (by rfl) hin

end Flean
