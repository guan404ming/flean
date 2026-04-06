import Flean.Apps.Common.List
import Flean.Apps.EFT.AdaptiveExpansionSum
import Flean.Arith.Predicates
import Flean.Bridge

/-!
# Flean.Apps.Compensated.Neumaier

Neumaier compensated summation under representability-only input assumptions.
-/

namespace Flean

/-- Neumaier step implemented via the already-verified `adaptiveFast2Sum`.
This removes Kahan's dominant-sum side condition by choosing the larger-magnitude
operand locally. -/
noncomputable def neumaierStep (fmt : FloatFormat) (s c x : ℝ) : ℝ × ℝ :=
  let p := adaptiveFast2Sum fmt s x
  (p.1, c - p.2)

/-- Real value represented by a Neumaier state. -/
def neumaierValue (sc : ℝ × ℝ) : ℝ :=
  sc.1 - sc.2

/-- Neumaier fold over a list of inputs. -/
noncomputable def neumaierFold (fmt : FloatFormat) : ℝ × ℝ → List ℝ → ℝ × ℝ
  | sc, [] => sc
  | sc, x :: xs => neumaierFold fmt (neumaierStep fmt sc.1 sc.2 x) xs

/-- User-facing Neumaier summation started from the first input and zero
compensation. It only requires representable inputs. -/
noncomputable def neumaierSum (fmt : FloatFormat) : List ℝ → ℝ × ℝ
  | [] => (0, 0)
  | x :: xs => neumaierFold fmt (x, 0) xs

/-- Practical Neumaier input contract: every input term is representable. -/
def NeumaierInput (fmt : FloatFormat) : List ℝ → Prop
  | [] => True
  | x :: xs => isRepresentable fmt x ∧ List.Forall (isRepresentable fmt) xs

theorem neumaierStep_exact {fmt : FloatFormat} (hβ : fmt.β = 2)
    {s c x : ℝ} (hs : isRepresentable fmt s) (hx : isRepresentable fmt x) :
    neumaierValue (neumaierStep fmt s c x) = neumaierValue (s, c) + x := by
  let p := adaptiveFast2Sum fmt s x
  have hp : s + x = p.1 + p.2 := by
    dsimp [p]
    simpa using adaptiveFast2Sum_exact hβ hs hx
  dsimp [neumaierStep, neumaierValue, p]
  linarith

theorem neumaierStep_head_repr {fmt : FloatFormat} {s c x : ℝ}
    (_hs : isRepresentable fmt s) (_hx : isRepresentable fmt x) :
    isRepresentable fmt (neumaierStep fmt s c x).1 := by
  unfold neumaierStep
  simpa using adaptiveFast2Sum_fst_repr fmt s x

theorem neumaierFold_exact {fmt : FloatFormat} (hβ : fmt.β = 2)
    {sc : ℝ × ℝ} {xs : List ℝ}
    (hs : isRepresentable fmt sc.1) (hxs : List.Forall (isRepresentable fmt) xs) :
    neumaierValue (neumaierFold fmt sc xs) = neumaierValue sc + xs.sum := by
  induction xs generalizing sc with
  | nil =>
      simp [neumaierFold, neumaierValue]
  | cons x xs ih =>
      rcases listForall_cons hxs with ⟨hx, htail⟩
      have hstep : neumaierValue (neumaierStep fmt sc.1 sc.2 x) = neumaierValue sc + x := by
        exact neumaierStep_exact hβ hs hx
      have hrepr : isRepresentable fmt (neumaierStep fmt sc.1 sc.2 x).1 := by
        exact neumaierStep_head_repr hs hx
      have htail_exact :
          neumaierValue (neumaierFold fmt (neumaierStep fmt sc.1 sc.2 x) xs) =
            neumaierValue (neumaierStep fmt sc.1 sc.2 x) + xs.sum := by
        exact ih hrepr htail
      calc
        neumaierValue (neumaierFold fmt sc (x :: xs))
            = neumaierValue (neumaierFold fmt (neumaierStep fmt sc.1 sc.2 x) xs) := by
                simp [neumaierFold]
        _ = neumaierValue (neumaierStep fmt sc.1 sc.2 x) + xs.sum := htail_exact
        _ = (neumaierValue sc + x) + xs.sum := by rw [hstep]
        _ = neumaierValue sc + (x :: xs).sum := by
              simp
              ring

theorem neumaierSum_exact {fmt : FloatFormat} (hβ : fmt.β = 2) {xs : List ℝ}
    (hin : NeumaierInput fmt xs) :
    neumaierValue (neumaierSum fmt xs) = xs.sum := by
  cases xs with
  | nil =>
      simp [neumaierSum, neumaierValue]
  | cons x xs =>
      rcases hin with ⟨hx, hxs⟩
      have hfold : neumaierValue (neumaierFold fmt (x, 0) xs) = neumaierValue (x, 0) + xs.sum :=
        neumaierFold_exact hβ hx hxs
      simpa [neumaierSum, neumaierValue] using hfold

theorem neumaierSum_tight_bound {fmt : FloatFormat} (hβ : fmt.β = 2) {xs : List ℝ}
    (hin : NeumaierInput fmt xs) :
    |xs.sum - (neumaierSum fmt xs).1| = |(neumaierSum fmt xs).2| := by
  have hexact := neumaierSum_exact hβ hin
  cases hsum : neumaierSum fmt xs with
  | mk s c =>
      dsimp [neumaierValue] at hexact
      rw [hsum] at hexact
      have hdiff : xs.sum - s = -c := by
        linarith
      have habs : |xs.sum - s| = |(-c)| := congrArg abs hdiff
      simpa [hsum, abs_neg] using habs

theorem neumaierSum_exact_binary64 {xs : List ℝ}
    (hin : NeumaierInput binary64 xs) :
    neumaierValue (neumaierSum binary64 xs) = xs.sum :=
  neumaierSum_exact (fmt := binary64) (by rfl) hin

theorem neumaierSum_exact_binary32 {xs : List ℝ}
    (hin : NeumaierInput binary32 xs) :
    neumaierValue (neumaierSum binary32 xs) = xs.sum :=
  neumaierSum_exact (fmt := binary32) (by rfl) hin

theorem neumaierSum_tight_bound_binary64 {xs : List ℝ}
    (hin : NeumaierInput binary64 xs) :
    |xs.sum - (neumaierSum binary64 xs).1| = |(neumaierSum binary64 xs).2| :=
  neumaierSum_tight_bound (fmt := binary64) (by rfl) hin

theorem neumaierSum_tight_bound_binary32 {xs : List ℝ}
    (hin : NeumaierInput binary32 xs) :
    |xs.sum - (neumaierSum binary32 xs).1| = |(neumaierSum binary32 xs).2| :=
  neumaierSum_tight_bound (fmt := binary32) (by rfl) hin

theorem FloatBits.toReal_isRepresentable_of_isFinite {spec : BinarySpec} (f : FloatBits spec)
    (hfin : f.isFinite = true) :
    isRepresentable spec.toFormat f.toReal := by
  unfold FloatBits.isFinite at hfin
  cases hclass : f.classify <;> simp [hclass] at hfin ⊢
  · exact f.toReal_isRepresentable (Or.inl hclass)
  · exact f.toReal_isRepresentable (Or.inr hclass)
  · simpa [FloatBits.toReal, hclass] using zero_isRepresentable spec.toFormat

theorem finiteFloatBits_map_toReal_repr {spec : BinarySpec} {xs : List (FloatBits spec)}
    (hfin : List.Forall (fun f => f.isFinite = true) xs) :
    List.Forall (isRepresentable spec.toFormat) (xs.map FloatBits.toReal) := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      rcases listForall_cons hfin with ⟨hx, hxs⟩
      simp [FloatBits.toReal_isRepresentable_of_isFinite, hx, ih hxs]

/-- User-facing bridge: any finite IEEE 754 input list maps to a real list
that automatically satisfies the `NeumaierInput` contract. -/
theorem neumaierInput_of_finiteFloatBits {spec : BinarySpec} {xs : List (FloatBits spec)}
    (hfin : List.Forall (fun f => f.isFinite = true) xs) :
    NeumaierInput spec.toFormat (xs.map FloatBits.toReal) := by
  cases xs with
  | nil =>
      simp [NeumaierInput]
  | cons x xs =>
      rcases listForall_cons hfin with ⟨hx, hxs⟩
      simp [NeumaierInput, FloatBits.toReal_isRepresentable_of_isFinite, hx,
        finiteFloatBits_map_toReal_repr hxs]

theorem neumaierSum_exact_of_finiteFloatBits {spec : BinarySpec} {xs : List (FloatBits spec)}
    (hfin : List.Forall (fun f => f.isFinite = true) xs) :
    neumaierValue (neumaierSum spec.toFormat (xs.map FloatBits.toReal)) =
      (xs.map FloatBits.toReal).sum :=
  neumaierSum_exact (fmt := spec.toFormat) (by rfl) (neumaierInput_of_finiteFloatBits hfin)

theorem neumaierSum_tight_bound_of_finiteFloatBits {spec : BinarySpec}
    {xs : List (FloatBits spec)}
    (hfin : List.Forall (fun f => f.isFinite = true) xs) :
    |(xs.map FloatBits.toReal).sum -
        (neumaierSum spec.toFormat (xs.map FloatBits.toReal)).1| =
      |(neumaierSum spec.toFormat (xs.map FloatBits.toReal)).2| :=
  neumaierSum_tight_bound (fmt := spec.toFormat) (by rfl)
    (neumaierInput_of_finiteFloatBits hfin)

end Flean
