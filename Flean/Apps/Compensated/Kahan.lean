import Flean.Apps.Common.List
import Flean.Apps.EFT.ExpansionSum

/-!
# Flean.Apps.Compensated.Kahan

Single-step and fold-level verification of Kahan compensated summation.
-/

namespace Flean

/-- One Kahan compensated summation step. -/
noncomputable def kahanStep (fmt : FloatFormat) (s c x : ℝ) : ℝ × ℝ :=
  let y := roundNNE fmt (x - c)
  let t := roundNNE fmt (s + y)
  let c' := roundNNE fmt ((t - s) - y)
  (t, c')

/-- The exact real value represented by a Kahan state `(s, c)` is `s - c`. -/
def kahanValue (sc : ℝ × ℝ) : ℝ :=
  sc.1 - sc.2

/-- Kahan fold over a list of inputs. -/
noncomputable def kahanFold (fmt : FloatFormat) : ℝ × ℝ → List ℝ → ℝ × ℝ
  | sc, [] => sc
  | sc, x :: xs => kahanFold fmt (kahanStep fmt sc.1 sc.2 x) xs

/-- Local proof obligations needed to make the Kahan step exact. -/
def KahanChain (fmt : FloatFormat) : (ℝ × ℝ) → List ℝ → Prop
  | _, [] => True
  | sc, x :: xs =>
      isRepresentable fmt sc.1 ∧
      isRepresentable fmt sc.2 ∧
      isRepresentable fmt x ∧
      isRepresentable fmt (x - sc.2) ∧
      |x - sc.2| ≤ |sc.1| ∧
      KahanChain fmt (kahanStep fmt sc.1 sc.2 x) xs

/-- User-facing list input condition for Kahan summation started from the
first list element with zero compensation. -/
def KahanInput (fmt : FloatFormat) : List ℝ → Prop
  | [] => True
  | x :: xs => isRepresentable fmt x ∧ KahanChain fmt (x, 0) xs

/-- Stronger, compositional sufficient condition for `KahanInput`:
every new addend is no larger than the current exact running sum, and every
running prefix sum remains representable. This keeps Kahan on the exact
zero-compensation path. -/
def KahanPrefixChain (fmt : FloatFormat) : ℝ → List ℝ → Prop
  | s, [] => isRepresentable fmt s
  | s, x :: xs =>
      isRepresentable fmt s ∧
      isRepresentable fmt x ∧
      |x| ≤ |s| ∧
      isRepresentable fmt (s + x) ∧
      KahanPrefixChain fmt (s + x) xs

/-- List-level version of `KahanPrefixChain`, started from the first input. -/
def KahanPrefixInput (fmt : FloatFormat) : List ℝ → Prop
  | [] => True
  | x :: xs => isRepresentable fmt x ∧ KahanPrefixChain fmt x xs

/-- Running prefix sums remain representable, without yet imposing the Kahan
magnitude side condition. -/
def RunningSumChain (fmt : FloatFormat) : ℝ → List ℝ → Prop
  | s, [] => isRepresentable fmt s
  | s, x :: xs =>
      isRepresentable fmt x ∧
      isRepresentable fmt (s + x) ∧
      RunningSumChain fmt (s + x) xs

/-- User-facing running-sum representability condition started from the first
input. -/
def RunningSumInput (fmt : FloatFormat) : List ℝ → Prop
  | [] => True
  | x :: xs => isRepresentable fmt x ∧ RunningSumChain fmt x xs

/-- Nonincreasing real stream. -/
def Nonincreasing : List ℝ → Prop
  | [] => True
  | [_] => True
  | x :: y :: xs => y ≤ x ∧ Nonincreasing (y :: xs)

/-- Easy-to-check sufficient condition for Kahan exactness:
the stream is nonnegative, nonincreasing, and every running prefix sum is
representable. -/
def KahanMonotoneChain (fmt : FloatFormat) : ℝ → ℝ → List ℝ → Prop
  | s, prev, [] => isRepresentable fmt s ∧ 0 ≤ prev ∧ prev ≤ s
  | s, prev, x :: xs =>
      isRepresentable fmt s ∧
      0 ≤ prev ∧
      prev ≤ s ∧
      isRepresentable fmt x ∧
      0 ≤ x ∧
      x ≤ prev ∧
      isRepresentable fmt (s + x) ∧
      KahanMonotoneChain fmt (s + x) x xs

/-- List-level version of `KahanMonotoneChain`, started from the first input. -/
def KahanMonotoneInput (fmt : FloatFormat) : List ℝ → Prop
  | [] => True
  | x :: xs => isRepresentable fmt x ∧ 0 ≤ x ∧ KahanMonotoneChain fmt x x xs

/-- Kahan summation started from the first element with zero compensation.
The empty list returns `(0,0)`. -/
noncomputable def kahanSum (fmt : FloatFormat) : List ℝ → ℝ × ℝ
  | [] => (0, 0)
  | x :: xs => kahanFold fmt (x, 0) xs

/-- A posteriori one-step value-error budget for Kahan. It charges the rounding
of the corrected addend `x - c` and the rounding of the compensation update. -/
noncomputable def kahanStepFallbackBudget (fmt : FloatFormat) (s c x : ℝ) : ℝ :=
  let y := roundNNE fmt (x - c)
  let t := roundNNE fmt (s + y)
  bpow fmt (cexp fmt (x - c)) / 2 + bpow fmt (cexp fmt ((t - s) - y)) / 2

/-- Recursive a posteriori budget for a Kahan fold started from an arbitrary
state. This accumulates the local fallback budgets actually encountered along
the computed run. -/
noncomputable def kahanFoldFallbackBudget (fmt : FloatFormat) :
    ℝ × ℝ → List ℝ → ℝ
  | _, [] => 0
  | sc, x :: xs =>
      kahanStepFallbackBudget fmt sc.1 sc.2 x +
        kahanFoldFallbackBudget fmt (kahanStep fmt sc.1 sc.2 x) xs

/-- User-facing fallback budget for `kahanSum`. -/
noncomputable def kahanSumFallbackBudget (fmt : FloatFormat) : List ℝ → ℝ
  | [] => 0
  | x :: xs => kahanFoldFallbackBudget fmt (x, 0) xs

theorem kahanStep_zero_of_repr_sum {fmt : FloatFormat} {s x : ℝ}
    (_hs : isRepresentable fmt s) (hx : isRepresentable fmt x)
    (hsx : isRepresentable fmt (s + x)) :
    kahanStep fmt s 0 x = (s + x, 0) := by
  have hy : roundNNE fmt (x - 0) = x := by
    simpa using roundNNE_repr_fixed fmt hx
  have ht : roundNNE fmt (s + x) = s + x := by
    simpa using roundNNE_repr_fixed fmt hsx
  dsimp [kahanStep]
  rw [hy]
  change (roundNNE fmt (s + x), roundNNE fmt ((roundNNE fmt (s + x) - s) - x)) = (s + x, 0)
  rw [ht]
  have hzero : ((s + x) - s) - x = 0 := by ring
  rw [hzero, roundNNE_zero]

/-- With zero initial compensation and the usual `fast2Sum` side condition,
the Kahan step is exactly the `fast2Sum` head together with the negated
residual. -/
theorem kahanStep_zero_eq_fast2Sum_neg {fmt : FloatFormat} (hβ : fmt.β = 2)
    {s x : ℝ} (hs : isRepresentable fmt s) (hx : isRepresentable fmt x)
    (hmag : |x| ≤ |s|) :
    let p := fast2Sum fmt s x
    kahanStep fmt s 0 x = (p.1, -p.2) := by
  let hi := roundNNE fmt (s + x)
  let bp := roundNNE fmt (hi - s)
  have hy : roundNNE fmt (x - 0) = x := by
    simpa using roundNNE_repr_fixed fmt hx
  have hbp : bp = hi - s := by
    dsimp [bp, hi]
    simpa using fast2Sum_sub_exact hβ hs hx hmag
  have herr_repr : isRepresentable fmt (x - (hi - s)) := by
    dsimp [hi]
    simpa using fast2Sum_err_repr hβ hs hx hmag
  have hcomp : roundNNE fmt ((hi - s) - x) = -(x - (hi - s)) := by
    have hneg_repr : isRepresentable fmt (-(x - (hi - s))) :=
      neg_isRepresentable herr_repr
    have : (hi - s) - x = -(x - (hi - s)) := by ring
    rw [this, roundNNE_repr_fixed fmt hneg_repr]
  have herr_fix : roundNNE fmt (x - (hi - s)) = x - (hi - s) := by
    exact roundNNE_repr_fixed fmt herr_repr
  dsimp [kahanStep]
  rw [hy]
  change (roundNNE fmt (s + x), roundNNE fmt ((roundNNE fmt (s + x) - s) - x)) =
      ((fast2Sum fmt s x).1, -((fast2Sum fmt s x).2))
  simp [fast2Sum, hi, bp, hbp, hcomp, herr_fix]

/-- Generalized single-step exactness: if the corrected addend `x - c` is
representable and no larger than `s`, the Kahan step is just `fast2Sum`
applied to `(s, x-c)`, with negated residual. -/
theorem kahanStep_eq_fast2Sum_neg {fmt : FloatFormat} (hβ : fmt.β = 2)
    {s c x : ℝ} (hs : isRepresentable fmt s) (_hc : isRepresentable fmt c)
    (_hx : isRepresentable fmt x) (hxc : isRepresentable fmt (x - c))
    (hmag : |x - c| ≤ |s|) :
    let y := x - c
    let p := fast2Sum fmt s y
    kahanStep fmt s c x = (p.1, -p.2) := by
  let y := x - c
  let hi := roundNNE fmt (s + y)
  let bp := roundNNE fmt (hi - s)
  have hy : roundNNE fmt (x - c) = y := by
    dsimp [y]
    exact roundNNE_repr_fixed fmt hxc
  have hbp : bp = hi - s := by
    dsimp [bp, hi, y]
    simpa using fast2Sum_sub_exact hβ hs hxc hmag
  have herr_repr : isRepresentable fmt (y - (hi - s)) := by
    dsimp [hi, y]
    simpa using fast2Sum_err_repr hβ hs hxc hmag
  have hcomp : roundNNE fmt ((hi - s) - y) = -(y - (hi - s)) := by
    have hneg_repr : isRepresentable fmt (-(y - (hi - s))) :=
      neg_isRepresentable herr_repr
    have : (hi - s) - y = -(y - (hi - s)) := by ring
    rw [this, roundNNE_repr_fixed fmt hneg_repr]
  have herr_fix : roundNNE fmt (y - (hi - s)) = y - (hi - s) := by
    exact roundNNE_repr_fixed fmt herr_repr
  dsimp [kahanStep]
  rw [hy]
  change (roundNNE fmt (s + y), roundNNE fmt ((roundNNE fmt (s + y) - s) - y)) =
      ((fast2Sum fmt s y).1, -((fast2Sum fmt s y).2))
  simp [fast2Sum, hi, bp, hbp, hcomp, herr_fix]

/-- Exact conservation law for one Kahan step under the local exactness
side condition. -/
theorem kahanStep_exact {fmt : FloatFormat} (hβ : fmt.β = 2)
    {s c x : ℝ} (hs : isRepresentable fmt s) (hc : isRepresentable fmt c)
    (hx : isRepresentable fmt x) (hxc : isRepresentable fmt (x - c))
    (hmag : |x - c| ≤ |s|) :
    let ⟨s', c'⟩ := kahanStep fmt s c x
    s + (x - c) = s' - c' := by
  let y := x - c
  let p := fast2Sum fmt s y
  have hk : kahanStep fmt s c x = (p.1, -p.2) :=
    kahanStep_eq_fast2Sum_neg hβ hs hc hx hxc hmag
  have hp : s + y = p.1 + p.2 := by
    dsimp [p, y]
    simpa using fast2Sum_exact hβ hs hxc hmag
  rw [hk]
  simp [hp, y]

/-- Representability of both outputs of one Kahan step under the local
exactness side condition. -/
theorem kahanStep_repr {fmt : FloatFormat} (hβ : fmt.β = 2)
    {s c x : ℝ} (hs : isRepresentable fmt s) (hc : isRepresentable fmt c)
    (hx : isRepresentable fmt x) (hxc : isRepresentable fmt (x - c))
    (hmag : |x - c| ≤ |s|) :
    let ⟨s', c'⟩ := kahanStep fmt s c x
    isRepresentable fmt s' ∧ isRepresentable fmt c' := by
  let y := x - c
  let p := fast2Sum fmt s y
  have hk : kahanStep fmt s c x = (p.1, -p.2) :=
    kahanStep_eq_fast2Sum_neg hβ hs hc hx hxc hmag
  rw [hk]
  exact ⟨fast2Sum_fst_repr fmt s y, neg_isRepresentable (fast2Sum_snd_repr fmt s y)⟩

/-- The Kahan step exactly preserves the real sum when started from zero
compensation under the local `fast2Sum` side condition. -/
theorem kahanStep_zero_exact {fmt : FloatFormat} (hβ : fmt.β = 2)
    {s x : ℝ} (hs : isRepresentable fmt s) (hx : isRepresentable fmt x)
    (hmag : |x| ≤ |s|) :
    let ⟨s', c'⟩ := kahanStep fmt s 0 x
    s + x = s' - c' := by
  let p := fast2Sum fmt s x
  have hk : kahanStep fmt s 0 x = (p.1, -p.2) :=
    kahanStep_zero_eq_fast2Sum_neg hβ hs hx hmag
  have hp : s + x = p.1 + p.2 := by
    dsimp [p]
    simpa using fast2Sum_exact hβ hs hx hmag
  rw [hk]
  simp [hp]

/-- Both outputs of the zero-compensation Kahan step are representable. -/
theorem kahanStep_zero_repr {fmt : FloatFormat} (hβ : fmt.β = 2)
    {s x : ℝ} (hs : isRepresentable fmt s) (hx : isRepresentable fmt x)
    (hmag : |x| ≤ |s|) :
    let ⟨s', c'⟩ := kahanStep fmt s 0 x
    isRepresentable fmt s' ∧ isRepresentable fmt c' := by
  let p := fast2Sum fmt s x
  have hk : kahanStep fmt s 0 x = (p.1, -p.2) :=
    kahanStep_zero_eq_fast2Sum_neg hβ hs hx hmag
  rw [hk]
  exact ⟨fast2Sum_fst_repr fmt s x, neg_isRepresentable (fast2Sum_snd_repr fmt s x)⟩

theorem kahanStep_zero_exact_binary64 {s x : ℝ}
    (hs : isRepresentable binary64 s) (hx : isRepresentable binary64 x)
    (hmag : |x| ≤ |s|) :
    let ⟨s', c'⟩ := kahanStep binary64 s 0 x
    s + x = s' - c' :=
  kahanStep_zero_exact (fmt := binary64) (by rfl) hs hx hmag

theorem kahanStep_zero_exact_binary32 {s x : ℝ}
    (hs : isRepresentable binary32 s) (hx : isRepresentable binary32 x)
    (hmag : |x| ≤ |s|) :
    let ⟨s', c'⟩ := kahanStep binary32 s 0 x
    s + x = s' - c' :=
  kahanStep_zero_exact (fmt := binary32) (by rfl) hs hx hmag

/-- A posteriori one-step fallback bound: even when the exact `fast2Sum` side
condition does not hold, the Kahan state value changes by at most the sum of
the corrected-addend rounding error and the compensation rounding error. -/
theorem kahanStep_fallback_value_error_le {fmt : FloatFormat} {s c x : ℝ} :
    |kahanValue (kahanStep fmt s c x) - (kahanValue (s, c) + x)| ≤
      kahanStepFallbackBudget fmt s c x := by
  let y := roundNNE fmt (x - c)
  let t := roundNNE fmt (s + y)
  let c' := roundNNE fmt ((t - s) - y)
  have hy :
      |(x - c) - y| ≤ bpow fmt (cexp fmt (x - c)) / 2 := by
    dsimp [y]
    simpa [abs_sub_comm] using roundNNE_sub_abs_le fmt (x - c)
  have hc :
      |((t - s) - y) - c'| ≤ bpow fmt (cexp fmt ((t - s) - y)) / 2 := by
    dsimp [c']
    simpa [abs_sub_comm] using roundNNE_sub_abs_le fmt ((t - s) - y)
  have hdecomp :
      kahanValue (kahanStep fmt s c x) - (kahanValue (s, c) + x) =
        ((y - (x - c)) - (c' - ((t - s) - y))) := by
    dsimp [kahanStep, kahanValue, y, t, c']
    ring
  rw [hdecomp]
  have htri :
      |(y - (x - c)) - (c' - ((t - s) - y))|
        ≤ |y - (x - c)| + |((t - s) - y) - c'| := by
    simpa [sub_eq_add_neg, abs_neg, abs_sub_comm] using
      (abs_add_le (y - (x - c)) (-(c' - ((t - s) - y)) : ℝ))
  have hy' : |y - (x - c)| = |(x - c) - y| := by rw [abs_sub_comm]
  dsimp [kahanStepFallbackBudget, y, t]
  rw [hy'] at htri
  linarith

/-- Global exactness of the Kahan fold under the stepwise exactness side
condition. The exact accumulated real value is always `s_final - c_final`. -/
theorem kahanFold_exact {fmt : FloatFormat} (hβ : fmt.β = 2)
    {sc : ℝ × ℝ} {xs : List ℝ} (hchain : KahanChain fmt sc xs) :
    kahanValue (kahanFold fmt sc xs) = kahanValue sc + xs.sum := by
  induction xs generalizing sc with
  | nil =>
      simp [kahanFold, kahanValue]
  | cons x xs ih =>
      rcases hchain with ⟨hs, hc, hx, hxc, hmag, htail⟩
      have hstep : kahanValue (kahanStep fmt sc.1 sc.2 x) = kahanValue sc + x := by
        have h := kahanStep_exact hβ hs hc hx hxc hmag
        dsimp [kahanValue] at h ⊢
        linarith
      have htail_exact :
          kahanValue (kahanFold fmt (kahanStep fmt sc.1 sc.2 x) xs) =
            kahanValue (kahanStep fmt sc.1 sc.2 x) + xs.sum := by
        exact ih htail
      calc
        kahanValue (kahanFold fmt sc (x :: xs))
            = kahanValue (kahanFold fmt (kahanStep fmt sc.1 sc.2 x) xs) := by
                simp [kahanFold]
        _ = kahanValue (kahanStep fmt sc.1 sc.2 x) + xs.sum := htail_exact
        _ = (kahanValue sc + x) + xs.sum := by rw [hstep]
        _ = kahanValue sc + (x :: xs).sum := by
              simp
              ring

/-- Tight forward error identity for the running sum component of Kahan fold:
the whole forward error is exactly the magnitude of the final compensation. -/
theorem kahanFold_tight_bound {fmt : FloatFormat} (hβ : fmt.β = 2)
    {sc : ℝ × ℝ} {xs : List ℝ} (hchain : KahanChain fmt sc xs) :
    |(kahanValue sc + xs.sum) - (kahanFold fmt sc xs).1| = |(kahanFold fmt sc xs).2| := by
  have hexact := kahanFold_exact hβ hchain
  let out := kahanFold fmt sc xs
  have hout : kahanValue out = kahanValue sc + xs.sum := hexact
  have hdiff : (kahanValue sc + xs.sum) - out.1 = -out.2 := by
    dsimp [kahanValue] at hout ⊢
    linarith
  rw [show kahanFold fmt sc xs = out from by rfl]
  have habs : |(kahanValue sc + xs.sum) - out.1| = |(-out.2)| := congrArg abs hdiff
  rw [abs_neg] at habs
  exact habs

/-- Zero-state specialization of `kahanFold_exact`. -/
theorem kahanFold_zero_exact {fmt : FloatFormat} (hβ : fmt.β = 2)
    {xs : List ℝ} (hchain : KahanChain fmt (0, 0) xs) :
    kahanValue (kahanFold fmt (0, 0) xs) = xs.sum := by
  simpa [kahanValue] using kahanFold_exact hβ hchain

/-- Tight forward error from the exact list sum to the final rounded sum,
for a Kahan fold started at `(0,0)`. -/
theorem kahanFold_zero_tight_bound {fmt : FloatFormat} (hβ : fmt.β = 2)
    {xs : List ℝ} (hchain : KahanChain fmt (0, 0) xs) :
    |xs.sum - (kahanFold fmt (0, 0) xs).1| = |(kahanFold fmt (0, 0) xs).2| := by
  simpa [kahanValue] using kahanFold_tight_bound hβ hchain

theorem kahanFold_zero_tight_bound_binary64 {xs : List ℝ}
    (hchain : KahanChain binary64 (0, 0) xs) :
    |xs.sum - (kahanFold binary64 (0, 0) xs).1| = |(kahanFold binary64 (0, 0) xs).2| :=
  kahanFold_zero_tight_bound (fmt := binary64) (by rfl) hchain

theorem kahanFold_zero_tight_bound_binary32 {xs : List ℝ}
    (hchain : KahanChain binary32 (0, 0) xs) :
    |xs.sum - (kahanFold binary32 (0, 0) xs).1| = |(kahanFold binary32 (0, 0) xs).2| :=
  kahanFold_zero_tight_bound (fmt := binary32) (by rfl) hchain

/-- Exactness theorem for the user-facing `kahanSum` API. -/
theorem kahanSum_exact {fmt : FloatFormat} (hβ : fmt.β = 2) {xs : List ℝ}
    (hin : KahanInput fmt xs) :
    kahanValue (kahanSum fmt xs) = xs.sum := by
  cases xs with
  | nil =>
      simp [kahanSum, kahanValue]
  | cons x xs =>
      rcases hin with ⟨_, hchain⟩
      have hfold : kahanValue (kahanFold fmt (x, 0) xs) = kahanValue (x, 0) + xs.sum :=
        kahanFold_exact hβ hchain
      simpa [kahanSum, kahanValue] using hfold

/-- Tight forward error bound for the user-facing `kahanSum` API. -/
theorem kahanSum_tight_bound {fmt : FloatFormat} (hβ : fmt.β = 2) {xs : List ℝ}
    (hin : KahanInput fmt xs) :
    |xs.sum - (kahanSum fmt xs).1| = |(kahanSum fmt xs).2| := by
  cases xs with
  | nil =>
      simp [kahanSum]
  | cons x xs =>
      rcases hin with ⟨_, hchain⟩
      have hfold :
          |(kahanValue (x, 0) + xs.sum) - (kahanFold fmt (x, 0) xs).1|
            = |(kahanFold fmt (x, 0) xs).2| :=
        kahanFold_tight_bound hβ hchain
      simpa [kahanSum, kahanValue] using hfold

theorem kahanSum_exact_binary64 {xs : List ℝ}
    (hin : KahanInput binary64 xs) :
    kahanValue (kahanSum binary64 xs) = xs.sum :=
  kahanSum_exact (fmt := binary64) (by rfl) hin

theorem kahanSum_exact_binary32 {xs : List ℝ}
    (hin : KahanInput binary32 xs) :
    kahanValue (kahanSum binary32 xs) = xs.sum :=
  kahanSum_exact (fmt := binary32) (by rfl) hin

theorem kahanSum_tight_bound_binary64 {xs : List ℝ}
    (hin : KahanInput binary64 xs) :
    |xs.sum - (kahanSum binary64 xs).1| = |(kahanSum binary64 xs).2| :=
  kahanSum_tight_bound (fmt := binary64) (by rfl) hin

theorem kahanSum_tight_bound_binary32 {xs : List ℝ}
    (hin : KahanInput binary32 xs) :
    |xs.sum - (kahanSum binary32 xs).1| = |(kahanSum binary32 xs).2| :=
  kahanSum_tight_bound (fmt := binary32) (by rfl) hin

/-- General fallback bound for the exact state value tracked by a Kahan fold.
This bound requires no exactness contract; it only sums the local rounding
budgets encountered along the computed run. -/
theorem kahanFold_fallback_value_error_le {fmt : FloatFormat}
    {sc : ℝ × ℝ} {xs : List ℝ} :
    |kahanValue (kahanFold fmt sc xs) - (kahanValue sc + xs.sum)| ≤
      kahanFoldFallbackBudget fmt sc xs := by
  induction xs generalizing sc with
  | nil =>
      simp [kahanFold, kahanFoldFallbackBudget, kahanValue]
  | cons x xs ih =>
      let sc' := kahanStep fmt sc.1 sc.2 x
      have hstep :
          |kahanValue sc' - (kahanValue sc + x)| ≤
            kahanStepFallbackBudget fmt sc.1 sc.2 x := by
        exact kahanStep_fallback_value_error_le (fmt := fmt) (s := sc.1) (c := sc.2) (x := x)
      have htail :
          |kahanValue (kahanFold fmt sc' xs) - (kahanValue sc' + xs.sum)| ≤
            kahanFoldFallbackBudget fmt sc' xs := by
        exact ih
      have hsplit :
          kahanValue (kahanFold fmt sc' xs) - (kahanValue sc + (x :: xs).sum) =
            (kahanValue (kahanFold fmt sc' xs) - (kahanValue sc' + xs.sum)) +
            (kahanValue sc' - (kahanValue sc + x)) := by
        simp [sc', kahanValue]
        ring
      have hmain :
          |kahanValue (kahanFold fmt sc' xs) - (kahanValue sc + (x :: xs).sum)|
            ≤ |kahanValue (kahanFold fmt sc' xs) - (kahanValue sc' + xs.sum)| +
              |kahanValue sc' - (kahanValue sc + x)| := by
        rw [hsplit]
        exact abs_add_le _ _
      have := add_le_add htail hstep
      simpa [kahanFold, kahanFoldFallbackBudget, sc', add_comm, add_left_comm, add_assoc] using
        le_trans hmain this

/-- User-facing fallback bound for the exact Kahan state value. -/
theorem kahanSum_fallback_value_error_le {fmt : FloatFormat} {xs : List ℝ} :
    |kahanValue (kahanSum fmt xs) - xs.sum| ≤ kahanSumFallbackBudget fmt xs := by
  cases xs with
  | nil =>
      simp [kahanSum, kahanSumFallbackBudget, kahanValue]
  | cons x xs =>
      simpa [kahanSum, kahanSumFallbackBudget, kahanValue] using
        (kahanFold_fallback_value_error_le (fmt := fmt) (sc := (x, 0)) (xs := xs))

/-- User-facing fallback bound for the running-sum component returned by
`kahanSum`. The total forward error is bounded by the a posteriori value-error
budget plus the magnitude of the final compensation. -/
theorem kahanSum_fallback_head_error_le {fmt : FloatFormat} {xs : List ℝ} :
    |xs.sum - (kahanSum fmt xs).1| ≤ kahanSumFallbackBudget fmt xs + |(kahanSum fmt xs).2| := by
  have hval := kahanSum_fallback_value_error_le (fmt := fmt) (xs := xs)
  cases hsum : kahanSum fmt xs with
  | mk s c =>
      rw [hsum] at hval
      simp at hval ⊢
      have hdecomp : xs.sum - s = (xs.sum - (s - c)) - c := by ring
      rw [hdecomp]
      have htri : |(xs.sum - (s - c)) - c| ≤ |xs.sum - (s - c)| + |c| := by
        simpa [sub_eq_add_neg] using abs_add_le (xs.sum - (s - c)) (-c)
      dsimp [kahanValue] at hval
      have hval' : |xs.sum - (s - c)| ≤ kahanSumFallbackBudget fmt xs := by
        simpa [abs_sub_comm] using hval
      calc
        |(xs.sum - (s - c)) - c| ≤ |xs.sum - (s - c)| + |c| := htri
        _ ≤ kahanSumFallbackBudget fmt xs + |c| := by gcongr

/-- Paper-facing fallback corollary: once the a posteriori Kahan fallback
budget is discharged by a standard `C * eps * sumAbs` estimate, the exact-state
value error immediately takes that form. -/
theorem kahanSum_fallback_value_error_le_of_C_eps_sumAbs
    {fmt : FloatFormat} {xs : List ℝ} {C : ℝ}
    (hbudget : kahanSumFallbackBudget fmt xs ≤ C * machineEpsilon fmt * sumAbs xs) :
    |kahanValue (kahanSum fmt xs) - xs.sum| ≤ C * machineEpsilon fmt * sumAbs xs :=
  le_trans (kahanSum_fallback_value_error_le (fmt := fmt) (xs := xs)) hbudget

/-- Paper-facing fallback corollary for the running-sum component returned by
`kahanSum`. -/
theorem kahanSum_fallback_head_error_le_of_C_eps_sumAbs
    {fmt : FloatFormat} {xs : List ℝ} {C : ℝ}
    (hbudget : kahanSumFallbackBudget fmt xs ≤ C * machineEpsilon fmt * sumAbs xs) :
    |xs.sum - (kahanSum fmt xs).1| ≤
      C * machineEpsilon fmt * sumAbs xs + |(kahanSum fmt xs).2| := by
  calc
    |xs.sum - (kahanSum fmt xs).1|
        ≤ kahanSumFallbackBudget fmt xs + |(kahanSum fmt xs).2| :=
          kahanSum_fallback_head_error_le (fmt := fmt) (xs := xs)
    _ ≤ C * machineEpsilon fmt * sumAbs xs + |(kahanSum fmt xs).2| := by
          gcongr

theorem kahanChain_of_prefixChain {fmt : FloatFormat} {s : ℝ} {xs : List ℝ}
    (hchain : KahanPrefixChain fmt s xs) :
    KahanChain fmt (s, 0) xs := by
  induction xs generalizing s with
  | nil =>
      simp [KahanChain]
  | cons x xs ih =>
      rcases hchain with ⟨hs, hx, hmag, hsx, htail⟩
      have hstep : kahanStep fmt s 0 x = (s + x, 0) :=
        kahanStep_zero_of_repr_sum hs hx hsx
      refine ⟨hs, zero_isRepresentable fmt, hx, ?_, ?_, ?_⟩
      · simpa using hx
      · simpa using hmag
      · simpa [hstep] using ih htail

theorem kahanInput_of_prefixInput {fmt : FloatFormat} {xs : List ℝ}
    (hin : KahanPrefixInput fmt xs) :
    KahanInput fmt xs := by
  cases xs with
  | nil =>
      simp [KahanInput]
  | cons x xs =>
      rcases hin with ⟨hx, hchain⟩
      exact ⟨hx, kahanChain_of_prefixChain hchain⟩

theorem kahanPrefixChain_of_monotoneChain {fmt : FloatFormat}
    {s prev : ℝ} {xs : List ℝ}
    (hin : KahanMonotoneChain fmt s prev xs) :
    KahanPrefixChain fmt s xs := by
  induction xs generalizing s prev with
  | nil =>
      exact hin.1
  | cons x xs ih =>
      rcases hin with ⟨hs, hprev0, hprev_le, hx, hx0, hxprev, hsx, htail⟩
      refine ⟨hs, hx, ?_, hsx, ?_⟩
      · rw [abs_of_nonneg hx0, abs_of_nonneg (le_trans hprev0 hprev_le)]
        linarith
      · exact ih htail

theorem kahanPrefixInput_of_monotoneInput {fmt : FloatFormat} {xs : List ℝ}
    (hin : KahanMonotoneInput fmt xs) :
    KahanPrefixInput fmt xs := by
  cases xs with
  | nil =>
      simp [KahanPrefixInput]
  | cons x xs =>
      rcases hin with ⟨hx, _, hchain⟩
      exact ⟨hx, kahanPrefixChain_of_monotoneChain hchain⟩

theorem kahanInput_of_monotoneInput {fmt : FloatFormat} {xs : List ℝ}
    (hin : KahanMonotoneInput fmt xs) :
    KahanInput fmt xs :=
  kahanInput_of_prefixInput (kahanPrefixInput_of_monotoneInput hin)

theorem kahanPrefixChain_sum_repr {fmt : FloatFormat} {s : ℝ} {xs : List ℝ}
    (hchain : KahanPrefixChain fmt s xs) :
    isRepresentable fmt (s + xs.sum) := by
  induction xs generalizing s with
  | nil =>
      simpa [KahanPrefixChain] using hchain
  | cons x xs ih =>
      rcases hchain with ⟨_, _, _, hsx, htail⟩
      have hrepr : isRepresentable fmt ((s + x) + xs.sum) := ih htail
      simpa [List.sum_cons, add_assoc] using hrepr

theorem kahanPrefixInput_sum_repr {fmt : FloatFormat} {xs : List ℝ}
    (hin : KahanPrefixInput fmt xs) :
    isRepresentable fmt xs.sum := by
  cases xs with
  | nil =>
      simpa using zero_isRepresentable fmt
  | cons x xs =>
      rcases hin with ⟨_, hchain⟩
      simpa [List.sum_cons] using kahanPrefixChain_sum_repr hchain

theorem kahanMonotoneChain_of_runningSumChain {fmt : FloatFormat}
    {s prev : ℝ} {xs : List ℝ}
    (hs : isRepresentable fmt s)
    (hrun : RunningSumChain fmt s xs)
    (hmono : Nonincreasing (prev :: xs))
    (hnonneg : ∀ x ∈ prev :: xs, 0 ≤ x)
    (hprev_le : prev ≤ s) :
    KahanMonotoneChain fmt s prev xs := by
  induction xs generalizing s prev with
  | nil =>
      refine ⟨?_, hnonneg prev (by simp), hprev_le⟩
      simpa [RunningSumChain] using hrun
  | cons x xs ih =>
      rcases hrun with ⟨hx, hsx, htail⟩
      cases xs with
      | nil =>
          have hxp : x ≤ prev := by
            simpa [Nonincreasing] using hmono.1
          have hprev0 : 0 ≤ prev := hnonneg prev (by simp)
          have hx0 : 0 ≤ x := hnonneg x (by simp)
          refine ⟨hs, hprev0, hprev_le, hx, hx0, hxp, hsx, ?_⟩
          · refine ⟨?_, hx0, by linarith⟩
            simpa [RunningSumChain] using htail
      | cons y ys =>
          have hmono_step : x ≤ prev := by
            simpa [Nonincreasing] using hmono.1
          have hmono_tail : Nonincreasing (x :: y :: ys) := by
            simpa [Nonincreasing] using hmono.2
          have hnonneg_tail : ∀ z ∈ x :: y :: ys, 0 ≤ z := by
            intro z hz
            exact hnonneg z (by simp [hz])
          have hprev0 : 0 ≤ prev := hnonneg prev (by simp)
          have hx0 : 0 ≤ x := hnonneg x (by simp)
          refine ⟨hs, hprev0, hprev_le, hx, hx0, hmono_step, hsx, ?_⟩
          · exact ih hsx htail hmono_tail hnonneg_tail (by linarith)

theorem kahanMonotoneInput_of_runningSums_of_nonincreasing {fmt : FloatFormat}
    {xs : List ℝ}
    (hrun : RunningSumInput fmt xs)
    (hmono : Nonincreasing xs)
    (hnonneg : ∀ x ∈ xs, 0 ≤ x) :
    KahanMonotoneInput fmt xs := by
  cases xs with
  | nil =>
      simp [KahanMonotoneInput]
  | cons x xs =>
      rcases hrun with ⟨hx, htail⟩
      have hx0 : 0 ≤ x := hnonneg x (by simp)
      refine ⟨hx, hx0, ?_⟩
      exact kahanMonotoneChain_of_runningSumChain hx htail hmono hnonneg (by linarith)

theorem kahanPrefixInput_of_runningSums_of_nonincreasing {fmt : FloatFormat}
    {xs : List ℝ}
    (hrun : RunningSumInput fmt xs)
    (hmono : Nonincreasing xs)
    (hnonneg : ∀ x ∈ xs, 0 ≤ x) :
    KahanPrefixInput fmt xs :=
  kahanPrefixInput_of_monotoneInput
    (kahanMonotoneInput_of_runningSums_of_nonincreasing hrun hmono hnonneg)

theorem kahanInput_of_runningSums_of_nonincreasing {fmt : FloatFormat}
    {xs : List ℝ}
    (hrun : RunningSumInput fmt xs)
    (hmono : Nonincreasing xs)
    (hnonneg : ∀ x ∈ xs, 0 ≤ x) :
    KahanInput fmt xs :=
  kahanInput_of_prefixInput
    (kahanPrefixInput_of_runningSums_of_nonincreasing hrun hmono hnonneg)

theorem kahanFold_zero_eq_sum_zero_of_prefixChain {fmt : FloatFormat} {s : ℝ} {xs : List ℝ}
    (hchain : KahanPrefixChain fmt s xs) :
    kahanFold fmt (s, 0) xs = (s + xs.sum, 0) := by
  induction xs generalizing s with
  | nil =>
      simp [kahanFold]
  | cons x xs ih =>
      rcases hchain with ⟨hs, hx, _, hsx, htail⟩
      have hstep : kahanStep fmt s 0 x = (s + x, 0) :=
        kahanStep_zero_of_repr_sum hs hx hsx
      calc
        kahanFold fmt (s, 0) (x :: xs)
            = kahanFold fmt (s + x, 0) xs := by simp [kahanFold, hstep]
        _ = ((s + x) + xs.sum, 0) := ih htail
        _ = (s + (x :: xs).sum, 0) := by simp [List.sum_cons, add_assoc]

theorem kahanSum_eq_sum_zero_of_prefixInput {fmt : FloatFormat} {xs : List ℝ}
    (hin : KahanPrefixInput fmt xs) :
    kahanSum fmt xs = (xs.sum, 0) := by
  cases xs with
  | nil =>
      simp [kahanSum]
  | cons x xs =>
      rcases hin with ⟨_, hchain⟩
      simpa [kahanSum, List.sum_cons] using kahanFold_zero_eq_sum_zero_of_prefixChain hchain

end Flean
