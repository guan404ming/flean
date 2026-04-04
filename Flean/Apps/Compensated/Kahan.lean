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

/-- Kahan summation started from the first element with zero compensation.
The empty list returns `(0,0)`. -/
noncomputable def kahanSum (fmt : FloatFormat) : List ℝ → ℝ × ℝ
  | [] => (0, 0)
  | x :: xs => kahanFold fmt (x, 0) xs

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

end Flean
