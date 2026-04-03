import Flean.Core.CastChain

/-!
# Flean.Core.ChainError

General n-step cast chain error decomposition.

The key lemma `chain_error_triangle` decomposes the error of any
nested rounding composition into a sum of individual rounding errors
via the triangle inequality. This enables compositional reasoning
about arbitrary-length cast chains.
-/

namespace Flean

/-! ## General chain decomposition lemma -/

/-- One-step peeling: the error of round(y) relative to x decomposes as
    |x - round(y)| ≤ |x - y| + |y - round(y)|.
    This is the fundamental building block for chain decomposition. -/
theorem chain_peel (fmt : FloatFormat) (x y : ℝ) :
    |x - roundNNE fmt y| ≤ |x - y| + |y - roundNNE fmt y| := by
  calc |x - roundNNE fmt y|
      = |(x - y) + (y - roundNNE fmt y)| := by congr 1; ring
    _ ≤ |x - y| + |y - roundNNE fmt y| := abs_add_le _ _

/-- Symmetric form: |x - round(y)| ≤ |x - y| + |roundNNE error of y|. -/
theorem chain_peel' (fmt : FloatFormat) (x y : ℝ) :
    |x - roundNNE fmt y| ≤ |x - y| + bpow fmt (cexp fmt y) / 2 :=
  le_trans (chain_peel fmt x y) (by linarith [roundNNE_sub_abs_le fmt y])

/-! ## Two-step chain -/

/-- Two-step chain: |x - R1(R2(x))| ≤ |x - R2(x)| + |R2(x) - R1(R2(x))|. -/
theorem chain_error_2 (fmt1 fmt2 : FloatFormat) (x : ℝ) :
    |x - roundNNE fmt1 (roundNNE fmt2 x)| ≤
      |x - roundNNE fmt2 x| + |roundNNE fmt2 x - roundNNE fmt1 (roundNNE fmt2 x)| :=
  chain_peel fmt1 x (roundNNE fmt2 x)

/-- Two-step chain with ULP bounds. -/
theorem chain_error_2_ulp (fmt1 fmt2 : FloatFormat) (x : ℝ) :
    |x - roundNNE fmt1 (roundNNE fmt2 x)| ≤
      bpow fmt2 (cexp fmt2 x) / 2 +
      bpow fmt1 (cexp fmt1 (roundNNE fmt2 x)) / 2 := by
  calc |x - roundNNE fmt1 (roundNNE fmt2 x)|
      ≤ |x - roundNNE fmt2 x| + |roundNNE fmt2 x - roundNNE fmt1 (roundNNE fmt2 x)| :=
        chain_error_2 fmt1 fmt2 x
    _ ≤ bpow fmt2 (cexp fmt2 x) / 2 + bpow fmt1 (cexp fmt1 (roundNNE fmt2 x)) / 2 := by
        linarith [roundNNE_sub_abs_le fmt2 x, roundNNE_sub_abs_le fmt1 (roundNNE fmt2 x)]

/-! ## Three-step chain -/

/-- Three-step chain decomposition. -/
theorem chain_error_3 (fmt1 fmt2 fmt3 : FloatFormat) (x : ℝ) :
    |x - roundNNE fmt1 (roundNNE fmt2 (roundNNE fmt3 x))| ≤
      |x - roundNNE fmt3 x| +
      |roundNNE fmt3 x - roundNNE fmt2 (roundNNE fmt3 x)| +
      |roundNNE fmt2 (roundNNE fmt3 x) -
        roundNNE fmt1 (roundNNE fmt2 (roundNNE fmt3 x))| := by
  set y := roundNNE fmt3 x
  set z := roundNNE fmt2 y
  calc |x - roundNNE fmt1 z|
      ≤ |x - z| + |z - roundNNE fmt1 z| := chain_peel fmt1 x z
    _ ≤ (|x - y| + |y - z|) + |z - roundNNE fmt1 z| := by
        linarith [chain_peel fmt2 x y]
    _ = _ := by ring

/-- Three-step chain with ULP bounds. -/
theorem chain_error_3_ulp (fmt1 fmt2 fmt3 : FloatFormat) (x : ℝ) :
    |x - roundNNE fmt1 (roundNNE fmt2 (roundNNE fmt3 x))| ≤
      bpow fmt3 (cexp fmt3 x) / 2 +
      bpow fmt2 (cexp fmt2 (roundNNE fmt3 x)) / 2 +
      bpow fmt1 (cexp fmt1 (roundNNE fmt2 (roundNNE fmt3 x))) / 2 := by
  calc |x - roundNNE fmt1 (roundNNE fmt2 (roundNNE fmt3 x))|
      ≤ |x - roundNNE fmt3 x| +
        |roundNNE fmt3 x - roundNNE fmt2 (roundNNE fmt3 x)| +
        |roundNNE fmt2 (roundNNE fmt3 x) -
          roundNNE fmt1 (roundNNE fmt2 (roundNNE fmt3 x))| :=
        chain_error_3 fmt1 fmt2 fmt3 x
    _ ≤ _ := by
        linarith [roundNNE_sub_abs_le fmt3 x,
                  roundNNE_sub_abs_le fmt2 (roundNNE fmt3 x),
                  roundNNE_sub_abs_le fmt1 (roundNNE fmt2 (roundNNE fmt3 x))]

/-! ## Four-step chain -/

/-- Four-step chain decomposition. -/
theorem chain_error_4 (fmt1 fmt2 fmt3 fmt4 : FloatFormat) (x : ℝ) :
    |x - roundNNE fmt1 (roundNNE fmt2 (roundNNE fmt3 (roundNNE fmt4 x)))| ≤
      |x - roundNNE fmt4 x| +
      |roundNNE fmt4 x - roundNNE fmt3 (roundNNE fmt4 x)| +
      |roundNNE fmt3 (roundNNE fmt4 x) -
        roundNNE fmt2 (roundNNE fmt3 (roundNNE fmt4 x))| +
      |roundNNE fmt2 (roundNNE fmt3 (roundNNE fmt4 x)) -
        roundNNE fmt1 (roundNNE fmt2 (roundNNE fmt3 (roundNNE fmt4 x)))| := by
  set a := roundNNE fmt4 x
  set b := roundNNE fmt3 a
  set c := roundNNE fmt2 b
  calc |x - roundNNE fmt1 c|
      ≤ |x - c| + |c - roundNNE fmt1 c| := chain_peel fmt1 x c
    _ ≤ (|x - b| + |b - c|) + |c - roundNNE fmt1 c| := by
        linarith [chain_peel fmt2 x b]
    _ ≤ ((|x - a| + |a - b|) + |b - c|) + |c - roundNNE fmt1 c| := by
        linarith [chain_peel fmt3 x a]
    _ = _ := by ring

/-! ## General n-step chain via lists -/

/-- Apply a list of rounding functions in sequence (innermost first). -/
noncomputable def roundChain (fmts : List FloatFormat) (x : ℝ) : ℝ :=
  fmts.foldl (fun acc fmt => roundNNE fmt acc) x

theorem roundChain_nil (x : ℝ) : roundChain [] x = x := rfl

theorem roundChain_cons (fmt : FloatFormat) (fmts : List FloatFormat) (x : ℝ) :
    roundChain (fmt :: fmts) x = roundChain fmts (roundNNE fmt x) := by
  unfold roundChain; simp [List.foldl]

theorem roundChain_singleton (fmt : FloatFormat) (x : ℝ) :
    roundChain [fmt] x = roundNNE fmt x := rfl

/-! ## General n-step error bound by induction

The total error of an n-step chain is bounded by the sum of individual
rounding errors. We define the "error sum" using the intermediate values
of the chain, then prove the bound by induction on the format list. -/

/-- The intermediate values of a chain: partial foldl results. -/
noncomputable def chainIntermediates (fmts : List FloatFormat) (x : ℝ) : List ℝ :=
  match fmts with
  | [] => []
  | fmt :: rest =>
    let y := roundNNE fmt x
    y :: chainIntermediates rest y

/-- Sum of individual rounding errors along a chain. -/
noncomputable def chainErrorSum (fmts : List FloatFormat) (x : ℝ) : ℝ :=
  match fmts with
  | [] => 0
  | fmt :: rest =>
    let y := roundNNE fmt x
    |x - y| + chainErrorSum rest y

theorem chainErrorSum_nonneg (fmts : List FloatFormat) (x : ℝ) :
    0 ≤ chainErrorSum fmts x := by
  induction fmts generalizing x with
  | nil => simp [chainErrorSum]
  | cons fmt rest ih => simp [chainErrorSum]; linarith [abs_nonneg (x - roundNNE fmt x), ih (roundNNE fmt x)]

/-- General n-step chain error bound: the total error is at most the sum
    of individual rounding errors. Proof by induction. -/
theorem roundChain_error_le_sum (fmts : List FloatFormat) (x : ℝ) :
    |x - roundChain fmts x| ≤ chainErrorSum fmts x := by
  induction fmts generalizing x with
  | nil => simp [roundChain, chainErrorSum]
  | cons fmt rest ih =>
    rw [roundChain_cons]; simp only [chainErrorSum]
    set y := roundNNE fmt x
    calc |x - roundChain rest y|
        = |(x - y) + (y - roundChain rest y)| := by congr 1; ring
      _ ≤ |x - y| + |y - roundChain rest y| := abs_add_le _ _
      _ ≤ |x - y| + chainErrorSum rest y := by linarith [ih y]

/-- Sum of bpow/2 at each step (using intermediate values for cexp). -/
noncomputable def chainBpowSum (fmts : List FloatFormat) (x : ℝ) : ℝ :=
  match fmts with
  | [] => 0
  | fmt :: rest =>
    bpow fmt (cexp fmt x) / 2 + chainBpowSum rest (roundNNE fmt x)

/-- The chain error sum is bounded by the sum of bpow/2 at each step. -/
theorem chainErrorSum_le_bpow_sum (fmts : List FloatFormat) (x : ℝ) :
    chainErrorSum fmts x ≤ chainBpowSum fmts x := by
  induction fmts generalizing x with
  | nil => simp [chainErrorSum, chainBpowSum]
  | cons fmt rest ih =>
    simp only [chainErrorSum, chainBpowSum]
    linarith [roundNNE_sub_abs_le fmt x, ih (roundNNE fmt x)]

/-- The main general theorem: total chain error ≤ sum of ULP/2 at each step.
    This works for ANY chain length. -/
theorem roundChain_error_le_bpow_sum (fmts : List FloatFormat) (x : ℝ) :
    |x - roundChain fmts x| ≤ chainBpowSum fmts x :=
  le_trans (roundChain_error_le_sum fmts x) (chainErrorSum_le_bpow_sum fmts x)

/-! ## Idempotence for chains of the same format -/

/-- A chain of the same format collapses to a single rounding. -/
theorem roundChain_same (fmt : FloatFormat) (n : ℕ) (x : ℝ) :
    roundChain (List.replicate (n + 1) fmt) x = roundNNE fmt x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, roundChain_cons]
    exact (ih (roundNNE fmt x)).trans (roundNNE_idempotent fmt x)

end Flean
