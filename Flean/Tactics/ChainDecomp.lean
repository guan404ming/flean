import Flean.Core.CastChain
import Lean

/-!
# Flean.Tactics.ChainDecomp

Recursive cast chain decomposition tactic.

`flean_chain_bound` automatically decomposes any nested roundNNE chain
into a sum of individual rounding errors using the triangle inequality.
Works for chains of length 1 through 4.

## Algorithm

Given `|x - roundNNE fmt1 (roundNNE fmt2 (... (roundNNE fmtN x)))| ≤ bound`:
1. Match the nesting depth
2. Apply the corresponding chain_error_N lemma
3. Bound each segment by roundNNE_sub_abs_le (ULP bound)
4. Compose with linarith
-/

namespace Flean

open Lean Meta Elab Tactic

/-- `flean_chain_bound` automatically bounds the error of a cast chain.
    Handles chains of length 1-4 by applying the corresponding decomposition
    lemma and bounding each step by the ULP error. -/
syntax (name := fleanChainBound) "flean_chain_bound" : tactic

@[tactic fleanChainBound]
def evalFleanChainBound : Tactic := fun _ => do
  let tactics ← `(tactic|
    first
    -- General n-step: roundChain form
    | exact roundChain_error_le_bpow_sum _ _
    -- 1-step
    | exact roundNNE_sub_abs_le _ _
    -- 2-step ULP bound
    | exact chain_error_2_ulp _ _ _
    -- 3-step ULP bound
    | exact chain_error_3_ulp _ _ _ _
    -- 4-step: decompose then bound each piece
    | (linarith [chain_error_4 _ _ _ _ _, roundNNE_sub_abs_le _ _,
                 roundNNE_sub_abs_le _ _, roundNNE_sub_abs_le _ _,
                 roundNNE_sub_abs_le _ _])
    -- 2-step triangle (looser form)
    | (linarith [chain_peel _ _ _, roundNNE_sub_abs_le _ _, roundNNE_sub_abs_le _ _])
    -- 3-step triangle
    | (linarith [chain_error_3 _ _ _ _, roundNNE_sub_abs_le _ _,
                 roundNNE_sub_abs_le _ _, roundNNE_sub_abs_le _ _])
    -- General error sum
    | exact roundChain_error_le_sum _ _
    -- Relative error
    | exact roundNNE_error_rel _ ‹_›
    -- Monotonicity
    | (exact finer_format_smaller_error _ _)
    -- Dominance
    | (exact cast_chain_error_dominance _ _)
  )
  evalTactic tactics

/-! ## Demos -/

-- 1-step chain
example (x : ℝ) :
    |x - roundNNE binary32 x| ≤ bpow binary32 (cexp binary32 x) / 2 := by
  flean_chain_bound

-- 2-step chain: abstract formats (direct lemma application)
example (fmt1 fmt2 : FloatFormat) (x : ℝ) :
    |x - roundNNE fmt1 (roundNNE fmt2 x)| ≤
      bpow fmt2 (cexp fmt2 x) / 2 +
      bpow fmt1 (cexp fmt1 (roundNNE fmt2 x)) / 2 :=
  chain_error_2_ulp fmt1 fmt2 x

-- 3-step chain: abstract formats (direct lemma application)
example (fmt1 fmt2 fmt3 : FloatFormat) (x : ℝ) :
    |x - roundNNE fmt1 (roundNNE fmt2 (roundNNE fmt3 x))| ≤
      bpow fmt3 (cexp fmt3 x) / 2 +
      bpow fmt2 (cexp fmt2 (roundNNE fmt3 x)) / 2 +
      bpow fmt1 (cexp fmt1 (roundNNE fmt2 (roundNNE fmt3 x))) / 2 :=
  chain_error_3_ulp fmt1 fmt2 fmt3 x

-- 2-step concrete: uses the lemma directly (avoids format unification timeout)
example (x : ℝ) :
    |x - roundNNE binary16 (roundNNE binary32 x)| ≤
      bpow binary32 (cexp binary32 x) / 2 +
      bpow binary16 (cexp binary16 (roundNNE binary32 x)) / 2 :=
  chain_error_2_ulp binary16 binary32 x

-- Demo: general n-step chain via roundChain (works for ANY length)
example (fmts : List FloatFormat) (x : ℝ) :
    |x - roundChain fmts x| ≤ chainBpowSum fmts x := by
  flean_chain_bound

-- Demo: 5-step chain via roundChain
example (x : ℝ) :
    |x - roundChain [binary64, binary32, binary16, binary32, binary16] x| ≤
      chainBpowSum [binary64, binary32, binary16, binary32, binary16] x := by
  flean_chain_bound

end Flean
