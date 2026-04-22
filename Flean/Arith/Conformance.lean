import Flean.Arith.Correctness.SpecialCases
import Flean.Arith.Environment

/-!
# Flean.Arith.Conformance

Executable/spec-facing conformance lemmas for key IEEE 754 behavior.
-/

namespace Flean

theorem add_inf_opposite_invalid_conformance {spec : BinarySpec}
    (a b : FloatBits spec) (mode : RoundingMode)
    (ha : a.classify = .infinite) (hb : b.classify = .infinite) (hs : a.isNeg ≠ b.isNeg) :
    (a.add b mode).flags.invalidOperation = true ∧
    (a.add b mode).value = FloatBits.quietNaN spec :=
  add_inf_opposite_invalid (a := a) (b := b) mode ha hb hs

theorem mul_inf_zero_invalid_conformance {spec : BinarySpec}
    (a b : FloatBits spec) (mode : RoundingMode)
    (ha : a.classify = .infinite) (hb : b.classify = .zero) :
    (a.mul b mode).flags.invalidOperation = true ∧
    (a.mul b mode).value = FloatBits.quietNaN spec :=
  mul_inf_zero_invalid_left (a := a) (b := b) mode ha hb

theorem div_zero_zero_invalid_conformance {spec : BinarySpec}
    (a b : FloatBits spec) (mode : RoundingMode)
    (ha : a.classify = .zero) (hb : b.classify = .zero) :
    (a.div b mode).flags.invalidOperation = true ∧
    (a.div b mode).value = FloatBits.quietNaN spec :=
  div_zero_zero_invalid (a := a) (b := b) mode ha hb

theorem minimumResult_preferRight_nan_policy {spec : BinarySpec}
    (a b : FloatBits spec) (ha : a.classify = .nan) (hb : b.classify = .nan) :
    (a.minimumResultWithNaNPolicy b .preferRight).value = b.quietedNaN := by
  simp [FloatBits.minimumResultWithNaNPolicy, propagateNaNResultWithPolicy,
    chooseNaNOperandByPolicy, ha, hb]

theorem maximumResult_preferRight_nan_policy {spec : BinarySpec}
    (a b : FloatBits spec) (ha : a.classify = .nan) (hb : b.classify = .nan) :
    (a.maximumResultWithNaNPolicy b .preferRight).value = b.quietedNaN := by
  simp [FloatBits.maximumResultWithNaNPolicy, propagateNaNResultWithPolicy,
    chooseNaNOperandByPolicy, ha, hb]

theorem execWithEnv_traps_when_invalid_enabled {α : Type}
    (env : FPEnv) (state : FPState) (r : OpResult α)
    (hTrap : env.traps.invalidOperation = true)
    (hInv : r.flags.invalidOperation = true) :
    (execWithEnv env state r).trapped = true := by
  unfold execWithEnv
  simp [ExceptionFlags.trapMask, ExceptionFlags.any, RuntimeResult.trap, hTrap, hInv]

theorem execWithEnv_sticky_invalid {α : Type}
    (env : FPEnv) (state : FPState) (r : OpResult α)
    (hInv : r.flags.invalidOperation = true) :
    (execWithEnv env state r).state.flags.invalidOperation = true := by
  unfold execWithEnv FPState.raise
  have hRaised : (state.flags ++ r.flags).invalidOperation = true := by
    have hMerge :
        (state.flags ++ r.flags).invalidOperation =
          (state.flags.invalidOperation || r.flags.invalidOperation) := rfl
    rw [hMerge, hInv]
    simp
  by_cases hAny : (r.flags.trapMask env.traps).any
  · simp [hAny, RuntimeResult.trap, hRaised]
  · simp [hAny, RuntimeResult.ok, hRaised]

theorem addExec_traps_when_invalid {spec : BinarySpec}
    (env : FPEnv) (state : FPState) (a b : FloatBits spec)
    (hTrap : env.traps.invalidOperation = true)
    (hInv : (a.add b env.roundingMode).flags.invalidOperation = true) :
    (FloatBits.addExec env state a b).trapped = true := by
  unfold FloatBits.addExec
  exact execWithEnv_traps_when_invalid_enabled env state (a.add b env.roundingMode) hTrap hInv

theorem addExec_sticky_invalid_flag {spec : BinarySpec}
    (env : FPEnv) (state : FPState) (a b : FloatBits spec)
    (hInv : (a.add b env.roundingMode).flags.invalidOperation = true) :
    (FloatBits.addExec env state a b).state.flags.invalidOperation = true := by
  unfold FloatBits.addExec
  exact execWithEnv_sticky_invalid env state (a.add b env.roundingMode) hInv

end Flean
