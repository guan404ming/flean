import Flean.Arith.Conversions
import Flean.Arith.Compare
import Flean.Arith.FMA
import Flean.Arith.MiscOps
import Flean.Arith.RoundToIntegral
import Flean.Arith.Sqrt

/-!
# Flean.Arith.Environment

IEEE 754-like runtime environment:
- dynamic rounding mode / tininess mode / NaN policy
- sticky status flags
- trap-enable mask
- execution wrappers for arithmetic/comparison operations
-/

namespace Flean

/-- Per-flag trap enable mask. -/
structure TrapEnables where
  invalidOperation : Bool := false
  divisionByZero : Bool := false
  overflow : Bool := false
  underflow : Bool := false
  inexact : Bool := false
  deriving DecidableEq, Repr

/-- Runtime floating-point environment. -/
structure FPEnv where
  roundingMode : RoundingMode := .roundNearestTiesToEven
  tininess : TininessDetectionMode := .beforeRounding
  nanPolicy : NaNPropagationPolicy := .preferLeft
  traps : TrapEnables := {}
  deriving DecidableEq, Repr

/-- Sticky runtime status flags. -/
structure FPState where
  flags : ExceptionFlags := {}
  deriving DecidableEq, Repr

/-- Runtime result:
    `value = none` when a trap is taken. -/
structure RuntimeResult (α : Type) where
  value : Option α
  state : FPState
  trapped : Bool := false
  trapFlags : ExceptionFlags := {}
  deriving Repr

def FPState.raise (s : FPState) (flags : ExceptionFlags) : FPState :=
  { flags := s.flags ++ flags }

def ExceptionFlags.trapMask (flags : ExceptionFlags) (traps : TrapEnables) : ExceptionFlags :=
  { invalidOperation := flags.invalidOperation && traps.invalidOperation
    divisionByZero := flags.divisionByZero && traps.divisionByZero
    overflow := flags.overflow && traps.overflow
    underflow := flags.underflow && traps.underflow
    inexact := flags.inexact && traps.inexact }

def RuntimeResult.ok {α : Type} (x : α) (state : FPState) : RuntimeResult α :=
  { value := some x, state := state }

def RuntimeResult.trap {α : Type} (state : FPState) (trapFlags : ExceptionFlags) : RuntimeResult α :=
  { value := none, state := state, trapped := true, trapFlags := trapFlags }

/-- Apply operation flags to state; return trapped result when enabled traps fire. -/
def execWithEnv {α : Type} (env : FPEnv) (state : FPState) (r : OpResult α) : RuntimeResult α :=
  let state' := state.raise r.flags
  let trapFlags := r.flags.trapMask env.traps
  if trapFlags.any then
    RuntimeResult.trap state' trapFlags
  else
    RuntimeResult.ok r.value state'

namespace FloatBits

noncomputable def addExec {spec : BinarySpec}
    (env : FPEnv) (state : FPState) (a b : FloatBits spec) : RuntimeResult (FloatBits spec) :=
  execWithEnv env state (a.add b env.roundingMode)

noncomputable def mulExec {spec : BinarySpec}
    (env : FPEnv) (state : FPState) (a b : FloatBits spec) : RuntimeResult (FloatBits spec) :=
  execWithEnv env state (a.mul b env.roundingMode)

noncomputable def divExec {spec : BinarySpec}
    (env : FPEnv) (state : FPState) (a b : FloatBits spec) : RuntimeResult (FloatBits spec) :=
  execWithEnv env state (a.div b env.roundingMode)

noncomputable def sqrtExec {spec : BinarySpec}
    (env : FPEnv) (state : FPState) (a : FloatBits spec) : RuntimeResult (FloatBits spec) :=
  execWithEnv env state (a.sqrtWithTininess env.roundingMode env.tininess)

noncomputable def fmaExec {spec : BinarySpec}
    (env : FPEnv) (state : FPState) (a b c : FloatBits spec) : RuntimeResult (FloatBits spec) :=
  execWithEnv env state (a.fmaWithTininess b c env.roundingMode env.tininess)

noncomputable def castExec {srcSpec dstSpec : BinarySpec}
    (env : FPEnv) (state : FPState) (a : FloatBits srcSpec) : RuntimeResult (FloatBits dstSpec) :=
  execWithEnv env state (a.castWithTininess (dstSpec := dstSpec) env.roundingMode env.tininess)

noncomputable def roundToIntegralExec {spec : BinarySpec}
    (env : FPEnv) (state : FPState) (a : FloatBits spec) : RuntimeResult (FloatBits spec) :=
  execWithEnv env state (a.roundToIntegral env.roundingMode)

noncomputable def quantizeExec {spec : BinarySpec}
    (env : FPEnv) (state : FPState) (x y : FloatBits spec) : RuntimeResult (FloatBits spec) :=
  execWithEnv env state (x.quantizeResultWithTininess y env.roundingMode env.tininess)

noncomputable def remainderExec {spec : BinarySpec}
    (env : FPEnv) (state : FPState) (x y : FloatBits spec) : RuntimeResult (FloatBits spec) :=
  execWithEnv env state (x.remainderResult y env.roundingMode)

noncomputable def minimumExec {spec : BinarySpec}
    (env : FPEnv) (state : FPState) (a b : FloatBits spec) : RuntimeResult (FloatBits spec) :=
  execWithEnv env state (a.minimumResultWithNaNPolicy b env.nanPolicy)

noncomputable def maximumExec {spec : BinarySpec}
    (env : FPEnv) (state : FPState) (a b : FloatBits spec) : RuntimeResult (FloatBits spec) :=
  execWithEnv env state (a.maximumResultWithNaNPolicy b env.nanPolicy)

noncomputable def minimumMagnitudeExec {spec : BinarySpec}
    (env : FPEnv) (state : FPState) (a b : FloatBits spec) : RuntimeResult (FloatBits spec) :=
  execWithEnv env state (a.minimumMagnitudeResultWithNaNPolicy b env.nanPolicy)

noncomputable def maximumMagnitudeExec {spec : BinarySpec}
    (env : FPEnv) (state : FPState) (a b : FloatBits spec) : RuntimeResult (FloatBits spec) :=
  execWithEnv env state (a.maximumMagnitudeResultWithNaNPolicy b env.nanPolicy)

noncomputable def compareEqExec {spec : BinarySpec}
    (env : FPEnv) (state : FPState) (a b : FloatBits spec) : RuntimeResult Bool :=
  let _ := env
  execWithEnv env state (a.eqResult b)

noncomputable def compareLtExec {spec : BinarySpec}
    (env : FPEnv) (state : FPState) (a b : FloatBits spec) : RuntimeResult Bool :=
  let _ := env
  execWithEnv env state (a.ltResult b)

noncomputable def compareLeExec {spec : BinarySpec}
    (env : FPEnv) (state : FPState) (a b : FloatBits spec) : RuntimeResult Bool :=
  let _ := env
  execWithEnv env state (a.leResult b)

end FloatBits

end Flean
