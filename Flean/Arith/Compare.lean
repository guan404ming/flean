import Flean.Binary.Defs
import Flean.Arith.Exceptions

/-!
# Flean.Arith.Compare

IEEE 754 comparison operations for floating-point numbers.
-/

namespace Flean

/-- Select a NaN payload source by policy (comparison module variant). -/
def chooseNaNOperandByPolicy {spec : BinarySpec}
    (policy : NaNPropagationPolicy) (f1 f2 : FloatBits spec) : FloatBits spec :=
  match policy with
  | .preferLeft => f1
  | .preferRight => f2
  | .preferLargerPayload =>
      if f1.nanPayload.toNat ≥ f2.nanPayload.toNat then f1 else f2

/-- NaN propagation helper for comparison-like operations that return a float.
    If either operand is NaN, returns a quieted NaN and sets invalid only for signaling NaNs.
    When both are NaN, the payload source follows `policy`. -/
def propagateNaNResultWithPolicy {spec : BinarySpec}
    (policy : NaNPropagationPolicy) (f1 f2 : FloatBits spec) : OpResult (FloatBits spec) :=
  if f1.classify == .nan || f2.classify == .nan then
    let picked :=
      if f1.classify == .nan && f2.classify == .nan then
        chooseNaNOperandByPolicy policy f1 f2
      else if f1.classify == .nan then
        f1
      else
        f2
    { value := picked.quietedNaN
      flags := { invalidOperation := f1.isSignalingNaN || f2.isSignalingNaN } }
  else
    { value := FloatBits.quietNaN spec }

def propagateNaNResult {spec : BinarySpec}
    (f1 f2 : FloatBits spec) : OpResult (FloatBits spec) :=
  propagateNaNResultWithPolicy .preferLeft f1 f2

/-- IEEE 754 equality predicate with invalid flag on signaling NaNs. -/
def FloatBits.eqResult {spec : BinarySpec} (f1 f2 : FloatBits spec) : OpResult Bool :=
  if f1.classify == .nan || f2.classify == .nan then
    { value := false, flags := { invalidOperation := f1.isSignalingNaN || f2.isSignalingNaN } }
  else if f1.classify == .zero && f2.classify == .zero then
    { value := true }
  else
    { value := f1.bits == f2.bits }

/-- IEEE 754 ordered less-than with invalid flag on NaNs. -/
def FloatBits.ltResult {spec : BinarySpec} (f1 f2 : FloatBits spec) : OpResult Bool :=
  if f1.classify == .nan || f2.classify == .nan then
    { value := false, flags := { invalidOperation := true } }
  else
    let s1 := f1.isNeg
    let s2 := f2.isNeg
    match s1, s2 with
    | true, false =>
      { value := !(f1.classify == .zero && f2.classify == .zero) }
    | false, true =>
      { value := false }
    | true, true =>
      { value := f1.bits.extractLsb' 0 (spec.expWidth + spec.sigWidth) >
          f2.bits.extractLsb' 0 (spec.expWidth + spec.sigWidth) }
    | false, false =>
      { value := f1.bits.extractLsb' 0 (spec.expWidth + spec.sigWidth) <
          f2.bits.extractLsb' 0 (spec.expWidth + spec.sigWidth) }

def FloatBits.leResult {spec : BinarySpec} (f1 f2 : FloatBits spec) : OpResult Bool :=
  let lt := f1.ltResult f2
  let eq := f1.eqResult f2
  { value := lt.value || eq.value, flags := lt.flags ++ eq.flags }

/-- Value-only IEEE equality wrapper. -/
def FloatBits.eq {spec : BinarySpec} (f1 f2 : FloatBits spec) : Bool :=
  (f1.eqResult f2).value

/-- Value-only IEEE ordered less-than wrapper. -/
def FloatBits.lt {spec : BinarySpec} (f1 f2 : FloatBits spec) : Bool :=
  (f1.ltResult f2).value

def FloatBits.le {spec : BinarySpec} (f1 f2 : FloatBits spec) : Bool :=
  (f1.leResult f2).value

/-- IEEE 754 `minimumNumber`-style helper. -/
def FloatBits.minNumResult {spec : BinarySpec} (f1 f2 : FloatBits spec) : OpResult (FloatBits spec) :=
  if f1.classify == .nan then
    { value := f2, flags := { invalidOperation := f1.isSignalingNaN } }
  else if f2.classify == .nan then
    { value := f1, flags := { invalidOperation := f2.isSignalingNaN } }
  else if f1.lt f2 then
    { value := f1 }
  else if f2.lt f1 then
    { value := f2 }
  else if f1.classify == .zero && f2.classify == .zero then
    if f1.isNeg then { value := f1 } else { value := f2 }
  else
    { value := f1 }

/-- IEEE 754 `maximumNumber`-style helper. -/
def FloatBits.maxNumResult {spec : BinarySpec} (f1 f2 : FloatBits spec) : OpResult (FloatBits spec) :=
  if f1.classify == .nan then
    { value := f2, flags := { invalidOperation := f1.isSignalingNaN } }
  else if f2.classify == .nan then
    { value := f1, flags := { invalidOperation := f2.isSignalingNaN } }
  else if f2.lt f1 then
    { value := f1 }
  else if f1.lt f2 then
    { value := f2 }
  else if f1.classify == .zero && f2.classify == .zero then
    if f1.isNeg then { value := f2 } else { value := f1 }
  else
    { value := f1 }

/-- IEEE 754 `minimumNumberMagnitude`-style helper. -/
def FloatBits.minNumMagResult {spec : BinarySpec} (f1 f2 : FloatBits spec) :
    OpResult (FloatBits spec) :=
  if f1.classify == .nan then
    { value := f2, flags := { invalidOperation := f1.isSignalingNaN } }
  else if f2.classify == .nan then
    { value := f1, flags := { invalidOperation := f2.isSignalingNaN } }
  else if f1.abs.lt f2.abs then
    { value := f1 }
  else if f2.abs.lt f1.abs then
    { value := f2 }
  else if f1.classify == .zero && f2.classify == .zero then
    if f1.isNeg then { value := f1 } else { value := f2 }
  else
    { value := f1 }

/-- IEEE 754 `maximumNumberMagnitude`-style helper. -/
def FloatBits.maxNumMagResult {spec : BinarySpec} (f1 f2 : FloatBits spec) :
    OpResult (FloatBits spec) :=
  if f1.classify == .nan then
    { value := f2, flags := { invalidOperation := f1.isSignalingNaN } }
  else if f2.classify == .nan then
    { value := f1, flags := { invalidOperation := f2.isSignalingNaN } }
  else if f2.abs.lt f1.abs then
    { value := f1 }
  else if f1.abs.lt f2.abs then
    { value := f2 }
  else if f1.classify == .zero && f2.classify == .zero then
    if f1.isNeg then { value := f2 } else { value := f1 }
  else
    { value := f1 }

/-- IEEE 754 `minimum` operation (NaN-propagating). -/
def FloatBits.minimumResultWithNaNPolicy {spec : BinarySpec}
    (f1 f2 : FloatBits spec) (policy : NaNPropagationPolicy) :
    OpResult (FloatBits spec) :=
  if f1.classify == .nan || f2.classify == .nan then
    propagateNaNResultWithPolicy policy f1 f2
  else if f1.lt f2 then
    { value := f1 }
  else if f2.lt f1 then
    { value := f2 }
  else if f1.classify == .zero && f2.classify == .zero then
    if f1.isNeg then { value := f1 } else { value := f2 }
  else
    { value := f1 }

/-- IEEE 754 `minimum` operation (NaN-propagating). -/
def FloatBits.minimumResult {spec : BinarySpec} (f1 f2 : FloatBits spec) : OpResult (FloatBits spec) :=
  f1.minimumResultWithNaNPolicy f2 .preferLeft

/-- IEEE 754 `maximum` operation (NaN-propagating). -/
def FloatBits.maximumResultWithNaNPolicy {spec : BinarySpec}
    (f1 f2 : FloatBits spec) (policy : NaNPropagationPolicy) :
    OpResult (FloatBits spec) :=
  if f1.classify == .nan || f2.classify == .nan then
    propagateNaNResultWithPolicy policy f1 f2
  else if f2.lt f1 then
    { value := f1 }
  else if f1.lt f2 then
    { value := f2 }
  else if f1.classify == .zero && f2.classify == .zero then
    if f1.isNeg then { value := f2 } else { value := f1 }
  else
    { value := f1 }

/-- IEEE 754 `maximum` operation (NaN-propagating). -/
def FloatBits.maximumResult {spec : BinarySpec} (f1 f2 : FloatBits spec) : OpResult (FloatBits spec) :=
  f1.maximumResultWithNaNPolicy f2 .preferLeft

/-- IEEE 754 `minimumMagnitude` operation (NaN-propagating). -/
def FloatBits.minimumMagnitudeResultWithNaNPolicy {spec : BinarySpec}
    (f1 f2 : FloatBits spec) (policy : NaNPropagationPolicy) :
    OpResult (FloatBits spec) :=
  if f1.classify == .nan || f2.classify == .nan then
    propagateNaNResultWithPolicy policy f1 f2
  else if f1.abs.lt f2.abs then
    { value := f1 }
  else if f2.abs.lt f1.abs then
    { value := f2 }
  else
    f1.minimumResultWithNaNPolicy f2 policy

/-- IEEE 754 `minimumMagnitude` operation (NaN-propagating). -/
def FloatBits.minimumMagnitudeResult {spec : BinarySpec}
    (f1 f2 : FloatBits spec) : OpResult (FloatBits spec) :=
  f1.minimumMagnitudeResultWithNaNPolicy f2 .preferLeft

/-- IEEE 754 `maximumMagnitude` operation (NaN-propagating). -/
def FloatBits.maximumMagnitudeResultWithNaNPolicy {spec : BinarySpec}
    (f1 f2 : FloatBits spec) (policy : NaNPropagationPolicy) :
    OpResult (FloatBits spec) :=
  if f1.classify == .nan || f2.classify == .nan then
    propagateNaNResultWithPolicy policy f1 f2
  else if f2.abs.lt f1.abs then
    { value := f1 }
  else if f1.abs.lt f2.abs then
    { value := f2 }
  else
    f1.maximumResultWithNaNPolicy f2 policy

/-- IEEE 754 `maximumMagnitude` operation (NaN-propagating). -/
def FloatBits.maximumMagnitudeResult {spec : BinarySpec}
    (f1 f2 : FloatBits spec) : OpResult (FloatBits spec) :=
  f1.maximumMagnitudeResultWithNaNPolicy f2 .preferLeft

def FloatBits.minNum {spec : BinarySpec} (f1 f2 : FloatBits spec) : FloatBits spec :=
  (f1.minNumResult f2).value

def FloatBits.maxNum {spec : BinarySpec} (f1 f2 : FloatBits spec) : FloatBits spec :=
  (f1.maxNumResult f2).value

def FloatBits.minNumMag {spec : BinarySpec} (f1 f2 : FloatBits spec) : FloatBits spec :=
  (f1.minNumMagResult f2).value

def FloatBits.maxNumMag {spec : BinarySpec} (f1 f2 : FloatBits spec) : FloatBits spec :=
  (f1.maxNumMagResult f2).value

def FloatBits.minimum {spec : BinarySpec} (f1 f2 : FloatBits spec) : FloatBits spec :=
  (f1.minimumResult f2).value

def FloatBits.maximum {spec : BinarySpec} (f1 f2 : FloatBits spec) : FloatBits spec :=
  (f1.maximumResult f2).value

def FloatBits.minimumMagnitude {spec : BinarySpec} (f1 f2 : FloatBits spec) : FloatBits spec :=
  (f1.minimumMagnitudeResult f2).value

def FloatBits.maximumMagnitude {spec : BinarySpec} (f1 f2 : FloatBits spec) : FloatBits spec :=
  (f1.maximumMagnitudeResult f2).value

end Flean
