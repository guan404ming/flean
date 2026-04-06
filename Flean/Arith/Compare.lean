import Flean.Binary.Defs
import Flean.Arith.Exceptions

/-!
# Flean.Arith.Compare

IEEE 754 comparison operations for floating-point numbers.
-/

namespace Flean

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
  else
    { value := f2 }

/-- IEEE 754 `maximumNumber`-style helper. -/
def FloatBits.maxNumResult {spec : BinarySpec} (f1 f2 : FloatBits spec) : OpResult (FloatBits spec) :=
  if f1.classify == .nan then
    { value := f2, flags := { invalidOperation := f1.isSignalingNaN } }
  else if f2.classify == .nan then
    { value := f1, flags := { invalidOperation := f2.isSignalingNaN } }
  else if f2.lt f1 then
    { value := f1 }
  else
    { value := f2 }

def FloatBits.minNum {spec : BinarySpec} (f1 f2 : FloatBits spec) : FloatBits spec :=
  (f1.minNumResult f2).value

def FloatBits.maxNum {spec : BinarySpec} (f1 f2 : FloatBits spec) : FloatBits spec :=
  (f1.maxNumResult f2).value

end Flean
