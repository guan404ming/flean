import Flean.Arith.Operations
import Flean.Arith.Conversions

/-!
# Flean.Arith.RoundToIntegral

Round a floating-point number to its nearest integral value (as a float).
-/

namespace Flean

/-- roundToIntegral: Returns the nearest integer in the same float format. -/
def FloatBits.roundToIntegral {spec : BinarySpec} (f : FloatBits spec) (mode : RoundingMode) : 
    OpResult (FloatBits spec) :=
  match f.classify with
  | .nan | .infinite | .zero => { value := f }
  | .normal | .subnormal =>
    let bias := spec.bias
    let e := f.expField.toNat
    let p := spec.sigWidth
    let e_real := (e : Int) - (bias : Int)
    
    if e_real ≥ p then
      -- Already an integer
      { value := f }
    else if e_real < -1 then
      -- Magnitude is less than 0.5, rounds to 0 or 1
      let truncated := 0
      let lsb := false
      let g := if e_real == -1 then true else false
      let r := false
      let s := true -- fractional part exists
      let roundUp := roundDecision mode f.isNeg truncated lsb g r s
      if roundUp then
        -- Rounds to 1.0 or -1.0
        let res_e := (bias : Nat)
        { value := FloatBits.fromFields f.signBit (BitVec.ofNat spec.expWidth res_e) (BitVec.ofNat p 0),
          flags := { inexact := true } }
      else
        { value := if f.isNeg then FloatBits.negZero spec else FloatBits.posZero spec,
          flags := { inexact := true } }
    else
      -- TODO: full integer rounding for mixed exponent range
      { value := f }

end Flean
