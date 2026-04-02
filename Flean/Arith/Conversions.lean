import Flean.Binary.Defs
import Flean.Arith.Operations
import Flean.Arith.RoundingHelper

/-!
# Flean.Arith.Conversions (Extended for Mixed Precision)

Support for casting between different floating-point formats (e.g., f32 to f16).
Crucial for ML compiler mixed-precision analysis.
-/

namespace Flean

/-- Generic cast between two different BinarySpecs.
    This is the core operation for mixed-precision ML compilers. -/
def FloatBits.cast {srcSpec dstSpec : BinarySpec} (f : FloatBits srcSpec) (mode : RoundingMode) :
    OpResult (FloatBits dstSpec) :=
  match f.classify with
  | .nan => { value := FloatBits.quietNaN dstSpec }
  | .infinite => { value := if f.isNeg then FloatBits.negInf dstSpec else FloatBits.posInf dstSpec }
  | .zero => { value := if f.isNeg then FloatBits.negZero dstSpec else FloatBits.posZero dstSpec }
  | .normal | .subnormal =>
    let (m, e) := f.getExtendedSignificand
    let srcBias := srcSpec.bias
    let dstBias := dstSpec.bias
    let srcP := srcSpec.sigWidth
    let dstP := dstSpec.sigWidth
    
    -- Real exponent: e - srcBias
    -- Target biased exponent: (e - srcBias) + dstBias
    let rawExp : Int := (e : Int) - (srcBias : Int) + (dstBias : Int)
    
    -- Align significand: shift from srcP to dstP
    if dstP ≥ srcP then
      -- Widening (e.g., f16 -> f32): no precision loss
      let scaledSig := m.toNat <<< (dstP - srcP)
      roundAndPack mode f.isNeg rawExp scaledSig
    else
      -- Narrowing (e.g., f32 -> f16): potential precision loss/rounding
      let _shift := srcP - dstP
      roundAndPack mode f.isNeg rawExp m.toNat

end Flean
