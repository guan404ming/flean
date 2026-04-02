import Flean.Core.Rounding
import Flean.Binary.Defs
import Flean.Binary.Special
import Flean.Arith.Exceptions

/-!
# Flean.Arith.RoundingHelper

Bit-level implementation of IEEE 754 rounding modes and final packing.
Provides the logic to round an intermediate significand with Guard, Round, and Sticky bits,
and handles gradual underflow (subnormals) and overflow.
-/

namespace Flean

/-- Rounding decision for an intermediate result. -/
def roundDecision (mode : RoundingMode) (isNeg : Bool) (m : Nat) (lsb g r s : Bool) : Bool :=
  let grs := g || r || s
  match mode with
  | .roundTowardZero => false
  | .roundTowardPositive => if !isNeg && grs then true else false
  | .roundTowardNegative => if isNeg && grs then true else false
  | .roundNearestTiesToEven =>
    if !g then false 
    else if r || s then true 
    else lsb
  | .roundNearestTiesAway =>
    if g then true else false

/-- Helper to extract G, R, S bits from a large integer and a shift count. -/
def getGRS (val : Nat) (shift : Int) : Bool × Bool × Bool :=
  if shift ≤ 0 then (false, false, false)
  else
    let s_nat := shift.toNat
    let g := (val >>> (s_nat - 1)) % 2 == 1
    let r := if s_nat > 1 then (val >>> (s_nat - 2)) % 2 == 1 else false
    let s := if s_nat > 2 then (val % (2 ^ (s_nat - 2)) != 0) else false
    (g, r, s)

/-- roundAndPack: The core logic for IEEE 754 rounding and overflow/underflow detection.
    `isNeg`: Sign bit.
    `rawExp`: Biased exponent (can be <= 0 for subnormals or very small results).
    `rawSig`: Significand scaled such that the 'p' bit is at 2^p. -/
def roundAndPack {spec : BinarySpec} (mode : RoundingMode) (isNeg : Bool) 
    (rawExp : Int) (rawSig : Nat) : OpResult (FloatBits spec) :=
  let p := spec.sigWidth
  let maxExp := (2^spec.expWidth - 1 : Int)
  
  -- 1. Handle Underflow (Gradual Underflow)
  let (effExp, effSig, g, r, s) := 
    if rawExp < 1 then
      let shift := 1 - rawExp
      let (g', r', s') := getGRS rawSig shift
      ((0 : Int), rawSig >>> shift.toNat, g', r', s')
    else
      (rawExp, rawSig, false, false, false) -- Already normalized or handled
      
  -- 2. Apply Rounding Decision
  let lsb := effSig % 2 == 1
  let roundUp := roundDecision mode isNeg effSig lsb g r s
  let roundedSig := if roundUp then effSig + 1 else effSig
  
  -- 3. Check for Carry-out from Rounding (e.g., 1.11...1 + 1 = 10.00...0)
  let (finalSig, finalExp) := 
    if roundedSig ≥ 2^(p + 1) then
      (roundedSig / 2, effExp + 1)
    else
      (roundedSig, effExp)
      
  -- 4. Check for Overflow
  if finalExp ≥ maxExp then
    let overflowResult := 
      match mode with
      | .roundTowardZero => FloatBits.maxFinite spec -- Placeholder for max finite
      | .roundTowardPositive => if !isNeg then FloatBits.posInf spec else FloatBits.maxFinite spec
      | .roundTowardNegative => if isNeg then FloatBits.negInf spec else FloatBits.maxFinite spec
      | _ => if isNeg then FloatBits.negInf spec else FloatBits.posInf spec
    { value := overflowResult, flags := { overflow := true, inexact := true } }
  else
    let res_sign := if isNeg then BitVec.ofNat 1 1 else BitVec.ofNat 1 0
    let res_m := BitVec.ofNat p (finalSig % 2^p)
    let res_e := BitVec.ofNat spec.expWidth finalExp.toNat
    let inexact := (g || r || s || roundUp)
    let underflow := (rawExp < 1) && inexact
    { value := FloatBits.fromFields res_sign res_e res_m,
      flags := { inexact := inexact, underflow := underflow } }

end Flean
