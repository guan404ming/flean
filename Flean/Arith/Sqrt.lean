import Flean.Binary.Defs
import Flean.Binary.Special
import Flean.Arith.Exceptions

/-!
# Flean.Arith.Sqrt

Bit-level square root for IEEE 754 floating-point numbers.
Uses a digit-by-digit algorithm on the significand.
-/

namespace Flean

/-- Bit-level square root for the significand.
    Given m in [1, 4), computes sqrt(m) in [1, 2). -/
def sqrtSignificand (m : Nat) (p : Nat) : Nat :=
  let rec loop (i : Nat) (res : Nat) (rem : Nat) : Nat :=
    match i with
    | 0 => res
    | i' + 1 =>
      let next_res := (res <<< 1) + 1
      if rem ≥ next_res then
        loop i' next_res (rem - next_res)
      else
        loop i' (res <<< 1) rem
  loop (p + 1) 0 m

/-- Finite square root implementation. -/
def FloatBits.sqrtFinite {spec : BinarySpec} (f : FloatBits spec) :
    OpResult (FloatBits spec) :=
  if f.isNeg && f.classify != .zero then
    { value := FloatBits.quietNaN spec, flags := { invalidOperation := true } }
  else if f.classify == .zero then
    { value := f }
  else
    let (m, e) := f.getExtendedSignificand
    let bias := spec.bias
    let p := spec.sigWidth
    -- Adjusted exponent: (e - bias) / 2
    -- If (e - bias) is odd, we shift m left by 1 to make it even
    let e_real := (e : Int) - (bias : Int)
    let (m_adj, final_e_real) := 
      if e_real % 2 == 0 then
        (m.toNat <<< p, e_real / 2)
      else
        (m.toNat <<< (p + 1), (e_real - 1) / 2)
    
    -- sqrtSignificand result: (p+1) bits or more
    let q := sqrtSignificand m_adj p
    let res_m := BitVec.ofNat p (q / 2) -- Truncate for roundTZ
    let final_e := final_e_real + (bias : Int)
    
    { value := FloatBits.fromFields 0 (BitVec.ofNat spec.expWidth final_e.toNat) res_m,
      flags := { inexact := true } } -- Simplification: assume inexact for now

/-- Main square root function. -/
def FloatBits.sqrt {spec : BinarySpec} (f : FloatBits spec) : OpResult (FloatBits spec) :=
  match f.classify with
  | .nan => { value := f }
  | .infinite => 
    if f.isNeg then { value := FloatBits.quietNaN spec, flags := { invalidOperation := true } }
    else { value := f }
  | _ => f.sqrtFinite

end Flean
