import Flean.Arith.Operations
import Flean.Binary.Defs
import Flean.Binary.Special

/-!
# Flean.Arith.FMA

Fused Multiply-Add: (a * b) + c without intermediate rounding.
Bit-level implementation with single rounding.
-/

namespace Flean

/-- Fused Multiply-Add for FloatBits.
    Computes (a * b) + c exactly before one final rounding. -/
def FloatBits.fma {spec : BinarySpec} (a b c : FloatBits spec) :
    OpResult (FloatBits spec) :=
  -- Special cases for multiplication first
  match a.mulSpecial b with
  | some res_mul => 
    match res_mul.value.addSpecial c with
    | some res_add => { value := res_add.value, flags := res_mul.flags ++ res_add.flags }
    | none => { value := res_mul.value, flags := res_mul.flags }
  | none =>
    -- Finite a, b: compute precise product m_ab = m1 * m2
    let (m1, e1) := a.getExtendedSignificand
    let (m2, e2) := b.getExtendedSignificand
    let p := spec.sigWidth
    let bias := spec.bias
    let m_ab := m1.toNat * m2.toNat -- Width: 2p + 2
    let e_ab : Int := (e1 : Int) + (e2 : Int) - (bias : Int) - (p : Int)
    let sign_ab := a.signBit ^^^ b.signBit
    
    -- Finite c: align m_c with m_ab
    let (m_c, e_c_nat) := c.getExtendedSignificand
    let e_c : Int := (e_c_nat : Int) - (p : Int)
    
    -- Common scale: 2^E_min
    let E_min := min e_ab e_c
    let m_ab_aligned := m_ab <<< (e_ab - E_min).toNat
    let m_c_aligned := m_c.toNat <<< (e_c - E_min).toNat
    
    -- Fused Addition/Subtraction
    let (res_m_full, res_sign, _res_inexact) :=
      if sign_ab == c.signBit then
        (m_ab_aligned + m_c_aligned, sign_ab, false)
      else if m_ab_aligned ≥ m_c_aligned then
        (m_ab_aligned - m_c_aligned, sign_ab, false)
      else
        (m_c_aligned - m_ab_aligned, c.signBit, false)
    
    -- Normalization and roundTZ
    if res_m_full == 0 then
      { value := FloatBits.posZero spec }
    else
      -- Target exponent e_res such that res_m_full is in [2^p, 2^(p+1))
      -- This requires finding the highest bit of res_m_full
      let hbit := Nat.log2 res_m_full
      let e_res_real : Int := (E_min + hbit) - (p : Int)
      
      let (final_m_val, final_e_real, inexact) := 
        if e_res_real + (bias : Int) ≥ 2^spec.expWidth - 1 then
          -- Overflow
          (0, (2^spec.expWidth - 1 : Int), true)
        else if e_res_real + (bias : Int) ≤ 0 then
          -- Underflow to subnormal/zero
          (0, (0 : Int), true)
        else
          let shift := hbit - p
          let rounded_m := res_m_full >>> shift
          (rounded_m % 2^p, e_res_real + (bias : Int), (res_m_full % 2^shift != 0))
      
      let res_bits := 
        if final_e_real ≥ 2^spec.expWidth - 1 then
          if res_sign == 1 then FloatBits.negInf spec else FloatBits.posInf spec
        else
          FloatBits.fromFields res_sign (BitVec.ofNat spec.expWidth final_e_real.toNat) (BitVec.ofNat p final_m_val)
      
      { value := res_bits, flags := if inexact then { inexact := true } else {} }

end Flean
