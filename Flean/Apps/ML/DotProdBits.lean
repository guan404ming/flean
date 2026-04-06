import Flean.Apps.ML.DotProd
import Flean.Arith.Correctness
import Flean.Arith.Conversions
import Flean.Core.CastChain

/-!
# Flean.Apps.ML.DotProdBits

 Bit-level fp16/fp32 mixed-precision dot-product skeleton connected to the
 real-valued `DotProd` model through discharged arithmetic-equivalence theorems.
-/

namespace Flean

/-- The bit-derived fp32 format refines the bit-derived fp16 format. -/
private theorem binarySpec16_toFormat_refines_binarySpec32_toFormat :
    FormatRefines binarySpec16.toFormat binarySpec32.toFormat where
  radix_eq := by simp [BinarySpec.toFormat]
  prec_le := by
    simp [BinarySpec.toFormat, binarySpec16, binarySpec32]
  emin_le := by
    simp [BinarySpec.toFormat, binarySpec16, binarySpec32, BinarySpec.bias]

/-- Finite-or-zero floating-point values, excluding NaN and infinities. -/
def FloatBitsFiniteOrZero {spec : BinarySpec} (f : FloatBits spec) : Prop :=
  f.classify = .normal ∨ f.classify = .subnormal ∨ f.classify = .zero

theorem FloatBits.toReal_isRepresentable_of_finiteOrZero {spec : BinarySpec}
    (f : FloatBits spec) (hfin : FloatBitsFiniteOrZero f) :
    isRepresentable spec.toFormat f.toReal := by
  rcases hfin with h | h | h
  · exact f.toReal_isRepresentable (Or.inl h)
  · exact f.toReal_isRepresentable (Or.inr h)
  · simpa [FloatBitsFiniteOrZero, FloatBits.toReal, h] using
      (zero_isRepresentable spec.toFormat)

/-- Exact widening of an fp16 bit pattern into fp32, represented as a bit-level
cast result. -/
noncomputable def upcast16To32 (a : FloatBits binarySpec16) : FloatBits binarySpec32 :=
  (a.cast (dstSpec := binarySpec32) .roundNearestTiesToEven).value

/-- Bit-level mixed-precision multiply: widen each fp16 input to fp32, then
perform the multiply in fp32. -/
noncomputable def mpMulBits (a b : FloatBits binarySpec16) : FloatBits binarySpec32 :=
  (upcast16To32 a).mul (upcast16To32 b) .roundNearestTiesToEven |>.value

/-- Bit-level mixed-precision accumulate step: add the widened product into the
fp32 accumulator. -/
noncomputable def mpAccStepBits (acc : FloatBits binarySpec32)
    (a b : FloatBits binarySpec16) : FloatBits binarySpec32 :=
  acc.add (mpMulBits a b) .roundNearestTiesToEven |>.value

/-- Recursive bit-level mixed-precision dot-product fold over zipped fp16 input
pairs with an fp32 accumulator. -/
noncomputable def mpDotProdBitsFold (acc : FloatBits binarySpec32) :
    List (FloatBits binarySpec16 × FloatBits binarySpec16) → FloatBits binarySpec32
  | [] => acc
  | (a, b) :: xs => mpDotProdBitsFold (mpAccStepBits acc a b) xs

/-- Bit-level mixed-precision dot product started from fp32 zero. -/
noncomputable def mpDotProdBits
    (as bs : List (FloatBits binarySpec16)) : FloatBits binarySpec32 :=
  mpDotProdBitsFold (FloatBits.zero binarySpec32) (as.zip bs)

/-- Local side conditions ensuring the bit-level mixed-precision multiply stays
within the finite fragment covered by the arithmetic-equivalence assumptions. -/
def MpMulBitsInput (a b : FloatBits binarySpec16) : Prop :=
  FloatBitsFiniteOrZero a ∧
  FloatBitsFiniteOrZero b ∧
  FloatBitsFiniteOrZero (upcast16To32 a) ∧
  FloatBitsFiniteOrZero (upcast16To32 b) ∧
  FloatBitsFiniteOrZero (mpMulBits a b)

/-- Local side conditions ensuring one bit-level accumulate step stays inside
the finite fragment covered by the arithmetic-equivalence assumptions. -/
def MpAccStepBitsInput (acc : FloatBits binarySpec32)
    (a b : FloatBits binarySpec16) : Prop :=
  FloatBitsFiniteOrZero acc ∧
  MpMulBitsInput a b ∧
  FloatBitsFiniteOrZero (mpAccStepBits acc a b)

/-- Recursive contract for the full bit-level dot-product fold. -/
def MpDotProdBitsChain (acc : FloatBits binarySpec32) :
    List (FloatBits binarySpec16 × FloatBits binarySpec16) → Prop
  | [] => FloatBitsFiniteOrZero acc
  | (a, b) :: xs =>
      MpAccStepBitsInput acc a b ∧
        MpDotProdBitsChain (mpAccStepBits acc a b) xs

private theorem upcast16To32_toReal_eq
    {a : FloatBits binarySpec16} (ha : FloatBitsFiniteOrZero a)
    (hup : FloatBitsFiniteOrZero (upcast16To32 a)) :
    (upcast16To32 a).toReal = a.toReal := by
  have hcast_real :
      (upcast16To32 a).toReal =
        castSpec binarySpec16.toFormat binarySpec32.toFormat .roundNearestTiesToEven a.toReal := by
    simpa [upcast16To32] using castBitEquiv binarySpec16 binarySpec32 .roundNearestTiesToEven a ha hup
  have ha_repr16 : isRepresentable binarySpec16.toFormat a.toReal :=
    FloatBits.toReal_isRepresentable_of_finiteOrZero a ha
  have ha_repr32 : isRepresentable binarySpec32.toFormat a.toReal :=
    isRepresentable_of_refines binarySpec16_toFormat_refines_binarySpec32_toFormat ha_repr16
  have hfix32 :
      castSpec binarySpec16.toFormat binarySpec32.toFormat .roundNearestTiesToEven a.toReal = a.toReal := by
    simp [castSpec, round, roundNNE_repr_fixed binarySpec32.toFormat ha_repr32]
  exact hcast_real.trans hfix32

theorem mpMulBits_toReal_eq_mpMul
    {a b : FloatBits binarySpec16} (hin : MpMulBitsInput a b) :
    (mpMulBits a b).toReal = mpMul a.toReal b.toReal := by
  rcases hin with ⟨ha, hb, hau, hbu, hmul_fin⟩
  have hau_real : (upcast16To32 a).toReal = a.toReal :=
    upcast16To32_toReal_eq ha hau
  have hbu_real : (upcast16To32 b).toReal = b.toReal :=
    upcast16To32_toReal_eq hb hbu
  have hmul_real :
      (mpMulBits a b).toReal =
        mulSpec binarySpec32.toFormat .roundNearestTiesToEven
          (upcast16To32 a).toReal (upcast16To32 b).toReal := by
    simpa [mpMulBits] using
      mulBitEquiv binarySpec32 .roundNearestTiesToEven (upcast16To32 a) (upcast16To32 b) hau hbu hmul_fin
  have ha_repr16 : isRepresentable binarySpec16.toFormat a.toReal :=
    FloatBits.toReal_isRepresentable_of_finiteOrZero a ha
  have hb_repr16 : isRepresentable binarySpec16.toFormat b.toReal :=
    FloatBits.toReal_isRepresentable_of_finiteOrZero b hb
  calc
    (mpMulBits a b).toReal
        = mulSpec binarySpec32.toFormat .roundNearestTiesToEven
            (upcast16To32 a).toReal (upcast16To32 b).toReal := hmul_real
    _ = roundNNE binarySpec32.toFormat ((upcast16To32 a).toReal * (upcast16To32 b).toReal) := by
          simp [mulSpec, round]
    _ = roundNNE binarySpec32.toFormat (a.toReal * b.toReal) := by
          rw [hau_real, hbu_real]
    _ = mpMul a.toReal b.toReal := by
          unfold mpMul
          rw [roundNNE_repr_fixed binarySpec16.toFormat ha_repr16,
            roundNNE_repr_fixed binarySpec16.toFormat hb_repr16]

theorem mpAccStepBits_toReal_eq_mpAccStep
    {acc : FloatBits binarySpec32} {a b : FloatBits binarySpec16}
    (hin : MpAccStepBitsInput acc a b) :
    (mpAccStepBits acc a b).toReal = mpAccStep acc.toReal a.toReal b.toReal := by
  rcases hin with ⟨hacc, hmul_in, hres⟩
  have hmul_real : (mpMulBits a b).toReal = mpMul a.toReal b.toReal :=
    mpMulBits_toReal_eq_mpMul hmul_in
  rcases hmul_in with ⟨_, _, _, _, hmul_fin⟩
  have hadd_real :
      (mpAccStepBits acc a b).toReal =
        addSpec binarySpec32.toFormat .roundNearestTiesToEven acc.toReal (mpMulBits a b).toReal := by
    simpa [mpAccStepBits] using
      addBitEquiv binarySpec32 .roundNearestTiesToEven acc (mpMulBits a b) hacc hmul_fin hres
  calc
    (mpAccStepBits acc a b).toReal
        = addSpec binarySpec32.toFormat .roundNearestTiesToEven acc.toReal (mpMulBits a b).toReal := hadd_real
    _ = roundNNE binarySpec32.toFormat (acc.toReal + (mpMulBits a b).toReal) := by
          simp [addSpec, round]
    _ = roundNNE binarySpec32.toFormat (acc.toReal + mpMul a.toReal b.toReal) := by
          rw [hmul_real]
    _ = mpAccStep acc.toReal a.toReal b.toReal := by
          rfl

private theorem zip_map_toReal_eq_map_zip
    (as bs : List (FloatBits binarySpec16)) :
    (as.map FloatBits.toReal).zip (bs.map FloatBits.toReal) =
      (as.zip bs).map (fun ab => (ab.1.toReal, ab.2.toReal)) := by
  induction as generalizing bs with
  | nil =>
      simp
  | cons a as ih =>
      cases bs with
      | nil =>
          simp
      | cons b bs =>
          simp [ih]

private theorem foldl_map_zip_toReal_eq
    (xs : List (FloatBits binarySpec16 × FloatBits binarySpec16)) (acc : ℝ) :
    xs.foldl (fun racc ab => mpAccStep racc ab.1.toReal ab.2.toReal) acc =
      (xs.map (fun ab => (ab.1.toReal, ab.2.toReal))).foldl
        (fun racc x => mpAccStep racc x.1 x.2) acc := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih]

theorem mpDotProdBitsFold_toReal_eq
    {acc : FloatBits binarySpec32} {xs : List (FloatBits binarySpec16 × FloatBits binarySpec16)}
    (hchain : MpDotProdBitsChain acc xs) :
    (mpDotProdBitsFold acc xs).toReal =
      xs.foldl (fun racc ab => mpAccStep racc ab.1.toReal ab.2.toReal) acc.toReal := by
  induction xs generalizing acc with
  | nil =>
      simp [mpDotProdBitsFold] at *
  | cons ab xs ih =>
      rcases ab with ⟨a, b⟩
      rcases hchain with ⟨hstep, htail⟩
      have hstep_real :
          (mpAccStepBits acc a b).toReal = mpAccStep acc.toReal a.toReal b.toReal :=
        mpAccStepBits_toReal_eq_mpAccStep hstep
      have htail_real :
          (mpDotProdBitsFold (mpAccStepBits acc a b) xs).toReal =
            xs.foldl (fun racc ab => mpAccStep racc ab.1.toReal ab.2.toReal)
              (mpAccStepBits acc a b).toReal :=
        ih htail
      simp [mpDotProdBitsFold, hstep_real, htail_real]

theorem mpDotProdBits_toReal_eq_mpDotProd
    {as bs : List (FloatBits binarySpec16)}
    (hchain : MpDotProdBitsChain (FloatBits.zero binarySpec32) (as.zip bs)) :
    (mpDotProdBits as bs).toReal = mpDotProd (as.map FloatBits.toReal) (bs.map FloatBits.toReal) := by
  have hfold :=
    mpDotProdBitsFold_toReal_eq hchain
  unfold mpDotProdBits mpDotProd
  rw [zip_map_toReal_eq_map_zip]
  rw [← foldl_map_zip_toReal_eq]
  simpa [FloatBits.zero_toReal] using hfold

end Flean
