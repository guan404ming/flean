import Flean.Apps.Common.List
import Flean.Apps.Compensated.Kahan

/-!
# Flean.Apps.Compensated.ChunkedKahan

Blockwise Kahan reduction built on the core Kahan fold.
-/

namespace Flean

/-- Summary value exported by one Kahan-reduced block. -/
noncomputable def kahanBlockValue (fmt : FloatFormat) (xs : List ℝ) : ℝ :=
  kahanValue (kahanSum fmt xs)

/-- Kahan summation after first reducing each block to its compensated summary. -/
noncomputable def chunkedKahanSum (fmt : FloatFormat) (xss : List (List ℝ)) : ℝ × ℝ :=
  kahanSum fmt (xss.map (kahanBlockValue fmt))

/-- Practical blockwise input contract:
every block is individually valid for Kahan, and the list of block summaries is
itself valid for the outer Kahan reduction. -/
def ChunkedKahanInput (fmt : FloatFormat) (xss : List (List ℝ)) : Prop :=
  List.Forall (KahanInput fmt) xss ∧ KahanInput fmt (xss.map (kahanBlockValue fmt))

private theorem map_kahanBlockValue_sum_eq_sum_map_sum {fmt : FloatFormat} (hβ : fmt.β = 2)
    {xss : List (List ℝ)} (hblocks : List.Forall (KahanInput fmt) xss) :
    (xss.map (kahanBlockValue fmt)).sum = (xss.map List.sum).sum := by
  induction xss with
  | nil =>
      simp
  | cons xs xss ih =>
      rcases listForall_cons hblocks with ⟨hxs, htail⟩
      have hhead : kahanBlockValue fmt xs = xs.sum := by
        exact kahanSum_exact hβ hxs
      simp [hhead, ih htail]

/-- Exactness of two-level blockwise Kahan reduction. -/
theorem chunkedKahanSum_exact {fmt : FloatFormat} (hβ : fmt.β = 2)
    {xss : List (List ℝ)} (hin : ChunkedKahanInput fmt xss) :
    kahanValue (chunkedKahanSum fmt xss) = (xss.map List.sum).sum := by
  rcases hin with ⟨hblocks, hout⟩
  have houter : kahanValue (chunkedKahanSum fmt xss) = (xss.map (kahanBlockValue fmt)).sum := by
    exact kahanSum_exact hβ hout
  rw [houter, map_kahanBlockValue_sum_eq_sum_map_sum hβ hblocks]

/-- Tight forward error bound for blockwise Kahan reduction. -/
theorem chunkedKahanSum_tight_bound {fmt : FloatFormat} (hβ : fmt.β = 2)
    {xss : List (List ℝ)} (hin : ChunkedKahanInput fmt xss) :
    |(xss.map List.sum).sum - (chunkedKahanSum fmt xss).1|
      = |(chunkedKahanSum fmt xss).2| := by
  rcases hin with ⟨hblocks, hout⟩
  have houter :
      |(xss.map (kahanBlockValue fmt)).sum - (chunkedKahanSum fmt xss).1|
        = |(chunkedKahanSum fmt xss).2| := by
    exact kahanSum_tight_bound hβ hout
  rw [map_kahanBlockValue_sum_eq_sum_map_sum hβ hblocks] at houter
  exact houter

end Flean
