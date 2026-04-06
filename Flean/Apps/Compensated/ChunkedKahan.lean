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

/-- A posteriori fallback budget for blockwise Kahan reduction: sum the local
block budgets, then add the outer Kahan fallback budget on the stream of block
summary values. -/
noncomputable def chunkedKahanFallbackBudget (fmt : FloatFormat) (xss : List (List ℝ)) : ℝ :=
  (xss.map (kahanSumFallbackBudget fmt)).sum +
    kahanSumFallbackBudget fmt (xss.map (kahanBlockValue fmt))

/-- Practical blockwise input contract:
every block is individually valid for Kahan, and the list of block summaries is
itself valid for the outer Kahan reduction. -/
def ChunkedKahanInput (fmt : FloatFormat) (xss : List (List ℝ)) : Prop :=
  List.Forall (KahanInput fmt) xss ∧ KahanInput fmt (xss.map (kahanBlockValue fmt))

/-- Stronger compositional sufficient condition for blockwise Kahan:
each block satisfies the prefix-sum contract, and the block-summary stream
does as well. -/
def ChunkedKahanPrefixInput (fmt : FloatFormat) (xss : List (List ℝ)) : Prop :=
  List.Forall (KahanPrefixInput fmt) xss ∧
    KahanPrefixInput fmt (xss.map List.sum)

/-- Easy-to-check sufficient condition for blockwise Kahan:
each block and the outer block-summary stream are nonnegative, nonincreasing,
and have representable running sums. -/
def ChunkedKahanMonotoneInput (fmt : FloatFormat) (xss : List (List ℝ)) : Prop :=
  List.Forall (KahanMonotoneInput fmt) xss ∧
    KahanMonotoneInput fmt (xss.map List.sum)

private theorem map_kahanBlockValue_error_sum_le {fmt : FloatFormat} {xss : List (List ℝ)} :
    (xss.map (fun xs => |kahanBlockValue fmt xs - xs.sum|)).sum
      ≤ (xss.map (kahanSumFallbackBudget fmt)).sum := by
  induction xss with
  | nil =>
      simp
  | cons xs xss ih =>
      simp only [List.map_cons, List.sum_cons]
      have hhead : |kahanBlockValue fmt xs - xs.sum| ≤ kahanSumFallbackBudget fmt xs := by
        unfold kahanBlockValue
        simpa [abs_sub_comm] using
          (kahanSum_fallback_value_error_le (fmt := fmt) (xs := xs))
      exact add_le_add hhead ih

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

private theorem map_kahanBlockValue_eq_map_sum_of_prefixInput {fmt : FloatFormat}
    {xss : List (List ℝ)} (hblocks : List.Forall (KahanPrefixInput fmt) xss) :
    xss.map (kahanBlockValue fmt) = xss.map List.sum := by
  induction xss with
  | nil =>
      simp
  | cons xs xss ih =>
      rcases listForall_cons hblocks with ⟨hxs, htail⟩
      have hhead : kahanBlockValue fmt xs = xs.sum := by
        unfold kahanBlockValue
        rw [kahanSum_eq_sum_zero_of_prefixInput hxs]
        simp [kahanValue]
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

/-- General fallback bound for the exact state value tracked by blockwise
Kahan reduction. This requires no exactness contract. -/
theorem chunkedKahanSum_fallback_value_error_le {fmt : FloatFormat}
    {xss : List (List ℝ)} :
    |kahanValue (chunkedKahanSum fmt xss) - (xss.map List.sum).sum|
      ≤ chunkedKahanFallbackBudget fmt xss := by
  have houter :
      |kahanValue (chunkedKahanSum fmt xss) - (xss.map (kahanBlockValue fmt)).sum|
        ≤ kahanSumFallbackBudget fmt (xss.map (kahanBlockValue fmt)) := by
    simpa [chunkedKahanSum] using
      (kahanSum_fallback_value_error_le (fmt := fmt) (xs := xss.map (kahanBlockValue fmt)))
  have hblocks :
      |(xss.map (kahanBlockValue fmt)).sum - (xss.map List.sum).sum|
        ≤ (xss.map (kahanSumFallbackBudget fmt)).sum := by
    calc
      |(xss.map (kahanBlockValue fmt)).sum - (xss.map List.sum).sum|
          ≤ (xss.map (fun xs => |kahanBlockValue fmt xs - xs.sum|)).sum := by
              simpa using
                map_sum_sub_le_sum_map_abs_sub xss (kahanBlockValue fmt) List.sum
      _ ≤ (xss.map (kahanSumFallbackBudget fmt)).sum := map_kahanBlockValue_error_sum_le
  have htri :
      |kahanValue (chunkedKahanSum fmt xss) - (xss.map List.sum).sum|
        ≤ |kahanValue (chunkedKahanSum fmt xss) - (xss.map (kahanBlockValue fmt)).sum| +
          |(xss.map (kahanBlockValue fmt)).sum - (xss.map List.sum).sum| := by
    have := abs_add_le
      (kahanValue (chunkedKahanSum fmt xss) - (xss.map (kahanBlockValue fmt)).sum)
      ((xss.map (kahanBlockValue fmt)).sum - (xss.map List.sum).sum)
    simpa [sub_eq_add_neg] using this
  have := add_le_add houter hblocks
  dsimp [chunkedKahanFallbackBudget]
  linarith

/-- Fallback bound for the running-sum component returned by blockwise Kahan. -/
theorem chunkedKahanSum_fallback_head_error_le {fmt : FloatFormat}
    {xss : List (List ℝ)} :
    |(xss.map List.sum).sum - (chunkedKahanSum fmt xss).1|
      ≤ chunkedKahanFallbackBudget fmt xss + |(chunkedKahanSum fmt xss).2| := by
  have hval := chunkedKahanSum_fallback_value_error_le (fmt := fmt) (xss := xss)
  cases hsum : chunkedKahanSum fmt xss with
  | mk s c =>
      rw [hsum] at hval
      simp at hval ⊢
      have hdecomp : (xss.map List.sum).sum - s = ((xss.map List.sum).sum - (s - c)) - c := by
        ring
      rw [hdecomp]
      have htri : |((xss.map List.sum).sum - (s - c)) - c|
          ≤ |(xss.map List.sum).sum - (s - c)| + |c| := by
        simpa [sub_eq_add_neg] using abs_add_le ((xss.map List.sum).sum - (s - c)) (-c)
      have hval' : |(xss.map List.sum).sum - (s - c)| ≤ chunkedKahanFallbackBudget fmt xss := by
        simpa [kahanValue, abs_sub_comm] using hval
      calc
        |((xss.map List.sum).sum - (s - c)) - c| ≤ |(xss.map List.sum).sum - (s - c)| + |c| := htri
        _ ≤ chunkedKahanFallbackBudget fmt xss + |c| := by gcongr

/-- Paper-facing fallback corollary for blockwise Kahan, normalized to the
flattened-input `sumAbs` form. -/
theorem chunkedKahanSum_fallback_value_error_le_of_C_eps_sumAbs
    {fmt : FloatFormat} {xss : List (List ℝ)} {C : ℝ}
    (hbudget : chunkedKahanFallbackBudget fmt xss ≤
      C * machineEpsilon fmt * sumAbs xss.flatten) :
    |kahanValue (chunkedKahanSum fmt xss) - (xss.map List.sum).sum|
      ≤ C * machineEpsilon fmt * sumAbs xss.flatten :=
  le_trans (chunkedKahanSum_fallback_value_error_le (fmt := fmt) (xss := xss)) hbudget

/-- Paper-facing fallback corollary for the running-sum component returned by
blockwise Kahan, normalized to the flattened-input `sumAbs` form. -/
theorem chunkedKahanSum_fallback_head_error_le_of_C_eps_sumAbs
    {fmt : FloatFormat} {xss : List (List ℝ)} {C : ℝ}
    (hbudget : chunkedKahanFallbackBudget fmt xss ≤
      C * machineEpsilon fmt * sumAbs xss.flatten) :
    |(xss.map List.sum).sum - (chunkedKahanSum fmt xss).1|
      ≤ C * machineEpsilon fmt * sumAbs xss.flatten + |(chunkedKahanSum fmt xss).2| := by
  calc
    |(xss.map List.sum).sum - (chunkedKahanSum fmt xss).1|
        ≤ chunkedKahanFallbackBudget fmt xss + |(chunkedKahanSum fmt xss).2| :=
          chunkedKahanSum_fallback_head_error_le (fmt := fmt) (xss := xss)
    _ ≤ C * machineEpsilon fmt * sumAbs xss.flatten + |(chunkedKahanSum fmt xss).2| := by
          gcongr

theorem chunkedKahanInput_of_prefixInput {fmt : FloatFormat} {xss : List (List ℝ)}
    (hin : ChunkedKahanPrefixInput fmt xss) :
    ChunkedKahanInput fmt xss := by
  rcases hin with ⟨hblocks, hout⟩
  refine ⟨?_, ?_⟩
  · exact hblocks.imp (fun xs hxs => kahanInput_of_prefixInput hxs)
  · rw [map_kahanBlockValue_eq_map_sum_of_prefixInput hblocks]
    exact kahanInput_of_prefixInput hout

theorem chunkedKahanPrefixInput_of_monotoneInput {fmt : FloatFormat} {xss : List (List ℝ)}
    (hin : ChunkedKahanMonotoneInput fmt xss) :
    ChunkedKahanPrefixInput fmt xss := by
  rcases hin with ⟨hblocks, hout⟩
  exact ⟨hblocks.imp (fun xs hxs => kahanPrefixInput_of_monotoneInput hxs),
    kahanPrefixInput_of_monotoneInput hout⟩

theorem chunkedKahanInput_of_monotoneInput {fmt : FloatFormat} {xss : List (List ℝ)}
    (hin : ChunkedKahanMonotoneInput fmt xss) :
    ChunkedKahanInput fmt xss :=
  chunkedKahanInput_of_prefixInput (chunkedKahanPrefixInput_of_monotoneInput hin)

end Flean
