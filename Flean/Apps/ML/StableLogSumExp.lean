import Mathlib.Data.List.MinMax
import Flean.Apps.Compensated.ChunkedKahan

/-!
# Flean.Apps.ML.StableLogSumExp

Stable `log-sum-exp` skeleton built on verified chunked reduction.

This file does not attempt to verify polynomial / table implementations of
`exp` and `log`. Instead, it proves the reduction skeleton that a CPP paper
would want first and also exposes a contract-parametric interface theorem so
the same reduction argument can be instantiated with different transcendental
backends:

1. choose a shift `m` dominating all inputs
2. prove every shifted exponent satisfies `0 < exp(x - m) ≤ 1`
3. reduce these positive terms with verified chunked Kahan reduction
4. conclude that the `log` argument is strictly positive and the chunked
   implementation computes the exact reduction target under the assumed input
   contract for the reduction layer

This is the natural bridge from the compensated-reduction story to a future
full `log-sum-exp` verification, with softmax packaged as a separate extension.
-/

namespace Flean

/-- Rounded transcendental wrapper for `exp`. -/
noncomputable def roundedExp (fmt : FloatFormat) (x : ℝ) : ℝ :=
  roundNNE fmt (Real.exp x)

/-- Blockwise collection of shifted exponentials. -/
noncomputable def shiftedExpBlocks (m : ℝ) (xss : List (List ℝ)) : List (List ℝ) :=
  xss.map (fun xs => xs.map (fun x => Real.exp (x - m)))

/-- Blockwise collection of rounded shifted exponentials. -/
noncomputable def roundedShiftedExpBlocks (fmt : FloatFormat) (m : ℝ)
    (xss : List (List ℝ)) : List (List ℝ) :=
  xss.map (fun xs => xs.map (fun x => roundedExp fmt (x - m)))

/-- Exact target reduced by stable blockwise `log-sum-exp`. -/
noncomputable def shiftedExpBlockSum (m : ℝ) (xss : List (List ℝ)) : ℝ :=
  ((shiftedExpBlocks m xss).map List.sum).sum

/-- Rounded transcendental target before the final `log`. -/
noncomputable def roundedShiftedExpBlockSum (fmt : FloatFormat) (m : ℝ)
    (xss : List (List ℝ)) : ℝ :=
  ((roundedShiftedExpBlocks fmt m xss).map List.sum).sum

/-- Sum of pointwise transcendental-rounding errors across all blocks. -/
noncomputable def roundedShiftedExpErrorSum (fmt : FloatFormat) (m : ℝ)
    (xss : List (List ℝ)) : ℝ :=
  (xss.map (fun xs => (xs.map (fun x => |Real.exp (x - m) - roundedExp fmt (x - m)|)).sum)).sum

/-- Stable blockwise `log-sum-exp` powered by chunked Kahan reduction. -/
noncomputable def stableLogSumExpBlocks (fmt : FloatFormat) (m : ℝ) (xss : List (List ℝ)) : ℝ :=
  m + Real.log (kahanValue (chunkedKahanSum fmt (shiftedExpBlocks m xss)))

/-- Stable blockwise `log-sum-exp` with rounded transcendental calls. -/
noncomputable def stableRoundedLogSumExpBlocks (fmt : FloatFormat) (m : ℝ)
    (xss : List (List ℝ)) : ℝ :=
  m + Real.log (kahanValue (chunkedKahanSum fmt (roundedShiftedExpBlocks fmt m xss)))

/-- `m` dominates every element in the block collection. -/
def BlocksDominatedBy (m : ℝ) (xss : List (List ℝ)) : Prop :=
  ∀ xs ∈ xss, ∀ x ∈ xs, x ≤ m

/-- The block collection contains at least one actual element. -/
def BlocksNonempty (xss : List (List ℝ)) : Prop :=
  ∃ xs ∈ xss, xs ≠ []

theorem roundedExp_isRepresentable (fmt : FloatFormat) (x : ℝ) :
    isRepresentable fmt (roundedExp fmt x) := by
  unfold roundedExp
  exact roundNNE_isRepresentable fmt (Real.exp x)

theorem roundedExp_abs_error_le (fmt : FloatFormat) (x : ℝ) :
    |Real.exp x - roundedExp fmt x| ≤ bpow fmt (cexp fmt (Real.exp x)) / 2 := by
  unfold roundedExp
  exact roundNNE_sub_abs_le fmt (Real.exp x)

theorem roundedExp_nonneg (fmt : FloatFormat) (x : ℝ) :
    0 ≤ roundedExp fmt x := by
  unfold roundedExp
  have hmono := roundNNE_monotone fmt (show (0 : ℝ) ≤ Real.exp x by exact le_of_lt (Real.exp_pos x))
  simpa [roundNNE_zero] using hmono

theorem roundedExp_pos_of_minNormal_le (fmt : FloatFormat) {x : ℝ}
    (hmin : minNormal fmt ≤ Real.exp x) :
    0 < roundedExp fmt x := by
  unfold roundedExp
  have hrepr_min : isRepresentable fmt (minNormal fmt) := by
    refine ⟨1, fmt.emin, ?_, ?_, le_rfl⟩
    · simp [minNormal]
    · have hpow_ge_two : 2 ≤ fmt.β ^ fmt.prec := by
        calc
          2 ≤ fmt.β ^ 1 := by simpa using fmt.hβ
          _ ≤ fmt.β ^ fmt.prec := by
              have hβ_ge_one : 1 ≤ fmt.β := le_trans (by decide) fmt.hβ
              exact Nat.pow_le_pow_right hβ_ge_one fmt.hprec
      have hpow_gt_one : 1 < fmt.β ^ fmt.prec := lt_of_lt_of_le (by norm_num) hpow_ge_two
      exact_mod_cast hpow_gt_one
  have hmono := roundNNE_monotone fmt hmin
  have hfix : roundNNE fmt (minNormal fmt) = minNormal fmt := by
    exact roundNNE_repr_fixed fmt hrepr_min
  have hmin_pos : 0 < minNormal fmt := by
    unfold minNormal
    exact zpow_pos fmt.β_pos _
  rw [hfix] at hmono
  exact lt_of_lt_of_le hmin_pos hmono

theorem roundedExp_le_one_plus_error (fmt : FloatFormat) {x : ℝ}
    (hx : x ≤ 0) :
    roundedExp fmt x ≤ 1 + bpow fmt (cexp fmt (Real.exp x)) / 2 := by
  have hround := roundedExp_abs_error_le fmt x
  have hexp_le : Real.exp x ≤ 1 := by
    calc
      Real.exp x ≤ Real.exp 0 := by exact Real.exp_le_exp.mpr hx
      _ = 1 := by simp
  have hleft : roundedExp fmt x - Real.exp x ≤ |Real.exp x - roundedExp fmt x| := by
    have := neg_abs_le (Real.exp x - roundedExp fmt x)
    linarith
  linarith

theorem roundedExp_monotone (fmt : FloatFormat) {x y : ℝ}
    (hxy : x ≤ y) :
    roundedExp fmt x ≤ roundedExp fmt y := by
  unfold roundedExp
  exact roundNNE_monotone fmt (Real.exp_le_exp.mpr hxy)

theorem exp_shift_nonneg_of_dominated {m x : ℝ} (hxm : x ≤ m) :
    x - m ≤ 0 := by linarith

theorem exp_shift_pos_of_dominated {m x : ℝ} (_hxm : x ≤ m) :
    0 < Real.exp (x - m) := by
  exact Real.exp_pos (x - m)

theorem exp_shift_le_one_of_dominated {m x : ℝ} (hxm : x ≤ m) :
    Real.exp (x - m) ≤ 1 := by
  have hnonpos : x - m ≤ 0 := by linarith
  calc
    Real.exp (x - m) ≤ Real.exp 0 := by
      exact Real.exp_le_exp.mpr hnonpos
    _ = 1 := by simp

theorem shiftedExpBlocks_terms_pos {m : ℝ} {xss : List (List ℝ)}
    (hdom : BlocksDominatedBy m xss) :
    ∀ xs ∈ shiftedExpBlocks m xss, ∀ y ∈ xs, 0 < y := by
  intro xs hxs y hy
  rcases List.mem_map.mp hxs with ⟨raw, hraw, rfl⟩
  rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
  exact exp_shift_pos_of_dominated (hdom raw hraw x hx)

theorem shiftedExpBlocks_terms_le_one {m : ℝ} {xss : List (List ℝ)}
    (hdom : BlocksDominatedBy m xss) :
    ∀ xs ∈ shiftedExpBlocks m xss, ∀ y ∈ xs, y ≤ 1 := by
  intro xs hxs y hy
  rcases List.mem_map.mp hxs with ⟨raw, hraw, rfl⟩
  rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
  exact exp_shift_le_one_of_dominated (hdom raw hraw x hx)

private theorem roundedShiftedExpList_nonincreasing {fmt : FloatFormat} {m : ℝ}
    {xs : List ℝ} (hmono : Nonincreasing xs) :
    Nonincreasing (xs.map (fun x => roundedExp fmt (x - m))) := by
  induction xs with
  | nil =>
      simp [Nonincreasing]
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [Nonincreasing]
      | cons y ys =>
          rcases hmono with ⟨hxy, htail⟩
          refine ⟨?_, ih htail⟩
          apply roundedExp_monotone
          linarith

private theorem roundedShiftedExpList_nonneg {fmt : FloatFormat} {m : ℝ}
    {xs : List ℝ} :
    ∀ y ∈ xs.map (fun x => roundedExp fmt (x - m)), 0 ≤ y := by
  intro y hy
  rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
  exact roundedExp_nonneg fmt (x - m)

private theorem roundedShiftedExpBlockSum_nonneg {fmt : FloatFormat} {m : ℝ}
    {xs : List ℝ} :
    0 ≤ (xs.map (fun x => roundedExp fmt (x - m))).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : 0 ≤ roundedExp fmt (x - m) := roundedExp_nonneg fmt (x - m)
      simpa [List.sum_cons] using add_nonneg hx ih

theorem roundedShiftedExp_kahanInput_of_runningSums_and_order {fmt : FloatFormat}
    {m : ℝ} {xs : List ℝ}
    (_hdom : ∀ x ∈ xs, x ≤ m)
    (hmono : Nonincreasing xs)
    (hrun : RunningSumInput fmt (xs.map (fun x => roundedExp fmt (x - m)))) :
    KahanInput fmt (xs.map (fun x => roundedExp fmt (x - m))) := by
  apply kahanInput_of_runningSums_of_nonincreasing hrun
  · exact roundedShiftedExpList_nonincreasing (fmt := fmt) (m := m) hmono
  · intro y hy
    exact roundedShiftedExpList_nonneg (fmt := fmt) (m := m) y hy

private theorem roundedShiftedExpBlocks_blocks_monotoneInput
    {fmt : FloatFormat} {m : ℝ} {xss : List (List ℝ)}
    (hdom : BlocksDominatedBy m xss)
    (hmono : List.Forall Nonincreasing xss)
    (hrun :
      List.Forall
        (fun xs => RunningSumInput fmt (xs.map (fun x => roundedExp fmt (x - m))))
        xss) :
    List.Forall (KahanMonotoneInput fmt) (roundedShiftedExpBlocks fmt m xss) := by
  induction xss with
  | nil =>
      simp [roundedShiftedExpBlocks]
  | cons xs xss ih =>
      rcases listForall_cons hmono with ⟨hxs_mono, hmono_tail⟩
      rcases listForall_cons hrun with ⟨hxs_run, hrun_tail⟩
      have hxs_nonneg :
          ∀ y ∈ xs.map (fun x => roundedExp fmt (x - m)), 0 ≤ y := by
        intro y hy
        exact roundedShiftedExpList_nonneg (fmt := fmt) (m := m) y hy
      have hhead : KahanMonotoneInput fmt (xs.map (fun x => roundedExp fmt (x - m))) :=
        kahanMonotoneInput_of_runningSums_of_nonincreasing
          hxs_run
          (roundedShiftedExpList_nonincreasing (fmt := fmt) (m := m) hxs_mono)
          hxs_nonneg
      have hdom_tail : BlocksDominatedBy m xss := by
        intro ys hys y hy
        exact hdom ys (by simp [hys]) y hy
      have htail :
          List.Forall (KahanMonotoneInput fmt) (roundedShiftedExpBlocks fmt m xss) :=
        ih hdom_tail hmono_tail hrun_tail
      simpa [roundedShiftedExpBlocks, List.Forall] using And.intro hhead htail

theorem roundedShiftedExpBlocks_chunkedKahanInput_of_runningSums_and_order
    {fmt : FloatFormat} {m : ℝ} {xss : List (List ℝ)}
    (hdom : BlocksDominatedBy m xss)
    (hmono : List.Forall Nonincreasing xss)
    (hrun :
      List.Forall
        (fun xs => RunningSumInput fmt (xs.map (fun x => roundedExp fmt (x - m))))
        xss)
    (hout_run : RunningSumInput fmt ((roundedShiftedExpBlocks fmt m xss).map List.sum))
    (hout_mono : Nonincreasing ((roundedShiftedExpBlocks fmt m xss).map List.sum)) :
    ChunkedKahanInput fmt (roundedShiftedExpBlocks fmt m xss) := by
  have hblocks_mono :
      List.Forall (KahanMonotoneInput fmt) (roundedShiftedExpBlocks fmt m xss) :=
    roundedShiftedExpBlocks_blocks_monotoneInput hdom hmono hrun
  have hout_nonneg :
      ∀ z ∈ ((roundedShiftedExpBlocks fmt m xss).map List.sum), 0 ≤ z := by
    intro z hz
    rcases List.mem_map.mp hz with ⟨ys, hys, rfl⟩
    rcases List.mem_map.mp hys with ⟨raw, hraw, rfl⟩
    exact roundedShiftedExpBlockSum_nonneg (fmt := fmt) (m := m)
  exact chunkedKahanInput_of_monotoneInput
    ⟨hblocks_mono,
      kahanMonotoneInput_of_runningSums_of_nonincreasing hout_run hout_mono hout_nonneg⟩

private theorem list_sum_pos_of_exists_pos {xs : List ℝ}
    (hne : xs ≠ []) (hpos : ∀ x ∈ xs, 0 < x) :
    0 < xs.sum := by
  induction xs with
  | nil =>
      contradiction
  | cons x xs ih =>
      cases xs with
      | nil =>
          simpa using hpos x (by simp)
      | cons y ys =>
          have hx : 0 < x := hpos x (by simp)
          have htail : 0 < (y :: ys).sum := by
            apply ih
            · simp
            · intro z hz
              exact hpos z (by simp [hz])
          simpa [List.sum_cons] using add_pos hx htail

private theorem list_sum_nonneg {xs : List ℝ}
    (hnonneg : ∀ x ∈ xs, 0 ≤ x) : 0 ≤ xs.sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : 0 ≤ x := hnonneg x (by simp)
      have htail : 0 ≤ xs.sum := by
        apply ih
        intro y hy
        exact hnonneg y (by simp [hy])
      simpa [List.sum_cons] using add_nonneg hx htail

private theorem list_sum_pos_of_mem_pos {xs : List ℝ}
    (hnonneg : ∀ y ∈ xs, 0 ≤ y) :
    ∀ {a : ℝ}, a ∈ xs → 0 < a → 0 < xs.sum := by
  induction xs with
  | nil =>
      intro a hmem
      cases hmem
  | cons y ys ih =>
      intro a hmem hapos
      simp at hmem
      rcases hmem with rfl | hmem
      · have htail : 0 ≤ ys.sum := by
          apply list_sum_nonneg
          intro z hz
          exact hnonneg z (by simp [hz])
        simpa [List.sum_cons] using add_pos_of_pos_of_nonneg hapos htail
      · have hy : 0 ≤ y := hnonneg y (by simp)
        have htail : 0 < ys.sum := by
          apply ih
          · intro z hz
            exact hnonneg z (by simp [hz])
          · exact hmem
          · exact hapos
        simpa [List.sum_cons] using add_pos_of_nonneg_of_pos hy htail

theorem shiftedExpBlockSum_pos {m : ℝ} {xss : List (List ℝ)}
    (hdom : BlocksDominatedBy m xss) (hne : BlocksNonempty xss) :
    0 < shiftedExpBlockSum m xss := by
  rcases hne with ⟨xs, hxs, hxs_ne⟩
  have hsum_pos : 0 < (xs.map (fun x => Real.exp (x - m))).sum := by
    apply list_sum_pos_of_exists_pos
    · cases hmap : xs.map (fun x => Real.exp (x - m)) with
      | nil =>
          cases xs with
          | nil => contradiction
          | cons x xs => simp at hmap
      | cons y ys => simp
    · intro y hy
      rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
      exact exp_shift_pos_of_dominated (hdom xs hxs x hx)
  have hmem :
      (xs.map (fun x => Real.exp (x - m))).sum ∈ (shiftedExpBlocks m xss).map List.sum := by
    apply List.mem_map.mpr
    exact ⟨xs.map (fun x => Real.exp (x - m)), by
      apply List.mem_map.mpr
      exact ⟨xs, hxs, rfl⟩, rfl⟩
  have hall_nonneg : ∀ z ∈ (shiftedExpBlocks m xss).map List.sum, 0 ≤ z := by
    intro z hz
    rcases List.mem_map.mp hz with ⟨ys, hys, rfl⟩
    apply list_sum_nonneg
    intro y hy
    exact le_of_lt ((shiftedExpBlocks_terms_pos hdom) ys hys y hy)
  exact list_sum_pos_of_mem_pos hall_nonneg hmem hsum_pos

theorem chunkedKahan_shiftedExp_exact {fmt : FloatFormat} (hβ : fmt.β = 2)
    {m : ℝ} {xss : List (List ℝ)}
    (hin : ChunkedKahanInput fmt (shiftedExpBlocks m xss)) :
    kahanValue (chunkedKahanSum fmt (shiftedExpBlocks m xss)) = shiftedExpBlockSum m xss := by
  simpa [shiftedExpBlockSum] using chunkedKahanSum_exact (fmt := fmt) hβ hin

theorem stableLogSumExpBlocks_exact {fmt : FloatFormat} (hβ : fmt.β = 2)
    {m : ℝ} {xss : List (List ℝ)}
    (hin : ChunkedKahanInput fmt (shiftedExpBlocks m xss))
    (_hdom : BlocksDominatedBy m xss)
    (_hne : BlocksNonempty xss) :
    stableLogSumExpBlocks fmt m xss = m + Real.log (shiftedExpBlockSum m xss) := by
  have hexact := chunkedKahan_shiftedExp_exact (fmt := fmt) hβ hin
  unfold stableLogSumExpBlocks
  rw [hexact]

theorem stableLogSumExpBlocks_log_arg_pos {fmt : FloatFormat} (hβ : fmt.β = 2)
    {m : ℝ} {xss : List (List ℝ)}
    (hin : ChunkedKahanInput fmt (shiftedExpBlocks m xss))
    (hdom : BlocksDominatedBy m xss)
    (hne : BlocksNonempty xss) :
    0 < kahanValue (chunkedKahanSum fmt (shiftedExpBlocks m xss)) := by
  rw [chunkedKahan_shiftedExp_exact (fmt := fmt) hβ hin]
  exact shiftedExpBlockSum_pos hdom hne

theorem chunkedKahan_roundedShiftedExp_exact {fmt : FloatFormat} (hβ : fmt.β = 2)
    {m : ℝ} {xss : List (List ℝ)}
    (hin : ChunkedKahanInput fmt (roundedShiftedExpBlocks fmt m xss)) :
    kahanValue (chunkedKahanSum fmt (roundedShiftedExpBlocks fmt m xss)) =
      roundedShiftedExpBlockSum fmt m xss := by
  simpa [roundedShiftedExpBlockSum] using
    chunkedKahanSum_exact (fmt := fmt) hβ hin

theorem stableRoundedLogSumExpBlocks_exact {fmt : FloatFormat} (hβ : fmt.β = 2)
    {m : ℝ} {xss : List (List ℝ)}
    (hin : ChunkedKahanInput fmt (roundedShiftedExpBlocks fmt m xss)) :
    stableRoundedLogSumExpBlocks fmt m xss = m + Real.log (roundedShiftedExpBlockSum fmt m xss) := by
  have hexact := chunkedKahan_roundedShiftedExp_exact (fmt := fmt) hβ hin
  unfold stableRoundedLogSumExpBlocks
  rw [hexact]

theorem stableRoundedLogSumExpBlocks_log_arg_pos {fmt : FloatFormat} (hβ : fmt.β = 2)
    {m : ℝ} {xss : List (List ℝ)}
    (hin : ChunkedKahanInput fmt (roundedShiftedExpBlocks fmt m xss))
    (hpos : 0 < roundedShiftedExpBlockSum fmt m xss) :
    0 < kahanValue (chunkedKahanSum fmt (roundedShiftedExpBlocks fmt m xss)) := by
  rw [chunkedKahan_roundedShiftedExp_exact (fmt := fmt) hβ hin]
  exact hpos

theorem shiftedExp_vs_roundedShiftedExp_block_bound {fmt : FloatFormat}
    {m : ℝ} {xs : List ℝ} :
    |(xs.map (fun x => Real.exp (x - m))).sum - (xs.map (fun x => roundedExp fmt (x - m))).sum|
      ≤ (xs.map (fun x => |Real.exp (x - m) - roundedExp fmt (x - m)|)).sum := by
  simpa using map_sum_sub_le_sum_map_abs_sub xs
    (fun x => Real.exp (x - m)) (fun x => roundedExp fmt (x - m))

theorem shiftedExp_vs_roundedShiftedExp_bound {fmt : FloatFormat}
    {m : ℝ} {xss : List (List ℝ)} :
    |shiftedExpBlockSum m xss - roundedShiftedExpBlockSum fmt m xss|
      ≤ roundedShiftedExpErrorSum fmt m xss := by
  unfold shiftedExpBlockSum roundedShiftedExpBlockSum roundedShiftedExpErrorSum
  calc
    |((shiftedExpBlocks m xss).map List.sum).sum - ((roundedShiftedExpBlocks fmt m xss).map List.sum).sum|
        ≤ (xss.map (fun xs =>
            |(xs.map (fun x => Real.exp (x - m))).sum -
              (xs.map (fun x => roundedExp fmt (x - m))).sum|)).sum := by
              simpa [shiftedExpBlocks, roundedShiftedExpBlocks] using
                map_sum_sub_le_sum_map_abs_sub xss
                  (fun xs => (xs.map (fun x => Real.exp (x - m))).sum)
                  (fun xs => (xs.map (fun x => roundedExp fmt (x - m))).sum)
    _ ≤ (xss.map (fun xs => (xs.map (fun x => |Real.exp (x - m) - roundedExp fmt (x - m)|)).sum)).sum := by
          induction xss with
          | nil =>
              simp
          | cons xs xss ih =>
              simp only [List.map_cons, List.sum_cons]
              have hhead := shiftedExp_vs_roundedShiftedExp_block_bound (fmt := fmt) (m := m) (xs := xs)
              linarith

theorem stableRoundedLogSumExpBlocks_preLog_error_bound {fmt : FloatFormat} (hβ : fmt.β = 2)
    {m : ℝ} {xss : List (List ℝ)}
    (hin : ChunkedKahanInput fmt (roundedShiftedExpBlocks fmt m xss)) :
    |shiftedExpBlockSum m xss -
      kahanValue (chunkedKahanSum fmt (roundedShiftedExpBlocks fmt m xss))|
      ≤ roundedShiftedExpErrorSum fmt m xss := by
  rw [chunkedKahan_roundedShiftedExp_exact (fmt := fmt) hβ hin]
  exact shiftedExp_vs_roundedShiftedExp_bound (fmt := fmt) (m := m)

/-- Discharge theorem for the rounded stable-log-sum-exp reduction: if the
rounded shifted-exponential blocks satisfy the stronger prefix-sum contract,
then they automatically satisfy `ChunkedKahanInput`. -/
theorem roundedShiftedExpBlocks_chunkedKahanInput_of_prefixInput {fmt : FloatFormat}
    {m : ℝ} {xss : List (List ℝ)}
    (hin :
      ChunkedKahanPrefixInput fmt (roundedShiftedExpBlocks fmt m xss)) :
    ChunkedKahanInput fmt (roundedShiftedExpBlocks fmt m xss) :=
  chunkedKahanInput_of_prefixInput hin

/-- Paper-facing wrapper theorem for the exact shifted-exponential
stable-log-sum-exp story. -/
theorem stableLogSumExpBlocks_main {fmt : FloatFormat} (hβ : fmt.β = 2)
    {m : ℝ} {xss : List (List ℝ)}
    (hin : ChunkedKahanInput fmt (shiftedExpBlocks m xss))
    (hdom : BlocksDominatedBy m xss)
    (hne : BlocksNonempty xss) :
    stableLogSumExpBlocks fmt m xss = m + Real.log (shiftedExpBlockSum m xss) ∧
      0 < kahanValue (chunkedKahanSum fmt (shiftedExpBlocks m xss)) := by
  refine ⟨stableLogSumExpBlocks_exact (fmt := fmt) hβ hin hdom hne,
    stableLogSumExpBlocks_log_arg_pos (fmt := fmt) hβ hin hdom hne⟩

/-- Paper-facing wrapper theorem for the rounded stable-log-sum-exp story:
exact reduction to the rounded target, positivity of the final log argument,
and a pre-log bound from transcendental rounding. -/
theorem stableRoundedLogSumExpBlocks_main {fmt : FloatFormat} (hβ : fmt.β = 2)
    {m : ℝ} {xss : List (List ℝ)}
    (hin : ChunkedKahanInput fmt (roundedShiftedExpBlocks fmt m xss))
    (hpos : 0 < roundedShiftedExpBlockSum fmt m xss) :
    stableRoundedLogSumExpBlocks fmt m xss = m + Real.log (roundedShiftedExpBlockSum fmt m xss) ∧
      0 < kahanValue (chunkedKahanSum fmt (roundedShiftedExpBlocks fmt m xss)) ∧
      |shiftedExpBlockSum m xss -
        kahanValue (chunkedKahanSum fmt (roundedShiftedExpBlocks fmt m xss))|
        ≤ roundedShiftedExpErrorSum fmt m xss := by
  refine ⟨stableRoundedLogSumExpBlocks_exact (fmt := fmt) hβ hin,
    stableRoundedLogSumExpBlocks_log_arg_pos (fmt := fmt) hβ hin hpos,
    stableRoundedLogSumExpBlocks_preLog_error_bound (fmt := fmt) hβ hin⟩

/-- Paper-facing discharge theorem: easy-to-check monotonicity and running-sum
conditions imply the full rounded stable-log-sum-exp guarantee. -/
theorem stableRoundedLogSumExpBlocks_main_of_runningSums_and_order
    {fmt : FloatFormat} (hβ : fmt.β = 2)
    {m : ℝ} {xss : List (List ℝ)}
    (hdom : BlocksDominatedBy m xss)
    (hmono : List.Forall Nonincreasing xss)
    (hrun :
      List.Forall
        (fun xs => RunningSumInput fmt (xs.map (fun x => roundedExp fmt (x - m))))
        xss)
    (hout_run : RunningSumInput fmt ((roundedShiftedExpBlocks fmt m xss).map List.sum))
    (hout_mono : Nonincreasing ((roundedShiftedExpBlocks fmt m xss).map List.sum))
    (hpos : 0 < roundedShiftedExpBlockSum fmt m xss) :
    stableRoundedLogSumExpBlocks fmt m xss = m + Real.log (roundedShiftedExpBlockSum fmt m xss) ∧
      0 < kahanValue (chunkedKahanSum fmt (roundedShiftedExpBlocks fmt m xss)) ∧
      |shiftedExpBlockSum m xss -
        kahanValue (chunkedKahanSum fmt (roundedShiftedExpBlocks fmt m xss))|
        ≤ roundedShiftedExpErrorSum fmt m xss := by
  have hin :
      ChunkedKahanInput fmt (roundedShiftedExpBlocks fmt m xss) :=
    roundedShiftedExpBlocks_chunkedKahanInput_of_runningSums_and_order
      (fmt := fmt) (m := m) hdom hmono hrun hout_run hout_mono
  exact stableRoundedLogSumExpBlocks_main (fmt := fmt) hβ hin hpos

/-- User-facing contract for the rounded stable-log-sum-exp discharge path.
This packages the easy-to-check assumptions that feed the internal
`ChunkedKahanInput` contract. -/
def StableRoundedLogSumExpContract (fmt : FloatFormat) (m : ℝ) (xss : List (List ℝ)) : Prop :=
  BlocksDominatedBy m xss ∧
  List.Forall Nonincreasing xss ∧
  List.Forall
    (fun xs => RunningSumInput fmt (xs.map (fun x => roundedExp fmt (x - m))))
    xss ∧
  RunningSumInput fmt ((roundedShiftedExpBlocks fmt m xss).map List.sum) ∧
  Nonincreasing ((roundedShiftedExpBlocks fmt m xss).map List.sum)

/-- Micro-example wrapper for the paper: once the user-facing contract is
established, the full rounded stable-log-sum-exp guarantee follows in one step. -/
theorem stableRoundedLogSumExpBlocks_main_of_contract
    {fmt : FloatFormat} (hβ : fmt.β = 2)
    {m : ℝ} {xss : List (List ℝ)}
    (hcontract : StableRoundedLogSumExpContract fmt m xss)
    (hpos : 0 < roundedShiftedExpBlockSum fmt m xss) :
    stableRoundedLogSumExpBlocks fmt m xss = m + Real.log (roundedShiftedExpBlockSum fmt m xss) ∧
      0 < kahanValue (chunkedKahanSum fmt (roundedShiftedExpBlocks fmt m xss)) ∧
      |shiftedExpBlockSum m xss -
        kahanValue (chunkedKahanSum fmt (roundedShiftedExpBlocks fmt m xss))|
        ≤ roundedShiftedExpErrorSum fmt m xss := by
  rcases hcontract with ⟨hdom, hmono, hrun, hout_run, hout_mono⟩
  exact stableRoundedLogSumExpBlocks_main_of_runningSums_and_order
    (fmt := fmt) hβ hdom hmono hrun hout_run hout_mono hpos

/-- Contract for plugging an `exp`/`log` backend into the stable LSE skeleton.
The proof obligations are exactly the properties needed by the reduction
pipeline, not a specific implementation strategy. -/
structure StableLSEModel where
  exp : ℝ → ℝ
  roundedExp : FloatFormat → ℝ → ℝ
  log : ℝ → ℝ
  exp_pos : ∀ x : ℝ, 0 < exp x
  roundedExp_nonneg : ∀ fmt x, 0 ≤ roundedExp fmt x
  roundedExp_monotone : ∀ fmt {x y : ℝ}, x ≤ y → roundedExp fmt x ≤ roundedExp fmt y

namespace StableLSEModel

variable (M : StableLSEModel)

/-- Model-parameterized exact shifted-transcendental blocks. -/
noncomputable def shiftedExpBlocks (m : ℝ) (xss : List (List ℝ)) : List (List ℝ) :=
  xss.map (fun xs => xs.map (fun x => M.exp (x - m)))

/-- Model-parameterized rounded shifted-transcendental blocks. -/
noncomputable def roundedShiftedExpBlocks (fmt : FloatFormat) (m : ℝ)
    (xss : List (List ℝ)) : List (List ℝ) :=
  xss.map (fun xs => xs.map (fun x => M.roundedExp fmt (x - m)))

/-- Model-parameterized exact target reduced by stable blockwise LSE. -/
noncomputable def shiftedExpBlockSum (m : ℝ) (xss : List (List ℝ)) : ℝ :=
  ((shiftedExpBlocks M m xss).map List.sum).sum

/-- Model-parameterized rounded transcendental target before the final `log`. -/
noncomputable def roundedShiftedExpBlockSum (fmt : FloatFormat) (m : ℝ)
    (xss : List (List ℝ)) : ℝ :=
  ((roundedShiftedExpBlocks M fmt m xss).map List.sum).sum

/-- Model-parameterized sum of pointwise transcendental-rounding errors. -/
noncomputable def roundedShiftedExpErrorSum (fmt : FloatFormat) (m : ℝ)
    (xss : List (List ℝ)) : ℝ :=
  (xss.map
      (fun xs => (xs.map (fun x => |M.exp (x - m) - M.roundedExp fmt (x - m)|)).sum)).sum

/-- Model-parameterized stable blockwise `log-sum-exp`. -/
noncomputable def stableRoundedLogSumExpBlocks (fmt : FloatFormat) (m : ℝ)
    (xss : List (List ℝ)) : ℝ :=
  m + M.log (kahanValue (chunkedKahanSum fmt (roundedShiftedExpBlocks M fmt m xss)))

private theorem roundedShiftedExpList_nonincreasing
    {fmt : FloatFormat} {m : ℝ} {xs : List ℝ}
    (hmono : Nonincreasing xs) :
    Nonincreasing (xs.map (fun x => M.roundedExp fmt (x - m))) := by
  induction xs with
  | nil =>
      simp [Nonincreasing]
  | cons x xs ih =>
      cases xs with
      | nil =>
          simp [Nonincreasing]
      | cons y ys =>
          rcases hmono with ⟨hxy, htail⟩
          refine ⟨?_, ih htail⟩
          exact M.roundedExp_monotone fmt (by linarith)

private theorem roundedShiftedExpList_nonneg
    {fmt : FloatFormat} {m : ℝ} {xs : List ℝ} :
    ∀ y ∈ xs.map (fun x => M.roundedExp fmt (x - m)), 0 ≤ y := by
  intro y hy
  rcases List.mem_map.mp hy with ⟨x, hx, rfl⟩
  exact M.roundedExp_nonneg fmt (x - m)

private theorem roundedShiftedExpBlockSum_nonneg
    {fmt : FloatFormat} {m : ℝ} {xs : List ℝ} :
    0 ≤ (xs.map (fun x => M.roundedExp fmt (x - m))).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : 0 ≤ M.roundedExp fmt (x - m) := M.roundedExp_nonneg fmt (x - m)
      simpa [List.sum_cons] using add_nonneg hx ih

private theorem roundedShiftedExpBlocks_blocks_monotoneInput
    {fmt : FloatFormat} {m : ℝ} {xss : List (List ℝ)}
    (hmono : List.Forall Nonincreasing xss)
    (hrun :
      List.Forall
        (fun xs => RunningSumInput fmt (xs.map (fun x => M.roundedExp fmt (x - m))))
        xss) :
    List.Forall (KahanMonotoneInput fmt) (roundedShiftedExpBlocks M fmt m xss) := by
  induction xss with
  | nil =>
      simp [roundedShiftedExpBlocks]
  | cons xs xss ih =>
      rcases listForall_cons hmono with ⟨hxs_mono, hmono_tail⟩
      rcases listForall_cons hrun with ⟨hxs_run, hrun_tail⟩
      have hxs_nonneg :
          ∀ y ∈ xs.map (fun x => M.roundedExp fmt (x - m)), 0 ≤ y := by
        intro y hy
        exact roundedShiftedExpList_nonneg (M := M) (fmt := fmt) (m := m) y hy
      have hhead : KahanMonotoneInput fmt (xs.map (fun x => M.roundedExp fmt (x - m))) :=
        kahanMonotoneInput_of_runningSums_of_nonincreasing
          hxs_run
          (roundedShiftedExpList_nonincreasing (M := M) (fmt := fmt) (m := m) hxs_mono)
          hxs_nonneg
      have htail :
          List.Forall (KahanMonotoneInput fmt) (roundedShiftedExpBlocks M fmt m xss) :=
        ih hmono_tail hrun_tail
      simpa [roundedShiftedExpBlocks, List.Forall] using And.intro hhead htail

/-- Discharge theorem for model-parameterized rounded blocks. -/
theorem roundedShiftedExpBlocks_chunkedKahanInput_of_runningSums_and_order
    {fmt : FloatFormat} {m : ℝ} {xss : List (List ℝ)}
    (hmono : List.Forall Nonincreasing xss)
    (hrun :
      List.Forall
        (fun xs => RunningSumInput fmt (xs.map (fun x => M.roundedExp fmt (x - m))))
        xss)
    (hout_run : RunningSumInput fmt ((roundedShiftedExpBlocks M fmt m xss).map List.sum))
    (hout_mono : Nonincreasing ((roundedShiftedExpBlocks M fmt m xss).map List.sum)) :
    ChunkedKahanInput fmt (roundedShiftedExpBlocks M fmt m xss) := by
  have hblocks_mono :
      List.Forall (KahanMonotoneInput fmt) (roundedShiftedExpBlocks M fmt m xss) :=
    roundedShiftedExpBlocks_blocks_monotoneInput (M := M) hmono hrun
  have hout_nonneg :
      ∀ z ∈ ((roundedShiftedExpBlocks M fmt m xss).map List.sum), 0 ≤ z := by
    intro z hz
    rcases List.mem_map.mp hz with ⟨ys, hys, rfl⟩
    rcases List.mem_map.mp hys with ⟨raw, hraw, rfl⟩
    exact roundedShiftedExpBlockSum_nonneg (M := M) (fmt := fmt) (m := m)
  exact chunkedKahanInput_of_monotoneInput
    ⟨hblocks_mono,
      kahanMonotoneInput_of_runningSums_of_nonincreasing hout_run hout_mono hout_nonneg⟩

/-- Model-parameterized exactness of chunked Kahan on rounded shifted blocks. -/
theorem chunkedKahan_roundedShiftedExp_exact {fmt : FloatFormat} (hβ : fmt.β = 2)
    {m : ℝ} {xss : List (List ℝ)}
    (hin : ChunkedKahanInput fmt (roundedShiftedExpBlocks M fmt m xss)) :
    kahanValue (chunkedKahanSum fmt (roundedShiftedExpBlocks M fmt m xss)) =
      roundedShiftedExpBlockSum M fmt m xss := by
  simpa [roundedShiftedExpBlockSum] using
    chunkedKahanSum_exact (fmt := fmt) hβ hin

/-- Model-parameterized exact reduction to the rounded transcendental target. -/
theorem stableRoundedLogSumExpBlocks_exact {fmt : FloatFormat} (hβ : fmt.β = 2)
    {m : ℝ} {xss : List (List ℝ)}
    (hin : ChunkedKahanInput fmt (roundedShiftedExpBlocks M fmt m xss)) :
    stableRoundedLogSumExpBlocks M fmt m xss = m + M.log (roundedShiftedExpBlockSum M fmt m xss) := by
  have hexact := chunkedKahan_roundedShiftedExp_exact (M := M) (fmt := fmt) hβ hin
  unfold stableRoundedLogSumExpBlocks
  rw [hexact]

/-- Model-parameterized positivity of the final `log` argument. -/
theorem stableRoundedLogSumExpBlocks_log_arg_pos {fmt : FloatFormat} (hβ : fmt.β = 2)
    {m : ℝ} {xss : List (List ℝ)}
    (hin : ChunkedKahanInput fmt (roundedShiftedExpBlocks M fmt m xss))
    (hpos : 0 < roundedShiftedExpBlockSum M fmt m xss) :
    0 < kahanValue (chunkedKahanSum fmt (roundedShiftedExpBlocks M fmt m xss)) := by
  rw [chunkedKahan_roundedShiftedExp_exact (M := M) (fmt := fmt) hβ hin]
  exact hpos

private theorem shiftedExp_vs_roundedShiftedExp_block_bound {fmt : FloatFormat}
    {m : ℝ} {xs : List ℝ} :
    |(xs.map (fun x => M.exp (x - m))).sum -
        (xs.map (fun x => M.roundedExp fmt (x - m))).sum|
      ≤ (xs.map (fun x => |M.exp (x - m) - M.roundedExp fmt (x - m)|)).sum := by
  simpa using map_sum_sub_le_sum_map_abs_sub xs
    (fun x => M.exp (x - m)) (fun x => M.roundedExp fmt (x - m))

/-- Model-parameterized pre-log bound from transcendental rounding error. -/
theorem shiftedExp_vs_roundedShiftedExp_bound {fmt : FloatFormat}
    {m : ℝ} {xss : List (List ℝ)} :
    |shiftedExpBlockSum M m xss - roundedShiftedExpBlockSum M fmt m xss|
      ≤ roundedShiftedExpErrorSum M fmt m xss := by
  unfold shiftedExpBlockSum roundedShiftedExpBlockSum roundedShiftedExpErrorSum
  calc
    |((shiftedExpBlocks M m xss).map List.sum).sum -
        ((roundedShiftedExpBlocks M fmt m xss).map List.sum).sum|
        ≤ (xss.map (fun xs =>
            |(xs.map (fun x => M.exp (x - m))).sum -
              (xs.map (fun x => M.roundedExp fmt (x - m))).sum|)).sum := by
              simpa [shiftedExpBlocks, roundedShiftedExpBlocks] using
                map_sum_sub_le_sum_map_abs_sub xss
                  (fun xs => (xs.map (fun x => M.exp (x - m))).sum)
                  (fun xs => (xs.map (fun x => M.roundedExp fmt (x - m))).sum)
    _ ≤ (xss.map
          (fun xs => (xs.map (fun x => |M.exp (x - m) - M.roundedExp fmt (x - m)|)).sum)).sum := by
          induction xss with
          | nil =>
              simp
          | cons xs xss ih =>
              simp only [List.map_cons, List.sum_cons]
              have hhead := shiftedExp_vs_roundedShiftedExp_block_bound
                (M := M) (fmt := fmt) (m := m) (xs := xs)
              linarith

/-- Model-parameterized pre-log composition theorem. -/
theorem stableRoundedLogSumExpBlocks_preLog_error_bound {fmt : FloatFormat} (hβ : fmt.β = 2)
    {m : ℝ} {xss : List (List ℝ)}
    (hin : ChunkedKahanInput fmt (roundedShiftedExpBlocks M fmt m xss)) :
    |shiftedExpBlockSum M m xss -
      kahanValue (chunkedKahanSum fmt (roundedShiftedExpBlocks M fmt m xss))|
      ≤ roundedShiftedExpErrorSum M fmt m xss := by
  rw [chunkedKahan_roundedShiftedExp_exact (M := M) (fmt := fmt) hβ hin]
  exact shiftedExp_vs_roundedShiftedExp_bound (M := M) (fmt := fmt) (m := m)

/-- Model-parameterized paper-facing main theorem. -/
theorem stableRoundedLogSumExpBlocks_main {fmt : FloatFormat} (hβ : fmt.β = 2)
    {m : ℝ} {xss : List (List ℝ)}
    (hin : ChunkedKahanInput fmt (roundedShiftedExpBlocks M fmt m xss))
    (hpos : 0 < roundedShiftedExpBlockSum M fmt m xss) :
    stableRoundedLogSumExpBlocks M fmt m xss = m + M.log (roundedShiftedExpBlockSum M fmt m xss) ∧
      0 < kahanValue (chunkedKahanSum fmt (roundedShiftedExpBlocks M fmt m xss)) ∧
      |shiftedExpBlockSum M m xss -
        kahanValue (chunkedKahanSum fmt (roundedShiftedExpBlocks M fmt m xss))|
        ≤ roundedShiftedExpErrorSum M fmt m xss := by
  refine ⟨stableRoundedLogSumExpBlocks_exact (M := M) (fmt := fmt) hβ hin,
    stableRoundedLogSumExpBlocks_log_arg_pos (M := M) (fmt := fmt) hβ hin hpos,
    stableRoundedLogSumExpBlocks_preLog_error_bound (M := M) (fmt := fmt) hβ hin⟩

/-- User-facing model contract mirroring the discharge path from monotonicity
and running-sum assumptions to the full theorem. -/
def StableRoundedLogSumExpContract (fmt : FloatFormat) (m : ℝ)
    (xss : List (List ℝ)) : Prop :=
  List.Forall Nonincreasing xss ∧
  List.Forall
    (fun xs => RunningSumInput fmt (xs.map (fun x => M.roundedExp fmt (x - m))))
    xss ∧
  RunningSumInput fmt ((roundedShiftedExpBlocks M fmt m xss).map List.sum) ∧
  Nonincreasing ((roundedShiftedExpBlocks M fmt m xss).map List.sum) ∧
  0 < roundedShiftedExpBlockSum M fmt m xss

/-- Single-step discharge theorem from model contract to full guarantee. -/
theorem stableRoundedLogSumExpBlocks_main_of_contract
    {fmt : FloatFormat} (hβ : fmt.β = 2)
    {m : ℝ} {xss : List (List ℝ)}
    (hcontract : StableRoundedLogSumExpContract M fmt m xss) :
    stableRoundedLogSumExpBlocks M fmt m xss = m + M.log (roundedShiftedExpBlockSum M fmt m xss) ∧
      0 < kahanValue (chunkedKahanSum fmt (roundedShiftedExpBlocks M fmt m xss)) ∧
      |shiftedExpBlockSum M m xss -
        kahanValue (chunkedKahanSum fmt (roundedShiftedExpBlocks M fmt m xss))|
        ≤ roundedShiftedExpErrorSum M fmt m xss := by
  rcases hcontract with ⟨hmono, hrun, hout_run, hout_mono, hpos⟩
  have hin :
      ChunkedKahanInput fmt (roundedShiftedExpBlocks M fmt m xss) :=
    roundedShiftedExpBlocks_chunkedKahanInput_of_runningSums_and_order
      (M := M) hmono hrun hout_run hout_mono
  exact stableRoundedLogSumExpBlocks_main (M := M) (fmt := fmt) hβ hin hpos

end StableLSEModel

/-- Default model instance matching the existing case-study definitions:
`exp`/`log` are interpreted by `Real.exp`/`Real.log` and rounded by `roundNNE`. -/
noncomputable def realStableLSEModel : StableLSEModel where
  exp := Real.exp
  roundedExp := fun fmt x => roundNNE fmt (Real.exp x)
  log := Real.log
  exp_pos := Real.exp_pos
  roundedExp_nonneg := by
    intro fmt x
    have hmono := roundNNE_monotone fmt
      (show (0 : ℝ) ≤ Real.exp x by exact le_of_lt (Real.exp_pos x))
    simpa [roundNNE_zero] using hmono
  roundedExp_monotone := by
    intro fmt x y hxy
    exact roundNNE_monotone fmt (Real.exp_le_exp.mpr hxy)


end Flean
