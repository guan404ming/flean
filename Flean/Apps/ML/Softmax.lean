import Flean.Apps.ML.StableLogSumExp

/-!
# Flean.Apps.ML.Softmax

Softmax normalization built on the stable shifted-exponential setup from
`StableLogSumExp`.
-/

namespace Flean

/-- Exact softmax-style normalization over the shifted exponential blocks. -/
noncomputable def softmaxBlocks (m : ℝ) (xss : List (List ℝ)) : List (List ℝ) :=
  let s := shiftedExpBlockSum m xss
  (shiftedExpBlocks m xss).map (fun xs => xs.map (fun x => x / s))

/-- Rounded softmax-style normalization over the shifted exponential blocks. -/
noncomputable def roundedSoftmaxBlocks (fmt : FloatFormat) (m : ℝ)
    (xss : List (List ℝ)) : List (List ℝ) :=
  let s := shiftedExpBlockSum m xss
  (shiftedExpBlocks m xss).map (fun xs => xs.map (fun x => roundNNE fmt (x / s)))

/-- Sum of pointwise normalization-rounding errors across all blocks. -/
noncomputable def roundedSoftmaxErrorSum (fmt : FloatFormat) (m : ℝ)
    (xss : List (List ℝ)) : ℝ :=
  let s := shiftedExpBlockSum m xss
  ((shiftedExpBlocks m xss).map
    (fun xs => (xs.map (fun x => |x / s - roundNNE fmt (x / s)|)).sum)).sum

private theorem list_sum_div {xs : List ℝ} {s : ℝ} :
    (xs.map (fun x => x / s)).sum = xs.sum / s := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [List.sum_cons, ih]
      ring

private theorem list_list_sum_div {xss : List (List ℝ)} {s : ℝ} :
    (xss.map (fun xs => (xs.map (fun x => x / s)).sum)).sum = (xss.map List.sum).sum / s := by
  simpa [list_sum_div] using (list_sum_div (xs := xss.map List.sum) (s := s))

private theorem map_map_sum_eq_sum_map_sum {xss : List (List ℝ)} {f : ℝ → ℝ} :
    (List.map List.sum (List.map (fun xs => List.map f xs) xss)).sum =
      (xss.map (fun xs => (xs.map f).sum)).sum := by
  induction xss with
  | nil =>
      simp
  | cons xs xss ih =>
      simp
      simpa [Function.comp] using ih

theorem softmaxBlocks_sum_one {m : ℝ} {xss : List (List ℝ)}
    (hdom : BlocksDominatedBy m xss) (hne : BlocksNonempty xss) :
    ((softmaxBlocks m xss).map List.sum).sum = 1 := by
  let s := shiftedExpBlockSum m xss
  have hs_pos : 0 < s := shiftedExpBlockSum_pos hdom hne
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  unfold softmaxBlocks
  dsimp [s]
  have hrewrite :
      (List.map List.sum
          (List.map (fun xs => List.map (fun x => x / s) xs) (shiftedExpBlocks m xss))).sum =
        ((shiftedExpBlocks m xss).map List.sum).sum / s := by
    simpa using (list_list_sum_div (xss := shiftedExpBlocks m xss) (s := s))
  rw [hrewrite]
  calc
    ((shiftedExpBlocks m xss).map List.sum).sum / s = s / s := by
          simp [s, shiftedExpBlockSum]
    _ = 1 := by field_simp [hs_ne]

theorem roundedSoftmaxBlocks_sum_error_bound {fmt : FloatFormat}
    {m : ℝ} {xss : List (List ℝ)}
    (hdom : BlocksDominatedBy m xss) (hne : BlocksNonempty xss) :
    |1 - ((roundedSoftmaxBlocks fmt m xss).map List.sum).sum|
      ≤ roundedSoftmaxErrorSum fmt m xss := by
  let s := shiftedExpBlockSum m xss
  have hsoftmax : ((softmaxBlocks m xss).map List.sum).sum = 1 :=
    softmaxBlocks_sum_one hdom hne
  rw [← hsoftmax]
  have hsoftmax_rewrite :
      ((softmaxBlocks m xss).map List.sum).sum =
        ((shiftedExpBlocks m xss).map List.sum).sum / s := by
    unfold softmaxBlocks
    dsimp [s]
    rw [map_map_sum_eq_sum_map_sum]
    exact list_list_sum_div (xss := shiftedExpBlocks m xss) (s := s)
  rw [hsoftmax_rewrite]
  unfold roundedSoftmaxBlocks roundedSoftmaxErrorSum
  dsimp [s]
  have hrounded_rewrite :
      (List.map List.sum
          (List.map (fun xs => List.map (fun x => roundNNE fmt (x / s)) xs)
            (shiftedExpBlocks m xss))).sum =
        ((shiftedExpBlocks m xss).map
          (fun xs => (xs.map (fun x => roundNNE fmt (x / s))).sum)).sum := by
    simpa using
      (map_map_sum_eq_sum_map_sum
        (xss := shiftedExpBlocks m xss) (f := fun x => roundNNE fmt (x / s)))
  rw [hrounded_rewrite]
  rw [← list_list_sum_div (xss := shiftedExpBlocks m xss) (s := s)]
  calc
    |((shiftedExpBlocks m xss).map (fun xs => (xs.map (fun x => x / s)).sum)).sum -
        ((shiftedExpBlocks m xss).map
          (fun xs => (xs.map (fun x => roundNNE fmt (x / s))).sum)).sum|
        ≤ ((shiftedExpBlocks m xss).map
            (fun xs =>
              |(xs.map (fun x => x / s)).sum -
                (xs.map (fun x => roundNNE fmt (x / s))).sum|)).sum := by
              simpa using
                map_sum_sub_le_sum_map_abs_sub (shiftedExpBlocks m xss)
                  (fun xs => (xs.map (fun x => x / s)).sum)
                  (fun xs => (xs.map (fun x => roundNNE fmt (x / s))).sum)
    _ ≤ ((shiftedExpBlocks m xss).map
          (fun xs => (xs.map (fun x => |x / s -
            roundNNE fmt (x / s)|)).sum)).sum := by
          induction (shiftedExpBlocks m xss) with
          | nil =>
              simp
          | cons xs xss ih =>
              simp only [List.map_cons, List.sum_cons]
              have hhead := map_sum_sub_le_sum_map_abs_sub xs
                (fun x => x / s)
                (fun x => roundNNE fmt (x / s))
              exact add_le_add hhead ih

end Flean
