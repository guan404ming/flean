import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Flatten
import Mathlib.Tactic

namespace Flean

/-- Sum of absolute values of a real list. -/
noncomputable def sumAbs (xs : List ℝ) : ℝ :=
  (xs.map abs).sum

theorem sumAbs_nil : sumAbs ([] : List ℝ) = 0 := by
  simp [sumAbs]

theorem sumAbs_cons (x : ℝ) (xs : List ℝ) :
    sumAbs (x :: xs) = |x| + sumAbs xs := by
  simp [sumAbs]

theorem sumAbs_nonneg (xs : List ℝ) : 0 ≤ sumAbs xs := by
  induction xs with
  | nil =>
      simp [sumAbs]
  | cons x xs ih =>
      simpa [sumAbs] using add_nonneg (abs_nonneg x) ih

theorem sumAbs_flatten (xss : List (List ℝ)) :
    sumAbs xss.flatten = (xss.map sumAbs).sum := by
  induction xss with
  | nil =>
      simp [sumAbs]
  | cons xs xss ih =>
      simp [sumAbs, List.flatten, List.map_append, List.sum_append]
      simpa [Function.comp, sumAbs] using ih

theorem listForall_cons {α : Type} {p : α → Prop} {x : α} {xs : List α}
    (h : List.Forall p (x :: xs)) : p x ∧ List.Forall p xs := by
  cases xs with
  | nil =>
      simpa [List.Forall] using h
  | cons y ys =>
      simpa [List.Forall] using h

theorem map_sum_sub_le_sum_map_abs_sub {α : Type} (xs : List α)
    (f g : α → ℝ) :
    |(xs.map f).sum - (xs.map g).sum| ≤ (xs.map (fun x => |f x - g x|)).sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      have htail :
          |f x - g x| + |(xs.map f).sum - (xs.map g).sum|
            ≤ |f x - g x| + (xs.map (fun y => |f y - g y|)).sum := by
        simpa using add_le_add (show |f x - g x| ≤ |f x - g x| by exact le_rfl) ih
      calc
        |((x :: xs).map f).sum - ((x :: xs).map g).sum|
            = |(f x - g x) + ((xs.map f).sum - (xs.map g).sum)| := by
                simp [List.sum_cons]
                ring_nf
        _ ≤ |f x - g x| + |(xs.map f).sum - (xs.map g).sum| := abs_add_le _ _
        _ ≤ |f x - g x| + (xs.map (fun y => |f y - g y|)).sum := htail
        _ = ((x :: xs).map (fun y => |f y - g y|)).sum := by
              simp [List.sum_cons]

end Flean
