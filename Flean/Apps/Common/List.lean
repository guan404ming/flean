import Mathlib.Data.List.Defs

namespace Flean

theorem listForall_cons {α : Type} {p : α → Prop} {x : α} {xs : List α}
    (h : List.Forall p (x :: xs)) : p x ∧ List.Forall p xs := by
  cases xs with
  | nil =>
      simpa [List.Forall] using h
  | cons y ys =>
      simpa [List.Forall] using h

end Flean
