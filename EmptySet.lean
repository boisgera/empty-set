import Mathlib

#check Set.nonempty_iff_ne_empty

-- Let's prove this theorem from scratch

theorem ne_empty_of_nonempty {α : Type} (s : Set α) : Set.Nonempty s -> s ≠ ∅ := by
  intro ⟨x, x_in_s⟩
  intro s_empty
  rw [s_empty] at x_in_s
  have x_in_empty := x_in_s
  rw [Set.empty_def] at x_in_empty
  rw [Set.mem_setOf_eq] at x_in_empty
  assumption

theorem nonempty_of_ne_empty {α : Type} (s : Set α) : s ≠ ∅ -> Set.Nonempty s := by
  contrapose
  rw[not_not]
  rw[Set.Nonempty]
  simp only [not_exists]
  intro h
  ext y
  rw[Set.empty_def, Set.mem_setOf_eq]
  simp only [iff_false]
  have y_not_in_s := h y
  assumption

theorem nonempty_iff_ne_empty {α : Type} (s : Set α) : Set.Nonempty s <-> s ≠ ∅ :=
  Iff.intro (ne_empty_of_nonempty s) (nonempty_of_ne_empty s)
