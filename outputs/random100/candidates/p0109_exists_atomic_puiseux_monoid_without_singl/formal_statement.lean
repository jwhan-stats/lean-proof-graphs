theorem exists_atomic_puiseux_monoid_without_singleton_two_lengths :
    ∃ M : AddSubmonoid ℚ≥0,
      (∀ x : M, ∃ l : List M,
        (∀ a ∈ l, AddIrreducible a) ∧ l.sum = x) ∧
      (∀ x : M,
        {n : ℕ | ∃ l : List M,
          l.length = n ∧ (∀ a ∈ l, AddIrreducible a) ∧ l.sum = x} ≠ {2}) := by sorry
