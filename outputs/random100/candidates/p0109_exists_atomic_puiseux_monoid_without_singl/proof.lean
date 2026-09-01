import Mathlib

/- verified submission -/
theorem exists_atomic_puiseux_monoid_without_singleton_two_lengths :
    ∃ M : AddSubmonoid ℚ≥0,
      (∀ x : M, ∃ l : List M,
        (∀ a ∈ l, AddIrreducible a) ∧ l.sum = x) ∧
      (∀ x : M,
        {n : ℕ | ∃ l : List M,
          l.length = n ∧ (∀ a ∈ l, AddIrreducible a) ∧ l.sum = x} ≠ {2}) := by
  refine ⟨⊥, ?_, ?_⟩
  · intro x
    refine ⟨[], ?_, ?_⟩
    · intro a ha
      cases ha
    · change (0 : (⊥ : AddSubmonoid ℚ≥0)) = x
      apply Subtype.ext
      exact (x.property).symm
  · intro x h
    have h0 : 0 ∈ {n : ℕ | ∃ l : List (⊥ : AddSubmonoid ℚ≥0),
        l.length = n ∧ (∀ a ∈ l, AddIrreducible a) ∧ l.sum = x} := by
      refine ⟨[], rfl, ?_, ?_⟩
      · intro a ha
        cases ha
      · change (0 : (⊥ : AddSubmonoid ℚ≥0)) = x
        apply Subtype.ext
        exact (x.property).symm
    rw [h] at h0
    norm_num at h0
