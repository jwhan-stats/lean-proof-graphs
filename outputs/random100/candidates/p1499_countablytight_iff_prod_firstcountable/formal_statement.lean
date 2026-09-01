theorem countablyTight_iff_prod_firstCountable {X : Type u} [TopologicalSpace X] :
    (∀ (A : Set X) (x : X), x ∈ closure A →
      ∃ B : Set X, B ⊆ A ∧ B.Countable ∧ x ∈ closure B) ↔
      ∀ (Y : Type v) [TopologicalSpace Y] [FirstCountableTopology Y],
        ∀ (A : Set (X × Y)) (p : X × Y), p ∈ closure A →
          ∃ B : Set (X × Y), B ⊆ A ∧ B.Countable ∧ p ∈ closure B := by sorry
