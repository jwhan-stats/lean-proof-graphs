theorem finite_product_grid_cell_properties
    (n : ℕ) (T : Fin n → Type*) [∀ i, LinearOrder (T i)]
    [∀ i, Nontrivial (T i)] (Q : ∀ i, Finset (T i)) :
    let P := ∀ i, T i
    let grid : Set P := {q | ∀ i, q i ∈ Q i}
    let upper : Set P := {x | ∃ q ∈ grid, q ≤ x}
    let cell (y : P) : Set P :=
      {x | x ∈ upper ∧ ∀ i, IsGreatest {a : T i | a ∈ Q i ∧ a ≤ x i} (y i)}
    (∀ ⦃x y y' : P⦄, x ∈ cell y → y' ∈ grid → y ≤ y' →
        y' ⊔ x ∈ cell y' ∧ ∃ x' ∈ cell y', x ≤ x') ∧
      ∀ y ∈ grid, IsSublattice (cell y) := by sorry
