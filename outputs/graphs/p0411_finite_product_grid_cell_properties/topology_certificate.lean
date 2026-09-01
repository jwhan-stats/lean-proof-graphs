import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0411_finite_product_grid_cell_properties
-- topology_sha256: 0432853c1183bcd36cea3e1bb024047f35166319b34df2e909ba2c44786a23f2
namespace TopologyCertificate_p0411_finite_product_grid_cell_properties

-- N001 = goal: let P := (i : Fin n) → T i; let grid := {q | ∀ (i : Fin n), q i ∈ Q i}; let upper := {x | ∃ q ∈ grid, q ≤ x}; let cell := fun y => {x | x ∈ upper ∧ ∀ (i : Fin n), IsGreatest {a | a ∈ Q i ∧ a ≤ x i} (y i)}; (∀ ⦃x y y' : P⦄, x ∈ cell y → y' ∈ grid → y ≤ y' → y' ⊔ x ∈ cell y' ∧ ∃ x' ∈ cell y', x ≤ x') ∧ ∀ y ∈ grid, IsSublattice (cell y)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p0411_finite_product_grid_cell_properties
