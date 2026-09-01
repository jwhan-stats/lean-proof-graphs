import Mathlib

/- accepted add_to_file helper 1 -/
lemma isGreatest_grid_lower_sup_right {α : Type*} [LinearOrder α]
    {Q : Finset α} {x y y' : α}
    (hx : IsGreatest {a : α | a ∈ Q ∧ a ≤ x} y)
    (hy' : y' ∈ Q) (hyy' : y ≤ y') :
    IsGreatest {a : α | a ∈ Q ∧ a ≤ y' ⊔ x} y' := by
  constructor
  · exact ⟨hy', le_sup_left⟩
  · intro a ha
    rcases ha with ⟨haQ, hle⟩
    rcases (le_sup_iff.mp hle) with hay' | hax
    · exact hay'
    · exact (hx.2 ⟨haQ, hax⟩).trans hyy'

lemma isGreatest_grid_lower_sup {α : Type*} [LinearOrder α]
    {Q : Finset α} {x z y : α}
    (hx : IsGreatest {a : α | a ∈ Q ∧ a ≤ x} y)
    (hz : IsGreatest {a : α | a ∈ Q ∧ a ≤ z} y) :
    IsGreatest {a : α | a ∈ Q ∧ a ≤ x ⊔ z} y := by
  constructor
  · exact ⟨hx.1.1, le_trans hx.1.2 le_sup_left⟩
  · intro a ha
    rcases ha with ⟨haQ, hle⟩
    rcases (le_sup_iff.mp hle) with hax | haz
    · exact hx.2 ⟨haQ, hax⟩
    · exact hz.2 ⟨haQ, haz⟩

lemma isGreatest_grid_lower_inf {α : Type*} [LinearOrder α]
    {Q : Finset α} {x z y : α}
    (hx : IsGreatest {a : α | a ∈ Q ∧ a ≤ x} y)
    (hz : IsGreatest {a : α | a ∈ Q ∧ a ≤ z} y) :
    IsGreatest {a : α | a ∈ Q ∧ a ≤ x ⊓ z} y := by
  constructor
  · exact ⟨hx.1.1, le_inf hx.1.2 hz.1.2⟩
  · intro a ha
    rcases ha with ⟨haQ, hle⟩
    exact hx.2 ⟨haQ, le_trans hle inf_le_left⟩

/- verified submission -/
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
      ∀ y ∈ grid, IsSublattice (cell y) := by
  dsimp only
  constructor
  · intro x y y' hx hy' hyy'
    have hjoin : y' ⊔ x ∈
        {x | (∃ q ∈ ({q | ∀ i, q i ∈ Q i} : Set (∀ i, T i)), q ≤ x) ∧
          ∀ i, IsGreatest {a : T i | a ∈ Q i ∧ a ≤ x i} (y' i)} := by
      constructor
      · rcases hx.1 with ⟨q, hq, hqx⟩
        exact ⟨q, hq, hqx.trans le_sup_right⟩
      · intro i
        exact isGreatest_grid_lower_sup_right (hx.2 i) (hy' i) (hyy' i)
    exact ⟨hjoin, y' ⊔ x, hjoin, le_sup_right⟩
  · intro y hy
    refine IsSublattice.mk ?_ ?_
    · intro x hx z hz
      constructor
      · rcases hx.1 with ⟨q, hq, hqx⟩
        rcases hz.1 with ⟨r, hr, hrz⟩
        refine ⟨q ⊔ r, ?_, ?_⟩
        · intro i
          rcases max_choice (q i) (r i) with hmax | hmax
          · rw [Pi.sup_apply, hmax]
            exact hq i
          · rw [Pi.sup_apply, hmax]
            exact hr i
        · exact sup_le (hqx.trans le_sup_left) (hrz.trans le_sup_right)
      · intro i
        exact isGreatest_grid_lower_sup (hx.2 i) (hz.2 i)
    · intro x hx z hz
      constructor
      · rcases hx.1 with ⟨q, hq, hqx⟩
        rcases hz.1 with ⟨r, hr, hrz⟩
        refine ⟨q ⊓ r, ?_, ?_⟩
        · intro i
          rcases min_choice (q i) (r i) with hmin | hmin
          · rw [Pi.inf_apply, hmin]
            exact hq i
          · rw [Pi.inf_apply, hmin]
            exact hr i
        · exact le_inf (inf_le_left.trans hqx) (inf_le_right.trans hrz)
      · intro i
        exact isGreatest_grid_lower_inf (hx.2 i) (hz.2 i)
