import Mathlib

/- verified submission -/
theorem abelian_surjective_add_id_star_commute
    {A : Type*} [AddCommGroup A] (φ : A →+ A)
    (hφ : Function.Surjective φ) :
    let ψ : A → A := fun a ↦ φ a + a
    Function.Commute φ ψ ∧
      ∀ x y : A, ψ x = φ y → ∃! z : A, φ z = x ∧ ψ z = y := by
  let ψ : A → A := fun a ↦ φ a + a
  constructor
  · intro a
    change φ (ψ a) = ψ (φ a)
    dsimp [ψ]
    simp [map_add, add_comm]
  · intro x y hxy
    have hxy' : ψ x = φ y := hxy
    refine ⟨y - x, ?_, ?_⟩
    · constructor
      · calc
          φ (y - x) = φ y - φ x := AddMonoidHom.map_sub φ y x
          _ = ψ x - φ x := by rw [← hxy']
          _ = x := by
            dsimp [ψ]
            abel
      · calc
          ψ (y - x) = φ (y - x) + (y - x) := rfl
          _ = x + (y - x) := by
            congr 1
            calc
              φ (y - x) = φ y - φ x := AddMonoidHom.map_sub φ y x
              _ = ψ x - φ x := by rw [← hxy']
              _ = x := by
                dsimp [ψ]
                abel
          _ = y := by abel
    · intro z hz
      have hzψ : ψ z = y := hz.2
      calc
        z = ψ z - φ z := by
          dsimp [ψ]
          abel
        _ = y - x := by rw [hzψ, hz.1]
