import Mathlib

/- verified submission -/
lemma rightIdeal_subset_of_units
    {R : Type*} [Ring R] {b d : R} (u v : Rˣ)
    (h : Set.range (fun y : R => b * y) ⊆ Set.range (fun y : R => d * y)) :
    Set.range (fun y : R => ((u : R) * b * (v : R)) * y) ⊆
      Set.range (fun y : R => ((u : R) * d * (v : R)) * y) := by
  intro z hz
  rcases hz with ⟨y, rfl⟩
  have hb : b * ((v : R) * y) ∈ Set.range (fun y : R => d * y) := by
    exact h ⟨((v : R) * y), rfl⟩
  rcases hb with ⟨w, hw⟩
  use (((v⁻¹ : Rˣ) : R) * w)
  simpa [mul_assoc] using congrArg (fun t : R => (u : R) * t) hw

lemma rightIdeal_eq_of_units
    {R : Type*} [Ring R] {b d : R} (u v : Rˣ)
    (h : Set.range (fun y : R => b * y) = Set.range (fun y : R => d * y)) :
    Set.range (fun y : R => ((u : R) * b * (v : R)) * y) =
      Set.range (fun y : R => ((u : R) * d * (v : R)) * y) := by
  apply Set.Subset.antisymm
  · exact rightIdeal_subset_of_units u v (subset_of_eq h)
  · exact rightIdeal_subset_of_units u v (subset_of_eq h.symm)

lemma leftIdeal_subset_of_units
    {R : Type*} [Ring R] {b d : R} (u v : Rˣ)
    (h : Set.range (fun y : R => y * b) ⊆ Set.range (fun y : R => y * d)) :
    Set.range (fun y : R => y * ((u : R) * b * (v : R))) ⊆
      Set.range (fun y : R => y * ((u : R) * d * (v : R))) := by
  intro z hz
  rcases hz with ⟨y, rfl⟩
  have hb : ((y * (u : R)) * b) ∈ Set.range (fun y : R => y * d) := by
    exact h ⟨(y * (u : R)), rfl⟩
  rcases hb with ⟨w, hw⟩
  use w * (((u⁻¹ : Rˣ) : R))
  simpa [mul_assoc] using congrArg (fun t : R => t * (v : R)) hw

lemma leftIdeal_eq_of_units
    {R : Type*} [Ring R] {b d : R} (u v : Rˣ)
    (h : Set.range (fun y : R => y * b) = Set.range (fun y : R => y * d)) :
    Set.range (fun y : R => y * ((u : R) * b * (v : R))) =
      Set.range (fun y : R => y * ((u : R) * d * (v : R))) := by
  apply Set.Subset.antisymm
  · exact leftIdeal_subset_of_units u v (subset_of_eq h)
  · exact leftIdeal_subset_of_units u v (subset_of_eq h.symm)

theorem inverseAlong_units
    {R : Type*} [Ring R] {a b d : R} (r s : Rˣ)
    (h_inner : b * a * b = b)
    (h_right : Set.range (fun y : R => b * y) = Set.range (fun y : R => d * y))
    (h_left : Set.range (fun y : R => y * b) = Set.range (fun y : R => y * d)) :
    (((r : R) * b * ((s⁻¹ : Rˣ) : R)) *
          ((s : R) * a * ((r⁻¹ : Rˣ) : R)) *
          ((r : R) * b * ((s⁻¹ : Rˣ) : R)) =
        (r : R) * b * ((s⁻¹ : Rˣ) : R)) ∧
      Set.range (fun y : R => ((r : R) * b * ((s⁻¹ : Rˣ) : R)) * y) =
        Set.range (fun y : R => ((r : R) * d * ((s⁻¹ : Rˣ) : R)) * y) ∧
      Set.range (fun y : R => y * ((r : R) * b * ((s⁻¹ : Rˣ) : R))) =
        Set.range (fun y : R => y * ((r : R) * d * ((s⁻¹ : Rˣ) : R))) := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      ((r : R) * b * ((s⁻¹ : Rˣ) : R)) *
          ((s : R) * a * ((r⁻¹ : Rˣ) : R)) *
          ((r : R) * b * ((s⁻¹ : Rˣ) : R))
          = (r : R) * (b * a * b) * ((s⁻¹ : Rˣ) : R) := by
            simp [mul_assoc]
      _ = (r : R) * b * ((s⁻¹ : Rˣ) : R) := by
            simp [h_inner, mul_assoc]
  · exact rightIdeal_eq_of_units r s⁻¹ h_right
  · exact leftIdeal_eq_of_units r s⁻¹ h_left
