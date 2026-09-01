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
        Set.range (fun y : R => y * ((r : R) * d * ((s⁻¹ : Rˣ) : R))) := by sorry
