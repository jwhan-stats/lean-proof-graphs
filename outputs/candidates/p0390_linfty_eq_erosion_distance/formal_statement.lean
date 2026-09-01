theorem linfty_eq_erosion_distance {X : Type*} (f g : X → ℝ) :
    (⨆ x : X, ENNReal.ofReal |f x - g x|) =
      sInf {d : ENNReal | ∃ ε : NNReal,
        d = (ε : ENNReal) ∧
        ∀ a b : ℝ, a < b →
          g ⁻¹' Set.Icc a b ⊆
              f ⁻¹' Set.Icc (a - (ε : ℝ)) (b + (ε : ℝ)) ∧
          f ⁻¹' Set.Icc a b ⊆
              g ⁻¹' Set.Icc (a - (ε : ℝ)) (b + (ε : ℝ)) } := by sorry
