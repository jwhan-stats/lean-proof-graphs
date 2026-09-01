theorem dimension_three_evaluation_of_asymptotic_coefficient :
    let H : ℝ → ℝ := fun a => if a < 0 then 0 else if a = 0 then 1 / 2 else 1
    let arccot : ℝ → ℝ := fun a => Real.pi / 2 - Real.arctan a
    let κ : ℝ → ℝ := fun a =>
      (1 / (4 * Real.pi)) *
        (-(1 / (2 * Real.pi)) *
            (∫ η in (-1 : ℝ)..1,
              if a = 0 ∧ η = 0 then 0
              else (1 - η ^ 2) * a / (a ^ 2 + η ^ 2))
          - 1 / 4 + H a * (1 + a ^ 2))
    ∀ a : ℝ,
      κ a =
        (1 / (4 * Real.pi)) *
          (-1 / 4 - (1 + a ^ 2) * arccot a / Real.pi +
            (1 + a ^ 2) + a / Real.pi) := by sorry
