import Mathlib

/- accepted add_to_file helper 1 -/
lemma arccot_integrand_hasDerivAt (a x : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun y : ℝ => (1 + a ^ 2) * Real.arctan (y / a) - a * y)
      ((1 - x ^ 2) * a / (a ^ 2 + x ^ 2)) x := by
  have hden : a ^ 2 + x ^ 2 ≠ 0 := by
    positivity
  have hderiv_arctan : HasDerivAt (fun y : ℝ => Real.arctan (y / a)) (a / (a ^ 2 + x ^ 2)) x := by
    have hdiv : HasDerivAt (fun y : ℝ => y / a) (1 / a) x := by
      simpa [div_eq_mul_inv] using (hasDerivAt_id x).mul_const (a⁻¹)
    convert (Real.hasDerivAt_arctan (x / a)).comp x hdiv using 1
    field_simp [ha]
  have hconst := hderiv_arctan.const_mul (1 + a ^ 2)
  have hlin : HasDerivAt (fun y : ℝ => a * y) a x := by
    simpa using (hasDerivAt_id x).const_mul a
  convert hconst.sub hlin using 1
  field_simp [hden]
  ring

lemma asymptotic_integrand_integral_of_ne_zero (a : ℝ) (ha : a ≠ 0) :
    (∫ η in (-1 : ℝ)..1,
      if a = 0 ∧ η = 0 then 0
      else (1 - η ^ 2) * a / (a ^ 2 + η ^ 2)) =
      2 * (1 + a ^ 2) * Real.arctan (1 / a) - 2 * a := by
  let F : ℝ → ℝ := fun x => (1 + a ^ 2) * Real.arctan (x / a) - a * x
  let f' : ℝ → ℝ := fun x => (1 - x ^ 2) * a / (a ^ 2 + x ^ 2)
  have hder : deriv F = f' := by
    funext x
    exact (arccot_integrand_hasDerivAt a x ha).deriv
  have hdiff : ∀ x ∈ Set.uIcc (-1 : ℝ) 1, DifferentiableAt ℝ F x := by
    intro x hx
    exact (arccot_integrand_hasDerivAt a x ha).differentiableAt
  have hcont : ContinuousOn f' (Set.uIcc (-1 : ℝ) 1) := by
    intro x hx
    fun_prop (disch := positivity)
  have hftc := intervalIntegral.integral_deriv_eq_sub' F hder hdiff hcont
  simp [ha, F, f'] at hftc ⊢
  rw [hftc]
  have hneg : Real.arctan (-1 / a) = -Real.arctan (1 / a) := by
    rw [show -1 / a = -(1 / a) by ring, Real.arctan_neg]
  rw [hneg]
  ring

lemma asymptotic_integrand_integral_zero :
    (∫ η in (-1 : ℝ)..1,
      if (0 : ℝ) = 0 ∧ η = 0 then 0
      else (1 - η ^ 2) * (0 : ℝ) / ((0 : ℝ) ^ 2 + η ^ 2)) = 0 := by
  simp

/- verified submission -/
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
            (1 + a ^ 2) + a / Real.pi) := by
  dsimp only
  intro a
  by_cases ha0 : a = 0
  · subst a
    simp [asymptotic_integrand_integral_zero, Real.pi_ne_zero]
    field_simp [Real.pi_ne_zero]
    ring
  · by_cases hneg : a < 0
    · have hI := asymptotic_integrand_integral_of_ne_zero a ha0
      have hrec : Real.arctan (1 / a) = -(Real.pi / 2) - Real.arctan a := by
        simpa [one_div] using Real.arctan_inv_of_neg hneg
      rw [hI, hrec]
      simp [ha0, hneg, Real.pi_ne_zero]
      field_simp [Real.pi_ne_zero]
      ring
    · have hpos : 0 < a := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm ha0)
      have hI := asymptotic_integrand_integral_of_ne_zero a ha0
      have hrec : Real.arctan (1 / a) = Real.pi / 2 - Real.arctan a := by
        simpa [one_div] using Real.arctan_inv_of_pos hpos
      rw [hI, hrec]
      simp [ha0, hneg, Real.pi_ne_zero]
      field_simp [Real.pi_ne_zero]
      ring
