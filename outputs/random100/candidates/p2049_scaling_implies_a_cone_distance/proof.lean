import Mathlib

/- accepted add_to_file helper 1 -/
section ConeDistanceHelpers

variable {C X : Type*} [MetricSpace C]
variable (q : X × NNReal → C)

lemma cone_unit_dist_sq_mem_Icc
    (hbound : ∀ (x₀ x₁ : X), x₀ ≠ x₁ →
      0 < dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ∧
        dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ≤ 4)
    (x y : X) :
    dist (q (x, 1)) (q (y, 1)) ^ 2 ∈ Set.Icc (0 : ℝ) 4 := by
  by_cases hxy : x = y
  · subst y
    simp
  · exact ⟨(hbound x y hxy).1.le, (hbound x y hxy).2⟩

lemma cone_angle_mem_Icc (x y : X) :
    Real.arccos (1 - dist (q (x, 1)) (q (y, 1)) ^ 2 / 2) ∈
      Set.Icc (0 : ℝ) Real.pi := by
  exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

lemma cone_cos_angle
    (hbound : ∀ (x₀ x₁ : X), x₀ ≠ x₁ →
      0 < dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ∧
        dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ≤ 4)
    (x y : X) :
    Real.cos (Real.arccos (1 - dist (q (x, 1)) (q (y, 1)) ^ 2 / 2)) =
      1 - dist (q (x, 1)) (q (y, 1)) ^ 2 / 2 := by
  have h := cone_unit_dist_sq_mem_Icc (C:=C) (X:=X) q hbound x y
  rw [Set.mem_Icc] at h
  apply Real.cos_arccos
  · linarith
  · linarith

lemma cone_angle_self (x : X) :
    Real.arccos (1 - dist (q (x, 1)) (q (x, 1)) ^ 2 / 2) = 0 := by
  simp

lemma cone_angle_comm (x y : X) :
    Real.arccos (1 - dist (q (x, 1)) (q (y, 1)) ^ 2 / 2) =
      Real.arccos (1 - dist (q (y, 1)) (q (x, 1)) ^ 2 / 2) := by
  rw [dist_comm]

lemma cone_angle_eq_zero_iff
    (hbound : ∀ (x₀ x₁ : X), x₀ ≠ x₁ →
      0 < dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ∧
        dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ≤ 4)
    (x y : X) :
    Real.arccos (1 - dist (q (x, 1)) (q (y, 1)) ^ 2 / 2) = 0 ↔ x = y := by
  constructor
  · intro hθ
    by_contra hxy
    have hb := hbound x y hxy
    have hcos := cone_cos_angle (C:=C) (X:=X) q hbound x y
    rw [hθ, Real.cos_zero] at hcos
    nlinarith
  · intro hxy
    subst y
    exact cone_angle_self (C:=C) q x

lemma cone_dist_sq
    (hscale : ∀ (x₀ x₁ : X) (r₀ r₁ : NNReal),
      dist (q (x₀, r₀)) (q (x₁, r₁)) ^ 2 =
        (r₀ : ℝ) * (r₁ : ℝ) * dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 +
          ((r₀ : ℝ) - (r₁ : ℝ)) ^ 2)
    (hbound : ∀ (x₀ x₁ : X), x₀ ≠ x₁ →
      0 < dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ∧
        dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ≤ 4)
    (x y : X) (r s : NNReal) :
    dist (q (x, r)) (q (y, s)) ^ 2 =
      (r : ℝ) ^ 2 + (s : ℝ) ^ 2 -
        2 * (r : ℝ) * (s : ℝ) *
          Real.cos (Real.arccos (1 - dist (q (x, 1)) (q (y, 1)) ^ 2 / 2)) := by
  rw [hscale x y r s, cone_cos_angle (C:=C) (X:=X) q hbound x y]
  ring

end ConeDistanceHelpers

/- accepted add_to_file helper 2 -/
lemma cone_path_sq_eq_aux (A B L M : ℝ)
    (hA : 0 < Real.sin A)
    (hL : L ^ 2 = (Real.sin B / Real.sin A)^2 +
      (Real.sin (A+B)/(2*Real.sin A))^2 -
      2*(Real.sin B / Real.sin A)*(Real.sin (A+B)/(2*Real.sin A))*Real.cos A)
    (hM : M ^ 2 = (Real.sin (A+B)/(2*Real.sin A))^2 + 1 -
      2*(Real.sin (A+B)/(2*Real.sin A))*1*Real.cos B) :
    L ^ 2 = M ^ 2 := by
  rw [hL,hM]
  field_simp [ne_of_gt hA]
  rw [Real.sin_add A B]
  nlinarith [Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B]

lemma cone_path_sum_sq_aux (A B L : ℝ)
    (hA : 0 < Real.sin A)
    (hL : L ^ 2 = (Real.sin B / Real.sin A)^2 +
      (Real.sin (A+B)/(2*Real.sin A))^2 -
      2*(Real.sin B / Real.sin A)*(Real.sin (A+B)/(2*Real.sin A))*Real.cos A) :
    (L + L)^2 = (Real.sin B / Real.sin A)^2 + 1 -
      2*(Real.sin B / Real.sin A)*1*Real.cos (A+B) := by
  rw [Real.sin_add A B] at hL
  field_simp [ne_of_gt hA] at hL
  rw [Real.cos_add A B]
  rw [show (L + L)^2 = 4 * L^2 by ring]
  field_simp [ne_of_gt hA]
  nlinarith [hL, Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B]

/- accepted add_to_file helper 3 -/
section ConeDistanceTriangle

variable {C X : Type*} [MetricSpace C]
variable (q : X × NNReal → C)

lemma cone_angle_triangle
    (hscale : ∀ (x₀ x₁ : X) (r₀ r₁ : NNReal),
      dist (q (x₀, r₀)) (q (x₁, r₁)) ^ 2 =
        (r₀ : ℝ) * (r₁ : ℝ) * dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 +
          ((r₀ : ℝ) - (r₁ : ℝ)) ^ 2)
    (hbound : ∀ (x₀ x₁ : X), x₀ ≠ x₁ →
      0 < dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ∧
        dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ≤ 4)
    (x y z : X) :
    Real.arccos (1 - dist (q (x, 1)) (q (z, 1)) ^ 2 / 2) ≤
      Real.arccos (1 - dist (q (x, 1)) (q (y, 1)) ^ 2 / 2) +
        Real.arccos (1 - dist (q (y, 1)) (q (z, 1)) ^ 2 / 2) := by
  by_cases hxy : x = y
  · subst y
    rw [cone_angle_self (C:=C) q x]
    simp
  by_cases hyz : y = z
  · subst z
    rw [cone_angle_self (C:=C) q y]
    simp
  let a := Real.arccos (1 - dist (q (x, 1)) (q (y, 1)) ^ 2 / 2)
  let b := Real.arccos (1 - dist (q (y, 1)) (q (z, 1)) ^ 2 / 2)
  let c := Real.arccos (1 - dist (q (x, 1)) (q (z, 1)) ^ 2 / 2)
  have haI : a ∈ Set.Icc (0 : ℝ) Real.pi := cone_angle_mem_Icc (C:=C) q x y
  have hbI : b ∈ Set.Icc (0 : ℝ) Real.pi := cone_angle_mem_Icc (C:=C) q y z
  have hcI : c ∈ Set.Icc (0 : ℝ) Real.pi := cone_angle_mem_Icc (C:=C) q x z
  rw [Set.mem_Icc] at haI hbI hcI
  have hane : a ≠ 0 := by
    intro ha
    exact hxy ((cone_angle_eq_zero_iff (C:=C) q hbound x y).mp ha)
  have hbne : b ≠ 0 := by
    intro hb
    exact hyz ((cone_angle_eq_zero_iff (C:=C) q hbound y z).mp hb)
  have hapos : 0 < a := lt_of_le_of_ne haI.1 (Ne.symm hane)
  have hbpos : 0 < b := lt_of_le_of_ne hbI.1 (Ne.symm hbne)
  by_cases hsum : Real.pi ≤ a + b
  · exact le_trans hcI.2 hsum
  · have hslt : a + b < Real.pi := lt_of_not_ge hsum
    by_contra hcle
    have hgt : a + b < c := lt_of_not_ge hcle
    have hspos : 0 < a + b := add_pos hapos hbpos
    have halt : a < Real.pi := by nlinarith
    have hblt : b < Real.pi := by nlinarith
    have hsinA : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi hapos halt
    have hsinB : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hbpos hblt
    have hsinS : 0 < Real.sin (a + b) := Real.sin_pos_of_pos_of_lt_pi hspos hslt
    let rv : ℝ := Real.sin b / Real.sin a
    let tv : ℝ := Real.sin (a + b) / (2 * Real.sin a)
    have hrvpos : 0 < rv := div_pos hsinB hsinA
    have htvpos : 0 < tv := div_pos hsinS (by positivity)
    let r : NNReal := ⟨rv, le_of_lt hrvpos⟩
    let t : NNReal := ⟨tv, le_of_lt htvpos⟩
    let D : ℝ := dist (q (x, r)) (q (z, 1))
    let L : ℝ := dist (q (x, r)) (q (y, t))
    let M : ℝ := dist (q (y, t)) (q (z, 1))
    have htri : D ≤ L + M := dist_triangle _ _ _
    have hD : D ^ 2 = rv ^ 2 + (1 : ℝ) ^ 2 -
        2 * rv * (1 : ℝ) * Real.cos c := by
      have h := cone_dist_sq (C:=C) q hscale hbound x z r 1
      change D ^ 2 = (r : ℝ) ^ 2 + ((1 : NNReal) : ℝ) ^ 2 -
        2 * (r : ℝ) * (((1 : NNReal) : ℝ)) * Real.cos c at h
      simpa [rv] using h
    have hL : L ^ 2 = rv ^ 2 + tv ^ 2 -
        2 * rv * tv * Real.cos a := by
      have h := cone_dist_sq (C:=C) q hscale hbound x y r t
      change L ^ 2 = (r : ℝ) ^ 2 + (t : ℝ) ^ 2 -
        2 * (r : ℝ) * (t : ℝ) * Real.cos a at h
      simpa [rv, tv] using h
    have hM : M ^ 2 = tv ^ 2 + (1 : ℝ) ^ 2 -
        2 * tv * (1 : ℝ) * Real.cos b := by
      have h := cone_dist_sq (C:=C) q hscale hbound y z t 1
      change M ^ 2 = (t : ℝ) ^ 2 + ((1 : NNReal) : ℝ) ^ 2 -
        2 * (t : ℝ) * (((1 : NNReal) : ℝ)) * Real.cos b at h
      simpa [tv] using h
    have hL' : L ^ 2 = (Real.sin b / Real.sin a)^2 +
        (Real.sin (a+b)/(2*Real.sin a))^2 -
        2*(Real.sin b / Real.sin a)*(Real.sin (a+b)/(2*Real.sin a))*Real.cos a := by
      simpa [rv, tv] using hL
    have hM' : M ^ 2 = (Real.sin (a+b)/(2*Real.sin a))^2 + 1 -
        2*(Real.sin (a+b)/(2*Real.sin a))*1*Real.cos b := by
      simpa [tv] using hM
    have hsqLM : L ^ 2 = M ^ 2 :=
      cone_path_sq_eq_aux a b L M hsinA hL' hM'
    have hLM : L = M := by
      have habs := (sq_eq_sq_iff_abs_eq_abs L M).mp hsqLM
      rwa [abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg] at habs
    have hsumsq' := cone_path_sum_sq_aux a b L hsinA hL'
    have hsumsq : (L + M) ^ 2 = rv ^ 2 + 1 -
        2 * rv * (1 : ℝ) * Real.cos (a + b) := by
      rw [show M = L from hLM.symm]
      simpa [rv] using hsumsq'
    have htri_sq : D ^ 2 ≤ (L + M) ^ 2 :=
      pow_le_pow_left₀ dist_nonneg htri 2
    rw [hsumsq] at htri_sq
    have hcoss : Real.cos c < Real.cos (a + b) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (le_of_lt hspos) hcI.2 hgt
    have hDgt : rv ^ 2 + 1 - 2 * rv * (1 : ℝ) * Real.cos (a + b) < D ^ 2 := by
      rw [hD]
      have hmul := mul_lt_mul_of_pos_left hcoss hrvpos
      nlinarith
    nlinarith

end ConeDistanceTriangle

/- verified submission -/
theorem scaling_implies_a_cone_distance
    {C X : Type*} [MetricSpace C]
    (q : X × NNReal → C)
    (hq : Function.Surjective q)
    (hscale : ∀ (x₀ x₁ : X) (r₀ r₁ : NNReal),
      dist (q (x₀, r₀)) (q (x₁, r₁)) ^ 2 =
        (r₀ : ℝ) * (r₁ : ℝ) * dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 +
          ((r₀ : ℝ) - (r₁ : ℝ)) ^ 2)
    (hbound : ∀ (x₀ x₁ : X), x₀ ≠ x₁ →
      0 < dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ∧
        dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ≤ 4) :
    let d_X : X × X → ℝ := fun p =>
      Real.arccos (1 - dist (q (p.1, 1)) (q (p.2, 1)) ^ 2 / 2);
    (∀ x₀ x₁ : X, d_X (x₀, x₁) ∈ Set.Icc (0 : ℝ) Real.pi) ∧
      (∃ m : MetricSpace X, ∀ x₀ x₁ : X,
        @dist X m.toPseudoMetricSpace.toDist x₀ x₁ = d_X (x₀, x₁)) ∧
      ∀ (x₀ x₁ : X) (r₀ r₁ : NNReal),
        dist (q (x₀, r₀)) (q (x₁, r₁)) ^ 2 =
          (r₀ : ℝ) ^ 2 + (r₁ : ℝ) ^ 2 -
            2 * (r₀ : ℝ) * (r₁ : ℝ) * Real.cos (d_X (x₀, x₁)) := by
  let dX : X × X → ℝ := fun p =>
    Real.arccos (1 - dist (q (p.1, 1)) (q (p.2, 1)) ^ 2 / 2)
  change (∀ x₀ x₁ : X, dX (x₀, x₁) ∈ Set.Icc (0 : ℝ) Real.pi) ∧
    (∃ m : MetricSpace X, ∀ x₀ x₁ : X,
      @dist X m.toPseudoMetricSpace.toDist x₀ x₁ = dX (x₀, x₁)) ∧
    ∀ (x₀ x₁ : X) (r₀ r₁ : NNReal),
      dist (q (x₀, r₀)) (q (x₁, r₁)) ^ 2 =
        (r₀ : ℝ) ^ 2 + (r₁ : ℝ) ^ 2 -
          2 * (r₀ : ℝ) * (r₁ : ℝ) * Real.cos (dX (x₀, x₁))
  let θ : X → X → ℝ := fun x y => dX (x, y)
  have hself : ∀ x : X, θ x x = 0 := by
    intro x
    exact cone_angle_self (C:=C) q x
  have hcomm : ∀ x y : X, θ x y = θ y x := by
    intro x y
    exact cone_angle_comm (C:=C) q x y
  have htriangle : ∀ x y z : X, θ x z ≤ θ x y + θ y z := by
    intro x y z
    exact cone_angle_triangle (C:=C) q hscale hbound x y z
  letI dinst : Dist X := ⟨θ⟩
  letI pms : PseudoMetricSpace X := {
    dist_self := hself
    dist_comm := hcomm
    dist_triangle := htriangle
  }
  let ms : MetricSpace X := MetricSpace.mk (by
    intro x y hxy
    exact (cone_angle_eq_zero_iff (C:=C) q hbound x y).mp hxy)
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    exact cone_angle_mem_Icc (C:=C) q x y
  · refine ⟨ms, ?_⟩
    intro x y
    rfl
  · intro x y r s
    exact cone_dist_sq (C:=C) q hscale hbound x y r s
