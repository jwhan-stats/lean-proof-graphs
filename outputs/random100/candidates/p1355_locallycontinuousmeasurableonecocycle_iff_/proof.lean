import Mathlib

/- verified submission -/
theorem locallyContinuousMeasurableOneCocycle_iff_continuousCrossedHomomorphism
    {G A : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [DistribMulAction G A] [ContinuousSMul G A]
    [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace A] [BorelSpace A]
    (c : G → A) :
    (Measurable c ∧
        (∀ s t : G, c (s * t) = c s + s • c t) ∧
        ∃ U : Set G, IsOpen U ∧ (1 : G) ∈ U ∧ ContinuousOn c U) ↔
      (Continuous c ∧ ∀ s t : G, c (s * t) = c s + s • c t) := by
  constructor
  · rintro ⟨hmeas, hcoc, U, hUopen, h1U, hcU⟩
    have hc1 : ContinuousAt c 1 := hcU.continuousAt (hUopen.mem_nhds h1U)
    have hcont : Continuous c := by
      rw [continuous_iff_continuousAt]
      intro g
      have hceq : c = fun x => c g + g • c (g⁻¹ * x) := by
        funext x
        calc
          c x = c (g * (g⁻¹ * x)) := by
            congr 1
            rw [← mul_assoc, mul_inv_cancel, one_mul]
          _ = c g + g • c (g⁻¹ * x) := hcoc g (g⁻¹ * x)
      rw [hceq]
      have hgx : ContinuousAt (fun x : G => g⁻¹ * x) g :=
        continuousAt_const.mul continuousAt_id
      have hc1g : ContinuousAt c (g⁻¹ * g) := by
        rw [inv_mul_cancel]
        exact hc1
      have hinner : ContinuousAt (fun x : G => c (g⁻¹ * x)) g :=
        ContinuousAt.comp hc1g hgx
      exact continuousAt_const.add (hinner.const_smul g)
    exact ⟨hcont, hcoc⟩
  · rintro ⟨hcont, hcoc⟩
    exact ⟨hcont.measurable, hcoc, Set.univ, isOpen_univ, Set.mem_univ 1, hcont.continuousOn⟩
