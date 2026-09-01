import Mathlib

/- verified submission -/
theorem average_projection_positive_definite
    {n : ℕ} (hn : 1 ≤ n)
    {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (C : ι → Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hC : ⨆ i, C i = ⊤)
    (J : Ω → Finset ι)
    (hproj : Measurable (fun ω =>
      (∑ i ∈ J ω, C i).starProjection))
    (hadm : ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 →
      μ {ω | x ∈ (∑ i ∈ J ω, C i)ᗮ} < 1) :
    ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 →
      0 < inner ℝ x
        ((∫ ω, (∑ i ∈ J ω, C i).starProjection ∂μ) x) := by
  intro x hx
  let K : Ω → Submodule ℝ (EuclideanSpace ℝ (Fin n)) := fun ω => ∑ i ∈ J ω, C i
  have hPint : MeasureTheory.Integrable (fun ω => (K ω).starProjection) μ := by
    refine MeasureTheory.Integrable.of_bound hproj.aestronglyMeasurable 1 ?_
    filter_upwards with ω
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
    intro v
    simpa using Submodule.norm_starProjection_apply_le (K ω) v
  have hφint : MeasureTheory.Integrable (fun ω => (K ω).starProjection x) μ :=
    hPint.apply_continuousLinearMap x
  have hfint : MeasureTheory.Integrable (fun ω => inner ℝ x ((K ω).starProjection x)) μ :=
    MeasureTheory.Integrable.const_inner x hφint
  have hfmeas : Measurable (fun ω => inner ℝ x ((K ω).starProjection x)) :=
    Measurable.const_inner (hproj.apply_continuousLinearMap x)
  have hnonneg : 0 ≤ fun ω => inner ℝ x ((K ω).starProjection x) := by
    intro ω
    have h := Submodule.re_inner_starProjection_nonneg (K ω) x
    convert h using 1
    rw [real_inner_comm]
    rfl
  have hnormsq (ω : Ω) :
      inner ℝ x ((K ω).starProjection x) = ‖(K ω).orthogonalProjection x‖ ^ 2 := by
    have h := Submodule.re_inner_starProjection_eq_normSq (K ω) x
    convert h using 1
    · rw [real_inner_comm]
      rfl
  have hsupp : Function.support (fun ω => inner ℝ x ((K ω).starProjection x)) =
      {ω | x ∈ (K ω)ᗮ}ᶜ := by
    ext ω
    constructor
    · intro hsupport horth
      have hsne : inner ℝ x ((K ω).starProjection x) ≠ 0 := Function.mem_support.mp hsupport
      have hpzero : (K ω).starProjection x = 0 :=
        (Submodule.starProjection_apply_eq_zero_iff (K ω)).2 horth
      exact hsne (by simp [hpzero])
    · intro hnotorth
      rw [Function.mem_support]
      by_contra hinner
      have hsquarezero : ‖(K ω).orthogonalProjection x‖ ^ 2 = 0 := by
        rw [← hnormsq ω, hinner]
      have hprojzero : (K ω).orthogonalProjection x = 0 := by
        have hnormzero : ‖(K ω).orthogonalProjection x‖ = 0 :=
          eq_zero_of_pow_eq_zero hsquarezero
        exact norm_eq_zero.mp hnormzero
      exact hnotorth ((Submodule.orthogonalProjection_eq_zero_iff).1 hprojzero)
  have hbad_meas : MeasurableSet {ω | x ∈ (K ω)ᗮ} := by
    have h := (measurableSet_support hfmeas).compl
    rwa [hsupp, compl_compl] at h
  have hsupp_pos :
      0 < μ (Function.support (fun ω => inner ℝ x ((K ω).starProjection x))) := by
    have hcomp : 0 < μ {ω | x ∈ (K ω)ᗮ}ᶜ := by
      rw [MeasureTheory.prob_compl_eq_one_sub hbad_meas]
      exact tsub_pos_iff_lt.2 (hadm x hx)
    rwa [hsupp]
  have hintpos : 0 < ∫ ω, inner ℝ x ((K ω).starProjection x) ∂μ :=
    (MeasureTheory.integral_pos_iff_support_of_nonneg hnonneg hfint).2 hsupp_pos
  calc
    0 < ∫ ω, inner ℝ x ((K ω).starProjection x) ∂μ := hintpos
    _ = inner ℝ x (∫ ω, (K ω).starProjection x ∂μ) := integral_inner hφint x
    _ = inner ℝ x ((∫ ω, (K ω).starProjection ∂μ) x) := by
      rw [ContinuousLinearMap.integral_apply hPint x]
