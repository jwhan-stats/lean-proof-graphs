import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p2468_average_projection_positive_definite
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: fcffa0d1dce110e47494d5dc1748590683433e407aeda54d2ca9aeab626ab31f
-- reconstructed_proof_sha256: c3c2ee76601932c699ac0058aeec3c0ffcfebd03cf300d82c76c78f06319c2d7
-- selected_edge_count: 11

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


#check_dependency_graph "average_projection_positive_definite" against "{\"edges\":[{\"conclusion\":{\"name\":\"hPint\",\"statement\":\"MeasureTheory.Integrable (fun ω => (K ω).starProjection) μ\"},\"graphEdgeId\":\"h_001_hpint\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"MeasureTheory.IsProbabilityMeasure μ\"},{\"name\":\"hproj\",\"statement\":\"Measurable fun ω => (∑ i ∈ J ω, C i).starProjection\"}],\"rawEdgeId\":\"telescope_15\"},{\"conclusion\":{\"name\":\"hfmeas\",\"statement\":\"Measurable fun ω => inner ℝ x ((K ω).starProjection x)\"},\"graphEdgeId\":\"h_004_hfmeas\",\"premises\":[{\"name\":\"hproj\",\"statement\":\"Measurable fun ω => (∑ i ∈ J ω, C i).starProjection\"}],\"rawEdgeId\":\"telescope_18\"},{\"conclusion\":{\"name\":\"hnonneg\",\"statement\":\"0 ≤ fun ω => inner ℝ x ((K ω).starProjection x)\"},\"graphEdgeId\":\"h_005_hnonneg\",\"premises\":[],\"rawEdgeId\":\"telescope_19\"},{\"conclusion\":{\"name\":\"hnormsq\",\"statement\":\"∀ (ω : Ω), inner ℝ x ((K ω).starProjection x) = ‖(K ω).orthogonalProjection x‖ ^ 2\"},\"graphEdgeId\":\"h_006_hnormsq\",\"premises\":[],\"rawEdgeId\":\"telescope_20\"},{\"conclusion\":{\"name\":\"hφint\",\"statement\":\"MeasureTheory.Integrable (fun ω => (K ω).starProjection x) μ\"},\"graphEdgeId\":\"h_002_h_int\",\"premises\":[{\"name\":\"hPint\",\"statement\":\"MeasureTheory.Integrable (fun ω => (K ω).starProjection) μ\"}],\"rawEdgeId\":\"telescope_16\"},{\"conclusion\":{\"name\":\"hsupp\",\"statement\":\"(Function.support fun ω => inner ℝ x ((K ω).starProjection x)) = {ω | x ∈ (K ω)ᗮ}ᶜ\"},\"graphEdgeId\":\"h_007_hsupp\",\"premises\":[{\"name\":\"hnormsq\",\"statement\":\"∀ (ω : Ω), inner ℝ x ((K ω).starProjection x) = ‖(K ω).orthogonalProjection x‖ ^ 2\"}],\"rawEdgeId\":\"telescope_21\"},{\"conclusion\":{\"name\":\"hfint\",\"statement\":\"MeasureTheory.Integrable (fun ω => inner ℝ x ((K ω).starProjection x)) μ\"},\"graphEdgeId\":\"h_003_hfint\",\"premises\":[{\"name\":\"hφint\",\"statement\":\"MeasureTheory.Integrable (fun ω => (K ω).starProjection x) μ\"}],\"rawEdgeId\":\"telescope_17\"},{\"conclusion\":{\"name\":\"hbad_meas\",\"statement\":\"MeasurableSet {ω | x ∈ (K ω)ᗮ}\"},\"graphEdgeId\":\"h_008_hbad_meas\",\"premises\":[{\"name\":\"hfmeas\",\"statement\":\"Measurable fun ω => inner ℝ x ((K ω).starProjection x)\"},{\"name\":\"hsupp\",\"statement\":\"(Function.support fun ω => inner ℝ x ((K ω).starProjection x)) = {ω | x ∈ (K ω)ᗮ}ᶜ\"}],\"rawEdgeId\":\"telescope_22\"},{\"conclusion\":{\"name\":\"hsupp_pos\",\"statement\":\"0 < μ (Function.support fun ω => inner ℝ x ((K ω).starProjection x))\"},\"graphEdgeId\":\"h_009_hsupp_pos\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"MeasureTheory.IsProbabilityMeasure μ\"},{\"name\":\"hadm\",\"statement\":\"∀ (x : EuclideanSpace ℝ (Fin n)), x ≠ 0 → μ {ω | x ∈ (∑ i ∈ J ω, C i)ᗮ} < 1\"},{\"name\":\"hx\",\"statement\":\"x ≠ 0\"},{\"name\":\"hsupp\",\"statement\":\"(Function.support fun ω => inner ℝ x ((K ω).starProjection x)) = {ω | x ∈ (K ω)ᗮ}ᶜ\"},{\"name\":\"hbad_meas\",\"statement\":\"MeasurableSet {ω | x ∈ (K ω)ᗮ}\"}],\"rawEdgeId\":\"telescope_23\"},{\"conclusion\":{\"name\":\"hintpos\",\"statement\":\"0 < ∫ (ω : Ω), inner ℝ x ((K ω).starProjection x) ∂μ\"},\"graphEdgeId\":\"h_010_hintpos\",\"premises\":[{\"name\":\"hfint\",\"statement\":\"MeasureTheory.Integrable (fun ω => inner ℝ x ((K ω).starProjection x)) μ\"},{\"name\":\"hnonneg\",\"statement\":\"0 ≤ fun ω => inner ℝ x ((K ω).starProjection x)\"},{\"name\":\"hsupp_pos\",\"statement\":\"0 < μ (Function.support fun ω => inner ℝ x ((K ω).starProjection x))\"}],\"rawEdgeId\":\"telescope_24\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"0 < inner ℝ x ((∫ (ω : Ω), (K ω).starProjection ∂μ) x)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hPint\",\"statement\":\"MeasureTheory.Integrable (fun ω => (K ω).starProjection) μ\"},{\"name\":\"hφint\",\"statement\":\"MeasureTheory.Integrable (fun ω => (K ω).starProjection x) μ\"},{\"name\":\"hintpos\",\"statement\":\"0 < ∫ (ω : Ω), inner ℝ x ((K ω).starProjection x) ∂μ\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2468_average_projection_positive_definite\",\"reconstructedProofSha256\":\"c3c2ee76601932c699ac0058aeec3c0ffcfebd03cf300d82c76c78f06319c2d7\",\"selectedEdgeCount\":11,\"theoremName\":\"average_projection_positive_definite\",\"topologySha256\":\"fcffa0d1dce110e47494d5dc1748590683433e407aeda54d2ca9aeab626ab31f\"}"
