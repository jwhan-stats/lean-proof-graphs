import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2468_average_projection_positive_definite
-- topology_sha256: fcffa0d1dce110e47494d5dc1748590683433e407aeda54d2ca9aeab626ab31f
namespace TopologyCertificate_p2468_average_projection_positive_definite

-- N001 = hadm: ∀ (x : EuclideanSpace ℝ (Fin n)), x ≠ 0 → μ {ω | x ∈ (∑ i ∈ J ω, C i)ᗮ} < 1
-- N002 = hproj: Measurable fun ω => (∑ i ∈ J ω, C i).starProjection
-- N003 = hx: x ≠ 0
-- N004 = inst._@.proofs.1509888941._hygCtx._hyg.17: MeasureTheory.IsProbabilityMeasure μ
-- N005 = hPint: MeasureTheory.Integrable (fun ω => (K ω).starProjection) μ
-- N006 = hfmeas: Measurable fun ω => inner ℝ x ((K ω).starProjection x)
-- N007 = hnonneg: 0 ≤ fun ω => inner ℝ x ((K ω).starProjection x)
-- N008 = hnormsq: ∀ (ω : Ω), inner ℝ x ((K ω).starProjection x) = ‖(K ω).orthogonalProjection x‖ ^ 2
-- N009 = hφint: MeasureTheory.Integrable (fun ω => (K ω).starProjection x) μ
-- N010 = hsupp: (Function.support fun ω => inner ℝ x ((K ω).starProjection x)) = {ω | x ∈ (K ω)ᗮ}ᶜ
-- N011 = hfint: MeasureTheory.Integrable (fun ω => inner ℝ x ((K ω).starProjection x)) μ
-- N012 = hbad_meas: MeasurableSet {ω | x ∈ (K ω)ᗮ}
-- N013 = hsupp_pos: 0 < μ (Function.support fun ω => inner ℝ x ((K ω).starProjection x))
-- N014 = hintpos: 0 < ∫ (ω : Ω), inner ℝ x ((K ω).starProjection x) ∂μ
-- N015 = goal: 0 < inner ℝ x ((∫ (ω : Ω), (K ω).starProjection ∂μ) x)

-- E001 represents h_001_hpint
-- E002 represents h_004_hfmeas
-- E003 represents h_005_hnonneg
-- E004 represents h_006_hnormsq
-- E005 represents h_002_h_int
-- E006 represents h_007_hsupp
-- E007 represents h_003_hfint
-- E008 represents h_008_hbad_meas
-- E009 represents h_009_hsupp_pos
-- E010 represents h_010_hintpos
-- E011 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (N008 : Prop)
    (N009 : Prop)
    (N010 : Prop)
    (N011 : Prop)
    (N012 : Prop)
    (N013 : Prop)
    (N014 : Prop)
    (N015 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N004 → N002 → N005)
    (E002 : N002 → N006)
    (E003 : N007)
    (E004 : N008)
    (E005 : N005 → N009)
    (E006 : N008 → N010)
    (E007 : N009 → N011)
    (E008 : N006 → N010 → N012)
    (E009 : N004 → N001 → N003 → N010 → N012 → N013)
    (E010 : N011 → N007 → N013 → N014)
    (E011 : N005 → N009 → N014 → N015)
    : N015 := by
  have H_N005 : N005 := E001 B004 B002
  have H_N006 : N006 := E002 B002
  have H_N007 : N007 := E003
  have H_N008 : N008 := E004
  have H_N009 : N009 := E005 H_N005
  have H_N010 : N010 := E006 H_N008
  have H_N011 : N011 := E007 H_N009
  have H_N012 : N012 := E008 H_N006 H_N010
  have H_N013 : N013 := E009 B004 B001 B003 H_N010 H_N012
  have H_N014 : N014 := E010 H_N011 H_N007 H_N013
  have H_N015 : N015 := E011 H_N005 H_N009 H_N014
  exact H_N015

end TopologyCertificate_p2468_average_projection_positive_definite
