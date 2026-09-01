import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2625_probability_measure_open_unit_interval_uni
-- topology_sha256: dfdaca984d8be8d649400da403019345f48213505b8a9db6b531bfc4b03b4ea3
namespace TopologyCertificate_p2625_probability_measure_open_unit_interval_uni

-- N001 = inst._@.proofs.1292248354._hygCtx._hyg.13: MeasureTheory.IsProbabilityMeasure μ
-- N002 = hcontIcc: ContinuousOn F (Set.Icc (1 / 4) 1)
-- N003 = hF14: F (1 / 4) < 1
-- N004 = hF1: 1 < F 1
-- N005 = h1mem: 1 ∈ Set.Ioo (F (1 / 4)) (F 1)
-- N006 = himage: 1 ∈ F '' Set.Ioo (1 / 4) 1
-- N007 = goal: ∃ s, 0 < s ∧ s < 1 ∧ ∫ (x : ↑(Set.Ioo 0 1)), (Real.exp (s * (1 - ↑x)) - 1) / (1 - ↑x) ∂μ = 1 ∧ ∀ (t : ℝ), 0 < t → ∫ (x : ↑(Set.Ioo 0 1)), (Real.exp (t * (1 - ↑x)) - 1) / (1 - ↑x) ∂μ = 1 → t = s

-- E001 represents h_001_hconticc
-- E002 represents h_002_hf14
-- E003 represents h_003_hf1
-- E004 represents h_004_h1mem
-- E005 represents h_005_himage
-- E006 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    (E002 : N001 → N003)
    (E003 : N001 → N004)
    (E004 : N003 → N004 → N005)
    (E005 : N002 → N005 → N006)
    (E006 : N001 → N006 → N007)
    : N007 := by
  have H_N002 : N002 := E001 B001
  have H_N003 : N003 := E002 B001
  have H_N004 : N004 := E003 B001
  have H_N005 : N005 := E004 H_N003 H_N004
  have H_N006 : N006 := E005 H_N002 H_N005
  have H_N007 : N007 := E006 B001 H_N006
  exact H_N007

end TopologyCertificate_p2625_probability_measure_open_unit_interval_uni
