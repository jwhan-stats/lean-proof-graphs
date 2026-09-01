import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1193_parseval_frame_spans_orthogonal
-- topology_sha256: 186c22b947cae8b637db1e4cb4152e1e644df8cfea430cf772137e20a4e64fdf
namespace TopologyCertificate_p1193_parseval_frame_spans_orthogonal

-- N001 = hdisjoint: Submodule.span ℝ (φ '' I) ⊓ Submodule.span ℝ (φ '' Iᶜ) = ⊥
-- N002 = hParseval: ∀ (x : EuclideanSpace ℝ (Fin M)), ∑ i, inner ℝ x (φ i) ^ 2 = ‖x‖ ^ 2
-- N003 = hu: u ∈ Submodule.span ℝ (φ '' I)
-- N004 = hv: v ∈ Submodule.span ℝ (φ '' Iᶜ)
-- N005 = hframe: Rollout_p1193_parseval_frame_spans_orthogonal.partialFrame φ Set.univ = LinearMap.id
-- N006 = hSIu_A: SI u ∈ A
-- N007 = hSCu_B: SC u ∈ B
-- N008 = hdecomp: ∀ (x : E), SI x + SC x = x
-- N009 = hSI_zero_on_B: ∀ v ∈ B, SI v = 0
-- N010 = hSCu_A: SC u ∈ A
-- N011 = hSCu_zero: SC u = 0
-- N012 = hSIv: SI v = 0
-- N013 = hSIu: SI u = u
-- N014 = goal: inner ℝ u v = 0

-- E001 represents h_001_hframe
-- E002 represents h_004_hsiu_a
-- E003 represents h_005_hscu_b
-- E004 represents h_002_hdecomp
-- E005 represents h_003_hsi_zero_on_b
-- E006 represents h_006_hscu_a
-- E007 represents h_007_hscu_zero
-- E008 represents h_009_hsiv
-- E009 represents h_008_hsiu
-- E010 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N002 → N005)
    (E002 : N006)
    (E003 : N007)
    (E004 : N005 → N008)
    (E005 : N001 → N008 → N009)
    (E006 : N008 → N003 → N006 → N010)
    (E007 : N001 → N007 → N010 → N011)
    (E008 : N009 → N004 → N012)
    (E009 : N008 → N011 → N013)
    (E010 : N013 → N012 → N014)
    : N014 := by
  have H_N005 : N005 := E001 B002
  have H_N006 : N006 := E002
  have H_N007 : N007 := E003
  have H_N008 : N008 := E004 H_N005
  have H_N009 : N009 := E005 B001 H_N008
  have H_N010 : N010 := E006 H_N008 B003 H_N006
  have H_N011 : N011 := E007 B001 H_N007 H_N010
  have H_N012 : N012 := E008 H_N009 B004
  have H_N013 : N013 := E009 H_N008 H_N011
  have H_N014 : N014 := E010 H_N013 H_N012
  exact H_N014

end TopologyCertificate_p1193_parseval_frame_spans_orthogonal
