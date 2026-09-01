import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0912_catlin_vertical_curve_is_geodesic
-- topology_sha256: ff55e243bcb013b3bb1fe2d4b53943a217b77c71844ab85c4d3c84a7f12cdfd5
namespace TopologyCertificate_p0912_catlin_vertical_curve_is_geodesic

-- N001 = ha: 0 < a
-- N002 = hfront: (z₀, w₀) ∈ frontier Ω
-- N003 = hreal: ∀ (z : ℂ), (evalAt z p).im = 0
-- N004 = heval: evalAt = Rollout_p0912_catlin_vertical_curve_is_geodesic.evalDiag
-- N005 = hr: r = Rollout_p0912_catlin_vertical_curve_is_geodesic.catlinR p
-- N006 = hM: M = Rollout_p0912_catlin_vertical_curve_is_geodesic.catlinM m p
-- N007 = hPC: PiecewiseC1 = Rollout_p0912_catlin_vertical_curve_is_geodesic.PiecewiseC1Curve
-- N008 = hrealG: ∀ (z : ℂ), (Rollout_p0912_catlin_vertical_curve_is_geodesic.evalDiag z p).im = 0
-- N009 = hΩdef: Ω = {q | Rollout_p0912_catlin_vertical_curve_is_geodesic.catlinR p q < 0}
-- N010 = hb: Rollout_p0912_catlin_vertical_curve_is_geodesic.catlinR p (z₀, w₀) = 0
-- N011 = goal: (∀ (t : ℝ), σ t ∈ Ω) ∧ ∀ (s t : ℝ), d (σ s) (σ t) = |s - t|

-- E001 represents h_001_heval
-- E002 represents h_006_hr
-- E003 represents h_007_hm
-- E004 represents h_008_hpc
-- E005 represents h_009_hrealg
-- E006 represents h_010_h_def
-- E007 represents h_011_hb
-- E008 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N004)
    (E002 : N005)
    (E003 : N006)
    (E004 : N007)
    (E005 : N003 → N004 → N008)
    (E006 : N005 → N009)
    (E007 : N002 → N009 → N010)
    (E008 : N001 → N006 → N007 → N008 → N009 → N010 → N011)
    : N011 := by
  have H_N004 : N004 := E001
  have H_N005 : N005 := E002
  have H_N006 : N006 := E003
  have H_N007 : N007 := E004
  have H_N008 : N008 := E005 B003 H_N004
  have H_N009 : N009 := E006 H_N005
  have H_N010 : N010 := E007 B002 H_N009
  have H_N011 : N011 := E008 B001 H_N006 H_N007 H_N008 H_N009 H_N010
  exact H_N011

end TopologyCertificate_p0912_catlin_vertical_curve_is_geodesic
