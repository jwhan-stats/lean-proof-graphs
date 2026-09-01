import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1067_complex_exp_modulus_bounds
-- topology_sha256: ae0775c9de803f41c6b91d674b58b5dd7eeb7343638294ca094a3b916b2a3aff
namespace TopologyCertificate_p1067_complex_exp_modulus_bounds

-- N001 = hz: -z.re ≥ ‖z‖ / 2 ∧ -z.re ≥ 3
-- N002 = hexp: 4 * -z.re + 2 ≤ Real.exp (-z.re)
-- N003 = hnormexp: ‖Complex.exp (-z)‖ = Real.exp (-z.re)
-- N004 = hz1: ‖z + 1‖ ≤ 1 / 2 * Real.exp (-z.re)
-- N005 = hlower_core: 1 / 2 * Real.exp (-z.re) ≤ ‖z + 1 + Complex.exp (-z)‖
-- N006 = hupper_core: ‖z + 1 + Complex.exp (-z)‖ ≤ 2 * Real.exp (-z.re)
-- N007 = goal: 1 / 2 * Real.exp (-z.re) ≤ ‖f z‖ ∧ ‖f z‖ ≤ 2 * Real.exp (-z.re)

-- E001 represents h_003_hexp
-- E002 represents h_005_hnormexp
-- E003 represents h_004_hz1
-- E004 represents h_006_hlower_core
-- E005 represents h_007_hupper_core
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
    (E002 : N003)
    (E003 : N001 → N002 → N004)
    (E004 : N004 → N003 → N005)
    (E005 : N001 → N002 → N004 → N003 → N006)
    (E006 : N005 → N006 → N007)
    : N007 := by
  have H_N002 : N002 := E001 B001
  have H_N003 : N003 := E002
  have H_N004 : N004 := E003 B001 H_N002
  have H_N005 : N005 := E004 H_N004 H_N003
  have H_N006 : N006 := E005 B001 H_N002 H_N004 H_N003
  have H_N007 : N007 := E006 H_N005 H_N006
  exact H_N007

end TopologyCertificate_p1067_complex_exp_modulus_bounds
