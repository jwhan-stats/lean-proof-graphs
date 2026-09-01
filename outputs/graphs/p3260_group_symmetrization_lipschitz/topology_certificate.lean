import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p3260_group_symmetrization_lipschitz
-- topology_sha256: 98cc2ec8af7eb795746b45890d773629394f9177fe3dbdba47ff1373fbbd3200
namespace TopologyCertificate_p3260_group_symmetrization_lipschitz

-- N001 = hact: ∀ (g : G) (x y : ↑X), ‖↑(g • x) - ↑(g • y)‖ ≤ ‖↑x - ↑y‖
-- N002 = hf: ∀ (x y : ↑X), |f x - f y| ≤ L * ‖↑x - ↑y‖
-- N003 = hL: 0 ≤ L
-- N004 = hCpos: 0 < C
-- N005 = hterm: ∀ (g : G), |f (g • x) - f (g • y)| ≤ L * ‖↑x - ↑y‖
-- N006 = hsum: |∑ g, f (g • x) - ∑ g, f (g • y)| ≤ C * (L * ‖↑x - ↑y‖)
-- N007 = hdiv: |(∑ g, f (g • x)) / C - (∑ g, f (g • y)) / C| ≤ L * ‖↑x - ↑y‖
-- N008 = goal: |(∑ g, f (g • x)) / C - (∑ g, f (g • y)) / C| ≤ L * ‖↑x - ↑y‖

-- E001 represents h_001_hcpos
-- E002 represents h_002_hterm
-- E003 represents h_003_hsum
-- E004 represents h_004_hdiv
-- E005 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (N008 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N004)
    (E002 : N001 → N003 → N002 → N005)
    (E003 : N005 → N006)
    (E004 : N004 → N006 → N007)
    (E005 : N007 → N008)
    : N008 := by
  have H_N004 : N004 := E001
  have H_N005 : N005 := E002 B001 B003 B002
  have H_N006 : N006 := E003 H_N005
  have H_N007 : N007 := E004 H_N004 H_N006
  have H_N008 : N008 := E005 H_N007
  exact H_N008

end TopologyCertificate_p3260_group_symmetrization_lipschitz
