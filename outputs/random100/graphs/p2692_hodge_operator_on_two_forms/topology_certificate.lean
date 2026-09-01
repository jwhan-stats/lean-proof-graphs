import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2692_hodge_operator_on_two_forms
-- topology_sha256: f78a667584570d9c4fb9b59661d293e0d2173c9926ebeb29901dc26023276f9e
namespace TopologyCertificate_p2692_hodge_operator_on_two_forms

-- N001 = h: star e_ab = -e_ab + (2 * μ) • e_bd ∧ star e_ac = e_ac ∧ star e_ad = (1 / (1 + q ^ 2)) • (2 • e_bc - (q ^ 2 * μ) • e_ad) ∧ star e_bc = (q ^ 2 / (1 + q ^ 2)) • (2 • e_ad + μ • e_bc) ∧ star e_bd = e_bd ∧ star e_cd = -e_cd
-- N002 = hq0: q ≠ 0
-- N003 = hq_neg_one: q ^ 2 ≠ -1
-- N004 = goal: star ∘ₗ star = LinearMap.id ∧ (star - LinearMap.id).ker = Submodule.span ℂ {e_bd, e_ac, e_ad + e_bc} ∧ (star + LinearMap.id).ker = Submodule.span ℂ {e_cd, e_ab - μ • e_bd, e_ad - (q ^ 2)⁻¹ • e_bc} ∧ Module.finrank ℂ ↥(star - LinearMap.id).ker = 3 ∧ Module.finrank ℂ ↥(star + LinearMap.id).ker = 3

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N002 → N003 → N001 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B002 B003 B001
  exact H_N004

end TopologyCertificate_p2692_hodge_operator_on_two_forms
