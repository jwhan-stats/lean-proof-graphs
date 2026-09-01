import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0925_tanh_ge_one_sub_exp_neg
-- topology_sha256: c31c7ef38ac30d758d597727d77d1f890e731380163812056eec74da2d1acdf6
namespace TopologyCertificate_p0925_tanh_ge_one_sub_exp_neg

-- N001 = hx: 0 ≤ x
-- N002 = goal: Real.tanh x ≥ 1 - Real.exp (-x)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    : N002 := by
  have H_N002 : N002 := E001 B001
  exact H_N002

end TopologyCertificate_p0925_tanh_ge_one_sub_exp_neg
