import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2342_c0singlezero_apply
-- topology_sha256: 21795638089805f2200533f25659a7f89ca729fc135727d8148dab9b2ca30161
namespace TopologyCertificate_p2342_c0singlezero_apply

-- N001 = goal: (Rollout_p2342_c0singlezero_apply.c0SingleZero x) n = (Rollout_p2342_c0singlezero_apply.c0SingleZero x) n

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p2342_c0singlezero_apply
