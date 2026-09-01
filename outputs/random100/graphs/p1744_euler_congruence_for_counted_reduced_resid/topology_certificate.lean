import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1744_euler_congruence_for_counted_reduced_resid
-- topology_sha256: 28dc7b12bcf67d899a4a1555e8b39cf898bb49fb686730674b97db4492424394
namespace TopologyCertificate_p1744_euler_congruence_for_counted_reduced_resid

-- N001 = hcoprime: x.Coprime N
-- N002 = hn: n = {a ∈ Finset.Ico 1 N | a.Coprime N}.card
-- N003 = hN: 0 < N
-- N004 = goal: x ^ n ≡ 1 [MOD N]

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N003 → N001 → N002 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B003 B001 B002
  exact H_N004

end TopologyCertificate_p1744_euler_congruence_for_counted_reduced_resid
