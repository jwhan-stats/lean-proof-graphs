import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1318_sequence_triangular_formula
-- topology_sha256: e12f68c590d052a3252704376bcc8420bd334abba0895d8d9e6f14d69b56ebc6
namespace TopologyCertificate_p1318_sequence_triangular_formula

-- N001 = hc₁: c 1 = 2
-- N002 = hc: ∀ (k : ℕ), 0 < k → c (2 * k) = 2 * (k + 1) ^ 2 ∧ c (2 * k + 1) = 2 * (k + 1) ^ 2
-- N003 = hn: 0 < n
-- N004 = goal: let m := (n + 2) / 2; let t := fun r => r * (r + 1) / 2; c n = 2 * m ^ 2 ∧ 2 * m ^ 2 = 2 * (t (m - 1) + t m)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N001 → N002 → N003 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B001 B002 B003
  exact H_N004

end TopologyCertificate_p1318_sequence_triangular_formula
