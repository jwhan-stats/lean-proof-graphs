import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0292_two_positive_roots_of_mu
-- topology_sha256: 50cc4749c4529bb764e87d2981f6c706ea22d32a28e9d891791887fe92f80b47
namespace TopologyCertificate_p0292_two_positive_roots_of_mu

-- N001 = hΛ: 0 < Λ
-- N002 = hM: 0 < M
-- N003 = hn: 4 ≤ n
-- N004 = goal: let lam := 2 * Λ / ((↑n - 2) * (↑n - 1)); let mu := fun r => 1 - 2 * M / r ^ (n - 3) - lam * r ^ 2; M ^ 2 * lam ^ (n - 3) < (↑n - 3) ^ (n - 3) / (↑n - 1) ^ (n - 1) → ∃ r_minus r_plus, 0 < r_minus ∧ r_minus < r_plus ∧ mu r_minus = 0 ∧ mu r_plus = 0 ∧ ∀ (r : ℝ), 0 < r → mu r = 0 → r = r_minus ∨ r = r_plus

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N003 → N002 → N001 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B003 B002 B001
  exact H_N004

end TopologyCertificate_p0292_two_positive_roots_of_mu
