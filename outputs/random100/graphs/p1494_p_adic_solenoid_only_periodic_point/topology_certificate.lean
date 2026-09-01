import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1494_p_adic_solenoid_only_periodic_point
-- topology_sha256: 3f89eab81a87f5fb87faadc8e5b9321d877ac94dd5afae1efdb5824852a46a7d
namespace TopologyCertificate_p1494_p_adic_solenoid_only_periodic_point

-- N001 = hk: 2 ≤ k
-- N002 = hP_recurrent: ∀ (q : ℕ), Nat.Prime q → ∀ (N : ℕ), ∃ n, N ≤ n ∧ P n = q
-- N003 = hz: (∀ (n : ℕ), ‖z n‖ = 1) ∧ ∀ (n : ℕ), z n = z (n + 1) ^ P n
-- N004 = goal: (∃ m, 0 < m ∧ Function.IsPeriodicPt (fun w n => w n ^ k) m z) ↔ z = fun x => 1

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N002 → N001 → N003 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B002 B001 B003
  exact H_N004

end TopologyCertificate_p1494_p_adic_solenoid_only_periodic_point
