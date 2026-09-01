import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0968_unique_nonzero_zero_of_exponential_factori
-- topology_sha256: d4ca74383152f0bfeefc3bc82eda301a06f7f3b5f660876d151afe5a084e3479
namespace TopologyCertificate_p0968_unique_nonzero_zero_of_exponential_factori

-- N001 = hk₂: k ≤ n - 1
-- N002 = hk₁: 1 ≤ k
-- N003 = hn: 2 ≤ n
-- N004 = goal: let h := fun x => Real.exp (2 * ↑k * x) * ∑ j ∈ Finset.range (n + 1), (-1) ^ (n - j) * (↑n.factorial / ↑j.factorial) * (↑n + ↑k) ^ (↑j - 1) * (↑n + ↑k - ↑j) * x ^ j - ∑ j ∈ Finset.range (n + 1), (-1) ^ (n - j) * (↑n.factorial / ↑j.factorial) * (↑n - ↑k) ^ (↑j - 1) * (↑n - ↑k - ↑j) * x ^ j; ∃ c, -1 < c ∧ c < 0 ∧ h c = 0 ∧ ∀ (x : ℝ), h x = 0 ↔ x = 0 ∨ x = c

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

end TopologyCertificate_p0968_unique_nonzero_zero_of_exponential_factori
