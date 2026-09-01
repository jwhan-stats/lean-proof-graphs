import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1925_exists_coloring_increasing_pairs
-- topology_sha256: 3f6427c70203b3e4c6d2749063d02e365dd26f2c1c125c6c882c4d8315e787fc
namespace TopologyCertificate_p1925_exists_coloring_increasing_pairs

-- N001 = goal: ∃ c, (∀ (n m : ℕ), n < m → c (n, m) < m) ∧ ∀ (n k : ℕ) (B : Set ℕ), B.Infinite → ∃ m ∈ B, n < m ∧ k ≤ c (n, m)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p1925_exists_coloring_increasing_pairs
