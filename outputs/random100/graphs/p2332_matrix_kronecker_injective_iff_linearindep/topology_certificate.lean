import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2332_matrix_kronecker_injective_iff_linearindep
-- topology_sha256: 812999549bfeac040effa04a22a8ad38d1e8fe269f6948bb066701c2a4298133
namespace TopologyCertificate_p2332_matrix_kronecker_injective_iff_linearindep

-- N001 = goal: ((∀ (n : ℕ), 0 < n → ∀ (X : Fin g → Matrix (Fin n) (Fin n) ℂ), ∑ j, (A j).kronecker (X j) = 0 → ∀ (j : Fin g), X j = 0) ↔ ∀ (z : Fin g → ℂ), ∑ j, z j • A j = 0 → ∀ (j : Fin g), z j = 0) ∧ ((∀ (z : Fin g → ℂ), ∑ j, z j • A j = 0 → ∀ (j : Fin g), z j = 0) ↔ LinearIndependent ℂ A)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p2332_matrix_kronecker_injective_iff_linearindep
