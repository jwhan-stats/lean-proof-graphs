import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1971_finite_diversity_induces_metric
-- topology_sha256: c03a45d7a39d855d98881c8e2d73689fa54da6b90960483569ca3b857b3d8a26
namespace TopologyCertificate_p1971_finite_diversity_induces_metric

-- N001 = h_triangle: ∀ (A B C : { A // A.Finite }), (↑B).Nonempty → δ ⟨↑A ∪ ↑C, ⋯⟩ ≤ δ ⟨↑A ∪ ↑B, ⋯⟩ + δ ⟨↑B ∪ ↑C, ⋯⟩
-- N002 = h_zero: ∀ (A : { A // A.Finite }), δ A = 0 ↔ (↑A).Subsingleton
-- N003 = goal: (∃ m, ∀ (x y : X), dist x y = δ ⟨{x, y}, ⋯⟩) ∧ (∀ (A B : { A // A.Finite }), ↑A ⊆ ↑B → δ A ≤ δ B) ∧ ∀ (A B : { A // A.Finite }), (↑A ∩ ↑B).Nonempty → δ ⟨↑A ∪ ↑B, ⋯⟩ ≤ δ A + δ B

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (B001 : N001)
    (B002 : N002)
    (E001 : N002 → N001 → N003)
    : N003 := by
  have H_N003 : N003 := E001 B002 B001
  exact H_N003

end TopologyCertificate_p1971_finite_diversity_induces_metric
