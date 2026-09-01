import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2823_two_local_inner_derivation_matrix_is_inner
-- topology_sha256: 1b9699c61657e610aa8a7c31dc7526a9ba513097385778c64a2cc219bdef2544
namespace TopologyCertificate_p2823_two_local_inner_derivation_matrix_is_inner

-- N001 = hΔ: ∀ (X Y : Matrix (Fin n) (Fin n) R), ∃ A, Δ X = A * X - X * A ∧ Δ Y = A * Y - Y * A
-- N002 = goal: ∃ B, ∀ (X : Matrix (Fin n) (Fin n) R), Δ X = B * X - X * B

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    : N002 := by
  have H_N002 : N002 := E001 B001
  exact H_N002

end TopologyCertificate_p2823_two_local_inner_derivation_matrix_is_inner
