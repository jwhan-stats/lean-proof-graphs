import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p3255_horseshoelikepenalty_strictconcave
-- topology_sha256: 35d8c5ea9a37d2b8ec8b339d43d5d2f09b426f320a12ddbb467aa4c09e83f31b
namespace TopologyCertificate_p3255_horseshoelikepenalty_strictconcave

-- N001 = ha: 0 < a
-- N002 = goal: let pen_a := fun x => -Real.log (Real.log (1 + a / x ^ 2)); ∀ (x y t : ℝ), x ≠ y → 0 < x ∧ 0 < y ∨ x < 0 ∧ y < 0 → 0 < t → t < 1 → pen_a (t * x + (1 - t) * y) > t * pen_a x + (1 - t) * pen_a y

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    : N002 := by
  have H_N002 : N002 := E001 B001
  exact H_N002

end TopologyCertificate_p3255_horseshoelikepenalty_strictconcave
