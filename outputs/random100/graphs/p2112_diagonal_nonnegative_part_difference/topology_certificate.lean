import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2112_diagonal_nonnegative_part_difference
-- topology_sha256: 541c0b3df8342957f6a05dab1b135f216666e01e3c4308e0074bef9b58f6652e
namespace TopologyCertificate_p2112_diagonal_nonnegative_part_difference

-- N001 = hω: ∀ (i : Fin n), 0 ≤ ω i ∧ ω i ≤ 1 ∧ (if 0 ≤ x i then 1 else 0) * x i - (if 0 ≤ y i then 1 else 0) * y i = ω i * (x i - y i)
-- N002 = goal: ∃ ω, (∀ (i : Fin n), 0 ≤ ω i ∧ ω i ≤ 1) ∧ ((fun z => Matrix.diagonal fun i => if 0 ≤ z i then 1 else 0) x).mulVec x - ((fun z => Matrix.diagonal fun i => if 0 ≤ z i then 1 else 0) y).mulVec y = (Matrix.diagonal ω).mulVec (x - y)

-- E001 represents h_001_h
-- E002 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (E001 : N001)
    (E002 : N001 → N002)
    : N002 := by
  have H_N001 : N001 := E001
  have H_N002 : N002 := E002 H_N001
  exact H_N002

end TopologyCertificate_p2112_diagonal_nonnegative_part_difference
