import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p2112_diagonal_nonnegative_part_difference
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 541c0b3df8342957f6a05dab1b135f216666e01e3c4308e0074bef9b58f6652e
-- reconstructed_proof_sha256: 481f7a61e57d2cb5b6e70040a95b27cffd8151229b355b6032698da9b4cbb8bf
-- selected_edge_count: 2

/- verified submission -/
lemma positive_part_secant_aux (x y : ℝ) :
    ∃ ω : ℝ, 0 ≤ ω ∧ ω ≤ 1 ∧
      (if 0 ≤ x then (1 : ℝ) else 0) * x -
        (if 0 ≤ y then (1 : ℝ) else 0) * y = ω * (x - y) := by
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · refine ⟨1, by norm_num, by norm_num, ?_⟩
      simp [hx, hy]
    · have hy_lt : y < 0 := lt_of_not_ge hy
      have hden : 0 < x - y := sub_pos.mpr (lt_of_lt_of_le hy_lt hx)
      refine ⟨x / (x - y), ?_, ?_, ?_⟩
      · exact div_nonneg hx (le_of_lt hden)
      · rw [div_le_one hden]
        nlinarith
      · simp [hx, hy]
        exact (div_mul_cancel₀ x (ne_of_gt hden)).symm
  · have hx_lt : x < 0 := lt_of_not_ge hx
    by_cases hy : 0 ≤ y
    · have hden : 0 < y - x := sub_pos.mpr (lt_of_lt_of_le hx_lt hy)
      refine ⟨y / (y - x), ?_, ?_, ?_⟩
      · exact div_nonneg hy (le_of_lt hden)
      · rw [div_le_one hden]
        nlinarith
      · simp [hx, hy]
        field_simp [ne_of_gt hden]
        ring
    · refine ⟨0, by norm_num, by norm_num, ?_⟩
      simp [hx, hy]

theorem diagonal_nonnegative_part_difference
    (n : ℕ) (hn : 0 < n) (x y : Fin n → ℝ) :
    let P : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ :=
      fun z => Matrix.diagonal (fun i => if 0 ≤ z i then 1 else 0)
    ∃ ω : Fin n → ℝ,
      (∀ i, 0 ≤ ω i ∧ ω i ≤ 1) ∧
        Matrix.mulVec (P x) x - Matrix.mulVec (P y) y =
          Matrix.mulVec (Matrix.diagonal ω) (x - y) := by
  let P : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ :=
    fun z => Matrix.diagonal (fun i => if 0 ≤ z i then 1 else 0)
  let ω : Fin n → ℝ :=
    fun i => Classical.choose (positive_part_secant_aux (x i) (y i))
  have hω : ∀ i : Fin n,
      0 ≤ ω i ∧ ω i ≤ 1 ∧
        (if 0 ≤ x i then (1 : ℝ) else 0) * x i -
          (if 0 ≤ y i then (1 : ℝ) else 0) * y i = ω i * (x i - y i) := by
    intro i
    dsimp [ω]
    exact Classical.choose_spec (positive_part_secant_aux (x i) (y i))
  refine ⟨ω, ?_, ?_⟩
  · intro i
    exact ⟨(hω i).1, (hω i).2.1⟩
  · funext i
    exact (by
      simpa [P, Matrix.mulVec_diagonal, Pi.sub_apply] using (hω i).2.2 :
        (Matrix.mulVec (P x) x - Matrix.mulVec (P y) y) i =
          (Matrix.mulVec (Matrix.diagonal ω) (x - y)) i)


#check_dependency_graph "diagonal_nonnegative_part_difference" against "{\"edges\":[{\"conclusion\":{\"name\":\"hω\",\"statement\":\"∀ (i : Fin n), 0 ≤ ω i ∧ ω i ≤ 1 ∧ (if 0 ≤ x i then 1 else 0) * x i - (if 0 ≤ y i then 1 else 0) * y i = ω i * (x i - y i)\"},\"graphEdgeId\":\"h_001_h\",\"premises\":[],\"rawEdgeId\":\"telescope_6\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∃ ω, (∀ (i : Fin n), 0 ≤ ω i ∧ ω i ≤ 1) ∧ ((fun z => Matrix.diagonal fun i => if 0 ≤ z i then 1 else 0) x).mulVec x - ((fun z => Matrix.diagonal fun i => if 0 ≤ z i then 1 else 0) y).mulVec y = (Matrix.diagonal ω).mulVec (x - y)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hω\",\"statement\":\"∀ (i : Fin n), 0 ≤ ω i ∧ ω i ≤ 1 ∧ (if 0 ≤ x i then 1 else 0) * x i - (if 0 ≤ y i then 1 else 0) * y i = ω i * (x i - y i)\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2112_diagonal_nonnegative_part_difference\",\"reconstructedProofSha256\":\"481f7a61e57d2cb5b6e70040a95b27cffd8151229b355b6032698da9b4cbb8bf\",\"selectedEdgeCount\":2,\"theoremName\":\"diagonal_nonnegative_part_difference\",\"topologySha256\":\"541c0b3df8342957f6a05dab1b135f216666e01e3c4308e0074bef9b58f6652e\"}"
