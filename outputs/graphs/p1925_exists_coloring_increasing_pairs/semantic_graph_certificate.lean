import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1925_exists_coloring_increasing_pairs
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 3f6427c70203b3e4c6d2749063d02e365dd26f2c1c125c6c882c4d8315e787fc
-- reconstructed_proof_sha256: be917624507e7ca877bbb0ccdf84a7409e55d13a709a8e6be08d7646f947c77f
-- selected_edge_count: 1

/- verified submission -/
theorem exists_coloring_increasing_pairs :
    ∃ c : ℕ × ℕ → ℕ,
      (∀ n m : ℕ, n < m → c (n, m) < m) ∧
      ∀ n k : ℕ, ∀ B : Set ℕ, B.Infinite →
        ∃ m ∈ B, n < m ∧ k ≤ c (n, m) := by
  use fun p => p.2 - 1
  constructor
  · intro n m h
    show m - 1 < m
    omega
  · intro n k B hB
    obtain ⟨m, hmB, hm⟩ := hB.exists_gt (max n k)
    refine ⟨m, hmB, lt_of_le_of_lt (Nat.le_max_left n k) hm, ?_⟩
    show k ≤ m - 1
    have := Nat.le_max_right n k
    omega


#check_dependency_graph "exists_coloring_increasing_pairs" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∃ c, (∀ (n m : ℕ), n < m → c (n, m) < m) ∧ ∀ (n k : ℕ) (B : Set ℕ), B.Infinite → ∃ m ∈ B, n < m ∧ k ≤ c (n, m)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1925_exists_coloring_increasing_pairs\",\"reconstructedProofSha256\":\"be917624507e7ca877bbb0ccdf84a7409e55d13a709a8e6be08d7646f947c77f\",\"selectedEdgeCount\":1,\"theoremName\":\"exists_coloring_increasing_pairs\",\"topologySha256\":\"3f6427c70203b3e4c6d2749063d02e365dd26f2c1c125c6c882c4d8315e787fc\"}"
