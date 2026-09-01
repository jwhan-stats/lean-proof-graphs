import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1763_basel_series
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 2f0bedcf54f8c11e6853d12d594dd879fa3f5a8a0457c32c42442f518da051ce
-- reconstructed_proof_sha256: 5cbe8371261b27b8dde866f5a57d66458163a40c7ca4693e6ee3bdecfe02a04e
-- selected_edge_count: 2

/- verified submission -/
theorem basel_series : HasSum (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) (Real.pi ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (g := Real.pi ^ 2 / 6) 1).mpr (by
    simpa using hasSum_zeta_two)
  simpa using h


#check_dependency_graph "basel_series" against "{\"edges\":[{\"conclusion\":{\"name\":\"h\",\"statement\":\"HasSum (fun n => 1 / ↑(n + 1) ^ 2) (Real.pi ^ 2 / 6)\"},\"graphEdgeId\":\"h_001_h\",\"premises\":[],\"rawEdgeId\":\"telescope_0\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"HasSum (fun n => 1 / ↑(n + 1) ^ 2) (Real.pi ^ 2 / 6)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"h\",\"statement\":\"HasSum (fun n => 1 / ↑(n + 1) ^ 2) (Real.pi ^ 2 / 6)\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1763_basel_series\",\"reconstructedProofSha256\":\"5cbe8371261b27b8dde866f5a57d66458163a40c7ca4693e6ee3bdecfe02a04e\",\"selectedEdgeCount\":2,\"theoremName\":\"basel_series\",\"topologySha256\":\"2f0bedcf54f8c11e6853d12d594dd879fa3f5a8a0457c32c42442f518da051ce\"}"
