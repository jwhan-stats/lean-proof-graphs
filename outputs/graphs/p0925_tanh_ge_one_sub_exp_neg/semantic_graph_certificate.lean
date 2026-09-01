import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p0925_tanh_ge_one_sub_exp_neg
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: c31c7ef38ac30d758d597727d77d1f890e731380163812056eec74da2d1acdf6
-- reconstructed_proof_sha256: 117b93ca571d859736b43fcd6aa91945b68ca73b359c57f9f260dff6354470fb
-- selected_edge_count: 1

/- verified submission -/
theorem tanh_ge_one_sub_exp_neg (x : ℝ) (hx : 0 ≤ x) :
    Real.tanh x ≥ 1 - Real.exp (-x) := by
  rw [Real.tanh_eq, Real.exp_neg]
  let t : ℝ := Real.exp x
  change (t - t⁻¹) / (t + t⁻¹) ≥ 1 - t⁻¹
  have ht : 0 < t := by
    dsimp [t]
    exact Real.exp_pos x
  have ht1 : 1 ≤ t := by
    dsimp [t]
    exact Real.one_le_exp hx
  field_simp [ht.ne']
  ring_nf
  nlinarith [sq_nonneg (t - 1)]


#check_dependency_graph "tanh_ge_one_sub_exp_neg" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"Real.tanh x ≥ 1 - Real.exp (-x)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hx\",\"statement\":\"0 ≤ x\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0925_tanh_ge_one_sub_exp_neg\",\"reconstructedProofSha256\":\"117b93ca571d859736b43fcd6aa91945b68ca73b359c57f9f260dff6354470fb\",\"selectedEdgeCount\":1,\"theoremName\":\"tanh_ge_one_sub_exp_neg\",\"topologySha256\":\"c31c7ef38ac30d758d597727d77d1f890e731380163812056eec74da2d1acdf6\"}"
