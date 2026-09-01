import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p0229_euclidean_decomposition_bound
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 60d8d4e289aa2948542a900b0644473c2588737e01bfa65a0a429d00fc12a92b
-- reconstructed_proof_sha256: ed084d87a7eba607d533b02d0cca9c0615efa29faf08751225b856440585e72c
-- selected_edge_count: 3

/- verified submission -/
theorem euclidean_decomposition_bound (n e p : ℕ) (hn : 0 < n) (he : 0 < e)
    (hp : Nat.Prime p) (hsize : 4 * p ^ 2 ≤ n + 2) (hep : e ≤ p + 1) :
    ∃ d f : ℕ, f < p ∧ n + 2 = p * d + f + e ∧
      d ≥ e + f + (2 * p - 2) := by
  have hp0 : 0 < p := hp.pos
  have hp2 : 2 ≤ p := hp.two_le
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp2
  have hm : e ≤ n + 2 := by
    have hp_sq : 2 + q + 1 ≤ 4 * (2 + q) ^ 2 := by
      nlinarith
    exact le_trans hep (le_trans hp_sq hsize)
  let d := (n + 2 - e) / (2 + q)
  let f := (n + 2 - e) % (2 + q)
  have hf : f < 2 + q := by
    dsimp [f]
    exact Nat.mod_lt _ (by omega)
  have hdiv : (2 + q) * d + f = n + 2 - e := by
    dsimp [d, f]
    exact Nat.div_add_mod (n + 2 - e) (2 + q)
  have hdecomp : n + 2 = (2 + q) * d + f + e := by
    calc
      n + 2 = (n + 2 - e) + e := (Nat.sub_add_cancel hm).symm
      _ = ((2 + q) * d + f) + e := by rw [hdiv]
      _ = (2 + q) * d + f + e := rfl
  have hd4 : 4 * (2 + q) - 2 ≤ d := by
    dsimp [d]
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2 + q)).mpr
    have hmul : (4 * (2 + q) - 2) * (2 + q) ≤ n + 2 - e := by
      apply (Nat.le_sub_iff_add_le hm).mpr
      have hsub : 4 * (2 + q) - 2 = 6 + 4 * q := by omega
      rw [hsub]
      nlinarith
    exact hmul
  refine ⟨d, f, hf, hdecomp, ?_⟩
  have htarget : e + f + (2 * (2 + q) - 2) ≤ 4 * (2 + q) - 2 := by
    omega
  exact le_trans htarget hd4


#check_dependency_graph "euclidean_decomposition_bound" against "{\"edges\":[{\"conclusion\":{\"name\":\"hp0\",\"statement\":\"0 < p\"},\"graphEdgeId\":\"h_001_hp0\",\"premises\":[{\"name\":\"hp\",\"statement\":\"Nat.Prime p\"}],\"rawEdgeId\":\"telescope_8\"},{\"conclusion\":{\"name\":\"hp2\",\"statement\":\"2 ≤ p\"},\"graphEdgeId\":\"h_002_hp2\",\"premises\":[{\"name\":\"hp\",\"statement\":\"Nat.Prime p\"}],\"rawEdgeId\":\"telescope_9\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∃ d, ∃ f < p, n + 2 = p * d + f + e ∧ d ≥ e + f + (2 * p - 2)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hp\",\"statement\":\"Nat.Prime p\"},{\"name\":\"hsize\",\"statement\":\"4 * p ^ 2 ≤ n + 2\"},{\"name\":\"hep\",\"statement\":\"e ≤ p + 1\"},{\"name\":\"hp0\",\"statement\":\"0 < p\"},{\"name\":\"hp2\",\"statement\":\"2 ≤ p\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0229_euclidean_decomposition_bound\",\"reconstructedProofSha256\":\"ed084d87a7eba607d533b02d0cca9c0615efa29faf08751225b856440585e72c\",\"selectedEdgeCount\":3,\"theoremName\":\"euclidean_decomposition_bound\",\"topologySha256\":\"60d8d4e289aa2948542a900b0644473c2588737e01bfa65a0a429d00fc12a92b\"}"
