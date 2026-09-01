import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1067_complex_exp_modulus_bounds
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: ae0775c9de803f41c6b91d674b58b5dd7eeb7343638294ca094a3b916b2a3aff
-- reconstructed_proof_sha256: 92a592b1c935f0f8a3fd913ea903056af176ecec6c7d55b162b8348316811d42
-- selected_edge_count: 6

/- verified submission -/
theorem complex_exp_modulus_bounds :
  let f : ℂ → ℂ := fun z => z + 1 + Complex.exp (-z)
  ∀ z : ℂ, -z.re ≥ ‖z‖ / 2 ∧ -z.re ≥ 3 →
    (1 / 2) * Real.exp (-z.re) ≤ ‖f z‖ ∧
      ‖f z‖ ≤ 2 * Real.exp (-z.re) := by
  intro f z hz
  have hx3 : 3 ≤ -z.re := hz.2
  have hnormz : ‖z‖ ≤ 2 * (-z.re) := by
    have h := hz.1
    nlinarith
  have hexp : 4 * (-z.re) + 2 ≤ Real.exp (-z.re) := by
    have hsum := Real.sum_le_exp_of_nonneg (show 0 ≤ -z.re by linarith) 5
    norm_num [Finset.sum_range_succ] at hsum
    nlinarith [sq_nonneg ((-z.re) - 3), sq_nonneg (-z.re)]
  have hz1 : ‖z + 1‖ ≤ (1 / 2) * Real.exp (-z.re) := by
    calc
      ‖z + 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_add_le z 1
      _ = ‖z‖ + 1 := by simp
      _ ≤ (1 / 2) * Real.exp (-z.re) := by
        nlinarith [Real.exp_nonneg (-z.re)]
  have hnormexp : ‖Complex.exp (-z)‖ = Real.exp (-z.re) := by
    simpa using Complex.norm_exp (-z)
  have hlower_core :
      (1 / 2) * Real.exp (-z.re) ≤ ‖z + 1 + Complex.exp (-z)‖ := by
    have hrev := norm_sub_le_norm_add (Complex.exp (-z)) (z + 1)
    rw [hnormexp] at hrev
    have hrev' : Real.exp (-z.re) - ‖z + 1‖ ≤ ‖z + 1 + Complex.exp (-z)‖ := by
      simpa [add_comm, add_left_comm, add_assoc] using hrev
    nlinarith [Real.exp_nonneg (-z.re)]
  have hupper_core :
      ‖z + 1 + Complex.exp (-z)‖ ≤ 2 * Real.exp (-z.re) := by
    have htri := norm_add_le (z + 1) (Complex.exp (-z))
    rw [hnormexp] at htri
    nlinarith [Real.exp_nonneg (-z.re)]
  exact ⟨hlower_core, hupper_core⟩


#check_dependency_graph "complex_exp_modulus_bounds" against "{\"edges\":[{\"conclusion\":{\"name\":\"hexp\",\"statement\":\"4 * -z.re + 2 ≤ Real.exp (-z.re)\"},\"graphEdgeId\":\"h_003_hexp\",\"premises\":[{\"name\":\"hz\",\"statement\":\"-z.re ≥ ‖z‖ / 2 ∧ -z.re ≥ 3\"}],\"rawEdgeId\":\"telescope_5\"},{\"conclusion\":{\"name\":\"hnormexp\",\"statement\":\"‖Complex.exp (-z)‖ = Real.exp (-z.re)\"},\"graphEdgeId\":\"h_005_hnormexp\",\"premises\":[],\"rawEdgeId\":\"telescope_7\"},{\"conclusion\":{\"name\":\"hz1\",\"statement\":\"‖z + 1‖ ≤ 1 / 2 * Real.exp (-z.re)\"},\"graphEdgeId\":\"h_004_hz1\",\"premises\":[{\"name\":\"hz\",\"statement\":\"-z.re ≥ ‖z‖ / 2 ∧ -z.re ≥ 3\"},{\"name\":\"hexp\",\"statement\":\"4 * -z.re + 2 ≤ Real.exp (-z.re)\"}],\"rawEdgeId\":\"telescope_6\"},{\"conclusion\":{\"name\":\"hlower_core\",\"statement\":\"1 / 2 * Real.exp (-z.re) ≤ ‖z + 1 + Complex.exp (-z)‖\"},\"graphEdgeId\":\"h_006_hlower_core\",\"premises\":[{\"name\":\"hz1\",\"statement\":\"‖z + 1‖ ≤ 1 / 2 * Real.exp (-z.re)\"},{\"name\":\"hnormexp\",\"statement\":\"‖Complex.exp (-z)‖ = Real.exp (-z.re)\"}],\"rawEdgeId\":\"telescope_8\"},{\"conclusion\":{\"name\":\"hupper_core\",\"statement\":\"‖z + 1 + Complex.exp (-z)‖ ≤ 2 * Real.exp (-z.re)\"},\"graphEdgeId\":\"h_007_hupper_core\",\"premises\":[{\"name\":\"hz\",\"statement\":\"-z.re ≥ ‖z‖ / 2 ∧ -z.re ≥ 3\"},{\"name\":\"hexp\",\"statement\":\"4 * -z.re + 2 ≤ Real.exp (-z.re)\"},{\"name\":\"hz1\",\"statement\":\"‖z + 1‖ ≤ 1 / 2 * Real.exp (-z.re)\"},{\"name\":\"hnormexp\",\"statement\":\"‖Complex.exp (-z)‖ = Real.exp (-z.re)\"}],\"rawEdgeId\":\"telescope_9\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"1 / 2 * Real.exp (-z.re) ≤ ‖f z‖ ∧ ‖f z‖ ≤ 2 * Real.exp (-z.re)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hlower_core\",\"statement\":\"1 / 2 * Real.exp (-z.re) ≤ ‖z + 1 + Complex.exp (-z)‖\"},{\"name\":\"hupper_core\",\"statement\":\"‖z + 1 + Complex.exp (-z)‖ ≤ 2 * Real.exp (-z.re)\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1067_complex_exp_modulus_bounds\",\"reconstructedProofSha256\":\"92a592b1c935f0f8a3fd913ea903056af176ecec6c7d55b162b8348316811d42\",\"selectedEdgeCount\":6,\"theoremName\":\"complex_exp_modulus_bounds\",\"topologySha256\":\"ae0775c9de803f41c6b91d674b58b5dd7eeb7343638294ca094a3b916b2a3aff\"}"
