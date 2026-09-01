import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p2161_cell_entropy_inequality_for_semidiscrete_f
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 914bb69b48bd25703fb73fec441a26a5ec4704a2b1e65300ddb0beca72209839
-- reconstructed_proof_sha256: 51d19a450c3431ccfe4246259fec55054226e7b688f918b56dd1693199bf62d5
-- selected_edge_count: 3

/- verified submission -/
theorem cell_entropy_inequality_for_semidiscrete_finite_volume_scheme
    {ι κ : Type*} [DecidableEq ι] [Fintype κ]
    (N : Finset ι)
    (V : ℝ) (hV : 0 < V)
    (A δ ε : ι → ℝ)
    (hA : ∀ r ∈ N, 0 ≤ A r)
    (hδ : ∀ r ∈ N, 0 < δ r)
    (hε : ∀ r ∈ N, 0 ≤ ε r)
    (qNeighbor : ι → κ → ℝ) (q : κ → ℝ)
    (T : ℝ) (hT : 0 < T)
    (H : ι → Matrix κ κ ℝ)
    (hH : ∀ r ∈ N, (H r).PosSemidef)
    (ρSNeighbor : ι → ℝ) (ρS : ℝ)
    (D : ι → ℝ) (dρSdt : ℝ) :
    let Δq : ι → κ → ℝ := fun r => qNeighbor r - q
    let entropyProduction : ι → ℝ := fun r =>
      ε r * dotProduct (Δq r) ((H r).mulVec (Δq r)) / (2 * T * δ r)
    let g : ι → ℝ := fun r => ε r * (ρSNeighbor r - ρS) / δ r
    dρSdt = (1 / V) * ∑ r ∈ N, A r * (-D r + g r + entropyProduction r) →
      dρSdt + (1 / V) * ∑ r ∈ N, A r * D r -
        (1 / V) * ∑ r ∈ N, A r * g r ≥ 0 := by
  intro Δq entropyProduction g hd
  have hprod : ∀ r ∈ N, 0 ≤ entropyProduction r := by
    intro r hr
    have hquad : 0 ≤ dotProduct (Δq r) ((H r).mulVec (Δq r)) := by
      simpa using (hH r hr).dotProduct_mulVec_nonneg (Δq r)
    have hden : 0 < 2 * T * δ r := by
      exact mul_pos (mul_pos (by norm_num) hT) (hδ r hr)
    exact div_nonneg (mul_nonneg (hε r hr) hquad) hden.le
  have hsum :
      ∑ r ∈ N, A r * (-D r + g r + entropyProduction r)
        = -∑ r ∈ N, A r * D r + ∑ r ∈ N, A r * g r +
            ∑ r ∈ N, A r * entropyProduction r := by
    simp_rw [mul_add, mul_neg]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  calc
    dρSdt + (1 / V) * ∑ r ∈ N, A r * D r -
        (1 / V) * ∑ r ∈ N, A r * g r
        = (1 / V) * ∑ r ∈ N, A r * entropyProduction r := by
          rw [hd, hsum]
          ring
    _ ≥ 0 := by
      exact mul_nonneg (one_div_nonneg.mpr hV.le)
        (Finset.sum_nonneg (fun r hr => mul_nonneg (hA r hr) (hprod r hr)))


#check_dependency_graph "cell_entropy_inequality_for_semidiscrete_finite_volume_scheme" against "{\"edges\":[{\"conclusion\":{\"name\":\"hprod\",\"statement\":\"∀ r ∈ N, 0 ≤ entropyProduction r\"},\"graphEdgeId\":\"h_001_hprod\",\"premises\":[{\"name\":\"hδ\",\"statement\":\"∀ r ∈ N, 0 < δ r\"},{\"name\":\"hε\",\"statement\":\"∀ r ∈ N, 0 ≤ ε r\"},{\"name\":\"hT\",\"statement\":\"0 < T\"},{\"name\":\"hH\",\"statement\":\"∀ r ∈ N, (H r).PosSemidef\"}],\"rawEdgeId\":\"telescope_27\"},{\"conclusion\":{\"name\":\"hsum\",\"statement\":\"∑ r ∈ N, A r * (-D r + g r + entropyProduction r) = -∑ r ∈ N, A r * D r + ∑ r ∈ N, A r * g r + ∑ r ∈ N, A r * entropyProduction r\"},\"graphEdgeId\":\"h_002_hsum\",\"premises\":[],\"rawEdgeId\":\"telescope_28\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"dρSdt + 1 / V * ∑ r ∈ N, A r * D r - 1 / V * ∑ r ∈ N, A r * g r ≥ 0\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hV\",\"statement\":\"0 < V\"},{\"name\":\"hA\",\"statement\":\"∀ r ∈ N, 0 ≤ A r\"},{\"name\":\"hd\",\"statement\":\"dρSdt = 1 / V * ∑ r ∈ N, A r * (-D r + g r + entropyProduction r)\"},{\"name\":\"hprod\",\"statement\":\"∀ r ∈ N, 0 ≤ entropyProduction r\"},{\"name\":\"hsum\",\"statement\":\"∑ r ∈ N, A r * (-D r + g r + entropyProduction r) = -∑ r ∈ N, A r * D r + ∑ r ∈ N, A r * g r + ∑ r ∈ N, A r * entropyProduction r\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2161_cell_entropy_inequality_for_semidiscrete_f\",\"reconstructedProofSha256\":\"51d19a450c3431ccfe4246259fec55054226e7b688f918b56dd1693199bf62d5\",\"selectedEdgeCount\":3,\"theoremName\":\"cell_entropy_inequality_for_semidiscrete_finite_volume_scheme\",\"topologySha256\":\"914bb69b48bd25703fb73fec441a26a5ec4704a2b1e65300ddb0beca72209839\"}"
