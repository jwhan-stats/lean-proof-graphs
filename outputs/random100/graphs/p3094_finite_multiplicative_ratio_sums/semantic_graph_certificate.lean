import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p3094_finite_multiplicative_ratio_sums
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 0f727dd412e7486054192c1914622fb71cd63ecb637578f20f992a8d2ee24e80
-- reconstructed_proof_sha256: dd870d418b7e4a9c7dfbcc6a7842cad3d95e9c2fa01b5b02f991ba2c7e7ccd6e
-- selected_edge_count: 8

/- verified submission -/
theorem finite_multiplicative_ratio_sums
    {I : Type*} [Fintype I] [Nonempty I]
    (r : I × I → ℝ)
    (hr_pos : ∀ e d : I, 0 < r (e, d))
    (hr_mul : ∀ e d b : I, r (e, d) = r (e, b) * r (b, d)) :
    ∀ b : I,
      (∑ e : I, (∑ d : I, r (d, e))⁻¹) =
          (∑ e : I, r (b, e)) / (∑ d : I, (r (d, b))⁻¹) ∧
      (∑ e : I, r (b, e)) / (∑ d : I, (r (d, b))⁻¹) =
          (∑ e : I, r (e, b)) / (∑ d : I, r (d, b)) ∧
      (∑ e : I, r (e, b)) / (∑ d : I, r (d, b)) = 1 := by
  intro b
  have hdiag : ∀ e : I, r (e, e) = 1 := by
    intro e
    have hz : r (e, e) ≠ 0 := ne_of_gt (hr_pos e e)
    have h : r (e, e) * r (e, e) = r (e, e) * 1 := by
      rw [mul_one]
      exact (hr_mul e e e).symm
    exact mul_left_cancel₀ hz h
  have hinv : ∀ e d : I, (r (e, d))⁻¹ = r (d, e) := by
    intro e d
    have hone : r (e, d) * r (d, e) = 1 := by
      rw [← hdiag e]
      exact (hr_mul e e d).symm
    exact inv_eq_of_mul_eq_one_right hone
  have hsum_pos : ∀ e : I, 0 < ∑ d : I, r (d, e) := by
    intro e
    exact Finset.sum_pos (fun d _ => hr_pos d e) Finset.univ_nonempty
  have hsum_ne : ∀ e : I, (∑ d : I, r (d, e)) ≠ 0 := by
    intro e
    exact ne_of_gt (hsum_pos e)
  have hA : (∑ e : I, (∑ d : I, r (d, e))⁻¹) = 1 := by
    have hterm : ∀ e : I,
        (∑ d : I, r (d, e))⁻¹ =
          r (e, b) / (∑ d : I, r (d, b)) := by
      intro e
      calc
        (∑ d : I, r (d, e))⁻¹
            = ((∑ d : I, r (d, b)) / r (e, b))⁻¹ := by
              congr 1
              rw [div_eq_mul_inv, Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro d _
              calc
                r (d, e) = r (d, b) * r (b, e) := hr_mul d e b
                _ = r (d, b) * (r (e, b))⁻¹ := by rw [hinv e b]
        _ = r (e, b) / (∑ d : I, r (d, b)) := inv_div _ _
    calc
      (∑ e : I, (∑ d : I, r (d, e))⁻¹)
          = ∑ e : I, r (e, b) / (∑ d : I, r (d, b)) := by
            apply Finset.sum_congr rfl
            intro e _
            exact hterm e
      _ = (∑ e : I, r (e, b)) / (∑ d : I, r (d, b)) := by
            rw [← Finset.sum_div]
      _ = (∑ d : I, r (d, b)) / (∑ d : I, r (d, b)) := rfl
      _ = 1 := div_self (hsum_ne b)
  have hB : (∑ e : I, r (b, e)) / (∑ d : I, (r (d, b))⁻¹) = 1 := by
    have hden : (∑ d : I, (r (d, b))⁻¹) = ∑ e : I, r (b, e) := by
      apply Finset.sum_congr rfl
      intro d _
      exact hinv d b
    have hnum_pos : 0 < ∑ e : I, r (b, e) :=
      Finset.sum_pos (fun e _ => hr_pos b e) Finset.univ_nonempty
    rw [hden]
    exact div_self (ne_of_gt hnum_pos)
  have hC : (∑ e : I, r (e, b)) / (∑ d : I, r (d, b)) = 1 := by
    have hnum : (∑ e : I, r (e, b)) = ∑ d : I, r (d, b) := rfl
    rw [hnum]
    exact div_self (hsum_ne b)
  exact ⟨hA.trans hB.symm, hB.trans hC.symm, hC⟩


#check_dependency_graph "finite_multiplicative_ratio_sums" against "{\"edges\":[{\"conclusion\":{\"name\":\"hdiag\",\"statement\":\"∀ (e : I), r (e, e) = 1\"},\"graphEdgeId\":\"h_001_hdiag\",\"premises\":[{\"name\":\"hr_pos\",\"statement\":\"∀ (e d : I), 0 < r (e, d)\"},{\"name\":\"hr_mul\",\"statement\":\"∀ (e d b : I), r (e, d) = r (e, b) * r (b, d)\"}],\"rawEdgeId\":\"telescope_7\"},{\"conclusion\":{\"name\":\"hsum_pos\",\"statement\":\"∀ (e : I), 0 < ∑ d, r (d, e)\"},\"graphEdgeId\":\"h_003_hsum_pos\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"Nonempty I\"},{\"name\":\"hr_pos\",\"statement\":\"∀ (e d : I), 0 < r (e, d)\"}],\"rawEdgeId\":\"telescope_9\"},{\"conclusion\":{\"name\":\"hinv\",\"statement\":\"∀ (e d : I), (r (e, d))⁻¹ = r (d, e)\"},\"graphEdgeId\":\"h_002_hinv\",\"premises\":[{\"name\":\"hr_mul\",\"statement\":\"∀ (e d b : I), r (e, d) = r (e, b) * r (b, d)\"},{\"name\":\"hdiag\",\"statement\":\"∀ (e : I), r (e, e) = 1\"}],\"rawEdgeId\":\"telescope_8\"},{\"conclusion\":{\"name\":\"hsum_ne\",\"statement\":\"∀ (e : I), ∑ d, r (d, e) ≠ 0\"},\"graphEdgeId\":\"h_004_hsum_ne\",\"premises\":[{\"name\":\"hsum_pos\",\"statement\":\"∀ (e : I), 0 < ∑ d, r (d, e)\"}],\"rawEdgeId\":\"telescope_10\"},{\"conclusion\":{\"name\":\"hA\",\"statement\":\"∑ e, (∑ d, r (d, e))⁻¹ = 1\"},\"graphEdgeId\":\"h_005_ha\",\"premises\":[{\"name\":\"hr_mul\",\"statement\":\"∀ (e d b : I), r (e, d) = r (e, b) * r (b, d)\"},{\"name\":\"hinv\",\"statement\":\"∀ (e d : I), (r (e, d))⁻¹ = r (d, e)\"},{\"name\":\"hsum_ne\",\"statement\":\"∀ (e : I), ∑ d, r (d, e) ≠ 0\"}],\"rawEdgeId\":\"telescope_11\"},{\"conclusion\":{\"name\":\"hB\",\"statement\":\"(∑ e, r (b, e)) / ∑ d, (r (d, b))⁻¹ = 1\"},\"graphEdgeId\":\"h_006_hb\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"Nonempty I\"},{\"name\":\"hr_pos\",\"statement\":\"∀ (e d : I), 0 < r (e, d)\"},{\"name\":\"hinv\",\"statement\":\"∀ (e d : I), (r (e, d))⁻¹ = r (d, e)\"}],\"rawEdgeId\":\"telescope_12\"},{\"conclusion\":{\"name\":\"hC\",\"statement\":\"(∑ e, r (e, b)) / ∑ d, r (d, b) = 1\"},\"graphEdgeId\":\"h_007_hc\",\"premises\":[{\"name\":\"hsum_ne\",\"statement\":\"∀ (e : I), ∑ d, r (d, e) ≠ 0\"}],\"rawEdgeId\":\"telescope_13\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∑ e, (∑ d, r (d, e))⁻¹ = (∑ e, r (b, e)) / ∑ d, (r (d, b))⁻¹ ∧ (∑ e, r (b, e)) / ∑ d, (r (d, b))⁻¹ = (∑ e, r (e, b)) / ∑ d, r (d, b) ∧ (∑ e, r (e, b)) / ∑ d, r (d, b) = 1\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hA\",\"statement\":\"∑ e, (∑ d, r (d, e))⁻¹ = 1\"},{\"name\":\"hB\",\"statement\":\"(∑ e, r (b, e)) / ∑ d, (r (d, b))⁻¹ = 1\"},{\"name\":\"hC\",\"statement\":\"(∑ e, r (e, b)) / ∑ d, r (d, b) = 1\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p3094_finite_multiplicative_ratio_sums\",\"reconstructedProofSha256\":\"dd870d418b7e4a9c7dfbcc6a7842cad3d95e9c2fa01b5b02f991ba2c7e7ccd6e\",\"selectedEdgeCount\":8,\"theoremName\":\"finite_multiplicative_ratio_sums\",\"topologySha256\":\"0f727dd412e7486054192c1914622fb71cd63ecb637578f20f992a8d2ee24e80\"}"
