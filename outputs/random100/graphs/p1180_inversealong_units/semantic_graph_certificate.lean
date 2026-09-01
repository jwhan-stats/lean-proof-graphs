import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1180_inversealong_units
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 14da5c37624322edd95e16aea21e85ecc3ac5185160255fc6420240c3d494907
-- reconstructed_proof_sha256: 0abd807556561f5c6db374723fbd7946a23f6ffc525373644d657d7653813c8a
-- selected_edge_count: 1

/- verified submission -/
lemma rightIdeal_subset_of_units
    {R : Type*} [Ring R] {b d : R} (u v : Rˣ)
    (h : Set.range (fun y : R => b * y) ⊆ Set.range (fun y : R => d * y)) :
    Set.range (fun y : R => ((u : R) * b * (v : R)) * y) ⊆
      Set.range (fun y : R => ((u : R) * d * (v : R)) * y) := by
  intro z hz
  rcases hz with ⟨y, rfl⟩
  have hb : b * ((v : R) * y) ∈ Set.range (fun y : R => d * y) := by
    exact h ⟨((v : R) * y), rfl⟩
  rcases hb with ⟨w, hw⟩
  use (((v⁻¹ : Rˣ) : R) * w)
  simpa [mul_assoc] using congrArg (fun t : R => (u : R) * t) hw

lemma rightIdeal_eq_of_units
    {R : Type*} [Ring R] {b d : R} (u v : Rˣ)
    (h : Set.range (fun y : R => b * y) = Set.range (fun y : R => d * y)) :
    Set.range (fun y : R => ((u : R) * b * (v : R)) * y) =
      Set.range (fun y : R => ((u : R) * d * (v : R)) * y) := by
  apply Set.Subset.antisymm
  · exact rightIdeal_subset_of_units u v (subset_of_eq h)
  · exact rightIdeal_subset_of_units u v (subset_of_eq h.symm)

lemma leftIdeal_subset_of_units
    {R : Type*} [Ring R] {b d : R} (u v : Rˣ)
    (h : Set.range (fun y : R => y * b) ⊆ Set.range (fun y : R => y * d)) :
    Set.range (fun y : R => y * ((u : R) * b * (v : R))) ⊆
      Set.range (fun y : R => y * ((u : R) * d * (v : R))) := by
  intro z hz
  rcases hz with ⟨y, rfl⟩
  have hb : ((y * (u : R)) * b) ∈ Set.range (fun y : R => y * d) := by
    exact h ⟨(y * (u : R)), rfl⟩
  rcases hb with ⟨w, hw⟩
  use w * (((u⁻¹ : Rˣ) : R))
  simpa [mul_assoc] using congrArg (fun t : R => t * (v : R)) hw

lemma leftIdeal_eq_of_units
    {R : Type*} [Ring R] {b d : R} (u v : Rˣ)
    (h : Set.range (fun y : R => y * b) = Set.range (fun y : R => y * d)) :
    Set.range (fun y : R => y * ((u : R) * b * (v : R))) =
      Set.range (fun y : R => y * ((u : R) * d * (v : R))) := by
  apply Set.Subset.antisymm
  · exact leftIdeal_subset_of_units u v (subset_of_eq h)
  · exact leftIdeal_subset_of_units u v (subset_of_eq h.symm)

theorem inverseAlong_units
    {R : Type*} [Ring R] {a b d : R} (r s : Rˣ)
    (h_inner : b * a * b = b)
    (h_right : Set.range (fun y : R => b * y) = Set.range (fun y : R => d * y))
    (h_left : Set.range (fun y : R => y * b) = Set.range (fun y : R => y * d)) :
    (((r : R) * b * ((s⁻¹ : Rˣ) : R)) *
          ((s : R) * a * ((r⁻¹ : Rˣ) : R)) *
          ((r : R) * b * ((s⁻¹ : Rˣ) : R)) =
        (r : R) * b * ((s⁻¹ : Rˣ) : R)) ∧
      Set.range (fun y : R => ((r : R) * b * ((s⁻¹ : Rˣ) : R)) * y) =
        Set.range (fun y : R => ((r : R) * d * ((s⁻¹ : Rˣ) : R)) * y) ∧
      Set.range (fun y : R => y * ((r : R) * b * ((s⁻¹ : Rˣ) : R))) =
        Set.range (fun y : R => y * ((r : R) * d * ((s⁻¹ : Rˣ) : R))) := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      ((r : R) * b * ((s⁻¹ : Rˣ) : R)) *
          ((s : R) * a * ((r⁻¹ : Rˣ) : R)) *
          ((r : R) * b * ((s⁻¹ : Rˣ) : R))
          = (r : R) * (b * a * b) * ((s⁻¹ : Rˣ) : R) := by
            simp [mul_assoc]
      _ = (r : R) * b * ((s⁻¹ : Rˣ) : R) := by
            simp [h_inner, mul_assoc]
  · exact rightIdeal_eq_of_units r s⁻¹ h_right
  · exact leftIdeal_eq_of_units r s⁻¹ h_left


#check_dependency_graph "inverseAlong_units" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"↑r * b * ↑s⁻¹ * (↑s * a * ↑r⁻¹) * (↑r * b * ↑s⁻¹) = ↑r * b * ↑s⁻¹ ∧ ((Set.range fun y => ↑r * b * ↑s⁻¹ * y) = Set.range fun y => ↑r * d * ↑s⁻¹ * y) ∧ (Set.range fun y => y * (↑r * b * ↑s⁻¹)) = Set.range fun y => y * (↑r * d * ↑s⁻¹)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"h_inner\",\"statement\":\"b * a * b = b\"},{\"name\":\"h_right\",\"statement\":\"(Set.range fun y => b * y) = Set.range fun y => d * y\"},{\"name\":\"h_left\",\"statement\":\"(Set.range fun y => y * b) = Set.range fun y => y * d\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1180_inversealong_units\",\"reconstructedProofSha256\":\"0abd807556561f5c6db374723fbd7946a23f6ffc525373644d657d7653813c8a\",\"selectedEdgeCount\":1,\"theoremName\":\"inverseAlong_units\",\"topologySha256\":\"14da5c37624322edd95e16aea21e85ecc3ac5185160255fc6420240c3d494907\"}"
