import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p0381_two_minimal_missing_faces_deletion
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 05d1d90c7d2ac7843a9bc9fde3759270e612281999887e2da50afe8bd3dbe0bf
-- reconstructed_proof_sha256: 688574ff63a98dba3908ff93b2258bc637f331384487238fbd5f3a16f1a161d8
-- selected_edge_count: 1

/- verified submission -/
theorem two_minimal_missing_faces_deletion
    (m : ℕ) (K : Set (Set ℕ)) (I J : Set ℕ)
    (hK_downward : IsLowerSet K)
    (hK_vertices : ∀ ⦃S : Set ℕ⦄, S ∈ K → S ⊆ Set.Icc 1 m)
    (hIJ : I ≠ J)
    (hmissing : ∀ S : Set ℕ,
      Minimal (fun T : Set ℕ => T ⊆ Set.Icc 1 m ∧ T ∉ K) S ↔
        S = I ∨ S = J)
    (hunion : I ∪ J = Set.Icc 1 m)
    (hinter : (I ∩ J).Nonempty)
    {w : ℕ} (hw : w ∈ I ∩ J) :
    ∀ S : Set ℕ, S ⊆ Set.Icc 1 m \ {w} → S ∈ K := by
  intro S hS
  by_contra hSK
  let C : Set (Set ℕ) :=
    {T : Set ℕ | T ⊆ Set.Icc 1 m ∧ T ∉ K ∧ T ⊆ S}
  have hSV : S ⊆ Set.Icc 1 m := hS.trans Set.diff_subset
  have hCfinite : C.Finite := by
    exact (Set.finite_Icc 1 m).powerset.subset (by
      intro T hT
      exact hT.1)
  have hCnonempty : C.Nonempty := by
    exact ⟨S, hSV, hSK, subset_rfl⟩
  obtain ⟨L, hLminC⟩ := hCfinite.exists_minimal hCnonempty
  have hLmin : Minimal (fun T : Set ℕ => T ⊆ Set.Icc 1 m ∧ T ∉ K) L := by
    constructor
    · exact ⟨hLminC.1.1, hLminC.1.2.1⟩
    · intro T hT hTL
      have hTC : T ∈ C := by
        exact ⟨hT.1, hT.2, hTL.trans hLminC.1.2.2⟩
      exact hLminC.2 hTC hTL
  rcases (hmissing L).mp hLmin with hLI | hLJ
  · have hwL : w ∈ L := by
      rw [hLI]
      exact hw.1
    have hwS : w ∈ S := hLminC.1.2.2 hwL
    exact (hS hwS).2 rfl
  · have hwL : w ∈ L := by
      rw [hLJ]
      exact hw.2
    have hwS : w ∈ S := hLminC.1.2.2 hwL
    exact (hS hwS).2 rfl


#check_dependency_graph "two_minimal_missing_faces_deletion" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"S ∈ K\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hmissing\",\"statement\":\"∀ (S : Set ℕ), Minimal (fun T => T ⊆ Set.Icc 1 m ∧ T ∉ K) S ↔ S = I ∨ S = J\"},{\"name\":\"hw\",\"statement\":\"w ∈ I ∩ J\"},{\"name\":\"hS\",\"statement\":\"S ⊆ Set.Icc 1 m \\\\ {w}\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0381_two_minimal_missing_faces_deletion\",\"reconstructedProofSha256\":\"688574ff63a98dba3908ff93b2258bc637f331384487238fbd5f3a16f1a161d8\",\"selectedEdgeCount\":1,\"theoremName\":\"two_minimal_missing_faces_deletion\",\"topologySha256\":\"05d1d90c7d2ac7843a9bc9fde3759270e612281999887e2da50afe8bd3dbe0bf\"}"
