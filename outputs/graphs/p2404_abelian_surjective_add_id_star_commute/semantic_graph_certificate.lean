import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p2404_abelian_surjective_add_id_star_commute
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 69f2cf3836ce8fc06e2967a6e32e72fdd62ebbb926a939b0967eab84873aa4af
-- reconstructed_proof_sha256: 5ad69869682c42ad676a89f591ed465ee0f23afa9a66d3ddad067fbbb9523b3b
-- selected_edge_count: 1

/- verified submission -/
theorem abelian_surjective_add_id_star_commute
    {A : Type*} [AddCommGroup A] (φ : A →+ A)
    (hφ : Function.Surjective φ) :
    let ψ : A → A := fun a ↦ φ a + a
    Function.Commute φ ψ ∧
      ∀ x y : A, ψ x = φ y → ∃! z : A, φ z = x ∧ ψ z = y := by
  let ψ : A → A := fun a ↦ φ a + a
  constructor
  · intro a
    change φ (ψ a) = ψ (φ a)
    dsimp [ψ]
    simp [map_add, add_comm]
  · intro x y hxy
    have hxy' : ψ x = φ y := hxy
    refine ⟨y - x, ?_, ?_⟩
    · constructor
      · calc
          φ (y - x) = φ y - φ x := AddMonoidHom.map_sub φ y x
          _ = ψ x - φ x := by rw [← hxy']
          _ = x := by
            dsimp [ψ]
            abel
      · calc
          ψ (y - x) = φ (y - x) + (y - x) := rfl
          _ = x + (y - x) := by
            congr 1
            calc
              φ (y - x) = φ y - φ x := AddMonoidHom.map_sub φ y x
              _ = ψ x - φ x := by rw [← hxy']
              _ = x := by
                dsimp [ψ]
                abel
          _ = y := by abel
    · intro z hz
      have hzψ : ψ z = y := hz.2
      calc
        z = ψ z - φ z := by
          dsimp [ψ]
          abel
        _ = y - x := by rw [hzψ, hz.1]


#check_dependency_graph "abelian_surjective_add_id_star_commute" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(Function.Commute ⇑φ fun a => φ a + a) ∧ ∀ (x y : A), (fun a => φ a + a) x = φ y → ∃! z, φ z = x ∧ (fun a => φ a + a) z = y\"},\"graphEdgeId\":\"h_goal\",\"premises\":[],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2404_abelian_surjective_add_id_star_commute\",\"reconstructedProofSha256\":\"5ad69869682c42ad676a89f591ed465ee0f23afa9a66d3ddad067fbbb9523b3b\",\"selectedEdgeCount\":1,\"theoremName\":\"abelian_surjective_add_id_star_commute\",\"topologySha256\":\"69f2cf3836ce8fc06e2967a6e32e72fdd62ebbb926a939b0967eab84873aa4af\"}"
