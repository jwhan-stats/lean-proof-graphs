import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1371_decktransformation_eq_id_of_fixed_point
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 49b9b585e041fe141c9e7bf83d6fcded9c12a63a2cdd4f73c72e7081daaf95bf
-- reconstructed_proof_sha256: 3c86b6251648168860a318a665f1cbd4177bacc040ae1d3e3aa41632e6f90926
-- selected_edge_count: 1

/- verified submission -/
theorem deckTransformation_eq_id_of_fixed_point
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace E]
    (p : E → B) (hp : Continuous p)
    (arc_lifting : ∀ (f : C(Set.Icc (0 : ℝ) 1, B))
      (t₀ : Set.Icc (0 : ℝ) 1) (e₀ : E), p e₀ = f t₀ →
        ∃! g : C(Set.Icc (0 : ℝ) 1, E),
          (∀ t, p (g t) = f t) ∧ g t₀ = e₀)
    (h : E ≃ₜ E) (hdeck : p ∘ h = p)
    {e : E} (he : h e = e) :
    h = Homeomorph.refl E := by
  apply Homeomorph.ext
  intro x
  let γ : Path e x := PathConnectedSpace.somePath e x
  let f : C(Set.Icc (0 : ℝ) 1, B) := ⟨fun t => p (γ t), hp.comp γ.continuous⟩
  let g₁ : C(Set.Icc (0 : ℝ) 1, E) := ⟨fun t => γ t, γ.continuous⟩
  let g₂ : C(Set.Icc (0 : ℝ) 1, E) := ⟨fun t => h (γ t), h.continuous.comp γ.continuous⟩
  have hbase : p e = f 0 := by
    exact (congrArg p γ.source).symm
  have huniq := arc_lifting f 0 e hbase
  have hg₁ : (∀ t, p (g₁ t) = f t) ∧ g₁ 0 = e := by
    constructor
    · intro t
      rfl
    · exact γ.source
  have hg₂ : (∀ t, p (g₂ t) = f t) ∧ g₂ 0 = e := by
    constructor
    · intro t
      exact congrFun hdeck (γ t)
    · calc
        g₂ 0 = h (γ 0) := rfl
        _ = h e := congrArg h γ.source
        _ = e := he
  have hg : g₁ = g₂ := huniq.unique hg₁ hg₂
  have hx : γ 1 = h (γ 1) := congrArg (fun g : C(Set.Icc (0 : ℝ) 1, E) => g 1) hg
  calc
    h x = h (γ 1) := by rw [γ.target]
    _ = γ 1 := hx.symm
    _ = x := γ.target


#check_dependency_graph "deckTransformation_eq_id_of_fixed_point" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"h = Homeomorph.refl E\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"PathConnectedSpace E\"},{\"name\":\"hp\",\"statement\":\"Continuous p\"},{\"name\":\"arc_lifting\",\"statement\":\"∀ (f : C(↑(Set.Icc 0 1), B)) (t₀ : ↑(Set.Icc 0 1)) (e₀ : E), p e₀ = f t₀ → ∃! g, (∀ (t : ↑(Set.Icc 0 1)), p (g t) = f t) ∧ g t₀ = e₀\"},{\"name\":\"hdeck\",\"statement\":\"p ∘ ⇑h = p\"},{\"name\":\"he\",\"statement\":\"h e = e\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1371_decktransformation_eq_id_of_fixed_point\",\"reconstructedProofSha256\":\"3c86b6251648168860a318a665f1cbd4177bacc040ae1d3e3aa41632e6f90926\",\"selectedEdgeCount\":1,\"theoremName\":\"deckTransformation_eq_id_of_fixed_point\",\"topologySha256\":\"49b9b585e041fe141c9e7bf83d6fcded9c12a63a2cdd4f73c72e7081daaf95bf\"}"
