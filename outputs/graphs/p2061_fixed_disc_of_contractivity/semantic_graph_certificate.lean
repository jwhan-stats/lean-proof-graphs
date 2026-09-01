import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p2061_fixed_disc_of_contractivity
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: cdaf7feb9a824a85005a206c49841c05ff511f246426e3bdb3992b5cb809e336
-- reconstructed_proof_sha256: 14a2e8f7c45aef925550aa76973c623083cf4d281916d470461e3b14635aefec
-- selected_edge_count: 1

/- verified submission -/
theorem fixed_disc_of_contractivity
    {X : Type*} [MetricSpace X]
    (T : X → X) (x₀ : X) (c : ℝ)
    (hc₀ : 0 ≤ c) (hc₁ : c < 1)
    (hcontractive : ∀ x : X, dist (T x) x ≤ c * dist (T x) x₀) :
    let ρ : ℝ := sInf {r : ℝ | ∃ x : X, T x ≠ x ∧ r = dist x (T x)}
    (∀ x : X, dist x x₀ ≤ ρ → x ≠ x₀ →
      0 < dist (T x) x₀ ∧ dist (T x) x₀ ≤ ρ) →
    ∀ x : X, dist x x₀ ≤ ρ → T x = x := by
  dsimp only
  intro h x hx
  by_cases hx0 : x = x₀
  · subst x
    by_cases hdpos : 0 < dist (T x₀) x₀
    · have hlt : c * dist (T x₀) x₀ < dist (T x₀) x₀ := by
        simpa using mul_lt_mul_of_pos_right hc₁ hdpos
      exact (not_lt_of_ge (hcontractive x₀) hlt).elim
    · have hd : dist (T x₀) x₀ = 0 := by
        exact le_antisymm (not_lt.mp hdpos) dist_nonneg
      exact dist_eq_zero.mp hd
  · by_contra hTx
    let S : Set ℝ := {r : ℝ | ∃ y : X, T y ≠ y ∧ r = dist y (T y)}
    have hSbdd : BddBelow S := by
      refine ⟨0, ?_⟩
      intro r hr
      rcases hr with ⟨y, hy, rfl⟩
      exact dist_nonneg
    have hSmem : dist x (T x) ∈ S := ⟨x, hTx, rfl⟩
    have hρ_le : sInf S ≤ dist x (T x) := csInf_le hSbdd hSmem
    have ha := h x hx hx0
    have hcon : dist x (T x) ≤ c * dist (T x) x₀ := by
      simpa [dist_comm] using hcontractive x
    have hlt : c * dist (T x) x₀ < dist (T x) x₀ := by
      simpa using mul_lt_mul_of_pos_right hc₁ ha.1
    have : sInf S < sInf S := by
      exact lt_of_lt_of_le
        (lt_of_le_of_lt (le_trans hρ_le hcon) hlt)
        ha.2
    exact (lt_irrefl (sInf S) this).elim


#check_dependency_graph "fixed_disc_of_contractivity" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let ρ := sInf {r | ∃ x, T x ≠ x ∧ r = dist x (T x)}; (∀ (x : X), dist x x₀ ≤ ρ → x ≠ x₀ → 0 < dist (T x) x₀ ∧ dist (T x) x₀ ≤ ρ) → ∀ (x : X), dist x x₀ ≤ ρ → T x = x\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hc₁\",\"statement\":\"c < 1\"},{\"name\":\"hcontractive\",\"statement\":\"∀ (x : X), dist (T x) x ≤ c * dist (T x) x₀\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2061_fixed_disc_of_contractivity\",\"reconstructedProofSha256\":\"14a2e8f7c45aef925550aa76973c623083cf4d281916d470461e3b14635aefec\",\"selectedEdgeCount\":1,\"theoremName\":\"fixed_disc_of_contractivity\",\"topologySha256\":\"cdaf7feb9a824a85005a206c49841c05ff511f246426e3bdb3992b5cb809e336\"}"
