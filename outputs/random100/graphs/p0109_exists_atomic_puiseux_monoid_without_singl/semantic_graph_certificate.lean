import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p0109_exists_atomic_puiseux_monoid_without_singl
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 1f8eb1a2dee6809ed1a7bee3e31417e9eae1d070ed67756f049a7393ee1739f4
-- reconstructed_proof_sha256: 86465e641a22ae41d707b46c4530d6e2d1cb16c849d6218821029248cc2ed7ad
-- selected_edge_count: 1

/- verified submission -/
theorem exists_atomic_puiseux_monoid_without_singleton_two_lengths :
    ∃ M : AddSubmonoid ℚ≥0,
      (∀ x : M, ∃ l : List M,
        (∀ a ∈ l, AddIrreducible a) ∧ l.sum = x) ∧
      (∀ x : M,
        {n : ℕ | ∃ l : List M,
          l.length = n ∧ (∀ a ∈ l, AddIrreducible a) ∧ l.sum = x} ≠ {2}) := by
  refine ⟨⊥, ?_, ?_⟩
  · intro x
    refine ⟨[], ?_, ?_⟩
    · intro a ha
      cases ha
    · change (0 : (⊥ : AddSubmonoid ℚ≥0)) = x
      apply Subtype.ext
      exact (x.property).symm
  · intro x h
    have h0 : 0 ∈ {n : ℕ | ∃ l : List (⊥ : AddSubmonoid ℚ≥0),
        l.length = n ∧ (∀ a ∈ l, AddIrreducible a) ∧ l.sum = x} := by
      refine ⟨[], rfl, ?_, ?_⟩
      · intro a ha
        cases ha
      · change (0 : (⊥ : AddSubmonoid ℚ≥0)) = x
        apply Subtype.ext
        exact (x.property).symm
    rw [h] at h0
    norm_num at h0


#check_dependency_graph "exists_atomic_puiseux_monoid_without_singleton_two_lengths" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∃ M, (∀ (x : ↥M), ∃ l, (∀ a ∈ l, AddIrreducible a) ∧ l.sum = x) ∧ ∀ (x : ↥M), {n | ∃ l, l.length = n ∧ (∀ a ∈ l, AddIrreducible a) ∧ l.sum = x} ≠ {2}\"},\"graphEdgeId\":\"h_goal\",\"premises\":[],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0109_exists_atomic_puiseux_monoid_without_singl\",\"reconstructedProofSha256\":\"86465e641a22ae41d707b46c4530d6e2d1cb16c849d6218821029248cc2ed7ad\",\"selectedEdgeCount\":1,\"theoremName\":\"exists_atomic_puiseux_monoid_without_singleton_two_lengths\",\"topologySha256\":\"1f8eb1a2dee6809ed1a7bee3e31417e9eae1d070ed67756f049a7393ee1739f4\"}"
