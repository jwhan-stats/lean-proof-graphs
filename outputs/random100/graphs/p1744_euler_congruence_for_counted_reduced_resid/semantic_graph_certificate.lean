import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1744_euler_congruence_for_counted_reduced_resid
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 28dc7b12bcf67d899a4a1555e8b39cf898bb49fb686730674b97db4492424394
-- reconstructed_proof_sha256: 1fab907a4efa03c9aa258ec39f0faa5dc83e0c7859b990645fa94f15b921edf4
-- selected_edge_count: 1

/- verified submission -/
theorem euler_congruence_for_counted_reduced_residues
    (N x n : ℕ) (hN : 0 < N) (hx : 0 < x)
    (hcoprime : Nat.Coprime x N)
    (hn : n = ((Finset.Ico 1 N).filter fun a => Nat.Coprime a N).card) :
    Nat.ModEq N (x ^ n) 1 := by
  by_cases hN1 : N = 1
  · subst N
    exact Nat.modEq_one
  · have hNgt : 1 < N := by omega
    have hsets :
        ((Finset.Ico 1 N).filter fun a => Nat.Coprime a N) =
          {a ∈ Finset.Ico 1 (1 + N) | N.Coprime a} := by
      ext a
      constructor
      · intro ha
        simp only [Finset.mem_filter, Finset.mem_Ico] at ha ⊢
        exact ⟨⟨ha.1.1, by omega⟩, ha.2.symm⟩
      · intro ha
        simp only [Finset.mem_filter, Finset.mem_Ico] at ha ⊢
        have ha_ne_N : a ≠ N := by
          intro h
          subst a
          have : N = 1 := (Nat.coprime_self N).mp ha.2
          omega
        exact ⟨⟨ha.1.1, by omega⟩, ha.2.symm⟩
    have hcard :
        ((Finset.Ico 1 N).filter fun a => Nat.Coprime a N).card = N.totient := by
      rw [hsets]
      exact Nat.filter_coprime_Ico_eq_totient N 1
    rw [hn, hcard]
    exact Nat.ModEq.pow_totient hcoprime


#check_dependency_graph "euler_congruence_for_counted_reduced_residues" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"x ^ n ≡ 1 [MOD N]\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hN\",\"statement\":\"0 < N\"},{\"name\":\"hcoprime\",\"statement\":\"x.Coprime N\"},{\"name\":\"hn\",\"statement\":\"n = {a ∈ Finset.Ico 1 N | a.Coprime N}.card\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1744_euler_congruence_for_counted_reduced_resid\",\"reconstructedProofSha256\":\"1fab907a4efa03c9aa258ec39f0faa5dc83e0c7859b990645fa94f15b921edf4\",\"selectedEdgeCount\":1,\"theoremName\":\"euler_congruence_for_counted_reduced_residues\",\"topologySha256\":\"28dc7b12bcf67d899a4a1555e8b39cf898bb49fb686730674b97db4492424394\"}"
