import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1335_quarter_stratifiable_diagonal_isgdelta_and
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: f6d5f2b5cdd3ab71e8e47d685829467cee1447f2787f921b97cf0a3b7dda70a0
-- reconstructed_proof_sha256: f30b800ea441ff0858d2c732e8184e5df22da3d512019b72e53f35ae716c25a0
-- selected_edge_count: 1

/- verified submission -/
theorem quarter_stratifiable_diagonal_isGDelta_and_countable_pseudocharacter
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (g : ℕ → X → Set X)
    (hg_open : ∀ n a, IsOpen (g n a))
    (hg_cover : ∀ n, ⋃ a, g n a = Set.univ)
    (hg_converges : ∀ (x : X) (a : ℕ → X),
      (∀ n, x ∈ g n (a n)) → Filter.Tendsto a Filter.atTop (nhds x)) :
    (∃ G : ℕ → Set (X × X),
      (∀ n, IsOpen (G n)) ∧
      Set.diagonal X = ⋂ n, G n) ∧
    ∀ x : X, ∃ V : ℕ → Set X,
      (∀ n, IsOpen (V n) ∧ x ∈ V n) ∧
      ⋂ n, V n = {x} := by
  classical
  constructor
  · refine ⟨fun n => ⋃ a, (g n a) ×ˢ (g n a), ?_, ?_⟩
    · intro n
      exact isOpen_iUnion fun a => (hg_open n a).prod (hg_open n a)
    · ext p
      constructor
      · intro hp
        rw [Set.mem_diagonal_iff] at hp
        rw [Set.mem_iInter]
        intro n
        have hc : p.1 ∈ ⋃ a, g n a := by
          rw [hg_cover n]
          trivial
        rw [Set.mem_iUnion] at hc
        rcases hc with ⟨a, hpa⟩
        rw [Set.mem_iUnion]
        exact ⟨a, by
          rw [Set.mem_prod]
          exact ⟨hpa, by simpa [hp] using hpa⟩⟩
      · intro hp
        rw [Set.mem_diagonal_iff]
        have hchoice : ∀ n, ∃ a, p.1 ∈ g n a ∧ p.2 ∈ g n a := by
          intro n
          have hpn : p ∈ ⋃ a, (g n a) ×ˢ (g n a) := Set.mem_iInter.mp hp n
          rw [Set.mem_iUnion] at hpn
          rcases hpn with ⟨a, hpa⟩
          exact ⟨a, Set.mem_prod.mp hpa⟩
        choose a ha using hchoice
        have hlim₁ := hg_converges p.1 a fun n => (ha n).1
        have hlim₂ := hg_converges p.2 a fun n => (ha n).2
        exact tendsto_nhds_unique hlim₁ hlim₂
  · intro x
    have hchoice : ∀ n, ∃ a, x ∈ g n a := by
      intro n
      have hx : x ∈ ⋃ a, g n a := by
        rw [hg_cover n]
        trivial
      rw [Set.mem_iUnion] at hx
      exact hx
    choose a ha using hchoice
    refine ⟨fun n => g n (a n), ?_, ?_⟩
    · intro n
      exact ⟨hg_open n (a n), ha n⟩
    · ext y
      constructor
      · intro hy
        have hy' : ∀ n, y ∈ g n (a n) := Set.mem_iInter.mp hy
        have hlimy := hg_converges y a hy'
        have hlimx := hg_converges x a ha
        have hyx : y = x := tendsto_nhds_unique hlimy hlimx
        simpa [hyx]
      · intro hy
        have hyx : y = x := by simpa using hy
        rw [Set.mem_iInter]
        intro n
        simpa [hyx] using ha n


#check_dependency_graph "quarter_stratifiable_diagonal_isGDelta_and_countable_pseudocharacter" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(∃ G, (∀ (n : ℕ), IsOpen (G n)) ∧ Set.diagonal X = ⋂ n, G n) ∧ ∀ (x : X), ∃ V, (∀ (n : ℕ), IsOpen (V n) ∧ x ∈ V n) ∧ ⋂ n, V n = {x}\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"T2Space X\"},{\"name\":\"hg_open\",\"statement\":\"∀ (n : ℕ) (a : X), IsOpen (g n a)\"},{\"name\":\"hg_cover\",\"statement\":\"∀ (n : ℕ), ⋃ a, g n a = Set.univ\"},{\"name\":\"hg_converges\",\"statement\":\"∀ (x : X) (a : ℕ → X), (∀ (n : ℕ), x ∈ g n (a n)) → Filter.Tendsto a Filter.atTop (nhds x)\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1335_quarter_stratifiable_diagonal_isgdelta_and\",\"reconstructedProofSha256\":\"f30b800ea441ff0858d2c732e8184e5df22da3d512019b72e53f35ae716c25a0\",\"selectedEdgeCount\":1,\"theoremName\":\"quarter_stratifiable_diagonal_isGDelta_and_countable_pseudocharacter\",\"topologySha256\":\"f6d5f2b5cdd3ab71e8e47d685829467cee1447f2787f921b97cf0a3b7dda70a0\"}"
