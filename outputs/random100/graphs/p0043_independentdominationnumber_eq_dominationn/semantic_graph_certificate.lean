import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p0043_independentdominationnumber_eq_dominationn
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: c61f4a83bcbad58f8e02ac4870c2a4154fb38a1c4798a2c300e2500f89251222
-- reconstructed_proof_sha256: 7aedf2967b66e6acc0db9287d6d4288dbd14f047917bab98e7d461eb6d5e7714
-- selected_edge_count: 1

/- accepted add_to_file helper 1 -/
def IsDominatingFinset {V : Type*} (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v : V, v ∉ D → ∃ w : V, w ∈ D ∧ G.Adj v w

def dominationCardinalities {V : Type*} [Fintype V] (G : SimpleGraph V) : Set ℕ :=
  {n : ℕ | ∃ D : Finset V, D.card = n ∧ IsDominatingFinset G D}

noncomputable def internalAdjPairs {V : Type*} (G : SimpleGraph V) (D : Finset V) : Finset (V × V) := by
  classical
  exact (D ×ˢ D).filter fun p : V × V => G.Adj p.1 p.2

noncomputable def internalAdjPairCount {V : Type*} (G : SimpleGraph V) (D : Finset V) : ℕ :=
  (internalAdjPairs G D).card

lemma exists_private_neighbor_of_min_dominating
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {n : ℕ} (hmin : ∀ E : Finset V, IsDominatingFinset G E → n ≤ E.card)
    {D : Finset V} (hDcard : D.card = n) (hDdom : IsDominatingFinset G D)
    {u v : V} (huD : u ∈ D) (hvD : v ∈ D) (huv : G.Adj u v) :
    ∃ p : V, p ∉ D ∧ G.Adj u p ∧ ∀ z : V, z ∈ D.erase u → ¬ G.Adj p z := by
  classical
  have hcard_erase_lt : (D.erase u).card < n := by
    rw [Finset.card_erase_of_mem huD, hDcard]
    have hpos : 0 < n := by
      rw [← hDcard]
      exact Finset.card_pos.mpr ⟨u, huD⟩
    omega
  have hnotdom : ¬ IsDominatingFinset G (D.erase u) := by
    intro hdom
    have hle := hmin (D.erase u) hdom
    omega
  unfold IsDominatingFinset at hnotdom
  push Not at hnotdom
  obtain ⟨x, hx_erase, hno⟩ := hnotdom
  by_cases hxD : x ∈ D
  · have hx_eq_u : x = u := by
      by_contra hxne
      exact hx_erase (Finset.mem_erase.mpr ⟨hxne, hxD⟩)
    subst x
    have hv_erase : v ∈ D.erase u := by
      exact Finset.mem_erase.mpr ⟨huv.ne.symm, hvD⟩
    exact False.elim (hno v hv_erase huv)
  · obtain ⟨z, hzD, hxz⟩ := hDdom x hxD
    have hz_eq_u : z = u := by
      by_contra hzne
      have hz_erase : z ∈ D.erase u := Finset.mem_erase.mpr ⟨hzne, hzD⟩
      exact hno z hz_erase hxz
    subst z
    exact ⟨x, hxD, (G.adj_comm x u).mp hxz, hno⟩

lemma internalAdjPairs_insert_private
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) {D : Finset V} {a p : V}
    (hpriv : ∀ z : V, z ∈ D.erase a → ¬ G.Adj p z) :
    internalAdjPairs G (insert p (D.erase a)) = internalAdjPairs G (D.erase a) := by
  classical
  ext q
  constructor
  · intro hq
    rw [internalAdjPairs, Finset.mem_filter] at hq ⊢
    obtain ⟨hqmem, hqadj⟩ := hq
    rw [Finset.mem_product] at hqmem ⊢
    have hq1' : q.1 = p ∨ q.1 ∈ D.erase a := by
      simpa [Finset.mem_insert] using hqmem.1
    have hq2' : q.2 = p ∨ q.2 ∈ D.erase a := by
      simpa [Finset.mem_insert] using hqmem.2
    rcases hq1' with hq1eq | hq1mem
    · rcases hq2' with hq2eq | hq2mem
      · have hdiag : q.1 = q.2 := hq1eq.trans hq2eq.symm
        rw [hdiag] at hqadj
        exact False.elim (G.irrefl hqadj)
      · rw [hq1eq] at hqadj
        exact False.elim (hpriv q.2 hq2mem hqadj)
    · rcases hq2' with hq2eq | hq2mem
      · have hqp : G.Adj p q.1 := by
          rw [hq2eq] at hqadj
          exact (G.adj_comm q.1 p).mp hqadj
        exact False.elim (hpriv q.1 hq1mem hqp)
      · exact ⟨⟨hq1mem, hq2mem⟩, hqadj⟩
  · intro hq
    rw [internalAdjPairs, Finset.mem_filter] at hq ⊢
    obtain ⟨hqmem, hqadj⟩ := hq
    rw [Finset.mem_product] at hqmem ⊢
    exact ⟨⟨Finset.mem_insert_of_mem hqmem.1, Finset.mem_insert_of_mem hqmem.2⟩, hqadj⟩

lemma internalAdjPairCount_erase_lt
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {D : Finset V} {a b : V} (ha : a ∈ D) (hb : b ∈ D.erase a)
    (hab : G.Adj a b) :
    internalAdjPairCount G (D.erase a) < internalAdjPairCount G D := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro q hq
    rw [internalAdjPairs, Finset.mem_filter, Finset.mem_product] at hq ⊢
    obtain ⟨⟨hq1, hq2⟩, hqadj⟩ := hq
    exact ⟨⟨(Finset.erase_subset a D) hq1, (Finset.erase_subset a D) hq2⟩, hqadj⟩
  · intro heq
    have hmem_full : (a,b) ∈ internalAdjPairs G D := by
      rw [internalAdjPairs, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨ha, (Finset.erase_subset a D) hb⟩, hab⟩
    have hmem_erase : (a,b) ∈ internalAdjPairs G (D.erase a) := by
      rw [heq]
      exact hmem_full
    rw [internalAdjPairs, Finset.mem_filter, Finset.mem_product] at hmem_erase
    exact (Finset.notMem_erase a D) hmem_erase.1.1

lemma min_dominating_independent
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hhigh : G.IsIndepSet {v : V | 2 < (G.neighborSet v).ncard}) :
    ∃ D : Finset V, D.card = sInf (dominationCardinalities G) ∧
      G.IsIndepSet (↑D : Set V) ∧ IsDominatingFinset G D := by
  classical
  let γ := sInf (dominationCardinalities G)
  have hnonempty : (dominationCardinalities G).Nonempty := by
    refine ⟨Fintype.card V, Finset.univ, ?_, ?_⟩
    · simp
    · intro v hv
      simp at hv
  have hγ_mem : γ ∈ dominationCardinalities G := Nat.sInf_mem hnonempty
  obtain ⟨D0, hD0card, hD0dom⟩ := hγ_mem
  let candidates : Finset (Finset V) :=
    Finset.univ.filter fun D : Finset V => D.card = γ ∧ IsDominatingFinset G D
  have hcandidates_nonempty : candidates.Nonempty := by
    refine ⟨D0, ?_⟩
    simp [candidates, hD0card, hD0dom]
  let cost : Finset V → ℕ := fun D => internalAdjPairCount G D
  obtain ⟨D, hDcandidate, hDmincost⟩ := Finset.exists_min_image candidates cost hcandidates_nonempty
  have hDprops : D.card = γ ∧ IsDominatingFinset G D := by
    simpa [candidates] using hDcandidate
  obtain ⟨hDcard, hDdom⟩ := hDprops
  have hγle : ∀ E : Finset V, IsDominatingFinset G E → γ ≤ E.card := by
    intro E hE
    exact Nat.sInf_le ⟨E, rfl, hE⟩
  refine ⟨D, hDcard, ?_, hDdom⟩
  by_contra hnotind
  rw [SimpleGraph.isIndepSet_iff] at hnotind
  unfold Set.Pairwise at hnotind
  push Not at hnotind
  obtain ⟨u, huD, v, hvD, huvne, huv⟩ := hnotind
  have hlow : ∃ a b : V, a ∈ D ∧ b ∈ D ∧ a ≠ b ∧ G.Adj a b ∧
      (G.neighborSet a).ncard ≤ 2 := by
    by_cases hu_high : 2 < (G.neighborSet u).ncard
    · have hv_not_high : ¬ 2 < (G.neighborSet v).ncard := by
        intro hv_high
        exact (hhigh hu_high hv_high huvne) huv
      exact ⟨v, u, hvD, huD, huvne.symm, (G.adj_comm u v).mp huv, not_lt.mp hv_not_high⟩
    · exact ⟨u, v, huD, hvD, huvne, huv, not_lt.mp hu_high⟩
  obtain ⟨a, b, haD, hbD, habne, hab, ha_low⟩ := hlow
  obtain ⟨p, hpD, hap, hprivate⟩ :=
    exists_private_neighbor_of_min_dominating G hγle hDcard hDdom haD hbD hab
  have hb_ne_p : b ≠ p := by
    intro h
    exact hpD (h ▸ hbD)
  have hneighbors_subset : ({b, p} : Set V) ⊆ G.neighborSet a := by
    intro z hz
    simp at hz
    rcases hz with hzb | hzp
    · rw [hzb]
      exact (G.mem_neighborSet a b).mpr hab
    · rw [hzp]
      exact (G.mem_neighborSet a p).mpr hap
  have hfiniteN : (G.neighborSet a).Finite := by
    exact Set.finite_univ.subset (by intro x hx; trivial)
  have hpair_card : ({b, p} : Set V).ncard = 2 := Set.ncard_pair hb_ne_p
  have hN_ge : 2 ≤ (G.neighborSet a).ncard := by
    rw [← hpair_card]
    exact Set.ncard_le_ncard hneighbors_subset hfiniteN
  have hN_card : (G.neighborSet a).ncard = 2 := le_antisymm ha_low hN_ge
  have hN_eq_pair : ({b, p} : Set V) = G.neighborSet a := by
    apply Set.eq_of_subset_of_ncard_le hneighbors_subset
    rw [hpair_card, hN_card]
  let D' : Finset V := insert p (D.erase a)
  have hp_not_erase : p ∉ D.erase a := by
    intro hp
    exact hpD ((Finset.erase_subset a D) hp)
  have hD'_card_D : D'.card = D.card := by
    dsimp [D']
    rw [Finset.card_insert_of_notMem hp_not_erase,
      Finset.card_erase_of_mem haD]
    have hDpos : 0 < D.card := Finset.card_pos.mpr ⟨a, haD⟩
    omega
  have hD'_card : D'.card = γ := by
    rw [hD'_card_D, hDcard]
  have hD'_dom : IsDominatingFinset G D' := by
    intro x hxD'
    by_cases hxD : x ∈ D
    · by_cases hxa : x = a
      · subst x
        exact ⟨p, by simp [D'], hap⟩
      · have hx_erase : x ∈ D.erase a := Finset.mem_erase.mpr ⟨hxa, hxD⟩
        exact False.elim (hxD' (Finset.mem_insert_of_mem hx_erase))
    · obtain ⟨z, hzD, hxz⟩ := hDdom x hxD
      by_cases hza : z = a
      · subst z
        have hxN : x ∈ G.neighborSet a :=
          (G.mem_neighborSet a x).mpr ((G.adj_comm x a).mp hxz)
        rw [← hN_eq_pair] at hxN
        simp at hxN
        rcases hxN with hxb | hxp
        · exact False.elim (hxD (hxb ▸ hbD))
        · exact False.elim (hxD' (hxp ▸ by simp [D']))
      · have hz_erase : z ∈ D.erase a := Finset.mem_erase.mpr ⟨hza, hzD⟩
        exact ⟨z, Finset.mem_insert_of_mem hz_erase, hxz⟩
  have hD'_candidate : D' ∈ candidates := by
    simp [candidates, hD'_card, hD'_dom]
  have hcost_eq : cost D' = cost (D.erase a) := by
    dsimp [cost, internalAdjPairCount]
    exact congrArg Finset.card (internalAdjPairs_insert_private G hprivate)
  have hb_erase : b ∈ D.erase a := Finset.mem_erase.mpr ⟨habne.symm, hbD⟩
  have hcost_lt : cost D' < cost D := by
    rw [hcost_eq]
    exact internalAdjPairCount_erase_lt G haD hb_erase hab
  have hcost_le := hDmincost D' hD'_candidate
  omega

/- verified submission -/
theorem independentDominationNumber_eq_dominationNumber
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hhigh : G.IsIndepSet {v : V | 2 < (G.neighborSet v).ncard}) :
    sInf {n : ℕ | ∃ D : Finset V,
      D.card = n ∧ G.IsIndepSet (↑D : Set V) ∧
        ∀ v : V, v ∉ D → ∃ w : V, w ∈ D ∧ G.Adj v w} =
    sInf {n : ℕ | ∃ D : Finset V,
      D.card = n ∧ ∀ v : V, v ∉ D → ∃ w : V, w ∈ D ∧ G.Adj v w} := by
  classical
  let independentCardinalities : Set ℕ :=
    {n : ℕ | ∃ D : Finset V,
      D.card = n ∧ G.IsIndepSet (↑D : Set V) ∧
        ∀ v : V, v ∉ D → ∃ w : V, w ∈ D ∧ G.Adj v w}
  let dominatingCardinalities : Set ℕ :=
    {n : ℕ | ∃ D : Finset V,
      D.card = n ∧ ∀ v : V, v ∉ D → ∃ w : V, w ∈ D ∧ G.Adj v w}
  change sInf independentCardinalities = sInf dominatingCardinalities
  obtain ⟨D, hDcard, hDind, hDdom⟩ := min_dominating_independent G hhigh
  have hdom_sets_eq : dominationCardinalities G = dominatingCardinalities := rfl
  have hDcard' : D.card = sInf dominatingCardinalities := by
    simpa [hdom_sets_eq] using hDcard
  have hI_nonempty : independentCardinalities.Nonempty := by
    exact ⟨sInf dominatingCardinalities, D, hDcard', hDind, hDdom⟩
  have hsubset : independentCardinalities ⊆ dominatingCardinalities := by
    intro n hn
    obtain ⟨E, hEcard, hEind, hEdom⟩ := hn
    exact ⟨E, hEcard, hEdom⟩
  have h_le_dom : sInf dominatingCardinalities ≤ sInf independentCardinalities := by
    exact Nat.sInf_le (hsubset (Nat.sInf_mem hI_nonempty))
  have h_le_ind : sInf independentCardinalities ≤ sInf dominatingCardinalities := by
    exact Nat.sInf_le ⟨D, hDcard', hDind, hDdom⟩
  exact le_antisymm h_le_ind h_le_dom


#check_dependency_graph "independentDominationNumber_eq_dominationNumber" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"sInf {n | ∃ D, D.card = n ∧ G.IsIndepSet ↑D ∧ ∀ v ∉ D, ∃ w ∈ D, G.Adj v w} = sInf {n | ∃ D, D.card = n ∧ ∀ v ∉ D, ∃ w ∈ D, G.Adj v w}\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hhigh\",\"statement\":\"G.IsIndepSet {v | 2 < (G.neighborSet v).ncard}\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0043_independentdominationnumber_eq_dominationn\",\"reconstructedProofSha256\":\"7aedf2967b66e6acc0db9287d6d4288dbd14f047917bab98e7d461eb6d5e7714\",\"selectedEdgeCount\":1,\"theoremName\":\"independentDominationNumber_eq_dominationNumber\",\"topologySha256\":\"c61f4a83bcbad58f8e02ac4870c2a4154fb38a1c4798a2c300e2500f89251222\"}"
