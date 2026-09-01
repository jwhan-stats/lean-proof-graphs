import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p0019_unique_diagonal_perfect_matching_iff_no_al
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: a1634d7f40419c801a109035bdeb7fe0590e91296c79e9c810f08e9363381342
-- reconstructed_proof_sha256: b243ec4df9709d2879cb7fb52ecaa6ace7b37f5054aaf31d25cfed2c8d268ddb
-- selected_edge_count: 2

/- accepted add_to_file helper 1 -/

open scoped BigOperators

section UniqueMatchingAlternating

variable {V : Type*} [Fintype V] {n : ℕ}
variable (G : SimpleGraph V) (x y : Fin n → V)

lemma sum_elim_bijective_x_injective
    (hxy : Function.Bijective (Sum.elim x y : Fin n ⊕ Fin n → V)) :
    Function.Injective x :=
  (Sum.elim_injective.mp hxy.injective).1

lemma sum_elim_bijective_y_injective
    (hxy : Function.Bijective (Sum.elim x y : Fin n ⊕ Fin n → V)) :
    Function.Injective y :=
  (Sum.elim_injective.mp hxy.injective).2.1

lemma sum_elim_bijective_x_ne_y
    (hxy : Function.Bijective (Sum.elim x y : Fin n ⊕ Fin n → V)) (i j : Fin n) :
    x i ≠ y j :=
  (Sum.elim_injective.mp hxy.injective).2.2 i j

lemma sum_elim_bijective_cases
    (hxy : Function.Bijective (Sum.elim x y : Fin n ⊕ Fin n → V)) (v : V) :
    (∃ i : Fin n, v = x i) ∨ (∃ i : Fin n, v = y i) := by
  obtain ⟨s, hs⟩ := hxy.surjective v
  cases s with
  | inl i => exact Or.inl ⟨i, hs.symm⟩
  | inr i => exact Or.inr ⟨i, hs.symm⟩

lemma no_adj_y_y_of_vertex_cover_range_x
    (hxy : Function.Bijective (Sum.elim x y : Fin n ⊕ Fin n → V))
    (hX : G.IsVertexCover (Set.range x)) {i j : Fin n} :
    ¬ G.Adj (y i) (y j) := by
  intro h
  rcases hX h with ⟨k, hki⟩ | ⟨k, hkj⟩
  · exact sum_elim_bijective_x_ne_y x y hxy k i hki
  · exact sum_elim_bijective_x_ne_y x y hxy k j hkj

end UniqueMatchingAlternating

/- accepted add_to_file helper 2 -/
section UniqueMatchingAlternating

variable {V : Type*} [Fintype V] {n : ℕ}
variable (G : SimpleGraph V) (x y : Fin n → V)

lemma maximal_independent_ncard_eq_of_minimal_covers
    (hxy : Function.Bijective (Sum.elim x y : Fin n ⊕ Fin n → V))
    (hunmixed : ∀ C : Set V, Minimal G.IsVertexCover C → C.ncard = n)
    {I : Set V} (hI : Maximal G.IsIndepSet I) : I.ncard = n := by
  have hcompl : Minimal G.IsVertexCover Iᶜ := by
    constructor
    · exact (SimpleGraph.isVertexCover_compl).2 hI.prop
    · intro C hC hsub
      have hInd : G.IsIndepSet Cᶜ := by
        have hVCcc : G.IsVertexCover (Cᶜ)ᶜ := by simpa using hC
        exact (SimpleGraph.isVertexCover_compl).1 hVCcc
      have hIC : I ⊆ Cᶜ := by
        intro v hvI hvC
        exact (hsub hvC) hvI
      have hCI : Cᶜ ⊆ I := hI.2 hInd hIC
      have : Iᶜ ⊆ C := by
        simpa using (Set.compl_subset_compl.mpr hCI)
      exact this
  have hcompn : Iᶜ.ncard = n := hunmixed Iᶜ hcompl
  have hsum : I.ncard + Iᶜ.ncard = Nat.card V := Set.ncard_add_ncard_compl I
  have hcard : Nat.card V = 2 * n := by
    have h := Fintype.card_congr (Equiv.ofBijective (Sum.elim x y : Fin n ⊕ Fin n → V) hxy)
    rw [Nat.card_eq_fintype_card]
    rw [← h]
    simp
    omega
  omega

end UniqueMatchingAlternating

/- accepted add_to_file helper 3 -/
section UniqueMatchingAlternating

variable {V : Type*} [Fintype V] {n : ℕ}
variable (x y : Fin n → V)

def diagonalGraph (hxy : Function.Bijective (Sum.elim x y : Fin n ⊕ Fin n → V)) : SimpleGraph V where
  Adj u v := ∃ i : Fin n, (u = x i ∧ v = y i) ∨ (u = y i ∧ v = x i)
  symm := by
    rintro u v ⟨i, h | h⟩
    · exact ⟨i, Or.inr ⟨h.2, h.1⟩⟩
    · exact ⟨i, Or.inl ⟨h.2, h.1⟩⟩
  loopless := ⟨by
    intro v
    rintro ⟨i, h | h⟩
    · exact sum_elim_bijective_x_ne_y x y hxy i i (h.1.symm.trans h.2)
    · exact sum_elim_bijective_x_ne_y x y hxy i i (h.2.symm.trans h.1)⟩

end UniqueMatchingAlternating

/- accepted add_to_file helper 4 -/
section UniqueMatchingAlternating

variable {V : Type*} [Fintype V] {n : ℕ}
variable (G : SimpleGraph V) (x y : Fin n → V)

lemma diagonalGraph_toSubgraph_isPerfectMatching
    (hxy : Function.Bijective (Sum.elim x y : Fin n ⊕ Fin n → V))
    (hdiag : ∀ i : Fin n, G.Adj (x i) (y i)) :
    (SimpleGraph.toSubgraph (diagonalGraph x y hxy) (by
      intro u v huv
      rcases huv with ⟨i, h | h⟩
      · rw [h.1, h.2]
        exact hdiag i
      · rw [h.1, h.2]
        exact (hdiag i).symm)).IsPerfectMatching := by
  let D := diagonalGraph x y hxy
  have hD : D ≤ G := by
    intro u v huv
    rcases huv with ⟨i, h | h⟩
    · rw [h.1, h.2]
      exact hdiag i
    · rw [h.1, h.2]
      exact (hdiag i).symm
  change (SimpleGraph.toSubgraph D hD).IsPerfectMatching
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro v
  rcases sum_elim_bijective_cases x y hxy v with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · refine ⟨y i, ?_, ?_⟩
    · change D.Adj (x i) (y i)
      exact ⟨i, Or.inl ⟨rfl, rfl⟩⟩
    · intro w hw
      change D.Adj (x i) w at hw
      rcases hw with ⟨j, h | h⟩
      · have hij : i = j := (sum_elim_bijective_x_injective x y hxy h.1)
        subst hij
        exact h.2
      · exact False.elim (sum_elim_bijective_x_ne_y x y hxy i j h.1)
  · refine ⟨x i, ?_, ?_⟩
    · change D.Adj (y i) (x i)
      exact ⟨i, Or.inr ⟨rfl, rfl⟩⟩
    · intro w hw
      change D.Adj (y i) w at hw
      rcases hw with ⟨j, h | h⟩
      · exact False.elim (sum_elim_bijective_x_ne_y x y hxy j i h.1.symm)
      · have hij : i = j := (sum_elim_bijective_y_injective x y hxy h.1)
        subst hij
        exact h.2

end UniqueMatchingAlternating

/- accepted add_to_file helper 5 -/
section UniqueMatchingAlternating

variable {V : Type*} [Fintype V] {n : ℕ}
variable (G : SimpleGraph V) (x y : Fin n → V)

lemma no_alternating_four_cycle_unordered
    (hdiag : ∀ i : Fin n, G.Adj (x i) (y i))
    (hB : ∀ i j : Fin n, i < j →
      ¬(G.Adj (x i) (y i) ∧ G.Adj (y i) (x j) ∧
        G.Adj (x j) (y j) ∧ G.Adj (y j) (x i)))
    {a b : Fin n} (hab : a ≠ b) :
    ¬(G.Adj (y a) (x b) ∧ G.Adj (y b) (x a)) := by
  intro h
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact hB a b hlt ⟨hdiag a, h.1, hdiag b, h.2⟩
  · exact hab heq
  · exact hB b a hgt ⟨hdiag b, h.2, hdiag a, h.1⟩

end UniqueMatchingAlternating

/- accepted add_to_file helper 6 -/
section UniqueMatchingAlternating

variable {V : Type*} [Fintype V] {n : ℕ}
variable (G : SimpleGraph V) (x y : Fin n → V)

def HasAlternatingIndexCycle (r : ℕ) : Prop :=
  ∃ i : Fin (r + 2) → Fin n, Function.Injective i ∧
    ∀ s : Fin (r + 2),
      G.Adj (x (i s)) (y (i s)) ∧
        G.Adj (y (i s)) (x (i (s + 1)))

end UniqueMatchingAlternating

/- accepted add_to_file helper 7 -/
section UniqueMatchingAlternating

variable {V : Type*} [Fintype V] {n : ℕ}
variable (G : SimpleGraph V) (x y : Fin n → V)

lemma no_chord_minimal_alternating_cycle
    (hdiag : ∀ i : Fin n, G.Adj (x i) (y i))
    {r : ℕ}
    (hmin : ∀ q < r, ¬ HasAlternatingIndexCycle G x y q)
    {i : Fin (r + 2) → Fin n} (hinj : Function.Injective i)
    (hedge : ∀ s : Fin (r + 2),
      G.Adj (x (i s)) (y (i s)) ∧
        G.Adj (y (i s)) (x (i (s + 1))))
    {d : Fin (r + 2)} (hd0 : d ≠ 0) (hd1 : d ≠ 1) :
    ¬ G.Adj (y (i 0)) (x (i d)) := by
  intro hch
  let R := r + 2
  have hdval0 : d.val ≠ 0 := by
    intro hv
    exact hd0 (Fin.ext hv)
  have hdval1 : d.val ≠ 1 := by
    intro hv
    apply hd1
    ext
    simp [hv]
  have hdval : 2 ≤ d.val := by omega
  let K := R - d.val
  have hK : K + d.val = R := by
    dsimp [K]
    omega
  have hKpos : 0 < K := by
    dsimp [K]
    have := d.isLt
    omega
  let L := K + 1
  let j0 : Fin L → Fin n :=
    fun u => if hu : u.val < K then
      i ⟨d.val + u.val, by omega⟩ else i 0
  have hj0inj : Function.Injective j0 := by
    intro a b h
    by_cases ha : a.val < K <;> by_cases hb : b.val < K
    · have hfin : (⟨d.val + a.val, by omega⟩ : Fin R) =
          ⟨d.val + b.val, by omega⟩ := hinj (by simpa [j0, ha, hb] using h)
      have hv := congrArg Fin.val hfin
      simp at hv
      exact Fin.ext (by omega)
    · have hfin : (⟨d.val + a.val, by omega⟩ : Fin R) = 0 :=
          hinj (by simpa [j0, ha, hb] using h)
      have hv := congrArg Fin.val hfin
      simp at hv
      omega
    · have hfin : (0 : Fin R) = ⟨d.val + b.val, by omega⟩ :=
          hinj (by simpa [j0, ha, hb] using h)
      have hv := congrArg Fin.val hfin
      simp at hv
      omega
    · have hav : a.val = K := by
        have := a.isLt
        dsimp [L] at this
        omega
      have hbv : b.val = K := by
        have := b.isLt
        dsimp [L] at this
        omega
      exact Fin.ext (by omega)
  have hj0edge : ∀ u : Fin L,
      G.Adj (x (j0 u)) (y (j0 u)) ∧
        G.Adj (y (j0 u)) (x (j0 (u + 1))) := by
    intro u
    refine ⟨by
      by_cases hu : u.val < K <;> simp [j0, hu, hdiag], ?_⟩
    by_cases hu : u.val < K
    · by_cases hu1 : u.val + 1 < K
      · let p : Fin R := ⟨d.val + u.val, by omega⟩
        have hcross : G.Adj (y (i p)) (x (i (p + 1))) := (hedge p).2
        have hnext : j0 (u + 1) = i (p + 1) := by
          have hvalu1 : (u + 1).val = u.val + 1 := by
            rw [Fin.val_add_one]
            have hne : u ≠ Fin.last K := by
              intro hulast
              have hv := congrArg Fin.val hulast
              simp [L] at hv
              omega
            simp [hne]
          have hcond : (u + 1).val < K := by omega
          dsimp [j0]
          rw [dif_pos hcond]
          apply congrArg i
          ext
          have hltR : d.val + u.val + 1 < R := by omega
          simp [p, hvalu1, Fin.val_add]
          rw [Nat.mod_eq_of_lt hltR]
          omega
        simpa [j0, p, hu, hnext] using hcross
      · have huval : u.val + 1 = K := by omega
        let p : Fin R := ⟨d.val + u.val, by omega⟩
        have hcross : G.Adj (y (i p)) (x (i (p + 1))) := (hedge p).2
        have hp1 : p + 1 = 0 := by
          ext
          have hpval : p.val + 1 = R := by
            dsimp [p]
            omega
          simp [Fin.val_add, hpval]
        have hnext : j0 (u + 1) = i 0 := by
          have hvalu1 : (u + 1).val = u.val + 1 := by
            rw [Fin.val_add_one]
            have hne : u ≠ Fin.last K := by
              intro hulast
              have hv := congrArg Fin.val hulast
              simp [L] at hv
              omega
            simp [hne]
          have hcond : ¬ (u + 1).val < K := by omega
          dsimp [j0]
          rw [dif_neg hcond]
        simpa [j0, p, hu, hnext, hp1] using hcross
    · have huval : u.val = K := by
        have := u.isLt
        dsimp [L] at this
        omega
      have hu_last : u = Fin.last K := by
        ext
        simp [L, huval]
      have hnext0 : j0 (u + 1) = j0 0 := by
        simp [hu_last]
      have hfirst : j0 0 = i d := by
        simp [j0, hKpos]
      have huself : j0 u = i 0 := by
        simp [j0, huval]
      rw [huself, hnext0, hfirst]
      exact hch
  let q := R - d.val - 1
  have hq : q < r := by
    dsimp [q, R]
    have := d.isLt
    omega
  have hL : q + 2 = L := by
    dsimp [q, L, K]
    have := d.isLt
    omega
  refine hmin q hq ⟨fun u => j0 (Fin.cast hL u), ?_, ?_⟩
  · intro a b h
    have hc : Fin.cast hL a = Fin.cast hL b := hj0inj h
    apply Fin.ext
    have hv := congrArg Fin.val hc
    simpa using hv
  · intro u
    have h := hj0edge (Fin.cast hL u)
    have hcastnext : Fin.cast hL (u + 1) = Fin.cast hL u + 1 := by
      ext
      simp [Fin.val_cast, Fin.val_add]
      exact congrArg (fun m => (u.val + 1) % m) hL
    simpa [hcastnext] using h

end UniqueMatchingAlternating

/- accepted add_to_file helper 8 -/
section UniqueMatchingAlternating

variable {V : Type*} [Fintype V] {n : ℕ}
variable (G : SimpleGraph V) (y : Fin n → V)

lemma no_adj_y_y_of_independent_range_y
    (hY : G.IsIndepSet (Set.range y)) {i j : Fin n} :
    ¬ G.Adj (y i) (y j) := by
  intro h
  by_cases hv : y i = y j
  · rw [hv] at h
    exact (G.loopless).irrefl (y j) h
  · exact hY (by exact ⟨i, rfl⟩) (by exact ⟨j, rfl⟩) hv h

end UniqueMatchingAlternating

/- accepted add_to_file helper 9 -/
lemma exists_function_cycle_of_injective_moved
    {α : Type*} [Fintype α] {σ : α → α} (hσ : Function.Injective σ)
    {a : α} (ha : σ a ≠ a) :
    ∃ r : ℕ, ∃ j : Fin (r + 2) → α, Function.Injective j ∧
      ∀ s : Fin (r + 2), j (s + 1) = σ (j s) := by
  let k := Function.minimalPeriod σ a
  have hper : a ∈ Function.periodicPts σ := hσ.mem_periodicPts a
  have hpos : 0 < k := Function.minimalPeriod_pos_of_mem_periodicPts hper
  have hk_ne_one : k ≠ 1 := by
    intro hk
    have hfix : Function.IsFixedPt σ a :=
      (Function.minimalPeriod_eq_one_iff_isFixedPt).1 hk
    exact ha hfix.eq
  have hk : 2 ≤ k := by omega
  let r := k - 2
  have hkr : k = r + 2 := by
    dsimp [r]
    omega
  refine ⟨r, fun s => σ^[s.val] a, ?_, ?_⟩
  · intro u v huv
    apply Fin.ext
    have hu : u.val < k := by omega
    have hv : v.val < k := by omega
    exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod hu hv).1 huv
  · intro s
    have hmod := (Function.iterate_mod_minimalPeriod_eq (f := σ) (x := a) (n := s.val + 1))
    change σ^[(s.val + 1) % k] a = σ^[s.val + 1] a at hmod
    have hval : (s + 1).val = (s.val + 1) % (r + 2) := by
      simp [Fin.val_add]
    have hmodulus : (s.val + 1) % (r + 2) = (s.val + 1) % k :=
      (congrArg (fun m => (s.val + 1) % m) hkr).symm
    have hvalk : (s + 1).val = (s.val + 1) % k := hval.trans hmodulus
    change σ^[(s + 1).val] a = σ (σ^[s.val] a)
    rw [hvalk, hmod, Function.iterate_succ_apply']

/- accepted add_to_file helper 10 -/
section UniqueMatchingAlternating

variable {V : Type*} [Fintype V] {n : ℕ}
variable (G : SimpleGraph V) (x y : Fin n → V)

lemma diagonal_toSubgraph_unique_of_no_cycles
    (hxy : Function.Bijective (Sum.elim x y : Fin n ⊕ Fin n → V))
    (hdiag : ∀ i : Fin n, G.Adj (x i) (y i))
    (hY : G.IsIndepSet (Set.range y))
    (hC : ∀ (r : ℕ) (i : Fin (r + 2) → Fin n), Function.Injective i →
      ¬(∀ s : Fin (r + 2),
        G.Adj (x (i s)) (y (i s)) ∧
          G.Adj (y (i s)) (x (i (s + 1)))))
    (M' : G.Subgraph) (hM' : M'.IsPerfectMatching) :
    M' = SimpleGraph.toSubgraph (diagonalGraph x y hxy) (by
      intro u v huv
      rcases huv with ⟨i, h | h⟩
      · rw [h.1, h.2]
        exact hdiag i
      · rw [h.1, h.2]
        exact (hdiag i).symm) := by
  let D := diagonalGraph x y hxy
  have hD : D ≤ G := by
    intro u v huv
    rcases huv with ⟨i, h | h⟩
    · rw [h.1, h.2]
      exact hdiag i
    · rw [h.1, h.2]
      exact (hdiag i).symm
  have hmate : ∀ v : V, ∃! w : V, M'.Adj v w :=
    (SimpleGraph.Subgraph.isPerfectMatching_iff).1 hM'
  let w : Fin n → V := fun i => Classical.choose (hmate (y i))
  have hw : ∀ i, M'.Adj (y i) (w i) ∧ ∀ z, M'.Adj (y i) z → z = w i := by
    intro i
    exact Classical.choose_spec (hmate (y i))
  have hxmate : ∀ i, ∃ k : Fin n, w i = x k := by
    intro i
    rcases sum_elim_bijective_cases x y hxy (w i) with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact ⟨k, hk⟩
    · have hbad : G.Adj (y i) (y k) := by
        rw [← hk]
        exact (hw i).1.adj_sub
      exact False.elim (no_adj_y_y_of_independent_range_y G y hY hbad)
  let σ : Fin n → Fin n := fun i => Classical.choose (hxmate i)
  have hσ : ∀ i, w i = x (σ i) := by
    intro i
    exact Classical.choose_spec (hxmate i)
  have hσadj : ∀ i, M'.Adj (y i) (x (σ i)) := by
    intro i
    rw [← hσ i]
    exact (hw i).1
  have hσinj : Function.Injective σ := by
    intro i j hij
    have hxi : M'.Adj (x (σ i)) (y i) := (hσadj i).symm
    have hxj : M'.Adj (x (σ i)) (y j) := by
      have h := hσadj j
      rw [← hij] at h
      exact h.symm
    have hspec := Classical.choose_spec (hmate (x (σ i)))
    have hyi : y i = Classical.choose (hmate (x (σ i))) := hspec.2 (y i) hxi
    have hyj : y j = Classical.choose (hmate (x (σ i))) := hspec.2 (y j) hxj
    have hy : y i = y j := hyi.trans hyj.symm
    exact (sum_elim_bijective_y_injective x y hxy) hy
  have hσid : σ = id := by
    by_contra hnot
    have hex : ∃ a, σ a ≠ a := by
      by_contra hall
      apply hnot
      funext a
      by_contra ha
      exact hall ⟨a, ha⟩
    obtain ⟨a, ha⟩ := hex
    obtain ⟨r, j, hinj, hcycle⟩ := exists_function_cycle_of_injective_moved hσinj ha
    exact hC r j hinj (by
      intro s
      constructor
      · exact hdiag (j s)
      · have h := (hσadj (j s)).adj_sub
        rwa [← hcycle s] at h)
  have hverts : M'.verts = (SimpleGraph.toSubgraph D hD).verts := by
    rw [SimpleGraph.toSubgraph_verts]
    exact Set.eq_univ_iff_forall.2 hM'.2
  apply SimpleGraph.Subgraph.ext hverts
  funext u v
  apply propext
  constructor
  · intro huv
    change D.Adj u v
    rcases sum_elim_bijective_cases x y hxy u with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · have hspec := Classical.choose_spec (hmate (x i))
      have hknown : M'.Adj (x i) (y i) := by
        have h := (hσadj i).symm
        simpa [hσid] using h
      have hv_eq : v = y i := by
        have hv := hspec.2 v huv
        have hy := hspec.2 (y i) hknown
        exact hv.trans hy.symm
      rw [hv_eq]
      exact ⟨i, Or.inl ⟨rfl, rfl⟩⟩
    · have hv_eq : v = x i := by
        have hspec := hw i
        have hv := hspec.2 v huv
        rw [hσ i, hσid] at hv
        exact hv
      rw [hv_eq]
      exact ⟨i, Or.inr ⟨rfl, rfl⟩⟩
  · intro huv
    change D.Adj u v at huv
    rcases huv with ⟨i, h | h⟩
    · rw [h.1, h.2]
      have h := (hσadj i).symm
      simpa [hσid] using h
    · rw [h.1, h.2]
      have h := hσadj i
      simpa [hσid] using h

end UniqueMatchingAlternating

/- accepted add_to_file helper 11 -/
section UniqueMatchingAlternating

variable {V : Type*} [Fintype V] {n : ℕ}
variable (x y : Fin n → V)

def swappedDiagonalGraph
    (hxy : Function.Bijective (Sum.elim x y : Fin n ⊕ Fin n → V))
    (i j : Fin n) : SimpleGraph V where
  Adj u v :=
    (∃ k : Fin n, k ≠ i ∧ k ≠ j ∧
      ((u = x k ∧ v = y k) ∨ (u = y k ∧ v = x k))) ∨
    ((u = y i ∧ v = x j) ∨ (u = x j ∧ v = y i)) ∨
    ((u = y j ∧ v = x i) ∨ (u = x i ∧ v = y j))
  symm := by
    rintro u v (⟨k, hki, hkj, h | h⟩ | (h | h) | (h | h))
    · exact Or.inl ⟨k, hki, hkj, Or.inr ⟨h.2, h.1⟩⟩
    · exact Or.inl ⟨k, hki, hkj, Or.inl ⟨h.2, h.1⟩⟩
    · exact Or.inr (Or.inl (Or.inr ⟨h.2, h.1⟩))
    · exact Or.inr (Or.inl (Or.inl ⟨h.2, h.1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))
  loopless := ⟨by
    intro v
    rintro (⟨k, hki, hkj, h | h⟩ | (h | h) | (h | h))
    · exact sum_elim_bijective_x_ne_y x y hxy k k (h.1.symm.trans h.2)
    · exact sum_elim_bijective_x_ne_y x y hxy k k (h.2.symm.trans h.1)
    · exact sum_elim_bijective_x_ne_y x y hxy j i (h.2.symm.trans h.1)
    · exact sum_elim_bijective_x_ne_y x y hxy j i (h.1.symm.trans h.2)
    · exact sum_elim_bijective_x_ne_y x y hxy i j (h.2.symm.trans h.1)
    · exact sum_elim_bijective_x_ne_y x y hxy i j (h.1.symm.trans h.2)⟩

end UniqueMatchingAlternating

/- accepted add_to_file helper 12 -/
section UniqueMatchingAlternating

variable {V : Type*} [Fintype V] {n : ℕ}
variable (x y : Fin n → V)

lemma swappedDiagonalGraph_adj_x
    (hxy : Function.Bijective (Sum.elim x y : Fin n ⊕ Fin n → V))
    {i j k : Fin n} (hij : i ≠ j) (w : V) :
    (swappedDiagonalGraph x y hxy i j).Adj (x k) w ↔
      (k = i ∧ w = y j) ∨ (k = j ∧ w = y i) ∨
        (k ≠ i ∧ k ≠ j ∧ w = y k) := by
  constructor
  · rintro (⟨l, hli, hlj, h | h⟩ | (h | h) | (h | h))
    · have hkl : k = l := sum_elim_bijective_x_injective x y hxy h.1
      subst hkl
      exact Or.inr (Or.inr ⟨hli, hlj, h.2⟩)
    · exact False.elim (sum_elim_bijective_x_ne_y x y hxy k l h.1)
    · exact False.elim (sum_elim_bijective_x_ne_y x y hxy k i h.1)
    · have hkj : k = j := sum_elim_bijective_x_injective x y hxy h.1
      subst hkj
      exact Or.inr (Or.inl ⟨rfl, h.2⟩)
    · exact False.elim (sum_elim_bijective_x_ne_y x y hxy k j h.1)
    · have hki : k = i := sum_elim_bijective_x_injective x y hxy h.1
      subst hki
      exact Or.inl ⟨rfl, h.2⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hki, hkj, rfl⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inl (Or.inr ⟨rfl, rfl⟩))
    · exact Or.inl ⟨k, hki, hkj, Or.inl ⟨rfl, rfl⟩⟩

end UniqueMatchingAlternating

/- accepted add_to_file helper 13 -/
section UniqueMatchingAlternating

variable {V : Type*} [Fintype V] {n : ℕ}
variable (G : SimpleGraph V) (x y : Fin n → V)

lemma exists_swapped_perfect_matching
    (hxy : Function.Bijective (Sum.elim x y : Fin n ⊕ Fin n → V))
    (hdiag : ∀ i : Fin n, G.Adj (x i) (y i))
    (hY : G.IsIndepSet (Set.range y))
    {i j : Fin n} (hij : i ≠ j)
    (hij1 : G.Adj (y i) (x j)) (hij2 : G.Adj (y j) (x i)) :
    ∃ M : G.Subgraph, M.IsPerfectMatching ∧ M.Adj (y i) (x j) := by
  let H := swappedDiagonalGraph x y hxy i j
  have hH : H ≤ G := by
    intro u v huv
    rcases huv with (⟨k, hki, hkj, h | h⟩ | (h | h) | (h | h))
    · rw [h.1, h.2]
      exact hdiag k
    · rw [h.1, h.2]
      exact (hdiag k).symm
    · rw [h.1, h.2]
      exact hij1
    · rw [h.1, h.2]
      exact hij1.symm
    · rw [h.1, h.2]
      exact hij2
    · rw [h.1, h.2]
      exact hij2.symm
  refine ⟨SimpleGraph.toSubgraph H hH, ?_, ?_⟩
  swap
  · rw [SimpleGraph.toSubgraph_adj]
    exact Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩))
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro v
  rcases sum_elim_bijective_cases x y hxy v with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · by_cases hki : k = i
    · subst k
      refine ⟨y j, ?_, ?_⟩
      · change (SimpleGraph.toSubgraph H hH).Adj (x i) (y j)
        rw [SimpleGraph.toSubgraph_adj]
        exact (swappedDiagonalGraph_adj_x x y hxy hij (y j)).2 (Or.inl ⟨rfl, rfl⟩)
      · intro w hw
        rw [SimpleGraph.toSubgraph_adj] at hw
        have hw' := (swappedDiagonalGraph_adj_x x y hxy hij w).1 hw
        rcases hw' with ⟨hki, hw⟩ | ⟨hkj, hw⟩ | ⟨hki, hkj, hw⟩
        · exact hw
        · exact False.elim (hij hkj)
        · exact False.elim (hki rfl)
    · by_cases hkj : k = j
      · subst k
        refine ⟨y i, ?_, ?_⟩
        · change (SimpleGraph.toSubgraph H hH).Adj (x j) (y i)
          rw [SimpleGraph.toSubgraph_adj]
          exact (swappedDiagonalGraph_adj_x x y hxy hij (y i)).2
            (Or.inr (Or.inl ⟨rfl, rfl⟩))
        · intro w hw
          rw [SimpleGraph.toSubgraph_adj] at hw
          have hw' := (swappedDiagonalGraph_adj_x x y hxy hij w).1 hw
          rcases hw' with ⟨hki, hw⟩ | ⟨hkj, hw⟩ | ⟨hki, hkj, hw⟩
          · exact False.elim (hij hki.symm)
          · exact hw
          · exact False.elim (hkj rfl)
      · refine ⟨y k, ?_, ?_⟩
        · change (SimpleGraph.toSubgraph H hH).Adj (x k) (y k)
          rw [SimpleGraph.toSubgraph_adj]
          exact (swappedDiagonalGraph_adj_x x y hxy hij (y k)).2
            (Or.inr (Or.inr ⟨hki, hkj, rfl⟩))
        · intro w hw
          rw [SimpleGraph.toSubgraph_adj] at hw
          have hw' := (swappedDiagonalGraph_adj_x x y hxy hij w).1 hw
          rcases hw' with ⟨hki', hw⟩ | ⟨hkj', hw⟩ | ⟨hki', hkj', hw⟩
          · exact False.elim (hki hki')
          · exact False.elim (hkj hkj')
          · exact hw
  · by_cases hki : k = i
    · subst k
      refine ⟨x j, ?_, ?_⟩
      · change (SimpleGraph.toSubgraph H hH).Adj (y i) (x j)
        rw [SimpleGraph.toSubgraph_adj]
        exact ((swappedDiagonalGraph_adj_x x y hxy hij (y i)).2
          (Or.inr (Or.inl ⟨rfl, rfl⟩))).symm
      · intro w hw
        rw [SimpleGraph.toSubgraph_adj] at hw
        rcases sum_elim_bijective_cases x y hxy w with ⟨l, rfl⟩ | ⟨l, rfl⟩
        · have hx : H.Adj (x l) (y i) := hw.symm
          have hx' := (swappedDiagonalGraph_adj_x x y hxy hij (y i)).1 hx
          rcases hx' with ⟨hli, hyl⟩ | ⟨hlj, hyl⟩ | ⟨hli, hlj, hyl⟩
          · have hij' : i = j := sum_elim_bijective_y_injective x y hxy hyl
            exact False.elim (hij hij')
          · rw [hlj]
          · have hil : i = l := sum_elim_bijective_y_injective x y hxy hyl
            exact False.elim (hli hil.symm)
        · have hbad : G.Adj (y i) (y l) := hH hw
          exact False.elim (no_adj_y_y_of_independent_range_y G y hY hbad)
    · by_cases hkj : k = j
      · subst k
        refine ⟨x i, ?_, ?_⟩
        · change (SimpleGraph.toSubgraph H hH).Adj (y j) (x i)
          rw [SimpleGraph.toSubgraph_adj]
          exact ((swappedDiagonalGraph_adj_x x y hxy hij (y j)).2
            (Or.inl ⟨rfl, rfl⟩)).symm
        · intro w hw
          rw [SimpleGraph.toSubgraph_adj] at hw
          rcases sum_elim_bijective_cases x y hxy w with ⟨l, rfl⟩ | ⟨l, rfl⟩
          · have hx : H.Adj (x l) (y j) := hw.symm
            have hx' := (swappedDiagonalGraph_adj_x x y hxy hij (y j)).1 hx
            rcases hx' with ⟨hli, hyl⟩ | ⟨hlj, hyl⟩ | ⟨hli, hlj, hyl⟩
            · rw [hli]
            · have hji : j = i := sum_elim_bijective_y_injective x y hxy hyl
              exact False.elim (hij hji.symm)
            · have hjl : j = l := sum_elim_bijective_y_injective x y hxy hyl
              exact False.elim (hlj hjl.symm)
          · have hbad : G.Adj (y j) (y l) := hH hw
            exact False.elim (no_adj_y_y_of_independent_range_y G y hY hbad)
      · refine ⟨x k, ?_, ?_⟩
        · change (SimpleGraph.toSubgraph H hH).Adj (y k) (x k)
          rw [SimpleGraph.toSubgraph_adj]
          exact ((swappedDiagonalGraph_adj_x x y hxy hij (y k)).2
            (Or.inr (Or.inr ⟨hki, hkj, rfl⟩))).symm
        · intro w hw
          rw [SimpleGraph.toSubgraph_adj] at hw
          rcases sum_elim_bijective_cases x y hxy w with ⟨l, rfl⟩ | ⟨l, rfl⟩
          · have hx : H.Adj (x l) (y k) := hw.symm
            have hx' := (swappedDiagonalGraph_adj_x x y hxy hij (y k)).1 hx
            rcases hx' with ⟨hli, hyl⟩ | ⟨hlj, hyl⟩ | ⟨hli, hlj, hyl⟩
            · have hkj' : k = j := sum_elim_bijective_y_injective x y hxy hyl
              exact False.elim (hkj hkj')
            · have hki' : k = i := sum_elim_bijective_y_injective x y hxy hyl
              exact False.elim (hki hki')
            · have hkl : k = l := sum_elim_bijective_y_injective x y hxy hyl
              rw [hkl.symm]
          · have hbad : G.Adj (y k) (y l) := hH hw
            exact False.elim (no_adj_y_y_of_independent_range_y G y hY hbad)

end UniqueMatchingAlternating

/- accepted add_to_file helper 14 -/
section UniqueMatchingAlternating

variable {V : Type*} [Fintype V] {n : ℕ}
variable (G : SimpleGraph V) (x y : Fin n → V)

lemma no_minimal_alternating_cycle_of_wellcovered
    (hxy : Function.Bijective (Sum.elim x y : Fin n ⊕ Fin n → V))
    (hdiag : ∀ i : Fin n, G.Adj (x i) (y i))
    (hY : G.IsIndepSet (Set.range y))
    (hunmixed : ∀ C : Set V, Minimal G.IsVertexCover C → C.ncard = n)
    {r : ℕ} (hr : 1 ≤ r)
    (hmin : ∀ q < r, ¬ HasAlternatingIndexCycle G x y q)
    {i : Fin (r + 2) → Fin n} (hinj : Function.Injective i)
    (hedge : ∀ s : Fin (r + 2),
      G.Adj (x (i s)) (y (i s)) ∧
        G.Adj (y (i s)) (x (i (s + 1)))) : False := by
  let R := r + 2
  have hchord : ∀ a b : Fin R,
      G.Adj (y (i a)) (x (i b)) → b = a ∨ b = a + 1 := by
    intro a b hab
    let ir : Fin R → Fin n := i ∘ fun s => s + a
    have hinjr : Function.Injective ir := by
      dsimp [ir]
      exact hinj.comp (add_left_injective a)
    have hedger : ∀ s : Fin R,
        G.Adj (x (ir s)) (y (ir s)) ∧
          G.Adj (y (ir s)) (x (ir (s + 1))) := by
      intro s
      have h := hedge (s + a)
      constructor
      · simpa [ir] using h.1
      · have hnext : s + a + 1 = (s + 1) + a := by abel
        simpa [ir, hnext] using h.2
    by_cases hd0 : b - a = 0
    · left
      exact sub_eq_zero.mp hd0
    · by_cases hd1 : b - a = 1
      · right
        have hb := eq_add_of_sub_eq hd1
        simpa [add_comm] using hb
      · have hno := no_chord_minimal_alternating_cycle G x y hdiag hmin hinjr hedger
          (d := b - a) hd0 hd1
        have hrot : G.Adj (y (ir 0)) (x (ir (b - a))) := by
          have hb : b - a + a = b := sub_add_cancel b a
          simpa [ir, hb] using hab
        exact False.elim (hno hrot)
  let p : Fin R := ⟨r + 1, by omega⟩
  let q : Fin R := ⟨r, by omega⟩
  have hp1 : p + 1 = 0 := by
    ext
    simp [p, R, Fin.val_add]
  have hq1 : q + 1 = p := by
    ext
    simp [p, q, R, Fin.val_add]
  have hq0 : q ≠ 0 := by
    apply Fin.ne_of_val_ne
    simp [q]
    omega
  have hqp : q ≠ p := by
    have hp0 : p ≠ 0 := by
      apply Fin.ne_of_val_ne
      simp [p]
    intro hqp
    rw [hqp, hp1] at hq1
    exact hp0 hq1.symm
  let S : Set V := {v | v = x (i 0) ∨ ∃ t : Fin R, t ≠ 0 ∧ t ≠ p ∧ v = y (i t)}
  have hS : G.IsIndepSet S := by
    rw [SimpleGraph.IsIndepSet]
    intro u hu v hv hne hadj
    rcases hu with rfl | ⟨a, ha0, hap, rfl⟩
    · rcases hv with rfl | ⟨b, hb0, hbp, rfl⟩
      · exact hne rfl
      · have h := hchord b 0 hadj.symm
        rcases h with hb | hb
        · exact hb0 hb.symm
        · have hb_eq_p : b = p := by
            have hadd : b + 1 = p + 1 := by
              rw [← hb, hp1]
            exact add_left_injective 1 hadd
          exact hbp hb_eq_p
    · rcases hv with rfl | ⟨b, hb0, hbp, rfl⟩
      · have h := hchord a 0 hadj
        rcases h with ha | ha
        · exact ha0 ha.symm
        · have ha_eq_p : a = p := by
            have hadd : a + 1 = p + 1 := by
              rw [← ha, hp1]
            exact add_left_injective 1 hadd
          exact hap ha_eq_p
      · exact no_adj_y_y_of_independent_range_y G y hY hadj
  obtain ⟨T, hST, hTmax⟩ := Finite.exists_le_maximal hS
  have hx0S : x (i 0) ∈ S := by
    dsimp [S]
    exact Or.inl rfl
  have hyqS : y (i q) ∈ S := by
    dsimp [S]
    exact Or.inr ⟨q, hq0, hqp, rfl⟩
  have hxp_notT : x (i p) ∉ T := by
    intro hxpT
    have hyqT : y (i q) ∈ T := hST hyqS
    have hneq : y (i q) ≠ x (i p) :=
      (sum_elim_bijective_x_ne_y x y hxy (i p) (i q)).symm
    have hadj : G.Adj (y (i q)) (x (i p)) := by
      simpa [hq1] using (hedge q).2
    exact hTmax.prop hyqT hxpT hneq hadj
  have hyp_notT : y (i p) ∉ T := by
    intro hypT
    have hx0T : x (i 0) ∈ T := hST hx0S
    have hneq : x (i 0) ≠ y (i p) :=
      sum_elim_bijective_x_ne_y x y hxy (i 0) (i p)
    have hadj : G.Adj (x (i 0)) (y (i p)) := by
      have h := (hedge p).2
      rw [hp1] at h
      exact h.symm
    exact hTmax.prop hx0T hypT hneq hadj
  haveI : Nonempty (Fin n ⊕ Fin n) := ⟨Sum.inl (i 0)⟩
  let f : V → Fin n ⊕ Fin n := Function.invFun (Sum.elim x y : Fin n ⊕ Fin n → V)
  have hf : Function.LeftInverse f (Sum.elim x y : Fin n ⊕ Fin n → V) :=
    Function.leftInverse_invFun hxy.injective
  let idx : V → Fin n := fun v => Sum.elim id id (f v)
  have hidx_x (a : Fin n) : idx (x a) = a := by
    have h := hf (Sum.inl a)
    simpa [idx, f] using congrArg (Sum.elim id id) h
  have hidx_y (a : Fin n) : idx (y a) = a := by
    have h := hf (Sum.inr a)
    simpa [idx, f] using congrArg (Sum.elim id id) h
  have hidx_inj : Set.InjOn idx T := by
    intro u hu v hv huv
    rcases sum_elim_bijective_cases x y hxy u with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · rcases sum_elim_bijective_cases x y hxy v with ⟨b, rfl⟩ | ⟨b, rfl⟩
      · have hab : a = b := by
          simpa [hidx_x, hidx_y] using huv
        subst hab
        rfl
      · have hab : a = b := by
          simpa [hidx_x, hidx_y] using huv
        subst hab
        have hneq : x a ≠ y a := sum_elim_bijective_x_ne_y x y hxy a a
        exact False.elim (hTmax.prop hu hv hneq (hdiag a))
    · rcases sum_elim_bijective_cases x y hxy v with ⟨b, rfl⟩ | ⟨b, rfl⟩
      · have hab : a = b := by
          simpa [hidx_x, hidx_y] using huv
        subst hab
        have hneq : y a ≠ x a :=
          (sum_elim_bijective_x_ne_y x y hxy a a).symm
        exact False.elim (hTmax.prop hu hv hneq (hdiag a).symm)
      · have hab : a = b := by
          simpa [hidx_x, hidx_y] using huv
        subst hab
        rfl
  have hnot_image : i p ∉ idx '' T := by
    rintro ⟨v, hvT, hvid⟩
    rcases sum_elim_bijective_cases x y hxy v with ⟨a, rfl⟩ | ⟨a, rfl⟩
    · have hai : a = i p := by
        simpa [hidx_x] using hvid
      subst hai
      exact hxp_notT hvT
    · have hai : a = i p := by
        simpa [hidx_y] using hvid
      subst hai
      exact hyp_notT hvT
  have hsub : idx '' T ⊆ ({i p}ᶜ : Set (Fin n)) := by
    intro k hk
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hk
    subst hk
    exact hnot_image hk
  have hcard_image : (idx '' T).ncard = T.ncard :=
    Set.ncard_image_of_injOn hidx_inj
  have hle : (idx '' T).ncard ≤ ({i p}ᶜ : Set (Fin n)).ncard :=
    Set.ncard_le_ncard hsub
  have hcompl : ({i p}ᶜ : Set (Fin n)).ncard = n - 1 := by
    rw [Set.ncard_compl]
    simp [Nat.card_eq_fintype_card]
  have hTcard : T.ncard = n :=
    maximal_independent_ncard_eq_of_minimal_covers G x y hxy hunmixed hTmax
  have hnpos : 0 < n := by
    have hlt := (i 0).isLt
    omega
  omega

end UniqueMatchingAlternating

/- verified submission -/
theorem unique_diagonal_perfect_matching_iff_no_alternating_cycle
    {V : Type*} [Fintype V] {n : ℕ} (hn : 1 ≤ n)
    (G : SimpleGraph V) (x y : Fin n → V)
    (hxy : Function.Bijective (Sum.elim x y : Fin n ⊕ Fin n → V))
    (h_no_isolated : ∀ v : V, ∃ w : V, G.Adj v w)
    (hX : Minimal G.IsVertexCover (Set.range x))
    (hY : Maximal G.IsIndepSet (Set.range y))
    (hdiag : ∀ i : Fin n, G.Adj (x i) (y i))
    (hunmixed : ∀ C : Set V, Minimal G.IsVertexCover C → C.ncard = n) :
    ((∃ M : G.Subgraph,
        M.IsPerfectMatching ∧
          (∀ u v : V, M.Adj u v ↔
            ∃ i : Fin n,
              (u = x i ∧ v = y i) ∨ (u = y i ∧ v = x i)) ∧
          ∀ M' : G.Subgraph, M'.IsPerfectMatching → M' = M) ↔
      ∀ i j : Fin n, i < j →
        ¬(G.Adj (x i) (y i) ∧ G.Adj (y i) (x j) ∧
          G.Adj (x j) (y j) ∧ G.Adj (y j) (x i))) ∧
    ((∀ i j : Fin n, i < j →
        ¬(G.Adj (x i) (y i) ∧ G.Adj (y i) (x j) ∧
          G.Adj (x j) (y j) ∧ G.Adj (y j) (x i))) ↔
      ∀ (r : ℕ) (i : Fin (r + 2) → Fin n), Function.Injective i →
        ¬(∀ s : Fin (r + 2),
          G.Adj (x (i s)) (y (i s)) ∧
            G.Adj (y (i s)) (x (i (s + 1))))) := by
  classical
  let B : Prop := ∀ i j : Fin n, i < j →
    ¬(G.Adj (x i) (y i) ∧ G.Adj (y i) (x j) ∧
      G.Adj (x j) (y j) ∧ G.Adj (y j) (x i))
  let C : Prop := ∀ (r : ℕ) (i : Fin (r + 2) → Fin n), Function.Injective i →
    ¬(∀ s : Fin (r + 2),
      G.Adj (x (i s)) (y (i s)) ∧
        G.Adj (y (i s)) (x (i (s + 1))))
  have hBC : B ↔ C := by
    constructor
    · intro hB r i hinj hcycle
      have hex : ∃ q : ℕ, HasAlternatingIndexCycle G x y q := ⟨r, i, hinj, hcycle⟩
      have hm0 : Nat.find hex ≠ 0 := by
        intro hm
        have hwit0 : HasAlternatingIndexCycle G x y 0 := by
          simpa [hm] using Nat.find_spec hex
        obtain ⟨j, hinjj, hedge⟩ := hwit0
        have hne : j 0 ≠ j 1 := hinjj.ne (by decide : (0 : Fin 2) ≠ 1)
        have hno := no_alternating_four_cycle_unordered G x y hdiag hB hne
        apply hno
        constructor
        · exact (hedge 0).2
        · have h := (hedge 1).2
          have hwrap : (1 : Fin 2) + 1 = 0 := by decide
          simpa [hwrap] using h
      have hmwit : HasAlternatingIndexCycle G x y (Nat.find hex) := Nat.find_spec hex
      obtain ⟨j, hinjj, hedge⟩ := hmwit
      have hm : 1 ≤ Nat.find hex := Nat.pos_of_ne_zero hm0
      have hmin : ∀ q < Nat.find hex, ¬ HasAlternatingIndexCycle G x y q := by
        intro q hq
        exact Nat.find_min hex hq
      exact no_minimal_alternating_cycle_of_wellcovered G x y hxy hdiag hY.prop hunmixed
        hm hmin hinjj hedge
    · intro hC i j hij hfour
      let seq : Fin 2 → Fin n := fun s => if s = 0 then i else j
      have hseqinj : Function.Injective seq := by
        intro a b h
        fin_cases a <;> fin_cases b
        · rfl
        · simp [seq] at h
          exact False.elim ((ne_of_lt hij) h)
        · simp [seq] at h
          exact False.elim ((ne_of_lt hij) h.symm)
        · rfl
      apply hC 0 seq hseqinj
      intro s
      fin_cases s
      · simp [seq]
        exact ⟨hfour.1, hfour.2.1⟩
      · simp [seq]
        constructor
        · exact hfour.2.2.1
        · have hwrap : (1 : Fin 2) + 1 = 0 := by decide
          simpa [seq, hwrap] using hfour.2.2.2
  constructor
  · constructor
    · rintro ⟨M, hM, hMadj, huniq⟩
      intro i j hij hfour
      have hijne : i ≠ j := ne_of_lt hij
      obtain ⟨M₂, hM₂, hcross⟩ := exists_swapped_perfect_matching G x y hxy hdiag hY.prop
        hijne hfour.2.1 hfour.2.2.2
      have hM₂eq : M₂ = M := huniq M₂ hM₂
      have hMcross : M.Adj (y i) (x j) := by
        rw [← hM₂eq]
        exact hcross
      obtain ⟨k, h | h⟩ := (hMadj (y i) (x j)).1 hMcross
      · exact sum_elim_bijective_x_ne_y x y hxy k i h.1.symm
      · have hki : k = i := (sum_elim_bijective_y_injective x y hxy h.1).symm
        have hkj : k = j := (sum_elim_bijective_x_injective x y hxy h.2).symm
        exact hijne (hki.symm.trans hkj)
    · intro hB
      have hC : C := hBC.1 hB
      let D := diagonalGraph x y hxy
      have hD : D ≤ G := by
        intro u v huv
        rcases huv with ⟨i, h | h⟩
        · rw [h.1, h.2]
          exact hdiag i
        · rw [h.1, h.2]
          exact (hdiag i).symm
      refine ⟨SimpleGraph.toSubgraph D hD, ?_, ?_, ?_⟩
      · exact diagonalGraph_toSubgraph_isPerfectMatching G x y hxy hdiag
      · intro u v
        rw [SimpleGraph.toSubgraph_adj]
        rfl
      · intro M' hM'
        exact diagonal_toSubgraph_unique_of_no_cycles G x y hxy hdiag hY.prop hC M' hM'
  · exact hBC


#check_dependency_graph "unique_diagonal_perfect_matching_iff_no_alternating_cycle" against "{\"edges\":[{\"conclusion\":{\"name\":\"hBC\",\"statement\":\"B ↔ C\"},\"graphEdgeId\":\"h_001_hbc\",\"premises\":[{\"name\":\"hxy\",\"statement\":\"Function.Bijective (Sum.elim x y)\"},{\"name\":\"hY\",\"statement\":\"Maximal G.IsIndepSet (Set.range y)\"},{\"name\":\"hdiag\",\"statement\":\"∀ (i : Fin n), G.Adj (x i) (y i)\"},{\"name\":\"hunmixed\",\"statement\":\"∀ (C : Set V), Minimal G.IsVertexCover C → C.ncard = n\"}],\"rawEdgeId\":\"telescope_15\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"((∃ M, M.IsPerfectMatching ∧ (∀ (u v : V), M.Adj u v ↔ ∃ i, u = x i ∧ v = y i ∨ u = y i ∧ v = x i) ∧ ∀ (M' : G.Subgraph), M'.IsPerfectMatching → M' = M) ↔ ∀ (i j : Fin n), i < j → ¬(G.Adj (x i) (y i) ∧ G.Adj (y i) (x j) ∧ G.Adj (x j) (y j) ∧ G.Adj (y j) (x i))) ∧ ((∀ (i j : Fin n), i < j → ¬(G.Adj (x i) (y i) ∧ G.Adj (y i) (x j) ∧ G.Adj (x j) (y j) ∧ G.Adj (y j) (x i))) ↔ ∀ (r : ℕ) (i : Fin (r + 2) → Fin n), Function.Injective i → ¬∀ (s : Fin (r + 2)), G.Adj (x (i s)) (y (i s)) ∧ G.Adj (y (i s)) (x (i (s + 1))))\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hxy\",\"statement\":\"Function.Bijective (Sum.elim x y)\"},{\"name\":\"hY\",\"statement\":\"Maximal G.IsIndepSet (Set.range y)\"},{\"name\":\"hdiag\",\"statement\":\"∀ (i : Fin n), G.Adj (x i) (y i)\"},{\"name\":\"hBC\",\"statement\":\"B ↔ C\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0019_unique_diagonal_perfect_matching_iff_no_al\",\"reconstructedProofSha256\":\"b243ec4df9709d2879cb7fb52ecaa6ace7b37f5054aaf31d25cfed2c8d268ddb\",\"selectedEdgeCount\":2,\"theoremName\":\"unique_diagonal_perfect_matching_iff_no_alternating_cycle\",\"topologySha256\":\"a1634d7f40419c801a109035bdeb7fe0590e91296c79e9c810f08e9363381342\"}"
