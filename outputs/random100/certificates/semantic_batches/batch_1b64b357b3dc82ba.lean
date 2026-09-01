import GraphCertificate
import Mathlib

namespace Rollout_p0019_unique_diagonal_perfect_matching_iff_no_al

-- graph_id: p0019_unique_diagonal_perfect_matching_iff_no_al
-- topology_sha256: a1634d7f40419c801a109035bdeb7fe0590e91296c79e9c810f08e9363381342
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

end Rollout_p0019_unique_diagonal_perfect_matching_iff_no_al

#check_dependency_graph "Rollout_p0019_unique_diagonal_perfect_matching_iff_no_al.unique_diagonal_perfect_matching_iff_no_alternating_cycle" against "{\"edges\":[{\"conclusion\":{\"name\":\"hBC\",\"statement\":\"B ↔ C\"},\"graphEdgeId\":\"h_001_hbc\",\"premises\":[{\"name\":\"hxy\",\"statement\":\"Function.Bijective (Sum.elim x y)\"},{\"name\":\"hY\",\"statement\":\"Maximal G.IsIndepSet (Set.range y)\"},{\"name\":\"hdiag\",\"statement\":\"∀ (i : Fin n), G.Adj (x i) (y i)\"},{\"name\":\"hunmixed\",\"statement\":\"∀ (C : Set V), Minimal G.IsVertexCover C → C.ncard = n\"}],\"rawEdgeId\":\"telescope_15\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"((∃ M, M.IsPerfectMatching ∧ (∀ (u v : V), M.Adj u v ↔ ∃ i, u = x i ∧ v = y i ∨ u = y i ∧ v = x i) ∧ ∀ (M' : G.Subgraph), M'.IsPerfectMatching → M' = M) ↔ ∀ (i j : Fin n), i < j → ¬(G.Adj (x i) (y i) ∧ G.Adj (y i) (x j) ∧ G.Adj (x j) (y j) ∧ G.Adj (y j) (x i))) ∧ ((∀ (i j : Fin n), i < j → ¬(G.Adj (x i) (y i) ∧ G.Adj (y i) (x j) ∧ G.Adj (x j) (y j) ∧ G.Adj (y j) (x i))) ↔ ∀ (r : ℕ) (i : Fin (r + 2) → Fin n), Function.Injective i → ¬∀ (s : Fin (r + 2)), G.Adj (x (i s)) (y (i s)) ∧ G.Adj (y (i s)) (x (i (s + 1))))\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hxy\",\"statement\":\"Function.Bijective (Sum.elim x y)\"},{\"name\":\"hY\",\"statement\":\"Maximal G.IsIndepSet (Set.range y)\"},{\"name\":\"hdiag\",\"statement\":\"∀ (i : Fin n), G.Adj (x i) (y i)\"},{\"name\":\"hBC\",\"statement\":\"B ↔ C\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0019_unique_diagonal_perfect_matching_iff_no_al\",\"reconstructedProofSha256\":\"b243ec4df9709d2879cb7fb52ecaa6ace7b37f5054aaf31d25cfed2c8d268ddb\",\"selectedEdgeCount\":2,\"theoremName\":\"Rollout_p0019_unique_diagonal_perfect_matching_iff_no_al.unique_diagonal_perfect_matching_iff_no_alternating_cycle\",\"topologySha256\":\"a1634d7f40419c801a109035bdeb7fe0590e91296c79e9c810f08e9363381342\"}"

namespace Rollout_p0043_independentdominationnumber_eq_dominationn

-- graph_id: p0043_independentdominationnumber_eq_dominationn
-- topology_sha256: c61f4a83bcbad58f8e02ac4870c2a4154fb38a1c4798a2c300e2500f89251222
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

end Rollout_p0043_independentdominationnumber_eq_dominationn

#check_dependency_graph "Rollout_p0043_independentdominationnumber_eq_dominationn.independentDominationNumber_eq_dominationNumber" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"sInf {n | ∃ D, D.card = n ∧ G.IsIndepSet ↑D ∧ ∀ v ∉ D, ∃ w ∈ D, G.Adj v w} = sInf {n | ∃ D, D.card = n ∧ ∀ v ∉ D, ∃ w ∈ D, G.Adj v w}\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hhigh\",\"statement\":\"G.IsIndepSet {v | 2 < (G.neighborSet v).ncard}\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0043_independentdominationnumber_eq_dominationn\",\"reconstructedProofSha256\":\"7aedf2967b66e6acc0db9287d6d4288dbd14f047917bab98e7d461eb6d5e7714\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p0043_independentdominationnumber_eq_dominationn.independentDominationNumber_eq_dominationNumber\",\"topologySha256\":\"c61f4a83bcbad58f8e02ac4870c2a4154fb38a1c4798a2c300e2500f89251222\"}"

namespace Rollout_p0109_exists_atomic_puiseux_monoid_without_singl

-- graph_id: p0109_exists_atomic_puiseux_monoid_without_singl
-- topology_sha256: 1f8eb1a2dee6809ed1a7bee3e31417e9eae1d070ed67756f049a7393ee1739f4
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

end Rollout_p0109_exists_atomic_puiseux_monoid_without_singl

#check_dependency_graph "Rollout_p0109_exists_atomic_puiseux_monoid_without_singl.exists_atomic_puiseux_monoid_without_singleton_two_lengths" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∃ M, (∀ (x : ↥M), ∃ l, (∀ a ∈ l, AddIrreducible a) ∧ l.sum = x) ∧ ∀ (x : ↥M), {n | ∃ l, l.length = n ∧ (∀ a ∈ l, AddIrreducible a) ∧ l.sum = x} ≠ {2}\"},\"graphEdgeId\":\"h_goal\",\"premises\":[],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0109_exists_atomic_puiseux_monoid_without_singl\",\"reconstructedProofSha256\":\"86465e641a22ae41d707b46c4530d6e2d1cb16c849d6218821029248cc2ed7ad\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p0109_exists_atomic_puiseux_monoid_without_singl.exists_atomic_puiseux_monoid_without_singleton_two_lengths\",\"topologySha256\":\"1f8eb1a2dee6809ed1a7bee3e31417e9eae1d070ed67756f049a7393ee1739f4\"}"

namespace Rollout_p0130_affinesemigroup_normal_equiv

-- graph_id: p0130_affinesemigroup_normal_equiv
-- topology_sha256: b6e0b51344ee410e1677d05af1a57204e4ffb055c0a46ace81c966c822d992e2
/- accepted add_to_file helper 1 -/
noncomputable def affineSemigroupBasis
    (d : ℕ) (hd : 1 ≤ d) (a : Fin d → Fin d → ℕ)
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ))) :
    Module.Basis (Fin d) ℝ (Fin d → ℝ) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  exact @basisOfLinearIndependentOfCardEqFinrank ℝ (Fin d → ℝ) _ _ _ (Fin d) this _
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)) haLI (by
        rw [Module.finrank_pi, Fintype.card_fin])

lemma affineSemigroupBasis_apply
    (d : ℕ) (hd : 1 ≤ d) (a : Fin d → Fin d → ℕ)
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ))) (i : Fin d) :
    affineSemigroupBasis d hd a haLI i = fun j => (a i j : ℝ) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  simp [affineSemigroupBasis]

lemma affineSemigroup_sum_coords
    {d : ℕ} {hd : 1 ≤ d} {a : Fin d → Fin d → ℕ}
    {haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ))}
    {x : Fin d → ℝ} {c : Fin d → ℝ}
    (hx : x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))) :
    ∀ i, (affineSemigroupBasis d hd a haLI).repr x i = c i := by
  intro i
  subst x
  let b := affineSemigroupBasis d hd a haLI
  have hb : ∀ k, b k = fun j : Fin d => (a k j : ℝ) := by
    intro k
    exact affineSemigroupBasis_apply d hd a haLI k
  have hsum : (∑ k, c k • (fun j : Fin d => (a k j : ℝ))) =
      (Finsupp.linearCombination ℝ (fun k => b k))
        (Finsupp.equivFunOnFinite.symm c) := by
    rw [Finsupp.linearCombination_apply]
    rw [Finsupp.sum_fintype]
    · simp [hb]
    · intro j
      simp
  rw [hsum, Module.Basis.repr_linearCombination]
  simp

abbrev affineSemigroupNatToInt (d : ℕ) : (Fin d → ℕ) → (Fin d → ℤ) :=
  fun u j => (u j : ℤ)

abbrev affineSemigroupNatToReal (d : ℕ) : (Fin d → ℕ) → (Fin d → ℝ) :=
  fun u j => (u j : ℝ)

abbrev affineSemigroupIntToReal (d : ℕ) : (Fin d → ℤ) → (Fin d → ℝ) :=
  fun u j => (u j : ℝ)

lemma affineSemigroup_S_coord_nonneg
    {d : ℕ} (hd : 1 ≤ d)
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    {haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ))}
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ)))
    {w : Fin d → ℕ} (hw : w ∈ S) (i : Fin d) :
    0 ≤ (affineSemigroupBasis d hd a haLI).repr
      (affineSemigroupNatToReal d w) i := by
  have hmem : affineSemigroupNatToReal d w ∈
      ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
        (S : Set (Fin d → ℕ))) := by
    exact ⟨w, hw, rfl⟩
  have hhull : affineSemigroupNatToReal d w ∈
      ConvexCone.hull ℝ
        ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
          (S : Set (Fin d → ℕ))) :=
    ConvexCone.subset_hull hmem
  rcases (hcone _ ).mp hhull with ⟨c, hc, hx⟩
  rw [affineSemigroup_sum_coords hx i]
  exact hc i

/- accepted add_to_file helper 2 -/
def affineSemigroupCone (d : ℕ) (a : Fin d → Fin d → ℕ) : Set (Fin d → ℝ) :=
  {x | ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
    x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))}

def affineSemigroupRelintCone (d : ℕ) (a : Fin d → Fin d → ℕ) : Set (Fin d → ℝ) :=
  {x | ∃ c : Fin d → ℝ, (∀ i, 0 < c i) ∧
    x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))}

def affineSemigroupFundamentalParallelepiped
    (d : ℕ) (a : Fin d → Fin d → ℕ) : Set (Fin d → ℝ) :=
  {x | ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i ∧ c i < 1) ∧
    x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))}

def affineSemigroupApery (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) (a : Fin d → Fin d → ℕ) :
    Set (Fin d → ℕ) :=
  {w | w ∈ S ∧ ∀ i, ¬∃ s : Fin d → ℕ, s ∈ S ∧ w = s + a i}

def affineSemigroupG (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) : Set (Fin d → ℤ) :=
  {z | ∃ u : Fin d → ℕ, u ∈ S ∧
    ∃ v : Fin d → ℕ, v ∈ S ∧
      z = affineSemigroupNatToInt d u - affineSemigroupNatToInt d v}

def affineSemigroupNormal (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) (a : Fin d → Fin d → ℕ) : Prop :=
  affineSemigroupNatToInt d '' (S : Set (Fin d → ℕ)) =
    affineSemigroupG d S ∩
      {z | affineSemigroupIntToReal d z ∈ affineSemigroupCone d a}

/- accepted add_to_file helper 3 -/
lemma affineSemigroup_normal_implies_condition4
    {d : ℕ} (hd : 1 ≤ d)
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haS : ∀ i, a i ∈ S)
    {haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ))}
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ)))
    (hnormal : affineSemigroupNormal d S a)
    {w : Fin d → ℕ} (hw : w ∈ affineSemigroupApery d S a) :
    affineSemigroupNatToReal d w ∈
      affineSemigroupFundamentalParallelepiped d a := by
  rcases hw with ⟨hwS, hnopred⟩
  have hmem : affineSemigroupNatToReal d w ∈
      ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
        (S : Set (Fin d → ℕ))) := by
    exact ⟨w, hwS, rfl⟩
  have hhull : affineSemigroupNatToReal d w ∈
      ConvexCone.hull ℝ
        ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
          (S : Set (Fin d → ℕ))) :=
    ConvexCone.subset_hull hmem
  rcases (hcone _ ).mp hhull with ⟨c, hc, hx⟩
  refine ⟨c, ?_, hx⟩
  intro i
  refine ⟨hc i, ?_⟩
  by_contra hlt
  have hci : 1 ≤ c i := le_of_not_gt hlt
  let z : Fin d → ℤ :=
    affineSemigroupNatToInt d w - affineSemigroupNatToInt d (a i)
  let dc : Fin d → ℝ := fun k => c k - (if k = i then 1 else 0)
  have hdc : ∀ k, 0 ≤ dc k := by
    intro k
    by_cases hk : k = i
    · simp [dc, hk, sub_nonneg.mpr hci]
    · simp [dc, hk, hc k]
  have hzreal : affineSemigroupIntToReal d z =
      affineSemigroupNatToReal d w - affineSemigroupNatToReal d (a i) := by
    funext j
    simp [z, affineSemigroupIntToReal, affineSemigroupNatToInt,
      affineSemigroupNatToReal, Int.cast_sub]
  have hzC : affineSemigroupIntToReal d z ∈ affineSemigroupCone d a := by
    refine ⟨dc, hdc, ?_⟩
    rw [hzreal, hx]
    simp [dc, Finset.sum_sub_distrib, sub_smul]
  have hzG : z ∈ affineSemigroupG d S := by
    refine ⟨w, hwS, a i, haS i, rfl⟩
  have hzimage : z ∈ affineSemigroupNatToInt d '' (S : Set (Fin d → ℕ)) := by
    change z ∈ affineSemigroupNatToInt d '' (S : Set (Fin d → ℕ))
    rw [hnormal]
    exact ⟨hzG, hzC⟩
  rcases hzimage with ⟨s, hsS, hsz⟩
  have hws : w = s + a i := by
    funext j
    have hpoint := congrFun hsz j
    change (s j : ℤ) = (w j : ℤ) - (a i j : ℤ) at hpoint
    have hnat : s j + a i j = w j := by
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_add]
      omega
    simpa [hnat]
  exact hnopred i ⟨s, hsS, hws⟩

/- accepted add_to_file helper 4 -/
def affineSemigroupLeS (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) :
    (Fin d → ℕ) → (Fin d → ℕ) → Prop :=
  fun u v => ∃ s : Fin d → ℕ, s ∈ S ∧ v = u + s

def affineSemigroupMaximalApery (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) (a : Fin d → Fin d → ℕ) :
    (Fin d → ℕ) → Prop :=
  fun m => m ∈ affineSemigroupApery d S a ∧
    ∀ w, w ∈ affineSemigroupApery d S a →
      affineSemigroupLeS d S m w → affineSemigroupLeS d S w m

def affineSemigroupQF (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) (a : Fin d → Fin d → ℕ) :
    Set (Fin d → ℤ) :=
  {f | ∃ m, affineSemigroupMaximalApery d S a m ∧
    f = affineSemigroupNatToInt d m -
      ∑ i, affineSemigroupNatToInt d (a i)}

def affineSemigroupCondition2 (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) (a : Fin d → Fin d → ℕ) : Prop :=
  ∀ f, f ∈ affineSemigroupQF d S a →
    -f ∈ affineSemigroupNatToInt d '' (S : Set (Fin d → ℕ)) ∧
      affineSemigroupIntToReal d (-f) ∈ affineSemigroupRelintCone d a

def affineSemigroupCondition3 (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) (a : Fin d → Fin d → ℕ) : Prop :=
  ∀ f, f ∈ affineSemigroupQF d S a →
    affineSemigroupIntToReal d (-f) ∈ affineSemigroupRelintCone d a

def affineSemigroupCondition4 (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) (a : Fin d → Fin d → ℕ) : Prop :=
  ∀ w, w ∈ affineSemigroupApery d S a →
    affineSemigroupNatToReal d w ∈
      affineSemigroupFundamentalParallelepiped d a

/- accepted add_to_file helper 5 -/
lemma affineSemigroup_normal_implies_condition2
    {d : ℕ} (hd : 1 ≤ d)
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haS : ∀ i, a i ∈ S)
    {haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ))}
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ)))
    (hnormal : affineSemigroupNormal d S a) :
    affineSemigroupCondition2 d S a := by
  intro f hf
  rcases hf with ⟨m, hm, rfl⟩
  rcases hm.1 with ⟨hmS, hmnopred⟩
  have hcond4 := affineSemigroup_normal_implies_condition4
    (d := d) (hd := hd) (S := S) (a := a) (haLI := haLI)
    haS hcone hnormal hm.1
  rcases hcond4 with ⟨c, hc, hxm⟩
  let q : Fin d → ℝ := fun i => 1 - c i
  have hq : ∀ i, 0 < q i := by
    intro i
    exact sub_pos.mpr (hc i).2
  have hsumaS : (∑ i, a i) ∈ S := by
    exact S.sum_mem (fun i hi => haS i)
  have hcastsum : affineSemigroupNatToInt d (∑ i, a i) =
      ∑ i, affineSemigroupNatToInt d (a i) := by
    funext j
    simp [affineSemigroupNatToInt]
  have hneg :
      -(affineSemigroupNatToInt d m - ∑ i, affineSemigroupNatToInt d (a i)) =
        ∑ i, affineSemigroupNatToInt d (a i) - affineSemigroupNatToInt d m := by
    abel
  have hG : -(affineSemigroupNatToInt d m -
      ∑ i, affineSemigroupNatToInt d (a i)) ∈ affineSemigroupG d S := by
    rw [hneg, ← hcastsum]
    exact ⟨∑ i, a i, hsumaS, m, hmS, rfl⟩
  have hreal :
      affineSemigroupIntToReal d
        (-(affineSemigroupNatToInt d m -
          ∑ i, affineSemigroupNatToInt d (a i))) =
        ∑ i, q i • (fun j : Fin d => (a i j : ℝ)) := by
    rw [hneg]
    funext j
    simp [affineSemigroupIntToReal, affineSemigroupNatToInt,
      affineSemigroupNatToReal, q]
    have hmcoord := congrFun hxm j
    simp [affineSemigroupNatToReal] at hmcoord
    rw [hmcoord]
    simp [Finset.sum_sub_distrib, sub_mul]
  have hrel :
      affineSemigroupIntToReal d
        (-(affineSemigroupNatToInt d m -
          ∑ i, affineSemigroupNatToInt d (a i))) ∈
        affineSemigroupRelintCone d a := by
    exact ⟨q, hq, hreal⟩
  have hC :
      affineSemigroupIntToReal d
        (-(affineSemigroupNatToInt d m -
          ∑ i, affineSemigroupNatToInt d (a i))) ∈
        affineSemigroupCone d a := by
    rcases hrel with ⟨r, hr, hx⟩
    exact ⟨r, fun i => le_of_lt (hr i), hx⟩
  have himage :
      -(affineSemigroupNatToInt d m -
        ∑ i, affineSemigroupNatToInt d (a i)) ∈
        affineSemigroupNatToInt d '' (S : Set (Fin d → ℕ)) := by
    change -(affineSemigroupNatToInt d m -
        ∑ i, affineSemigroupNatToInt d (a i)) ∈
      affineSemigroupNatToInt d '' (S : Set (Fin d → ℕ))
    rw [hnormal]
    exact ⟨hG, hC⟩
  exact ⟨himage, hrel⟩

/- accepted add_to_file helper 6 -/
lemma affineSemigroup_exists_apery_reduction
    {d : ℕ}
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    {s : Fin d → ℕ} (hs : s ∈ S) :
    ∃ w : Fin d → ℕ, ∃ n : Fin d → ℕ,
      w ∈ affineSemigroupApery d S a ∧
        s = w + ∑ i, n i • a i := by
  let total : (Fin d → ℕ) → ℕ := fun u => ∑ j, u j
  have step : ∀ N : ℕ, ∀ t : Fin d → ℕ, t ∈ S → total t = N →
      ∃ w : Fin d → ℕ, ∃ n : Fin d → ℕ,
        w ∈ affineSemigroupApery d S a ∧
          t = w + ∑ i, n i • a i := by
    intro N
    refine Nat.strong_induction_on N ?_
    intro N ih t htS htN
    by_cases hAp : ∀ i, ¬∃ p : Fin d → ℕ, p ∈ S ∧ t = p + a i
    · exact ⟨t, 0, ⟨htS, hAp⟩, by simp⟩
    · have hbad : ∃ i, ∃ p : Fin d → ℕ, p ∈ S ∧ t = p + a i := by
        push Not at hAp
        rcases hAp with ⟨i, hi⟩
        exact ⟨i, hi⟩
      rcases hbad with ⟨i, p, hpS, htp⟩
      have haneq : a i ≠ 0 := by
        intro hz
        have hrealne := haLI.ne_zero i
        apply hrealne
        funext j
        simp [hz]
      have hapos : 0 < total (a i) := by
        have hex : ∃ j, a i j ≠ 0 := by
          by_contra hnone
          push Not at hnone
          apply haneq
          funext j
          exact hnone j
        rcases hex with ⟨j, hj⟩
        exact Finset.sum_pos' (fun k hk => Nat.zero_le _)
          ⟨j, Finset.mem_univ j, Nat.pos_of_ne_zero hj⟩
      have htot : total t = total p + total (a i) := by
        rw [htp]
        simp [total, Finset.sum_add_distrib]
      have hlt : total p < N := by
        omega
      have hpN : total p = total p := rfl
      rcases ih (total p) hlt p hpS hpN with ⟨w, n, hw, hpw⟩
      refine ⟨w, fun k => n k + (if k = i then 1 else 0), hw, ?_⟩
      rw [htp, hpw]
      have hsumif : (∑ k, (if k = i then (1 : ℕ) else 0) • a k) = a i := by
        simp
      calc
        (w + ∑ k, n k • a k) + a i
            = w + (∑ k, n k • a k + a i) := by abel
        _ = w + (∑ k, n k • a k + ∑ k, (if k = i then (1 : ℕ) else 0) • a k) := by
          rw [hsumif]
        _ = w + ∑ k, (n k + (if k = i then 1 else 0)) • a k := by
          rw [← Finset.sum_add_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          simp [add_smul]
  exact step (total s) s hs rfl

/- accepted add_to_file helper 7 -/
def affineSemigroupIntCastLinear (d : ℕ) :
    (Fin d → ℤ) →ₗ[ℤ] (Fin d → ℝ) where
  toFun := affineSemigroupIntToReal d
  map_add' := by
    intro x y
    funext j
    simp [affineSemigroupIntToReal]
  map_smul' := by
    intro z x
    funext j
    simp [affineSemigroupIntToReal]

/- accepted add_to_file helper 8 -/
lemma affineSemigroup_int_linearIndependent
    {d : ℕ} {a : Fin d → Fin d → ℕ}
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ))) :
    LinearIndependent ℤ
      (fun i : Fin d => affineSemigroupNatToInt d (a i)) := by
  have hzreal : LinearIndependent ℤ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)) := by
    refine LinearIndependent.restrict_scalars ?_ haLI
    simpa using (Int.cast_injective (α := ℝ))
  refine LinearIndependent.of_comp (affineSemigroupIntCastLinear d) ?_
  simpa [affineSemigroupIntCastLinear, affineSemigroupIntToReal,
    affineSemigroupNatToInt] using hzreal

/- accepted add_to_file helper 9 -/
def affineSemigroupIntegerLattice
    (d : ℕ) (a : Fin d → Fin d → ℕ) : Submodule ℤ (Fin d → ℤ) :=
  Submodule.span ℤ
    (Set.range (fun i : Fin d => affineSemigroupNatToInt d (a i)))

/- accepted add_to_file helper 10 -/
lemma affineSemigroup_finite_quotient_integerLattice
    {d : ℕ} {a : Fin d → Fin d → ℕ}
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ))) :
    Finite ((Fin d → ℤ) ⧸ affineSemigroupIntegerLattice d a) := by
  refine Submodule.finiteQuotientOfFreeOfRankEq
    (affineSemigroupIntegerLattice d a) ?_
  rw [affineSemigroupIntegerLattice,
    finrank_span_eq_card (affineSemigroup_int_linearIndependent haLI),
    Module.finrank_pi, Fintype.card_fin]

/- accepted add_to_file helper 11 -/
lemma affineSemigroup_exists_positive_nsmul_mem_integerLattice
    {d : ℕ} {a : Fin d → Fin d → ℕ}
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    (z : Fin d → ℤ) :
    ∃ n : ℕ, 0 < n ∧ n • z ∈ affineSemigroupIntegerLattice d a := by
  haveI : Finite ((Fin d → ℤ) ⧸ affineSemigroupIntegerLattice d a) :=
    affineSemigroup_finite_quotient_integerLattice haLI
  let q : (Fin d → ℤ) ⧸ affineSemigroupIntegerLattice d a :=
    Submodule.Quotient.mk (p := affineSemigroupIntegerLattice d a) z
  refine ⟨addOrderOf q, addOrderOf_pos q, ?_⟩
  have hq : addOrderOf q • q = 0 := addOrderOf_nsmul_eq_zero q
  have hmk : Submodule.Quotient.mk (p := affineSemigroupIntegerLattice d a)
      (addOrderOf q • z) =
      (0 : (Fin d → ℤ) ⧸ affineSemigroupIntegerLattice d a) := by
    change addOrderOf q •
        (Submodule.Quotient.mk (p := affineSemigroupIntegerLattice d a) z) = 0
    exact hq
  exact (Submodule.Quotient.mk_eq_zero (affineSemigroupIntegerLattice d a)).mp hmk

/- accepted add_to_file helper 12 -/
lemma affineSemigroup_exists_S_sub_mem_integerLattice
    {d : ℕ} {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    {z : Fin d → ℤ} (hz : z ∈ affineSemigroupG d S) :
    ∃ s : Fin d → ℕ, s ∈ S ∧
      z - affineSemigroupNatToInt d s ∈ affineSemigroupIntegerLattice d a := by
  rcases hz with ⟨u, huS, v, hvS, rfl⟩
  rcases affineSemigroup_exists_positive_nsmul_mem_integerLattice haLI
      (affineSemigroupNatToInt d v) with ⟨N, hNpos, hNH⟩
  let s : Fin d → ℕ := u + (N - 1) • v
  have hsS : s ∈ S := S.add_mem huS (S.nsmul_mem hvS (N - 1))
  refine ⟨s, hsS, ?_⟩
  have hcast : affineSemigroupNatToInt d s =
      affineSemigroupNatToInt d u +
        (N - 1) • affineSemigroupNatToInt d v := by
    funext j
    simp [s, affineSemigroupNatToInt]
  have hzcalc :
      (affineSemigroupNatToInt d u - affineSemigroupNatToInt d v) -
          affineSemigroupNatToInt d s =
        -(N • affineSemigroupNatToInt d v) := by
    rw [hcast]
    have hN : N - 1 + 1 = N := Nat.sub_one_add_one_eq_of_pos hNpos
    have hNv : N • affineSemigroupNatToInt d v =
        (N - 1) • affineSemigroupNatToInt d v +
          affineSemigroupNatToInt d v := by
      nth_rewrite 1 [← hN]
      rw [add_nsmul, one_nsmul]
    rw [hNv]
    abel
  rw [hzcalc]
  exact Submodule.neg_mem _ hNH

/- accepted add_to_file helper 13 -/
lemma affineSemigroup_nat_sum_a_mem_integerLattice
    {d : ℕ} {a : Fin d → Fin d → ℕ} (n : Fin d → ℕ) :
    affineSemigroupNatToInt d (∑ i, n i • a i) ∈
      affineSemigroupIntegerLattice d a := by
  rw [affineSemigroupIntegerLattice]
  have hsum : affineSemigroupNatToInt d (∑ i, n i • a i) =
      ∑ i, n i • affineSemigroupNatToInt d (a i) := by
    funext j
    simp [affineSemigroupNatToInt]
  rw [hsum]
  exact Submodule.sum_mem _ (fun i hi =>
    (Submodule.span ℤ
      (Set.range (fun i : Fin d => affineSemigroupNatToInt d (a i)))).toAddSubmonoid.nsmul_mem
      (Submodule.subset_span ⟨i, rfl⟩) (n i))

lemma affineSemigroup_exists_apery_int_coords_of_G
    {d : ℕ} {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    {z : Fin d → ℤ} (hz : z ∈ affineSemigroupG d S) :
    ∃ w : Fin d → ℕ, w ∈ affineSemigroupApery d S a ∧
      ∃ k : Fin d → ℤ,
        z - affineSemigroupNatToInt d w =
          ∑ i, k i • affineSemigroupNatToInt d (a i) := by
  rcases affineSemigroup_exists_S_sub_mem_integerLattice haLI hz with
    ⟨s, hsS, hzsub⟩
  rcases affineSemigroup_exists_apery_reduction haLI hsS with
    ⟨w, n, hw, hsw⟩
  have hsdiff :
      affineSemigroupNatToInt d s - affineSemigroupNatToInt d w ∈
        affineSemigroupIntegerLattice d a := by
    rw [hsw]
    have hcast :
        affineSemigroupNatToInt d (w + ∑ i, n i • a i) -
            affineSemigroupNatToInt d w =
          affineSemigroupNatToInt d (∑ i, n i • a i) := by
      funext j
      simp [affineSemigroupNatToInt]
    rw [hcast]
    exact affineSemigroup_nat_sum_a_mem_integerLattice n
  have hzw : z - affineSemigroupNatToInt d w ∈
      affineSemigroupIntegerLattice d a := by
    have hsum := Submodule.add_mem _ hzsub hsdiff
    convert hsum using 1
    abel
  rw [affineSemigroupIntegerLattice,
    Submodule.mem_span_range_iff_exists_fun] at hzw
  rcases hzw with ⟨k, hk⟩
  exact ⟨w, hw, k, hk.symm⟩

/- accepted add_to_file helper 14 -/
lemma affineSemigroup_image_subset_G_inter_cone
    {d : ℕ}
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))) :
    affineSemigroupNatToInt d '' (S : Set (Fin d → ℕ)) ⊆
      affineSemigroupG d S ∩
        {z | affineSemigroupIntToReal d z ∈ affineSemigroupCone d a} := by
  rintro z ⟨s, hsS, rfl⟩
  constructor
  · refine ⟨s, hsS, 0, S.zero_mem, ?_⟩
    funext j
    simp [affineSemigroupNatToInt]
  · have hmem : affineSemigroupNatToReal d s ∈
        ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
          (S : Set (Fin d → ℕ))) := by
      exact ⟨s, hsS, rfl⟩
    have hhull : affineSemigroupNatToReal d s ∈ ConvexCone.hull ℝ
        ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
          (S : Set (Fin d → ℕ))) :=
      ConvexCone.subset_hull hmem
    have hreal : affineSemigroupIntToReal d (affineSemigroupNatToInt d s) =
        affineSemigroupNatToReal d s := by
      funext j
      simp [affineSemigroupIntToReal, affineSemigroupNatToInt,
        affineSemigroupNatToReal]
    change affineSemigroupIntToReal d (affineSemigroupNatToInt d s) ∈
      affineSemigroupCone d a
    rw [hreal]
    exact (hcone _).mp hhull

/- accepted add_to_file helper 15 -/
lemma affineSemigroup_condition4_implies_normal
    {d : ℕ} (hd : 1 ≤ d)
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haS : ∀ i, a i ∈ S)
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ)))
    (hcond4 : affineSemigroupCondition4 d S a) :
    affineSemigroupNormal d S a := by
  apply Set.Subset.antisymm (affineSemigroup_image_subset_G_inter_cone hcone)
  rintro z ⟨hzG, hzC⟩
  rcases affineSemigroup_exists_apery_int_coords_of_G haLI hzG with
    ⟨w, hwAp, k, hzwk⟩
  rcases hcond4 w hwAp with ⟨c, hc, hxw⟩
  rcases hzC with ⟨q, hq, hxz⟩
  have hHreal : affineSemigroupIntToReal d
        (z - affineSemigroupNatToInt d w) =
      ∑ i, (k i : ℝ) • (fun j : Fin d => (a i j : ℝ)) := by
    rw [hzwk]
    funext j
    simp [affineSemigroupIntToReal, affineSemigroupNatToInt]
  have hknonneg : ∀ i, 0 ≤ k i := by
    intro i
    have hqcoord := affineSemigroup_sum_coords
      (d := d) (hd := hd) (a := a) (haLI := haLI) hxz i
    have hwcoord := affineSemigroup_sum_coords
      (d := d) (hd := hd) (a := a) (haLI := haLI) hxw i
    have hkcoord := affineSemigroup_sum_coords
      (d := d) (hd := hd) (a := a) (haLI := haLI) hHreal i
    have hdiffcast : affineSemigroupIntToReal d
          (z - affineSemigroupNatToInt d w) =
        affineSemigroupIntToReal d z - affineSemigroupNatToReal d w := by
      funext j
      simp [affineSemigroupIntToReal, affineSemigroupNatToInt,
        affineSemigroupNatToReal, Int.cast_sub]
    have hqck : q i - c i = (k i : ℝ) := by
      calc
        q i - c i
            = ((affineSemigroupBasis d hd a haLI).repr
                (affineSemigroupIntToReal d z) i) -
              ((affineSemigroupBasis d hd a haLI).repr
                (affineSemigroupNatToReal d w) i) := by
                  rw [hqcoord, hwcoord]
        _ = ((affineSemigroupBasis d hd a haLI).repr
              (affineSemigroupIntToReal d z -
                affineSemigroupNatToReal d w) i) := by
              simp
        _ = ((affineSemigroupBasis d hd a haLI).repr
              (affineSemigroupIntToReal d
                (z - affineSemigroupNatToInt d w)) i) := by
              rw [hdiffcast]
        _ = (k i : ℝ) := hkcoord
    have hkgt : (-1 : ℝ) < (k i : ℝ) := by
      rw [← hqck]
      have hq0 := hq i
      have hc1 := (hc i).2
      linarith
    have hkgtint : -1 < k i := by
      exact_mod_cast hkgt
    omega
  let n : Fin d → ℕ := fun i => Int.toNat (k i)
  have hnk : ∀ i, ((n i : ℤ) = k i) := by
    intro i
    exact Int.toNat_of_nonneg (hknonneg i)
  have hsumk : (∑ i, k i • affineSemigroupNatToInt d (a i)) =
      affineSemigroupNatToInt d (∑ i, n i • a i) := by
    funext j
    simp [n, affineSemigroupNatToInt, hnk]
  have hzeq : z =
      affineSemigroupNatToInt d (w + ∑ i, n i • a i) := by
    have hz1 : z = affineSemigroupNatToInt d w +
        ∑ i, k i • affineSemigroupNatToInt d (a i) := by
      calc
        z = (z - affineSemigroupNatToInt d w) +
            affineSemigroupNatToInt d w := by abel
        _ = (∑ i, k i • affineSemigroupNatToInt d (a i)) +
            affineSemigroupNatToInt d w := by rw [hzwk]
        _ = affineSemigroupNatToInt d w +
            ∑ i, k i • affineSemigroupNatToInt d (a i) := by abel
    rw [hz1, hsumk]
    funext j
    simp [affineSemigroupNatToInt]
  have hsumS : (∑ i, n i • a i) ∈ S := by
    exact S.sum_mem (fun i hi => S.nsmul_mem (haS i) (n i))
  have htS : w + ∑ i, n i • a i ∈ S :=
    S.add_mem hwAp.1 hsumS
  exact ⟨w + ∑ i, n i • a i, htS, hzeq.symm⟩

/- accepted add_to_file helper 16 -/
lemma affineSemigroup_eq_add_sum_a_of_int_sub
    {d : ℕ} {a : Fin d → Fin d → ℕ}
    {w₁ w₂ : Fin d → ℕ} {k : Fin d → ℤ}
    (hk : ∀ i, 0 ≤ k i)
    (h : affineSemigroupNatToInt d w₂ - affineSemigroupNatToInt d w₁ =
      ∑ i, k i • affineSemigroupNatToInt d (a i)) :
    w₂ = w₁ + ∑ i, Int.toNat (k i) • a i := by
  let n : Fin d → ℕ := fun i => Int.toNat (k i)
  have hnk : ∀ i, ((n i : ℤ) = k i) := by
    intro i
    exact Int.toNat_of_nonneg (hk i)
  have hsumk : (∑ i, k i • affineSemigroupNatToInt d (a i)) =
      affineSemigroupNatToInt d (∑ i, n i • a i) := by
    funext j
    simp [n, affineSemigroupNatToInt, hnk]
  have hzeq : affineSemigroupNatToInt d w₂ =
      affineSemigroupNatToInt d (w₁ + ∑ i, n i • a i) := by
    have hz1 : affineSemigroupNatToInt d w₂ =
        affineSemigroupNatToInt d w₁ +
          ∑ i, k i • affineSemigroupNatToInt d (a i) := by
      calc
        affineSemigroupNatToInt d w₂ =
            (affineSemigroupNatToInt d w₂ -
              affineSemigroupNatToInt d w₁) +
              affineSemigroupNatToInt d w₁ := by abel
        _ = (∑ i, k i • affineSemigroupNatToInt d (a i)) +
              affineSemigroupNatToInt d w₁ := by rw [h]
        _ = affineSemigroupNatToInt d w₁ +
              ∑ i, k i • affineSemigroupNatToInt d (a i) := by abel
    rw [hz1, hsumk]
    funext j
    simp [affineSemigroupNatToInt]
  funext j
  apply Nat.cast_injective (R := ℤ)
  change (w₂ j : ℤ) = ((w₁ + ∑ i, n i • a i) j : ℤ)
  simpa [affineSemigroupNatToInt] using congrFun hzeq j

/- accepted add_to_file helper 17 -/
lemma affineSemigroup_sum_nat_smul_eq_add_a
    {d : ℕ} {S : AddSubmonoid (Fin d → ℕ)}
    {a : Fin d → Fin d → ℕ}
    (haS : ∀ i, a i ∈ S) {n : Fin d → ℕ}
    {i : Fin d} (hi : 0 < n i) :
    ∃ t : Fin d → ℕ, t ∈ S ∧
      ∑ k, n k • a k = t + a i := by
  let m : Fin d → ℕ := fun k => if k = i then n k - 1 else n k
  refine ⟨∑ k, m k • a k, ?_, ?_⟩
  · exact S.sum_mem (fun k hk => S.nsmul_mem (haS k) (m k))
  · have hn : n = fun k => m k + (if k = i then 1 else 0) := by
      funext k
      by_cases hk : k = i
      · simp [m, hk, Nat.sub_add_cancel hi]
      · simp [m, hk]
    calc
      ∑ k, n k • a k
          = ∑ k, (m k + (if k = i then 1 else 0)) • a k := by rw [hn]
      _ = ∑ k, m k • a k + ∑ k, (if k = i then (1 : ℕ) else 0) • a k := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k hk
          simp [add_smul]
      _ = ∑ k, m k • a k + a i := by simp

/- accepted add_to_file helper 18 -/
lemma affineSemigroup_apery_fiber_finite
    {d : ℕ} (hd : 1 ≤ d)
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haS : ∀ i, a i ∈ S)
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ)))
    (Q : (Fin d → ℤ) ⧸ affineSemigroupIntegerLattice d a) :
    {w : Fin d → ℕ | w ∈ affineSemigroupApery d S a ∧
      Submodule.Quotient.mk (p := affineSemigroupIntegerLattice d a)
        (affineSemigroupNatToInt d w) = Q}.Finite := by
  let F : Set (Fin d → ℕ) :=
    {w | w ∈ affineSemigroupApery d S a ∧
      Submodule.Quotient.mk (p := affineSemigroupIntegerLattice d a)
        (affineSemigroupNatToInt d w) = Q}
  change F.Finite
  obtain ⟨z₀, hz₀⟩ := Submodule.Quotient.mk_surjective
    (p := affineSemigroupIntegerLattice d a) Q
  have hkexists : ∀ w : F, ∃ k : Fin d → ℤ,
      affineSemigroupNatToInt d w - z₀ =
        ∑ i, k i • affineSemigroupNatToInt d (a i) := by
    intro w
    have hmk :
        Submodule.Quotient.mk (p := affineSemigroupIntegerLattice d a)
          (affineSemigroupNatToInt d w) =
        Submodule.Quotient.mk (p := affineSemigroupIntegerLattice d a) z₀ := by
      rw [w.2.2, hz₀]
    have hmem : affineSemigroupNatToInt d w - z₀ ∈
        affineSemigroupIntegerLattice d a :=
      (Submodule.Quotient.eq (affineSemigroupIntegerLattice d a)).mp hmk
    rw [affineSemigroupIntegerLattice,
      Submodule.mem_span_range_iff_exists_fun] at hmem
    rcases hmem with ⟨k, hk⟩
    exact ⟨k, hk.symm⟩
  let kfun : F → (Fin d → ℤ) := fun w => Classical.choose (hkexists w)
  have hkfun : ∀ w : F,
      affineSemigroupNatToInt d w - z₀ =
        ∑ i, kfun w i • affineSemigroupNatToInt d (a i) :=
    fun w => Classical.choose_spec (hkexists w)
  let b := affineSemigroupBasis d hd a haLI
  let q₀ : Fin d → ℝ := fun i =>
    b.repr (affineSemigroupIntToReal d z₀) i
  have hcoord : ∀ (w : F) (i : Fin d),
      b.repr (affineSemigroupIntToReal d (affineSemigroupNatToInt d w)) i =
        q₀ i + (kfun w i : ℝ) := by
    intro w i
    have hHreal : affineSemigroupIntToReal d
          (affineSemigroupNatToInt d w - z₀) =
        ∑ j, (kfun w j : ℝ) • (fun l : Fin d => (a j l : ℝ)) := by
      rw [hkfun w]
      funext j
      simp [affineSemigroupIntToReal, affineSemigroupNatToInt]
    have hkcoord := affineSemigroup_sum_coords
      (d := d) (hd := hd) (a := a) (haLI := haLI) hHreal i
    have hdiffcast : affineSemigroupIntToReal d
          (affineSemigroupNatToInt d w - z₀) =
        affineSemigroupIntToReal d (affineSemigroupNatToInt d w) -
          affineSemigroupIntToReal d z₀ := by
      funext j
      simp [affineSemigroupIntToReal, affineSemigroupNatToInt, Int.cast_sub]
    calc
      b.repr (affineSemigroupIntToReal d (affineSemigroupNatToInt d w)) i
          = (b.repr (affineSemigroupIntToReal d
              (affineSemigroupNatToInt d w - z₀)) i) +
            b.repr (affineSemigroupIntToReal d z₀) i := by
              rw [hdiffcast]
              simp
      _ = q₀ i + (kfun w i : ℝ) := by
              rw [hkcoord]
              simp [q₀, add_comm]
  have hlower : ∀ (w : F) (i : Fin d),
      Int.ceil (-(q₀ i)) ≤ kfun w i := by
    intro w i
    have hqnonneg := affineSemigroup_S_coord_nonneg
      (d := d) (hd := hd) (S := S) (a := a) (haLI := haLI) hcone
      w.2.1.1 i
    have hcast :
        affineSemigroupIntToReal d (affineSemigroupNatToInt d w) =
          affineSemigroupNatToReal d w := by
      funext j
      simp [affineSemigroupIntToReal, affineSemigroupNatToInt,
        affineSemigroupNatToReal]
    have hq : q₀ i + (kfun w i : ℝ) ≥ 0 := by
      rw [← hcoord w i, hcast]
      exact hqnonneg
    apply (Int.ceil_le).mpr
    linarith
  let mK : Fin d → ℤ := fun i => Int.ceil (-(q₀ i))
  let nfun : F → (Fin d → ℕ) := fun w i =>
    Int.toNat (kfun w i - mK i)
  have hnge : ∀ (w : F) (i : Fin d), 0 ≤ kfun w i - mK i := by
    intro w i
    exact sub_nonneg.mpr (hlower w i)
  have hnfun_cast : ∀ (w : F) (i : Fin d),
      ((nfun w i : ℤ) = kfun w i - mK i) := by
    intro w i
    exact Int.toNat_of_nonneg (hnge w i)
  have hninj : Function.Injective nfun := by
    intro x y hxy
    have hksame : kfun x = kfun y := by
      funext i
      have hi := congrFun hxy i
      have hx := hnfun_cast x i
      have hy := hnfun_cast y i
      have : ((nfun x i : ℤ) = (nfun y i : ℤ)) := by rw [hi]
      omega
    apply Subtype.ext
    have hint : affineSemigroupNatToInt d x = affineSemigroupNatToInt d y := by
      have hx := hkfun x
      have hy := hkfun y
      rw [hksame] at hx
      calc
        affineSemigroupNatToInt d x =
            (affineSemigroupNatToInt d x - z₀) + z₀ := by abel
        _ = (affineSemigroupNatToInt d y - z₀) + z₀ := by rw [hx, hy]
        _ = affineSemigroupNatToInt d y := by abel
    funext j
    have hj := congrFun hint j
    change ((x : Fin d → ℕ) j : ℤ) = ((y : Fin d → ℕ) j : ℤ) at hj
    exact Nat.cast_injective (R := ℤ) hj
  have hanti : IsAntichain (· ≤ ·) (Set.range nfun) := by
    intro x hx y hy hne hxy
    rcases hx with ⟨X, rfl⟩
    rcases hy with ⟨Y, rfl⟩
    have hkle : ∀ i, kfun X i ≤ kfun Y i := by
      intro i
      have hi := hxy i
      have hX := hnfun_cast X i
      have hY := hnfun_cast Y i
      have hcast : ((nfun X i : ℤ) ≤ (nfun Y i : ℤ)) := by exact_mod_cast hi
      omega
    by_cases hksame : kfun X = kfun Y
    · apply hne
      funext i
      have hX := hnfun_cast X i
      have hY := hnfun_cast Y i
      have hk : kfun X i - mK i = kfun Y i - mK i := by rw [hksame]
      have hcast :
          ((nfun X i : ℤ) = (nfun Y i : ℤ)) := by omega
      exact Nat.cast_injective (R := ℤ) hcast
    · have hex : ∃ i, kfun X i ≠ kfun Y i := by
        by_contra h
        push Not at h
        apply hksame
        funext i
        exact h i
      rcases hex with ⟨i, hi⟩
      have hlt : kfun X i < kfun Y i := lt_of_le_of_ne (hkle i) hi
      let kd : Fin d → ℤ := fun j => kfun Y j - kfun X j
      have hkd : ∀ j, 0 ≤ kd j := by
        intro j
        exact sub_nonneg.mpr (hkle j)
      have hdiff :
          affineSemigroupNatToInt d Y - affineSemigroupNatToInt d X =
            ∑ j, kd j • affineSemigroupNatToInt d (a j) := by
        have hXH := hkfun X
        have hYH := hkfun Y
        calc
          affineSemigroupNatToInt d Y - affineSemigroupNatToInt d X
              = (affineSemigroupNatToInt d Y - z₀) -
                (affineSemigroupNatToInt d X - z₀) := by abel
          _ = (∑ j, kfun Y j • affineSemigroupNatToInt d (a j)) -
              (∑ j, kfun X j • affineSemigroupNatToInt d (a j)) := by
                rw [hYH, hXH]
          _ = ∑ j, kd j • affineSemigroupNatToInt d (a j) := by
                simp [kd, Finset.sum_sub_distrib, sub_smul]
      have hnat := affineSemigroup_eq_add_sum_a_of_int_sub hkd hdiff
      let nd : Fin d → ℕ := fun j => Int.toNat (kd j)
      have hndi : 0 < nd i := by
        have hpos : 0 < kd i := sub_pos.mpr hlt
        change 0 < Int.toNat (kd i)
        have hcast := Int.toNat_of_nonneg (le_of_lt hpos)
        omega
      rcases affineSemigroup_sum_nat_smul_eq_add_a haS hndi with ⟨t, htS, hsumt⟩
      have hpre : (Y : Fin d → ℕ) = ((X : Fin d → ℕ) + t) + a i := by
        calc
          (Y : Fin d → ℕ) = (X : Fin d → ℕ) + ∑ j, nd j • a j := hnat
          _ = (X : Fin d → ℕ) + (t + a i) := by rw [hsumt]
          _ = ((X : Fin d → ℕ) + t) + a i := by abel
      exact Y.property.1.2 i ⟨X + t, S.add_mem X.property.1.1 htS, hpre⟩
  have hPWO : (Set.range nfun).PartiallyWellOrderedOn (· ≤ ·) :=
    Set.partiallyWellOrderedOn_of_wellQuasiOrdered wellQuasiOrdered_le
      (Set.range nfun)
  have hrange : (Set.range nfun).Finite :=
    hanti.finite_of_partiallyWellOrderedOn hPWO
  have hfinite : Finite F := (Set.finite_range_iff hninj).mp hrange
  exact Set.finite_coe_iff.mp hfinite

/- accepted add_to_file helper 19 -/
lemma affineSemigroup_apery_finite
    {d : ℕ} (hd : 1 ≤ d)
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haS : ∀ i, a i ∈ S)
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))) :
    (affineSemigroupApery d S a).Finite := by
  haveI : Finite ((Fin d → ℤ) ⧸ affineSemigroupIntegerLattice d a) :=
    affineSemigroup_finite_quotient_integerLattice haLI
  let F : ((Fin d → ℤ) ⧸ affineSemigroupIntegerLattice d a) →
      Set (Fin d → ℕ) :=
    fun Q => {w | w ∈ affineSemigroupApery d S a ∧
      Submodule.Quotient.mk (p := affineSemigroupIntegerLattice d a)
        (affineSemigroupNatToInt d w) = Q}
  have hAp : affineSemigroupApery d S a = ⋃ Q, F Q := by
    ext w
    constructor
    · intro hw
      refine Set.mem_iUnion.mpr ?_
      exact ⟨_, hw, rfl⟩
    · intro hw
      rcases Set.mem_iUnion.mp hw with ⟨Q, hwQ⟩
      exact hwQ.1
  rw [hAp]
  exact Set.finite_iUnion (fun Q =>
    affineSemigroup_apery_fiber_finite hd haS haLI hcone Q)

/- accepted add_to_file helper 20 -/
lemma affineSemigroup_exists_maximal_apery_above
    {d : ℕ} (hd : 1 ≤ d)
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haS : ∀ i, a i ∈ S)
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ)))
    {w : Fin d → ℕ} (hw : w ∈ affineSemigroupApery d S a) :
    ∃ m : Fin d → ℕ,
      affineSemigroupLeS d S w m ∧
        affineSemigroupMaximalApery d S a m := by
  letI : Preorder (Fin d → ℕ) :=
    { le := affineSemigroupLeS d S
      lt := fun u v => affineSemigroupLeS d S u v ∧
        ¬affineSemigroupLeS d S v u
      le_refl := by
        intro u
        exact ⟨0, S.zero_mem, by simp⟩
      le_trans := by
        intro u v t huv hvt
        rcases huv with ⟨s, hsS, hv⟩
        rcases hvt with ⟨r, hrS, ht⟩
        refine ⟨s + r, S.add_mem hsS hrS, ?_⟩
        rw [ht, hv]
        abel
      lt_iff_le_not_ge := by
        intro u v
        rfl }
  have hfinite := affineSemigroup_apery_finite hd haS haLI hcone
  rcases hfinite.exists_le_maximal hw with ⟨m, hwm, hm⟩
  refine ⟨m, hwm, hm.1, ?_⟩
  intro x hx hmx
  exact hm.2 hx hmx

/- accepted add_to_file helper 21 -/
lemma affineSemigroup_condition3_implies_condition4
    {d : ℕ} (hd : 1 ≤ d)
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haS : ∀ i, a i ∈ S)
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ)))
    (hcond3 : affineSemigroupCondition3 d S a) :
    affineSemigroupCondition4 d S a := by
  intro w hw
  rcases affineSemigroup_exists_maximal_apery_above
    (d := d) (hd := hd) (S := S) (a := a) (haLI := haLI)
    haS hcone hw with ⟨m, hwm, hmax⟩
  let f : Fin d → ℤ := affineSemigroupNatToInt d m -
    ∑ i, affineSemigroupNatToInt d (a i)
  have hfQF : f ∈ affineSemigroupQF d S a := by
    exact ⟨m, hmax, rfl⟩
  rcases hcond3 f hfQF with ⟨r, hr, hxr⟩
  let b := affineSemigroupBasis d hd a haLI
  have hm_lt_one : ∀ i,
      b.repr (affineSemigroupNatToReal d m) i < 1 := by
    intro i
    have hnegreal : affineSemigroupIntToReal d (-f) =
        (∑ k, (1 : ℝ) • (fun j : Fin d => (a k j : ℝ))) -
          affineSemigroupNatToReal d m := by
      funext j
      simp [f, affineSemigroupIntToReal, affineSemigroupNatToInt,
        affineSemigroupNatToReal]
    have hsumrepr :
        (∑ c, (b.repr (fun j : Fin d => (a c j : ℝ))) i) = 1 := by
      calc
        (∑ c, (b.repr (fun j : Fin d => (a c j : ℝ))) i)
            = ∑ c, (b.repr (b c)) i := by
              apply Finset.sum_congr rfl
              intro c hc
              rw [affineSemigroupBasis_apply d hd a haLI]
        _ = 1 := by simp
    have hcoordneg :
        b.repr (affineSemigroupIntToReal d (-f)) i =
          1 - b.repr (affineSemigroupNatToReal d m) i := by
      rw [hnegreal]
      simp [hsumrepr]
    have hrcoord := affineSemigroup_sum_coords
      (d := d) (hd := hd) (a := a) (haLI := haLI) hxr i
    rw [hcoordneg] at hrcoord
    have hri := hr i
    linarith
  have hw_nonneg : ∀ i,
      0 ≤ b.repr (affineSemigroupNatToReal d w) i := by
    intro i
    exact affineSemigroup_S_coord_nonneg
      (d := d) (hd := hd) (S := S) (a := a) (haLI := haLI) hcone hw.1 i
  have hw_le_m : ∀ i,
      b.repr (affineSemigroupNatToReal d w) i ≤
        b.repr (affineSemigroupNatToReal d m) i := by
    intro i
    rcases hwm with ⟨s, hsS, hm⟩
    have hs_nonneg := affineSemigroup_S_coord_nonneg
      (d := d) (hd := hd) (S := S) (a := a) (haLI := haLI) hcone hsS i
    have hmreal : affineSemigroupNatToReal d m =
        affineSemigroupNatToReal d w + affineSemigroupNatToReal d s := by
      rw [hm]
      funext j
      simp [affineSemigroupNatToReal]
    have hcoord := congrArg (fun x : Fin d → ℝ =>
        b.repr x i) hmreal
    simp at hcoord
    rw [hcoord]
    linarith
  let q : Fin d → ℝ := fun i =>
    b.repr (affineSemigroupNatToReal d w) i
  refine ⟨q, ?_, ?_⟩
  · intro i
    exact ⟨hw_nonneg i, lt_of_le_of_lt (hw_le_m i) (hm_lt_one i)⟩
  · calc
      affineSemigroupNatToReal d w =
          ∑ i, q i • b i := by
            symm
            exact b.sum_repr (affineSemigroupNatToReal d w)
      _ = ∑ i, q i • (fun j : Fin d => (a i j : ℝ)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [affineSemigroupBasis_apply d hd a haLI]

/- verified submission -/
theorem affineSemigroup_normal_equiv
    (d : ℕ) (hd : 1 ≤ d)
    (S : AddSubmonoid (Fin d → ℕ)) (hSfg : S.FG)
    (a : Fin d → Fin d → ℕ)
    (haS : ∀ i, a i ∈ S)
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ)))
    (hminray : ∀ (i : Fin d) (u : Fin d → ℕ),
      u ∈ S → u ≠ 0 →
      (∃ r : ℝ, 0 ≤ r ∧
        (fun j : Fin d => (u j : ℝ)) =
          r • (fun j : Fin d => (a i j : ℝ))) →
      ∀ j, a i j ≤ u j) :
    let natToInt : (Fin d → ℕ) → (Fin d → ℤ) :=
      fun u j => (u j : ℤ)
    let natToReal : (Fin d → ℕ) → (Fin d → ℝ) :=
      fun u j => (u j : ℝ)
    let intToReal : (Fin d → ℤ) → (Fin d → ℝ) :=
      fun u j => (u j : ℝ)
    let C : Set (Fin d → ℝ) :=
      {x | ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
        x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))}
    let relintC : Set (Fin d → ℝ) :=
      {x | ∃ c : Fin d → ℝ, (∀ i, 0 < c i) ∧
        x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))}
    let fundamentalParallelepiped : Set (Fin d → ℝ) :=
      {x | ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i ∧ c i < 1) ∧
        x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))}
    let apery : Set (Fin d → ℕ) :=
      {w | w ∈ S ∧ ∀ i, ¬∃ s : Fin d → ℕ, s ∈ S ∧ w = s + a i}
    let leS : (Fin d → ℕ) → (Fin d → ℕ) → Prop :=
      fun u v => ∃ s : Fin d → ℕ, s ∈ S ∧ v = u + s
    let maximalApery : (Fin d → ℕ) → Prop :=
      fun m => m ∈ apery ∧
        ∀ w, w ∈ apery → leS m w → leS w m
    let QF : Set (Fin d → ℤ) :=
      {f | ∃ m, maximalApery m ∧
        f = natToInt m - ∑ i, natToInt (a i)}
    let G : Set (Fin d → ℤ) :=
      {z | ∃ u : Fin d → ℕ, u ∈ S ∧
        ∃ v : Fin d → ℕ, v ∈ S ∧ z = natToInt u - natToInt v}
    let normal : Prop :=
      natToInt '' (S : Set (Fin d → ℕ)) =
        G ∩ {z | intToReal z ∈ C}
    let condition2 : Prop :=
      ∀ f, f ∈ QF →
        -f ∈ natToInt '' (S : Set (Fin d → ℕ)) ∧
          intToReal (-f) ∈ relintC
    let condition3 : Prop :=
      ∀ f, f ∈ QF → intToReal (-f) ∈ relintC
    let condition4 : Prop :=
      ∀ w, w ∈ apery → natToReal w ∈ fundamentalParallelepiped
    (normal ↔ condition2) ∧ (normal ↔ condition3) ∧ (normal ↔ condition4) := by
  change (affineSemigroupNormal d S a ↔ affineSemigroupCondition2 d S a) ∧
    (affineSemigroupNormal d S a ↔ affineSemigroupCondition3 d S a) ∧
    (affineSemigroupNormal d S a ↔ affineSemigroupCondition4 d S a)
  have h34 : affineSemigroupCondition3 d S a →
      affineSemigroupCondition4 d S a := by
    intro h3
    exact affineSemigroup_condition3_implies_condition4
      (d := d) (hd := hd) (S := S) (a := a) (haLI := haLI)
      haS hcone h3
  have h4N : affineSemigroupCondition4 d S a →
      affineSemigroupNormal d S a := by
    intro h4
    exact affineSemigroup_condition4_implies_normal
      (d := d) (hd := hd) (S := S) (a := a)
      haS haLI hcone h4
  have hN2 : affineSemigroupNormal d S a →
      affineSemigroupCondition2 d S a := by
    intro hN
    exact affineSemigroup_normal_implies_condition2
      (d := d) (hd := hd) (S := S) (a := a) (haLI := haLI)
      haS hcone hN
  constructor
  · constructor
    · exact hN2
    · intro h2
      exact h4N (h34 (fun f hf => (h2 f hf).2))
  · constructor
    · constructor
      · intro hN f hf
        exact (hN2 hN f hf).2
      · intro h3
        exact h4N (h34 h3)
    · constructor
      · intro hN w hw
        exact affineSemigroup_normal_implies_condition4
          (d := d) (hd := hd) (S := S) (a := a) (haLI := haLI)
          haS hcone hN hw
      · exact h4N

end Rollout_p0130_affinesemigroup_normal_equiv

#check_dependency_graph "Rollout_p0130_affinesemigroup_normal_equiv.affineSemigroup_normal_equiv" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let natToInt := fun u j => ↑(u j); let natToReal := fun u j => ↑(u j); let intToReal := fun u j => ↑(u j); let C := {x | ∃ c, (∀ (i : Fin d), 0 ≤ c i) ∧ x = ∑ i, c i • fun j => ↑(a i j)}; let relintC := {x | ∃ c, (∀ (i : Fin d), 0 < c i) ∧ x = ∑ i, c i • fun j => ↑(a i j)}; let fundamentalParallelepiped := {x | ∃ c, (∀ (i : Fin d), 0 ≤ c i ∧ c i < 1) ∧ x = ∑ i, c i • fun j => ↑(a i j)}; let apery := {w | w ∈ S ∧ ∀ (i : Fin d), ¬∃ s ∈ S, w = s + a i}; let leS := fun u v => ∃ s ∈ S, v = u + s; let maximalApery := fun m => m ∈ apery ∧ ∀ w ∈ apery, leS m w → leS w m; let QF := {f | ∃ m, maximalApery m ∧ f = natToInt m - ∑ i, natToInt (a i)}; let G := {z | ∃ u ∈ S, ∃ v ∈ S, z = natToInt u - natToInt v}; let normal := natToInt '' ↑S = G ∩ {z | intToReal z ∈ C}; let condition2 := ∀ f ∈ QF, -f ∈ natToInt '' ↑S ∧ intToReal (-f) ∈ relintC; let condition3 := ∀ f ∈ QF, intToReal (-f) ∈ relintC; let condition4 := ∀ w ∈ apery, natToReal w ∈ fundamentalParallelepiped; (normal ↔ condition2) ∧ (normal ↔ condition3) ∧ (normal ↔ condition4)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hd\",\"statement\":\"1 ≤ d\"},{\"name\":\"haS\",\"statement\":\"∀ (i : Fin d), a i ∈ S\"},{\"name\":\"haLI\",\"statement\":\"LinearIndependent ℝ fun i j => ↑(a i j)\"},{\"name\":\"hcone\",\"statement\":\"∀ (x : Fin d → ℝ), x ∈ ConvexCone.hull ℝ ((fun u j => ↑(u j)) '' ↑S) ↔ ∃ c, (∀ (i : Fin d), 0 ≤ c i) ∧ x = ∑ i, c i • fun j => ↑(a i j)\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0130_affinesemigroup_normal_equiv\",\"reconstructedProofSha256\":\"cb7233a68a6118393aa37b189778a13ecbed506886a57b9eae26129aa1a45739\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p0130_affinesemigroup_normal_equiv.affineSemigroup_normal_equiv\",\"topologySha256\":\"b6e0b51344ee410e1677d05af1a57204e4ffb055c0a46ace81c966c822d992e2\"}"

namespace Rollout_p0194_seifert_chi_div_e_lt_one

-- graph_id: p0194_seifert_chi_div_e_lt_one
-- topology_sha256: 470b34ed7bca3de6884d3a0c03c78e97958a03ba5b950199a12ad928a6fa2baf
/- verified submission -/
lemma seifert_nat_div_lt_one_rat {a b : ℕ} (h : a < b) :
    (a : ℚ) / (b : ℚ) < 1 := by
  have hb : 0 < (b : ℚ) := by
    exact_mod_cast Nat.zero_lt_of_lt h
  exact (div_lt_one hb).mpr (by exact_mod_cast h)

lemma seifert_nat_inv_pos_rat {b : ℕ} (hb : 2 ≤ b) :
    0 < (b : ℚ)⁻¹ := by
  have hb0 : 0 < (b : ℚ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hb)
  exact inv_pos.mpr hb0

theorem seifert_chi_div_e_lt_one
    (t d : ℕ) (n q : ℕ → ℕ)
    (hn : ∀ i, 1 ≤ i → i ≤ t → 2 ≤ n i)
    (hq_pos : ∀ i, 1 ≤ i → i ≤ t → 1 ≤ q i)
    (hq_lt : ∀ i, 1 ≤ i → i ≤ t → q i < n i)
    (hcoprime : ∀ i, 1 ≤ i → i ≤ t → Nat.Coprime (n i) (q i))
    (he : 0 < (d : ℚ) - ∑ i ∈ Finset.Icc 1 t, (q i : ℚ) / (n i : ℚ))
    (hcases :
      (t = 3 ∧
        (4 ≤ d ∨
          (d = 3 ∧ q 1 = 1) ∨
          (d = 2 ∧ q 1 = 1 ∧ q 2 = 1))) ∨
      (t = 4 ∧ 3 ≤ d ∧ q 1 = 1 ∧ q 2 = 1 ∧ q 3 = 1)) :
    let e : ℚ := (d : ℚ) - ∑ i ∈ Finset.Icc 1 t, (q i : ℚ) / (n i : ℚ)
    let χ : ℚ := -2 + ∑ i ∈ Finset.Icc 1 t, (1 - 1 / (n i : ℚ))
    χ / e < 1 := by
  rw [div_lt_one he]
  rcases hcases with h3 | h4
  · rcases h3 with ⟨ht, hc⟩
    subst t
    rcases hc with hd | hd | hd
    · have hdQ : (4 : ℚ) ≤ d := by exact_mod_cast hd
      have hq1 : (q 1 : ℚ) / (n 1 : ℚ) < 1 :=
        seifert_nat_div_lt_one_rat (hq_lt 1 (by norm_num) (by norm_num))
      have hq2 : (q 2 : ℚ) / (n 2 : ℚ) < 1 :=
        seifert_nat_div_lt_one_rat (hq_lt 2 (by norm_num) (by norm_num))
      have hq3 : (q 3 : ℚ) / (n 3 : ℚ) < 1 :=
        seifert_nat_div_lt_one_rat (hq_lt 3 (by norm_num) (by norm_num))
      have hn1 : 0 < (n 1 : ℚ)⁻¹ :=
        seifert_nat_inv_pos_rat (hn 1 (by norm_num) (by norm_num))
      have hn2 : 0 < (n 2 : ℚ)⁻¹ :=
        seifert_nat_inv_pos_rat (hn 2 (by norm_num) (by norm_num))
      have hn3 : 0 < (n 3 : ℚ)⁻¹ :=
        seifert_nat_inv_pos_rat (hn 3 (by norm_num) (by norm_num))
      have hsumq : ∑ i ∈ Finset.Icc 1 3, (q i : ℚ) / (n i : ℚ) < 3 := by
        norm_num [Finset.sum_Icc_succ_top]
        nlinarith
      have hsuminv_exp :
          0 < (n 1 : ℚ)⁻¹ + (n 2 : ℚ)⁻¹ + (n 3 : ℚ)⁻¹ :=
        add_pos (add_pos hn1 hn2) hn3
      have hchi : -2 + ∑ i ∈ Finset.Icc 1 3, (1 - 1 / (n i : ℚ)) < 1 := by
        norm_num [Finset.sum_Icc_succ_top]
        linarith
      have he1 : 1 < (d : ℚ) - ∑ i ∈ Finset.Icc 1 3, (q i : ℚ) / (n i : ℚ) := by
        nlinarith
      exact lt_trans hchi he1
    · rcases hd with ⟨hd, hq1nat⟩
      subst d
      have hq2 : (q 2 : ℚ) / (n 2 : ℚ) < 1 :=
        seifert_nat_div_lt_one_rat (hq_lt 2 (by norm_num) (by norm_num))
      have hq3 : (q 3 : ℚ) / (n 3 : ℚ) < 1 :=
        seifert_nat_div_lt_one_rat (hq_lt 3 (by norm_num) (by norm_num))
      have hn2 : 0 < (n 2 : ℚ)⁻¹ :=
        seifert_nat_inv_pos_rat (hn 2 (by norm_num) (by norm_num))
      have hn3 : 0 < (n 3 : ℚ)⁻¹ :=
        seifert_nat_inv_pos_rat (hn 3 (by norm_num) (by norm_num))
      norm_num [Finset.sum_Icc_succ_top, hq1nat]
      nlinarith
    · rcases hd with ⟨hd, hq1nat, hq2nat⟩
      subst d
      have hq3 : (q 3 : ℚ) / (n 3 : ℚ) < 1 :=
        seifert_nat_div_lt_one_rat (hq_lt 3 (by norm_num) (by norm_num))
      have hn3 : 0 < (n 3 : ℚ)⁻¹ :=
        seifert_nat_inv_pos_rat (hn 3 (by norm_num) (by norm_num))
      norm_num [Finset.sum_Icc_succ_top, hq1nat, hq2nat]
      nlinarith
  · rcases h4 with ⟨ht, hd, hq1nat, hq2nat, hq3nat⟩
    subst t
    have hdQ : (3 : ℚ) ≤ d := by exact_mod_cast hd
    have hq4 : (q 4 : ℚ) / (n 4 : ℚ) < 1 :=
      seifert_nat_div_lt_one_rat (hq_lt 4 (by norm_num) (by norm_num))
    have hn4 : 0 < (n 4 : ℚ)⁻¹ :=
      seifert_nat_inv_pos_rat (hn 4 (by norm_num) (by norm_num))
    norm_num [Finset.sum_Icc_succ_top, hq1nat, hq2nat, hq3nat]
    nlinarith

end Rollout_p0194_seifert_chi_div_e_lt_one

#check_dependency_graph "Rollout_p0194_seifert_chi_div_e_lt_one.seifert_chi_div_e_lt_one" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let e := ↑d - ∑ i ∈ Finset.Icc 1 t, ↑(q i) / ↑(n i); let χ := -2 + ∑ i ∈ Finset.Icc 1 t, (1 - 1 / ↑(n i)); χ / e < 1\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hn\",\"statement\":\"∀ (i : ℕ), 1 ≤ i → i ≤ t → 2 ≤ n i\"},{\"name\":\"hq_pos\",\"statement\":\"∀ (i : ℕ), 1 ≤ i → i ≤ t → 1 ≤ q i\"},{\"name\":\"hq_lt\",\"statement\":\"∀ (i : ℕ), 1 ≤ i → i ≤ t → q i < n i\"},{\"name\":\"hcoprime\",\"statement\":\"∀ (i : ℕ), 1 ≤ i → i ≤ t → (n i).Coprime (q i)\"},{\"name\":\"he\",\"statement\":\"0 < ↑d - ∑ i ∈ Finset.Icc 1 t, ↑(q i) / ↑(n i)\"},{\"name\":\"hcases\",\"statement\":\"t = 3 ∧ (4 ≤ d ∨ d = 3 ∧ q 1 = 1 ∨ d = 2 ∧ q 1 = 1 ∧ q 2 = 1) ∨ t = 4 ∧ 3 ≤ d ∧ q 1 = 1 ∧ q 2 = 1 ∧ q 3 = 1\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0194_seifert_chi_div_e_lt_one\",\"reconstructedProofSha256\":\"acc5d9e8655a2b2f9b242c8f020af14c37daad312522d7453bc7279e31f249fc\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p0194_seifert_chi_div_e_lt_one.seifert_chi_div_e_lt_one\",\"topologySha256\":\"470b34ed7bca3de6884d3a0c03c78e97958a03ba5b950199a12ad928a6fa2baf\"}"

namespace Rollout_p0203_bounded_degree_unit_circle_conjugates_clos

-- graph_id: p0203_bounded_degree_unit_circle_conjugates_clos
-- topology_sha256: 0d3ed57d531cecb968ecb1c17477c7cc833bca9b3dff39bd1ddde5a273c210da
/- accepted add_to_file helper 1 -/
lemma finite_algebraic_integer_of_bounded_conjugates_inter_Icc
    (N : ℕ) (a b : ℝ) :
    ({x : ℝ | 1 < x ∧
        IsIntegral ℤ x ∧
        (minpoly ℚ x).natDegree ≤ N ∧
        (∀ z : ℂ,
          ((minpoly ℚ x).map (algebraMap ℚ ℂ)).IsRoot z →
          z ≠ (x : ℂ) → ‖z‖ ≤ 1)} ∩ Set.Icc a b).Finite := by
  let R : ℝ := max |a| |b|
  let M : ℝ := max R 1 ^ N * ↑(N.choose (N / 2))
  let K : ℤ := (⌈M⌉₊ : ℤ)
  let U : Set ℤ := Set.Icc (-K) K
  have hU : U.Finite := by
    dsimp [U]
    exact Set.finite_Icc (-K) K
  have hroots_finite :
      (⋃ f : Polynomial ℤ,
        ⋃ (_ : f.natDegree ≤ N ∧ ∀ i : ℕ, f.coeff i ∈ U),
          ↑((Polynomial.map (algebraMap ℤ ℝ) f).roots.toFinset : Set ℝ)).Finite := by
    exact Polynomial.bUnion_roots_finite (algebraMap ℤ ℝ) N hU
  refine hroots_finite.subset ?_
  intro x hx
  rcases hx with ⟨hxS, hxIcc⟩
  rcases hxS with ⟨hxgt, hZ, hdeg, hconj⟩
  let q : Polynomial ℤ := minpoly ℤ x
  have hQ : IsIntegral ℚ x := IsIntegral.tower_top hZ
  have hqmonic : q.Monic := minpoly.monic hZ
  have hpmonic : (minpoly ℚ x).Monic := minpoly.monic hQ
  have hmin : minpoly ℚ x = q.map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hZ
  have hmaps : (minpoly ℚ x).map (algebraMap ℚ ℂ) = q.map (algebraMap ℤ ℂ) := by
    rw [hmin, Polynomial.map_map]
    congr 1
  have hqdeg : q.natDegree ≤ N := by
    have hdegmap : (q.map (algebraMap ℤ ℚ)).natDegree = q.natDegree :=
      Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective ℤ ℚ) q
    have hpq : (minpoly ℚ x).natDegree = q.natDegree := by
      rw [hmin, hdegmap]
    exact hpq ▸ hdeg
  have hx_abs : |x| ≤ R := by
    have haR : |a| ≤ R := le_max_left |a| |b|
    have hbR : |b| ≤ R := le_max_right |a| |b|
    apply abs_le.mpr
    constructor
    · have hnega : -R ≤ a := by
        have h1 : -|a| ≤ a := neg_abs_le a
        have h2 : -R ≤ -|a| := by linarith
        linarith
      linarith [hxIcc.1]
    · have hble : b ≤ R := le_trans (le_abs_self b) hbR
      linarith [hxIcc.2]
  have hrootbound : ∀ z ∈ (q.map (algebraMap ℤ ℂ)).roots, ‖z‖ ≤ max R 1 := by
    intro z hz
    rw [← hmaps] at hz
    have hzroot : ((minpoly ℚ x).map (algebraMap ℚ ℂ)).IsRoot z :=
      (Polynomial.mem_roots (hpmonic.map _).ne_zero).mp hz
    by_cases hzx : z = (x : ℂ)
    · subst z
      calc
        ‖(x : ℂ)‖ = |x| := by simp
        _ ≤ R := hx_abs
        _ ≤ max R 1 := le_max_left R 1
    · exact (hconj z hzroot hzx).trans (le_max_right R 1)
  have hcoeffU : ∀ i : ℕ, q.coeff i ∈ U := by
    intro i
    have hc' := Polynomial.coeff_bdd_of_roots_le (algebraMap ℤ ℂ) hqmonic
      (IsAlgClosed.splits _) hqdeg hrootbound i
    have hmax : max (max R 1) 1 = max R 1 := max_eq_left (le_max_right R 1)
    have hc : ‖((q.map (algebraMap ℤ ℂ)).coeff i)‖ ≤ M := by
      simpa [M, hmax] using hc'
    rw [Polynomial.coeff_map] at hc
    change ‖((q.coeff i : ℤ) : ℂ)‖ ≤ M at hc
    rw [Complex.norm_intCast] at hc
    have hreal : |(q.coeff i : ℝ)| ≤ (⌈M⌉₊ : ℝ) := hc.trans (Nat.le_ceil M)
    have hzint : |q.coeff i| ≤ (⌈M⌉₊ : ℤ) := by exact_mod_cast hreal
    dsimp [U, K]
    exact abs_le.mp hzint
  have hxroot : (q.map (algebraMap ℤ ℝ)).IsRoot x := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap, minpoly.aeval]
  have hxmemroots : x ∈ ((q.map (algebraMap ℤ ℝ)).roots.toFinset : Finset ℝ) := by
    exact Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots (hqmonic.map _).ne_zero).mpr hxroot)
  refine Set.mem_iUnion.mpr ⟨q, ?_⟩
  refine Set.mem_iUnion.mpr ⟨⟨hqdeg, hcoeffU⟩, ?_⟩
  exact hxmemroots

/- accepted add_to_file helper 2 -/
lemma closed_and_isolated_of_finite_inter_Icc_one
    (S : Set ℝ)
    (hfin : ∀ x : ℝ, (S ∩ Set.Icc (x - 1) (x + 1)).Finite) :
    IsClosed S ∧
      ∀ x ∈ S, ∃ ε > 0, S ∩ Set.Ioo (x - ε) (x + ε) = {x} := by
  constructor
  · rw [← isOpen_compl_iff, Metric.isOpen_iff]
    intro x hx
    let T : Set ℝ := S ∩ Set.Icc (x - 1) (x + 1)
    have hT : T.Finite := hfin x
    have hxnotT : x ∉ T := by
      intro hxT
      exact hx hxT.1
    have hTopen : IsOpen Tᶜ := hT.isClosed.isOpen_compl
    obtain ⟨δ, hδpos, hδball⟩ := (Metric.isOpen_iff.mp hTopen) x hxnotT
    refine ⟨min δ 1, lt_min hδpos zero_lt_one, ?_⟩
    intro y hy hyS
    have hyδ : y ∈ Metric.ball x δ := (Metric.ball_subset_ball (min_le_left δ 1)) hy
    have hyTcomp : y ∉ T := hδball hyδ
    have hyIcc : y ∈ Set.Icc (x - 1) (x + 1) := by
      have hyone : y ∈ Metric.ball x 1 := (Metric.ball_subset_ball (min_le_right δ 1)) hy
      rw [Metric.mem_ball, Real.dist_eq] at hyone
      have hxy : |y - x| < 1 := by
        linarith [abs_sub_comm x y]
      constructor
      · linarith [neg_lt_of_abs_lt hxy]
      · linarith [lt_of_abs_lt hxy]
    exact hyTcomp ⟨hyS, hyIcc⟩
  · intro x hxS
    let T : Set ℝ := S ∩ Set.Icc (x - 1) (x + 1)
    have hT : T.Finite := hfin x
    have hxT : x ∈ T := by
      constructor
      · exact hxS
      · constructor <;> linarith
    obtain ⟨δ, hδpos, hδball⟩ :=
      Metric.exists_ball_inter_eq_singleton_of_mem_discrete hT.isDiscrete hxT
    refine ⟨min δ 1, lt_min hδpos zero_lt_one, ?_⟩
    ext y
    constructor
    · intro hy
      have hyδ : y ∈ Metric.ball x δ := by
        apply (Metric.ball_subset_ball (min_le_left δ 1))
        rw [Metric.mem_ball, Real.dist_eq]
        have hxy : |y - x| < min δ 1 := by
          apply abs_sub_lt_iff.mpr
          constructor <;> linarith [hy.2.1, hy.2.2]
        linarith [abs_sub_comm x y]
      have hyIcc : y ∈ Set.Icc (x - 1) (x + 1) := by
        have hlo : x - min δ 1 < y := hy.2.1
        have hhi : y < x + min δ 1 := hy.2.2
        constructor <;> linarith [min_le_right δ 1]
      have hyT : y ∈ T := ⟨hy.1, hyIcc⟩
      have : y ∈ Metric.ball x δ ∩ T := ⟨hyδ, hyT⟩
      rw [hδball] at this
      simpa using this
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      constructor
      · exact hxS
      · constructor <;> linarith [lt_min hδpos zero_lt_one]

/- verified submission -/
theorem bounded_degree_unit_circle_conjugates_closed_discrete
    (B : ℝ) (hB : 0 < B) :
    let S_B : Set ℝ :=
      {x | 1 < x ∧
        IsIntegral ℤ x ∧
        ((minpoly ℚ x).natDegree : ℝ) ≤ B ∧
        (∀ z : ℂ,
          ((minpoly ℚ x).map (algebraMap ℚ ℂ)).IsRoot z →
          z ≠ (x : ℂ) → ‖z‖ ≤ 1) ∧
        (∃ z : ℂ,
          ((minpoly ℚ x).map (algebraMap ℚ ℂ)).IsRoot z ∧
          z ≠ (x : ℂ) ∧ ‖z‖ = 1)};
    IsClosed S_B ∧
      ∀ x ∈ S_B, ∃ ε > 0, S_B ∩ Set.Ioo (x - ε) (x + ε) = {x} := by
  let S_B : Set ℝ :=
      {x | 1 < x ∧
        IsIntegral ℤ x ∧
        ((minpoly ℚ x).natDegree : ℝ) ≤ B ∧
        (∀ z : ℂ,
          ((minpoly ℚ x).map (algebraMap ℚ ℂ)).IsRoot z →
          z ≠ (x : ℂ) → ‖z‖ ≤ 1) ∧
        (∃ z : ℂ,
          ((minpoly ℚ x).map (algebraMap ℚ ℂ)).IsRoot z ∧
          z ≠ (x : ℂ) ∧ ‖z‖ = 1)}
  change IsClosed S_B ∧
      ∀ x ∈ S_B, ∃ ε > 0, S_B ∩ Set.Ioo (x - ε) (x + ε) = {x}
  have hfin : ∀ x : ℝ, (S_B ∩ Set.Icc (x - 1) (x + 1)).Finite := by
    intro x
    refine (finite_algebraic_integer_of_bounded_conjugates_inter_Icc
      ⌊B⌋₊ (x - 1) (x + 1)).subset ?_
    intro y hy
    rcases hy with ⟨hyS, hyIcc⟩
    rcases hyS with ⟨hygt, hyint, hydeg, hyroots, hyunit⟩
    constructor
    · exact ⟨hygt, hyint, Nat.le_floor hydeg, hyroots⟩
    · exact hyIcc
  exact closed_and_isolated_of_finite_inter_Icc_one S_B hfin

end Rollout_p0203_bounded_degree_unit_circle_conjugates_clos

#check_dependency_graph "Rollout_p0203_bounded_degree_unit_circle_conjugates_clos.bounded_degree_unit_circle_conjugates_closed_discrete" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let S_B := {x | 1 < x ∧ IsIntegral ℤ x ∧ ↑(minpoly ℚ x).natDegree ≤ B ∧ (∀ (z : ℂ), (Polynomial.map (algebraMap ℚ ℂ) (minpoly ℚ x)).IsRoot z → z ≠ ↑x → ‖z‖ ≤ 1) ∧ ∃ z, (Polynomial.map (algebraMap ℚ ℂ) (minpoly ℚ x)).IsRoot z ∧ z ≠ ↑x ∧ ‖z‖ = 1}; IsClosed S_B ∧ ∀ x ∈ S_B, ∃ ε > 0, S_B ∩ Set.Ioo (x - ε) (x + ε) = {x}\"},\"graphEdgeId\":\"h_goal\",\"premises\":[],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0203_bounded_degree_unit_circle_conjugates_clos\",\"reconstructedProofSha256\":\"3f4b66458cca99b3424a1e5e891e895af9d70123ff9756984be2e507410ea525\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p0203_bounded_degree_unit_circle_conjugates_clos.bounded_degree_unit_circle_conjugates_closed_discrete\",\"topologySha256\":\"0d3ed57d531cecb968ecb1c17477c7cc833bca9b3dff39bd1ddde5a273c210da\"}"

namespace Rollout_p0229_euclidean_decomposition_bound

-- graph_id: p0229_euclidean_decomposition_bound
-- topology_sha256: 60d8d4e289aa2948542a900b0644473c2588737e01bfa65a0a429d00fc12a92b
/- verified submission -/
theorem euclidean_decomposition_bound (n e p : ℕ) (hn : 0 < n) (he : 0 < e)
    (hp : Nat.Prime p) (hsize : 4 * p ^ 2 ≤ n + 2) (hep : e ≤ p + 1) :
    ∃ d f : ℕ, f < p ∧ n + 2 = p * d + f + e ∧
      d ≥ e + f + (2 * p - 2) := by
  have hp0 : 0 < p := hp.pos
  have hp2 : 2 ≤ p := hp.two_le
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp2
  have hm : e ≤ n + 2 := by
    have hp_sq : 2 + q + 1 ≤ 4 * (2 + q) ^ 2 := by
      nlinarith
    exact le_trans hep (le_trans hp_sq hsize)
  let d := (n + 2 - e) / (2 + q)
  let f := (n + 2 - e) % (2 + q)
  have hf : f < 2 + q := by
    dsimp [f]
    exact Nat.mod_lt _ (by omega)
  have hdiv : (2 + q) * d + f = n + 2 - e := by
    dsimp [d, f]
    exact Nat.div_add_mod (n + 2 - e) (2 + q)
  have hdecomp : n + 2 = (2 + q) * d + f + e := by
    calc
      n + 2 = (n + 2 - e) + e := (Nat.sub_add_cancel hm).symm
      _ = ((2 + q) * d + f) + e := by rw [hdiv]
      _ = (2 + q) * d + f + e := rfl
  have hd4 : 4 * (2 + q) - 2 ≤ d := by
    dsimp [d]
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2 + q)).mpr
    have hmul : (4 * (2 + q) - 2) * (2 + q) ≤ n + 2 - e := by
      apply (Nat.le_sub_iff_add_le hm).mpr
      have hsub : 4 * (2 + q) - 2 = 6 + 4 * q := by omega
      rw [hsub]
      nlinarith
    exact hmul
  refine ⟨d, f, hf, hdecomp, ?_⟩
  have htarget : e + f + (2 * (2 + q) - 2) ≤ 4 * (2 + q) - 2 := by
    omega
  exact le_trans htarget hd4

end Rollout_p0229_euclidean_decomposition_bound

#check_dependency_graph "Rollout_p0229_euclidean_decomposition_bound.euclidean_decomposition_bound" against "{\"edges\":[{\"conclusion\":{\"name\":\"hp0\",\"statement\":\"0 < p\"},\"graphEdgeId\":\"h_001_hp0\",\"premises\":[{\"name\":\"hp\",\"statement\":\"Nat.Prime p\"}],\"rawEdgeId\":\"telescope_8\"},{\"conclusion\":{\"name\":\"hp2\",\"statement\":\"2 ≤ p\"},\"graphEdgeId\":\"h_002_hp2\",\"premises\":[{\"name\":\"hp\",\"statement\":\"Nat.Prime p\"}],\"rawEdgeId\":\"telescope_9\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∃ d, ∃ f < p, n + 2 = p * d + f + e ∧ d ≥ e + f + (2 * p - 2)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hp\",\"statement\":\"Nat.Prime p\"},{\"name\":\"hsize\",\"statement\":\"4 * p ^ 2 ≤ n + 2\"},{\"name\":\"hep\",\"statement\":\"e ≤ p + 1\"},{\"name\":\"hp0\",\"statement\":\"0 < p\"},{\"name\":\"hp2\",\"statement\":\"2 ≤ p\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0229_euclidean_decomposition_bound\",\"reconstructedProofSha256\":\"ed084d87a7eba607d533b02d0cca9c0615efa29faf08751225b856440585e72c\",\"selectedEdgeCount\":3,\"theoremName\":\"Rollout_p0229_euclidean_decomposition_bound.euclidean_decomposition_bound\",\"topologySha256\":\"60d8d4e289aa2948542a900b0644473c2588737e01bfa65a0a429d00fc12a92b\"}"

namespace Rollout_p0246_formalpowerseries_automorphism_exact_seque

-- graph_id: p0246_formalpowerseries_automorphism_exact_seque
-- topology_sha256: 8fca2d9d47864411a13fe5cf51fc66dc9cb51f610c367e248277ea0507cb00dc
/- accepted add_to_file helper 1 -/

noncomputable section

namespace FPSAut

abbrev PS := PowerSeries ℂ

instance : TopologicalSpace PS :=
  PowerSeries.WithPiTopology.instTopologicalSpace ℂ

instance : UniformSpace PS :=
  PowerSeries.WithPiTopology.instUniformSpace ℂ

instance : IsUniformAddGroup PS :=
  PowerSeries.WithPiTopology.instIsUniformAddGroup ℂ

instance : IsTopologicalRing PS :=
  PowerSeries.WithPiTopology.instIsTopologicalRing ℂ

instance : T2Space PS :=
  PowerSeries.WithPiTopology.instT2Space ℂ

instance : CompleteSpace PS :=
  PowerSeries.WithPiTopology.instCompleteSpace ℂ

instance : ContinuousSMul ℂ PS :=
  MvPowerSeries.WithPiTopology.instContinuousSMul (σ := Unit) (R := ℂ) (S := ℂ)

lemma algHom_constantCoeff_X (φ : PS →ₐ[ℂ] PS) :
    PowerSeries.constantCoeff (φ PowerSeries.X) = 0 := by
  by_contra hc
  let c : ℂ := PowerSeries.constantCoeff (φ PowerSeries.X)
  have hunit : IsUnit (PowerSeries.X - PowerSeries.C c : PS) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp [c, hc]
  have hunit_image : IsUnit (φ (PowerSeries.X - PowerSeries.C c : PS)) :=
    hunit.map φ.toRingHom
  have hphiC : φ (PowerSeries.C c : PS) = PowerSeries.C c := by
    rw [PowerSeries.C_eq_algebraMap]
    exact φ.commutes c
  have hconst : PowerSeries.constantCoeff (φ (PowerSeries.X - PowerSeries.C c : PS)) = 0 := by
    calc
      PowerSeries.constantCoeff (φ (PowerSeries.X - PowerSeries.C c : PS))
          = PowerSeries.constantCoeff (φ PowerSeries.X - φ (PowerSeries.C c : PS)) := by
              rw [map_sub]
      _ = c - c := by simp [c, hphiC]
      _ = 0 := sub_self c
  rw [PowerSeries.isUnit_iff_constantCoeff, hconst] at hunit_image
  exact not_isUnit_zero hunit_image

lemma algHom_coeff_eq_sum (φ : PS →ₐ[ℂ] PS) (n : ℕ) (f : PS) :
    (PowerSeries.coeff n) (φ f) =
      ∑ i ∈ Finset.range (n + 1),
        (PowerSeries.coeff i) f * (PowerSeries.coeff n) ((φ PowerSeries.X) ^ i) := by
  let p : Polynomial ℂ := PowerSeries.trunc (n + 1) f
  have hdiv : PowerSeries.X ^ (n + 1) ∣ f - (p : PS) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    simp [p, PowerSeries.coeff_trunc, hm]
  rcases hdiv with ⟨r, hr⟩
  have hXdvd : PowerSeries.X ∣ φ PowerSeries.X := by
    rw [PowerSeries.X_dvd_iff]
    exact algHom_constantCoeff_X φ
  have hpowdvd : PowerSeries.X ^ (n + 1) ∣ (φ PowerSeries.X) ^ (n + 1) :=
    pow_dvd_pow_of_dvd hXdvd (n + 1)
  have htaildvd : PowerSeries.X ^ (n + 1) ∣ (φ PowerSeries.X) ^ (n + 1) * φ r :=
    Dvd.dvd.mul_right hpowdvd (φ r)
  have htailcoeff :
      (PowerSeries.coeff n) ((φ PowerSeries.X) ^ (n + 1) * φ r) = 0 :=
    (PowerSeries.X_pow_dvd_iff.mp htaildvd) n (Nat.lt_succ_self n)
  have hsplit : φ f = φ (p : PS) + (φ PowerSeries.X) ^ (n + 1) * φ r := by
    calc
      φ f = φ ((f - (p : PS)) + (p : PS)) := by rw [sub_add_cancel]
      _ = φ (PowerSeries.X ^ (n + 1) * r + (p : PS)) := by rw [hr]
      _ = (φ PowerSeries.X) ^ (n + 1) * φ r + φ (p : PS) := by
        simp [map_add, map_mul, map_pow]
      _ = φ (p : PS) + (φ PowerSeries.X) ^ (n + 1) * φ r := add_comm _ _
  have hp : φ (p : PS) =
      Polynomial.eval₂ (algebraMap ℂ PS) (φ PowerSeries.X) p := by
    have h := Polynomial.aeval_algHom_apply φ (PowerSeries.X : PS) p
    have hXcoe : Polynomial.aeval (PowerSeries.X : PS) =
        (Polynomial.coeToPowerSeries.algHom (A := ℂ) : Polynomial ℂ →ₐ[ℂ] PS) := by
      apply Polynomial.algHom_ext
      simp
    calc
      φ (p : PS) = φ ((Polynomial.aeval (PowerSeries.X : PS)) p) := by
        rw [hXcoe]
        rfl
      _ = (Polynomial.aeval (φ PowerSeries.X)) p := h.symm
      _ = Polynomial.eval₂ (algebraMap ℂ PS) (φ PowerSeries.X) p := Polynomial.aeval_def _ _
  calc
    (PowerSeries.coeff n) (φ f)
        = (PowerSeries.coeff n) (φ (p : PS)) +
          (PowerSeries.coeff n) ((φ PowerSeries.X) ^ (n + 1) * φ r) := by
            rw [hsplit, map_add]
    _ = (PowerSeries.coeff n) (φ (p : PS)) := by simp [htailcoeff]
    _ = (PowerSeries.coeff n)
          (Polynomial.eval₂ (algebraMap ℂ PS) (φ PowerSeries.X) p) := by rw [hp]
    _ = ∑ i ∈ Finset.range (n + 1),
          (PowerSeries.coeff i) f * (PowerSeries.coeff n) ((φ PowerSeries.X) ^ i) := by
        rw [PowerSeries.eval₂_trunc_eq_sum_range]
        simp

lemma algHom_continuous (φ : PS →ₐ[ℂ] PS) :
    Continuous (φ : PS → PS) := by
  have hcoeff : ∀ n : ℕ, Continuous fun f : PS => (PowerSeries.coeff n) (φ f) := by
    intro n
    have hfun : (fun f : PS => (PowerSeries.coeff n) (φ f)) =
        (fun f : PS => ∑ i ∈ Finset.range (n + 1),
          (PowerSeries.coeff i) f * (PowerSeries.coeff n) ((φ PowerSeries.X) ^ i)) := by
      funext f
      exact algHom_coeff_eq_sum φ n f
    rw [hfun]
    apply continuous_finset_sum
    intro i hi
    exact (PowerSeries.WithPiTopology.continuous_coeff ℂ i).mul continuous_const
  have hmc : ∀ d : Unit →₀ ℕ, Continuous fun f : PS => MvPowerSeries.coeff d (φ f) := by
    intro d
    have deq : d = (Finsupp.single (α := Unit) () (d ())) := by
      apply Finsupp.ext
      intro x
      cases x
      simp
    have hd : (fun f : PS => MvPowerSeries.coeff d (φ f)) =
        (fun f : PS => PowerSeries.coeff (d ()) (φ f)) := by
      funext f
      rw [deq]
      simp [PowerSeries.coeff]
    rw [hd]
    exact hcoeff (d ())
  have hpi : Continuous (fun f : PS => fun d : Unit →₀ ℕ => MvPowerSeries.coeff d (φ f)) :=
    continuous_pi hmc
  change Continuous (fun f : PS => φ f)
  exact hpi

lemma algEquiv_continuous (ρ : PS ≃ₐ[ℂ] PS) :
    Continuous (ρ : PS → PS) ∧ Continuous (ρ.symm : PS → PS) :=
  ⟨algHom_continuous ρ.toAlgHom, algHom_continuous ρ.symm.toAlgHom⟩

/- accepted add_to_file helper 2 -/
lemma preservingSubgroup_one (S : Set PS) :
    (1 : PS ≃ₐ[ℂ] PS) '' S = S := by
  ext x
  simp

def preservingSubgroup (S : Set PS) : Subgroup (PS ≃ₐ[ℂ] PS) where
  carrier := {ρ | (ρ : PS → PS) '' S = S}
  one_mem' := preservingSubgroup_one S
  mul_mem' := by
    intro ρ σ hρ hσ
    calc
      ((ρ * σ : PS ≃ₐ[ℂ] PS) : PS → PS) '' S
          = (ρ : PS → PS) '' ((σ : PS → PS) '' S) := by
            ext x
            simp [Set.mem_image, AlgEquiv.mul_apply]
      _ = (ρ : PS → PS) '' S := by rw [hσ]
      _ = S := hρ
  inv_mem' := by
    intro ρ hρ
    have hpre : (ρ : PS → PS) ⁻¹' S = S := by
      calc
        (ρ : PS → PS) ⁻¹' S = (ρ : PS → PS) ⁻¹' ((ρ : PS → PS) '' S) := by rw [hρ]
        _ = S := Equiv.preimage_image ρ.toEquiv S
    calc
      ((ρ⁻¹ : PS ≃ₐ[ℂ] PS) : PS → PS) '' S = (ρ : PS → PS) ⁻¹' S := by
        change ρ.toEquiv.symm '' S = (ρ : PS → PS) ⁻¹' S
        exact Equiv.image_symm_eq_preimage ρ.toEquiv S
      _ = S := hpre

/- accepted add_to_file helper 3 -/
lemma expand_injective {p : ℕ} (hp : p ≠ 0) :
    Function.Injective (PowerSeries.expand p hp : PS →ₐ[ℂ] PS) := by
  intro f g h
  ext k
  have hk := congrArg (PowerSeries.coeff (p * k)) h
  have hpos : 0 < p := Nat.pos_of_ne_zero hp
  simpa [PowerSeries.coeff_expand, Nat.mul_div_cancel_left k hpos] using hk

/- accepted add_to_file helper 4 -/
noncomputable def restrictExpandAlgHom {p : ℕ} (hp : p ≠ 0)
    (ρ : PS ≃ₐ[ℂ] PS)
    (hρ : (ρ : PS → PS) '' Set.range (PowerSeries.expand p hp : PS →ₐ[ℂ] PS) =
      Set.range (PowerSeries.expand p hp : PS →ₐ[ℂ] PS)) :
    PS →ₐ[ℂ] PS :=
  let e : PS →ₐ[ℂ] PS := PowerSeries.expand p hp
  let S : Set PS := Set.range e
  let F : PS → PS := fun f =>
    Classical.choose (show ∃ g, e g = ρ (e f) from by
      have hmem : ρ (e f) ∈ S := by
        have him : ρ (e f) ∈ (ρ : PS → PS) '' S := by
          exact ⟨e f, ⟨f, rfl⟩, rfl⟩
        rwa [hρ] at him
      rcases hmem with ⟨g, hg⟩
      exact ⟨g, hg⟩)
  have hF : ∀ f, e (F f) = ρ (e f) := fun f =>
    Classical.choose_spec (show ∃ g, e g = ρ (e f) from by
      have hmem : ρ (e f) ∈ S := by
        have him : ρ (e f) ∈ (ρ : PS → PS) '' S := by
          exact ⟨e f, ⟨f, rfl⟩, rfl⟩
        rwa [hρ] at him
      rcases hmem with ⟨g, hg⟩
      exact ⟨g, hg⟩)
  { toFun := F
    map_one' := by
      apply expand_injective hp
      calc
        e (F 1) = ρ (e 1) := hF 1
        _ = 1 := by simp
        _ = e 1 := by simp
    map_mul' := by
      intro x y
      apply expand_injective hp
      calc
        e (F (x * y)) = ρ (e (x * y)) := hF (x * y)
        _ = ρ (e x) * ρ (e y) := by simp
        _ = e (F x) * e (F y) := by rw [hF x, hF y]
        _ = e (F x * F y) := by simp
    map_zero' := by
      apply expand_injective hp
      calc
        e (F 0) = ρ (e 0) := hF 0
        _ = 0 := by simp
        _ = e 0 := by simp
    map_add' := by
      intro x y
      apply expand_injective hp
      calc
        e (F (x + y)) = ρ (e (x + y)) := hF (x + y)
        _ = ρ (e x) + ρ (e y) := by simp
        _ = e (F x) + e (F y) := by rw [hF x, hF y]
        _ = e (F x + F y) := by simp
    commutes' := by
      intro r
      apply expand_injective hp
      calc
        e (F ((algebraMap ℂ PS) r)) = ρ (e ((algebraMap ℂ PS) r)) := hF _
        _ = (algebraMap ℂ PS) r := by
          simp [e, PowerSeries.C_eq_algebraMap]
        _ = e ((algebraMap ℂ PS) r) := by
          simp [e, PowerSeries.C_eq_algebraMap] }

/- accepted add_to_file helper 5 -/
lemma restrictExpandAlgHom_spec {p : ℕ} (hp : p ≠ 0)
    (ρ : PS ≃ₐ[ℂ] PS)
    (hρ : (ρ : PS → PS) '' Set.range (PowerSeries.expand p hp : PS →ₐ[ℂ] PS) =
      Set.range (PowerSeries.expand p hp : PS →ₐ[ℂ] PS)) (f : PS) :
    (PowerSeries.expand p hp) ((restrictExpandAlgHom hp ρ hρ) f) =
      ρ ((PowerSeries.expand p hp) f) := by
  unfold restrictExpandAlgHom
  simp only
  exact Classical.choose_spec (show ∃ g, (PowerSeries.expand p hp) g =
    ρ ((PowerSeries.expand p hp) f) from by
      have hmem : ρ ((PowerSeries.expand p hp) f) ∈
          Set.range (PowerSeries.expand p hp : PS →ₐ[ℂ] PS) := by
        have him : ρ ((PowerSeries.expand p hp) f) ∈ (ρ : PS → PS) ''
            Set.range (PowerSeries.expand p hp : PS →ₐ[ℂ] PS) := by
          exact ⟨(PowerSeries.expand p hp) f, ⟨f, rfl⟩, rfl⟩
        rwa [hρ] at him
      rcases hmem with ⟨g, hg⟩
      exact ⟨g, hg⟩)

/- accepted add_to_file helper 6 -/
lemma restrictExpandAlgHom_bijective {p : ℕ} (hp : p ≠ 0)
    (ρ : PS ≃ₐ[ℂ] PS)
    (hρ : (ρ : PS → PS) '' Set.range (PowerSeries.expand p hp : PS →ₐ[ℂ] PS) =
      Set.range (PowerSeries.expand p hp : PS →ₐ[ℂ] PS)) :
    Function.Bijective (restrictExpandAlgHom hp ρ hρ) := by
  let e : PS →ₐ[ℂ] PS := PowerSeries.expand p hp
  let S : Set PS := Set.range e
  constructor
  · intro x y hxy
    apply expand_injective hp
    have hx := restrictExpandAlgHom_spec hp ρ hρ x
    have hy := restrictExpandAlgHom_spec hp ρ hρ y
    have heq : ρ (e x) = ρ (e y) := by
      calc
        ρ (e x) = e ((restrictExpandAlgHom hp ρ hρ) x) := by
          simpa [e] using hx.symm
        _ = e ((restrictExpandAlgHom hp ρ hρ) y) := by rw [hxy]
        _ = ρ (e y) := by simpa [e] using hy
    exact ρ.injective heq
  · intro y
    have hyS : e y ∈ S := ⟨y, rfl⟩
    have him : e y ∈ (ρ : PS → PS) '' S := by
      rwa [hρ]
    rcases him with ⟨x, hxS, hρx⟩
    rcases hxS with ⟨f, rfl⟩
    refine ⟨f, ?_⟩
    apply expand_injective hp
    calc
      e ((restrictExpandAlgHom hp ρ hρ) f) = ρ (e f) := by
        simpa [e] using restrictExpandAlgHom_spec hp ρ hρ f
      _ = e y := hρx

noncomputable def restrictExpandEquiv {p : ℕ} (hp : p ≠ 0)
    (ρ : PS ≃ₐ[ℂ] PS)
    (hρ : (ρ : PS → PS) '' Set.range (PowerSeries.expand p hp : PS →ₐ[ℂ] PS) =
      Set.range (PowerSeries.expand p hp : PS →ₐ[ℂ] PS)) :
    PS ≃ₐ[ℂ] PS :=
  AlgEquiv.ofBijective (restrictExpandAlgHom hp ρ hρ)
    (restrictExpandAlgHom_bijective hp ρ hρ)

lemma restrictExpandEquiv_spec {p : ℕ} (hp : p ≠ 0)
    (ρ : PS ≃ₐ[ℂ] PS)
    (hρ : (ρ : PS → PS) '' Set.range (PowerSeries.expand p hp : PS →ₐ[ℂ] PS) =
      Set.range (PowerSeries.expand p hp : PS →ₐ[ℂ] PS)) (f : PS) :
    (PowerSeries.expand p hp) ((restrictExpandEquiv hp ρ hρ) f) =
      ρ ((PowerSeries.expand p hp) f) := by
  exact restrictExpandAlgHom_spec hp ρ hρ f

/- accepted add_to_file helper 7 -/
noncomputable def restrictExpandMonoidHom {p : ℕ} (hp : p ≠ 0) :
    preservingSubgroup (Set.range (PowerSeries.expand p hp : PS →ₐ[ℂ] PS)) →*
      (⊤ : Subgroup (PS ≃ₐ[ℂ] PS)) where
  toFun ρ := ⟨restrictExpandEquiv hp ρ.1 ρ.2, trivial⟩
  map_one' := by
    apply Subtype.ext
    apply AlgEquiv.ext
    intro f
    apply expand_injective hp
    calc
      (PowerSeries.expand p hp)
          ((restrictExpandEquiv hp (1 : PS ≃ₐ[ℂ] PS) (preservingSubgroup_one _)) f)
          = (1 : PS ≃ₐ[ℂ] PS) ((PowerSeries.expand p hp) f) := by
            exact restrictExpandEquiv_spec hp _ _ f
      _ = (PowerSeries.expand p hp) f := by simp
  map_mul' := by
    intro ρ σ
    apply Subtype.ext
    apply AlgEquiv.ext
    intro f
    apply expand_injective hp
    calc
      (PowerSeries.expand p hp) ((restrictExpandEquiv hp (ρ * σ).1 (ρ * σ).2) f)
          = ((ρ * σ).1 : PS ≃ₐ[ℂ] PS) ((PowerSeries.expand p hp) f) := by
            exact restrictExpandEquiv_spec hp _ _ f
      _ = ρ.1 (σ.1 ((PowerSeries.expand p hp) f)) := by
            simp [AlgEquiv.mul_apply]
      _ = ρ.1 ((PowerSeries.expand p hp) ((restrictExpandEquiv hp σ.1 σ.2) f)) := by
            rw [restrictExpandEquiv_spec hp σ.1 σ.2 f]
      _ = (PowerSeries.expand p hp)
          ((restrictExpandEquiv hp ρ.1 ρ.2) ((restrictExpandEquiv hp σ.1 σ.2) f)) := by
            rw [restrictExpandEquiv_spec hp ρ.1 ρ.2]
      _ = (PowerSeries.expand p hp)
          (((restrictExpandEquiv hp ρ.1 ρ.2) * (restrictExpandEquiv hp σ.1 σ.2) :
            PS ≃ₐ[ℂ] PS) f) := by
            simp [AlgEquiv.mul_apply]

/- accepted add_to_file helper 8 -/
lemma binomialSeries_pow_eq (n : ℕ) (r : ℚ) :
    (PowerSeries.binomialSeries ℂ r) ^ n =
      PowerSeries.binomialSeries ℂ ((n : ℚ) * r) := by
  induction n with
  | zero => simp [PowerSeries.binomialSeries_zero]
  | succ n ih =>
      calc
        (PowerSeries.binomialSeries ℂ r) ^ (n + 1)
            = (PowerSeries.binomialSeries ℂ r) ^ n * PowerSeries.binomialSeries ℂ r := by
                rw [pow_succ]
        _ = PowerSeries.binomialSeries ℂ ((n : ℚ) * r) *
            PowerSeries.binomialSeries ℂ r := by rw [ih]
        _ = PowerSeries.binomialSeries ℂ ((n : ℚ) * r + r) := by
                rw [← PowerSeries.binomialSeries_add]
        _ = PowerSeries.binomialSeries ℂ (((n + 1 : ℕ) : ℚ) * r) := by
                congr 1
                push_cast
                ring

lemma binomialSeries_inv_pow (n : ℕ) (hn : n ≠ 0) :
    (PowerSeries.binomialSeries ℂ ((n : ℚ)⁻¹)) ^ n = 1 + PowerSeries.X := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  calc
    (PowerSeries.binomialSeries ℂ ((n : ℚ)⁻¹)) ^ n
        = PowerSeries.binomialSeries ℂ ((n : ℚ) * (n : ℚ)⁻¹) :=
          binomialSeries_pow_eq n _
    _ = PowerSeries.binomialSeries ℂ (1 : ℚ) := by rw [mul_inv_cancel₀ hnq]
    _ = (1 + PowerSeries.X) ^ 1 := by
          exact PowerSeries.binomialSeries_nat (A := ℂ) (R := ℚ) 1
    _ = 1 + PowerSeries.X := by simp

/- accepted add_to_file helper 9 -/
lemma subst_one {a : PS} (ha : PowerSeries.HasSubst a) :
    PowerSeries.subst a (1 : PowerSeries ℂ) = 1 := by
  rw [← PowerSeries.coe_substAlgHom ha]
  exact map_one (PowerSeries.substAlgHom ha)

lemma subst_one_add_X {a : PS} (ha : PowerSeries.HasSubst a) :
    PowerSeries.subst a (1 + PowerSeries.X : PowerSeries ℂ) = 1 + a := by
  rw [PowerSeries.subst_add ha, subst_one ha, PowerSeries.subst_X ha]

lemma exists_pow_eq_of_constantCoeff_ne_zero {N : ℕ} (hN : 0 < N) (q : PS)
    (hq : PowerSeries.constantCoeff q ≠ 0) : ∃ r : PS, r ^ N = q := by
  classical
  let c : ℂ := PowerSeries.constantCoeff q
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (k := ℂ) c (n := N) hN
  have hb0 : b ≠ 0 := by
    intro hzero
    apply hq
    calc
      c = b ^ N := hb.symm
      _ = 0 := by rw [hzero, zero_pow (Nat.ne_of_gt hN)]
  let u : PS := q * PowerSeries.C c⁻¹
  have huconst : PowerSeries.constantCoeff u = 1 := by
    calc
      PowerSeries.constantCoeff u = c * c⁻¹ := by simp [u, c]
      _ = 1 := mul_inv_cancel₀ hq
  let x : PS := u - 1
  have hxconst : PowerSeries.constantCoeff x = 0 := by
    simp [x, huconst]
  have hx : PowerSeries.HasSubst x :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hxconst
  let B : PowerSeries ℂ := PowerSeries.binomialSeries ℂ ((N : ℚ)⁻¹)
  let t : PS := PowerSeries.subst x B
  have ht : t ^ N = u := by
    calc
      t ^ N = PowerSeries.subst x (B ^ N) := by
        rw [PowerSeries.subst_pow hx]
      _ = PowerSeries.subst x (1 + PowerSeries.X : PowerSeries ℂ) := by
        dsimp [B]
        rw [binomialSeries_inv_pow N (Nat.ne_of_gt hN)]
      _ = 1 + x := subst_one_add_X hx
      _ = u := by simp [x]
  refine ⟨PowerSeries.C b * t, ?_⟩
  calc
    (PowerSeries.C b * t) ^ N = (PowerSeries.C b) ^ N * t ^ N := by
      rw [mul_pow]
    _ = PowerSeries.C c * u := by
      rw [ht]
      congr 1
      calc
        (PowerSeries.C b) ^ N = PowerSeries.C (b ^ N) := by simp [map_pow]
        _ = PowerSeries.C c := by rw [hb]
    _ = q := by
      calc
        PowerSeries.C c * u = q * (PowerSeries.C c * PowerSeries.C c⁻¹) := by
          dsimp [u]
          ring
        _ = q * PowerSeries.C (c * c⁻¹) := by rw [← map_mul]
        _ = q * 1 := by rw [mul_inv_cancel₀ hq, map_one]
        _ = q := mul_one q

/- accepted add_to_file helper 10 -/
lemma algEquiv_constantCoeff_X (ρ : PS ≃ₐ[ℂ] PS) :
    PowerSeries.constantCoeff (ρ PowerSeries.X) = 0 :=
  algHom_constantCoeff_X ρ.toAlgHom

lemma algEquiv_coeff_one_X_ne_zero (ρ : PS ≃ₐ[ℂ] PS) :
    (PowerSeries.coeff 1) (ρ PowerSeries.X) ≠ 0 := by
  intro h1
  have h0 := algEquiv_constantCoeff_X ρ
  have h := algHom_coeff_eq_sum ρ.symm.toAlgHom 1 (ρ PowerSeries.X)
  have hzero : (PowerSeries.coeff 1) (ρ.symm (ρ PowerSeries.X)) = 0 := by
    simpa [Finset.sum_range_succ, h0, h1] using h
  have hone : (PowerSeries.coeff 1) (ρ.symm (ρ PowerSeries.X)) = 1 := by
    simp
  rw [hone] at hzero
  exact one_ne_zero hzero

/- accepted add_to_file helper 11 -/
lemma coeff_pow_eq_zero_of_constantCoeff_zero_of_lt {w : PS}
    (h0 : PowerSeries.constantCoeff w = 0) {i n : ℕ} (h : n < i) :
    (PowerSeries.coeff n) (w ^ i) = 0 := by
  have hXdvd : (PowerSeries.X : PS) ∣ w := by
    rw [PowerSeries.X_dvd_iff]
    exact h0
  have hi : (PowerSeries.X : PS) ^ i ∣ w ^ i := pow_dvd_pow_of_dvd hXdvd i
  have hs : (PowerSeries.X : PS) ^ (n + 1) ∣ (PowerSeries.X : PS) ^ i :=
    pow_dvd_pow (PowerSeries.X : PS) (Nat.succ_le_of_lt h)
  have htail : (PowerSeries.X : PS) ^ (n + 1) ∣ w ^ i := hs.trans hi
  exact (PowerSeries.X_pow_dvd_iff.mp htail) n (Nat.lt_succ_self n)

lemma order_eq_one_of_constantCoeff_zero {w : PS}
    (h0 : PowerSeries.constantCoeff w = 0)
    (h1 : (PowerSeries.coeff 1) w ≠ 0) : w.order = 1 := by
  change w.order = ((1 : ℕ) : ℕ∞)
  rw [PowerSeries.order_eq_nat]
  constructor
  · exact h1
  · intro i hi
    interval_cases i
    simpa [PowerSeries.coeff_zero_eq_constantCoeff] using h0

lemma coeff_self_pow_eq_coeff_one_pow {w : PS} (n : ℕ)
    (h0 : PowerSeries.constantCoeff w = 0)
    (h1 : (PowerSeries.coeff 1) w ≠ 0) :
    (PowerSeries.coeff n) (w ^ n) = ((PowerSeries.coeff 1) w) ^ n := by
  have horder : w.order = 1 := order_eq_one_of_constantCoeff_zero h0 h1
  have horderpow : (w ^ n).order = n := by
    rw [PowerSeries.order_pow, horder]
    simp
  have htoNat : (w ^ n).order.toNat = n := by
    rw [horderpow]
    rfl
  have hdecomp : PowerSeries.X ^ n * (w ^ n).divXPowOrder = w ^ n := by
    have h := PowerSeries.X_pow_order_mul_divXPowOrder (f := w ^ n)
    rwa [htoNat] at h
  have hcoeff_div :
      (PowerSeries.coeff n) (w ^ n) =
        PowerSeries.constantCoeff ((w ^ n).divXPowOrder) := by
    calc
      (PowerSeries.coeff n) (w ^ n)
          = (PowerSeries.coeff n) (PowerSeries.X ^ n * (w ^ n).divXPowOrder) := by
              rw [hdecomp]
      _ = (PowerSeries.coeff 0) ((w ^ n).divXPowOrder) := by
              convert PowerSeries.coeff_X_pow_mul ((w ^ n).divXPowOrder) n 0 using 2
              simp
      _ = PowerSeries.constantCoeff ((w ^ n).divXPowOrder) := by
              rw [PowerSeries.coeff_zero_eq_constantCoeff]
  have hlead : PowerSeries.constantCoeff w.divXPowOrder = (PowerSeries.coeff 1) w := by
    have hdecw : PowerSeries.X ^ 1 * w.divXPowOrder = w := by
      have h := PowerSeries.X_pow_order_mul_divXPowOrder (f := w)
      rwa [horder] at h
    calc
      PowerSeries.constantCoeff w.divXPowOrder
          = (PowerSeries.coeff 0) w.divXPowOrder := by
              rw [PowerSeries.coeff_zero_eq_constantCoeff]
      _ = (PowerSeries.coeff (0 + 1)) (PowerSeries.X ^ 1 * w.divXPowOrder) := by
              rw [PowerSeries.coeff_X_pow_mul]
      _ = (PowerSeries.coeff 1) w := by
              rw [hdecw]
  calc
    (PowerSeries.coeff n) (w ^ n)
        = PowerSeries.constantCoeff ((w ^ n).divXPowOrder) := hcoeff_div
    _ = PowerSeries.constantCoeff (w.divXPowOrder ^ n) := by
          rw [PowerSeries.divXPowOrder_pow]
    _ = (PowerSeries.constantCoeff w.divXPowOrder) ^ n := by simp
    _ = ((PowerSeries.coeff 1) w) ^ n := by rw [hlead]

/- accepted add_to_file helper 12 -/
noncomputable def substPreimage (w g : PS) : PS :=
  PowerSeries.mk fun n =>
    Nat.strongRec
      (fun n rec =>
        ((PowerSeries.coeff n) g -
          ∑ i ∈ Finset.range n,
            (if hi : i < n then rec i hi else 0) *
              (PowerSeries.coeff n) (w ^ i)) *
          (((PowerSeries.coeff 1) w) ^ n)⁻¹)
      n

lemma coeff_substPreimage (w g : PS) (n : ℕ) :
    (PowerSeries.coeff n) (substPreimage w g) =
      ((PowerSeries.coeff n) g -
        ∑ i ∈ Finset.range n,
          (PowerSeries.coeff i) (substPreimage w g) *
            (PowerSeries.coeff n) (w ^ i)) *
        (((PowerSeries.coeff 1) w) ^ n)⁻¹ := by
  rw [substPreimage, PowerSeries.coeff_mk, Nat.strongRec_eq]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  simp [hin]

lemma substAlgHom_surjective_of_constantCoeff_zero {w : PS}
    (h0 : PowerSeries.constantCoeff w = 0)
    (h1 : (PowerSeries.coeff 1) w ≠ 0) :
    Function.Surjective
      (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' h0) :
        PS →ₐ[ℂ] PS) := by
  intro g
  let hw := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  let subhom : PS →ₐ[ℂ] PS := PowerSeries.substAlgHom hw
  let f := substPreimage w g
  refine ⟨f, ?_⟩
  ext n
  have hX : subhom PowerSeries.X = w := by
    change (PowerSeries.substAlgHom hw) PowerSeries.X = w
    rw [PowerSeries.coe_substAlgHom]
    exact PowerSeries.subst_X hw
  have h := algHom_coeff_eq_sum subhom n f
  rw [hX] at h
  let a : ℂ := (PowerSeries.coeff 1) w
  have han : a ^ n ≠ 0 := pow_ne_zero n h1
  have hprev :
      (∑ i ∈ Finset.range (n + 1),
        (PowerSeries.coeff i) f * (PowerSeries.coeff n) (w ^ i)) =
      (∑ i ∈ Finset.range n,
        (PowerSeries.coeff i) f * (PowerSeries.coeff n) (w ^ i)) +
        (PowerSeries.coeff n) f * a ^ n := by
    rw [Finset.sum_range_succ]
    congr 1
    simp [a, coeff_self_pow_eq_coeff_one_pow n h0 h1]
  have hfn :
      (PowerSeries.coeff n) f =
        (((PowerSeries.coeff n) g -
          ∑ i ∈ Finset.range n,
            (PowerSeries.coeff i) f * (PowerSeries.coeff n) (w ^ i)) * (a ^ n)⁻¹) := by
    simpa [f, a] using coeff_substPreimage w g n
  calc
    (PowerSeries.coeff n) (subhom f)
        = ∑ i ∈ Finset.range (n + 1),
          (PowerSeries.coeff i) f * (PowerSeries.coeff n) (w ^ i) := h
    _ = (∑ i ∈ Finset.range n,
          (PowerSeries.coeff i) f * (PowerSeries.coeff n) (w ^ i)) +
          (PowerSeries.coeff n) f * a ^ n := hprev
    _ = (∑ i ∈ Finset.range n,
          (PowerSeries.coeff i) f * (PowerSeries.coeff n) (w ^ i)) +
          (((PowerSeries.coeff n) g -
            ∑ i ∈ Finset.range n,
              (PowerSeries.coeff i) f * (PowerSeries.coeff n) (w ^ i)) *
            (a ^ n)⁻¹) * a ^ n := by rw [hfn]
    _ = (PowerSeries.coeff n) g := by
      rw [mul_assoc, inv_mul_cancel₀ han, mul_one]
      simp

/- accepted add_to_file helper 13 -/
lemma substAlgHom_injective_of_constantCoeff_zero {w : PS}
    (h0 : PowerSeries.constantCoeff w = 0)
    (h1 : (PowerSeries.coeff 1) w ≠ 0) :
    Function.Injective
      (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' h0) :
        PS →ₐ[ℂ] PS) := by
  intro x y hxy
  let hw := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  let subhom : PS →ₐ[ℂ] PS := PowerSeries.substAlgHom hw
  have hX : subhom PowerSeries.X = w := by
    change (PowerSeries.substAlgHom hw) PowerSeries.X = w
    rw [PowerSeries.coe_substAlgHom]
    exact PowerSeries.subst_X hw
  have hd : subhom (x - y) = 0 := by
    calc
      subhom (x - y) = subhom x - subhom y := by simp
      _ = 0 := by simp [subhom, hxy]
  ext n
  have hcoeffzero : ∀ n, (PowerSeries.coeff n) (x - y) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      have h := algHom_coeff_eq_sum subhom n (x - y)
      rw [hX] at h
      have hsum :
          ∑ i ∈ Finset.range (n + 1),
            (PowerSeries.coeff i) (x - y) * (PowerSeries.coeff n) (w ^ i) = 0 := by
        calc
          ∑ i ∈ Finset.range (n + 1),
              (PowerSeries.coeff i) (x - y) * (PowerSeries.coeff n) (w ^ i)
              = (PowerSeries.coeff n) (subhom (x - y)) := h.symm
          _ = 0 := by rw [hd]; simp
      have hprev :
          (∑ i ∈ Finset.range n,
            (PowerSeries.coeff i) (x - y) * (PowerSeries.coeff n) (w ^ i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hn : i < n := Finset.mem_range.mp hi
        rw [ih i hn]
        simp
      have hlast :
          (PowerSeries.coeff n) (x - y) * ((PowerSeries.coeff 1) w) ^ n = 0 := by
        have hs := hsum
        rw [Finset.sum_range_succ, hprev, coeff_self_pow_eq_coeff_one_pow n h0 h1] at hs
        simpa using hs
      exact (mul_eq_zero.mp hlast).resolve_right (pow_ne_zero n h1)
  have hn := hcoeffzero n
  simpa [sub_eq_zero] using hn

noncomputable def substAlgEquivOfConstantCoeffZero {w : PS}
    (h0 : PowerSeries.constantCoeff w = 0)
    (h1 : (PowerSeries.coeff 1) w ≠ 0) : PS ≃ₐ[ℂ] PS :=
  AlgEquiv.ofBijective
    (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' h0) :
      PS →ₐ[ℂ] PS)
    ⟨substAlgHom_injective_of_constantCoeff_zero h0 h1,
      substAlgHom_surjective_of_constantCoeff_zero h0 h1⟩

/- accepted add_to_file helper 14 -/
lemma algHom_ext_of_X {φ ψ : PS →ₐ[ℂ] PS}
    (hX : φ PowerSeries.X = ψ PowerSeries.X) : φ = ψ := by
  ext f n
  rw [algHom_coeff_eq_sum φ n f, algHom_coeff_eq_sum ψ n f, hX]

lemma algEquiv_ext_of_X {ρ σ : PS ≃ₐ[ℂ] PS}
    (hX : ρ PowerSeries.X = σ PowerSeries.X) : ρ = σ := by
  apply AlgEquiv.ext
  intro f
  have h : ρ.toAlgHom = σ.toAlgHom := algHom_ext_of_X hX
  exact congrFun (congrArg (⇑) h) f

/- accepted add_to_file helper 15 -/
lemma algEquiv_order_X (ψ : PS ≃ₐ[ℂ] PS) :
    (ψ PowerSeries.X).order = 1 :=
  order_eq_one_of_constantCoeff_zero (algEquiv_constantCoeff_X ψ)
    (algEquiv_coeff_one_X_ne_zero ψ)

/- accepted add_to_file helper 16 -/
lemma expand_order_algEquiv_X {N : ℕ} (hN : N ≠ 0) (ψ : PS ≃ₐ[ℂ] PS) :
    ((PowerSeries.expand N hN) (ψ PowerSeries.X)).order = N := by
  rw [PowerSeries.order_expand, algEquiv_order_X]
  simp

/- accepted add_to_file helper 17 -/
lemma exists_lift_algEquiv_expand {N : ℕ} (hN : 0 < N) (ψ : PS ≃ₐ[ℂ] PS) :
    ∃ σ : PS ≃ₐ[ℂ] PS,
      (∀ f : PS, σ ((PowerSeries.expand N (Nat.ne_of_gt hN)) f) =
        (PowerSeries.expand N (Nat.ne_of_gt hN)) (ψ f)) := by
  classical
  let e : PS →ₐ[ℂ] PS := PowerSeries.expand N (Nat.ne_of_gt hN)
  let q : PS := e (ψ PowerSeries.X)
  have horderq : q.order = N := by
    dsimp [q, e]
    exact expand_order_algEquiv_X (Nat.ne_of_gt hN) ψ
  have hdiv : (PowerSeries.X : PS) ^ N ∣ q := by
    have h := PowerSeries.X_pow_order_dvd (φ := q)
    have hto : q.order.toNat = N := by
      rw [horderq]
      rfl
    rwa [hto] at h
  rcases hdiv with ⟨u, hu⟩
  have huconst : PowerSeries.constantCoeff u ≠ 0 := by
    intro hzero
    have hqN : (PowerSeries.coeff N) q = 0 := by
      calc
        (PowerSeries.coeff N) q = (PowerSeries.coeff N) ((PowerSeries.X : PS) ^ N * u) := by
          rw [hu]
        _ = (PowerSeries.coeff 0) u := by
          convert PowerSeries.coeff_X_pow_mul u N 0 using 2
          simp
        _ = PowerSeries.constantCoeff u := by
          rw [PowerSeries.coeff_zero_eq_constantCoeff]
        _ = 0 := hzero
    have hlead : (PowerSeries.coeff N) q = (PowerSeries.coeff 1) (ψ PowerSeries.X) := by
      dsimp [q, e]
      rw [PowerSeries.coeff_expand]
      have hdivN : N / N = 1 := Nat.div_self hN
      simp [hdivN]
    have hnon := algEquiv_coeff_one_X_ne_zero ψ
    exact hnon (hlead ▸ hqN)
  obtain ⟨r, hr⟩ := exists_pow_eq_of_constantCoeff_ne_zero hN u huconst
  have hrconst : PowerSeries.constantCoeff r ≠ 0 := by
    intro hzero
    apply huconst
    calc
      PowerSeries.constantCoeff u = PowerSeries.constantCoeff (r ^ N) := by rw [← hr]
      _ = (PowerSeries.constantCoeff r) ^ N := by simp
      _ = 0 := by rw [hzero, zero_pow (Nat.ne_of_gt hN)]
  let w : PS := PowerSeries.X * r
  have hw0 : PowerSeries.constantCoeff w = 0 := by
    simp [w]
  have hw1 : (PowerSeries.coeff 1) w ≠ 0 := by
    have hcoeff : (PowerSeries.coeff 1) w = PowerSeries.constantCoeff r := by
      calc
        (PowerSeries.coeff 1) w = (PowerSeries.coeff 1) (r * (PowerSeries.X : PS) ^ 1) := by
          simp [w, mul_comm]
        _ = (PowerSeries.coeff 0) r := by
          convert PowerSeries.coeff_mul_X_pow r 1 0 using 2
        _ = PowerSeries.constantCoeff r := by
          rw [PowerSeries.coeff_zero_eq_constantCoeff]
    rw [hcoeff]
    exact hrconst
  let σ : PS ≃ₐ[ℂ] PS := substAlgEquivOfConstantCoeffZero hw0 hw1
  have hσX : σ PowerSeries.X = w := by
    change (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' hw0) :
      PS →ₐ[ℂ] PS) PowerSeries.X = w
    rw [PowerSeries.coe_substAlgHom]
    exact PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hw0)
  have hwN : w ^ N = q := by
    calc
      w ^ N = ((PowerSeries.X : PS) * r) ^ N := rfl
      _ = (PowerSeries.X : PS) ^ N * r ^ N := by rw [mul_pow]
      _ = (PowerSeries.X : PS) ^ N * u := by rw [hr]
      _ = q := hu.symm
  refine ⟨σ, ?_⟩
  intro f
  have hcomp : σ.toAlgHom.comp e = e.comp ψ.toAlgHom := by
    apply algHom_ext_of_X
    calc
      (σ.toAlgHom.comp e) PowerSeries.X = σ (e PowerSeries.X) := rfl
      _ = σ ((PowerSeries.X : PS) ^ N) := by
        rw [show e PowerSeries.X = (PowerSeries.X : PS) ^ N by
          dsimp [e]
          exact PowerSeries.expand_X N (Nat.ne_of_gt hN)]
      _ = (σ PowerSeries.X) ^ N := by simp
      _ = w ^ N := by rw [hσX]
      _ = q := hwN
      _ = (e.comp ψ.toAlgHom) PowerSeries.X := rfl
  calc
    σ (e f) = (σ.toAlgHom.comp e) f := rfl
    _ = (e.comp ψ.toAlgHom) f := by rw [hcomp]
    _ = e (ψ f) := rfl

/- accepted add_to_file helper 18 -/
lemma image_range_expand_eq_of_lift {N : ℕ} (hN : 0 < N)
    (σ ψ : PS ≃ₐ[ℂ] PS)
    (hcomm : ∀ f : PS, σ ((PowerSeries.expand N (Nat.ne_of_gt hN)) f) =
      (PowerSeries.expand N (Nat.ne_of_gt hN)) (ψ f)) :
    (σ : PS → PS) '' Set.range (PowerSeries.expand N (Nat.ne_of_gt hN) : PS →ₐ[ℂ] PS) =
      Set.range (PowerSeries.expand N (Nat.ne_of_gt hN) : PS →ₐ[ℂ] PS) := by
  let e : PS →ₐ[ℂ] PS := PowerSeries.expand N (Nat.ne_of_gt hN)
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩
    rcases hx with ⟨f, rfl⟩
    exact ⟨ψ f, (hcomm f).symm⟩
  · intro hy
    rcases hy with ⟨f, rfl⟩
    refine ⟨e (ψ.symm f), ⟨ψ.symm f, rfl⟩, ?_⟩
    calc
      σ (e (ψ.symm f)) = e (ψ (ψ.symm f)) := hcomm _
      _ = e f := by simp

/- accepted add_to_file helper 19 -/
lemma restrictExpandMonoidHom_lift {N : ℕ} (hN : 0 < N)
    (σ ψ : PS ≃ₐ[ℂ] PS)
    (hcomm : ∀ f : PS, σ ((PowerSeries.expand N (Nat.ne_of_gt hN)) f) =
      (PowerSeries.expand N (Nat.ne_of_gt hN)) (ψ f)) :
    ((restrictExpandMonoidHom (Nat.ne_of_gt hN)
      ⟨σ, image_range_expand_eq_of_lift hN σ ψ hcomm⟩ :
        (⊤ : Subgroup (PS ≃ₐ[ℂ] PS))).1 : PS ≃ₐ[ℂ] PS) = ψ := by
  apply AlgEquiv.ext
  intro f
  apply expand_injective (Nat.ne_of_gt hN)
  calc
    (PowerSeries.expand N (Nat.ne_of_gt hN))
        (((restrictExpandMonoidHom (Nat.ne_of_gt hN)
          ⟨σ, image_range_expand_eq_of_lift hN σ ψ hcomm⟩ :
            (⊤ : Subgroup (PS ≃ₐ[ℂ] PS))).1 : PS ≃ₐ[ℂ] PS) f)
        = σ ((PowerSeries.expand N (Nat.ne_of_gt hN)) f) := by
          exact restrictExpandEquiv_spec _ _ _ f
    _ = (PowerSeries.expand N (Nat.ne_of_gt hN)) (ψ f) := hcomm f

/- accepted add_to_file helper 20 -/
lemma eq_one_of_pow_eq_one_of_constantCoeff_eq_one {N : ℕ} (hN : 0 < N) {u : PS}
    (huN : u ^ N = 1) (hu0 : PowerSeries.constantCoeff u = 1) : u = 1 := by
  have hfac : (u - 1) * ∑ i ∈ Finset.range N, u ^ i = 0 := by
    calc
      (u - 1) * ∑ i ∈ Finset.range N, u ^ i = u ^ N - 1 := mul_geom_sum u N
      _ = 0 := by rw [huN, sub_self]
  have hsum_ne : ∑ i ∈ Finset.range N, u ^ i ≠ 0 := by
    intro hzero
    have hconst : PowerSeries.constantCoeff (∑ i ∈ Finset.range N, u ^ i) = N := by
      simp [map_sum, map_pow, hu0]
    have hNzero : (N : ℂ) = 0 := by
      calc
        (N : ℂ) = PowerSeries.constantCoeff (∑ i ∈ Finset.range N, u ^ i) := by
          simp [hconst]
        _ = 0 := by rw [hzero]; simp
    exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)) hNzero
  have hsub : u - 1 = 0 := (mul_eq_zero.mp hfac).resolve_right hsum_ne
  exact sub_eq_zero.mp hsub

/- accepted add_to_file helper 21 -/
lemma coeff_one_ne_zero_of_pow_eq_X_pow {N : ℕ} (hN : 0 < N) {v : PS}
    (h0 : PowerSeries.constantCoeff v = 0) (hv : v ^ N = (PowerSeries.X : PS) ^ N) :
    (PowerSeries.coeff 1) v ≠ 0 := by
  intro h1
  have hX2 : (PowerSeries.X : PS) ^ 2 ∣ v := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · simpa [PowerSeries.coeff_zero_eq_constantCoeff] using h0
    · exact h1
  have hpow : (PowerSeries.X : PS) ^ (2 * N) ∣ v ^ N := by
    have h := pow_dvd_pow_of_dvd hX2 N
    simpa [pow_mul] using h
  have hXN : (PowerSeries.X : PS) ^ (N + 1) ∣ (PowerSeries.X : PS) ^ N := by
    have hs : (PowerSeries.X : PS) ^ (N + 1) ∣ (PowerSeries.X : PS) ^ (2 * N) := by
      apply pow_dvd_pow
      omega
    have ht : (PowerSeries.X : PS) ^ (2 * N) ∣ (PowerSeries.X : PS) ^ N := by
      rw [← hv]
      exact hpow
    exact hs.trans ht
  have hcoeff : (PowerSeries.coeff N) ((PowerSeries.X : PS) ^ N) = 0 :=
    (PowerSeries.X_pow_dvd_iff.mp hXN) N (Nat.lt_succ_self N)
  have hone : (PowerSeries.coeff N) ((PowerSeries.X : PS) ^ N) = 1 := by
    simp
  rw [hone] at hcoeff
  exact one_ne_zero hcoeff

/- accepted add_to_file helper 22 -/
lemma constantCoeff_divXPowOrder_of_order_eq_one {w : PS}
    (horder : w.order = 1) :
    PowerSeries.constantCoeff w.divXPowOrder = (PowerSeries.coeff 1) w := by
  have hdecw : PowerSeries.X ^ 1 * w.divXPowOrder = w := by
    have h := PowerSeries.X_pow_order_mul_divXPowOrder (f := w)
    rwa [horder] at h
  calc
    PowerSeries.constantCoeff w.divXPowOrder
        = (PowerSeries.coeff 0) w.divXPowOrder := by
            rw [PowerSeries.coeff_zero_eq_constantCoeff]
    _ = (PowerSeries.coeff (0 + 1)) (PowerSeries.X ^ 1 * w.divXPowOrder) := by
            rw [PowerSeries.coeff_X_pow_mul]
    _ = (PowerSeries.coeff 1) w := by
            rw [hdecw]

/- accepted add_to_file helper 23 -/
lemma exists_root_of_pow_eq_X_pow {N : ℕ} (hN : 0 < N) {v : PS}
    (h0 : PowerSeries.constantCoeff v = 0) (hv : v ^ N = (PowerSeries.X : PS) ^ N) :
    ∃ ε : rootsOfUnity N ℂ,
      v = algebraMap ℂ PS (((ε : ℂˣ) : ℂ)) * PowerSeries.X := by
  let a : ℂ := (PowerSeries.coeff 1) v
  have ha0 : a ≠ 0 := coeff_one_ne_zero_of_pow_eq_X_pow hN h0 hv
  have haN : a ^ N = 1 := by
    have hc := congrArg (PowerSeries.coeff N) hv
    rw [coeff_self_pow_eq_coeff_one_pow N h0 ha0] at hc
    simpa [a] using hc
  let εu : ℂˣ := Units.ofPowEqOne a N haN (Nat.ne_of_gt hN)
  have hεmem : εu ∈ rootsOfUnity N ℂ := by
    simp [rootsOfUnity, εu]
  let ε : rootsOfUnity N ℂ := ⟨εu, hεmem⟩
  have hεval : (((ε : ℂˣ) : ℂ)) = a := by
    simp [ε, εu]
  refine ⟨ε, ?_⟩
  let t : PS := PowerSeries.C a⁻¹ * v
  have htN : t ^ N = (PowerSeries.X : PS) ^ N := by
    calc
      t ^ N = (PowerSeries.C a⁻¹) ^ N * v ^ N := by
        dsimp [t]
        rw [mul_pow]
      _ = PowerSeries.C ((a⁻¹) ^ N) * (PowerSeries.X : PS) ^ N := by
        rw [hv]
        congr 1
        rw [← map_pow, inv_pow]
      _ = (PowerSeries.X : PS) ^ N := by
        rw [inv_pow, haN, inv_one, map_one, one_mul]
  have ht0 : PowerSeries.constantCoeff t = 0 := by
    simp [t, h0]
  have ht1 : (PowerSeries.coeff 1) t = 1 := by
    calc
      (PowerSeries.coeff 1) t = a⁻¹ * a := by simp [t, a]
      _ = 1 := inv_mul_cancel₀ ha0
  have htorder : t.order = 1 := by
    apply order_eq_one_of_constantCoeff_zero ht0
    rw [ht1]
    exact one_ne_zero
  let u : PS := t.divXPowOrder
  have htdecomp : (PowerSeries.X : PS) * u = t := by
    have h := PowerSeries.X_pow_order_mul_divXPowOrder (f := t)
    rw [htorder] at h
    simpa [u] using h
  have huN : u ^ N = 1 := by
    have hmul : (PowerSeries.X : PS) ^ N * u ^ N = (PowerSeries.X : PS) ^ N * 1 := by
      calc
        (PowerSeries.X : PS) ^ N * u ^ N = ((PowerSeries.X : PS) * u) ^ N := by
          rw [mul_pow]
        _ = t ^ N := by rw [htdecomp]
        _ = (PowerSeries.X : PS) ^ N := htN
        _ = (PowerSeries.X : PS) ^ N * 1 := by simp
    have hXne : (PowerSeries.X : PS) ^ N ≠ 0 := by simp
    exact mul_left_cancel₀ hXne hmul
  have hu0 : PowerSeries.constantCoeff u = 1 := by
    calc
      PowerSeries.constantCoeff u = (PowerSeries.coeff 1) t := by
        dsimp [u]
        exact constantCoeff_divXPowOrder_of_order_eq_one htorder
      _ = 1 := ht1
  have hu : u = 1 := eq_one_of_pow_eq_one_of_constantCoeff_eq_one hN huN hu0
  have htX : t = PowerSeries.X := by
    calc
      t = (PowerSeries.X : PS) * u := htdecomp.symm
      _ = PowerSeries.X := by rw [hu, mul_one]
  calc
    v = PowerSeries.C a * t := by
      dsimp [t]
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha0, map_one, one_mul]
    _ = PowerSeries.C a * PowerSeries.X := by rw [htX]
    _ = algebraMap ℂ PS (((ε : ℂˣ) : ℂ)) * PowerSeries.X := by
      rw [hεval, PowerSeries.C_eq_algebraMap]

/- accepted add_to_file helper 24 -/
noncomputable def rootScaleAlgEquiv {N : ℕ} (ε : rootsOfUnity N ℂ) : PS ≃ₐ[ℂ] PS :=
  let a : ℂ := ((ε : ℂˣ) : ℂ)
  substAlgEquivOfConstantCoeffZero (w := algebraMap ℂ PS a * PowerSeries.X)
    (by simp)
    (by
      have ha : a ≠ 0 := Units.ne_zero _
      simpa [a] using ha)

lemma rootScaleAlgEquiv_X {N : ℕ} (ε : rootsOfUnity N ℂ) :
    (rootScaleAlgEquiv ε) PowerSeries.X =
      algebraMap ℂ PS (((ε : ℂˣ) : ℂ)) * PowerSeries.X := by
  let a : ℂ := ((ε : ℂˣ) : ℂ)
  have h0 : PowerSeries.constantCoeff (algebraMap ℂ PS a * PowerSeries.X) = 0 := by
    simp
  change (PowerSeries.substAlgHom
      (PowerSeries.HasSubst.of_constantCoeff_zero' h0) :
      PS →ₐ[ℂ] PS) PowerSeries.X = _
  rw [PowerSeries.coe_substAlgHom]
  exact PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' h0)

/- accepted add_to_file helper 25 -/
lemma rootScaleAlgEquiv_expand {N : ℕ} (hN : 0 < N) (ε : rootsOfUnity N ℂ)
    (f : PS) :
    (rootScaleAlgEquiv ε) ((PowerSeries.expand N (Nat.ne_of_gt hN)) f) =
      (PowerSeries.expand N (Nat.ne_of_gt hN)) f := by
  let e : PS →ₐ[ℂ] PS := PowerSeries.expand N (Nat.ne_of_gt hN)
  have hcomp : (rootScaleAlgEquiv ε).toAlgHom.comp e = e := by
    apply algHom_ext_of_X
    calc
      ((rootScaleAlgEquiv ε).toAlgHom.comp e) PowerSeries.X
          = (rootScaleAlgEquiv ε) (e PowerSeries.X) := rfl
      _ = (rootScaleAlgEquiv ε) ((PowerSeries.X : PS) ^ N) := by
        rw [show e PowerSeries.X = (PowerSeries.X : PS) ^ N by
          dsimp [e]
          exact PowerSeries.expand_X N (Nat.ne_of_gt hN)]
      _ = ((rootScaleAlgEquiv ε) PowerSeries.X) ^ N := by simp
      _ = (algebraMap ℂ PS (((ε : ℂˣ) : ℂ)) * PowerSeries.X) ^ N := by
        rw [rootScaleAlgEquiv_X]
      _ = (PowerSeries.X : PS) ^ N := by
        have hu : (ε : ℂˣ) ^ N = 1 := ε.2
        have hroot : ((((ε : ℂˣ) : ℂ)) ^ N) = 1 := by
          have hv := congrArg Units.val hu
          simpa using hv
        calc
          (algebraMap ℂ PS (((ε : ℂˣ) : ℂ)) * PowerSeries.X) ^ N
              = (algebraMap ℂ PS (((ε : ℂˣ) : ℂ))) ^ N * PowerSeries.X ^ N := by
                  rw [mul_pow]
          _ = algebraMap ℂ PS ((((ε : ℂˣ) : ℂ)) ^ N) * PowerSeries.X ^ N := by
                  simp
          _ = (PowerSeries.X : PS) ^ N := by rw [hroot, map_one, one_mul]
      _ = e PowerSeries.X := by
        rw [show e PowerSeries.X = (PowerSeries.X : PS) ^ N by
          dsimp [e]
          exact PowerSeries.expand_X N (Nat.ne_of_gt hN)]
  calc
    (rootScaleAlgEquiv ε) (e f) = ((rootScaleAlgEquiv ε).toAlgHom.comp e) f := rfl
    _ = e f := by rw [hcomp]

/- accepted add_to_file helper 26 -/
noncomputable def rootScaleMonoidHom {N : ℕ} (hN : 0 < N) :
    rootsOfUnity N ℂ →*
      preservingSubgroup (Set.range (PowerSeries.expand N (Nat.ne_of_gt hN) : PS →ₐ[ℂ] PS)) where
  toFun ε :=
    ⟨rootScaleAlgEquiv ε,
      image_range_expand_eq_of_lift hN (rootScaleAlgEquiv ε) 1 (fun f => by
        simpa using rootScaleAlgEquiv_expand hN ε f)⟩
  map_one' := by
    apply Subtype.ext
    apply algEquiv_ext_of_X
    rw [rootScaleAlgEquiv_X]
    simp
  map_mul' := by
    intro ε δ
    apply Subtype.ext
    apply algEquiv_ext_of_X
    calc
      (rootScaleAlgEquiv (ε * δ)) PowerSeries.X
          = algebraMap ℂ PS ((((ε * δ : rootsOfUnity N ℂ) : ℂˣ) : ℂ)) * PowerSeries.X :=
            rootScaleAlgEquiv_X _
      _ = algebraMap ℂ PS (((ε : ℂˣ) : ℂ) * ((δ : ℂˣ) : ℂ)) * PowerSeries.X := by
            congr 2
      _ = (rootScaleAlgEquiv ε) ((rootScaleAlgEquiv δ) PowerSeries.X) := by
            rw [rootScaleAlgEquiv_X]
            calc
              algebraMap ℂ PS (((ε : ℂˣ) : ℂ) * ((δ : ℂˣ) : ℂ)) * PowerSeries.X
                  = (algebraMap ℂ PS (((ε : ℂˣ) : ℂ)) *
                      algebraMap ℂ PS (((δ : ℂˣ) : ℂ))) * PowerSeries.X := by
                      rw [map_mul]
              _ = algebraMap ℂ PS (((δ : ℂˣ) : ℂ)) *
                    (algebraMap ℂ PS (((ε : ℂˣ) : ℂ)) * PowerSeries.X) := by
                    ring
              _ = (rootScaleAlgEquiv ε)
                    (algebraMap ℂ PS (((δ : ℂˣ) : ℂ)) * PowerSeries.X) := by
                    rw [map_mul]
                    have hC : (rootScaleAlgEquiv ε)
                        ((algebraMap ℂ PS) (((δ : ℂˣ) : ℂ))) =
                      (algebraMap ℂ PS) (((δ : ℂˣ) : ℂ)) :=
                      (rootScaleAlgEquiv ε).commutes _
                    rw [hC, rootScaleAlgEquiv_X]
      _ = ((rootScaleAlgEquiv ε * rootScaleAlgEquiv δ : PS ≃ₐ[ℂ] PS)) PowerSeries.X := by
            rw [AlgEquiv.mul_apply]

/- accepted add_to_file helper 27 -/
lemma rootScaleMonoidHom_injective {N : ℕ} (hN : 0 < N) :
    Function.Injective (rootScaleMonoidHom hN) := by
  intro ε δ h
  have hX := congrArg (fun ρ :
      preservingSubgroup (Set.range (PowerSeries.expand N (Nat.ne_of_gt hN) : PS →ₐ[ℂ] PS)) =>
      (ρ.1 : PS ≃ₐ[ℂ] PS) PowerSeries.X) h
  change (rootScaleAlgEquiv ε) PowerSeries.X = (rootScaleAlgEquiv δ) PowerSeries.X at hX
  rw [rootScaleAlgEquiv_X, rootScaleAlgEquiv_X] at hX
  have hcoeff := congrArg (PowerSeries.coeff 1) hX
  simp at hcoeff
  apply Subtype.ext
  apply Units.ext
  exact hcoeff

/- accepted add_to_file helper 28 -/
lemma restrictExpandMonoidHom_rootScale {N : ℕ} (hN : 0 < N)
    (ε : rootsOfUnity N ℂ) :
    (restrictExpandMonoidHom (Nat.ne_of_gt hN)) ((rootScaleMonoidHom hN) ε) = 1 := by
  have h := restrictExpandMonoidHom_lift hN (rootScaleAlgEquiv ε) 1 (fun f => by
    simpa using rootScaleAlgEquiv_expand hN ε f)
  apply Subtype.ext
  exact h

/- accepted add_to_file helper 29 -/
lemma rootScaleMonoidHom_range_eq_restrictExpandMonoidHom_ker {N : ℕ} (hN : 0 < N) :
    (rootScaleMonoidHom hN).range =
      (restrictExpandMonoidHom (Nat.ne_of_gt hN)).ker := by
  apply le_antisymm
  · intro ρ hρ
    rcases hρ with ⟨ε, rfl⟩
    exact restrictExpandMonoidHom_rootScale hN ε
  · intro ρ hρ
    have hunder :
        (((restrictExpandMonoidHom (Nat.ne_of_gt hN)) ρ).1 :
          PS ≃ₐ[ℂ] PS) = 1 :=
      congrArg Subtype.val hρ
    let e : PS →ₐ[ℂ] PS := PowerSeries.expand N (Nat.ne_of_gt hN)
    have hspec := restrictExpandEquiv_spec (Nat.ne_of_gt hN) ρ.1 ρ.2 PowerSeries.X
    have hpow : (ρ.1 PowerSeries.X) ^ N = (PowerSeries.X : PS) ^ N := by
      calc
        (ρ.1 PowerSeries.X) ^ N = ρ.1 ((PowerSeries.X : PS) ^ N) := by simp
        _ = ρ.1 (e PowerSeries.X) := by
          rw [show e PowerSeries.X = (PowerSeries.X : PS) ^ N by
            dsimp [e]
            exact PowerSeries.expand_X N (Nat.ne_of_gt hN)]
        _ = e ((((restrictExpandMonoidHom (Nat.ne_of_gt hN)) ρ).1 :
            PS ≃ₐ[ℂ] PS) PowerSeries.X) := by
          dsimp [e] at hspec ⊢
          exact hspec.symm
        _ = e PowerSeries.X := by rw [hunder]; simp
        _ = (PowerSeries.X : PS) ^ N := by
          dsimp [e]
          exact PowerSeries.expand_X N (Nat.ne_of_gt hN)
    have h0 := algEquiv_constantCoeff_X ρ.1
    obtain ⟨ε, hε⟩ := exists_root_of_pow_eq_X_pow hN h0 hpow
    refine ⟨ε, ?_⟩
    apply Subtype.ext
    apply algEquiv_ext_of_X
    calc
      ((rootScaleMonoidHom hN) ε).1 PowerSeries.X =
          algebraMap ℂ PS (((ε : ℂˣ) : ℂ)) * PowerSeries.X := by
            change (rootScaleAlgEquiv ε) PowerSeries.X = _
            exact rootScaleAlgEquiv_X ε
      _ = ρ.1 PowerSeries.X := hε.symm

/- accepted add_to_file helper 30 -/
lemma algEquiv_coeff_one_mul_X (ρ σ : PS ≃ₐ[ℂ] PS) :
    (PowerSeries.coeff 1) ((ρ * σ) PowerSeries.X) =
      (PowerSeries.coeff 1) (ρ PowerSeries.X) *
        (PowerSeries.coeff 1) (σ PowerSeries.X) := by
  have h := algHom_coeff_eq_sum ρ.toAlgHom 1 (σ PowerSeries.X)
  have h0 := algEquiv_constantCoeff_X σ
  calc
    (PowerSeries.coeff 1) ((ρ * σ) PowerSeries.X)
        = (PowerSeries.coeff 1) (ρ (σ PowerSeries.X)) := by
          rw [AlgEquiv.mul_apply]
    _ = ∑ i ∈ Finset.range 2,
        (PowerSeries.coeff i) (σ PowerSeries.X) *
          (PowerSeries.coeff 1) ((ρ PowerSeries.X) ^ i) := by
          simpa using h
    _ = (PowerSeries.coeff 1) (ρ PowerSeries.X) *
        (PowerSeries.coeff 1) (σ PowerSeries.X) := by
          simp [Finset.sum_range_succ, h0, mul_comm]

noncomputable def algEquivLeadingUnit (ρ : PS ≃ₐ[ℂ] PS) : ℂˣ where
  val := (PowerSeries.coeff 1) (ρ PowerSeries.X)
  inv := (PowerSeries.coeff 1) (ρ.symm PowerSeries.X)
  val_inv := by
    have h := algEquiv_coeff_one_mul_X ρ ρ.symm
    rw [← h]
    simp
  inv_val := by
    have h := algEquiv_coeff_one_mul_X ρ.symm ρ
    rw [← h]
    simp

/- accepted add_to_file helper 31 -/
noncomputable def algEquivLeadingMonoidHom : (PS ≃ₐ[ℂ] PS) →* ℂˣ where
  toFun := algEquivLeadingUnit
  map_one' := by
    apply Units.ext
    simp [algEquivLeadingUnit]
  map_mul' := by
    intro ρ σ
    apply Units.ext
    change (PowerSeries.coeff 1) ((ρ * σ) PowerSeries.X) =
      (PowerSeries.coeff 1) (ρ PowerSeries.X) *
        (PowerSeries.coeff 1) (σ PowerSeries.X)
    exact algEquiv_coeff_one_mul_X ρ σ

/- accepted add_to_file helper 32 -/
lemma algEquivLeadingMonoidHom_rootScale {N : ℕ} (ε : rootsOfUnity N ℂ) :
    algEquivLeadingMonoidHom (rootScaleAlgEquiv ε) = (ε : ℂˣ) := by
  apply Units.ext
  change (PowerSeries.coeff 1) ((rootScaleAlgEquiv ε) PowerSeries.X) =
    (((ε : ℂˣ) : ℂ))
  rw [rootScaleAlgEquiv_X]
  simp

/- accepted add_to_file helper 33 -/
lemma rootScaleMonoidHom_range_le_center {N : ℕ} (hN : 0 < N) :
    (rootScaleMonoidHom hN).range ≤
      Subgroup.center
        (preservingSubgroup (Set.range (PowerSeries.expand N (Nat.ne_of_gt hN) :
          PS →ₐ[ℂ] PS))) := by
  intro x hx
  rcases hx with ⟨ε, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  let D := preservingSubgroup (Set.range (PowerSeries.expand N (Nat.ne_of_gt hN) :
    PS →ₐ[ℂ] PS))
  let a : D := (rootScaleMonoidHom hN) ε
  let τ : D := a * y * a⁻¹ * y⁻¹
  let μ : D →* (⊤ : Subgroup (PS ≃ₐ[ℂ] PS)) := restrictExpandMonoidHom (Nat.ne_of_gt hN)
  have hker : τ ∈ μ.ker := by
    rw [MonoidHom.mem_ker]
    have hcalc : μ τ = μ a * μ y * (μ a)⁻¹ * (μ y)⁻¹ := by
      dsimp [τ]
      rw [μ.map_mul, μ.map_mul, μ.map_mul, μ.map_inv, μ.map_inv]
    have haμ : μ a = 1 := restrictExpandMonoidHom_rootScale hN ε
    rw [hcalc, haμ]
    simp
  let L : (PS ≃ₐ[ℂ] PS) →* ℂˣ := algEquivLeadingMonoidHom
  have hleadcalc :
      L (τ.1 : PS ≃ₐ[ℂ] PS) =
        L (a.1 : PS ≃ₐ[ℂ] PS) * L (y.1 : PS ≃ₐ[ℂ] PS) *
          (L (a.1 : PS ≃ₐ[ℂ] PS))⁻¹ * (L (y.1 : PS ≃ₐ[ℂ] PS))⁻¹ := by
    dsimp [τ]
    rw [L.map_mul, L.map_mul, L.map_mul, L.map_inv, L.map_inv]
  have hlead : L (τ.1 : PS ≃ₐ[ℂ] PS) = 1 := by
    have ha : L (a.1 : PS ≃ₐ[ℂ] PS) = (ε : ℂˣ) := by
      change L (rootScaleAlgEquiv ε) = (ε : ℂˣ)
      exact algEquivLeadingMonoidHom_rootScale ε
    rw [hleadcalc, ha]
    simp
  have hrange : τ ∈ (rootScaleMonoidHom hN).range := by
    rw [rootScaleMonoidHom_range_eq_restrictExpandMonoidHom_ker hN]
    exact hker
  rcases hrange with ⟨δ, hδ⟩
  have hδunit : (δ : ℂˣ) = 1 := by
    calc
      (δ : ℂˣ) = L ((rootScaleAlgEquiv δ) : PS ≃ₐ[ℂ] PS) :=
        (algEquivLeadingMonoidHom_rootScale δ).symm
      _ = L (τ.1 : PS ≃ₐ[ℂ] PS) := by
        rw [← hδ]
        rfl
      _ = 1 := hlead
  have hδroot : δ = 1 := by
    apply Subtype.ext
    exact hδunit
  have hτ : τ = 1 := by
    rw [← hδ, hδroot, map_one]
  have hconj : a * y * a⁻¹ = y := by
    have h := congrArg (· * y) hτ
    simpa [τ, mul_assoc] using h
  have hcomm : a * y = y * a := by
    have h := congrArg (· * a) hconj
    simpa [mul_assoc] using h
  calc
    y * (rootScaleMonoidHom hN) ε = y * a := by rfl
    _ = a * y := hcomm.symm
    _ = (rootScaleMonoidHom hN) ε * y := by rfl

/- accepted add_to_file helper 34 -/
end FPSAut

open FPSAut

/- verified submission -/
theorem formalPowerSeries_automorphism_exact_sequence (N : ℕ) (hN : 2 ≤ N) :
  let A := PowerSeries ℂ
  let _ : TopologicalSpace A :=
    PowerSeries.WithPiTopology.instTopologicalSpace ℂ
  let e : A →ₐ[ℂ] A :=
    PowerSeries.expand N (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hN))
  let G := A ≃ₐ[ℂ] A
  let S : Set A := Set.range e
  ∃ (Aut : Subgroup G) (AutN : Subgroup G),
    (∀ ρ : G, ρ ∈ Aut ↔
      Continuous (ρ : A → A) ∧ Continuous (ρ.symm : A → A)) ∧
    (∀ ρ : G, ρ ∈ AutN ↔
      Continuous (ρ : A → A) ∧ Continuous (ρ.symm : A → A) ∧ ρ '' S = S) ∧
    ∃ (ι : rootsOfUnity N ℂ →* AutN) (μ : AutN →* Aut),
      (∀ (ρ : AutN) (f : A), e ((μ ρ : G) f) = (ρ : G) (e f)) ∧
      (∀ ρ : AutN,
        e ((μ ρ : G) PowerSeries.X) = ((ρ : G) PowerSeries.X) ^ N) ∧
      (∀ ε : rootsOfUnity N ℂ,
        (ι ε : G) PowerSeries.X =
          algebraMap ℂ A (((ε : ℂˣ) : ℂ)) * PowerSeries.X) ∧
      Function.Injective ι ∧
      Function.Surjective μ ∧
      ι.range = μ.ker ∧
      ι.range ≤ Subgroup.center AutN := by
  classical
  let hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_two hN
  let A := PowerSeries ℂ
  let htop : TopologicalSpace A :=
    PowerSeries.WithPiTopology.instTopologicalSpace ℂ
  let e : A →ₐ[ℂ] A := PowerSeries.expand N (Nat.ne_of_gt hNpos)
  let G := A ≃ₐ[ℂ] A
  let S : Set A := Set.range e
  let Aut : Subgroup G := ⊤
  let AutN : Subgroup G := preservingSubgroup S
  refine ⟨Aut, AutN, ?_, ?_, ?_⟩
  · intro ρ
    constructor
    · intro _
      exact algEquiv_continuous ρ
    · intro _
      trivial
  · intro ρ
    constructor
    · intro hρ
      have hc := algEquiv_continuous ρ
      exact ⟨hc.1, hc.2, hρ⟩
    · intro hρ
      exact hρ.2.2
  · let ι : rootsOfUnity N ℂ →* AutN := rootScaleMonoidHom hNpos
    let μ : AutN →* Aut := restrictExpandMonoidHom (Nat.ne_of_gt hNpos)
    refine ⟨ι, μ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ρ f
      exact restrictExpandEquiv_spec (Nat.ne_of_gt hNpos) ρ.1 ρ.2 f
    · intro ρ
      calc
        e ((μ ρ : G) PowerSeries.X) = (ρ : G) (e PowerSeries.X) :=
          restrictExpandEquiv_spec (Nat.ne_of_gt hNpos) ρ.1 ρ.2 PowerSeries.X
        _ = ((ρ : G) PowerSeries.X) ^ N := by
          rw [show e PowerSeries.X = (PowerSeries.X : A) ^ N by
            dsimp [e]
            exact PowerSeries.expand_X N (Nat.ne_of_gt hNpos)]
          simp
    · intro ε
      exact rootScaleAlgEquiv_X ε
    · exact rootScaleMonoidHom_injective hNpos
    · intro y
      obtain ⟨σ, hcomm⟩ := exists_lift_algEquiv_expand hNpos (y.1 : G)
      let hmem : (σ : G) '' S = S :=
        image_range_expand_eq_of_lift hNpos σ y.1 hcomm
      refine ⟨⟨σ, hmem⟩, ?_⟩
      apply Subtype.ext
      exact restrictExpandMonoidHom_lift hNpos σ y.1 hcomm
    · exact rootScaleMonoidHom_range_eq_restrictExpandMonoidHom_ker hNpos
    · exact rootScaleMonoidHom_range_le_center hNpos

end
end Rollout_p0246_formalpowerseries_automorphism_exact_seque

#check_dependency_graph "Rollout_p0246_formalpowerseries_automorphism_exact_seque.formalPowerSeries_automorphism_exact_sequence" against "{\"edges\":[{\"conclusion\":{\"name\":\"hNpos\",\"statement\":\"0 < N\"},\"graphEdgeId\":\"h_001_hnpos\",\"premises\":[{\"name\":\"hN\",\"statement\":\"2 ≤ N\"}],\"rawEdgeId\":\"telescope_2\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∃ Aut AutN, (∀ (ρ : PowerSeries ℂ ≃ₐ[ℂ] PowerSeries ℂ), ρ ∈ Aut ↔ Continuous ⇑ρ ∧ Continuous ⇑ρ.symm) ∧ (∀ (ρ : PowerSeries ℂ ≃ₐ[ℂ] PowerSeries ℂ), ρ ∈ AutN ↔ Continuous ⇑ρ ∧ Continuous ⇑ρ.symm ∧ ⇑ρ '' Set.range ⇑(PowerSeries.expand N ⋯) = Set.range ⇑(PowerSeries.expand N ⋯)) ∧ ∃ ι μ, (∀ (ρ : ↥AutN) (f : PowerSeries ℂ), (PowerSeries.expand N ⋯) (↑(μ ρ) f) = ↑ρ ((PowerSeries.expand N ⋯) f)) ∧ (∀ (ρ : ↥AutN), (PowerSeries.expand N ⋯) (↑(μ ρ) PowerSeries.X) = ↑ρ PowerSeries.X ^ N) ∧ (∀ (ε : ↥(rootsOfUnity N ℂ)), ↑(ι ε) PowerSeries.X = (algebraMap ℂ (PowerSeries ℂ)) ↑↑ε * PowerSeries.X) ∧ Function.Injective ⇑ι ∧ Function.Surjective ⇑μ ∧ ι.range = μ.ker ∧ ι.range ≤ Subgroup.center ↥AutN\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hN\",\"statement\":\"2 ≤ N\"},{\"name\":\"hNpos\",\"statement\":\"0 < N\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0246_formalpowerseries_automorphism_exact_seque\",\"reconstructedProofSha256\":\"0dadb5df0ebc9d8016b15add1f3b7228d695024ed2a437558b2f431127081ba9\",\"selectedEdgeCount\":2,\"theoremName\":\"Rollout_p0246_formalpowerseries_automorphism_exact_seque.formalPowerSeries_automorphism_exact_sequence\",\"topologySha256\":\"8fca2d9d47864411a13fe5cf51fc66dc9cb51f610c367e248277ea0507cb00dc\"}"

namespace Rollout_p0252_reciprocal_eq_neg_one_pow_of_roots_abs_one

-- graph_id: p0252_reciprocal_eq_neg_one_pow_of_roots_abs_one
-- topology_sha256: 8135949077b0fb96d1c6fae3bccdb4227c53b9d315b1129708d80ccc0e0481f7
/- accepted add_to_file helper 1 -/

open Polynomial

lemma reverse_quadratic_unit (a : ℝ) :
    (X ^ 2 - C (2 * a) * X + C (1 : ℝ)).reverse =
      X ^ 2 - C (2 * a) * X + C (1 : ℝ) := by
  let q : Polynomial ℝ := X ^ 2 - C (2 * a) * X + C (1 : ℝ)
  have hdeg : q.natDegree = 2 := by
    dsimp [q]
    compute_degree!
  change q.reverse = q
  ext k
  rw [Polynomial.coeff_reverse, hdeg]
  by_cases hk : k ≤ 2
  · interval_cases k <;> simp [Polynomial.revAt_le, q, Polynomial.coeff_one]
  · have hkgt : 2 < k := Nat.lt_of_not_ge hk
    have hzero : q.coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      simpa [hdeg] using hkgt
    simp [Polynomial.revAt_eq_self_of_lt hkgt, hzero]

lemma reverse_X_sub_C_neg_one :
    (X - C (-1 : ℝ)).reverse = X - C (-1 : ℝ) := by
  let q : Polynomial ℝ := X - C (-1 : ℝ)
  have hdeg : q.natDegree = 1 := by
    dsimp [q]
    compute_degree!
  change q.reverse = q
  ext k
  rw [Polynomial.coeff_reverse, hdeg]
  by_cases hk : k ≤ 1
  · interval_cases k <;> simp [Polynomial.revAt_le, q, Polynomial.coeff_one]
  · have hkgt : 1 < k := Nat.lt_of_not_ge hk
    have hzero : q.coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      simpa [hdeg] using hkgt
    simp [Polynomial.revAt_eq_self_of_lt hkgt, hzero]

lemma reverse_X_sub_C_one_pow (n : ℕ) :
    ((X - C (1 : ℝ)) ^ n).reverse = ((-1 : ℝ) ^ n) • (X - C (1 : ℝ)) ^ n := by
  let A : Polynomial ℝ := X - C (1 : ℝ)
  have hbase : A.reverse = C (-1 : ℝ) * A := by
    have hdeg : A.natDegree = 1 := by
      dsimp [A]
      compute_degree!
    ext k
    rw [Polynomial.coeff_reverse, hdeg]
    by_cases hk : k ≤ 1
    · interval_cases k <;> simp [Polynomial.revAt_le, A, Polynomial.coeff_one]
    · have hkgt : 1 < k := Nat.lt_of_not_ge hk
      have hzero : A.coeff k = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        simpa [hdeg] using hkgt
      simp [Polynomial.revAt_eq_self_of_lt hkgt, hzero]
  have hrevpow : (A ^ n).reverse = A.reverse ^ n := by
    induction n with
    | zero =>
        change (C (1 : ℝ)).reverse = (C (1 : ℝ)) ^ 0
        rw [Polynomial.reverse_C]
        simp
    | succ n ih =>
        rw [pow_succ, Polynomial.reverse_mul_of_domain, ih, pow_succ]
  change (A ^ n).reverse = ((-1 : ℝ) ^ n) • A ^ n
  rw [hrevpow, hbase, mul_pow, ← map_pow, ← Polynomial.smul_eq_C_mul]

/- accepted add_to_file helper 2 -/
lemma isRoot_real_of_map_isRoot_of_im_eq_zero
    (f : Polynomial ℝ) {z : ℂ} (him : z.im = 0)
    (hz : (f.map (algebraMap ℝ ℂ)).IsRoot z) : f.IsRoot z.re := by
  let r := z.re
  have hzr : z = (r : ℂ) := by
    apply Complex.ext <;> simp [r, him]
  have hrootmap : (f.map (algebraMap ℝ ℂ)).IsRoot (r : ℂ) := by
    simpa [hzr] using hz
  rw [Polynomial.IsRoot.def, Polynomial.eval_map] at hrootmap
  have heval₂ := Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) r (p := f)
  have hmapzero : algebraMap ℝ ℂ (f.eval r) = 0 := by
    rw [show algebraMap ℝ ℂ r = (r : ℂ) by rfl] at heval₂
    exact heval₂ ▸ hrootmap
  rw [Polynomial.IsRoot.def]
  exact (RingHom.injective (algebraMap ℝ ℂ)) hmapzero

lemma aeval_eq_zero_of_map_isRoot
    (f : Polynomial ℝ) {z : ℂ}
    (hz : (f.map (algebraMap ℝ ℂ)).IsRoot z) :
    (Polynomial.aeval z) f = 0 := by
  rw [Polynomial.IsRoot.def, Polynomial.eval_map] at hz
  rw [Polynomial.aeval_def]
  exact hz

/- accepted add_to_file helper 3 -/
lemma reverse_eq_self_of_roots_norm_one_of_not_root_one
    (f : Polynomial ℝ) (hf : f ≠ 0)
    (hroots : ∀ z : ℂ, (f.map (algebraMap ℝ ℂ)).IsRoot z → ‖z‖ = 1)
    (h1 : ¬ f.IsRoot 1) :
    f.reverse = f := by
  let P : ℕ → Prop := fun n =>
    ∀ g : Polynomial ℝ, g.natDegree = n → g ≠ 0 →
      (∀ z : ℂ, (g.map (algebraMap ℝ ℂ)).IsRoot z → ‖z‖ = 1) →
      ¬ g.IsRoot 1 → g.reverse = g
  have H : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro g hdeg hg0 hgroots hg1
        by_cases hconst : g.natDegree = 0
        · rw [Polynomial.eq_C_of_natDegree_eq_zero hconst, Polynomial.reverse_C]
        · have hFdeg : (g.map (algebraMap ℝ ℂ)).degree ≠ 0 := by
            rw [Polynomial.degree_map, Polynomial.degree_eq_natDegree hg0]
            exact_mod_cast hconst
          obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hFdeg
          have hzn : ‖z‖ = 1 := hgroots z hz
          by_cases him : z.im = 0
          · have hrroot : g.IsRoot z.re :=
              isRoot_real_of_map_isRoot_of_im_eq_zero g him hz
            have habs : |z.re| = 1 := by
              have hzr : z = (z.re : ℂ) := by
                apply Complex.ext <;> simp [him]
              rw [hzr] at hzn
              simpa using hzn
            have hrneg : z.re = -1 := by
              rcases eq_or_eq_neg_of_abs_eq habs with hr | hr
              · exfalso
                exact hg1 (by rwa [hr] at hrroot)
              · exact hr
            have hdvd : X - C (-1 : ℝ) ∣ g := by
              rw [Polynomial.dvd_iff_isRoot]
              simpa [hrneg] using hrroot
            rcases hdvd with ⟨h, gh⟩
            have hh0 : h ≠ 0 := by
              intro hh
              apply hg0
              rw [gh, hh, mul_zero]
            have hroots_h : ∀ w : ℂ, (h.map (algebraMap ℝ ℂ)).IsRoot w → ‖w‖ = 1 := by
              intro w hw
              have hgw : (g.map (algebraMap ℝ ℂ)).IsRoot w := by
                rw [gh, Polynomial.map_mul]
                exact Polynomial.root_mul.2 (Or.inr hw)
              exact hgroots w hgw
            have h1_h : ¬ h.IsRoot 1 := by
              intro hh
              have hrootg : g.IsRoot 1 := by
                rw [gh]
                exact Polynomial.root_mul.2 (Or.inr hh)
              exact hg1 hrootg
            have hq0 : X - C (-1 : ℝ) ≠ 0 := (Polynomial.monic_X_sub_C _).ne_zero
            have hdegmul : g.natDegree = (X - C (-1 : ℝ)).natDegree + h.natDegree := by
              rw [gh, Polynomial.natDegree_mul hq0 hh0]
            have hqdeg : (X - C (-1 : ℝ)).natDegree = 1 := by
              compute_degree!
            have hhlt : h.natDegree < n := by
              rw [← hdeg, hdegmul, hqdeg]
              omega
            have hhrev : h.reverse = h :=
              ih h.natDegree hhlt h rfl hh0 hroots_h h1_h
            rw [gh, Polynomial.reverse_mul_of_domain, reverse_X_sub_C_neg_one, hhrev]
          · have haeval : (Polynomial.aeval z) g = 0 :=
              aeval_eq_zero_of_map_isRoot g hz
            have hdvd : X ^ 2 - C (2 * z.re) * X + C (1 : ℝ) ∣ g := by
              have h := Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero g haeval him
              have hnormsq : ‖z‖ ^ 2 = (1 : ℝ) := by
                rw [hzn]
                norm_num
              simpa [hnormsq] using h
            rcases hdvd with ⟨h, gh⟩
            have hh0 : h ≠ 0 := by
              intro hh
              apply hg0
              rw [gh, hh, mul_zero]
            have hroots_h : ∀ w : ℂ, (h.map (algebraMap ℝ ℂ)).IsRoot w → ‖w‖ = 1 := by
              intro w hw
              have hgw : (g.map (algebraMap ℝ ℂ)).IsRoot w := by
                rw [gh, Polynomial.map_mul]
                exact Polynomial.root_mul.2 (Or.inr hw)
              exact hgroots w hgw
            have h1_h : ¬ h.IsRoot 1 := by
              intro hh
              have hrootg : g.IsRoot 1 := by
                rw [gh]
                exact Polynomial.root_mul.2 (Or.inr hh)
              exact hg1 hrootg
            have hq0 : X ^ 2 - C (2 * z.re) * X + C (1 : ℝ) ≠ 0 := by
              have hdegq : (X ^ 2 - C (2 * z.re) * X + C (1 : ℝ)).natDegree = 2 := by
                compute_degree!
              intro hq
              rw [hq] at hdegq
              norm_num at hdegq
            have hdegmul : g.natDegree =
                (X ^ 2 - C (2 * z.re) * X + C (1 : ℝ)).natDegree + h.natDegree := by
              rw [gh, Polynomial.natDegree_mul hq0 hh0]
            have hqdeg : (X ^ 2 - C (2 * z.re) * X + C (1 : ℝ)).natDegree = 2 := by
              compute_degree!
            have hhlt : h.natDegree < n := by
              rw [← hdeg, hdegmul, hqdeg]
              omega
            have hhrev : h.reverse = h :=
              ih h.natDegree hhlt h rfl hh0 hroots_h h1_h
            rw [gh, Polynomial.reverse_mul_of_domain, reverse_quadratic_unit, hhrev]
  exact H f.natDegree f rfl hf hroots h1

/- verified submission -/
theorem reciprocal_eq_neg_one_pow_of_roots_abs_one
    (f : Polynomial ℝ) (n : ℕ) (hf : f ≠ 0)
    (hroots : ∀ z : ℂ, (f.map (algebraMap ℝ ℂ)).IsRoot z → ‖z‖ = 1)
    (hn : f.rootMultiplicity 1 = n) :
    f.reverse = ((-1 : ℝ) ^ n) • f := by
  let A : Polynomial ℝ := X - C (1 : ℝ)
  have hdvd : A ^ n ∣ f := by
    have h := Polynomial.pow_rootMultiplicity_dvd f (1 : ℝ)
    rwa [hn] at h
  rcases hdvd with ⟨g, hfg⟩
  have hg0 : g ≠ 0 := by
    intro hg
    apply hf
    rw [hfg, hg, mul_zero]
  have hnotg : ¬ g.IsRoot 1 := by
    intro hgroot
    have hlin : A ∣ g := by
      rw [Polynomial.dvd_iff_isRoot]
      exact hgroot
    rcases hlin with ⟨h, gh⟩
    have hbig : A ^ (n + 1) ∣ f := by
      use h
      rw [hfg, gh]
      change A ^ n * (A * h) = A ^ (n + 1) * h
      rw [pow_succ]
      ring
    have hnot := Polynomial.pow_rootMultiplicity_not_dvd hf (1 : ℝ)
    rw [hn] at hnot
    exact hnot hbig
  have hgroots : ∀ z : ℂ, (g.map (algebraMap ℝ ℂ)).IsRoot z → ‖z‖ = 1 := by
    intro z hz
    have hrootf : (f.map (algebraMap ℝ ℂ)).IsRoot z := by
      rw [hfg, Polynomial.map_mul]
      exact Polynomial.root_mul.2 (Or.inr hz)
    exact hroots z hrootf
  have hgrev : g.reverse = g :=
    reverse_eq_self_of_roots_norm_one_of_not_root_one g hg0 hgroots hnotg
  rw [hfg, Polynomial.reverse_mul_of_domain, reverse_X_sub_C_one_pow, hgrev, smul_mul_assoc]

end Rollout_p0252_reciprocal_eq_neg_one_pow_of_roots_abs_one

#check_dependency_graph "Rollout_p0252_reciprocal_eq_neg_one_pow_of_roots_abs_one.reciprocal_eq_neg_one_pow_of_roots_abs_one" against "{\"edges\":[{\"conclusion\":{\"name\":\"hdvd\",\"statement\":\"A ^ n ∣ f\"},\"graphEdgeId\":\"h_001_hdvd\",\"premises\":[{\"name\":\"hn\",\"statement\":\"Polynomial.rootMultiplicity 1 f = n\"}],\"rawEdgeId\":\"telescope_6\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"f.reverse = (-1) ^ n • f\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hf\",\"statement\":\"f ≠ 0\"},{\"name\":\"hroots\",\"statement\":\"∀ (z : ℂ), (Polynomial.map (algebraMap ℝ ℂ) f).IsRoot z → ‖z‖ = 1\"},{\"name\":\"hn\",\"statement\":\"Polynomial.rootMultiplicity 1 f = n\"},{\"name\":\"hdvd\",\"statement\":\"A ^ n ∣ f\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0252_reciprocal_eq_neg_one_pow_of_roots_abs_one\",\"reconstructedProofSha256\":\"c8d0557b1bfb53b4360e1a89f409935e1a246e1f3fbfe327c0b3d3346182f3f2\",\"selectedEdgeCount\":2,\"theoremName\":\"Rollout_p0252_reciprocal_eq_neg_one_pow_of_roots_abs_one.reciprocal_eq_neg_one_pow_of_roots_abs_one\",\"topologySha256\":\"8135949077b0fb96d1c6fae3bccdb4227c53b9d315b1129708d80ccc0e0481f7\"}"

namespace Rollout_p0256_marking_equivalence

-- graph_id: p0256_marking_equivalence
-- topology_sha256: acea382a18f4676772634e4c125bc3b8781d6f109529629ba6e047944a7af310
/- accepted add_to_file helper 1 -/

lemma exists_perm_comp_eq_of_injective {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f g : α → β) (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ σ : Equiv.Perm β, σ ∘ f = g := by
  classical
  let p : β → Prop := fun x => ∃ a, f a = x
  let q : β → Prop := fun x => ∃ a, g a = x
  let ef : α ≃ {x // p x} := Function.Embedding.toEquivRange ⟨f, hf⟩
  let eg : α ≃ {x // q x} := Function.Embedding.toEquivRange ⟨g, hg⟩
  let es : {x // p x} ≃ {x // q x} := ef.symm.trans eg
  have hfcard : Fintype.card {x : β // p x} = Fintype.card α :=
    Fintype.card_congr ef.symm
  have hgcard : Fintype.card {x : β // q x} = Fintype.card α :=
    Fintype.card_congr eg.symm
  have hcard : Fintype.card {x // ¬p x} = Fintype.card {x // ¬q x} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hfcard, hgcard]
  let ec : {x // ¬p x} ≃ {x // ¬q x} := Fintype.equivOfCardEq hcard
  let esum : {x // p x} ⊕ {x // ¬p x} ≃ {x // q x} ⊕ {x // ¬q x} := es.sumCongr ec
  let σ : Equiv.Perm β :=
    (Equiv.sumCompl p).symm.trans (esum.trans (Equiv.sumCompl q))
  use σ
  funext a
  have hfa : (⟨f a, ⟨a, rfl⟩⟩ : {x // p x}) = ef a := by
    apply Subtype.ext
    rfl
  change (Equiv.sumCompl q) (esum ((Equiv.sumCompl p).symm (f a))) = g a
  rw [Equiv.sumCompl_symm_apply_of_pos (p := p) (⟨a, rfl⟩ : p (f a))]
  rw [hfa]
  simp [esum, es]
  rfl

/- accepted add_to_file helper 2 -/
namespace MarkingEquivalence

abbrev MVertex (d k : ℕ) := Fin d ⊕ Fin k
abbrev MEdge (n d k : ℕ) :=
  ({p : Fin d × Fin d // p.1 < p.2} × Fin n) ⊕ (Fin d × Fin k)

def mends {n d k : ℕ} : MEdge n d k → Sym2 (MVertex d k)
  | Sum.inl x => Sym2.mk (Sum.inl x.1.val.1) (Sum.inl x.1.val.2)
  | Sum.inr x => Sym2.mk (Sum.inl x.1) (Sum.inr x.2)

abbrev MMarking (n d k r : ℕ) := {μ : Fin r → MEdge n d k // Function.Injective μ}

def unmarkedRel {n d k r : ℕ} (μ : Fin r → MEdge n d k) : MVertex d k → MVertex d k → Prop :=
  fun u v => ∃ e : MEdge n d k, e ∉ Set.range μ ∧ mends e = Sym2.mk u v

def unmarkedGraph {n d k r : ℕ} (μ : Fin r → MEdge n d k) : SimpleGraph (MVertex d k) :=
  SimpleGraph.fromRel (unmarkedRel μ)

def mirreducible {n d k r : ℕ} (μ : MMarking n d k r) : Prop :=
  (unmarkedGraph μ.1).Connected

def applyPermMarking {n d k r : ℕ} (σ : Equiv.Perm (MEdge n d k)) (μ : MMarking n d k r) :
    MMarking n d k r :=
  ⟨fun i => σ (μ.1 i), σ.injective.comp μ.2⟩

def applySwapMarking {n d k r : ℕ} (a b : MEdge n d k) (μ : MMarking n d k r) :
    MMarking n d k r :=
  applyPermMarking (Equiv.swap a b) μ

end MarkingEquivalence

/- accepted add_to_file helper 3 -/
namespace MarkingEquivalence

def MDMove {n d k r : ℕ} : MMarking n d k r → MMarking n d k r → Prop := fun μ ν =>
  ∃ a b : MEdge n d k, a ≠ b ∧ mends a = mends b ∧
    ν.1 = fun i => Equiv.swap a b (μ.1 i)

def MTMove {n d k r : ℕ} : MMarking n d k r → MMarking n d k r → Prop := fun μ ν =>
  ∃ D D' D'' : MVertex d k,
    D ≠ D' ∧ D ≠ D'' ∧ D' ≠ D'' ∧
    ∃ q q' q'' : MEdge n d k,
      mends q = Sym2.mk D' D'' ∧
      mends q' = Sym2.mk D D'' ∧
      mends q'' = Sym2.mk D D' ∧
      ν.1 = if q' ∈ Set.range μ.1 then μ.1
        else fun i => Equiv.swap q q'' (μ.1 i)

def MMove {n d k r : ℕ} (μ ν : MMarking n d k r) : Prop :=
  MDMove μ ν ∨ MTMove μ ν

lemma MDMove.move {n d k r : ℕ} {μ ν : MMarking n d k r} (h : MDMove μ ν) : MMove μ ν :=
  Or.inl h

lemma MTMove.move {n d k r : ℕ} {μ ν : MMarking n d k r} (h : MTMove μ ν) : MMove μ ν :=
  Or.inr h

end MarkingEquivalence

/- accepted add_to_file helper 4 -/
namespace MarkingEquivalence

lemma dmove_swap {n d k r : ℕ} {a b : MEdge n d k} (hab : a ≠ b)
    (hends : mends a = mends b) (μ : MMarking n d k r) :
    MDMove μ (applySwapMarking a b μ) := by
  exact ⟨a, b, hab, hends, rfl⟩

lemma tmove_swap {n d k r : ℕ} (μ : MMarking n d k r) {D D' D'' : MVertex d k}
    (h12 : D ≠ D') (h13 : D ≠ D'') (h23 : D' ≠ D'')
    {q q' q'' : MEdge n d k}
    (hq : mends q = Sym2.mk D' D'')
    (hq' : mends q' = Sym2.mk D D'')
    (hq'' : mends q'' = Sym2.mk D D')
    (hun : q' ∉ Set.range μ.1) :
    MTMove μ (applySwapMarking q q'' μ) := by
  refine ⟨D, D', D'', h12, h13, h23, q, q', q'', hq, hq', hq'', ?_⟩
  simp [applySwapMarking, applyPermMarking, hun]

end MarkingEquivalence

/- accepted add_to_file helper 5 -/
namespace MarkingEquivalence

lemma mem_range_perm_comp {β ι : Type*} [DecidableEq β] (σ : Equiv.Perm β)
    (f : ι → β) (b : β) :
    b ∈ Set.range (fun i => σ (f i)) ↔ σ.symm b ∈ Set.range f := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    apply σ.injective
    simpa using hi
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    change σ (f i) = b
    rw [hi]
    simp

lemma mends_swap_parallel_apply {n d k : ℕ} {a b : MEdge n d k}
    (hends : mends a = mends b) (e : MEdge n d k) :
    mends (Equiv.swap a b e) = mends e := by
  classical
  by_cases ha : e = a
  · subst ha
    simp [hends]
  · by_cases hb : e = b
    · subst hb
      simp [hends]
    · simp [Equiv.swap_apply_of_ne_of_ne ha hb]

lemma unmarkedRel_swap_parallel {n d k r : ℕ} (μ : Fin r → MEdge n d k)
    {a b : MEdge n d k} (hends : mends a = mends b) (u v : MVertex d k) :
    unmarkedRel (fun i => Equiv.swap a b (μ i)) u v ↔ unmarkedRel μ u v := by
  classical
  constructor
  · rintro ⟨e, he, hend⟩
    have he' : Equiv.swap a b e ∉ Set.range μ := by
      have hiff := mem_range_perm_comp (σ := Equiv.swap a b) (f := μ) (b := e)
      exact (not_congr hiff).mp he
    refine ⟨Equiv.swap a b e, he', ?_⟩
    rw [mends_swap_parallel_apply hends]
    exact hend
  · rintro ⟨e, he, hend⟩
    have he' : Equiv.swap a b e ∉ Set.range (fun i => Equiv.swap a b (μ i)) := by
      have hiff := mem_range_perm_comp (σ := Equiv.swap a b) (f := μ) (b := Equiv.swap a b e)
      have hbase : (Equiv.swap a b).symm (Equiv.swap a b e) ∉ Set.range μ := by simpa using he
      exact (not_congr hiff).mpr hbase
    refine ⟨Equiv.swap a b e, he', ?_⟩
    rw [mends_swap_parallel_apply hends]
    exact hend

lemma dmove_preserves_irreducible {n d k r : ℕ} {μ : MMarking n d k r}
    {a b : MEdge n d k} (hends : mends a = mends b)
    (hμ : mirreducible μ) : mirreducible (applySwapMarking a b μ) := by
  unfold mirreducible unmarkedGraph applySwapMarking applyPermMarking
  have hrel : unmarkedRel (fun i => (Equiv.swap a b) (μ.1 i)) = unmarkedRel μ.1 := by
    funext u v
    exact propext (unmarkedRel_swap_parallel μ.1 hends u v)
  rw [hrel]
  exact hμ

end MarkingEquivalence

/- accepted add_to_file helper 6 -/
namespace MarkingEquivalence

lemma old_adj_reachable_swap_triangle {n d k r : ℕ} (μ : MMarking n d k r)
    {D D' D'' : MVertex d k}
    (h12 : D ≠ D') (h13 : D ≠ D'') (h23 : D' ≠ D'')
    {q q' q'' : MEdge n d k}
    (hq : mends q = Sym2.mk D' D'')
    (hq' : mends q' = Sym2.mk D D'')
    (hq'' : mends q'' = Sym2.mk D D')
    (hq'un : q' ∉ Set.range μ.1)
    {u v : MVertex d k}
    (hadj : (unmarkedGraph μ.1).Adj u v) :
    (unmarkedGraph (applySwapMarking q q'' μ).1).Reachable u v := by
  classical
  let σ : Equiv.Perm (MEdge n d k) := Equiv.swap q q''
  have hqq' : q ≠ q' := by
    intro h
    rw [h, hq'] at hq
    rw [Sym2.eq_iff] at hq
    rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h12 h1
    · exact h13 h1
  have hqq'' : q ≠ q'' := by
    intro h
    rw [h, hq''] at hq
    rw [Sym2.eq_iff] at hq
    rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h12 h1
    · exact h13 h1
  have hq'q'' : q' ≠ q'' := by
    intro h
    rw [h, hq''] at hq'
    rw [Sym2.eq_iff] at hq'
    rcases hq' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h23 h2
    · exact h13 h1
  have adj_of {x y : MVertex d k} {e : MEdge n d k}
      (hxy : x ≠ y) (hunm : e ∉ Set.range (fun i => σ (μ.1 i)))
      (hends : mends e = Sym2.mk x y) :
      (unmarkedGraph (applySwapMarking q q'' μ).1).Adj x y := by
    unfold unmarkedGraph applySwapMarking applyPermMarking
    rw [SimpleGraph.fromRel_adj]
    exact ⟨hxy, Or.inl ⟨e, hunm, by simpa [σ] using hends⟩⟩
  have hq'new : q' ∉ Set.range (fun i => σ (μ.1 i)) := by
    have hiff := mem_range_perm_comp (σ := σ) (f := μ.1) (b := q')
    have hfix : σ.symm q' = q' := by
      simp [σ, Equiv.swap_apply_of_ne_of_ne hqq'.symm hq'q'']
    intro hmem
    exact hq'un (by simpa [hfix] using hiff.mp hmem)
  rw [unmarkedGraph, SimpleGraph.fromRel_adj] at hadj
  rcases hadj with ⟨huv, hor⟩
  rcases hor with hrel | hrel
  · rcases hrel with ⟨e, he, hend⟩
    by_cases heq : e = q
    · subst e
      by_cases hq''old : q'' ∈ Set.range μ.1
      · have hq''new : q'' ∉ Set.range (fun i => σ (μ.1 i)) := by
          have hiff := mem_range_perm_comp (σ := σ) (f := μ.1) (b := q'')
          have hsymm : σ.symm q'' = q := by simp [σ]
          intro hmem
          exact he (by simpa [hsymm] using hiff.mp hmem)
        have hreach : (unmarkedGraph (applySwapMarking q q'' μ).1).Reachable D' D'' :=
          ((adj_of h12 hq''new hq'').symm.reachable).trans
            (adj_of h13 hq'new hq').reachable
        have hpair : Sym2.mk u v = Sym2.mk D' D'' := by rw [← hend, hq]
        rcases Sym2.eq_iff.mp hpair with ⟨hu, hv⟩ | ⟨hu, hv⟩
        · subst u; subst v; exact hreach
        · subst u; subst v; exact hreach.symm
      · have hqnew : q ∉ Set.range (fun i => σ (μ.1 i)) := by
          have hiff := mem_range_perm_comp (σ := σ) (f := μ.1) (b := q)
          have hsymm : σ.symm q = q'' := by simp [σ]
          intro hmem
          exact hq''old (by simpa [hsymm] using hiff.mp hmem)
        exact (adj_of huv hqnew (by simpa [σ] using hend)).reachable
    · by_cases heq'' : e = q''
      · subst e
        by_cases hqold : q ∈ Set.range μ.1
        · have hqnew : q ∉ Set.range (fun i => σ (μ.1 i)) := by
            have hiff := mem_range_perm_comp (σ := σ) (f := μ.1) (b := q)
            have hsymm : σ.symm q = q'' := by simp [σ]
            intro hmem
            exact he (by simpa [hsymm] using hiff.mp hmem)
          have hreach : (unmarkedGraph (applySwapMarking q q'' μ).1).Reachable D D' :=
            (adj_of h13 hq'new hq').reachable.trans
              ((adj_of h23 hqnew hq).symm.reachable)
          have hpair : Sym2.mk u v = Sym2.mk D D' := by rw [← hend, hq'']
          rcases Sym2.eq_iff.mp hpair with ⟨hu, hv⟩ | ⟨hu, hv⟩
          · subst u; subst v; exact hreach
          · subst u; subst v; exact hreach.symm
        · have hq''new : q'' ∉ Set.range (fun i => σ (μ.1 i)) := by
            have hiff := mem_range_perm_comp (σ := σ) (f := μ.1) (b := q'')
            have hsymm : σ.symm q'' = q := by simp [σ]
            intro hmem
            exact hqold (by simpa [hsymm] using hiff.mp hmem)
          exact (adj_of huv hq''new (by simpa [σ] using hend)).reachable
      · have henew : e ∉ Set.range (fun i => σ (μ.1 i)) := by
          have hiff := mem_range_perm_comp (σ := σ) (f := μ.1) (b := e)
          have hfix : σ.symm e = e := by
            simp [σ, Equiv.swap_apply_of_ne_of_ne heq heq'']
          intro hmem
          exact he (by simpa [hfix] using hiff.mp hmem)
        exact (adj_of huv henew (by simpa [σ] using hend)).reachable
  · rcases hrel with ⟨e, he, hend⟩
    have hend' : mends e = Sym2.mk u v := by
      calc
        mends e = Sym2.mk v u := hend
        _ = Sym2.mk u v := Sym2.eq_swap
    by_cases heq : e = q
    · subst e
      by_cases hq''old : q'' ∈ Set.range μ.1
      · have hq''new : q'' ∉ Set.range (fun i => σ (μ.1 i)) := by
          have hiff := mem_range_perm_comp (σ := σ) (f := μ.1) (b := q'')
          have hsymm : σ.symm q'' = q := by simp [σ]
          intro hmem
          exact he (by simpa [hsymm] using hiff.mp hmem)
        have hreach : (unmarkedGraph (applySwapMarking q q'' μ).1).Reachable D' D'' :=
          ((adj_of h12 hq''new hq'').symm.reachable).trans
            (adj_of h13 hq'new hq').reachable
        have hpair : Sym2.mk u v = Sym2.mk D' D'' := by rw [← hend', hq]
        rcases Sym2.eq_iff.mp hpair with ⟨hu, hv⟩ | ⟨hu, hv⟩
        · subst u; subst v; exact hreach
        · subst u; subst v; exact hreach.symm
      · have hqnew : q ∉ Set.range (fun i => σ (μ.1 i)) := by
          have hiff := mem_range_perm_comp (σ := σ) (f := μ.1) (b := q)
          have hsymm : σ.symm q = q'' := by simp [σ]
          intro hmem
          exact hq''old (by simpa [hsymm] using hiff.mp hmem)
        exact (adj_of huv hqnew (by simpa [σ] using hend')).reachable
    · by_cases heq'' : e = q''
      · subst e
        by_cases hqold : q ∈ Set.range μ.1
        · have hqnew : q ∉ Set.range (fun i => σ (μ.1 i)) := by
            have hiff := mem_range_perm_comp (σ := σ) (f := μ.1) (b := q)
            have hsymm : σ.symm q = q'' := by simp [σ]
            intro hmem
            exact he (by simpa [hsymm] using hiff.mp hmem)
          have hreach : (unmarkedGraph (applySwapMarking q q'' μ).1).Reachable D D' :=
            (adj_of h13 hq'new hq').reachable.trans
              ((adj_of h23 hqnew hq).symm.reachable)
          have hpair : Sym2.mk u v = Sym2.mk D D' := by rw [← hend', hq'']
          rcases Sym2.eq_iff.mp hpair with ⟨hu, hv⟩ | ⟨hu, hv⟩
          · subst u; subst v; exact hreach
          · subst u; subst v; exact hreach.symm
        · have hq''new : q'' ∉ Set.range (fun i => σ (μ.1 i)) := by
            have hiff := mem_range_perm_comp (σ := σ) (f := μ.1) (b := q'')
            have hsymm : σ.symm q'' = q := by simp [σ]
            intro hmem
            exact hqold (by simpa [hsymm] using hiff.mp hmem)
          exact (adj_of huv hq''new (by simpa [σ] using hend')).reachable
      · have henew : e ∉ Set.range (fun i => σ (μ.1 i)) := by
          have hiff := mem_range_perm_comp (σ := σ) (f := μ.1) (b := e)
          have hfix : σ.symm e = e := by
            simp [σ, Equiv.swap_apply_of_ne_of_ne heq heq'']
          intro hmem
          exact he (by simpa [hfix] using hiff.mp hmem)
        exact (adj_of huv henew (by simpa [σ] using hend')).reachable

end MarkingEquivalence

/- accepted add_to_file helper 7 -/
namespace MarkingEquivalence

lemma tmove_preserves_irreducible {n d k r : ℕ} (μ : MMarking n d k r)
    {D D' D'' : MVertex d k}
    (h12 : D ≠ D') (h13 : D ≠ D'') (h23 : D' ≠ D'')
    {q q' q'' : MEdge n d k}
    (hq : mends q = Sym2.mk D' D'')
    (hq' : mends q' = Sym2.mk D D'')
    (hq'' : mends q'' = Sym2.mk D D')
    (hq'un : q' ∉ Set.range μ.1)
    (hμ : mirreducible μ) :
    mirreducible (applySwapMarking q q'' μ) := by
  unfold mirreducible
  haveI : Nonempty (MVertex d k) := hμ.nonempty
  refine SimpleGraph.Connected.mk ?_
  intro u v
  have hold : (unmarkedGraph μ.1).Reachable u v := hμ.preconnected u v
  rw [SimpleGraph.reachable_eq_reflTransGen] at hold
  induction hold with
  | refl => exact SimpleGraph.Reachable.refl u
  | tail hrt hadj ih =>
      exact ih.trans (old_adj_reachable_swap_triangle μ h12 h13 h23 hq hq' hq'' hq'un hadj)

end MarkingEquivalence

/- accepted add_to_file helper 8 -/
namespace MarkingEquivalence

def root {d k : ℕ} (hd : 0 < d) : MVertex d k :=
  Sum.inl (⟨0, hd⟩ : Fin d)

def starEdge {n d k : ℕ} (hn : 0 < n) (hd : 0 < d)
    (x : MVertex d k) (hx : x ≠ root hd) : MEdge n d k :=
  match x with
  | Sum.inl i =>
      haveI : NeZero d := ⟨Nat.ne_of_gt hd⟩
      have hine : (⟨0, hd⟩ : Fin d) ≠ i := by
        intro h
        apply hx
        cases h
        rfl
      let p : {p : Fin d × Fin d // p.1 < p.2} :=
        ⟨Prod.mk (⟨0, hd⟩ : Fin d) i, lt_of_le_of_ne (Fin.zero_le i) hine⟩
      Sum.inl (p, ⟨0, hn⟩)
  | Sum.inr j => Sum.inr (⟨0, hd⟩, j)

lemma mends_starEdge {n d k : ℕ} (hn : 0 < n) (hd : 0 < d)
    (x : MVertex d k) (hx : x ≠ root hd) :
    mends (starEdge hn hd x hx) = Sym2.mk (root hd) x := by
  cases x with
  | inl i =>
      unfold starEdge mends root
      simp
  | inr j =>
      unfold starEdge mends root
      simp

lemma starEdge_eq_of_mends_eq {n d k : ℕ} (hn : 0 < n) (hd : 0 < d)
    {x y : MVertex d k} (hx : x ≠ root hd) (hy : y ≠ root hd)
    (h : starEdge hn hd x hx = starEdge hn hd y hy) : x = y := by
  have he := congrArg mends h
  rw [mends_starEdge hn hd x hx, mends_starEdge hn hd y hy] at he
  rw [Sym2.eq_iff] at he
  rcases he with ⟨hr, hxy⟩ | ⟨hry, hxr⟩
  · exact hxy
  · exact False.elim (hy hry.symm)

def IsCanonicalStarEdge {n d k : ℕ} (hn : 0 < n) (hd : 0 < d) : MEdge n d k → Prop :=
  fun e => ∃ (x : MVertex d k) (hx : x ≠ root hd), e = starEdge hn hd x hx

abbrev PosEdge {n d k : ℕ} (hn : 0 < n) (hd : 0 < d) :=
  {e : MEdge n d k // ¬ IsCanonicalStarEdge hn hd e}

end MarkingEquivalence

/- accepted add_to_file helper 9 -/
namespace MarkingEquivalence

lemma exists_cross_of_reachable {V : Type*} [DecidableEq V]
    {r : V → V → Prop} {S : Finset V} {a b : V}
    (h : Relation.ReflTransGen r a b) (ha : a ∉ S) (hb : b ∈ S) :
    ∃ x ∉ S, ∃ y ∈ S, r x y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      exact False.elim (ha hb)
  | head hac hcb ih =>
      rename_i a c
      by_cases hc : c ∈ S
      · exact ⟨a, ha, c, hc, hac⟩
      · exact ih hc

end MarkingEquivalence

/- accepted add_to_file helper 10 -/
namespace MarkingEquivalence

lemma notMem_range_applySwap_preimage {n d k r : ℕ} (μ : MMarking n d k r)
    {a b target source : MEdge n d k}
    (hpre : Equiv.swap a b target = source)
    (hs : source ∉ Set.range μ.1) :
    target ∉ Set.range (applySwapMarking a b μ).1 := by
  classical
  intro hmem
  have hiff := mem_range_perm_comp (σ := Equiv.swap a b) (f := μ.1) (b := target)
  have hsrc : (Equiv.swap a b).symm target ∈ Set.range μ.1 := hiff.mp hmem
  exact hs (by simpa [hpre] using hsrc)

lemma notMem_range_applySwap_fixed {n d k r : ℕ} (μ : MMarking n d k r)
    {a b e : MEdge n d k}
    (hfix : Equiv.swap a b e = e)
    (he : e ∉ Set.range μ.1) :
    e ∉ Set.range (applySwapMarking a b μ).1 := by
  classical
  intro hmem
  have hiff := mem_range_perm_comp (σ := Equiv.swap a b) (f := μ.1) (b := e)
  have hsrc : (Equiv.swap a b).symm e ∈ Set.range μ.1 := hiff.mp hmem
  exact he (by simpa [hfix] using hsrc)

end MarkingEquivalence

/- accepted add_to_file helper 11 -/
namespace MarkingEquivalence

lemma exists_unmarked_edge_of_adj {n d k r : ℕ} {μ : Fin r → MEdge n d k}
    {a b : MVertex d k} (hadj : (unmarkedGraph μ).Adj a b) :
    ∃ e : MEdge n d k, e ∉ Set.range μ ∧ mends e = Sym2.mk a b := by
  rw [unmarkedGraph, SimpleGraph.fromRel_adj] at hadj
  rcases hadj with ⟨hab, hor⟩
  rcases hor with hrel | hrel
  · exact hrel
  · rcases hrel with ⟨e, he, hend⟩
    exact ⟨e, he, hend.trans Sym2.eq_swap⟩

end MarkingEquivalence

/- accepted add_to_file helper 12 -/
namespace MarkingEquivalence

lemma starify_one_step {n d k r : ℕ} (hn : 0 < n) (hd : 0 < d)
    (μ : MMarking n d k r) (hμ : mirreducible μ)
    (S : Finset (MVertex d k)) (hroot : root hd ∈ S)
    (hstar : ∀ x ∈ S, ∀ hx : x ≠ root hd,
      starEdge hn hd x hx ∉ Set.range μ.1)
    {a b : MVertex d k} (ha : a ∉ S) (hb : b ∈ S)
    (hadj : (unmarkedGraph μ.1).Adj a b) :
    ∃ μ' : MMarking n d k r,
      Relation.ReflTransGen MMove μ μ' ∧ mirreducible μ' ∧
      ∀ x ∈ insert a S, ∀ hx : x ≠ root hd,
        starEdge hn hd x hx ∉ Set.range μ'.1 := by
  classical
  obtain ⟨e, he, hend⟩ := exists_unmarked_edge_of_adj hadj
  have haR : a ≠ root hd := by
    intro har
    exact ha (har ▸ hroot)
  by_cases hsa : starEdge hn hd a haR ∈ Set.range μ.1
  · by_cases hbR : b = root hd
    · subst b
      let sa := starEdge hn hd a haR
      have hendsym : mends e = Sym2.mk (root hd) a := hend.trans Sym2.eq_swap
      have hends : mends sa = mends e := by
        rw [mends_starEdge hn hd a haR, hendsym]
      have hsane : sa ≠ e := by
        intro h
        exact he (h ▸ hsa)
      refine ⟨applySwapMarking sa e μ, Relation.ReflTransGen.single ?_, ?_, ?_⟩
      · exact MDMove.move (dmove_swap hsane hends μ)
      · exact dmove_preserves_irreducible hends hμ
      · intro x hxS hxR
        rw [Finset.mem_insert] at hxS
        rcases hxS with rfl | hxS
        · apply notMem_range_applySwap_preimage μ
            (a := sa) (b := e) (target := sa) (source := e)
          · simp
          · exact he
        · have hxa : x ≠ a := by
            intro hxa
            exact ha (hxa ▸ hxS)
          have hfix : Equiv.swap sa e (starEdge hn hd x hxR) = starEdge hn hd x hxR := by
            apply Equiv.swap_apply_of_ne_of_ne
            · intro hsx
              exact hxa (starEdge_eq_of_mends_eq hn hd hxR haR hsx)
            · intro hxe
              have heq := congrArg mends hxe
              rw [mends_starEdge hn hd x hxR, hendsym] at heq
              rw [Sym2.eq_iff] at heq
              rcases heq with ⟨hroot, hxa'⟩ | ⟨hroota, hxroot⟩
              · exact hxa hxa'
              · exact haR hroota.symm
          apply notMem_range_applySwap_fixed μ hfix
          exact hstar x hxS hxR
    · let sa := starEdge hn hd a haR
      let sb := starEdge hn hd b hbR
      have hsb : sb ∉ Set.range μ.1 := hstar b hb hbR
      have hRb : root hd ≠ b := fun h => hbR h.symm
      have hRa : root hd ≠ a := fun h => haR h.symm
      have hab' : a ≠ b := by
        have h := hadj
        rw [unmarkedGraph, SimpleGraph.fromRel_adj] at h
        exact h.1
      have hT : MTMove μ (applySwapMarking e sa μ) :=
        tmove_swap μ hRa hRb hab'
          (q := e) (q' := sb) (q'' := sa) hend
          (mends_starEdge hn hd b hbR) (mends_starEdge hn hd a haR) hsb
      refine ⟨applySwapMarking e sa μ, Relation.ReflTransGen.single ?_, ?_, ?_⟩
      · exact MTMove.move hT
      · exact tmove_preserves_irreducible μ hRa hRb hab' hend
          (mends_starEdge hn hd b hbR) (mends_starEdge hn hd a haR) hsb hμ
      · intro x hxS hxR
        rw [Finset.mem_insert] at hxS
        rcases hxS with rfl | hxS
        · apply notMem_range_applySwap_preimage μ
            (a := e) (b := sa) (target := sa) (source := e)
          · simp
          · exact he
        · have hxa : x ≠ a := by
            intro hxa
            exact ha (hxa ▸ hxS)
          have hfix : Equiv.swap e sa (starEdge hn hd x hxR) = starEdge hn hd x hxR := by
            apply Equiv.swap_apply_of_ne_of_ne
            · intro hxe
              have heq := congrArg mends hxe
              rw [mends_starEdge hn hd x hxR, hend] at heq
              rw [Sym2.eq_iff] at heq
              rcases heq with ⟨hroota, hxb⟩ | ⟨hrootb, hxa'⟩
              · exact hRa hroota
              · exact hRb hrootb
            · intro hxsa
              exact hxa (starEdge_eq_of_mends_eq hn hd hxR haR hxsa)
          apply notMem_range_applySwap_fixed μ hfix
          exact hstar x hxS hxR
  · refine ⟨μ, Relation.ReflTransGen.refl, hμ, ?_⟩
    intro x hxS hxR
    rw [Finset.mem_insert] at hxS
    rcases hxS with rfl | hxS
    · exact hsa
    · exact hstar x hxS hxR

end MarkingEquivalence

/- accepted add_to_file helper 13 -/
namespace MarkingEquivalence

lemma exists_unmarked_edge_from_root {n d k r : ℕ} (hd : 0 < d)
    (μ : MMarking n d k r) (hμ : mirreducible μ)
    {v : MVertex d k} (hv : v ≠ root hd) :
    ∃ z : MVertex d k, z ≠ root hd ∧
      ∃ e : MEdge n d k, e ∉ Set.range μ.1 ∧ mends e = Sym2.mk (root hd) z := by
  have hreach : (unmarkedGraph μ.1).Reachable (root hd) v := hμ.preconnected _ _
  rw [SimpleGraph.reachable_eq_reflTransGen] at hreach
  rcases Relation.ReflTransGen.cases_head hreach with hEq | ⟨z, hAdj, hrest⟩
  · exact False.elim (hv hEq.symm)
  · refine ⟨z, ?_, ?_⟩
    · intro hz
      subst z
      rw [unmarkedGraph, SimpleGraph.fromRel_adj] at hAdj
      exact hAdj.1 rfl
    · exact exists_unmarked_edge_of_adj hAdj

end MarkingEquivalence

/- accepted add_to_file helper 14 -/
namespace MarkingEquivalence

lemma starify_aux_measure {n d k r : ℕ} (hn : 0 < n) (hd : 0 < d) :
    ∀ m : ℕ, ∀ (S : Finset (MVertex d k)) (μ : MMarking n d k r),
      Fintype.card (MVertex d k) - S.card = m →
      root hd ∈ S →
      (∀ x ∈ S, ∀ hx : x ≠ root hd,
        starEdge hn hd x hx ∉ Set.range μ.1) →
      mirreducible μ →
      ∃ μ' : MMarking n d k r,
        Relation.ReflTransGen MMove μ μ' ∧ mirreducible μ' ∧
        ∀ x : MVertex d k, ∀ hx : x ≠ root hd,
          starEdge hn hd x hx ∉ Set.range μ'.1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro S μ hmeasure hroot hstar hμ
      by_cases hS : S = Finset.univ
      · refine ⟨μ, Relation.ReflTransGen.refl, hμ, ?_⟩
        intro x hx
        exact hstar x (by rw [hS]; simp) hx
      · have hnotall : ∃ a : MVertex d k, a ∉ S := by
          by_contra hnone
          apply hS
          ext a
          simp only [Finset.mem_univ, iff_true]
          show a ∈ S
          by_contra ha
          exact hnone ⟨a, ha⟩
        rcases hnotall with ⟨a, ha⟩
        have hreach : (unmarkedGraph μ.1).Reachable a (root hd) := hμ.preconnected _ _
        rw [SimpleGraph.reachable_eq_reflTransGen] at hreach
        obtain ⟨x, hx, y, hy, hxy⟩ := exists_cross_of_reachable hreach ha hroot
        obtain ⟨μ₁, hpath₁, hμ₁, hstar₁⟩ :=
          starify_one_step hn hd μ hμ S hroot hstar hx hy hxy
        have hltcard : S.card < Fintype.card (MVertex d k) := by
          have hss : S ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr hS
          have := Finset.card_lt_card hss
          simpa using this
        have hlt : Fintype.card (MVertex d k) - (insert x S).card < m := by
          rw [← hmeasure, Finset.card_insert_of_notMem hx]
          omega
        obtain ⟨μ₂, hpath₂, hμ₂, hstar₂⟩ :=
          ih (Fintype.card (MVertex d k) - (insert x S).card) hlt
            (insert x S) μ₁ rfl (Finset.mem_insert_of_mem hroot) hstar₁ hμ₁
        exact ⟨μ₂, hpath₁.trans hpath₂, hμ₂, hstar₂⟩

lemma starify_with_seed {n d k r : ℕ} (hn : 0 < n) (hd : 0 < d)
    (μ : MMarking n d k r) (hμ : mirreducible μ)
    {z : MVertex d k} (hz : z ≠ root hd)
    (hseed : starEdge hn hd z hz ∉ Set.range μ.1) :
    ∃ μ' : MMarking n d k r,
      Relation.ReflTransGen MMove μ μ' ∧ mirreducible μ' ∧
      ∀ x : MVertex d k, ∀ hx : x ≠ root hd,
        starEdge hn hd x hx ∉ Set.range μ'.1 := by
  classical
  let S : Finset (MVertex d k) := {root hd, z}
  have hroot : root hd ∈ S := by simp [S]
  have hstar : ∀ x ∈ S, ∀ hx : x ≠ root hd,
      starEdge hn hd x hx ∉ Set.range μ.1 := by
    intro x hxS hx
    simp [S] at hxS
    rcases hxS with rfl | rfl
    · exact False.elim (hx rfl)
    · exact hseed
  exact starify_aux_measure hn hd (Fintype.card (MVertex d k) - S.card)
    S μ rfl hroot hstar hμ

end MarkingEquivalence

/- accepted add_to_file helper 15 -/
namespace MarkingEquivalence

lemma starify {n d k r : ℕ} (hn : 0 < n) (hd : 0 < d)
    (μ : MMarking n d k r) (hμ : mirreducible μ) :
    ∃ μ' : MMarking n d k r,
      Relation.ReflTransGen MMove μ μ' ∧ mirreducible μ' ∧
      ∀ x : MVertex d k, ∀ hx : x ≠ root hd,
        starEdge hn hd x hx ∉ Set.range μ'.1 := by
  classical
  by_cases hsingle : ∀ v : MVertex d k, v = root hd
  · exact ⟨μ, Relation.ReflTransGen.refl, hμ, fun x hx => False.elim (hx (hsingle x))⟩
  · push_neg at hsingle
    rcases hsingle with ⟨v, hv⟩
    obtain ⟨z, hz, e, he, hend⟩ := exists_unmarked_edge_from_root hd μ hμ hv
    let sz := starEdge hn hd z hz
    by_cases hsz : sz ∈ Set.range μ.1
    · have hendsym : mends e = Sym2.mk z (root hd) := hend.trans Sym2.eq_swap
      have hends : mends sz = mends e := by
        rw [mends_starEdge hn hd z hz, hendsym, Sym2.eq_swap]
      have hsne : sz ≠ e := by
        intro h
        exact he (h ▸ hsz)
      let μ₁ := applySwapMarking sz e μ
      have hpath₁ : Relation.ReflTransGen MMove μ μ₁ :=
        Relation.ReflTransGen.single (MDMove.move (dmove_swap hsne hends μ))
      have hμ₁ : mirreducible μ₁ := dmove_preserves_irreducible hends hμ
      have hseed₁ : sz ∉ Set.range μ₁.1 := by
        apply notMem_range_applySwap_preimage μ
          (a := sz) (b := e) (target := sz) (source := e)
        · simp
        · exact he
      obtain ⟨μ₂, hpath₂, hμ₂, hstar₂⟩ := starify_with_seed hn hd μ₁ hμ₁ hz hseed₁
      exact ⟨μ₂, hpath₁.trans hpath₂, hμ₂, hstar₂⟩
    · exact starify_with_seed hn hd μ hμ hz hsz

end MarkingEquivalence

/- accepted add_to_file helper 16 -/
namespace MarkingEquivalence

noncomputable def liftPosPerm {n d k : ℕ} (hn : 0 < n) (hd : 0 < d) :
    Equiv.Perm (PosEdge (k := k) hn hd) →* Equiv.Perm (MEdge n d k) := by
  classical
  exact Equiv.Perm.extendDomainHom (Equiv.refl (PosEdge (k := k) hn hd))

end MarkingEquivalence

/- accepted add_to_file helper 17 -/
namespace MarkingEquivalence

lemma liftPosPerm_swap {n d k : ℕ} (hn : 0 < n) (hd : 0 < d)
    (x y : PosEdge (k := k) hn hd) :
    liftPosPerm hn hd (Equiv.swap x y) = Equiv.swap x.1 y.1 := by
  classical
  apply Equiv.ext
  intro e
  by_cases heP : ¬ IsCanonicalStarEdge hn hd e
  · rw [liftPosPerm]
    rw [Equiv.Perm.extendDomainHom_apply]
    rw [Equiv.Perm.extendDomain_apply_subtype (Equiv.swap x y)
      (p := fun e => ¬ IsCanonicalStarEdge hn hd e)
      (Equiv.refl (PosEdge (k:=k) hn hd)) heP]
    by_cases hx : e = x.1
    · subst e
      simp
    · by_cases hy : e = y.1
      · subst e
        simp
      · have hrhs : Equiv.swap x.1 y.1 e = e := Equiv.swap_apply_of_ne_of_ne hx hy
        rw [hrhs]
        change ((Equiv.swap x y) ⟨e, heP⟩).1 = e
        rw [Equiv.swap_apply_of_ne_of_ne]
        · intro hsub
          exact hx (congrArg Subtype.val hsub)
        · intro hsub
          exact hy (congrArg Subtype.val hsub)
  · have heC : IsCanonicalStarEdge hn hd e := by
      by_contra h
      exact heP h
    have hnotP : ¬ ¬ IsCanonicalStarEdge hn hd e := by
      intro h
      exact h heC
    have hfixx : e ≠ x.1 := by
      intro h
      exact x.2 (h ▸ heC)
    have hfixy : e ≠ y.1 := by
      intro h
      exact y.2 (h ▸ heC)
    rw [Equiv.swap_apply_of_ne_of_ne hfixx hfixy]
    rw [liftPosPerm]
    rw [Equiv.Perm.extendDomainHom_apply]
    rw [Equiv.Perm.extendDomain_apply_not_subtype (Equiv.swap x y)
      (p := fun e => ¬ IsCanonicalStarEdge hn hd e)
      (Equiv.refl (PosEdge (k:=k) hn hd)) hnotP]

end MarkingEquivalence

/- accepted add_to_file helper 18 -/
namespace MarkingEquivalence

lemma mends_eq_mk_of_mem {n d k : ℕ} {e : MEdge n d k} {z : MVertex d k}
    (h : Sym2.Mem z (mends e)) :
    ∃ w : MVertex d k, mends e = Sym2.mk z w := by
  revert h
  exact Sym2.inductionOn (mends e) (fun a b hmem => by
    rw [Sym2.mem_iff'] at hmem
    rcases hmem with rfl | rfl
    · exact ⟨b, rfl⟩
    · exact ⟨a, Sym2.eq_swap⟩)

def PosAdj {n d k : ℕ} (hn : 0 < n) (hd : 0 < d) :
    PosEdge (k := k) hn hd → PosEdge (k := k) hn hd → Prop :=
  fun x y => x ≠ y ∧ ∃ z : MVertex d k, z ≠ root hd ∧
    Sym2.Mem z (mends x.1) ∧ Sym2.Mem z (mends y.1)

end MarkingEquivalence

/- accepted add_to_file helper 19 -/
namespace MarkingEquivalence

lemma mends_ne_of_eq {n d k : ℕ} {e : MEdge n d k} {u v : MVertex d k}
    (h : mends e = Sym2.mk u v) : u ≠ v := by
  intro huv
  subst v
  cases e with
  | inl e =>
      simp only [mends] at h
      have hs := Sym2.eq_iff.mp h
      rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hv : e.1.val.1 = e.1.val.2 := Sum.inl.inj (h1.trans h2.symm)
        exact (ne_of_lt e.1.property) hv
      · have hv : e.1.val.1 = e.1.val.2 := Sum.inl.inj (h1.trans h2.symm)
        exact (ne_of_lt e.1.property) hv
  | inr e =>
      simp only [mends] at h
      have hs := Sym2.eq_iff.mp h
      rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        exact Sum.inr_ne_inl (h2.trans h1.symm)

lemma starEdge_ne_of_other_ne {n d k : ℕ} (hn : 0 < n) (hd : 0 < d)
    {y : MVertex d k} (hy : y ≠ root hd) {u v : MVertex d k}
    (h : mends (starEdge hn hd y hy) = Sym2.mk u v)
    (hu : u ≠ root hd) (hv : v ≠ root hd) : False := by
  rw [mends_starEdge hn hd y hy] at h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨hur, hyv⟩ | ⟨hvr, hyu⟩
  · exact hu hur.symm
  · exact hv hvr.symm

end MarkingEquivalence

/- accepted add_to_file helper 20 -/
namespace MarkingEquivalence

lemma star_unmarked_applySwap_pos {n d k r : ℕ} (hn : 0 < n) (hd : 0 < d)
    (μ : MMarking n d k r)
    (hstar : ∀ x : MVertex d k, ∀ hx : x ≠ root hd,
      starEdge hn hd x hx ∉ Set.range μ.1)
    (x y : PosEdge (k := k) hn hd)
    (w : MVertex d k) (hw : w ≠ root hd) :
    starEdge hn hd w hw ∉ Set.range (applySwapMarking x.1 y.1 μ).1 := by
  classical
  let sw := starEdge hn hd w hw
  have hwx : sw ≠ x.1 := by
    intro h
    exact x.2 ⟨w, hw, h.symm⟩
  have hwy : sw ≠ y.1 := by
    intro h
    exact y.2 ⟨w, hw, h.symm⟩
  have hfix : Equiv.swap x.1 y.1 sw = sw :=
    Equiv.swap_apply_of_ne_of_ne hwx hwy
  exact notMem_range_applySwap_fixed μ hfix (hstar w hw)

end MarkingEquivalence

/- accepted add_to_file helper 21 -/
namespace MarkingEquivalence

lemma rtc_posadj_swap {n d k r : ℕ} (hn : 0 < n) (hd : 0 < d)
    (μ : MMarking n d k r)
    (hstar : ∀ x : MVertex d k, ∀ hx : x ≠ root hd,
      starEdge hn hd x hx ∉ Set.range μ.1)
    {x y : PosEdge (k := k) hn hd} (hxy : PosAdj hn hd x y) :
    Relation.ReflTransGen MMove μ (applySwapMarking x.1 y.1 μ) := by
  classical
  rcases hxy with ⟨hne, A, hA, hxmem, hymem⟩
  obtain ⟨B, hxends⟩ := mends_eq_mk_of_mem hxmem
  obtain ⟨C, hyends⟩ := mends_eq_mk_of_mem hymem
  have hAB : A ≠ B := mends_ne_of_eq hxends
  have hAC : A ≠ C := mends_ne_of_eq hyends
  by_cases hends : mends x.1 = mends y.1
  · have hneE : x.1 ≠ y.1 := by
      intro h
      exact hne (Subtype.ext h)
    exact Relation.ReflTransGen.single
      (MDMove.move (dmove_swap hneE hends μ))
  · have hBC : B ≠ C := by
      intro h
      apply hends
      rw [hxends, hyends, h]
    have hRA : root hd ≠ A := fun h => hA h.symm
    by_cases hB : B = root hd
    · have hC : C ≠ root hd := by
        intro h
        apply hends
        rw [hxends, hyends, hB, h]
      let sC := starEdge hn hd C hC
      have hsC : sC ∉ Set.range μ.1 := hstar C hC
      have hxends' : mends x.1 = Sym2.mk (root hd) A := hxends.trans (by rw [hB]; exact Sym2.eq_swap)
      have hRC : root hd ≠ C := fun h => hC h.symm
      have hT : MTMove μ (applySwapMarking y.1 x.1 μ) :=
        tmove_swap μ hRA hRC hAC
          (q := y.1) (q' := sC) (q'' := x.1) hyends
          (mends_starEdge hn hd C hC) hxends' hsC
      have hswap : applySwapMarking y.1 x.1 μ = applySwapMarking x.1 y.1 μ := by
        apply Subtype.ext
        funext i
        simp [applySwapMarking, applyPermMarking, Equiv.swap_comm]
      rw [← hswap]
      exact Relation.ReflTransGen.single (MTMove.move hT)
    · by_cases hC : C = root hd
      · let sB := starEdge hn hd B hB
        have hsB : sB ∉ Set.range μ.1 := hstar B hB
        have hyends' : mends y.1 = Sym2.mk (root hd) A := hyends.trans (by rw [hC]; exact Sym2.eq_swap)
        have hRB : root hd ≠ B := fun h => hB h.symm
        have hT : MTMove μ (applySwapMarking x.1 y.1 μ) :=
          tmove_swap μ hRA hRB hAB
            (q := x.1) (q' := sB) (q'' := y.1) hxends
            (mends_starEdge hn hd B hB) hyends' hsB
        exact Relation.ReflTransGen.single (MTMove.move hT)
      · let sA := starEdge hn hd A hA
        let sB := starEdge hn hd B hB
        let sC := starEdge hn hd C hC
        have hsB : sB ∉ Set.range μ.1 := hstar B hB
        have hsC : sC ∉ Set.range μ.1 := hstar C hC
        have hRB : root hd ≠ B := fun h => hB h.symm
        have hRC : root hd ≠ C := fun h => hC h.symm
        have hsA_ne_x : sA ≠ x.1 := by
          intro h
          have hm : mends sA = Sym2.mk A B := by
            have hm0 := congrArg mends h
            rwa [hxends] at hm0
          exact starEdge_ne_of_other_ne hn hd hA hm hA hB
        have hsA_ne_y : sA ≠ y.1 := by
          intro h
          have hm : mends sA = Sym2.mk A C := by
            have hm0 := congrArg mends h
            rwa [hyends] at hm0
          exact starEdge_ne_of_other_ne hn hd hA hm hA hC
        have hsB_ne_sA : sB ≠ sA := by
          intro h
          exact hAB (starEdge_eq_of_mends_eq hn hd hB hA h).symm
        have hsC_ne_sA : sC ≠ sA := by
          intro h
          exact hAC (starEdge_eq_of_mends_eq hn hd hC hA h).symm
        let μ₁ := applySwapMarking x.1 sA μ
        have hT₁ : MTMove μ μ₁ :=
          tmove_swap μ hRA hRB hAB
            (q := x.1) (q' := sB) (q'' := sA) hxends
            (mends_starEdge hn hd B hB) (mends_starEdge hn hd A hA) hsB
        have hsC₁ : sC ∉ Set.range μ₁.1 := by
          have hfix : Equiv.swap x.1 sA sC = sC := by
            apply Equiv.swap_apply_of_ne_of_ne
            · intro h
              have hm : mends sC = Sym2.mk A B := by
                have hm0 := congrArg mends h
                rwa [hxends] at hm0
              exact starEdge_ne_of_other_ne hn hd hC hm hA hB
            · exact hsC_ne_sA
          exact notMem_range_applySwap_fixed μ hfix hsC
        have hsB₁ : sB ∉ Set.range μ₁.1 := by
          have hfix : Equiv.swap x.1 sA sB = sB := by
            apply Equiv.swap_apply_of_ne_of_ne
            · intro h
              have hm : mends sB = Sym2.mk A B := by
                have hm0 := congrArg mends h
                rwa [hxends] at hm0
              exact starEdge_ne_of_other_ne hn hd hB hm hA hB
            · exact hsB_ne_sA
          exact notMem_range_applySwap_fixed μ hfix hsB
        let μ₂ := applySwapMarking y.1 sA μ₁
        have hT₂ : MTMove μ₁ μ₂ :=
          tmove_swap μ₁ hRA hRC hAC
            (q := y.1) (q' := sC) (q'' := sA) hyends
            (mends_starEdge hn hd C hC) (mends_starEdge hn hd A hA) hsC₁
        have hsB₂ : sB ∉ Set.range μ₂.1 := by
          have hfix : Equiv.swap y.1 sA sB = sB := by
            apply Equiv.swap_apply_of_ne_of_ne
            · intro h
              have hm : mends sB = Sym2.mk A C := by
                have hm0 := congrArg mends h
                rwa [hyends] at hm0
              exact starEdge_ne_of_other_ne hn hd hB hm hA hC
            · exact hsB_ne_sA
          exact notMem_range_applySwap_fixed μ₁ hfix hsB₁
        let μ₃ := applySwapMarking x.1 sA μ₂
        have hT₃ : MTMove μ₂ μ₃ :=
          tmove_swap μ₂ hRA hRB hAB
            (q := x.1) (q' := sB) (q'' := sA) hxends
            (mends_starEdge hn hd B hB) (mends_starEdge hn hd A hA) hsB₂
        have hpath : Relation.ReflTransGen MMove μ μ₃ :=
          (Relation.ReflTransGen.single (MTMove.move hT₁)).trans
            ((Relation.ReflTransGen.single (MTMove.move hT₂)).trans
              (Relation.ReflTransGen.single (MTMove.move hT₃)))
        have hμ₃ : μ₃ = applySwapMarking x.1 y.1 μ := by
          apply Subtype.ext
          funext i
          have hperm :
              Equiv.swap x.1 sA * Equiv.swap y.1 sA * Equiv.swap x.1 sA =
                Equiv.swap x.1 y.1 := by
            have h := Equiv.swap_mul_swap_mul_swap
              (x := y.1) (y := sA) (z := x.1)
              (by
                intro h
                exact hsA_ne_y h.symm)
              (by
                intro h
                exact hne (Subtype.ext h.symm))
            simpa [Equiv.swap_comm] using h
          have happ := congrArg (fun σ : Equiv.Perm (MEdge n d k) => σ (μ.1 i)) hperm
          simpa [μ₁, μ₂, μ₃, applySwapMarking, applyPermMarking, Equiv.Perm.mul_apply] using happ
        rw [hμ₃] at hpath
        exact hpath

end MarkingEquivalence

/- accepted add_to_file helper 22 -/
namespace MarkingEquivalence

lemma rtc_swap_of_posadj_path {n d k r : ℕ} (hn : 0 < n) (hd : 0 < d)
    {x y : PosEdge (k := k) hn hd} (hne : x ≠ y)
    (h : Relation.ReflTransGen (PosAdj hn hd) x y) :
    ∀ (μ : MMarking n d k r),
      (∀ v : MVertex d k, ∀ hv : v ≠ root hd,
        starEdge hn hd v hv ∉ Set.range μ.1) →
      Relation.ReflTransGen MMove μ (applySwapMarking x.1 y.1 μ) := by
  induction h with
  | refl =>
      intro μ hstar
      exact False.elim (hne rfl)
  | tail hxy hyz ih =>
      rename_i y z
      intro μ hstar
      by_cases hxyeq : x = y
      · subst y
        exact rtc_posadj_swap hn hd μ hstar hyz
      · let μ₁ := applySwapMarking x.1 y.1 μ
        have hstar₁ : ∀ v : MVertex d k, ∀ hv : v ≠ root hd,
            starEdge hn hd v hv ∉ Set.range μ₁.1 :=
          fun v hv => star_unmarked_applySwap_pos hn hd μ hstar x y v hv
        have hpath₁ : Relation.ReflTransGen MMove μ μ₁ := ih hxyeq μ hstar
        let μ₂ := applySwapMarking y.1 z.1 μ₁
        have hstar₂ : ∀ v : MVertex d k, ∀ hv : v ≠ root hd,
            starEdge hn hd v hv ∉ Set.range μ₂.1 :=
          fun v hv => star_unmarked_applySwap_pos hn hd μ₁ hstar₁ y z v hv
        have hpath₂ : Relation.ReflTransGen MMove μ₁ μ₂ :=
          rtc_posadj_swap hn hd μ₁ hstar₁ hyz
        let μ₃ := applySwapMarking x.1 y.1 μ₂
        have hstar₃ : ∀ v : MVertex d k, ∀ hv : v ≠ root hd,
            starEdge hn hd v hv ∉ Set.range μ₃.1 :=
          fun v hv => star_unmarked_applySwap_pos hn hd μ₂ hstar₂ x y v hv
        have hpath₃ : Relation.ReflTransGen MMove μ₂ μ₃ := ih hxyeq μ₂ hstar₂
        have hpath : Relation.ReflTransGen MMove μ μ₃ :=
          hpath₁.trans (hpath₂.trans hpath₃)
        have hμ₃ : μ₃ = applySwapMarking x.1 z.1 μ := by
          apply Subtype.ext
          funext i
          have hperm :
              Equiv.swap x.1 y.1 * Equiv.swap y.1 z.1 * Equiv.swap x.1 y.1 =
                Equiv.swap x.1 z.1 := by
            have hyz' : z.1 ≠ y.1 := by
              intro hE
              exact hyz.1 (Subtype.ext hE.symm)
            have hzx : z.1 ≠ x.1 := by
              intro hE
              exact hne (Subtype.ext hE.symm)
            have hswap := Equiv.swap_mul_swap_mul_swap
              (x := z.1) (y := y.1) (z := x.1) hyz' hzx
            simpa [Equiv.swap_comm] using hswap
          have happ := congrArg (fun σ : Equiv.Perm (MEdge n d k) => σ (μ.1 i)) hperm
          simpa [μ₁, μ₂, μ₃, applySwapMarking, applyPermMarking, Equiv.Perm.mul_apply] using happ
        rw [hμ₃] at hpath
        exact hpath

end MarkingEquivalence

/- accepted add_to_file helper 23 -/
namespace MarkingEquivalence

def hubVertex {d k : ℕ} (hd2 : 1 < d) : MVertex d k :=
  Sum.inl (⟨1, hd2⟩ : Fin d)

def llEdge {n d k : ℕ} (hn : 0 < n) (i j : Fin d) (hij : i ≠ j) : MEdge n d k :=
  if hlt : i < j then
    Sum.inl (⟨(i, j), hlt⟩, ⟨0, hn⟩)
  else
    Sum.inl (⟨(j, i), lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)⟩, ⟨0, hn⟩)

lemma mends_llEdge {n d k : ℕ} (hn : 0 < n) (i j : Fin d) (hij : i ≠ j) :
    mends (llEdge hn i j hij) = Sym2.mk (Sum.inl i : MVertex d k) (Sum.inl j) := by
  unfold llEdge
  split <;> simp [mends, Sym2.eq_swap]

end MarkingEquivalence

/- accepted add_to_file helper 24 -/
namespace MarkingEquivalence

lemma llEdge_notCanonical {n d k : ℕ} (hn : 0 < n) {hd : 0 < d}
    {i j : Fin d} (hij : i ≠ j)
    (hi : (Sum.inl i : MVertex d k) ≠ root hd)
    (hj : (Sum.inl j : MVertex d k) ≠ root hd) :
    ¬ IsCanonicalStarEdge (k := k) hn hd (llEdge (k := k) hn i j hij) := by
  rintro ⟨x, hx, hEq⟩
  have hm := congrArg mends hEq
  rw [mends_llEdge (k := k) hn i j hij, mends_starEdge hn hd x hx] at hm
  have hmstar : mends (starEdge hn hd x hx) =
      Sym2.mk (Sum.inl i : MVertex d k) (Sum.inl j) := by
    rw [mends_starEdge hn hd x hx]
    exact hm.symm
  exact starEdge_ne_of_other_ne hn hd hx hmstar hi hj

lemma inl_ne_root_of_ne {d k : ℕ} {hd : 0 < d} {i : Fin d}
    (hi : i ≠ ⟨0, hd⟩) : (Sum.inl i : MVertex d k) ≠ root hd := by
  intro h
  apply hi
  cases h
  rfl

lemma fin_ne_of_inl_ne_root {d k : ℕ} {hd : 0 < d} {i : Fin d}
    (hi : (Sum.inl i : MVertex d k) ≠ root hd) : i ≠ ⟨0, hd⟩ := by
  intro h
  apply hi
  rw [h]
  rfl

lemma inr_ne_root {d k : ℕ} (hd : 0 < d) (j : Fin k) :
    (Sum.inr j : MVertex d k) ≠ root hd := by
  intro h
  cases h

end MarkingEquivalence

/- accepted add_to_file helper 25 -/
namespace MarkingEquivalence

lemma mem_mends_of_eq_left {n d k : ℕ} {e : MEdge n d k} {u v : MVertex d k}
    (h : mends e = Sym2.mk u v) : Sym2.Mem u (mends e) := by
  rw [h, Sym2.mem_iff']
  exact Or.inl rfl

lemma mem_mends_of_eq_right {n d k : ℕ} {e : MEdge n d k} {u v : MVertex d k}
    (h : mends e = Sym2.mk u v) : Sym2.Mem v (mends e) := by
  rw [h, Sym2.mem_iff']
  exact Or.inr rfl

lemma hub_mem_llEdge_left {n d k : ℕ} (hn : 0 < n) {hd2 : 1 < d}
    (i : Fin d) (h : ⟨1, hd2⟩ ≠ i) :
    Sym2.Mem (hubVertex (k := k) hd2)
      (mends (llEdge (k := k) hn (⟨1, hd2⟩ : Fin d) i h)) := by
  apply mem_mends_of_eq_left (mends_llEdge (k := k) hn (⟨1, hd2⟩ : Fin d) i h)

lemma hub_mem_llEdge_right {n d k : ℕ} (hn : 0 < n) {hd2 : 1 < d}
    (i : Fin d) (h : i ≠ ⟨1, hd2⟩) :
    Sym2.Mem (hubVertex (k := k) hd2)
      (mends (llEdge (k := k) hn i (⟨1, hd2⟩ : Fin d) h)) := by
  apply mem_mends_of_eq_right (mends_llEdge (k := k) hn i (⟨1, hd2⟩ : Fin d) h)

end MarkingEquivalence

/- accepted add_to_file helper 26 -/
namespace MarkingEquivalence

lemma exists_hub_neighbor {n d k : ℕ} (hn : 0 < n) {hd2 : 1 < d}
    (p : PosEdge (k := k) hn (Nat.lt_trans Nat.zero_lt_one hd2)) :
    ∃ q : PosEdge (k := k) hn (Nat.lt_trans Nat.zero_lt_one hd2),
      Sym2.Mem (hubVertex (k := k) hd2) (mends q.1) ∧
      Relation.ReflTransGen (PosAdj hn (Nat.lt_trans Nat.zero_lt_one hd2)) p q := by
  classical
  let hd : 0 < d := Nat.lt_trans Nat.zero_lt_one hd2
  let hubF : Fin d := ⟨1, hd2⟩
  let rootF : Fin d := ⟨0, hd⟩
  have hhubR : hubVertex (k := k) hd2 ≠ root hd :=
    inl_ne_root_of_ne (by
      intro h
      have : (1 : ℕ) = 0 := congrArg Fin.val h
      omega)
  cases hp : p.1 with
  | inr x =>
      rcases x with ⟨i, j⟩
      by_cases hiH : i = hubF
      · refine ⟨p, ?_, Relation.ReflTransGen.refl⟩
        have hend : mends p.1 = Sym2.mk (Sum.inl i : MVertex d k) (Sum.inr j) := by
          simp [hp, mends]
        rw [hiH] at hend
        exact mem_mends_of_eq_left hend
      · have hiRfin : i ≠ rootF := by
          intro hi0
          have hcan : IsCanonicalStarEdge (k := k) hn hd p.1 :=
            ⟨Sum.inr j, inr_ne_root hd j, by
              simp [hp, starEdge, hi0, rootF]⟩
          exact p.2 hcan
        have hiR : (Sum.inl i : MVertex d k) ≠ root hd := inl_ne_root_of_ne hiRfin
        have hhubi : hubF ≠ i := fun h => hiH h.symm
        let qe : MEdge n d k := llEdge (k := k) hn hubF i hhubi
        have hqP : ¬ IsCanonicalStarEdge (k := k) hn hd qe :=
          llEdge_notCanonical hn hhubi hhubR hiR
        let q : PosEdge (k := k) hn hd := ⟨qe, hqP⟩
        refine ⟨q, ?_, Relation.ReflTransGen.single ?_⟩
        · exact hub_mem_llEdge_left (k := k) hn i hhubi
        · refine ⟨?_, Sum.inl i, hiR, ?_, ?_⟩
          · intro hqp
            have hmem := hub_mem_llEdge_left (k := k) hn i hhubi
            have hqeq : q.1 = p.1 := congrArg Subtype.val hqp.symm
            have hmem' : Sym2.Mem (hubVertex (k := k) hd2) (mends p.1) := by
              rw [← hqeq]
              exact hmem
            have hendp : mends p.1 = Sym2.mk (Sum.inl i : MVertex d k) (Sum.inr j) := by
              simp [hp, mends]
            rw [hendp, Sym2.mem_iff'] at hmem'
            rcases hmem' with h | h
            · exact hiH (Sum.inl.inj h).symm
            · cases h
          · have hendp : mends p.1 = Sym2.mk (Sum.inl i : MVertex d k) (Sum.inr j) := by
              simp [hp, mends]
            exact mem_mends_of_eq_left hendp
          · exact mem_mends_of_eq_right (mends_llEdge (k := k) hn hubF i hhubi)
  | inl x =>
      rcases x with ⟨⟨⟨i, j⟩, hij⟩, c⟩
      have hendp : mends p.1 = Sym2.mk (Sum.inl i : MVertex d k) (Sum.inl j) := by
        simp [hp, mends]
      by_cases hiH : i = hubF
      · refine ⟨p, ?_, Relation.ReflTransGen.refl⟩
        rw [hiH] at hendp
        exact mem_mends_of_eq_left hendp
      · by_cases hjH : j = hubF
        · refine ⟨p, ?_, Relation.ReflTransGen.refl⟩
          rw [hjH] at hendp
          exact mem_mends_of_eq_right hendp
        · by_cases hi0 : i = rootF
          · have hjRfin : j ≠ rootF := by
              intro hj0
              have hval : i.val < j.val := hij
              rw [hi0, hj0] at hval
              simp [rootF] at hval
            have hjR : (Sum.inl j : MVertex d k) ≠ root hd := inl_ne_root_of_ne hjRfin
            have hhubj : hubF ≠ j := fun h => hjH h.symm
            let qe : MEdge n d k := llEdge (k := k) hn hubF j hhubj
            have hqP : ¬ IsCanonicalStarEdge (k := k) hn hd qe :=
              llEdge_notCanonical hn hhubj hhubR hjR
            let q : PosEdge (k := k) hn hd := ⟨qe, hqP⟩
            refine ⟨q, ?_, Relation.ReflTransGen.single ?_⟩
            · exact hub_mem_llEdge_left (k := k) hn j hhubj
            · refine ⟨?_, Sum.inl j, hjR, ?_, ?_⟩
              · intro hqp
                have hmem := hub_mem_llEdge_left (k := k) hn j hhubj
                have hqeq : q.1 = p.1 := congrArg Subtype.val hqp.symm
                have hmem' : Sym2.Mem (hubVertex (k := k) hd2) (mends p.1) := by
                  rw [← hqeq]
                  exact hmem
                rw [hendp, Sym2.mem_iff'] at hmem'
                rcases hmem' with h | h
                · exact hiH (Sum.inl.inj h).symm
                · exact hjH (Sum.inl.inj h).symm
              · exact mem_mends_of_eq_right hendp
              · exact mem_mends_of_eq_right (mends_llEdge (k := k) hn hubF j hhubj)
          · have hiR : (Sum.inl i : MVertex d k) ≠ root hd := inl_ne_root_of_ne hi0
            have hhubi : hubF ≠ i := fun h => hiH h.symm
            let qe : MEdge n d k := llEdge (k := k) hn hubF i hhubi
            have hqP : ¬ IsCanonicalStarEdge (k := k) hn hd qe :=
              llEdge_notCanonical hn hhubi hhubR hiR
            let q : PosEdge (k := k) hn hd := ⟨qe, hqP⟩
            refine ⟨q, ?_, Relation.ReflTransGen.single ?_⟩
            · exact hub_mem_llEdge_left (k := k) hn i hhubi
            · refine ⟨?_, Sum.inl i, hiR, ?_, ?_⟩
              · intro hqp
                have hmem := hub_mem_llEdge_left (k := k) hn i hhubi
                have hqeq : q.1 = p.1 := congrArg Subtype.val hqp.symm
                have hmem' : Sym2.Mem (hubVertex (k := k) hd2) (mends p.1) := by
                  rw [← hqeq]
                  exact hmem
                rw [hendp, Sym2.mem_iff'] at hmem'
                rcases hmem' with h | h
                · exact hiH (Sum.inl.inj h).symm
                · exact hjH (Sum.inl.inj h).symm
              · exact mem_mends_of_eq_left hendp
              · exact mem_mends_of_eq_right (mends_llEdge (k := k) hn hubF i hhubi)

end MarkingEquivalence

/- accepted add_to_file helper 27 -/
namespace MarkingEquivalence

lemma PosAdj.symm {n d k : ℕ} (hn : 0 < n) (hd : 0 < d)
    {x y : PosEdge (k := k) hn hd} (h : PosAdj hn hd x y) :
    PosAdj hn hd y x := by
  rcases h with ⟨hne, z, hz, hxz, hyz⟩
  exact ⟨hne.symm, z, hz, hyz, hxz⟩

lemma rtc_posadj_symm {n d k : ℕ} (hn : 0 < n) (hd : 0 < d)
    {x y : PosEdge (k := k) hn hd}
    (h : Relation.ReflTransGen (PosAdj hn hd) x y) :
    Relation.ReflTransGen (PosAdj hn hd) y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact (Relation.ReflTransGen.single (PosAdj.symm hn hd hyz)).trans ih

lemma posadj_reachable_all {n d k : ℕ} (hn : 0 < n) {hd2 : 1 < d}
    (x y : PosEdge (k := k) hn (Nat.lt_trans Nat.zero_lt_one hd2)) :
    Relation.ReflTransGen (PosAdj hn (Nat.lt_trans Nat.zero_lt_one hd2)) x y := by
  classical
  let hd : 0 < d := Nat.lt_trans Nat.zero_lt_one hd2
  obtain ⟨a, ha, hxa⟩ := exists_hub_neighbor (k := k) hn (hd2 := hd2) x
  obtain ⟨b, hb, hyb⟩ := exists_hub_neighbor (k := k) hn (hd2 := hd2) y
  have hhubR : hubVertex (k := k) hd2 ≠ root hd :=
    inl_ne_root_of_ne (by
      intro h
      have : (1 : ℕ) = 0 := congrArg Fin.val h
      omega)
  have hab : Relation.ReflTransGen (PosAdj hn hd) a b := by
    by_cases hEq : a = b
    · subst b
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single
        ⟨hEq, hubVertex (k := k) hd2, hhubR, ha, hb⟩
  exact hxa.trans (hab.trans (rtc_posadj_symm hn hd hyb))

end MarkingEquivalence

/- accepted add_to_file helper 28 -/
namespace MarkingEquivalence

lemma liftPosPerm_apply_canonical {n d k : ℕ} (hn : 0 < n) (hd : 0 < d)
    (σ : Equiv.Perm (PosEdge (k := k) hn hd))
    {e : MEdge n d k} (he : IsCanonicalStarEdge hn hd e) :
    (liftPosPerm hn hd σ) e = e := by
  classical
  rw [liftPosPerm, Equiv.Perm.extendDomainHom_apply]
  rw [Equiv.Perm.extendDomain_apply_not_subtype σ
    (p := fun e => ¬ IsCanonicalStarEdge hn hd e)
    (Equiv.refl (PosEdge (k := k) hn hd))]
  intro h
  exact h he

lemma star_unmarked_applyPerm_pos {n d k r : ℕ} (hn : 0 < n) (hd : 0 < d)
    (σ : Equiv.Perm (PosEdge (k := k) hn hd))
    (μ : MMarking n d k r)
    (hstar : ∀ x : MVertex d k, ∀ hx : x ≠ root hd,
      starEdge hn hd x hx ∉ Set.range μ.1)
    (x : MVertex d k) (hx : x ≠ root hd) :
    starEdge hn hd x hx ∉ Set.range (applyPermMarking (liftPosPerm hn hd σ) μ).1 := by
  classical
  intro hmem
  have hiff := mem_range_perm_comp (σ := liftPosPerm hn hd σ) (f := μ.1)
    (b := starEdge hn hd x hx)
  have hold := hiff.mp hmem
  have hfixsymm : (liftPosPerm hn hd σ).symm (starEdge hn hd x hx) =
      starEdge hn hd x hx := by
    have hfix := liftPosPerm_apply_canonical hn hd σ.symm
      (e := starEdge hn hd x hx) ⟨x, hx, rfl⟩
    simpa using hfix
  exact hstar x hx (by simpa [hfixsymm] using hold)

end MarkingEquivalence

/- accepted add_to_file helper 29 -/
namespace MarkingEquivalence

lemma rtc_applyPerm_pos {n d k r : ℕ} (hn : 0 < n) {hd2 : 1 < d}
    (μ : MMarking n d k r)
    (hstar : ∀ x : MVertex d k, ∀ hx : x ≠ root (Nat.lt_trans Nat.zero_lt_one hd2),
      starEdge hn (Nat.lt_trans Nat.zero_lt_one hd2) x hx ∉ Set.range μ.1)
    (σ : Equiv.Perm (PosEdge (k := k) hn (Nat.lt_trans Nat.zero_lt_one hd2))) :
    Relation.ReflTransGen MMove μ
      (applyPermMarking (liftPosPerm hn (Nat.lt_trans Nat.zero_lt_one hd2) σ) μ) := by
  classical
  let hd : 0 < d := Nat.lt_trans Nat.zero_lt_one hd2
  let P := PosEdge (k := k) hn hd
  let motive : Equiv.Perm P → Prop := fun σ =>
    Relation.ReflTransGen MMove μ (applyPermMarking (liftPosPerm hn hd σ) μ)
  have hone : motive 1 := by
    change Relation.ReflTransGen MMove μ (applyPermMarking (liftPosPerm hn hd (1 : Equiv.Perm P)) μ)
    have hid : applyPermMarking (liftPosPerm hn hd (1 : Equiv.Perm P)) μ = μ := by
      apply Subtype.ext
      funext i
      simp [applyPermMarking]
    simpa [hid] using (Relation.ReflTransGen.refl : Relation.ReflTransGen MMove μ μ)
  have hstep : ∀ (τ : Equiv.Perm P) (x y : P), x ≠ y → motive τ →
      motive (Equiv.swap x y * τ) := by
    intro τ x y hxy hτ
    change Relation.ReflTransGen MMove μ
      (applyPermMarking (liftPosPerm hn hd (Equiv.swap x y * τ)) μ)
    let μτ := applyPermMarking (liftPosPerm hn hd τ) μ
    have hstarτ : ∀ v : MVertex d k, ∀ hv : v ≠ root hd,
        starEdge hn hd v hv ∉ Set.range μτ.1 :=
      fun v hv => star_unmarked_applyPerm_pos hn hd τ μ hstar v hv
    have hpath : Relation.ReflTransGen MMove μτ (applySwapMarking x.1 y.1 μτ) :=
      rtc_swap_of_posadj_path hn hd hxy (posadj_reachable_all (k := k) hn (hd2 := hd2) x y)
        μτ hstarτ
    have hnext : applySwapMarking x.1 y.1 μτ =
        applyPermMarking (liftPosPerm hn hd (Equiv.swap x y * τ)) μ := by
      apply Subtype.ext
      funext i
      simp [μτ, applySwapMarking, applyPermMarking, map_mul,
        liftPosPerm_swap hn hd x y, Equiv.Perm.mul_apply]
    simpa [hnext] using hτ.trans hpath
  exact Equiv.Perm.swap_induction_on σ hone hstep

end MarkingEquivalence

/- accepted add_to_file helper 30 -/
namespace MarkingEquivalence

lemma liftPosPerm_apply_pos {n d k : ℕ} (hn : 0 < n) (hd : 0 < d)
    (σ : Equiv.Perm (PosEdge (k := k) hn hd))
    (p : PosEdge (k := k) hn hd) :
    (liftPosPerm hn hd σ) p.1 = (σ p).1 := by
  classical
  rw [liftPosPerm, Equiv.Perm.extendDomainHom_apply]
  rw [Equiv.Perm.extendDomain_apply_subtype σ
    (p := fun e => ¬ IsCanonicalStarEdge hn hd e)
    (Equiv.refl (PosEdge (k := k) hn hd)) p.2]
  simp

end MarkingEquivalence

/- accepted add_to_file helper 31 -/
namespace MarkingEquivalence

lemma star_unmarked_equiv {n d k r : ℕ} (hn : 0 < n) {hd2 : 1 < d}
    (μ ν : MMarking n d k r)
    (hμstar : ∀ x : MVertex d k, ∀ hx : x ≠ root (Nat.lt_trans Nat.zero_lt_one hd2),
      starEdge hn (Nat.lt_trans Nat.zero_lt_one hd2) x hx ∉ Set.range μ.1)
    (hνstar : ∀ x : MVertex d k, ∀ hx : x ≠ root (Nat.lt_trans Nat.zero_lt_one hd2),
      starEdge hn (Nat.lt_trans Nat.zero_lt_one hd2) x hx ∉ Set.range ν.1) :
    Relation.ReflTransGen MMove μ ν := by
  classical
  let hd : 0 < d := Nat.lt_trans Nat.zero_lt_one hd2
  let P := PosEdge (k := k) hn hd
  let f : Fin r → P := fun i =>
    ⟨μ.1 i, by
      intro hcan
      rcases hcan with ⟨x, hx, hEq⟩
      exact hμstar x hx ⟨i, hEq⟩⟩
  let g : Fin r → P := fun i =>
    ⟨ν.1 i, by
      intro hcan
      rcases hcan with ⟨x, hx, hEq⟩
      exact hνstar x hx ⟨i, hEq⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply μ.2
    exact congrArg Subtype.val hij
  have hg : Function.Injective g := by
    intro i j hij
    apply ν.2
    exact congrArg Subtype.val hij
  obtain ⟨σ, hσ⟩ := exists_perm_comp_eq_of_injective f g hf hg
  have hpath := rtc_applyPerm_pos (k := k) hn (hd2 := hd2) μ hμstar σ
  have htarget : applyPermMarking (liftPosPerm hn hd σ) μ = ν := by
    apply Subtype.ext
    funext i
    calc
      (liftPosPerm hn hd σ) (μ.1 i) = (σ (f i)).1 := by
        rw [liftPosPerm_apply_pos hn hd σ (f i)]
      _ = (g i).1 := by
        have hi := congrFun hσ i
        exact congrArg Subtype.val hi
      _ = ν.1 i := rfl
  rw [htarget] at hpath
  exact hpath

end MarkingEquivalence

/- accepted add_to_file helper 32 -/
namespace MarkingEquivalence

lemma edge_d1_eq {n k : ℕ} (e : MEdge n 1 k) :
    ∃ j : Fin k, e = Sum.inr (⟨0, Nat.zero_lt_one⟩, j) := by
  cases e with
  | inl x =>
      rcases x with ⟨⟨⟨i, j⟩, hij⟩, c⟩
      have hi : i.val < 1 := i.isLt
      have hj : j.val < 1 := j.isLt
      have hlt : i.val < j.val := hij
      omega
  | inr x =>
      rcases x with ⟨i, j⟩
      refine ⟨j, ?_⟩
      congr 1
      congr 1
      apply Fin.ext
      have hi : i.val < 1 := i.isLt
      omega

lemma d1_star_unmarked {n k r : ℕ} (μ : MMarking n 1 k r)
    (hμ : mirreducible μ) (j : Fin k) :
    Sum.inr (⟨0, Nat.zero_lt_one⟩, j) ∉ Set.range μ.1 := by
  classical
  let R : MVertex 1 k := Sum.inl (⟨0, Nat.zero_lt_one⟩ : Fin 1)
  let F : MVertex 1 k := Sum.inr j
  have hRF : R ≠ F := by simp [R, F]
  have hreach : (unmarkedGraph μ.1).Reachable R F := hμ.preconnected _ _
  rw [SimpleGraph.reachable_eq_reflTransGen] at hreach
  rcases Relation.ReflTransGen.cases_tail hreach with hEq | ⟨c, hrtc, hAdj⟩
  · exact False.elim (hRF hEq.symm)
  · obtain ⟨e, he, hend⟩ := exists_unmarked_edge_of_adj hAdj
    obtain ⟨j₀, hj₀⟩ := edge_d1_eq e
    have hend₀ : mends e = Sym2.mk R (Sum.inr j₀ : MVertex 1 k) := by
      simp [hj₀, mends, R]
    have hpair : Sym2.mk c F = Sym2.mk R (Sum.inr j₀ : MVertex 1 k) := by
      rw [← hend, hend₀]
    rw [Sym2.eq_iff] at hpair
    rcases hpair with ⟨hcR, hjF⟩ | ⟨hcF, hFR⟩
    · have hj₀j : j₀ = j := (Sum.inr.inj hjF).symm
      subst c
      subst j₀
      simpa [hj₀] using he
    · exact False.elim (hRF hFR.symm)

end MarkingEquivalence

/- accepted add_to_file helper 33 -/
namespace MarkingEquivalence

lemma d1_markings_eq {n k r : ℕ} (μ ν : MMarking n 1 k r)
    (hμ : mirreducible μ) (hν : mirreducible ν) : μ = ν := by
  have hr : r = 0 := by
    by_contra hr
    let i : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
    obtain ⟨j, hj⟩ := edge_d1_eq (μ.1 i)
    exact d1_star_unmarked μ hμ j ⟨i, hj⟩
  subst r
  apply Subtype.ext
  funext i
  exact Fin.elim0 i

end MarkingEquivalence

/- accepted add_to_file helper 34 -/
namespace MarkingEquivalence

lemma d0_markings_eq {n k r : ℕ} (μ ν : MMarking n 0 k r) : μ = ν := by
  have hr : r = 0 := by
    by_contra hr
    let i : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
    cases h : μ.1 i with
    | inl e =>
        exact e.1.val.1.elim0
    | inr e =>
        exact e.1.elim0
  subst r
  apply Subtype.ext
  funext i
  exact Fin.elim0 i

end MarkingEquivalence

/- accepted add_to_file helper 35 -/
namespace MarkingEquivalence

lemma MDMove.symm {n d k r : ℕ} {μ ν : MMarking n d k r}
    (h : MDMove μ ν) : MDMove ν μ := by
  rcases h with ⟨a, b, hab, hends, hfun⟩
  refine ⟨a, b, hab, hends, ?_⟩
  funext i
  rw [hfun]
  simp

lemma MTMove.symm {n d k r : ℕ} {μ ν : MMarking n d k r}
    (h : MTMove μ ν) : MTMove ν μ := by
  classical
  rcases h with ⟨D, D', D'', h12, h13, h23, q, q', q'', hq, hq', hq'', hfun⟩
  have hqq' : q ≠ q' := by
    intro h
    rw [h, hq'] at hq
    rw [Sym2.eq_iff] at hq
    rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h12 h1
    · exact h13 h1
  have hqq'' : q ≠ q'' := by
    intro h
    rw [h, hq''] at hq
    rw [Sym2.eq_iff] at hq
    rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h12 h1
    · exact h13 h1
  have hq'q'' : q' ≠ q'' := by
    intro h
    rw [h, hq''] at hq'
    rw [Sym2.eq_iff] at hq'
    rcases hq' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h23 h2
    · exact h13 h1
  by_cases hmarked : q' ∈ Set.range μ.1
  · have hνq' : q' ∈ Set.range ν.1 := by
      rw [hfun, if_pos hmarked]
      exact hmarked
    refine ⟨D, D', D'', h12, h13, h23, q, q', q'', hq, hq', hq'', ?_⟩
    rw [if_pos hνq']
    rw [hfun, if_pos hmarked]
  · have hνq' : q' ∉ Set.range ν.1 := by
      rw [hfun, if_neg hmarked]
      have hfix : Equiv.swap q q'' q' = q' :=
        Equiv.swap_apply_of_ne_of_ne hqq'.symm hq'q''
      exact notMem_range_applySwap_fixed μ hfix hmarked
    refine ⟨D, D', D'', h12, h13, h23, q, q', q'', hq, hq', hq'', ?_⟩
    rw [if_neg hνq']
    funext i
    rw [hfun, if_neg hmarked]
    simp

lemma MMove.symmetric {n d k r : ℕ} : Symmetric (MMove (n := n) (d := d) (k := k) (r := r)) := by
  intro μ ν h
  rcases h with h | h
  · exact Or.inl (MDMove.symm h)
  · exact Or.inr (MTMove.symm h)

end MarkingEquivalence

/- accepted add_to_file helper 36 -/
namespace MarkingEquivalence

lemma marking_equiv_hd2 {n d k r : ℕ} (hn : 0 < n) (hd2 : 1 < d)
    (μ ν : MMarking n d k r) (hμ : mirreducible μ) (hν : mirreducible ν) :
    Relation.ReflTransGen MMove μ ν := by
  let hd : 0 < d := Nat.lt_trans Nat.zero_lt_one hd2
  obtain ⟨μ₁, hμpath, hμ₁, hμstar⟩ := starify hn hd μ hμ
  obtain ⟨ν₁, hνpath, hν₁, hνstar⟩ := starify hn hd ν hν
  have hmid : Relation.ReflTransGen MMove μ₁ ν₁ :=
    star_unmarked_equiv (k := k) hn (hd2 := hd2) μ₁ ν₁ hμstar hνstar
  have hνback : Relation.ReflTransGen MMove ν₁ ν :=
    Relation.ReflTransGen.symmetric MMove.symmetric hνpath
  exact hμpath.trans (hmid.trans hνback)

end MarkingEquivalence

/- verified submission -/
theorem marking_equivalence
    (n d k r : ℕ) (hn : 0 < n) :
    let V := Fin d ⊕ Fin k
    let E := ({p : Fin d × Fin d // p.1 < p.2} × Fin n) ⊕ (Fin d × Fin k)
    let ends : E → Sym2 V := fun e =>
      match e with
      | Sum.inl x => Sym2.mk (Sum.inl x.1.val.1 : V) (Sum.inl x.1.val.2 : V)
      | Sum.inr x => Sym2.mk (Sum.inl x.1 : V) (Sum.inr x.2 : V)
    let Marking := {μ : Fin r → E // Function.Injective μ}
    let irreducible : Marking → Prop := fun μ =>
      (SimpleGraph.fromRel (fun u v : V =>
        ∃ e : E, e ∉ Set.range μ.1 ∧ ends e = Sym2.mk u v)).Connected
    let DMove : Marking → Marking → Prop := fun μ ν =>
      ∃ a b : E, a ≠ b ∧ ends a = ends b ∧
        ν.1 = fun i => Equiv.swap a b (μ.1 i)
    let TMove : Marking → Marking → Prop := fun μ ν =>
      ∃ D D' D'' : V,
        D ≠ D' ∧ D ≠ D'' ∧ D' ≠ D'' ∧
        ∃ q q' q'' : E,
          ends q = Sym2.mk D' D'' ∧
          ends q' = Sym2.mk D D'' ∧
          ends q'' = Sym2.mk D D' ∧
          ν.1 = if q' ∈ Set.range μ.1 then μ.1
            else fun i => Equiv.swap q q'' (μ.1 i)
    let Move : Marking → Marking → Prop := fun μ ν => DMove μ ν ∨ TMove μ ν
    ∀ μ ν : Marking, irreducible μ → irreducible ν →
      Relation.ReflTransGen Move μ ν := by
  intro V E ends Marking irreducible DMove TMove Move μ ν hμ hν
  change MarkingEquivalence.mirreducible μ at hμ
  change MarkingEquivalence.mirreducible ν at hν
  change Relation.ReflTransGen (MarkingEquivalence.MMove (n:=n) (d:=d) (k:=k) (r:=r)) μ ν
  by_cases hd0 : d = 0
  · subst d
    have hEq := MarkingEquivalence.d0_markings_eq (n:=n) (k:=k) (r:=r) μ ν
    rw [hEq]
  · by_cases hd1 : d = 1
    · subst d
      have hEq := MarkingEquivalence.d1_markings_eq (n:=n) (k:=k) (r:=r) μ ν hμ hν
      rw [hEq]
    · have hd2 : 1 < d := by omega
      exact MarkingEquivalence.marking_equiv_hd2 (n:=n) (d:=d) (k:=k) (r:=r) hn hd2 μ ν hμ hν

end Rollout_p0256_marking_equivalence

#check_dependency_graph "Rollout_p0256_marking_equivalence.marking_equivalence" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"Relation.ReflTransGen Move μ ν\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hn\",\"statement\":\"0 < n\"},{\"name\":\"hμ\",\"statement\":\"irreducible μ\"},{\"name\":\"hν\",\"statement\":\"irreducible ν\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0256_marking_equivalence\",\"reconstructedProofSha256\":\"f546a85dd85832b60512ac83157f0aedb52d1218b94f5f6f282d4041f4f8af85\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p0256_marking_equivalence.marking_equivalence\",\"topologySha256\":\"acea382a18f4676772634e4c125bc3b8781d6f109529629ba6e047944a7af310\"}"

namespace Rollout_p0273_weighted_one_dimensional_dirichlet_lower_b

-- graph_id: p0273_weighted_one_dimensional_dirichlet_lower_b
-- topology_sha256: 85a9ca16859e3f43eb966e57535a3693c8d641cc05d9875fedaae5db579da175
/- accepted add_to_file helper 1 -/
open MeasureTheory
open scoped Interval

lemma l2_cauchy_schwarz_integral {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    {u v : X → ℝ} (hu : MeasureTheory.MemLp u 2 μ) (hv : MeasureTheory.MemLp v 2 μ) :
    (∫ x, u x * v x ∂μ) ^ 2 ≤
      (∫ x, u x ^ 2 ∂μ) * (∫ x, v x ^ 2 ∂μ) := by
  let A : ℝ := ∫ x, u x ^ 2 ∂μ
  let B : ℝ := ∫ x, v x ^ 2 ∂μ
  let I : ℝ := ∫ x, u x * v x ∂μ
  have hu2 : MeasureTheory.Integrable (fun x => u x ^ 2) μ := hu.integrable_sq
  have hv2 : MeasureTheory.Integrable (fun x => v x ^ 2) μ := hv.integrable_sq
  have huv : MeasureTheory.Integrable (fun x => u x * v x) μ := hu.integrable_mul hv
  have hquad (t : ℝ) : 0 ≤ t ^ 2 * A - 2 * t * I + B := by
    have hnon : 0 ≤ ∫ x, (t * u x - v x) ^ 2 ∂μ := by
      exact MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
    have hexp : (∫ x, (t * u x - v x) ^ 2 ∂μ) = t ^ 2 * A - 2 * t * I + B := by
      calc
        (∫ x, (t * u x - v x) ^ 2 ∂μ)
            = ∫ x, (t ^ 2 * (u x ^ 2) + (-(2 * t)) * (u x * v x)) + v x ^ 2 ∂μ := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              ring
        _ = (∫ x, t ^ 2 * (u x ^ 2) + (-(2 * t)) * (u x * v x) ∂μ) + ∫ x, v x ^ 2 ∂μ := by
          exact MeasureTheory.integral_add ((hu2.const_mul (t ^ 2)).add (huv.const_mul (-(2 * t)))) hv2
        _ = ((∫ x, t ^ 2 * (u x ^ 2) ∂μ) + ∫ x, (-(2 * t)) * (u x * v x) ∂μ) + ∫ x, v x ^ 2 ∂μ := by
          rw [MeasureTheory.integral_add (hu2.const_mul (t ^ 2)) (huv.const_mul (-(2 * t)))]
        _ = t ^ 2 * A - 2 * t * I + B := by
          rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
          dsimp [A, B, I]
          ring
    rwa [hexp] at hnon
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  change I ^ 2 ≤ A * B
  by_cases hAeq : A = 0
  · have hIeq : I = 0 := by
      by_contra hI0
      have ht := hquad ((B + 1) / (2 * I))
      rw [hAeq] at ht
      have hcalc : ((B + 1) / (2 * I)) ^ 2 * 0 - 2 * ((B + 1) / (2 * I)) * I + B = -1 := by
        field_simp [hI0]
        ring_nf
      linarith
    rw [hAeq, hIeq]
    simp
  · have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hAeq)
    have ht := hquad (I / A)
    have hcalc : (I / A) ^ 2 * A - 2 * (I / A) * I + B = B - I ^ 2 / A := by
      field_simp [hAeq]
      ring_nf
    rw [hcalc] at ht
    have hmul := mul_nonneg ht hApos.le
    have hcalc2 : (B - I ^ 2 / A) * A = B * A - I ^ 2 := by
      field_simp [hAeq]
    rw [hcalc2] at hmul
    nlinarith

/- accepted add_to_file helper 2 -/
lemma integral_inv_eq_of_two_valued_on_interval
    (b θ₀ : ℝ) (α : ℝ → ℝ)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hθ0 : 0 < θ₀) (hθ1 : θ₀ < 2 * Real.pi)
    (hαmeas : AEMeasurable α
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))))
    (hαvalues : ∀ᵐ θ ∂(MeasureTheory.volume.restrict
      (Set.Icc (0 : ℝ) (2 * Real.pi))), α θ ∈ ({b ^ 2, 1} : Set ℝ))
    (hαmeasure : (MeasureTheory.volume.restrict
      (Set.Icc (0 : ℝ) (2 * Real.pi))) {θ | α θ = b ^ 2} = ENNReal.ofReal θ₀) :
    ∫ θ, (α θ)⁻¹ ∂(MeasureTheory.volume.restrict
      (Set.Icc (0 : ℝ) (2 * Real.pi))) =
      2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1) := by
  classical
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict
    (Set.Icc (0 : ℝ) (2 * Real.pi))
  let β : ℝ → ℝ := AEMeasurable.mk α hαmeas
  let A : Set ℝ := {θ | β θ = b ^ 2}
  let q : ℝ → ℝ := A.piecewise (fun _ => (b ^ 2)⁻¹) (fun _ => 1)
  have hβmeas : Measurable β := hαmeas.measurable_mk
  have hA : MeasurableSet A := hβmeas (measurableSet_singleton _)
  have hβae : α =ᵐ[μ] β := hαmeas.ae_eq_mk
  have hβvalues : ∀ᵐ θ ∂μ, β θ ∈ ({b ^ 2, 1} : Set ℝ) := by
    filter_upwards [hαvalues, hβae] with θ hθ h_eq
    simpa [h_eq] using hθ
  have hsets : ({θ | α θ = b ^ 2} : Set ℝ) =ᵐ[μ] A := by
    filter_upwards [hβae] with θ h_eq
    apply propext
    constructor
    · intro h
      change β θ = b ^ 2
      rw [← h_eq]
      exact h
    · intro h
      change α θ = b ^ 2
      rw [h_eq]
      exact h
  have hAmeasure : μ A = ENNReal.ofReal θ₀ := by
    rw [← MeasureTheory.measure_congr hsets]
    exact hαmeasure
  have hμuniv : μ Set.univ = ENNReal.ofReal (2 * Real.pi) := by
    dsimp [μ]
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Icc]
    congr 1
    ring
  have hAfin : μ A ≠ ⊤ := by
    rw [hAmeasure]
    simp
  have hAcomp : μ Aᶜ = ENNReal.ofReal (2 * Real.pi - θ₀) := by
    rw [MeasureTheory.measure_compl hA hAfin, hμuniv, hAmeasure,
      ← ENNReal.ofReal_sub _ hθ0.le]
  have hAreal : μ.real A = θ₀ := by
    rw [MeasureTheory.measureReal_def, hAmeasure, ENNReal.toReal_ofReal hθ0.le]
  have hAcompreal : μ.real Aᶜ = 2 * Real.pi - θ₀ := by
    rw [MeasureTheory.measureReal_def, hAcomp,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hθ1.le)]
  have hαβinv : (fun θ => (α θ)⁻¹) =ᵐ[μ] (fun θ => (β θ)⁻¹) := by
    filter_upwards [hβae] with θ h_eq
    rw [h_eq]
  have hb2lt1 : b ^ 2 < 1 := by nlinarith
  have hb2ne1 : b ^ 2 ≠ 1 := ne_of_lt hb2lt1
  have hβq : (fun θ => (β θ)⁻¹) =ᵐ[μ] q := by
    filter_upwards [hβvalues] with θ hθ
    rcases hθ with hθ | hθ
    · have hmem : θ ∈ A := hθ
      simpa [q, hθ] using
        (Set.piecewise_eq_of_mem A (fun _ : ℝ => (b ^ 2)⁻¹) (fun _ : ℝ => 1) hmem).symm
    · have hθeq : β θ = 1 := by simpa using hθ
      have hnot : θ ∉ A := by
        intro hmem
        dsimp [A] at hmem
        rw [hθeq] at hmem
        exact hb2ne1 hmem.symm
      simpa [q, hθeq] using
        (Set.piecewise_eq_of_notMem A (fun _ : ℝ => (b ^ 2)⁻¹) (fun _ : ℝ => 1) hnot).symm
  have hic : MeasureTheory.IntegrableOn (fun _ : ℝ => (b ^ 2)⁻¹) A μ :=
    (integrable_const _).integrableOn
  have hid : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Aᶜ μ :=
    (integrable_const _).integrableOn
  calc
    ∫ θ, (α θ)⁻¹ ∂μ = ∫ θ, (β θ)⁻¹ ∂μ :=
      MeasureTheory.integral_congr_ae hαβinv
    _ = ∫ θ, q θ ∂μ := MeasureTheory.integral_congr_ae hβq
    _ = (∫ θ in A, (b ^ 2)⁻¹ ∂μ) + ∫ θ in Aᶜ, (1 : ℝ) ∂μ := by
      dsimp [q]
      exact MeasureTheory.integral_piecewise hA hic hid
    _ = μ.real A * (b ^ 2)⁻¹ + μ.real Aᶜ := by
      rw [MeasureTheory.setIntegral_const, MeasureTheory.setIntegral_const]
      simp [smul_eq_mul]
    _ = 2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1) := by
      rw [hAreal, hAcompreal]
      ring

/- accepted add_to_file helper 3 -/
lemma weighted_l1_sq_le_weighted_l2_mul_inv
    {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    [MeasureTheory.IsFiniteMeasure μ]
    (b : ℝ) (α g : X → ℝ)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hαmeas : AEMeasurable α μ)
    (hαvalues : ∀ᵐ x ∂μ, α x ∈ ({b ^ 2, 1} : Set ℝ))
    (hg : MeasureTheory.MemLp g 2 μ) :
    (∫ x, |g x| ∂μ) ^ 2 ≤
      (∫ x, α x * |g x| ^ 2 ∂μ) * ∫ x, (α x)⁻¹ ∂μ := by
  let u : X → ℝ := fun x => √(α x) * |g x|
  let v : X → ℝ := fun x => √((α x)⁻¹)
  have hαpos_of_val : ∀ {x : X}, α x ∈ ({b ^ 2, 1} : Set ℝ) → 0 < α x := by
    intro x hx
    rcases hx with hx | hx
    · rw [hx]
      exact sq_pos_of_pos hb0
    · have hx1 : α x = 1 := by simpa using hx
      rw [hx1]
      norm_num
  have hu : MeasureTheory.MemLp u 2 μ := by
    apply MeasureTheory.MemLp.mono hg.abs
    · exact (hαmeas.sqrt.mul hg.aemeasurable.abs).aestronglyMeasurable
    · filter_upwards [hαvalues] with x hx
      have hsqrt_nonneg : 0 ≤ √(α x) := Real.sqrt_nonneg _
      have hsqrt_le_one : √(α x) ≤ 1 := by
        rcases hx with hx | hx
        · rw [hx, Real.sqrt_sq hb0.le]
          exact hb1.le
        · have hx1 : α x = 1 := by simpa using hx
          rw [hx1]
          simp
      dsimp [u]
      rw [abs_mul, abs_of_nonneg hsqrt_nonneg, abs_abs]
      nlinarith [abs_nonneg (g x)]
  have hv : MeasureTheory.MemLp v 2 μ := by
    apply MeasureTheory.MemLp.mono
      (MeasureTheory.memLp_const (b⁻¹) (μ := μ) (p := 2))
    · exact hαmeas.inv.sqrt.aestronglyMeasurable
    · filter_upwards [hαvalues] with x hx
      have hsqrt_le : √((α x)⁻¹) ≤ b⁻¹ := by
        rcases hx with hx | hx
        · rw [hx, Real.sqrt_inv, Real.sqrt_sq hb0.le]
        · have hx1 : α x = 1 := by simpa using hx
          rw [hx1]
          simp
          exact (one_le_inv₀ hb0).2 hb1.le
      dsimp [v]
      rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (inv_nonneg.mpr hb0.le)]
      exact hsqrt_le
  have hprod_ae : (fun x => u x * v x) =ᵐ[μ] fun x => |g x| := by
    filter_upwards [hαvalues] with x hx
    have hpos : 0 < α x := hαpos_of_val hx
    have hsqrt : √(α x) * √((α x)⁻¹) = 1 := by
      rw [Real.sqrt_inv]
      exact mul_inv_cancel₀ ((Real.sqrt_ne_zero').2 hpos)
    dsimp [u, v]
    calc
      √(α x) * |g x| * √((α x)⁻¹)
          = (√(α x) * √((α x)⁻¹)) * |g x| := by ring
      _ = |g x| := by rw [hsqrt, one_mul]
  have hCsquare_ae : (fun x => u x ^ 2) =ᵐ[μ] fun x => α x * |g x| ^ 2 := by
    filter_upwards [hαvalues] with x hx
    have hpos : 0 < α x := hαpos_of_val hx
    dsimp [u]
    rw [mul_pow, Real.sq_sqrt hpos.le]
  have hDsquare_ae : (fun x => v x ^ 2) =ᵐ[μ] fun x => (α x)⁻¹ := by
    filter_upwards [hαvalues] with x hx
    have hpos : 0 < α x := hαpos_of_val hx
    dsimp [v]
    rw [Real.sq_sqrt (inv_nonneg.mpr hpos.le)]
  have hcs := l2_cauchy_schwarz_integral hu hv
  rw [MeasureTheory.integral_congr_ae hprod_ae,
    MeasureTheory.integral_congr_ae hCsquare_ae,
    MeasureTheory.integral_congr_ae hDsquare_ae] at hcs
  exact hcs

/- verified submission -/
theorem weighted_one_dimensional_Dirichlet_lower_bound
    (b θ₀ : ℝ) (α φ : ℝ → ℝ)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hθ0 : 0 < θ₀) (hθ1 : θ₀ < 2 * Real.pi)
    (hαmeas : AEMeasurable α
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))))
    (hαbounded : MeasureTheory.MemLp α ⊤
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))))
    (hαvalues : ∀ᵐ θ ∂(MeasureTheory.volume.restrict
      (Set.Icc (0 : ℝ) (2 * Real.pi))), α θ ∈ ({b ^ 2, 1} : Set ℝ))
    (hαmeasure : (MeasureTheory.volume.restrict
      (Set.Icc (0 : ℝ) (2 * Real.pi))) {θ | α θ = b ^ 2} = ENNReal.ofReal θ₀)
    (hφac : AbsolutelyContinuousOnInterval φ 0 (2 * Real.pi))
    (hφL2 : MeasureTheory.MemLp φ 2
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))))
    (hφderivL2 : MeasureTheory.MemLp (deriv φ) 2
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))))
    (hφend : φ (2 * Real.pi) - φ 0 = 2 * Real.pi) :
    (1 / 2 : ℝ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), α θ * |deriv φ θ| ^ 2 ≥
      2 * Real.pi ^ 2 / (2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1)) := by
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict
    (Set.Icc (0 : ℝ) (2 * Real.pi))
  let L : ℝ := ∫ θ, |deriv φ θ| ∂μ
  let C : ℝ := ∫ θ, α θ * |deriv φ θ| ^ 2 ∂μ
  let D : ℝ := ∫ θ, (α θ)⁻¹ ∂μ
  have h0le : 0 ≤ 2 * Real.pi := mul_nonneg zero_le_two Real.pi_pos.le
  have hinterval_to_restrict (f : ℝ → ℝ) :
      ∫ θ in (0 : ℝ)..(2 * Real.pi), f θ = ∫ θ, f θ ∂μ := by
    rw [intervalIntegral.integral_of_le h0le]
    exact (MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioc_ae_eq_Icc' (by simp : MeasureTheory.volume ({0} : Set ℝ) = 0))).trans rfl
  have hcs : L ^ 2 ≤ C * D := by
    dsimp [L, C, D]
    exact weighted_l1_sq_le_weighted_l2_mul_inv b α (deriv φ) hb0 hb1 hαmeas hαvalues
      hφderivL2
  have hD : D = 2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1) := by
    dsimp [D, μ]
    exact integral_inv_eq_of_two_valued_on_interval b θ₀ α hb0 hb1 hθ0 hθ1
      hαmeas hαvalues hαmeasure
  have hIntg : ∫ θ, deriv φ θ ∂μ = 2 * Real.pi := by
    rw [← hinterval_to_restrict (deriv φ),
      AbsolutelyContinuousOnInterval.integral_deriv_eq_sub hφac, hφend]
  have hLlower : 2 * Real.pi ≤ L := by
    have htriangle := MeasureTheory.abs_integral_le_integral_abs (μ := μ) (f := deriv φ)
    rw [hIntg, abs_of_nonneg h0le] at htriangle
    exact htriangle
  have hLnonneg : 0 ≤ L := by
    dsimp [L]
    exact MeasureTheory.integral_nonneg fun θ => abs_nonneg (deriv φ θ)
  have hTsq_le_Lsq : (2 * Real.pi) ^ 2 ≤ L ^ 2 := by
    apply sq_le_sq.2
    rw [abs_of_nonneg h0le, abs_of_nonneg hLnonneg]
    exact hLlower
  have hCD : (2 * Real.pi) ^ 2 ≤ C * D := hTsq_le_Lsq.trans hcs
  have hb2lt1 : b ^ 2 < 1 := by nlinarith
  have hinv_gt_one : 1 < (b ^ 2)⁻¹ :=
    (one_lt_inv₀ (sq_pos_of_pos hb0)).2 hb2lt1
  have hdenpos : 0 < 2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1) := by
    nlinarith [Real.pi_pos, hθ0, hinv_gt_one]
  have hmain : 2 * Real.pi ^ 2 / (2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1)) ≤
      (1 / 2 : ℝ) * C := by
    rw [div_le_iff₀ hdenpos]
    nlinarith [hCD, hD]
  have hCeq : ∫ θ in (0 : ℝ)..(2 * Real.pi), α θ * |deriv φ θ| ^ 2 = C :=
    hinterval_to_restrict (fun θ => α θ * |deriv φ θ| ^ 2)
  rw [hCeq]
  exact hmain

end Rollout_p0273_weighted_one_dimensional_dirichlet_lower_b

#check_dependency_graph "Rollout_p0273_weighted_one_dimensional_dirichlet_lower_b.weighted_one_dimensional_Dirichlet_lower_bound" against "{\"edges\":[{\"conclusion\":{\"name\":\"h0le\",\"statement\":\"0 ≤ 2 * Real.pi\"},\"graphEdgeId\":\"h_001_h0le\",\"premises\":[],\"rawEdgeId\":\"telescope_20\"},{\"conclusion\":{\"name\":\"hcs\",\"statement\":\"L ^ 2 ≤ C * D\"},\"graphEdgeId\":\"h_003_hcs\",\"premises\":[{\"name\":\"hb0\",\"statement\":\"0 < b\"},{\"name\":\"hb1\",\"statement\":\"b < 1\"},{\"name\":\"hαmeas\",\"statement\":\"AEMeasurable α (MeasureTheory.volume.restrict (Set.Icc 0 (2 * Real.pi)))\"},{\"name\":\"hαvalues\",\"statement\":\"∀ᵐ (θ : ℝ) ∂MeasureTheory.volume.restrict (Set.Icc 0 (2 * Real.pi)), α θ ∈ {b ^ 2, 1}\"},{\"name\":\"hφderivL2\",\"statement\":\"MeasureTheory.MemLp (deriv φ) 2 (MeasureTheory.volume.restrict (Set.Icc 0 (2 * Real.pi)))\"}],\"rawEdgeId\":\"telescope_22\"},{\"conclusion\":{\"name\":\"hD\",\"statement\":\"D = 2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1)\"},\"graphEdgeId\":\"h_004_hd\",\"premises\":[{\"name\":\"hb0\",\"statement\":\"0 < b\"},{\"name\":\"hb1\",\"statement\":\"b < 1\"},{\"name\":\"hθ0\",\"statement\":\"0 < θ₀\"},{\"name\":\"hθ1\",\"statement\":\"θ₀ < 2 * Real.pi\"},{\"name\":\"hαmeas\",\"statement\":\"AEMeasurable α (MeasureTheory.volume.restrict (Set.Icc 0 (2 * Real.pi)))\"},{\"name\":\"hαvalues\",\"statement\":\"∀ᵐ (θ : ℝ) ∂MeasureTheory.volume.restrict (Set.Icc 0 (2 * Real.pi)), α θ ∈ {b ^ 2, 1}\"},{\"name\":\"hαmeasure\",\"statement\":\"(MeasureTheory.volume.restrict (Set.Icc 0 (2 * Real.pi))) {θ | α θ = b ^ 2} = ENNReal.ofReal θ₀\"}],\"rawEdgeId\":\"telescope_23\"},{\"conclusion\":{\"name\":\"hLnonneg\",\"statement\":\"0 ≤ L\"},\"graphEdgeId\":\"h_007_hlnonneg\",\"premises\":[],\"rawEdgeId\":\"telescope_26\"},{\"conclusion\":{\"name\":\"hb2lt1\",\"statement\":\"b ^ 2 < 1\"},\"graphEdgeId\":\"h_010_hb2lt1\",\"premises\":[{\"name\":\"hb0\",\"statement\":\"0 < b\"},{\"name\":\"hb1\",\"statement\":\"b < 1\"}],\"rawEdgeId\":\"telescope_29\"},{\"conclusion\":{\"name\":\"hinterval_to_restrict\",\"statement\":\"∀ (f : ℝ → ℝ), ∫ (θ : ℝ) in 0..2 * Real.pi, f θ = ∫ (θ : ℝ), f θ ∂μ\"},\"graphEdgeId\":\"h_002_hinterval_to_restrict\",\"premises\":[{\"name\":\"h0le\",\"statement\":\"0 ≤ 2 * Real.pi\"}],\"rawEdgeId\":\"telescope_21\"},{\"conclusion\":{\"name\":\"hinv_gt_one\",\"statement\":\"1 < (b ^ 2)⁻¹\"},\"graphEdgeId\":\"h_011_hinv_gt_one\",\"premises\":[{\"name\":\"hb0\",\"statement\":\"0 < b\"},{\"name\":\"hb2lt1\",\"statement\":\"b ^ 2 < 1\"}],\"rawEdgeId\":\"telescope_30\"},{\"conclusion\":{\"name\":\"hIntg\",\"statement\":\"∫ (θ : ℝ), deriv φ θ ∂μ = 2 * Real.pi\"},\"graphEdgeId\":\"h_005_hintg\",\"premises\":[{\"name\":\"hφac\",\"statement\":\"AbsolutelyContinuousOnInterval φ 0 (2 * Real.pi)\"},{\"name\":\"hφend\",\"statement\":\"φ (2 * Real.pi) - φ 0 = 2 * Real.pi\"},{\"name\":\"hinterval_to_restrict\",\"statement\":\"∀ (f : ℝ → ℝ), ∫ (θ : ℝ) in 0..2 * Real.pi, f θ = ∫ (θ : ℝ), f θ ∂μ\"}],\"rawEdgeId\":\"telescope_24\"},{\"conclusion\":{\"name\":\"hdenpos\",\"statement\":\"0 < 2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1)\"},\"graphEdgeId\":\"h_012_hdenpos\",\"premises\":[{\"name\":\"hb0\",\"statement\":\"0 < b\"},{\"name\":\"hb1\",\"statement\":\"b < 1\"},{\"name\":\"hθ0\",\"statement\":\"0 < θ₀\"},{\"name\":\"hθ1\",\"statement\":\"θ₀ < 2 * Real.pi\"},{\"name\":\"hinv_gt_one\",\"statement\":\"1 < (b ^ 2)⁻¹\"}],\"rawEdgeId\":\"telescope_31\"},{\"conclusion\":{\"name\":\"hCeq\",\"statement\":\"∫ (θ : ℝ) in 0..2 * Real.pi, α θ * |deriv φ θ| ^ 2 = C\"},\"graphEdgeId\":\"h_014_hceq\",\"premises\":[{\"name\":\"hinterval_to_restrict\",\"statement\":\"∀ (f : ℝ → ℝ), ∫ (θ : ℝ) in 0..2 * Real.pi, f θ = ∫ (θ : ℝ), f θ ∂μ\"}],\"rawEdgeId\":\"telescope_33\"},{\"conclusion\":{\"name\":\"hLlower\",\"statement\":\"2 * Real.pi ≤ L\"},\"graphEdgeId\":\"h_006_hllower\",\"premises\":[{\"name\":\"h0le\",\"statement\":\"0 ≤ 2 * Real.pi\"},{\"name\":\"hIntg\",\"statement\":\"∫ (θ : ℝ), deriv φ θ ∂μ = 2 * Real.pi\"}],\"rawEdgeId\":\"telescope_25\"},{\"conclusion\":{\"name\":\"hTsq_le_Lsq\",\"statement\":\"(2 * Real.pi) ^ 2 ≤ L ^ 2\"},\"graphEdgeId\":\"h_008_htsq_le_lsq\",\"premises\":[{\"name\":\"h0le\",\"statement\":\"0 ≤ 2 * Real.pi\"},{\"name\":\"hLlower\",\"statement\":\"2 * Real.pi ≤ L\"},{\"name\":\"hLnonneg\",\"statement\":\"0 ≤ L\"}],\"rawEdgeId\":\"telescope_27\"},{\"conclusion\":{\"name\":\"hmain\",\"statement\":\"2 * Real.pi ^ 2 / (2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1)) ≤ 1 / 2 * C\"},\"graphEdgeId\":\"h_013_hmain\",\"premises\":[{\"name\":\"hcs\",\"statement\":\"L ^ 2 ≤ C * D\"},{\"name\":\"hD\",\"statement\":\"D = 2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1)\"},{\"name\":\"hTsq_le_Lsq\",\"statement\":\"(2 * Real.pi) ^ 2 ≤ L ^ 2\"},{\"name\":\"hdenpos\",\"statement\":\"0 < 2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1)\"}],\"rawEdgeId\":\"telescope_32\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"1 / 2 * ∫ (θ : ℝ) in 0..2 * Real.pi, α θ * |deriv φ θ| ^ 2 ≥ 2 * Real.pi ^ 2 / (2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1))\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hmain\",\"statement\":\"2 * Real.pi ^ 2 / (2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1)) ≤ 1 / 2 * C\"},{\"name\":\"hCeq\",\"statement\":\"∫ (θ : ℝ) in 0..2 * Real.pi, α θ * |deriv φ θ| ^ 2 = C\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0273_weighted_one_dimensional_dirichlet_lower_b\",\"reconstructedProofSha256\":\"8daa9f8974782856b2931c1224f8e532c59705f96566c59000509963506c6f6b\",\"selectedEdgeCount\":14,\"theoremName\":\"Rollout_p0273_weighted_one_dimensional_dirichlet_lower_b.weighted_one_dimensional_Dirichlet_lower_bound\",\"topologySha256\":\"85a9ca16859e3f43eb966e57535a3693c8d641cc05d9875fedaae5db579da175\"}"

namespace Rollout_p0292_two_positive_roots_of_mu

-- graph_id: p0292_two_positive_roots_of_mu
-- topology_sha256: 50cc4749c4529bb764e87d2981f6c706ea22d32a28e9d891791887fe92f80b47
/- accepted add_to_file helper 1 -/
lemma deriv_hump_factor (k : ℕ) (hk : 0 < k) (lam x : ℝ) :
    deriv (fun x : ℝ => x ^ k - lam * x ^ (k + 2)) x =
      x ^ (k - 1) * ((k : ℝ) - lam * (k + 2 : ℝ) * x ^ 2) := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ k) ((k : ℝ) * x ^ (k - 1)) x := by
    simpa using hasDerivAt_pow k x
  have h2 : HasDerivAt (fun x : ℝ => x ^ (k+2)) ((k+2 : ℝ) * x ^ (k+1)) x := by
    simpa using hasDerivAt_pow (k+2) x
  have hd := h1.sub (h2.const_mul lam)
  change deriv ((fun x : ℝ => x ^ k) - (fun x : ℝ => lam * x ^ (k + 2))) x = _
  rw [hd.deriv]
  have hk' : k + 1 = k - 1 + 2 := by omega
  rw [hk']
  rw [pow_add]
  ring

/- accepted add_to_file helper 2 -/
lemma hump_strictMono_on_left (k : ℕ) (hk : 0 < k) {lam : ℝ} (hlam : 0 < lam) :
    StrictMonoOn (fun x : ℝ => x ^ k - lam * x ^ (k + 2))
      (Set.Icc 0 (Real.sqrt ((k : ℝ) / (lam * (k + 2 : ℝ))))) := by
  let c := Real.sqrt ((k : ℝ) / (lam * (k + 2 : ℝ)))
  have hdiff : Differentiable ℝ (fun x : ℝ => x ^ k - lam * x ^ (k + 2)) := by
    exact (differentiable_pow k).sub ((differentiable_pow (k+2)).const_mul lam)
  apply strictMonoOn_of_deriv_pos (D := Set.Icc 0 c) (convex_Icc 0 c)
  · exact hdiff.continuous.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hcsq : c ^ 2 = (k : ℝ) / (lam * (k + 2 : ℝ)) := by
      dsimp [c]
      exact Real.sq_sqrt (by positivity)
    have hxsq : x ^ 2 < c ^ 2 := by
      rw [sq_lt_sq, abs_of_pos hx.1, abs_of_pos]
      · exact hx.2
      · dsimp [c]
        positivity
    have hcoef : 0 < lam * (k + 2 : ℝ) := by positivity
    have hfactor : 0 < (k : ℝ) - lam * (k + 2 : ℝ) * x ^ 2 := by
      have hmul := mul_lt_mul_of_pos_left hxsq hcoef
      rw [hcsq] at hmul
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      field_simp at hmul
      nlinarith
    rw [deriv_hump_factor k hk]
    exact mul_pos (pow_pos hx.1 _) hfactor

lemma hump_strictAnti_on_right (k : ℕ) (hk : 0 < k) {lam : ℝ} (hlam : 0 < lam) :
    StrictAntiOn (fun x : ℝ => x ^ k - lam * x ^ (k + 2))
      (Set.Icc (Real.sqrt ((k : ℝ) / (lam * (k + 2 : ℝ)))) (1 / Real.sqrt lam)) := by
  let c := Real.sqrt ((k : ℝ) / (lam * (k + 2 : ℝ)))
  let z := 1 / Real.sqrt lam
  have hdiff : Differentiable ℝ (fun x : ℝ => x ^ k - lam * x ^ (k + 2)) := by
    exact (differentiable_pow k).sub ((differentiable_pow (k+2)).const_mul lam)
  apply strictAntiOn_of_deriv_neg (D := Set.Icc c z) (convex_Icc c z)
  · exact hdiff.continuous.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hcpos : 0 < c := by dsimp [c]; positivity
    have hxpos : 0 < x := lt_trans hcpos hx.1
    have hcsq : c ^ 2 = (k : ℝ) / (lam * (k + 2 : ℝ)) := by
      dsimp [c]
      exact Real.sq_sqrt (by positivity)
    have hxsq : c ^ 2 < x ^ 2 := by
      rw [sq_lt_sq, abs_of_pos hcpos, abs_of_pos hxpos]
      exact hx.1
    have hcoef : 0 < lam * (k + 2 : ℝ) := by positivity
    have hfactor : (k : ℝ) - lam * (k + 2 : ℝ) * x ^ 2 < 0 := by
      have hmul := mul_lt_mul_of_pos_left hxsq hcoef
      rw [hcsq] at hmul
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      field_simp at hmul
      nlinarith
    rw [deriv_hump_factor k hk]
    exact mul_neg_of_pos_of_neg (pow_pos hxpos _) hfactor

/- accepted add_to_file helper 3 -/
lemma two_roots_hump (k : ℕ) (hk : 0 < k) {M lam : ℝ} (hM : 0 < M) (hlam : 0 < lam)
    (hcond : M ^ 2 * lam ^ k < (k : ℝ) ^ k / ((k : ℝ) + 2) ^ (k + 2)) :
    ∃ r_minus r_plus : ℝ,
      0 < r_minus ∧ r_minus < r_plus ∧
      (r_minus ^ k - lam * r_minus ^ (k + 2)) = 2 * M ∧
      (r_plus ^ k - lam * r_plus ^ (k + 2)) = 2 * M ∧
      ∀ r : ℝ, 0 < r →
        (r ^ k - lam * r ^ (k + 2)) = 2 * M →
        r = r_minus ∨ r = r_plus := by
  let h : ℝ → ℝ := fun x => x ^ k - lam * x ^ (k + 2)
  let c := Real.sqrt ((k : ℝ) / (lam * (k + 2 : ℝ)))
  let z := 1 / Real.sqrt lam
  have hdiff : Differentiable ℝ h := by
    dsimp [h]
    exact (differentiable_pow k).sub ((differentiable_pow (k+2)).const_mul lam)
  have hcont : Continuous h := hdiff.continuous
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hzpos : 0 < z := by dsimp [z]; positivity
  have hcsq : c ^ 2 = (k : ℝ) / (lam * (k + 2 : ℝ)) := by
    dsimp [c]
    exact Real.sq_sqrt (by positivity)
  have hzsq : z ^ 2 = 1 / lam := by
    dsimp [z]
    rw [div_pow, Real.sq_sqrt (le_of_lt hlam)]
    norm_num
  have hcltz : c < z := by
    have hsq : c ^ 2 < z ^ 2 := by
      rw [hcsq, hzsq]
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      rw [div_lt_div_iff₀]
      · nlinarith
      · positivity
      · exact hlam
    have := sq_lt_sq.mp hsq
    rwa [abs_of_pos hcpos, abs_of_pos hzpos] at this
  have hcval : h c = c ^ k * (2 / ((k : ℝ) + 2)) := by
    dsimp [h]
    rw [pow_add]
    rw [hcsq]
    have hcoef : 0 < lam * (k + 2 : ℝ) := by positivity
    field_simp
    ring
  have hcsqid : (h c) ^ 2 * lam ^ k =
      4 * (k : ℝ) ^ k / ((k : ℝ) + 2) ^ (k + 2) := by
    have hprod : c ^ 2 * lam = (k : ℝ) / ((k : ℝ) + 2) := by
      rw [hcsq]
      have hcoef : 0 < lam * (k + 2 : ℝ) := by positivity
      field_simp
    have hpow : (c ^ k) ^ 2 * lam ^ k = ((k : ℝ) / ((k : ℝ) + 2)) ^ k := by
      calc
        (c ^ k) ^ 2 * lam ^ k = (c ^ 2) ^ k * lam ^ k := by
          rw [← pow_mul]
          rw [← pow_mul]
          rw [Nat.mul_comm k 2]
        _ = (c ^ 2 * lam) ^ k := by rw [mul_pow]
        _ = ((k : ℝ) / ((k : ℝ) + 2)) ^ k := by rw [hprod]
    calc
      (h c) ^ 2 * lam ^ k = (c ^ k * (2 / ((k : ℝ) + 2))) ^ 2 * lam ^ k := by rw [hcval]
      _ = (2 / ((k : ℝ) + 2)) ^ 2 * ((c ^ k) ^ 2 * lam ^ k) := by ring
      _ = (2 / ((k : ℝ) + 2)) ^ 2 * ((k : ℝ) / ((k : ℝ) + 2)) ^ k := by rw [hpow]
      _ = 4 * (k : ℝ) ^ k / ((k : ℝ) + 2) ^ (k + 2) := by
        rw [div_pow, div_pow]
        field_simp
        rw [pow_add]
        ring
  have hcvalue_pos : 0 < h c := by
    rw [hcval]
    positivity
  have hcmax : 2 * M < h c := by
    have h4 : (2 * M) ^ 2 * lam ^ k < 4 * (k : ℝ) ^ k / ((k : ℝ) + 2) ^ (k + 2) := by
      have hmul := mul_lt_mul_of_pos_left hcond (show (0 : ℝ) < 4 by norm_num)
      convert hmul using 1
      · ring
      · ring
    have hsquares_mul : (2 * M) ^ 2 * lam ^ k < (h c) ^ 2 * lam ^ k := by
      calc
        (2 * M) ^ 2 * lam ^ k < 4 * (k : ℝ) ^ k / ((k : ℝ) + 2) ^ (k + 2) := h4
        _ = (h c) ^ 2 * lam ^ k := hcsqid.symm
    have hsquares : (2 * M) ^ 2 < (h c) ^ 2 := by
      nlinarith [hsquares_mul, pow_pos hlam k]
    have htarget : 0 < 2 * M := by positivity
    have := sq_lt_sq.mp hsquares
    rwa [abs_of_pos htarget, abs_of_pos hcvalue_pos] at this
  have hz : h z = 0 := by
    have hzlam : lam * z ^ 2 = 1 := by
      rw [hzsq]
      field_simp
    dsimp [h]
    rw [pow_add]
    nlinarith [pow_pos hzpos k]
  obtain ⟨r_minus, hrminusI, hrminus_eq⟩ := by
    have hmem : 2 * M ∈ Set.Ioo (h 0) (h c) := by
      have h0 : h 0 = 0 := by
        dsimp [h]
        simp [Nat.ne_zero_of_lt hk]
      rw [h0]
      exact ⟨by positivity, hcmax⟩
    have himg := intermediate_value_Ioo (show 0 ≤ c from le_of_lt hcpos) hcont.continuousOn hmem
    simpa [Set.mem_image] using himg
  obtain ⟨r_plus, hrplusI, hrplus_eq⟩ := by
    have hmem : 2 * M ∈ Set.Ioo (h z) (h c) := by
      rw [hz]
      exact ⟨by positivity, hcmax⟩
    have himg := intermediate_value_Ioo' (show c ≤ z from le_of_lt hcltz) hcont.continuousOn hmem
    simpa [Set.mem_image] using himg
  refine ⟨r_minus, r_plus, hrminusI.1, lt_trans hrminusI.2 hrplusI.1, ?_, ?_, ?_⟩
  · simpa [h] using hrminus_eq
  · simpa [h] using hrplus_eq
  · intro r hrpos hr_eq
    have hr_eq_h : h r = 2 * M := by simpa [h] using hr_eq
    have hleft : StrictMonoOn h (Set.Icc 0 c) := by
      simpa [h, c] using hump_strictMono_on_left k hk hlam
    have hright : StrictAntiOn h (Set.Icc c z) := by
      simpa [h, c, z] using hump_strictAnti_on_right k hk hlam
    have hform : h r = r ^ k * (1 - lam * r ^ 2) := by
      dsimp [h]
      rw [pow_add]
      ring
    have hprodpos : 0 < r ^ k * (1 - lam * r ^ 2) := by
      rw [← hform, hr_eq_h]
      positivity
    have hfactorpos : 0 < 1 - lam * r ^ 2 := by
      nlinarith [hprodpos, pow_pos hrpos k]
    have hrsq : r ^ 2 < z ^ 2 := by
      rw [hzsq]
      rw [lt_div_iff₀ hlam]
      nlinarith
    have hrltz : r < z := by
      have := sq_lt_sq.mp hrsq
      rwa [abs_of_pos hrpos, abs_of_pos hzpos] at this
    rcases lt_trichotomy r c with hrc | rfl | hrc
    · left
      apply hleft.injOn
      · exact ⟨le_of_lt hrpos, le_of_lt hrc⟩
      · exact ⟨le_of_lt hrminusI.1, le_of_lt hrminusI.2⟩
      · rw [hr_eq_h, hrminus_eq]
    · exfalso
      linarith
    · right
      apply hright.injOn
      · exact ⟨le_of_lt hrc, le_of_lt hrltz⟩
      · exact ⟨le_of_lt hrplusI.1, le_of_lt hrplusI.2⟩
      · rw [hr_eq_h, hrplus_eq]

/- accepted add_to_file helper 4 -/
lemma hump_to_mu_nat (k : ℕ) {M lam r : ℝ} (hr : 0 < r)
    (hh : r ^ k - lam * r ^ (k + 2) = 2 * M) :
    1 - 2 * M / r ^ k - lam * r ^ 2 = 0 := by
  have hrpow : r ^ k ≠ 0 := pow_ne_zero _ hr.ne'
  have hdiv := congrArg (fun x : ℝ => x / r ^ k) hh
  rw [pow_add] at hdiv
  field_simp [hrpow] at hdiv ⊢
  linarith

lemma mu_to_hump_nat (k : ℕ) {M lam r : ℝ} (hr : 0 < r)
    (hmu : 1 - 2 * M / r ^ k - lam * r ^ 2 = 0) :
    r ^ k - lam * r ^ (k + 2) = 2 * M := by
  have hrpow : r ^ k ≠ 0 := pow_ne_zero _ hr.ne'
  have hmul := congrArg (fun x : ℝ => x * r ^ k) hmu
  field_simp [hrpow] at hmul
  rw [pow_add]
  linarith

/- verified submission -/
theorem two_positive_roots_of_mu
    (n : ℤ) (hn : 4 ≤ n)
    (M Λ : ℝ) (hM : 0 < M) (hΛ : 0 < Λ) :
    let lam : ℝ := 2 * Λ / (((n : ℝ) - 2) * ((n : ℝ) - 1))
    let mu : ℝ → ℝ := fun r ↦ 1 - 2 * M / r ^ (n - 3) - lam * r ^ 2
    M ^ 2 * lam ^ (n - 3) <
        ((n : ℝ) - 3) ^ (n - 3) / ((n : ℝ) - 1) ^ (n - 1) →
      ∃ r_minus r_plus : ℝ,
        0 < r_minus ∧ r_minus < r_plus ∧
        mu r_minus = 0 ∧ mu r_plus = 0 ∧
        ∀ r : ℝ, 0 < r → mu r = 0 → r = r_minus ∨ r = r_plus := by
  dsimp
  set lam : ℝ := 2 * Λ / (((n : ℝ) - 2) * ((n : ℝ) - 1))
  set mu : ℝ → ℝ := fun r ↦ 1 - 2 * M / r ^ (n - 3) - lam * r ^ 2
  intro hcond
  let k : ℕ := (n - 3).toNat
  have hk_nonneg : (0 : ℤ) ≤ n - 3 := by omega
  have hk_int : (k : ℤ) = n - 3 := by
    dsimp [k]
    exact Int.toNat_of_nonneg hk_nonneg
  have hk : 0 < k := by omega
  have hkR : (k : ℝ) = (n : ℝ) - 3 := by exact_mod_cast hk_int
  have hk2_int : ((k + 2 : ℕ) : ℤ) = n - 1 := by omega
  have hk2R : ((k : ℝ) + 2) = (n : ℝ) - 1 := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hk2_int
    norm_num at this
    linarith
  have hlam : 0 < lam := by
    dsimp [lam]
    have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hn2 : 0 < (n : ℝ) - 2 := by linarith
    have hn1 : 0 < (n : ℝ) - 1 := by linarith
    have hden : 0 < ((n : ℝ) - 2) * ((n : ℝ) - 1) := mul_pos hn2 hn1
    positivity
  have hcond_nat : M ^ 2 * lam ^ k <
      (k : ℝ) ^ k / ((k : ℝ) + 2) ^ (k + 2) := by
    convert hcond using 2
    · rw [← hk_int, zpow_natCast]
    · rw [← hkR, ← hk_int, zpow_natCast]
    · rw [← hk2R, ← hk2_int, zpow_natCast]
  obtain ⟨r_minus, r_plus, hrminus_pos, hr_lt, hminus_hump, hplus_hump, huniq⟩ :=
    two_roots_hump k hk hM hlam hcond_nat
  have hpowcast : ∀ r : ℝ, r ^ (n - 3) = r ^ k := by
    intro r
    rw [← hk_int, zpow_natCast]
  refine ⟨r_minus, r_plus, hrminus_pos, hr_lt, ?_, ?_, ?_⟩
  · rw [hpowcast]
    exact hump_to_mu_nat k hrminus_pos hminus_hump
  · rw [hpowcast]
    exact hump_to_mu_nat k (lt_trans hrminus_pos hr_lt) hplus_hump
  · intro r hr hmu
    rw [hpowcast] at hmu
    exact huniq r hr (mu_to_hump_nat k hr hmu)

end Rollout_p0292_two_positive_roots_of_mu

#check_dependency_graph "Rollout_p0292_two_positive_roots_of_mu.two_positive_roots_of_mu" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let lam := 2 * Λ / ((↑n - 2) * (↑n - 1)); let mu := fun r => 1 - 2 * M / r ^ (n - 3) - lam * r ^ 2; M ^ 2 * lam ^ (n - 3) < (↑n - 3) ^ (n - 3) / (↑n - 1) ^ (n - 1) → ∃ r_minus r_plus, 0 < r_minus ∧ r_minus < r_plus ∧ mu r_minus = 0 ∧ mu r_plus = 0 ∧ ∀ (r : ℝ), 0 < r → mu r = 0 → r = r_minus ∨ r = r_plus\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hn\",\"statement\":\"4 ≤ n\"},{\"name\":\"hM\",\"statement\":\"0 < M\"},{\"name\":\"hΛ\",\"statement\":\"0 < Λ\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0292_two_positive_roots_of_mu\",\"reconstructedProofSha256\":\"9ba3a700a3689acbebad016432a5db700a757f0410ce62eb406116fb0ea54f2f\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p0292_two_positive_roots_of_mu.two_positive_roots_of_mu\",\"topologySha256\":\"50cc4749c4529bb764e87d2981f6c706ea22d32a28e9d891791887fe92f80b47\"}"

namespace Rollout_p0332_weighted_pointwise_inequality_on_circle

-- graph_id: p0332_weighted_pointwise_inequality_on_circle
-- topology_sha256: 6f4bae9a03feda456d41ac3f456a5cbcdd29e3ad1446d5e45fe53e4ab70acc24
/- accepted add_to_file helper 1 -/

lemma sqrt_integral_sin_sq_half_le_pi_abs_sin {y : ℝ} (hy0 : 0 ≤ y) (hyπ : y ≤ Real.pi) :
    Real.sqrt (∫ t in (0:ℝ)..y, Real.sin (t / 2) ^ 2) ≤
      Real.pi * |Real.sin (y / 2)| := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have hpt : ∀ t ∈ Set.Icc 0 y, Real.sin (t / 2) ^ 2 ≤ (t / 2) ^ 2 := by
      intro t ht
      exact Real.sin_sq_le_sq
    have hsint : IntervalIntegrable (fun t : ℝ => Real.sin (t / 2) ^ 2) MeasureTheory.volume 0 y := by
      exact (Real.continuous_sin.comp (continuous_id.div_const 2)).pow 2 |>.intervalIntegrable 0 y
    have htint : IntervalIntegrable (fun t : ℝ => (t / 2) ^ 2) MeasureTheory.volume 0 y := by
      exact (continuous_id.div_const 2).pow 2 |>.intervalIntegrable 0 y
    have hA : ∫ t in (0:ℝ)..y, Real.sin (t / 2) ^ 2 ≤ ∫ t in (0:ℝ)..y, (t / 2) ^ 2 :=
      intervalIntegral.integral_mono_on hy0 hsint htint hpt
    have hcalc : ∫ t in (0:ℝ)..y, (t / 2) ^ 2 = y ^ 3 / 12 := by
      have hcongr : Set.EqOn (fun t : ℝ => (t / 2) ^ 2) (fun t => (1 / 4 : ℝ) * t ^ 2) (Set.uIcc 0 y) := by
        intro t ht
        ring
      calc
        ∫ t in (0:ℝ)..y, (t / 2) ^ 2 = ∫ t in (0:ℝ)..y, (1 / 4 : ℝ) * t ^ 2 :=
          intervalIntegral.integral_congr hcongr
        _ = (1 / 4 : ℝ) * ∫ t in (0:ℝ)..y, t ^ 2 := by
          rw [intervalIntegral.integral_const_mul]
        _ = y ^ 3 / 12 := by
          rw [integral_pow]
          ring
    have hjordan0 : (2 / Real.pi) * |y / 2| ≤ |Real.sin (y / 2)| := by
      apply Real.mul_abs_le_abs_sin
      rw [abs_of_nonneg (by positivity : 0 ≤ y / 2)]
      nlinarith [Real.pi_pos]
    have hpi_lower : y ≤ Real.pi * |Real.sin (y / 2)| := by
      have habs : |y / 2| = y / 2 := abs_of_nonneg (by positivity)
      rw [habs] at hjordan0
      have hpi : 0 < Real.pi := Real.pi_pos
      have hmul := mul_le_mul_of_nonneg_left hjordan0 (le_of_lt hpi)
      field_simp at hmul ⊢
      nlinarith
    have hy_le_twelve : y ≤ 12 := by
      nlinarith [Real.pi_lt_four, hyπ]
    calc
      ∫ t in (0:ℝ)..y, Real.sin (t / 2) ^ 2 ≤ y ^ 3 / 12 := by
        rw [hcalc] at hA
        exact hA
      _ ≤ y ^ 2 := by
        nlinarith [sq_nonneg y, hy0, hy_le_twelve]
      _ ≤ (Real.pi * |Real.sin (y / 2)|) ^ 2 := by
        have hnonneg2 : 0 ≤ y := hy0
        nlinarith [mul_self_le_mul_self hnonneg2 hpi_lower]

lemma interval_deriv_norm_le_sqrt_weighted_mul_sqrt_sin_sq {f : ℝ → ℝ} {a b : ℝ}
    (hAC : AbsolutelyContinuousOnInterval f (-Real.pi) Real.pi)
    (hW : MeasureTheory.IntegrableOn
      (fun t : ℝ => |deriv f t| ^ 2 / Real.sin (t / 2) ^ 2)
      (Set.Icc (-Real.pi) Real.pi))
    (hab : a ≤ b) (ha : -Real.pi ≤ a) (hb : b ≤ Real.pi) :
    |∫ t in a..b, deriv f t| ≤
      Real.sqrt (∫ t in Set.Icc (-Real.pi) Real.pi,
        |deriv f t| ^ 2 / Real.sin (t / 2) ^ 2) *
      Real.sqrt (∫ t in a..b, Real.sin (t / 2) ^ 2) := by
  let w : ℝ → ℝ := fun t => |deriv f t| ^ 2 / Real.sin (t / 2) ^ 2
  let v : ℝ → ℝ := fun t => deriv f t / Real.sin (t / 2)
  let s : Set ℝ := Set.Ioc a b
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict s
  let A : ℝ := ∫ t in a..b, Real.sin (t / 2) ^ 2
  let I : ℝ := ∫ t in Set.Icc (-Real.pi) Real.pi, w t
  have hπ : -Real.pi ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hsub : Set.uIcc a b ⊆ Set.uIcc (-Real.pi) Real.pi := by
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le hπ]
    exact Set.Icc_subset_Icc ha hb
  have hACab : AbsolutelyContinuousOnInterval f a b := hAC.mono hsub
  have hderab : IntervalIntegrable (deriv f) MeasureTheory.volume a b :=
    hACab.intervalIntegrable_deriv
  have hnorm : |∫ t in a..b, deriv f t| ≤ ∫ t in a..b, |deriv f t| := by
    simpa [Real.norm_eq_abs] using
      (intervalIntegral.norm_integral_le_integral_norm (μ := MeasureTheory.volume)
        (f := fun t : ℝ => deriv f t) hab)
  have hderAES : MeasureTheory.AEStronglyMeasurable (deriv f) μ := by
    simpa [s, μ] using hderab.aestronglyMeasurable
  have hsinCont : Continuous fun t : ℝ => Real.sin (t / 2) :=
    Real.continuous_sin.comp (continuous_id.div_const 2)
  have hsinAES : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => Real.sin (t / 2)) μ :=
    hsinCont.aestronglyMeasurable
  have hvAES : MeasureTheory.AEStronglyMeasurable v μ := by
    simpa [v] using hderAES.div₀ hsinAES
  have hIoc_subset : Set.Ioc a b ⊆ Set.Icc (-Real.pi) Real.pi := by
    intro t ht
    constructor
    · exact le_trans ha (le_of_lt ht.1)
    · exact le_trans ht.2 hb
  have hWsub : MeasureTheory.IntegrableOn w (Set.Ioc a b) := by
    simpa [w] using hW.mono_set hIoc_subset
  have hwsq (d q : ℝ) : |d| ^ 2 / q ^ 2 = (d / q) ^ 2 := by
    by_cases hq : q = 0
    · simp [hq]
    · field_simp [hq]
      rw [sq_abs]
  have hvnormsq (d q : ℝ) : ‖d / q‖ ^ (2 : ℝ) = |d| ^ 2 / q ^ 2 := by
    calc
      ‖d / q‖ ^ (2 : ℝ) = ‖d / q‖ ^ 2 := by norm_num
      _ = |d| ^ 2 / q ^ 2 := by
        rw [Real.norm_eq_abs, abs_div, div_pow]
        simp [sq_abs]
  have hv2int : MeasureTheory.Integrable (fun t => v t ^ 2) μ := by
    have hEqOn : Set.EqOn w (fun t => v t ^ 2) (Set.Ioc a b) := by
      intro t ht
      simp only [w, v]
      exact hwsq (deriv f t) (Real.sin (t / 2))
    have hOn : MeasureTheory.IntegrableOn (fun t => v t ^ 2) (Set.Ioc a b) :=
      hWsub.congr_fun hEqOn measurableSet_Ioc
    simpa [μ, s] using hOn.integrable
  have hvMem : MeasureTheory.MemLp v 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hvAES).2 hv2int
  have hvMem' : MeasureTheory.MemLp v (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hvMem
  have hgMem0 : MeasureTheory.MemLp (fun t : ℝ => Real.sin (t / 2)) 2 μ := by
    apply MeasureTheory.MemLp.of_bound hsinAES 1
    filter_upwards with t
    rw [Real.norm_eq_abs]
    exact Real.abs_sin_le_one _
  have hgMem : MeasureTheory.MemLp (fun t : ℝ => Real.sin (t / 2)) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hgMem0
  have hholder := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ := μ)
    (f := v) (g := fun t : ℝ => Real.sin (t / 2)) (p := (2 : ℝ)) (q := (2 : ℝ))
    (by exact ⟨by norm_num, by norm_num, by norm_num⟩) hvMem' hgMem
  have hprod_ae : (fun t : ℝ => ‖v t‖ * ‖Real.sin (t / 2)‖) =ᵐ[μ]
      fun t => ‖deriv f t‖ := by
    filter_upwards [MeasureTheory.Measure.ae_ne μ 0,
      MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t htne ht
    have ht_lower : -Real.pi < t := lt_of_le_of_lt ha ht.1
    have hsinne : Real.sin (t / 2) ≠ 0 := by
      intro hzero
      have hlow : -Real.pi < t / 2 := by nlinarith [ht_lower, Real.pi_pos]
      have hhigh : t / 2 < Real.pi := by nlinarith [ht.2, hb, Real.pi_pos]
      have htzero : t = 0 := by
        have hhalf : t / 2 = 0 := (Real.sin_eq_zero_iff_of_lt_of_lt hlow hhigh).mp hzero
        linarith
      exact htne htzero
    simp only [v]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, ← abs_mul,
      div_mul_cancel₀ _ hsinne]
  have hprodint : (∫ t, ‖v t‖ * ‖Real.sin (t / 2)‖ ∂μ) =
      ∫ t in a..b, |deriv f t| := by
    calc
      (∫ t, ‖v t‖ * ‖Real.sin (t / 2)‖ ∂μ) = ∫ t, ‖deriv f t‖ ∂μ :=
        MeasureTheory.integral_congr_ae hprod_ae
      _ = ∫ t in Set.Ioc a b, |deriv f t| := by
        simp [μ, s, Real.norm_eq_abs]
      _ = ∫ t in a..b, |deriv f t| := by
        rw [← intervalIntegral.integral_of_le hab]
  have hfirst_int : (∫ t, ‖v t‖ ^ (2 : ℝ) ∂μ) ≤ I := by
    have hnonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi)] w := by
      filter_upwards with t
      simp [w]
      positivity
    have hmono : (∫ t in Set.Ioc a b, w t) ≤ I := by
      unfold I w
      exact MeasureTheory.setIntegral_mono_set hW hnonneg
        (show Set.Ioc a b ≤ᵐ[MeasureTheory.volume] Set.Icc (-Real.pi) Real.pi from
          Filter.Eventually.of_forall hIoc_subset)
    have hEqOn : Set.EqOn (fun t => ‖v t‖ ^ (2 : ℝ)) w (Set.Ioc a b) := by
      intro t ht
      simp only [w, v]
      exact hvnormsq (deriv f t) (Real.sin (t / 2))
    calc
      (∫ t, ‖v t‖ ^ (2 : ℝ) ∂μ) = ∫ t in Set.Ioc a b, w t := by
        rw [show (∫ t, ‖v t‖ ^ (2 : ℝ) ∂μ) = ∫ t in Set.Ioc a b, ‖v t‖ ^ (2 : ℝ) by rfl]
        exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hEqOn
      _ ≤ I := hmono
  have hfactor1 : (∫ t, ‖v t‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤ Real.sqrt I := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt hfirst_int
  have hsecond_int : (∫ t, ‖Real.sin (t / 2)‖ ^ (2 : ℝ) ∂μ) = A := by
    calc
      (∫ t, ‖Real.sin (t / 2)‖ ^ (2 : ℝ) ∂μ)
          = ∫ t in Set.Ioc a b, Real.sin (t / 2) ^ 2 := by
            rw [show (∫ t, ‖Real.sin (t / 2)‖ ^ (2 : ℝ) ∂μ) =
              ∫ t in Set.Ioc a b, ‖Real.sin (t / 2)‖ ^ (2 : ℝ) by rfl]
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
            intro t ht
            change ‖Real.sin (t / 2)‖ ^ 2 = Real.sin (t / 2) ^ 2
            rw [Real.norm_eq_abs]
            simp [sq_abs]
      _ = A := by
        simp only [A]
        rw [← intervalIntegral.integral_of_le hab]
  have hfactor2 : (∫ t, ‖Real.sin (t / 2)‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤ Real.sqrt A := by
    rw [hsecond_int, ← Real.sqrt_eq_rpow]
  have hfactor2_nonneg : 0 ≤ (∫ t, ‖Real.sin (t / 2)‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    positivity
  calc
    |∫ t in a..b, deriv f t| ≤ ∫ t in a..b, |deriv f t| := hnorm
    _ = ∫ t, ‖v t‖ * ‖Real.sin (t / 2)‖ ∂μ := hprodint.symm
    _ ≤ (∫ t, ‖v t‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (∫ t, ‖Real.sin (t / 2)‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hholder
    _ ≤ Real.sqrt I * Real.sqrt A :=
      mul_le_mul hfactor1 hfactor2 hfactor2_nonneg (Real.sqrt_nonneg I)
    _ = Real.sqrt (∫ t in Set.Icc (-Real.pi) Real.pi,
        |deriv f t| ^ 2 / Real.sin (t / 2) ^ 2) *
        Real.sqrt (∫ t in a..b, Real.sin (t / 2) ^ 2) := by
      simp [I, A, w]

lemma pointwise_weighted_bound_on_circle {f : ℝ → ℝ} {x : ℝ}
    (hAC : AbsolutelyContinuousOnInterval f (-Real.pi) Real.pi)
    (hf0 : f 0 = 0)
    (hW : MeasureTheory.IntegrableOn
      (fun t : ℝ => |deriv f t| ^ 2 / Real.sin (t / 2) ^ 2)
      (Set.Icc (-Real.pi) Real.pi))
    (hxl : -Real.pi ≤ x) (hxu : x ≤ Real.pi) :
    |f x| ≤ Real.pi * |Real.sin (x / 2)| *
      Real.sqrt (∫ t in Set.Icc (-Real.pi) Real.pi,
        |deriv f t| ^ 2 / Real.sin (t / 2) ^ 2) := by
  let I : ℝ := ∫ t in Set.Icc (-Real.pi) Real.pi,
    |deriv f t| ^ 2 / Real.sin (t / 2) ^ 2
  rcases le_total 0 x with hx0 | hx0
  · have hπ : -Real.pi ≤ Real.pi := by nlinarith [Real.pi_pos]
    have hsub : Set.uIcc 0 x ⊆ Set.uIcc (-Real.pi) Real.pi := by
      rw [Set.uIcc_of_le hx0, Set.uIcc_of_le hπ]
      exact Set.Icc_subset_Icc (neg_nonpos.mpr Real.pi_nonneg) hxu
    have hACx : AbsolutelyContinuousOnInterval f 0 x := hAC.mono hsub
    have hftc : ∫ t in (0:ℝ)..x, deriv f t = f x := by
      have h := hACx.integral_deriv_eq_sub
      rw [hf0] at h
      simpa using h
    have hcs : |f x| ≤ Real.sqrt I *
        Real.sqrt (∫ t in (0:ℝ)..x, Real.sin (t / 2) ^ 2) := by
      have h := interval_deriv_norm_le_sqrt_weighted_mul_sqrt_sin_sq hAC hW hx0
        (neg_nonpos.mpr Real.pi_nonneg) hxu
      rw [hftc] at h
      simpa [I] using h
    have hkernel := sqrt_integral_sin_sq_half_le_pi_abs_sin hx0 hxu
    calc
      |f x| ≤ Real.sqrt I *
        Real.sqrt (∫ t in (0:ℝ)..x, Real.sin (t / 2) ^ 2) := hcs
      _ ≤ Real.sqrt I * (Real.pi * |Real.sin (x / 2)|) :=
        mul_le_mul_of_nonneg_left hkernel (Real.sqrt_nonneg I)
      _ = Real.pi * |Real.sin (x / 2)| * Real.sqrt I := by
        ring
      _ = Real.pi * |Real.sin (x / 2)| *
          Real.sqrt (∫ t in Set.Icc (-Real.pi) Real.pi,
            |deriv f t| ^ 2 / Real.sin (t / 2) ^ 2) := by
        simp [I]
  · have hy0 : 0 ≤ -x := by linarith
    have hyπ : -x ≤ Real.pi := by linarith
    have hπ : -Real.pi ≤ Real.pi := by nlinarith [Real.pi_pos]
    have hsub : Set.uIcc x 0 ⊆ Set.uIcc (-Real.pi) Real.pi := by
      rw [Set.uIcc_of_le hx0, Set.uIcc_of_le hπ]
      exact Set.Icc_subset_Icc hxl (by positivity)
    have hACx : AbsolutelyContinuousOnInterval f x 0 := hAC.mono hsub
    have hftc : ∫ t in x..0, deriv f t = -f x := by
      have h := hACx.integral_deriv_eq_sub
      rw [hf0] at h
      simpa using h
    have hsin_even : ∫ t in x..0, Real.sin (t / 2) ^ 2 =
        ∫ t in (0:ℝ)..(-x), Real.sin (t / 2) ^ 2 := by
      have hcomp := intervalIntegral.integral_comp_neg
        (fun t : ℝ => Real.sin (t / 2) ^ 2) (a := x) (b := 0)
      have hcongr : Set.EqOn (fun t : ℝ => Real.sin (-t / 2) ^ 2)
          (fun t : ℝ => Real.sin (t / 2) ^ 2) (Set.uIcc x 0) := by
        intro t ht
        change Real.sin (-t / 2) ^ 2 = Real.sin (t / 2) ^ 2
        have : Real.sin (-t / 2) = -Real.sin (t / 2) := by
          rw [show -t / 2 = -(t / 2) by ring, Real.sin_neg]
        rw [this, neg_sq]
      calc
        ∫ t in x..0, Real.sin (t / 2) ^ 2 =
            ∫ t in x..0, Real.sin (-t / 2) ^ 2 := by
          exact (intervalIntegral.integral_congr hcongr).symm
        _ = ∫ t in -0..-x, Real.sin (t / 2) ^ 2 := hcomp
        _ = ∫ t in (0:ℝ)..(-x), Real.sin (t / 2) ^ 2 := by simp
    have hcs : |f x| ≤ Real.sqrt I *
        Real.sqrt (∫ t in x..0, Real.sin (t / 2) ^ 2) := by
      have h := interval_deriv_norm_le_sqrt_weighted_mul_sqrt_sin_sq hAC hW hx0 hxl
        (by positivity)
      rw [hftc, abs_neg] at h
      simpa [I] using h
    have hkernel := sqrt_integral_sin_sq_half_le_pi_abs_sin hy0 hyπ
    have hsin_abs : |Real.sin ((-x) / 2)| = |Real.sin (x / 2)| := by
      rw [show (-x) / 2 = -(x / 2) by ring, Real.sin_neg, abs_neg]
    rw [hsin_abs] at hkernel
    calc
      |f x| ≤ Real.sqrt I *
        Real.sqrt (∫ t in x..0, Real.sin (t / 2) ^ 2) := hcs
      _ = Real.sqrt I *
        Real.sqrt (∫ t in (0:ℝ)..(-x), Real.sin (t / 2) ^ 2) := by
        rw [hsin_even]
      _ ≤ Real.sqrt I * (Real.pi * |Real.sin (x / 2)|) :=
        mul_le_mul_of_nonneg_left hkernel (Real.sqrt_nonneg I)
      _ = Real.pi * |Real.sin (x / 2)| * Real.sqrt I := by
        ring
      _ = Real.pi * |Real.sin (x / 2)| *
          Real.sqrt (∫ t in Set.Icc (-Real.pi) Real.pi,
            |deriv f t| ^ 2 / Real.sin (t / 2) ^ 2) := by
        simp [I]

/- verified submission -/
theorem weighted_pointwise_inequality_on_circle :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : ℝ → ℝ,
        Function.Periodic f (2 * Real.pi) →
        AbsolutelyContinuousOnInterval f (-Real.pi) Real.pi →
        f 0 = 0 →
        MeasureTheory.IntegrableOn
          (fun x : ℝ => |deriv f x| ^ 2 / Real.sin (x / 2) ^ 2)
          (Set.Icc (-Real.pi) Real.pi) →
        essSup
            (fun x : ℝ => |f x| / |Real.sin (x / 2)|)
            (MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi)) ≤
          C * Real.sqrt
            (∫ x in Set.Icc (-Real.pi) Real.pi,
              |deriv f x| ^ 2 / Real.sin (x / 2) ^ 2) := by
  refine ⟨Real.pi, Real.pi_pos, ?_⟩
  intro f hperiodic hAC hf0 hW
  let I : ℝ := ∫ x in Set.Icc (-Real.pi) Real.pi,
    |deriv f x| ^ 2 / Real.sin (x / 2) ^ 2
  let μ : MeasureTheory.Measure ℝ :=
    MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi)
  let B : ℝ := Real.pi * Real.sqrt I
  change essSup (fun x : ℝ => |f x| / |Real.sin (x / 2)|) μ ≤ B
  have hI_nonneg : 0 ≤ I := by
    dsimp [I]
    apply MeasureTheory.integral_nonneg
    intro x
    positivity
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hpoint : ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      |f x| / |Real.sin (x / 2)| ≤ B := by
    intro x hx
    have hbound : |f x| ≤ Real.pi * |Real.sin (x / 2)| * Real.sqrt I := by
      simpa [I] using pointwise_weighted_bound_on_circle hAC hf0 hW hx.1 hx.2
    by_cases hs : Real.sin (x / 2) = 0
    · have hle0 : |f x| ≤ 0 := by
        simpa [hs] using hbound
      have hfx0 : f x = 0 := by
        have habs0 : |f x| = 0 := le_antisymm hle0 (abs_nonneg _)
        exact abs_eq_zero.mp habs0
      have hzero : |f x| / |Real.sin (x / 2)| = 0 := by
        simp [hfx0, hs]
      rw [hzero]
      exact hB_nonneg
    · have hden : 0 < |Real.sin (x / 2)| := abs_pos.mpr hs
      rw [div_le_iff₀ hden]
      calc
        |f x| ≤ Real.pi * |Real.sin (x / 2)| * Real.sqrt I := hbound
        _ = (Real.pi * Real.sqrt I) * |Real.sin (x / 2)| := by ring
        _ = B * |Real.sin (x / 2)| := by rfl
  haveI : (MeasureTheory.ae μ).NeBot := by
    rw [MeasureTheory.ae_neBot]
    intro hμ
    change MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi) = 0 at hμ
    have hs : MeasureTheory.volume (Set.Icc (-Real.pi) Real.pi) = 0 :=
      MeasureTheory.Measure.restrict_eq_zero.mp hμ
    rw [Real.volume_Icc] at hs
    have hle := ENNReal.ofReal_eq_zero.mp hs
    nlinarith [Real.pi_pos]
  have hbelow : Filter.IsBoundedUnder (fun x y : ℝ => x ≥ y) (MeasureTheory.ae μ)
      (fun x : ℝ => |f x| / |Real.sin (x / 2)|) := by
    apply Filter.isBoundedUnder_of
    exact ⟨0, fun x => by positivity⟩
  have hcob : Filter.IsCoboundedUnder (fun x y : ℝ => x ≤ y) (MeasureTheory.ae μ)
      (fun x : ℝ => |f x| / |Real.sin (x / 2)|) := by
    simpa using hbelow.isCoboundedUnder_flip
  have hbound_ae : (fun x : ℝ => |f x| / |Real.sin (x / 2)|) ≤ᵐ[μ] fun _ => B := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with x hx
    exact hpoint x hx
  exact Filter.limsup_le_of_le (hf := hcob) hbound_ae

end Rollout_p0332_weighted_pointwise_inequality_on_circle

#check_dependency_graph "Rollout_p0332_weighted_pointwise_inequality_on_circle.weighted_pointwise_inequality_on_circle" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∃ C, 0 < C ∧ ∀ (f : ℝ → ℝ), Function.Periodic f (2 * Real.pi) → AbsolutelyContinuousOnInterval f (-Real.pi) Real.pi → f 0 = 0 → MeasureTheory.IntegrableOn (fun x => |deriv f x| ^ 2 / Real.sin (x / 2) ^ 2) (Set.Icc (-Real.pi) Real.pi) MeasureTheory.volume → essSup (fun x => |f x| / |Real.sin (x / 2)|) (MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi)) ≤ C * √(∫ (x : ℝ) in Set.Icc (-Real.pi) Real.pi, |deriv f x| ^ 2 / Real.sin (x / 2) ^ 2)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0332_weighted_pointwise_inequality_on_circle\",\"reconstructedProofSha256\":\"c0f9c4178bcae7c3b1f8f3cbc252ced0829e73ea32c869fc88c1f4e768d1783e\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p0332_weighted_pointwise_inequality_on_circle.weighted_pointwise_inequality_on_circle\",\"topologySha256\":\"6f4bae9a03feda456d41ac3f456a5cbcdd29e3ad1446d5e45fe53e4ab70acc24\"}"

namespace Rollout_p0367_weakhomotopyequivalence_of_iunion_open_res

-- graph_id: p0367_weakhomotopyequivalence_of_iunion_open_res
-- topology_sha256: d8054a5027501cba618538efb0a26a4cda17a805880f39cd49477c4e14fe5b91
/- accepted add_to_file helper 1 -/
lemma exists_cover_stage_of_isCompact
    {X : Type*} [TopologicalSpace X] {ι : Type*} [Nonempty ι]
    [Preorder ι] [IsDirectedOrder ι]
    {K : Set X} (hK : IsCompact K)
    (U : ι → Set X)
    (hU_open : ∀ n, IsOpen (U n))
    (hU_mono : Monotone U)
    (hU_cover : ⋃ n, U n = Set.univ) :
    ∃ n, K ⊆ U n := by
  refine hK.elim_directed_cover U hU_open ?_ hU_mono.directed_le
  rw [hU_cover]
  exact Set.subset_univ K

/-- Restrict a generalized loop to a subset containing its range. -/
def genLoopRestrict
    {N X : Type*} [TopologicalSpace N] [TopologicalSpace X]
    (s : Set X) {x : X} (hx : x ∈ s)
    (p : GenLoop N X x) (hp : Set.range p.1 ⊆ s) :
    GenLoop N s ⟨x, hx⟩ := by
  refine ⟨⟨fun y => ⟨p.1 y, hp ⟨y, rfl⟩⟩, ?_⟩, ?_⟩
  · exact p.1.continuous.subtype_mk (fun y => hp ⟨y, rfl⟩)
  · intro y hy
    apply Subtype.ext
    exact p.2 y hy

/-- Extend a generalized loop from a subset to the ambient space. -/
def genLoopExtend
    {N X : Type*} [TopologicalSpace N] [TopologicalSpace X]
    (s : Set X) {x : X} (hx : x ∈ s)
    (p : GenLoop N s ⟨x, hx⟩) :
    GenLoop N X x := by
  refine ⟨⟨fun y => p.1 y, continuous_subtype_val.comp p.1.continuous⟩, ?_⟩
  intro y hy
  exact congrArg Subtype.val (p.2 y hy)

/- verified submission -/
theorem weakHomotopyEquivalence_of_iUnion_open_restrictions
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y))
    (U : {n : ℕ // 1 ≤ n} → Set X)
    (hU_open : ∀ n, IsOpen (U n))
    (hU_mono : Monotone U)
    (hU_cover : ⋃ n, U n = Set.univ)
    (hf : ∀ n,
      let g : C(U n, Y) :=
        ⟨fun x => f x.1, f.continuous.comp continuous_subtype_val⟩
      Function.Bijective
          (Quotient.map g (by
            intro a b h
            exact h.map (fun p => p.map g.continuous)) :
            ZerothHomotopy (U n) → ZerothHomotopy Y) ∧
        ∀ (k : ℕ) (x : U n), Function.Bijective
          (Quotient.map
            (fun p : GenLoop (Fin (k + 1)) (U n) x =>
              (⟨g.comp p.1, by
                intro y hy
                rw [ContinuousMap.comp_apply, p.2 y hy]⟩ :
                GenLoop (Fin (k + 1)) Y (g x)))
            (by
              intro p q h
              exact h.map (fun H => H.compContinuousMap g)) :
            HomotopyGroup.Pi (k + 1) (U n) x →
              HomotopyGroup.Pi (k + 1) Y (g x))) :
    Function.Bijective
        (Quotient.map f (by
          intro a b h
          exact h.map (fun p => p.map f.continuous)) :
          ZerothHomotopy X → ZerothHomotopy Y) ∧
      ∀ (k : ℕ) (x : X), Function.Bijective
        (Quotient.map
          (fun p : GenLoop (Fin (k + 1)) X x =>
            (⟨f.comp p.1, by
              intro y hy
              rw [ContinuousMap.comp_apply, p.2 y hy]⟩ :
              GenLoop (Fin (k + 1)) Y (f x)))
          (by
            intro p q h
            exact h.map (fun H => H.compContinuousMap f)) :
          HomotopyGroup.Pi (k + 1) X x → HomotopyGroup.Pi (k + 1) Y (f x)) := by
  constructor
  · constructor
    · intro a b hab
      obtain ⟨x, rfl⟩ := Quotient.exists_rep a
      obtain ⟨y, rfl⟩ := Quotient.exists_rep b
      let K : Set X := {x, y}
      have hK : IsCompact K := by
        simp [K]
      obtain ⟨n, hnK⟩ :=
        exists_cover_stage_of_isCompact hK U hU_open hU_mono hU_cover
      have hx : x ∈ U n := hnK (by simp [K])
      have hy : y ∈ U n := hnK (by simp [K])
      let x' : U n := ⟨x, hx⟩
      let y' : U n := ⟨y, hy⟩
      let g : C(U n, Y) :=
        ⟨fun z => f z.1, f.continuous.comp continuous_subtype_val⟩
      have hlocal :
          (Quotient.map g (by
            intro a b h
            exact h.map (fun p => p.map g.continuous)) :
            ZerothHomotopy (U n) → ZerothHomotopy Y) ⟦x'⟧ =
          (Quotient.map g (by
            intro a b h
            exact h.map (fun p => p.map g.continuous)) :
            ZerothHomotopy (U n) → ZerothHomotopy Y) ⟦y'⟧ := by
        exact hab
      have hxy_local := (hf n).1.1 hlocal
      have hxy : Joined x y := by
        exact (Quotient.eq.mp hxy_local).map
          (fun p => p.map continuous_subtype_val)
      exact Quotient.eq.mpr hxy
    · intro b
      obtain ⟨y, rfl⟩ := Quotient.exists_rep b
      let n : {n : ℕ // 1 ≤ n} := ⟨1, le_rfl⟩
      obtain ⟨a, ha⟩ := (hf n).1.2 (⟦y⟧ : ZerothHomotopy Y)
      obtain ⟨x, rfl⟩ := Quotient.exists_rep a
      use (⟦x.1⟧ : ZerothHomotopy X)
      exact ha
  · intro k x
    constructor
    · intro a b hab
      obtain ⟨p, rfl⟩ := Quotient.exists_rep a
      obtain ⟨q, rfl⟩ := Quotient.exists_rep b
      let K : Set X := Set.range p.1 ∪ Set.range q.1 ∪ {x}
      have hpK : IsCompact (Set.range p.1) := isCompact_range p.1.continuous
      have hqK : IsCompact (Set.range q.1) := isCompact_range q.1.continuous
      have hK : IsCompact K := by
        unfold K
        exact (hpK.union hqK).union isCompact_singleton
      obtain ⟨n, hnK⟩ :=
        exists_cover_stage_of_isCompact hK U hU_open hU_mono hU_cover
      have hx : x ∈ U n := hnK (by simp [K])
      have hp : Set.range p.1 ⊆ U n := by
        intro z hz
        exact hnK (Set.mem_union_left {x}
          (Set.mem_union_left (Set.range q.1) hz))
      have hq : Set.range q.1 ⊆ U n := by
        intro z hz
        exact hnK (Set.mem_union_left {x}
          (Set.mem_union_right (Set.range p.1) hz))
      let x' : U n := ⟨x, hx⟩
      let pU := genLoopRestrict (U n) hx p hp
      let qU := genLoopRestrict (U n) hx q hq
      let g : C(U n, Y) :=
        ⟨fun z => f z.1, f.continuous.comp continuous_subtype_val⟩
      have hlocal :
          (Quotient.map
            (fun r : GenLoop (Fin (k + 1)) (U n) x' =>
              (⟨g.comp r.1, by
                intro y hy
                rw [ContinuousMap.comp_apply, r.2 y hy]⟩ :
                GenLoop (Fin (k + 1)) Y (g x')))
            (by
              intro r s h
              exact h.map (fun H => H.compContinuousMap g)) :
            HomotopyGroup.Pi (k + 1) (U n) x' →
              HomotopyGroup.Pi (k + 1) Y (g x')) ⟦pU⟧ =
          (Quotient.map
            (fun r : GenLoop (Fin (k + 1)) (U n) x' =>
              (⟨g.comp r.1, by
                intro y hy
                rw [ContinuousMap.comp_apply, r.2 y hy]⟩ :
                GenLoop (Fin (k + 1)) Y (g x')))
            (by
              intro r s h
              exact h.map (fun H => H.compContinuousMap g)) :
            HomotopyGroup.Pi (k + 1) (U n) x' →
              HomotopyGroup.Pi (k + 1) Y (g x')) ⟦qU⟧ := by
        exact hab
      have hpq_local := ((hf n).2 k x').1 hlocal
      have hpqX : GenLoop.Homotopic p q := by
        exact (Quotient.eq.mp hpq_local).map (fun H =>
          H.compContinuousMap
            (⟨Subtype.val, continuous_subtype_val⟩ : C(U n, X)))
      exact Quotient.eq.mpr hpqX
    · intro b
      obtain ⟨q, rfl⟩ := Quotient.exists_rep b
      let K : Set X := {x}
      have hK : IsCompact K := by
        simp [K]
      obtain ⟨n, hnK⟩ :=
        exists_cover_stage_of_isCompact hK U hU_open hU_mono hU_cover
      have hx : x ∈ U n := hnK (by simp [K])
      let x' : U n := ⟨x, hx⟩
      obtain ⟨a, ha⟩ :=
        ((hf n).2 k x').2
          (⟦q⟧ : HomotopyGroup.Pi (k + 1) Y (f x))
      obtain ⟨p, rfl⟩ := Quotient.exists_rep a
      use (⟦genLoopExtend (U n) hx p⟧ :
        HomotopyGroup.Pi (k + 1) X x)
      exact ha

end Rollout_p0367_weakhomotopyequivalence_of_iunion_open_res

#check_dependency_graph "Rollout_p0367_weakhomotopyequivalence_of_iunion_open_res.weakHomotopyEquivalence_of_iUnion_open_restrictions" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"Function.Bijective (Quotient.map ⇑f ⋯) ∧ ∀ (k : ℕ) (x : X), Function.Bijective (Quotient.map (fun p => ⟨f.comp ↑p, ⋯⟩) ⋯)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hU_open\",\"statement\":\"∀ (n : { n // 1 ≤ n }), IsOpen (U n)\"},{\"name\":\"hU_mono\",\"statement\":\"Monotone U\"},{\"name\":\"hU_cover\",\"statement\":\"⋃ n, U n = Set.univ\"},{\"name\":\"hf\",\"statement\":\"∀ (n : { n // 1 ≤ n }), let g := { toFun := fun x => f ↑x, continuous_toFun := ⋯ }; Function.Bijective (Quotient.map ⇑g ⋯) ∧ ∀ (k : ℕ) (x : ↑(U n)), Function.Bijective (Quotient.map (fun p => ⟨g.comp ↑p, ⋯⟩) ⋯)\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0367_weakhomotopyequivalence_of_iunion_open_res\",\"reconstructedProofSha256\":\"021b5d859c09bf217def9d432e626804cba028c718e90a5d7d260509c806db5b\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p0367_weakhomotopyequivalence_of_iunion_open_res.weakHomotopyEquivalence_of_iUnion_open_restrictions\",\"topologySha256\":\"d8054a5027501cba618538efb0a26a4cda17a805880f39cd49477c4e14fe5b91\"}"

namespace Rollout_p0378_finite_g_set_subcategory_contains_all_mono

-- graph_id: p0378_finite_g_set_subcategory_contains_all_mono
-- topology_sha256: c7aa6e819654a31c1b25326607ad68d547a4afb2514a948524abcfdf1173b344
/- accepted add_to_file helper 1 -/
open CategoryTheory
open CategoryTheory.Limits
namespace FiniteGSetProof
universe u
@[reducible]
def trivialMulAction (G : Type u) [Monoid G] (A : Type) : MulAction G A where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
@[reducible]
def trivialObj (G : Type u) [Monoid G] (A : Type) [Finite A] : Action (FintypeCat.{0}) G := by
  letI : MulAction G A := trivialMulAction G A
  exact Action.FintypeCat.ofMulAction G (FintypeCat.of A)
def actionHomOfEquivariant {G : Type u} [Monoid G] {X Y : Action (FintypeCat.{0}) G}
    (φ : X.V.obj → Y.V.obj)
    (hφ : ∀ g x, φ (ConcreteCategory.hom (X.ρ g) x) = ConcreteCategory.hom (Y.ρ g) (φ x)) : X ⟶ Y where
  hom := FintypeCat.homMk φ
  comm := by intro g; ext x; exact hφ g x
lemma concreteCategoryHom_actionHomOfEquivariant {G : Type u} [Monoid G]
    {X Y : Action (FintypeCat.{0}) G} (φ : X.V.obj → Y.V.obj)
    (hφ : ∀ g x, φ (ConcreteCategory.hom (X.ρ g) x) = ConcreteCategory.hom (Y.ρ g) (φ x)) :
    ConcreteCategory.hom (actionHomOfEquivariant φ hφ : X ⟶ Y) = φ := rfl
noncomputable def toTrivialObj (G : Type u) [Monoid G] (A : Type) [Finite A] [Nonempty A]
    (X : Action (FintypeCat.{0}) G) : X ⟶ trivialObj G A :=
  let a : A := Classical.choice inferInstance
  actionHomOfEquivariant (fun _ => a) (by intro g x; rfl)
def trivialMap (G : Type u) [Monoid G] {A B : Type} [Finite A] [Finite B]
    (φ : A → B) : trivialObj G A ⟶ trivialObj G B :=
  actionHomOfEquivariant φ (by intro g x; rfl)
variable (G : Type u) [Group G]
def oneObj : Action (FintypeCat.{0}) G := trivialObj G PUnit
def twoObj : Action (FintypeCat.{0}) G := trivialObj G Bool
noncomputable def oneMap {X : Action (FintypeCat) G} : X ⟶ oneObj G := toTrivialObj G PUnit X
def truth : oneObj G ⟶ twoObj G := trivialMap G (fun _ => true)
def falsehood : oneObj G ⟶ twoObj G := trivialMap G (fun _ => false)
lemma concreteCategoryHom_truth :
    ⇑(ConcreteCategory.hom (truth G)) = (fun _ : PUnit => true) := rfl
lemma concreteCategoryHom_falsehood :
    ⇑(ConcreteCategory.hom (falsehood G)) = (fun _ : PUnit => false) := rfl
noncomputable instance oneUnique (X : Action (FintypeCat) G) : Unique (X ⟶ oneObj G) where
  default := oneMap G
  uniq f := by apply Action.hom_ext; ext x; cases f x; rfl
noncomputable def oneIsTerminal : Limits.IsTerminal (oneObj G) := Limits.IsTerminal.ofUnique (oneObj G)
noncomputable abbrev initialObj : Action (FintypeCat) G := ⊥_ _
noncomputable def truthSource : Bool → Action (FintypeCat) G
  | false => initialObj G
  | true => oneObj G
def truthTarget : Bool → Action (FintypeCat) G
  | false => oneObj G
  | true => oneObj G
noncomputable def sourceCofan : Cofan (truthSource G) where
  pt := oneObj G
  ι := Discrete.natTrans fun
    | ⟨false⟩ => initial.to (oneObj G)
    | ⟨true⟩ => 𝟙 (oneObj G)
noncomputable def sourceCofanIsColimit : IsColimit (sourceCofan G) := by
  refine IsColimit.mk (fun s => s.ι.app ⟨true⟩) ?_ ?_
  · intro s j
    cases j using Discrete.casesOn with
    | mk a =>
      cases a
      · exact initial.hom_ext _ _
      · exact Category.id_comp _
  · intro s m hm
    simpa [sourceCofan] using hm ⟨true⟩
lemma from_one_apply_action {W : Action (FintypeCat) G} (h : oneObj G ⟶ W) (g : G) :
    h PUnit.unit = ConcreteCategory.hom (W.ρ g) (h PUnit.unit) := by
  have hcomm := congrArg (fun φ : (oneObj G).V ⟶ W.V =>
      ConcreteCategory.hom φ PUnit.unit) (h.comm g)
  simpa using hcomm
noncomputable def targetCofan : Cofan (truthTarget G) where
  pt := twoObj G
  ι := Discrete.natTrans fun
    | ⟨false⟩ => truth G
    | ⟨true⟩ => falsehood G
noncomputable def targetCofanIsColimit : IsColimit (targetCofan G) := by
  let desc (s : Cocone (Discrete.functor (truthTarget G))) : twoObj G ⟶ s.pt :=
    actionHomOfEquivariant
      (fun b : (twoObj G).V.obj =>
        match (show Bool from b) with
        | true => s.ι.app ⟨false⟩ PUnit.unit
        | false => s.ι.app ⟨true⟩ PUnit.unit)
      (by
        intro g b
        cases (show Bool from b)
        · exact from_one_apply_action G (s.ι.app ⟨true⟩) g
        · exact from_one_apply_action G (s.ι.app ⟨false⟩) g)
  refine IsColimit.mk desc ?_ ?_
  · intro s j
    cases j using Discrete.casesOn with
    | mk a =>
      cases a
      · apply ConcreteCategory.ext_apply
        intro x
        cases x
        rw [ConcreteCategory.comp_apply]
        change (ConcreteCategory.hom (desc s)) ((ConcreteCategory.hom (truth G)) PUnit.unit) = _
        rw [concreteCategoryHom_actionHomOfEquivariant, concreteCategoryHom_truth]
        rfl
      · apply ConcreteCategory.ext_apply
        intro x
        cases x
        rw [ConcreteCategory.comp_apply]
        change (ConcreteCategory.hom (desc s)) ((ConcreteCategory.hom (falsehood G)) PUnit.unit) = _
        rw [concreteCategoryHom_actionHomOfEquivariant, concreteCategoryHom_falsehood]
        rfl
  · intro s m hm
    apply ConcreteCategory.ext_apply
    intro b
    cases (show Bool from b)
    · have h := ConcreteCategory.congr_hom (hm ⟨true⟩) PUnit.unit
      rw [ConcreteCategory.comp_apply] at h
      change (ConcreteCategory.hom m) ((ConcreteCategory.hom (falsehood G)) PUnit.unit) = _ at h
      rw [concreteCategoryHom_falsehood] at h
      simp only [] at h
      exact h
    · have h := ConcreteCategory.congr_hom (hm ⟨false⟩) PUnit.unit
      rw [ConcreteCategory.comp_apply] at h
      change (ConcreteCategory.hom m) ((ConcreteCategory.hom (truth G)) PUnit.unit) = _ at h
      rw [concreteCategoryHom_truth] at h
      simp only [] at h
      exact h
end FiniteGSetProof

/- accepted add_to_file helper 2 -/
namespace FiniteGSetProof

variable (G : Type u) [Group G]

noncomputable def targetCofanTrue : Cofan (truthTarget G) where
  pt := twoObj G
  ι := Discrete.natTrans fun
    | ⟨false⟩ => falsehood G
    | ⟨true⟩ => truth G

noncomputable def targetCofanTrueIsColimit : IsColimit (targetCofanTrue G) := by
  let desc (s : Cocone (Discrete.functor (truthTarget G))) : twoObj G ⟶ s.pt :=
    actionHomOfEquivariant
      (fun b : (twoObj G).V.obj =>
        match (show Bool from b) with
        | true => s.ι.app ⟨true⟩ PUnit.unit
        | false => s.ι.app ⟨false⟩ PUnit.unit)
      (by
        intro g b
        cases (show Bool from b)
        · exact from_one_apply_action G (s.ι.app ⟨false⟩) g
        · exact from_one_apply_action G (s.ι.app ⟨true⟩) g)
  refine IsColimit.mk desc ?_ ?_
  · intro s j
    cases j using Discrete.casesOn with
    | mk a =>
      cases a
      · apply ConcreteCategory.ext_apply
        intro x
        cases x
        rw [ConcreteCategory.comp_apply]
        change (ConcreteCategory.hom (desc s)) ((ConcreteCategory.hom (falsehood G)) PUnit.unit) = _
        rw [concreteCategoryHom_actionHomOfEquivariant, concreteCategoryHom_falsehood]
        rfl
      · apply ConcreteCategory.ext_apply
        intro x
        cases x
        rw [ConcreteCategory.comp_apply]
        change (ConcreteCategory.hom (desc s)) ((ConcreteCategory.hom (truth G)) PUnit.unit) = _
        rw [concreteCategoryHom_actionHomOfEquivariant, concreteCategoryHom_truth]
        rfl
  · intro s m hm
    apply ConcreteCategory.ext_apply
    intro b
    cases (show Bool from b)
    · have h := ConcreteCategory.congr_hom (hm ⟨false⟩) PUnit.unit
      rw [ConcreteCategory.comp_apply] at h
      change (ConcreteCategory.hom m) ((ConcreteCategory.hom (falsehood G)) PUnit.unit) = _ at h
      rw [concreteCategoryHom_falsehood] at h
      simp only [] at h
      exact h
    · have h := ConcreteCategory.congr_hom (hm ⟨true⟩) PUnit.unit
      rw [ConcreteCategory.comp_apply] at h
      change (ConcreteCategory.hom m) ((ConcreteCategory.hom (truth G)) PUnit.unit) = _ at h
      rw [concreteCategoryHom_truth] at h
      simp only [] at h
      exact h

end FiniteGSetProof

/- accepted add_to_file helper 3 -/
namespace FiniteGSetProof

variable (G : Type u) [Group G]

noncomputable def truthNat : Discrete.functor (truthSource G) ⟶ Discrete.functor (truthTarget G) :=
  Discrete.natTrans fun
    | ⟨false⟩ => initial.to (oneObj G)
    | ⟨true⟩ => 𝟙 (oneObj G)

lemma truthNat_comm (j : Discrete Bool) :
    (sourceCofan G).ι.app j ≫ truth G =
      (truthNat G).app j ≫ (targetCofanTrue G).ι.app j := by
  cases j using Discrete.casesOn with
  | mk a =>
    cases a
    · exact initial.hom_ext _ _
    · rfl

end FiniteGSetProof

/- accepted add_to_file helper 4 -/
namespace FiniteGSetProof

lemma morphismProperty_truth (G : Type*) [Group G] [Finite G]
    (D : CategoryTheory.MorphismProperty (Action (FintypeCat) G))
    (hD_id : {X Y : Action (FintypeCat) G} → (f : X ⟶ Y) →
      D f → D (CategoryTheory.CategoryStruct.id X) ∧
        D (CategoryTheory.CategoryStruct.id Y))
    (hD_pullback : D.IsStableUnderBaseChange)
    (hD_coproduct : D.IsStableUnderFiniteCoproducts)
    (hD_empty : D (CategoryTheory.Limits.initial.to
      (CategoryTheory.Limits.terminal (Action (FintypeCat) G)))) :
    D (truth G) := by
  classical
  haveI : D.IsStableUnderBaseChange := hD_pullback
  haveI : D.IsStableUnderFiniteCoproducts := hD_coproduct
  haveI : D.RespectsIso := hD_pullback.respectsIso
  let e := terminalIsoIsTerminal (oneIsTerminal G)
  have hInitOne' : D (initial.to (terminal (Action (FintypeCat) G)) ≫ e.hom) :=
    MorphismProperty.RespectsIso.postcomp D e.hom
      (initial.to (terminal (Action (FintypeCat) G))) hD_empty
  have hInitOne : D (initial.to (oneObj G)) := by
    convert hInitOne' using 1
  have hIdOne : D (𝟙 (oneObj G)) := (hD_id (initial.to (oneObj G)) hInitOne).2
  have hcomponents : D.functorCategory (Discrete Bool) (truthNat G) := by
    intro j
    cases j using Discrete.casesOn with
    | mk a =>
      cases a
      · exact hInitOne
      · exact hIdOne
  exact (hD_coproduct.isStableUnderCoproductsOfShape Bool).condition
    (Discrete.functor (truthSource G)) (Discrete.functor (truthTarget G))
    (sourceCofan G) (targetCofanTrue G)
    (sourceCofanIsColimit G) (targetCofanTrueIsColimit G)
    (truthNat G) hcomponents (truth G) (fun j => truthNat_comm G j)

end FiniteGSetProof

/- accepted add_to_file helper 5 -/
namespace FiniteGSetProof

variable (G : Type*) [Group G]

lemma rho_apply (X : Action (FintypeCat) G) (g : G) (x : X.V.obj) :
    ConcreteCategory.hom (X.ρ g) x = g • x := by
  rfl

lemma hom_apply_action {X Y : Action (FintypeCat) G} (f : X ⟶ Y) (g : G) (x : X.V.obj) :
    f (ConcreteCategory.hom (X.ρ g) x) = ConcreteCategory.hom (Y.ρ g) (f x) := by
  have h := congrArg (fun φ : X.V ⟶ Y.V => ConcreteCategory.hom φ x) (f.comm g)
  simpa [ConcreteCategory.comp_apply] using h

lemma hom_apply_smul {X Y : Action (FintypeCat) G} (f : X ⟶ Y) (g : G) (x : X.V.obj) :
    f (g • x) = g • f x := by
  simpa [rho_apply G] using hom_apply_action G f g x

end FiniteGSetProof

/- accepted add_to_file helper 6 -/
namespace FiniteGSetProof

variable (G : Type*) [Group G]

noncomputable def characteristicMap {X Y : Action (FintypeCat) G} (f : X ⟶ Y) :
    Y ⟶ twoObj G := by
  classical
  exact actionHomOfEquivariant
    (fun y => if ∃ x : X.V.obj, f x = y then true else false)
    (by
      intro g y
      change (if ∃ x : X.V.obj, f x = g • y then true else false) =
        (if ∃ x : X.V.obj, f x = y then true else false)
      have hiff : (∃ x : X.V.obj, f x = g • y) ↔ (∃ x : X.V.obj, f x = y) := by
        constructor
        · rintro ⟨x, hx⟩
          refine ⟨g⁻¹ • x, ?_⟩
          calc
            f (g⁻¹ • x) = g⁻¹ • f x := hom_apply_smul G f g⁻¹ x
            _ = g⁻¹ • (g • y) := by rw [hx]
            _ = y := inv_smul_smul g y
        · rintro ⟨x, hx⟩
          refine ⟨g • x, ?_⟩
          calc
            f (g • x) = g • f x := hom_apply_smul G f g x
            _ = g • y := by rw [hx]
      rw [propext hiff])

end FiniteGSetProof

/- accepted add_to_file helper 7 -/
namespace FiniteGSetProof

variable (G : Type*) [Group G]

lemma characteristicMap_apply {X Y : Action (FintypeCat) G} (f : X ⟶ Y) (y : Y.V.obj)
    [Decidable (∃ x : X.V.obj, f x = y)] :
    characteristicMap G f y = (if ∃ x : X.V.obj, f x = y then true else false) := by
  unfold characteristicMap
  rw [concreteCategoryHom_actionHomOfEquivariant]
  congr

end FiniteGSetProof

/- accepted add_to_file helper 8 -/
namespace FiniteGSetProof

variable (G : Type*) [Group G]

lemma oneMap_apply {X : Action (FintypeCat) G} (x : X.V.obj) :
    oneMap G x = PUnit.unit := by
  rfl

noncomputable def characteristicSquare {X Y : Action (FintypeCat) G} (f : X ⟶ Y) :
    Square (Action (FintypeCat) G) := by
  classical
  refine Square.mk (oneMap G) f (truth G) (characteristicMap G f) ?_
  apply ConcreteCategory.ext_apply
  intro x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  rw [oneMap_apply, concreteCategoryHom_truth]
  simp [characteristicMap_apply]

end FiniteGSetProof

/- accepted add_to_file helper 9 -/
namespace FiniteGSetProof

variable (G : Type*) [Group G]

lemma characteristicSquare_isPullback {X Y : Action (FintypeCat) G} (f : X ⟶ Y) [Mono f] :
    (characteristicSquare G f).IsPullback := by
  classical
  have hf_inj : Function.Injective (ConcreteCategory.hom f) :=
    (ConcreteCategory.mono_iff_injective_of_preservesPullback f).mp inferInstance
  let F := Action.forget (FintypeCat) G ⋙ FintypeCat.incl
  have hmap : ((characteristicSquare G f).map F).IsPullback := by
    refine (CategoryTheory.Limits.Types.isPullback_iff _ _ _ _).mpr ⟨?_, ?_, ?_⟩
    · exact ((characteristicSquare G f).map F).fac
    · intro x y h
      exact hf_inj h.2
    · intro p y hp
      cases p
      have hχ : characteristicMap G f y = true := hp.symm
      rw [characteristicMap_apply] at hχ
      split at hχ
      case isTrue hmem =>
        rcases hmem with ⟨x, hx⟩
        exact ⟨x, oneMap_apply G x, hx⟩
      case isFalse hnot =>
        simp at hχ
  exact Square.IsPullback.of_map F hmap

end FiniteGSetProof

/- accepted add_to_file helper 10 -/
namespace FiniteGSetProof

universe u v

@[reducible]
def trivialMulActionU (G : Type u) [Monoid G] (A : Type v) : MulAction G A where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[reducible]
def trivialObjU (G : Type u) [Monoid G] (A : Type v) [Finite A] : Action (FintypeCat.{v}) G := by
  letI : MulAction G A := trivialMulActionU G A
  exact Action.FintypeCat.ofMulAction G (FintypeCat.of A)

def actionHomOfEquivariantU {G : Type u} [Monoid G] {X Y : Action (FintypeCat.{v}) G}
    (φ : X.V.obj → Y.V.obj)
    (hφ : ∀ g x, φ (ConcreteCategory.hom (X.ρ g) x) = ConcreteCategory.hom (Y.ρ g) (φ x)) : X ⟶ Y where
  hom := FintypeCat.homMk φ
  comm := by intro g; ext x; exact hφ g x

lemma concreteCategoryHom_actionHomOfEquivariantU {G : Type u} [Monoid G]
    {X Y : Action (FintypeCat.{v}) G} (φ : X.V.obj → Y.V.obj)
    (hφ : ∀ g x, φ (ConcreteCategory.hom (X.ρ g) x) = ConcreteCategory.hom (Y.ρ g) (φ x)) :
    ConcreteCategory.hom (actionHomOfEquivariantU φ hφ : X ⟶ Y) = φ := rfl

noncomputable def toTrivialObjU (G : Type u) [Monoid G] (A : Type v) [Finite A] [Nonempty A]
    (X : Action (FintypeCat.{v}) G) : X ⟶ trivialObjU G A :=
  let a : A := Classical.choice inferInstance
  actionHomOfEquivariantU (fun _ => a) (by intro g x; rfl)

def trivialMapU (G : Type u) [Monoid G] {A B : Type v} [Finite A] [Finite B]
    (φ : A → B) : trivialObjU G A ⟶ trivialObjU G B :=
  actionHomOfEquivariantU φ (by intro g x; rfl)

variable (G : Type u) [Group G]

@[reducible]
def oneObjU : Action (FintypeCat.{v}) G := trivialObjU G (ULift.{v,0} PUnit.{1})
@[reducible]
def twoObjU : Action (FintypeCat.{v}) G := trivialObjU G (ULift.{v,0} Bool)
noncomputable def oneMapU {X : Action (FintypeCat.{v}) G} : X ⟶ oneObjU G :=
  toTrivialObjU G (ULift.{v,0} PUnit.{1}) X
def truthU : oneObjU G ⟶ twoObjU G :=
  trivialMapU G (fun _ : ULift.{v,0} PUnit.{1} => (ULift.up true : ULift.{v,0} Bool))
def falsehoodU : oneObjU G ⟶ twoObjU G :=
  trivialMapU G (fun _ : ULift.{v,0} PUnit.{1} => (ULift.up false : ULift.{v,0} Bool))

lemma concreteCategoryHom_truthU :
    (⇑(ConcreteCategory.hom (truthU G)) : (ULift.{v,0} PUnit.{1}) → ULift.{v,0} Bool) =
      (fun _ : ULift.{v,0} PUnit.{1} => (ULift.up true : ULift.{v,0} Bool)) := rfl
lemma concreteCategoryHom_falsehoodU :
    (⇑(ConcreteCategory.hom (falsehoodU G)) : (ULift.{v,0} PUnit.{1}) → ULift.{v,0} Bool) =
      (fun _ : ULift.{v,0} PUnit.{1} => (ULift.up false : ULift.{v,0} Bool)) := rfl

noncomputable instance oneUniqueU (X : Action (FintypeCat.{v}) G) : Unique (X ⟶ oneObjU G) where
  default := oneMapU G
  uniq f := by
    apply Action.hom_ext
    ext x
    cases f x with
    | up q =>
      cases q
      rfl

noncomputable def oneIsTerminalU : Limits.IsTerminal (oneObjU (G:=G)) :=
  Limits.IsTerminal.ofUnique _

noncomputable abbrev initialObjU : Action (FintypeCat.{v}) G := ⊥_ _

end FiniteGSetProof

/- accepted add_to_file helper 11 -/
namespace FiniteGSetProof
universe u v
variable (G : Type u) [Group G]

noncomputable def truthSourceU : Bool → Action (FintypeCat.{v}) G
  | false => initialObjU G
  | true => oneObjU G

def truthTargetU : Bool → Action (FintypeCat.{v}) G
  | false => oneObjU G
  | true => oneObjU G

noncomputable def sourceCofanU : Cofan (truthSourceU G) where
  pt := oneObjU G
  ι := Discrete.natTrans fun
    | ⟨false⟩ => initial.to (oneObjU G)
    | ⟨true⟩ => 𝟙 (oneObjU G)

noncomputable def sourceCofanUIsColimit : IsColimit (sourceCofanU G) := by
  refine IsColimit.mk (fun s => s.ι.app ⟨true⟩) ?_ ?_
  · intro s j
    cases j using Discrete.casesOn with
    | mk a =>
      cases a
      · exact initial.hom_ext _ _
      · exact Category.id_comp _
  · intro s m hm
    simpa [sourceCofanU] using hm ⟨true⟩

lemma from_one_apply_actionU {W : Action (FintypeCat.{v}) G} (h : oneObjU G ⟶ W) (g : G) :
    h (ULift.up PUnit.unit) = ConcreteCategory.hom (W.ρ g) (h (ULift.up PUnit.unit)) := by
  have hcomm := congrArg (fun φ : (oneObjU G).V ⟶ W.V =>
      ConcreteCategory.hom φ (ULift.up PUnit.unit)) (h.comm g)
  simpa using hcomm

noncomputable def targetCofanTrueU : Cofan (truthTargetU G) where
  pt := twoObjU G
  ι := Discrete.natTrans fun
    | ⟨false⟩ => falsehoodU G
    | ⟨true⟩ => truthU G

noncomputable def targetCofanTrueUIsColimit : IsColimit (targetCofanTrueU G) := by
  let desc (s : Cocone (Discrete.functor (truthTargetU G))) : twoObjU G ⟶ s.pt :=
    actionHomOfEquivariantU
      (fun b : (twoObjU G).V.obj =>
        if (show ULift.{v,0} Bool from b).down then
          s.ι.app ⟨true⟩ (ULift.up PUnit.unit)
        else
          s.ι.app ⟨false⟩ (ULift.up PUnit.unit))
      (by
        intro g b
        cases b with
        | up q =>
          cases q
          · exact from_one_apply_actionU G (s.ι.app ⟨false⟩) g
          · exact from_one_apply_actionU G (s.ι.app ⟨true⟩) g)
  refine IsColimit.mk desc ?_ ?_
  · intro s j
    cases j using Discrete.casesOn with
    | mk a =>
      cases a
      · apply ConcreteCategory.ext_apply
        intro x
        cases x with
        | up q =>
          cases q
          rw [ConcreteCategory.comp_apply]
          change (ConcreteCategory.hom (desc s)) ((ConcreteCategory.hom (falsehoodU G))
            (ULift.up PUnit.unit)) = _
          rw [concreteCategoryHom_actionHomOfEquivariantU, concreteCategoryHom_falsehoodU]
          rfl
      · apply ConcreteCategory.ext_apply
        intro x
        cases x with
        | up q =>
          cases q
          rw [ConcreteCategory.comp_apply]
          change (ConcreteCategory.hom (desc s)) ((ConcreteCategory.hom (truthU G))
            (ULift.up PUnit.unit)) = _
          rw [concreteCategoryHom_actionHomOfEquivariantU, concreteCategoryHom_truthU]
          rfl
  · intro s m hm
    apply ConcreteCategory.ext_apply
    intro b
    cases b with
    | up q =>
      cases q
      · have h := ConcreteCategory.congr_hom (hm ⟨false⟩) (ULift.up PUnit.unit)
        rw [ConcreteCategory.comp_apply] at h
        change (ConcreteCategory.hom m) ((ConcreteCategory.hom (falsehoodU G))
          (ULift.up PUnit.unit)) = _ at h
        rw [concreteCategoryHom_falsehoodU] at h
        simp only [] at h
        exact h
      · have h := ConcreteCategory.congr_hom (hm ⟨true⟩) (ULift.up PUnit.unit)
        rw [ConcreteCategory.comp_apply] at h
        change (ConcreteCategory.hom m) ((ConcreteCategory.hom (truthU G))
          (ULift.up PUnit.unit)) = _ at h
        rw [concreteCategoryHom_truthU] at h
        simp only [] at h
        exact h

end FiniteGSetProof

/- accepted add_to_file helper 12 -/
namespace FiniteGSetProof
universe u v
variable (G : Type u) [Group G]

noncomputable def truthNatU : Discrete.functor (truthSourceU G) ⟶ Discrete.functor (truthTargetU G) :=
  Discrete.natTrans fun
    | ⟨false⟩ => initial.to (oneObjU G)
    | ⟨true⟩ => 𝟙 (oneObjU G)

lemma truthNatU_comm (j : Discrete Bool) :
    (sourceCofanU G).ι.app j ≫ truthU G =
      (truthNatU G).app j ≫ (targetCofanTrueU G).ι.app j := by
  cases j using Discrete.casesOn with
  | mk a =>
    cases a
    · exact initial.hom_ext _ _
    · rfl

end FiniteGSetProof

/- accepted add_to_file helper 13 -/
namespace FiniteGSetProof
universe u v
lemma morphismProperty_truthU (G : Type u) [Group G] [Finite G]
    (D : CategoryTheory.MorphismProperty (Action (FintypeCat.{v}) G))
    (hD_id : {X Y : Action (FintypeCat.{v}) G} → (f : X ⟶ Y) →
      D f → D (CategoryTheory.CategoryStruct.id X) ∧
        D (CategoryTheory.CategoryStruct.id Y))
    (hD_pullback : D.IsStableUnderBaseChange)
    (hD_coproduct : D.IsStableUnderFiniteCoproducts)
    (hD_empty : D (CategoryTheory.Limits.initial.to
      (CategoryTheory.Limits.terminal (Action (FintypeCat.{v}) G)))) :
    D (truthU G) := by
  classical
  haveI : D.IsStableUnderBaseChange := hD_pullback
  haveI : D.IsStableUnderFiniteCoproducts := hD_coproduct
  haveI : D.RespectsIso := hD_pullback.respectsIso
  let e := terminalIsoIsTerminal (oneIsTerminalU (G:=G))
  have hInitOne' : D (initial.to (terminal (Action (FintypeCat.{v}) G)) ≫ e.hom) :=
    MorphismProperty.RespectsIso.postcomp D e.hom
      (initial.to (terminal (Action (FintypeCat.{v}) G))) hD_empty
  have hInitOne : D (initial.to (oneObjU G)) := by
    convert hInitOne' using 1
    exact initial.hom_ext _ _
  have hIdOne : D (𝟙 (oneObjU G)) := (hD_id (initial.to (oneObjU G)) hInitOne).2
  have hcomponents : D.functorCategory (Discrete Bool) (truthNatU G) := by
    intro j
    cases j using Discrete.casesOn with
    | mk a =>
      cases a
      · exact hInitOne
      · exact hIdOne
  exact (hD_coproduct.isStableUnderCoproductsOfShape Bool).condition
    (Discrete.functor (truthSourceU G)) (Discrete.functor (truthTargetU G))
    (sourceCofanU G) (targetCofanTrueU G)
    (sourceCofanUIsColimit G) (targetCofanTrueUIsColimit G)
    (truthNatU G) hcomponents (truthU G) (fun j => truthNatU_comm G j)
end FiniteGSetProof

/- accepted add_to_file helper 14 -/
namespace FiniteGSetProof
universe u v
variable (G : Type u) [Group G]

lemma rho_applyU (X : Action (FintypeCat.{v}) G) (g : G) (x : X.V.obj) :
    ConcreteCategory.hom (X.ρ g) x = g • x := by
  rfl

lemma hom_apply_actionU {X Y : Action (FintypeCat.{v}) G} (f : X ⟶ Y) (g : G) (x : X.V.obj) :
    f (ConcreteCategory.hom (X.ρ g) x) = ConcreteCategory.hom (Y.ρ g) (f x) := by
  have h := congrArg (fun φ : X.V ⟶ Y.V => ConcreteCategory.hom φ x) (f.comm g)
  simpa [ConcreteCategory.comp_apply] using h

lemma hom_apply_smulU {X Y : Action (FintypeCat.{v}) G} (f : X ⟶ Y) (g : G) (x : X.V.obj) :
    f (g • x) = g • f x := by
  simpa [rho_applyU G] using hom_apply_actionU G f g x

end FiniteGSetProof

/- accepted add_to_file helper 15 -/
namespace FiniteGSetProof
universe u v
variable (G : Type u) [Group G]

noncomputable def characteristicMapU {X Y : Action (FintypeCat.{v}) G} (f : X ⟶ Y) :
    Y ⟶ twoObjU G := by
  classical
  exact actionHomOfEquivariantU
    (fun y => if ∃ x : X.V.obj, f x = y then (ULift.up true : ULift.{v,0} Bool)
      else (ULift.up false : ULift.{v,0} Bool))
    (by
      intro g y
      change (if ∃ x : X.V.obj, f x = g • y then (ULift.up true : ULift.{v,0} Bool)
          else (ULift.up false : ULift.{v,0} Bool)) =
        (if ∃ x : X.V.obj, f x = y then (ULift.up true : ULift.{v,0} Bool)
          else (ULift.up false : ULift.{v,0} Bool))
      have hiff : (∃ x : X.V.obj, f x = g • y) ↔ (∃ x : X.V.obj, f x = y) := by
        constructor
        · rintro ⟨x, hx⟩
          refine ⟨g⁻¹ • x, ?_⟩
          calc
            f (g⁻¹ • x) = g⁻¹ • f x := hom_apply_smulU G f g⁻¹ x
            _ = g⁻¹ • (g • y) := by rw [hx]
            _ = y := inv_smul_smul g y
        · rintro ⟨x, hx⟩
          refine ⟨g • x, ?_⟩
          calc
            f (g • x) = g • f x := hom_apply_smulU G f g x
            _ = g • y := by rw [hx]
      rw [propext hiff])

lemma characteristicMapU_apply {X Y : Action (FintypeCat.{v}) G} (f : X ⟶ Y) (y : Y.V.obj)
    [Decidable (∃ x : X.V.obj, f x = y)] :
    characteristicMapU G f y =
      (if ∃ x : X.V.obj, f x = y then (ULift.up true : ULift.{v,0} Bool)
        else (ULift.up false : ULift.{v,0} Bool)) := by
  unfold characteristicMapU
  rw [concreteCategoryHom_actionHomOfEquivariantU]
  congr

lemma oneMapU_apply {X : Action (FintypeCat.{v}) G} (x : X.V.obj) :
    oneMapU G x = ULift.up PUnit.unit := by
  cases oneMapU G x with
  | up q =>
    cases q
    rfl

end FiniteGSetProof

/- accepted add_to_file helper 16 -/
namespace FiniteGSetProof
universe u v
variable (G : Type u) [Group G]

noncomputable def characteristicSquareU {X Y : Action (FintypeCat.{v}) G} (f : X ⟶ Y) :
    Square (Action (FintypeCat.{v}) G) := by
  classical
  refine Square.mk (oneMapU G) f (truthU G) (characteristicMapU G f) ?_
  apply ConcreteCategory.ext_apply
  intro x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  rw [oneMapU_apply, concreteCategoryHom_truthU]
  simp [characteristicMapU_apply]

lemma characteristicSquareU_isPullback {X Y : Action (FintypeCat.{v}) G} (f : X ⟶ Y) [Mono f] :
    (characteristicSquareU G f).IsPullback := by
  classical
  have hf_inj : Function.Injective (ConcreteCategory.hom f) :=
    (ConcreteCategory.mono_iff_injective_of_preservesPullback f).mp inferInstance
  let F := Action.forget (FintypeCat.{v}) G ⋙ FintypeCat.incl
  have hmap : ((characteristicSquareU G f).map F).IsPullback := by
    refine (CategoryTheory.Limits.Types.isPullback_iff _ _ _ _).mpr ⟨?_, ?_, ?_⟩
    · exact ((characteristicSquareU G f).map F).fac
    · intro x y h
      exact hf_inj h.2
    · intro p y hp
      cases p with
      | up q =>
        cases q
        have hχ : characteristicMapU G f y = ULift.up true := hp.symm
        rw [characteristicMapU_apply] at hχ
        split at hχ
        case isTrue hmem =>
          rcases hmem with ⟨x, hx⟩
          exact ⟨x, oneMapU_apply G x, hx⟩
        case isFalse hnot =>
          cases hχ
  exact Square.IsPullback.of_map F hmap

end FiniteGSetProof

/- verified submission -/
theorem finite_G_set_subcategory_contains_all_monomorphisms
    (G : Type*) [Group G] [Finite G]
    (D : CategoryTheory.MorphismProperty (Action (FintypeCat) G))
    (hD_id : {X Y : Action (FintypeCat) G} → (f : X ⟶ Y) →
      D f → D (CategoryTheory.CategoryStruct.id X) ∧
        D (CategoryTheory.CategoryStruct.id Y))
    (hD_comp : D.IsStableUnderComposition)
    (hD_pullback : D.IsStableUnderBaseChange)
    (hD_coproduct : D.IsStableUnderFiniteCoproducts)
    (hD_empty : D (CategoryTheory.Limits.initial.to
      (CategoryTheory.Limits.terminal (Action (FintypeCat) G)))) :
    CategoryTheory.MorphismProperty.monomorphisms (Action (FintypeCat) G) ≤ D := by
  intro X Y f hf
  haveI : Mono f := hf
  haveI : D.IsStableUnderBaseChange := hD_pullback
  have htruth : D (FiniteGSetProof.truthU G) :=
    FiniteGSetProof.morphismProperty_truthU G D hD_id hD_pullback hD_coproduct hD_empty
  exact CategoryTheory.MorphismProperty.of_isPullback
    (FiniteGSetProof.characteristicSquareU_isPullback G f) htruth

end Rollout_p0378_finite_g_set_subcategory_contains_all_mono

#check_dependency_graph "Rollout_p0378_finite_g_set_subcategory_contains_all_mono.finite_G_set_subcategory_contains_all_monomorphisms" against "{\"edges\":[{\"conclusion\":{\"name\":\"htruth\",\"statement\":\"D (Rollout_p0378_finite_g_set_subcategory_contains_all_mono.FiniteGSetProof.truthU G)\"},\"graphEdgeId\":\"h_001_htruth\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"Finite G\"},{\"name\":\"hD_id\",\"statement\":\"∀ {X Y : Action FintypeCat G} (f : X ⟶ Y), D f → D (CategoryTheory.CategoryStruct.id X) ∧ D (CategoryTheory.CategoryStruct.id Y)\"},{\"name\":\"hD_pullback\",\"statement\":\"D.IsStableUnderBaseChange\"},{\"name\":\"hD_coproduct\",\"statement\":\"D.IsStableUnderFiniteCoproducts\"},{\"name\":\"hD_empty\",\"statement\":\"D (CategoryTheory.Limits.initial.to (⊤_ Action FintypeCat G))\"}],\"rawEdgeId\":\"telescope_13\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"D f\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hD_pullback\",\"statement\":\"D.IsStableUnderBaseChange\"},{\"name\":\"hf\",\"statement\":\"CategoryTheory.MorphismProperty.monomorphisms (Action FintypeCat G) f\"},{\"name\":\"htruth\",\"statement\":\"D (Rollout_p0378_finite_g_set_subcategory_contains_all_mono.FiniteGSetProof.truthU G)\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0378_finite_g_set_subcategory_contains_all_mono\",\"reconstructedProofSha256\":\"a5cee289afacb30b6b2f8b055822c820f3656e9ccac6447b0fa05c1376cfc8dd\",\"selectedEdgeCount\":2,\"theoremName\":\"Rollout_p0378_finite_g_set_subcategory_contains_all_mono.finite_G_set_subcategory_contains_all_monomorphisms\",\"topologySha256\":\"c7aa6e819654a31c1b25326607ad68d547a4afb2514a948524abcfdf1173b344\"}"

namespace Rollout_p0412_almosttrivial_and_almostfinite_of_shortexa

-- graph_id: p0412_almosttrivial_and_almostfinite_of_shortexa
-- topology_sha256: 9cb15c8d2be7ea66532caeaf9ddd881b9b97f2e4113556f5d73c0e7fcd4dc7c6
/- accepted add_to_file helper 1 -/
lemma torsion_map_le {R A B : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
    (u : A →ₗ[R] B) :
    Submodule.torsion R A ≤ Submodule.comap u (Submodule.torsion R B) := by
  intro a ha
  change u a ∈ Submodule.torsion R B
  rw [Submodule.mem_torsion_iff] at ha ⊢
  rcases ha with ⟨r, hr⟩
  use r
  rw [Submonoid.smul_def] at hr ⊢
  rw [← map_smul, hr, map_zero]

lemma torsion_reflect_of_injective {R A B : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
    (u : A →ₗ[R] B) (hu : Function.Injective u) {a : A}
    (ha : u a ∈ Submodule.torsion R B) : a ∈ Submodule.torsion R A := by
  rw [Submodule.mem_torsion_iff] at ha ⊢
  rcases ha with ⟨r, hr⟩
  use r
  rw [Submonoid.smul_def] at hr ⊢
  apply hu
  rw [map_smul, hr, map_zero]

/- accepted add_to_file helper 2 -/
lemma exists_nonzero_annihilates_torsion_of_isNoetherian
    {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [IsNoetherian R M] :
    ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M, r • m = 0 := by
  have hfin : Module.Finite R (Submodule.torsion R M) :=
    Module.IsNoetherian.finite R (Submodule.torsion R M)
  rcases Submodule.annihilator_top_inter_nonZeroDivisors
      (M := Submodule.torsion R M) (Submodule.torsion_isTorsion (R := R) (M := M)) with ⟨r, hrann, hrnz⟩
  refine ⟨r, nonZeroDivisors.ne_zero hrnz, ?_⟩
  intro m
  exact Module.isTorsionBySet_annihilator_top R (Submodule.torsion R M)
    (a := ⟨r, hrann⟩) (x := m)

/- accepted add_to_file helper 3 -/
lemma torsion_right_annihilated_of_shortExact
    {R M₀ M₁ M₂ : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₀] [Module R M₁] [Module R M₂]
    (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂)
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hT₁ : ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₁, r • m = 0)
    [Module.Finite R (M₁ ⧸ Submodule.torsion R M₁)] [IsNoetherianRing R] :
    ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₂, r • m = 0 := by
  let Q₀ := M₀ ⧸ Submodule.torsion R M₀
  let Q₁ := M₁ ⧸ Submodule.torsion R M₁
  let qF : Q₀ →ₗ[R] Q₁ :=
    Submodule.mapQ (Submodule.torsion R M₀) (Submodule.torsion R M₁) f (torsion_map_le f)
  let C := Q₁ ⧸ qF.range
  haveI : Module.Finite R C := by
    exact Module.Finite.quotient R qF.range
  haveI : IsNoetherian R C := isNoetherian_of_isNoetherianRing_of_finite R C
  rcases exists_nonzero_annihilates_torsion_of_isNoetherian (R := R) (M := C) with ⟨b, hb0, hb⟩
  rcases hT₁ with ⟨a, ha0, ha⟩
  refine ⟨a * b, mul_ne_zero ha0 hb0, ?_⟩
  intro z
  rcases hg (z : M₂) with ⟨x, hx⟩
  have hclass : Submodule.Quotient.mk (Submodule.Quotient.mk x : Q₁) ∈ Submodule.torsion R C := by
    rw [Submodule.mem_torsion_iff]
    have hzmem : (z : M₂) ∈ Submodule.torsion R M₂ := z.property
    rw [Submodule.mem_torsion_iff] at hzmem
    rcases hzmem with ⟨c, hc⟩
    use c
    rw [Submonoid.smul_def] at hc ⊢
    have hgx : g ((c : R) • x) = 0 := by
      rw [map_smul, hx, hc]
    rcases ((hfg ((c : R) • x)).mp hgx) with ⟨y, hy⟩
    have hinner : (c : R) • (Submodule.Quotient.mk x : Q₁) =
        Submodule.Quotient.mk ((c : R) • x : M₁) := by
      calc
        (c : R) • (Submodule.Quotient.mk x : Q₁)
            = (c : R) • (Submodule.mkQ (Submodule.torsion R M₁)) x := rfl
        _ = (Submodule.mkQ (Submodule.torsion R M₁)) ((c : R) • x) := by
              exact (map_smul (Submodule.mkQ (Submodule.torsion R M₁)) (c : R) x).symm
        _ = Submodule.Quotient.mk ((c : R) • x : M₁) := rfl
    have houter : (c : R) • (Submodule.Quotient.mk (Submodule.Quotient.mk x : Q₁) : C) =
        Submodule.Quotient.mk ((c : R) • (Submodule.Quotient.mk x : Q₁) : Q₁) := by
      calc
        (c : R) • (Submodule.Quotient.mk (Submodule.Quotient.mk x : Q₁) : C)
            = (c : R) • (Submodule.mkQ qF.range) (Submodule.Quotient.mk x : Q₁) := rfl
        _ = (Submodule.mkQ qF.range) ((c : R) • (Submodule.Quotient.mk x : Q₁)) := by
              exact (map_smul (Submodule.mkQ qF.range) (c : R)
                (Submodule.Quotient.mk x : Q₁)).symm
        _ = Submodule.Quotient.mk ((c : R) • (Submodule.Quotient.mk x : Q₁) : Q₁) := rfl
    have hq : (c : R) • (Submodule.Quotient.mk (Submodule.Quotient.mk x : Q₁) : C) =
        (Submodule.Quotient.mk (qF (Submodule.Quotient.mk y : Q₀) : Q₁) : C) := by
      rw [houter, hinner, ← hy]
      exact congrArg (fun u : Q₁ => (Submodule.Quotient.mk u : C))
        (Submodule.mapQ_apply (Submodule.torsion R M₀)
          (Submodule.torsion R M₁) f y).symm
    rw [hq]
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  have hbclass := hb ⟨Submodule.Quotient.mk (Submodule.Quotient.mk x : Q₁), hclass⟩
  have hbmem : Submodule.Quotient.mk (b • x : M₁) ∈ qF.range := by
    have hbclass' : Submodule.Quotient.mk (Submodule.Quotient.mk (b • x : M₁) : Q₁) = (0 : C) := by
      have hv : b • (Submodule.Quotient.mk (Submodule.Quotient.mk x : Q₁) : C) = 0 := by
        exact congrArg Subtype.val hbclass
      have hinner : b • (Submodule.Quotient.mk x : Q₁) =
          Submodule.Quotient.mk (b • x : M₁) := by
        calc
          b • (Submodule.Quotient.mk x : Q₁)
              = b • (Submodule.mkQ (Submodule.torsion R M₁)) x := rfl
          _ = (Submodule.mkQ (Submodule.torsion R M₁)) (b • x) := by
                exact (map_smul (Submodule.mkQ (Submodule.torsion R M₁)) b x).symm
          _ = Submodule.Quotient.mk (b • x : M₁) := rfl
      have houter : b • (Submodule.Quotient.mk (Submodule.Quotient.mk x : Q₁) : C) =
          Submodule.Quotient.mk (b • (Submodule.Quotient.mk x : Q₁) : Q₁) := by
        calc
          b • (Submodule.Quotient.mk (Submodule.Quotient.mk x : Q₁) : C)
              = b • (Submodule.mkQ qF.range) (Submodule.Quotient.mk x : Q₁) := rfl
          _ = (Submodule.mkQ qF.range) (b • (Submodule.Quotient.mk x : Q₁)) := by
                exact (map_smul (Submodule.mkQ qF.range) b
                  (Submodule.Quotient.mk x : Q₁)).symm
          _ = Submodule.Quotient.mk (b • (Submodule.Quotient.mk x : Q₁) : Q₁) := rfl
      rw [houter, hinner] at hv
      exact hv
    rw [Submodule.Quotient.mk_eq_zero] at hbclass'
    exact hbclass'
  rcases hbmem with ⟨q₀, hq₀⟩
  rcases Submodule.Quotient.mk_surjective (Submodule.torsion R M₀) q₀ with ⟨y, rfl⟩
  have hqmap : qF (Submodule.Quotient.mk y : Q₀) = Submodule.Quotient.mk (f y : M₁) := by
    change (Submodule.mapQ (Submodule.torsion R M₀) (Submodule.torsion R M₁) f
      (torsion_map_le f)) (Submodule.Quotient.mk y) = Submodule.Quotient.mk (f y)
    exact Submodule.mapQ_apply (Submodule.torsion R M₀) (Submodule.torsion R M₁) f y
  have hq₀' : Submodule.Quotient.mk (b • x : M₁) = Submodule.Quotient.mk (f y : M₁) :=
    hq₀.symm.trans hqmap
  have hdiff : b • x - f y ∈ Submodule.torsion R M₁ := by
    exact (Submodule.Quotient.eq (Submodule.torsion R M₁)).mp hq₀'
  have hakill : a • (b • x - f y) = 0 := by
    have := congrArg Subtype.val (ha ⟨b • x - f y, hdiff⟩)
    simpa using this
  have hgkill : g (a • (b • x - f y)) = 0 := by
    rw [hakill, map_zero]
  have hgf : g (f y) = 0 := by
    exact (hfg (f y)).mpr ⟨y, rfl⟩
  have hmain : (a * b) • g x = 0 := by
    rw [map_smul, map_sub, map_smul, hgf, sub_zero] at hgkill
    rw [smul_smul] at hgkill
    exact hgkill
  ext
  rw [hx] at hmain
  exact hmain

/- accepted add_to_file helper 4 -/
lemma finite_quotient_middle_of_shortExact
    {R M₀ M₁ M₂ : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₀] [Module R M₁] [Module R M₂]
    (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂)
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hT₂ : ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₂, r • m = 0)
    [Module.Finite R (M₀ ⧸ Submodule.torsion R M₀)]
    [Module.Finite R (M₂ ⧸ Submodule.torsion R M₂)] [IsNoetherianRing R] :
    Module.Finite R (M₁ ⧸ Submodule.torsion R M₁) := by
  let Q₀ := M₀ ⧸ Submodule.torsion R M₀
  let Q₁ := M₁ ⧸ Submodule.torsion R M₁
  let Q₂ := M₂ ⧸ Submodule.torsion R M₂
  let qF : Q₀ →ₗ[R] Q₁ :=
    Submodule.mapQ (Submodule.torsion R M₀) (Submodule.torsion R M₁) f (torsion_map_le f)
  let qG : Q₁ →ₗ[R] Q₂ :=
    Submodule.mapQ (Submodule.torsion R M₁) (Submodule.torsion R M₂) g (torsion_map_le g)
  have hqG_surj : Function.Surjective qG := by
    intro z
    rcases Submodule.Quotient.mk_surjective (Submodule.torsion R M₂) z with ⟨m, rfl⟩
    rcases hg m with ⟨x, hx⟩
    use Submodule.Quotient.mk x
    have hmap : qG (Submodule.Quotient.mk x : Q₁) = Submodule.Quotient.mk (g x : M₂) := by
      change (Submodule.mapQ (Submodule.torsion R M₁) (Submodule.torsion R M₂) g
        (torsion_map_le g)) (Submodule.Quotient.mk x) = Submodule.Quotient.mk (g x)
      exact Submodule.mapQ_apply (Submodule.torsion R M₁) (Submodule.torsion R M₂) g x
    rw [hmap, hx]
  rcases hT₂ with ⟨b, hb0, hb⟩
  let bm : Q₁ →ₗ[R] Q₁ := b • LinearMap.id
  have hLfg : qF.range.FG := by
    exact Module.Finite.iff_fg.mp (Module.Finite.range qF)
  have hmaple : Submodule.map bm qG.ker ≤ qF.range := by
    intro y hy
    rw [Submodule.mem_map] at hy
    rcases hy with ⟨x, hxK, rfl⟩
    rcases Submodule.Quotient.mk_surjective (Submodule.torsion R M₁) x with ⟨m, rfl⟩
    have hzero : qG (Submodule.Quotient.mk m : Q₁) = 0 := LinearMap.mem_ker.mp hxK
    have hqGmap : qG (Submodule.Quotient.mk m : Q₁) = Submodule.Quotient.mk (g m : M₂) := by
      change (Submodule.mapQ (Submodule.torsion R M₁) (Submodule.torsion R M₂) g
        (torsion_map_le g)) (Submodule.Quotient.mk m) = Submodule.Quotient.mk (g m)
      exact Submodule.mapQ_apply (Submodule.torsion R M₁) (Submodule.torsion R M₂) g m
    have hgtors : g m ∈ Submodule.torsion R M₂ := by
      rw [hqGmap, Submodule.Quotient.mk_eq_zero] at hzero
      exact hzero
    have hbkill : b • g m = 0 := by
      have := congrArg Subtype.val (hb ⟨g m, hgtors⟩)
      simpa using this
    have hgb : g (b • m) = 0 := by
      rw [map_smul, hbkill]
    rcases ((hfg (b • m)).mp hgb) with ⟨y, hy⟩
    change b • (Submodule.Quotient.mk m : Q₁) ∈ qF.range
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    have hqFmap : qF (Submodule.Quotient.mk y : Q₀) = Submodule.Quotient.mk (f y : M₁) := by
      change (Submodule.mapQ (Submodule.torsion R M₀) (Submodule.torsion R M₁) f
        (torsion_map_le f)) (Submodule.Quotient.mk y) = Submodule.Quotient.mk (f y)
      exact Submodule.mapQ_apply (Submodule.torsion R M₀) (Submodule.torsion R M₁) f y
    rw [hqFmap, hy]
    calc
      Submodule.Quotient.mk (b • m : M₁)
          = b • (Submodule.mkQ (Submodule.torsion R M₁)) m := by
            exact map_smul (Submodule.mkQ (Submodule.torsion R M₁)) b m
      _ = b • (Submodule.Quotient.mk m : Q₁) := rfl
  have hmapfg : (Submodule.map bm qG.ker).FG :=
    Submodule.FG.of_le hLfg hmaple
  have hkerbot : qG.ker ⊓ bm.ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rcases hx with ⟨-, hxb⟩
    have hbzero : bm x = 0 := LinearMap.mem_ker.mp hxb
    change b • x = 0 at hbzero
    apply smul_right_injective Q₁ hb0
    change b • x = b • (0 : Q₁)
    rw [hbzero, smul_zero]
  have hkerfg : (qG.ker ⊓ bm.ker).FG := by
    rw [hkerbot]
    exact Submodule.fg_bot
  have hKfg : qG.ker.FG := Submodule.fg_of_fg_map_of_fg_inf_ker bm hmapfg hkerfg
  haveI : Module.Finite R qG.ker := Module.Finite.iff_fg.mpr hKfg
  have hexact : Function.Exact qG.ker.subtype qG := by
    intro x
    constructor
    · intro hx
      exact ⟨⟨x, LinearMap.mem_ker.mpr hx⟩, rfl⟩
    · intro hx
      rcases hx with ⟨y, hy⟩
      have : qG (y : Q₁) = 0 := LinearMap.mem_ker.mp y.property
      rw [← hy]
      exact this
  exact Module.Finite.of_exact hexact hqG_surj

/- accepted add_to_file helper 5 -/
lemma torsion_middle_annihilated_of_shortExact
    {R M₀ M₁ M₂ : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₀] [Module R M₁] [Module R M₂]
    (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂)
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hT₀ : ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₀, r • m = 0)
    (hT₂ : ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₂, r • m = 0) :
    ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₁, r • m = 0 := by
  rcases hT₀ with ⟨a, ha0, ha⟩
  rcases hT₂ with ⟨b, hb0, hb⟩
  refine ⟨a * b, mul_ne_zero ha0 hb0, ?_⟩
  intro z
  have hgz : g (z : M₁) ∈ Submodule.torsion R M₂ := torsion_map_le g z.property
  have hbkill : b • g (z : M₁) = 0 := by
    have := congrArg Subtype.val (hb ⟨g (z : M₁), hgz⟩)
    simpa using this
  have hgb : g (b • (z : M₁)) = 0 := by
    rw [map_smul, hbkill]
  rcases ((hfg (b • (z : M₁))).mp hgb) with ⟨y, hy⟩
  have hfy : f y ∈ Submodule.torsion R M₁ := by
    rw [hy]
    exact (Submodule.torsion R M₁).smul_mem b z.property
  have hytor : y ∈ Submodule.torsion R M₀ :=
    torsion_reflect_of_injective f hf hfy
  have hakill : a • y = 0 := by
    have := congrArg Subtype.val (ha ⟨y, hytor⟩)
    simpa using this
  have hfzero : f (a • y) = 0 := by
    rw [hakill, map_zero]
  have hmain : (a * b) • (z : M₁) = 0 := by
    rw [map_smul, hy] at hfzero
    rw [smul_smul] at hfzero
    exact hfzero
  ext
  exact hmain

/- accepted add_to_file helper 6 -/
lemma finite_quotient_left_of_shortExact
    {R M₀ M₁ : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M₀] [AddCommGroup M₁]
    [Module R M₀] [Module R M₁]
    (f : M₀ →ₗ[R] M₁) (hf : Function.Injective f)
    [Module.Finite R (M₁ ⧸ Submodule.torsion R M₁)] [IsNoetherianRing R] :
    Module.Finite R (M₀ ⧸ Submodule.torsion R M₀) := by
  let Q₀ := M₀ ⧸ Submodule.torsion R M₀
  let Q₁ := M₁ ⧸ Submodule.torsion R M₁
  let qF : Q₀ →ₗ[R] Q₁ :=
    Submodule.mapQ (Submodule.torsion R M₀) (Submodule.torsion R M₁) f (torsion_map_le f)
  have hqF_inj : Function.Injective qF := by
    intro x y hxy
    rcases Submodule.Quotient.mk_surjective (Submodule.torsion R M₀) x with ⟨x, rfl⟩
    rcases Submodule.Quotient.mk_surjective (Submodule.torsion R M₀) y with ⟨y, rfl⟩
    have hxmap : qF (Submodule.Quotient.mk x : Q₀) = Submodule.Quotient.mk (f x : M₁) := by
      change (Submodule.mapQ (Submodule.torsion R M₀) (Submodule.torsion R M₁) f
        (torsion_map_le f)) (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x)
      exact Submodule.mapQ_apply (Submodule.torsion R M₀) (Submodule.torsion R M₁) f x
    have hymap : qF (Submodule.Quotient.mk y : Q₀) = Submodule.Quotient.mk (f y : M₁) := by
      change (Submodule.mapQ (Submodule.torsion R M₀) (Submodule.torsion R M₁) f
        (torsion_map_le f)) (Submodule.Quotient.mk y) = Submodule.Quotient.mk (f y)
      exact Submodule.mapQ_apply (Submodule.torsion R M₀) (Submodule.torsion R M₁) f y
    rw [hxmap, hymap] at hxy
    have hdiff : f x - f y ∈ Submodule.torsion R M₁ :=
      (Submodule.Quotient.eq (Submodule.torsion R M₁)).mp hxy
    have hfdiff : f (x - y) ∈ Submodule.torsion R M₁ := by
      rw [map_sub]
      exact hdiff
    have htor : x - y ∈ Submodule.torsion R M₀ :=
      torsion_reflect_of_injective f hf hfdiff
    exact (Submodule.Quotient.eq (Submodule.torsion R M₀)).mpr htor
  haveI : IsNoetherian R Q₁ := isNoetherian_of_isNoetherianRing_of_finite R Q₁
  exact Module.Finite.of_injective qF hqF_inj

/- accepted add_to_file helper 7 -/
lemma finite_quotient_right_of_shortExact
    {R M₁ M₂ : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₁] [Module R M₂]
    (g : M₁ →ₗ[R] M₂) (hg : Function.Surjective g)
    [Module.Finite R (M₁ ⧸ Submodule.torsion R M₁)] :
    Module.Finite R (M₂ ⧸ Submodule.torsion R M₂) := by
  let Q₁ := M₁ ⧸ Submodule.torsion R M₁
  let Q₂ := M₂ ⧸ Submodule.torsion R M₂
  let qG : Q₁ →ₗ[R] Q₂ :=
    Submodule.mapQ (Submodule.torsion R M₁) (Submodule.torsion R M₂) g (torsion_map_le g)
  have hqG_surj : Function.Surjective qG := by
    intro z
    rcases Submodule.Quotient.mk_surjective (Submodule.torsion R M₂) z with ⟨m, rfl⟩
    rcases hg m with ⟨x, hx⟩
    use Submodule.Quotient.mk x
    have hmap : qG (Submodule.Quotient.mk x : Q₁) = Submodule.Quotient.mk (g x : M₂) := by
      change (Submodule.mapQ (Submodule.torsion R M₁) (Submodule.torsion R M₂) g
        (torsion_map_le g)) (Submodule.Quotient.mk x) = Submodule.Quotient.mk (g x)
      exact Submodule.mapQ_apply (Submodule.torsion R M₁) (Submodule.torsion R M₂) g x
    rw [hmap, hx]
  exact Module.Finite.of_surjective qG hqG_surj

/- accepted add_to_file helper 8 -/
lemma torsion_left_annihilated_of_shortExact
    {R M₀ M₁ : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M₀] [AddCommGroup M₁]
    [Module R M₀] [Module R M₁]
    (f : M₀ →ₗ[R] M₁) (hf : Function.Injective f)
    (hT₁ : ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₁, r • m = 0) :
    ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₀, r • m = 0 := by
  rcases hT₁ with ⟨a, ha0, ha⟩
  refine ⟨a, ha0, ?_⟩
  intro z
  have hfz : f (z : M₀) ∈ Submodule.torsion R M₁ := torsion_map_le f z.property
  have hkill : a • f (z : M₀) = 0 := by
    have := congrArg Subtype.val (ha ⟨f (z : M₀), hfz⟩)
    simpa using this
  have hfkill : f (a • (z : M₀)) = 0 := by
    rw [map_smul, hkill]
  have hmain : a • (z : M₀) = 0 := hf (by rw [hfkill, map_zero])
  ext
  exact hmain

/- verified submission -/
theorem almostTrivial_and_almostFinite_of_shortExact
    {R : Type*} [CommRing R] [IsDomain R]
    {M₀ M₁ M₂ : Type*}
    [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₀] [Module R M₁] [Module R M₂]
    (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂)
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    ((∃ r : R, r ≠ 0 ∧ ∀ m : M₁, r • m = 0) ↔
      (∃ r : R, r ≠ 0 ∧ ∀ m : M₀, r • m = 0) ∧
      (∃ r : R, r ≠ 0 ∧ ∀ m : M₂, r • m = 0)) ∧
    (IsNoetherianRing R →
      (((∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₁, r • m = 0) ∧
          Module.Finite R (M₁ ⧸ Submodule.torsion R M₁)) ↔
        ((∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₀, r • m = 0) ∧
          Module.Finite R (M₀ ⧸ Submodule.torsion R M₀)) ∧
        ((∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₂, r • m = 0) ∧
          Module.Finite R (M₂ ⧸ Submodule.torsion R M₂)))) := by
  constructor
  · constructor
    · intro h
      rcases h with ⟨r, hr0, hr⟩
      constructor
      · refine ⟨r, hr0, ?_⟩
        intro m
        apply hf
        rw [map_smul, hr (f m), map_zero]
      · refine ⟨r, hr0, ?_⟩
        intro z
        rcases hg z with ⟨m, rfl⟩
        rw [← map_smul, hr m, map_zero]
    · intro h
      rcases h with ⟨⟨a, ha0, ha⟩, ⟨b, hb0, hb⟩⟩
      refine ⟨a * b, mul_ne_zero ha0 hb0, ?_⟩
      intro m
      have hgb : g (b • m) = 0 := by
        rw [map_smul, hb (g m)]
      rcases ((hfg (b • m)).mp hgb) with ⟨y, hy⟩
      have hfy : f (a • y) = 0 := by
        rw [ha y, map_zero]
      rw [map_smul, hy] at hfy
      rw [smul_smul] at hfy
      exact hfy
  · intro hNoeth
    haveI : IsNoetherianRing R := hNoeth
    constructor
    · intro hA
      rcases hA with ⟨hT₁, hF₁⟩
      haveI : Module.Finite R (M₁ ⧸ Submodule.torsion R M₁) := hF₁
      have hT₀ := torsion_left_annihilated_of_shortExact f hf hT₁
      have hF₀ := finite_quotient_left_of_shortExact f hf
      have hF₂ := finite_quotient_right_of_shortExact g hg
      have hT₂ := torsion_right_annihilated_of_shortExact f g hfg hg hT₁
      exact ⟨⟨hT₀, hF₀⟩, ⟨hT₂, hF₂⟩⟩
    · intro hA
      rcases hA with ⟨⟨hT₀, hF₀⟩, ⟨hT₂, hF₂⟩⟩
      haveI : Module.Finite R (M₀ ⧸ Submodule.torsion R M₀) := hF₀
      haveI : Module.Finite R (M₂ ⧸ Submodule.torsion R M₂) := hF₂
      have hT₁ := torsion_middle_annihilated_of_shortExact f g hf hfg hT₀ hT₂
      have hF₁ := finite_quotient_middle_of_shortExact f g hfg hg hT₂
      exact ⟨hT₁, hF₁⟩

end Rollout_p0412_almosttrivial_and_almostfinite_of_shortexa

#check_dependency_graph "Rollout_p0412_almosttrivial_and_almostfinite_of_shortexa.almostTrivial_and_almostFinite_of_shortExact" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"((∃ r, r ≠ 0 ∧ ∀ (m : M₁), r • m = 0) ↔ (∃ r, r ≠ 0 ∧ ∀ (m : M₀), r • m = 0) ∧ ∃ r, r ≠ 0 ∧ ∀ (m : M₂), r • m = 0) ∧ (IsNoetherianRing R → ((∃ r, r ≠ 0 ∧ ∀ (m : ↥(Submodule.torsion R M₁)), r • m = 0) ∧ Module.Finite R (M₁ ⧸ Submodule.torsion R M₁) ↔ ((∃ r, r ≠ 0 ∧ ∀ (m : ↥(Submodule.torsion R M₀)), r • m = 0) ∧ Module.Finite R (M₀ ⧸ Submodule.torsion R M₀)) ∧ (∃ r, r ≠ 0 ∧ ∀ (m : ↥(Submodule.torsion R M₂)), r • m = 0) ∧ Module.Finite R (M₂ ⧸ Submodule.torsion R M₂)))\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"IsDomain R\"},{\"name\":\"hf\",\"statement\":\"Function.Injective ⇑f\"},{\"name\":\"hfg\",\"statement\":\"Function.Exact ⇑f ⇑g\"},{\"name\":\"hg\",\"statement\":\"Function.Surjective ⇑g\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0412_almosttrivial_and_almostfinite_of_shortexa\",\"reconstructedProofSha256\":\"25a2a34c7b49ca71783bba99a5a0cb7c4acf087341d9c21bf827f7cbfd6306d3\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p0412_almosttrivial_and_almostfinite_of_shortexa.almostTrivial_and_almostFinite_of_shortExact\",\"topologySha256\":\"9cb15c8d2be7ea66532caeaf9ddd881b9b97f2e4113556f5d73c0e7fcd4dc7c6\"}"

namespace Rollout_p0414_veronese_affineindependent

-- graph_id: p0414_veronese_affineindependent
-- topology_sha256: f61763d7c3c5fc654d7efba8545fcae2b44416562e2f20714ee9fb6cc89e5284
/- accepted add_to_file helper 1 -/
noncomputable section

def VeroneseIndex (m p q : ℕ) := {ab : (Fin m →₀ ℕ) × (Fin m →₀ ℕ) //
  ab.1.sum (fun _ n => n) ≤ p ∧ ab.2.sum (fun _ n => n) ≤ q}

noncomputable def veroneseVector (m p q : ℕ) (z : Fin m → ℂ) : VeroneseIndex m p q → ℂ :=
  fun ab =>
    ab.1.1.prod (fun i n => z i ^ n) *
      ab.1.2.prod (fun i n => (starRingEnd ℂ (z i)) ^ n)

noncomputable def coordForNe {m : ℕ} {a b : Fin m → ℂ} (h : a ≠ b) : Fin m :=
  Classical.choose (Function.ne_iff.mp h)

lemma coordForNe_apply_ne {m : ℕ} {a b : Fin m → ℂ} (h : a ≠ b) :
    a (coordForNe h) ≠ b (coordForNe h) :=
  Classical.choose_spec (Function.ne_iff.mp h)

noncomputable def veroneseLagrangeFactor
    {m r : ℕ} (x : Fin r → (Fin m → ℂ)) {j k : Fin r} (hjk : x j ≠ x k) :
    MvPolynomial (Fin m) ℂ :=
  let i := coordForNe hjk
  (MvPolynomial.X i - MvPolynomial.C (x j i)) *
    MvPolynomial.C ((x k i - x j i)⁻¹)

lemma veroneseLagrangeFactor_totalDegree_le
    {m r : ℕ} (x : Fin r → (Fin m → ℂ)) {j k : Fin r} (hjk : x j ≠ x k) :
    (veroneseLagrangeFactor x hjk).totalDegree ≤ 1 := by
  unfold veroneseLagrangeFactor
  let i := coordForNe hjk
  have h₁ : (MvPolynomial.X i - MvPolynomial.C (x j i) :
      MvPolynomial (Fin m) ℂ).totalDegree ≤ 1 := by
    calc
      (MvPolynomial.X i - MvPolynomial.C (x j i) :
          MvPolynomial (Fin m) ℂ).totalDegree
          ≤ max (MvPolynomial.totalDegree (MvPolynomial.X i :
              MvPolynomial (Fin m) ℂ))
              (MvPolynomial.totalDegree (MvPolynomial.C (x j i) :
              MvPolynomial (Fin m) ℂ)) :=
        MvPolynomial.totalDegree_sub _ _
      _ = 1 := by simp [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
  calc
    ((MvPolynomial.X i - MvPolynomial.C (x j i)) *
        MvPolynomial.C ((x k i - x j i)⁻¹) :
        MvPolynomial (Fin m) ℂ).totalDegree
        ≤ (MvPolynomial.X i - MvPolynomial.C (x j i) :
            MvPolynomial (Fin m) ℂ).totalDegree +
          (MvPolynomial.C ((x k i - x j i)⁻¹) :
            MvPolynomial (Fin m) ℂ).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ 1 + 0 := Nat.add_le_add h₁ (by rw [MvPolynomial.totalDegree_C])
    _ = 1 := by norm_num

@[simp]
lemma veroneseLagrangeFactor_eval_left
    {m r : ℕ} (x : Fin r → (Fin m → ℂ)) {j k : Fin r} (hjk : x j ≠ x k) :
    MvPolynomial.eval (x j) (veroneseLagrangeFactor x hjk) = 0 := by
  simp [veroneseLagrangeFactor]

@[simp]
lemma veroneseLagrangeFactor_eval_right
    {m r : ℕ} (x : Fin r → (Fin m → ℂ)) {j k : Fin r} (hjk : x j ≠ x k) :
    MvPolynomial.eval (x k) (veroneseLagrangeFactor x hjk) = 1 := by
  let i := coordForNe hjk
  have hne : x k i - x j i ≠ 0 := by
    intro hzero
    apply coordForNe_apply_ne hjk
    exact (sub_eq_zero.mp (by simpa [i] using hzero)).symm
  simp [veroneseLagrangeFactor, i, hne]

noncomputable def veroneseLagrangePoly
    {m r : ℕ} (x : Fin r → (Fin m → ℂ)) (hx : Function.Injective x) (k : Fin r) :
    MvPolynomial (Fin m) ℂ :=
  (Finset.univ.erase k).attach.prod fun j =>
    veroneseLagrangeFactor x (hx.ne (Finset.mem_erase.mp j.2).1)

lemma veroneseLagrangePoly_totalDegree_le
    {m p r : ℕ} (hrp : r ≤ p + 1) (x : Fin r → (Fin m → ℂ))
    (hx : Function.Injective x) (k : Fin r) :
    (veroneseLagrangePoly x hx k).totalDegree ≤ p := by
  have hcard : (Finset.univ.erase k).card = r - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
  calc
    (veroneseLagrangePoly x hx k).totalDegree
        ≤ ∑ j ∈ (Finset.univ.erase k).attach,
            (veroneseLagrangeFactor x (hx.ne (Finset.mem_erase.mp j.2).1)).totalDegree := by
          simpa [veroneseLagrangePoly] using
            MvPolynomial.totalDegree_finset_prod (Finset.univ.erase k).attach
              (fun j => veroneseLagrangeFactor x (hx.ne (Finset.mem_erase.mp j.2).1))
    _ ≤ ∑ j ∈ (Finset.univ.erase k).attach, 1 := by
          exact Finset.sum_le_sum fun j hj =>
            veroneseLagrangeFactor_totalDegree_le x _
    _ = r - 1 := by simp [hcard]
    _ ≤ p := by omega

@[simp]
lemma veroneseLagrangePoly_eval_self
    {m r : ℕ} (x : Fin r → (Fin m → ℂ)) (hx : Function.Injective x) (k : Fin r) :
    MvPolynomial.eval (x k) (veroneseLagrangePoly x hx k) = 1 := by
  simp [veroneseLagrangePoly, MvPolynomial.eval_prod]

lemma veroneseLagrangePoly_eval_of_ne
    {m r : ℕ} (x : Fin r → (Fin m → ℂ)) (hx : Function.Injective x)
    {l k : Fin r} (hlk : l ≠ k) :
    MvPolynomial.eval (x l) (veroneseLagrangePoly x hx k) = 0 := by
  rw [veroneseLagrangePoly, MvPolynomial.eval_prod]
  let l' : ↥(Finset.univ.erase k) :=
    ⟨l, Finset.mem_erase.mpr ⟨hlk, Finset.mem_univ l⟩⟩
  have hmem : l' ∈ (Finset.univ.erase k).attach := Finset.mem_attach _ _
  have hzero : MvPolynomial.eval (x l)
      (veroneseLagrangeFactor x (hx.ne (Finset.mem_erase.mp l'.2).1)) = 0 := by
    simp [l']
  exact Finset.prod_eq_zero hmem hzero

end

/- accepted add_to_file helper 2 -/
noncomputable section

noncomputable def veronesePolyEval
    (m p q : ℕ) (Q : MvPolynomial (Fin m) ℂ) (hQ : Q.totalDegree ≤ p) :
    (VeroneseIndex m p q → ℂ) →ₗ[ℂ] ℂ where
  toFun w := Q.support.attach.sum fun a =>
    Q.coeff a.1 * w ⟨(a.1, 0),
      (MvPolynomial.le_totalDegree a.2).trans hQ,
      by simp⟩
  map_add' w u := by
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c w := by
    simp [Finset.mul_sum, mul_left_comm, mul_assoc]

lemma veronesePolyEval_veroneseVector
    (m p q : ℕ) (Q : MvPolynomial (Fin m) ℂ) (hQ : Q.totalDegree ≤ p)
    (z : Fin m → ℂ) :
    veronesePolyEval m p q Q hQ (veroneseVector m p q z) =
      MvPolynomial.eval z Q := by
  rw [MvPolynomial.eval_eq']
  simpa [veronesePolyEval, veroneseVector] using
    (Finset.sum_attach Q.support
      (fun a => Q.coeff a * a.prod (fun i n => z i ^ n)))

end

/- accepted add_to_file helper 3 -/
theorem veronese_linearIndependent_complex
    (m p q r : ℕ) (hrp : r ≤ p + 1)
    (x : Fin r → (Fin m → ℂ)) (hx : Function.Injective x) :
    LinearIndependent ℂ (fun j : Fin r => veroneseVector m p q (x j)) := by
  rw [Fintype.linearIndependent_iff]
  intro g h k
  let Q := veroneseLagrangePoly x hx k
  have hQ : Q.totalDegree ≤ p := by
    exact veroneseLagrangePoly_totalDegree_le hrp x hx k
  let L := veronesePolyEval m p q Q hQ
  have hzero : L (∑ j, g j • veroneseVector m p q (x j)) = 0 := by
    simpa using congrArg L h
  have hcalc1 : L (∑ j, g j • veroneseVector m p q (x j)) =
      ∑ j, g j * MvPolynomial.eval (x j) Q := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp [L, veronesePolyEval_veroneseVector]
  have hsum : (∑ j, g j * MvPolynomial.eval (x j) Q) = g k := by
    rw [Finset.sum_eq_single k]
    · simp [Q]
    · intro j hj hjk
      rw [show MvPolynomial.eval (x j) Q = 0 from by
        simpa [Q] using veroneseLagrangePoly_eval_of_ne x hx hjk]
      simp
    · intro hk
      simp at hk
  exact (hcalc1.trans hsum).symm.trans hzero

/- verified submission -/
theorem veronese_affineIndependent
    (m p q r : ℕ) (hr : 1 ≤ r) (hrp : r ≤ p + 1)
    (x : Fin r → (Fin m → ℂ)) (hx : Function.Injective x) :
    let I := {ab : (Fin m →₀ ℕ) × (Fin m →₀ ℕ) //
      ab.1.sum (fun _ n => n) ≤ p ∧ ab.2.sum (fun _ n => n) ≤ q}
    let v : (Fin m → ℂ) → (I → ℂ) := fun z ab =>
      ab.1.1.prod (fun i n => z i ^ n) *
        ab.1.2.prod (fun i n => (starRingEnd ℂ (z i)) ^ n)
    AffineIndependent ℝ (fun j : Fin r => v (x j)) := by
  change AffineIndependent ℝ (fun j : Fin r => veroneseVector m p q (x j))
  have hC : LinearIndependent ℂ (fun j : Fin r => veroneseVector m p q (x j)) :=
    veronese_linearIndependent_complex m p q r hrp x hx
  have hinj : Function.Injective fun a : ℝ => a • (1 : ℂ) := by
    intro a b h
    exact Complex.ofReal_injective (by simpa using h)
  exact (hC.restrict_scalars hinj).affineIndependent

end Rollout_p0414_veronese_affineindependent

#check_dependency_graph "Rollout_p0414_veronese_affineindependent.veronese_affineIndependent" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let I := { ab // (ab.1.sum fun x n => n) ≤ p ∧ (ab.2.sum fun x n => n) ≤ q }; let v := fun z ab => ((↑ab).1.prod fun i n => z i ^ n) * (↑ab).2.prod fun i n => (starRingEnd ℂ) (z i) ^ n; AffineIndependent ℝ fun j => v (x j)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hrp\",\"statement\":\"r ≤ p + 1\"},{\"name\":\"hx\",\"statement\":\"Function.Injective x\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0414_veronese_affineindependent\",\"reconstructedProofSha256\":\"9fec76d1a8c882b2f60e565c6543c98c8cfbbee7c4988b8cba9438833d6daf2e\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p0414_veronese_affineindependent.veronese_affineIndependent\",\"topologySha256\":\"f61763d7c3c5fc654d7efba8545fcae2b44416562e2f20714ee9fb6cc89e5284\"}"

namespace Rollout_p0489_caristi_kirk_bmetric_fixed_point

-- graph_id: p0489_caristi_kirk_bmetric_fixed_point
-- topology_sha256: e3c506562155440bc52f1df77609cd5aa3e4eb91c6122edfd93871c94b5cd418
/- accepted add_to_file helper 1 -/
lemma caristi_iterate_phi_bound
    (X : Type*) (d : X × X → NNReal) (Φ : X → NNReal) (f : X → X) (A : ℝ)
    (hA : 1 < A)
    (hcaristi : ∀ x : X,
      (d (x, f x) : ℝ) ≤ (Φ x : ℝ) - A * (Φ (f x) : ℝ))
    (x₀ : X) (n : ℕ) :
    (Φ ((f^[n]) x₀) : ℝ) ≤ (Φ x₀ : ℝ) * (A⁻¹) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      let x := (f^[n]) x₀
      have hcar := hcaristi x
      have hdnonneg : (0:ℝ) ≤ d (x, f x) := NNReal.coe_nonneg _
      have hmul : A * (Φ (f x) : ℝ) ≤ (Φ x : ℝ) := by linarith
      have hnext : (Φ (f x) : ℝ) ≤ (Φ x : ℝ) / A := by
        rw [le_div_iff₀ (by linarith : 0 < A)]
        simpa [mul_comm] using hmul
      have hrw : (f^[n+1]) x₀ = f x := by
        simpa [x] using (Function.iterate_succ_apply' f n x₀)
      rw [hrw]
      calc
        (Φ (f x) : ℝ) ≤ (Φ x : ℝ) / A := hnext
        _ ≤ ((Φ x₀ : ℝ) * A⁻¹ ^ n) / A := by
          gcongr
        _ = (Φ x₀ : ℝ) * A⁻¹ ^ (n+1) := by
          ring_nf

lemma tendsto_dist_pair_atTop_prod_zero_of_summable
    {X : Type*} [PseudoMetricSpace X] (x : ℕ → X) (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n)
    (hadj : ∀ n, dist (x n) (x (n + 1)) ≤ a n)
    (hsum : Summable a) :
    Filter.Tendsto (fun p : ℕ × ℕ => dist (x p.1) (x p.2))
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
  have htail_summ : ∀ m : ℕ, Summable fun k : ℕ => a (m + k) := by
    intro m
    have h := (summable_nat_add_iff m).2 hsum
    simpa [Nat.add_comm] using h
  have htail_tendsto : Filter.Tendsto (fun m : ℕ => ∑' k : ℕ, a (m + k))
      Filter.atTop (nhds 0) := by
    simpa [Nat.add_comm] using tendsto_sum_nat_add a
  have hpair_le : ∀ {m n : ℕ}, m ≤ n →
      dist (x m) (x n) ≤ ∑' k : ℕ, a (m + k) := by
    intro m n hmn
    calc
      dist (x m) (x n) ≤ ∑ k ∈ Finset.Ico m n, a k :=
        dist_le_Ico_sum_of_dist_le hmn (fun {_} _ _ => hadj _)
      _ = ∑ k ∈ Finset.range (n - m), a (m + k) :=
        Finset.sum_Ico_eq_sum_range a m n
      _ ≤ ∑' k : ℕ, a (m + k) := by
        exact (htail_summ m).sum_le_tsum (Finset.range (n - m))
          (fun k hk => ha0 (m + k))
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop).1 htail_tendsto ε hε
  have hrect : {p : ℕ × ℕ | N ≤ p.1 ∧ N ≤ p.2} ∈ Filter.atTop ×ˢ Filter.atTop := by
    exact Filter.prod_mem_prod
      (Filter.mem_atTop_sets.2 ⟨N, fun b hb => hb⟩ : Set.Ici N ∈ (Filter.atTop : Filter ℕ))
      (Filter.mem_atTop_sets.2 ⟨N, fun b hb => hb⟩ : Set.Ici N ∈ (Filter.atTop : Filter ℕ))
  exact Filter.Eventually.mono hrect (by
    intro p hp
    have htail_nonneg : ∀ m, 0 ≤ ∑' k : ℕ, a (m + k) := by
      intro m
      exact tsum_nonneg (fun k => ha0 (m + k))
    have htail_lt1 : ∑' k : ℕ, a (p.1 + k) < ε := by
      have hdist := hN p.1 hp.1
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (htail_nonneg p.1)] at hdist
      exact hdist
    have htail_lt2 : ∑' k : ℕ, a (p.2 + k) < ε := by
      have hdist := hN p.2 hp.2
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (htail_nonneg p.2)] at hdist
      exact hdist
    have hdist_nonneg : 0 ≤ dist (x p.1) (x p.2) := dist_nonneg
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hdist_nonneg]
    rcases le_total p.1 p.2 with hle | hle
    · exact lt_of_le_of_lt (hpair_le hle) htail_lt1
    · rw [dist_comm]
      exact lt_of_le_of_lt (hpair_le hle) htail_lt2)

/- accepted add_to_file helper 2 -/
lemma bmetric_predist_four_max
    (X : Type*) (s : ℝ) (d : X × X → NNReal)
    (hs : 1 ≤ s)
    (hd_triangle : ∀ x y z : X,
      (d (x, y) : ℝ) ≤ s * ((d (x, z) : ℝ) + (d (z, y) : ℝ)))
    {N : ℕ} (hN : 0 < N)
    (hpow : (s + 2 * s ^ 2) ^ ((N : ℝ)⁻¹) ≤ 2)
    (x₁ x₂ x₃ x₄ : X) :
    (d (x₁, x₄) : NNReal) ^ ((N : ℝ)⁻¹) ≤
      2 * max ((d (x₁, x₂) : NNReal) ^ ((N : ℝ)⁻¹))
        (max ((d (x₂, x₃) : NNReal) ^ ((N : ℝ)⁻¹))
          ((d (x₃, x₄) : NNReal) ^ ((N : ℝ)⁻¹))) := by
  let p : ℝ := (N : ℝ)⁻¹
  let D : X × X → ℝ := fun xy => (d xy : ℝ)
  let M : ℝ := max (D (x₁, x₂)) (max (D (x₂, x₃)) (D (x₃, x₄)))
  have hs0 : 0 ≤ s := by linarith
  have hM0 : 0 ≤ M := by
    exact le_trans (NNReal.coe_nonneg _) (le_max_left _ _)
  have h12 : D (x₁, x₂) ≤ M := by exact le_max_left _ _
  have h23 : D (x₂, x₃) ≤ M := by
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have h34 : D (x₃, x₄) ≤ M := by
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have h24 : D (x₂, x₄) ≤ 2 * s * M := by
    have ht := hd_triangle x₂ x₄ x₃
    calc
      D (x₂, x₄) ≤ s * (D (x₂, x₃) + D (x₃, x₄)) := by simpa [D] using ht
      _ ≤ s * (M + M) := by gcongr
      _ = 2 * s * M := by ring
  have h14 : D (x₁, x₄) ≤ (s + 2 * s ^ 2) * M := by
    have ht := hd_triangle x₁ x₄ x₂
    calc
      D (x₁, x₄) ≤ s * (D (x₁, x₂) + D (x₂, x₄)) := by simpa [D] using ht
      _ ≤ s * (M + 2 * s * M) := by gcongr
      _ = (s + 2 * s ^ 2) * M := by ring
  have hp0 : 0 ≤ p := by positivity
  have hK0 : 0 ≤ s + 2 * s ^ 2 := by positivity
  have hreal :
      D (x₁, x₄) ^ p ≤
        2 * max (D (x₁, x₂) ^ p)
          (max (D (x₂, x₃) ^ p) (D (x₃, x₄) ^ p)) := by
    calc
      D (x₁, x₄) ^ p ≤ ((s + 2 * s ^ 2) * M) ^ p :=
        Real.rpow_le_rpow (NNReal.coe_nonneg _) h14 hp0
      _ = (s + 2 * s ^ 2) ^ p * M ^ p := Real.mul_rpow hK0 hM0
      _ ≤ 2 * M ^ p := by
        gcongr
      _ = 2 * max (D (x₁, x₂) ^ p)
          (max (D (x₂, x₃) ^ p) (D (x₃, x₄) ^ p)) := by
        dsimp [M, D]
        rw [Real.rpow_max (NNReal.coe_nonneg _)
          (by
            exact le_trans (NNReal.coe_nonneg _) (le_max_left _ _)) hp0]
        rw [Real.rpow_max (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) hp0]
  exact_mod_cast (by simpa [p, D] using hreal)

/- accepted add_to_file helper 3 -/
lemma caristi_orbit_tendsto_pair
    (X : Type*) (s : ℝ) (d : X × X → NNReal) (Φ : X → NNReal)
    (f : X → X) (A : ℝ)
    (hs : 1 ≤ s)
    (hd_zero : ∀ x y : X, d (x, y) = 0 ↔ x = y)
    (hd_symm : ∀ x y : X, d (x, y) = d (y, x))
    (hd_triangle : ∀ x y z : X,
      (d (x, y) : ℝ) ≤ s * ((d (x, z) : ℝ) + (d (z, y) : ℝ)))
    (hA : 1 < A)
    (hcaristi : ∀ x : X,
      (d (x, f x) : ℝ) ≤ (Φ x : ℝ) - A * (Φ (f x) : ℝ))
    (x₀ : X) :
    Filter.Tendsto (fun p : ℕ × ℕ => d ((f^[p.1]) x₀, (f^[p.2]) x₀))
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
  let x : ℕ → X := fun n => (f^[n]) x₀
  let K : ℝ := s + 2 * s ^ 2
  obtain ⟨N, hNgt⟩ := exists_nat_gt K
  have hKpos : 0 < K := by
    dsimp [K]
    positivity
  have hNpos : 0 < N := by
    have hNR : (0:ℝ) < N := lt_trans hKpos hNgt
    exact_mod_cast hNR
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hNpos
  let p : ℝ := (N : ℝ)⁻¹
  have hp0 : 0 ≤ p := by positivity
  have hpne : p ≠ 0 := by positivity
  have hK0 : 0 ≤ K := le_of_lt hKpos
  have hbase : K ≤ (2 ^ N : ℝ) := by
    have hNpow : (N : ℝ) < (2 ^ N : ℝ) := by
      exact_mod_cast (Nat.lt_two_pow_self : N < 2 ^ N)
    linarith
  have hpow : K ^ p ≤ 2 := by
    calc
      K ^ p ≤ ((2 ^ N : ℝ) ^ p) := Real.rpow_le_rpow hK0 hbase hp0
      _ = 2 := by
        dsimp [p]
        rw [← Real.rpow_natCast (2 : ℝ) N]
        rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        field_simp [hN0]
        norm_num
  let q : X → X → NNReal := fun u v => (d (u, v) : NNReal) ^ p
  have hq_self : ∀ u : X, q u u = 0 := by
    intro u
    have hduu : d (u, u) = 0 := (hd_zero u u).2 rfl
    simp [q, hduu, hpne]
  have hq_comm : ∀ u v : X, q u v = q v u := by
    intro u v
    simp [q, hd_symm u v]
  have hq_four : ∀ x₁ x₂ x₃ x₄ : X,
      q x₁ x₄ ≤ 2 * max (q x₁ x₂) (max (q x₂ x₃) (q x₃ x₄)) := by
    intro x₁ x₂ x₃ x₄
    simpa [q, p, K] using
      bmetric_predist_four_max X s d hs hd_triangle hNpos (by simpa [K, p] using hpow)
        x₁ x₂ x₃ x₄
  letI P : PseudoMetricSpace X := PseudoMetricSpace.ofPreNNDist q hq_self hq_comm
  have hphi : ∀ n : ℕ, (Φ (x n) : ℝ) ≤ (Φ x₀ : ℝ) * A⁻¹ ^ n := by
    intro n
    simpa [x] using caristi_iterate_phi_bound X d Φ f A hA hcaristi x₀ n
  have hstep_phi : ∀ n : ℕ, (d (x n, x (n + 1)) : ℝ) ≤ (Φ (x n) : ℝ) := by
    intro n
    have hcar := hcaristi (x n)
    have hrw : x (n + 1) = f (x n) := by
      simpa [x] using (Function.iterate_succ_apply' f n x₀)
    have hdnonneg : (0:ℝ) ≤ d (x n, f (x n)) := NNReal.coe_nonneg _
    have hAphi : (0:ℝ) ≤ A * (Φ (f (x n)) : ℝ) := by positivity
    rw [hrw]
    linarith
  let C : ℝ := (Φ x₀ : ℝ) ^ p
  let r : ℝ := A⁻¹ ^ p
  have hqstep_bound : ∀ n : ℕ,
      ((q (x n) (x (n + 1)) : NNReal) : ℝ) ≤ C * r ^ n := by
    intro n
    have hpow_exch : ((A⁻¹ : ℝ) ^ n) ^ p = (A⁻¹ ^ p) ^ n := by
      rw [← Real.rpow_natCast (A⁻¹ : ℝ) n, ← Real.rpow_natCast ((A⁻¹ : ℝ) ^ p) n]
      rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ A⁻¹)]
      rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ A⁻¹)]
      congr 1
      ring
    calc
      (((q (x n) (x (n + 1)) : NNReal) : ℝ)) = (d (x n, x (n + 1)) : ℝ) ^ p := by
        simp [q, NNReal.coe_rpow]
      _ ≤ (Φ (x n) : ℝ) ^ p :=
        Real.rpow_le_rpow (NNReal.coe_nonneg _) (hstep_phi n) hp0
      _ ≤ ((Φ x₀ : ℝ) * A⁻¹ ^ n) ^ p :=
        Real.rpow_le_rpow (NNReal.coe_nonneg _) (hphi n) hp0
      _ = C * r ^ n := by
        dsimp [C, r]
        rw [Real.mul_rpow (NNReal.coe_nonneg _) (by positivity : (0:ℝ) ≤ A⁻¹ ^ n)]
        rw [hpow_exch]
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact Real.rpow_nonneg (by positivity : (0:ℝ) ≤ A⁻¹) p
  have hr1 : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one (by positivity : (0:ℝ) ≤ A⁻¹)
      (inv_lt_one_of_one_lt₀ hA) (by positivity : 0 < p)
  have hqstep_summable : Summable fun n : ℕ =>
      ((q (x n) (x (n + 1)) : NNReal) : ℝ) := by
    have hgeom : Summable fun n : ℕ => r ^ n := summable_geometric_of_lt_one hr0 hr1
    exact Summable.of_nonneg_of_le (fun n => NNReal.coe_nonneg _)
      hqstep_bound (hgeom.mul_left C)
  have hrho_tendsto :
      Filter.Tendsto (fun pair : ℕ × ℕ => dist (x pair.1) (x pair.2))
        (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
    exact tendsto_dist_pair_atTop_prod_zero_of_summable x
      (fun n => ((q (x n) (x (n + 1)) : NNReal) : ℝ))
      (fun n => NNReal.coe_nonneg _)
      (fun n => PseudoMetricSpace.dist_ofPreNNDist_le q hq_self hq_comm (x n) (x (n + 1)))
      hqstep_summable
  have hq_lower : ∀ pair : ℕ × ℕ,
      ((q (x pair.1) (x pair.2) : NNReal) : ℝ) ≤ 2 * dist (x pair.1) (x pair.2) := by
    intro pair
    exact PseudoMetricSpace.le_two_mul_dist_ofPreNNDist q hq_self hq_comm hq_four
      (x pair.1) (x pair.2)
  have hq_tendsto :
      Filter.Tendsto (fun pair : ℕ × ℕ =>
          ((q (x pair.1) (x pair.2) : NNReal) : ℝ))
        (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hrho_tendsto.const_mul (2 : ℝ))
      (fun pair => NNReal.coe_nonneg _) hq_lower
  have hpow_tendsto :
      Filter.Tendsto (fun pair : ℕ × ℕ =>
          (((q (x pair.1) (x pair.2) : NNReal) : ℝ)) ^ N)
        (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
    have h := hq_tendsto.pow N
    simpa [hNpos.ne'] using h
  have hpow_eq :
      (fun pair : ℕ × ℕ => (((q (x pair.1) (x pair.2) : NNReal) : ℝ)) ^ N) =
        fun pair : ℕ × ℕ => (d (x pair.1, x pair.2) : ℝ) := by
    funext pair
    simp [q, p, NNReal.coe_rpow,
      Real.rpow_inv_natCast_pow (NNReal.coe_nonneg (d (x pair.1, x pair.2))) hNpos.ne']
  rw [hpow_eq] at hpow_tendsto
  exact (NNReal.tendsto_coe).1 (by simpa [x] using hpow_tendsto)

/- verified submission -/
theorem caristi_kirk_bMetric_fixed_point
    (X : Type*) [Nonempty X]
    (s : ℝ) (d : X × X → NNReal) (Φ : X → NNReal) (f : X → X) (A : ℝ)
    (hs : 1 ≤ s)
    (hd_zero : ∀ x y : X, d (x, y) = 0 ↔ x = y)
    (hd_symm : ∀ x y : X, d (x, y) = d (y, x))
    (hd_triangle : ∀ x y z : X,
      (d (x, y) : ℝ) ≤ s * ((d (x, z) : ℝ) + (d (z, y) : ℝ)))
    (hcomplete : ∀ x : ℕ → X,
      Filter.Tendsto (fun p : ℕ × ℕ => d (x p.1, x p.2))
        (Filter.atTop ×ˢ Filter.atTop) (nhds 0) →
      ∃ u : X, Filter.Tendsto (fun n : ℕ => d (x n, u)) Filter.atTop (nhds 0))
    (hA : 1 < A)
    (hf_continuous : ∀ (x : ℕ → X) (u : X),
      Filter.Tendsto (fun n : ℕ => d (x n, u)) Filter.atTop (nhds 0) →
      Filter.Tendsto (fun n : ℕ => d (f (x n), f u)) Filter.atTop (nhds 0))
    (hcaristi : ∀ x : X,
      (d (x, f x) : ℝ) ≤ (Φ x : ℝ) - A * (Φ (f x) : ℝ)) :
    ∀ x₀ : X, ∃ u : X, f u = u ∧
      Filter.Tendsto (fun n : ℕ => d ((f^[n]) x₀, u)) Filter.atTop (nhds 0) := by
  intro x₀
  let x : ℕ → X := fun n => (f^[n]) x₀
  have hcauchy :
      Filter.Tendsto (fun p : ℕ × ℕ => d (x p.1, x p.2))
        (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
    simpa [x] using caristi_orbit_tendsto_pair X s d Φ f A hs hd_zero hd_symm
      hd_triangle hA hcaristi x₀
  obtain ⟨u, hu⟩ := hcomplete x hcauchy
  have hfx : Filter.Tendsto (fun n : ℕ => d (f (x n), f u)) Filter.atTop (nhds 0) :=
    hf_continuous x u hu
  have hshift : Filter.Tendsto (fun n : ℕ => d (x (n + 1), u)) Filter.atTop (nhds 0) := by
    simpa [Function.comp_def, Nat.add_comm] using
      hu.comp (Filter.tendsto_add_atTop_nat 1)
  have hupper_tendsto : Filter.Tendsto
      (fun n : ℕ => s * ((d (f (x n), f u) : ℝ) + (d (x (n + 1), u) : ℝ)))
      Filter.atTop (nhds 0) := by
    have hfxR : Filter.Tendsto (fun n : ℕ => (d (f (x n), f u) : ℝ))
        Filter.atTop (nhds 0) := (NNReal.tendsto_coe).2 hfx
    have hshiftR : Filter.Tendsto (fun n : ℕ => (d (x (n + 1), u) : ℝ))
        Filter.atTop (nhds 0) := (NNReal.tendsto_coe).2 hshift
    simpa using (hfxR.add hshiftR).const_mul s
  have hineq : ∀ n : ℕ,
      (d (f u, u) : ℝ) ≤
        s * ((d (f (x n), f u) : ℝ) + (d (x (n + 1), u) : ℝ)) := by
    intro n
    have ht := hd_triangle (f u) u (f (x n))
    have hsymm1 : (d (f u, f (x n)) : ℝ) = (d (f (x n), f u) : ℝ) := by
      exact congrArg NNReal.toReal (hd_symm (f u) (f (x n)))
    have hrw : x (n + 1) = f (x n) := by
      simpa [x] using (Function.iterate_succ_apply' f n x₀)
    calc
      (d (f u, u) : ℝ) ≤ s * ((d (f u, f (x n)) : ℝ) + (d (f (x n), u) : ℝ)) := ht
      _ = s * ((d (f (x n), f u) : ℝ) + (d (x (n + 1), u) : ℝ)) := by
        rw [hsymm1, ← hrw]
  have hconst_tendsto_real : Filter.Tendsto (fun _ : ℕ => (d (f u, u) : ℝ))
      Filter.atTop (nhds 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper_tendsto
      (fun _ => NNReal.coe_nonneg _) hineq
  have hconst_tendsto : Filter.Tendsto (fun _ : ℕ => d (f u, u))
      Filter.atTop (nhds 0) := (NNReal.tendsto_coe).1 hconst_tendsto_real
  have hzero : d (f u, u) = 0 := by
    have h := tendsto_nhds_unique hconst_tendsto tendsto_const_nhds
    exact h.symm
  have hfixed : f u = u := (hd_zero (f u) u).1 hzero
  exact ⟨u, hfixed, by simpa [x] using hu⟩

end Rollout_p0489_caristi_kirk_bmetric_fixed_point

#check_dependency_graph "Rollout_p0489_caristi_kirk_bmetric_fixed_point.caristi_kirk_bMetric_fixed_point" against "{\"edges\":[{\"conclusion\":{\"name\":\"hcauchy\",\"statement\":\"Filter.Tendsto (fun p => d (x p.1, x p.2)) (Filter.atTop ×ˢ Filter.atTop) (nhds 0)\"},\"graphEdgeId\":\"h_001_hcauchy\",\"premises\":[{\"name\":\"hs\",\"statement\":\"1 ≤ s\"},{\"name\":\"hd_zero\",\"statement\":\"∀ (x y : X), d (x, y) = 0 ↔ x = y\"},{\"name\":\"hd_symm\",\"statement\":\"∀ (x y : X), d (x, y) = d (y, x)\"},{\"name\":\"hd_triangle\",\"statement\":\"∀ (x y z : X), ↑(d (x, y)) ≤ s * (↑(d (x, z)) + ↑(d (z, y)))\"},{\"name\":\"hA\",\"statement\":\"1 < A\"},{\"name\":\"hcaristi\",\"statement\":\"∀ (x : X), ↑(d (x, f x)) ≤ ↑(Φ x) - A * ↑(Φ (f x))\"}],\"rawEdgeId\":\"telescope_17\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∃ u, f u = u ∧ Filter.Tendsto (fun n => d (f^[n] x₀, u)) Filter.atTop (nhds 0)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hd_zero\",\"statement\":\"∀ (x y : X), d (x, y) = 0 ↔ x = y\"},{\"name\":\"hd_symm\",\"statement\":\"∀ (x y : X), d (x, y) = d (y, x)\"},{\"name\":\"hd_triangle\",\"statement\":\"∀ (x y z : X), ↑(d (x, y)) ≤ s * (↑(d (x, z)) + ↑(d (z, y)))\"},{\"name\":\"hcomplete\",\"statement\":\"∀ (x : ℕ → X), Filter.Tendsto (fun p => d (x p.1, x p.2)) (Filter.atTop ×ˢ Filter.atTop) (nhds 0) → ∃ u, Filter.Tendsto (fun n => d (x n, u)) Filter.atTop (nhds 0)\"},{\"name\":\"hf_continuous\",\"statement\":\"∀ (x : ℕ → X) (u : X), Filter.Tendsto (fun n => d (x n, u)) Filter.atTop (nhds 0) → Filter.Tendsto (fun n => d (f (x n), f u)) Filter.atTop (nhds 0)\"},{\"name\":\"hcauchy\",\"statement\":\"Filter.Tendsto (fun p => d (x p.1, x p.2)) (Filter.atTop ×ˢ Filter.atTop) (nhds 0)\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0489_caristi_kirk_bmetric_fixed_point\",\"reconstructedProofSha256\":\"fb7c2ed30a2457a3fe100abbf439e471d2a98f12fac28c3d6456b7c379bc0e0f\",\"selectedEdgeCount\":2,\"theoremName\":\"Rollout_p0489_caristi_kirk_bmetric_fixed_point.caristi_kirk_bMetric_fixed_point\",\"topologySha256\":\"e3c506562155440bc52f1df77609cd5aa3e4eb91c6122edfd93871c94b5cd418\"}"

namespace Rollout_p0496_normalized_modified_kbessel_nonincreasing_

-- graph_id: p0496_normalized_modified_kbessel_nonincreasing_
-- topology_sha256: 76e85da9bebe4ed58125c383835dd52ecbe6599bc93f9169392c1b938160e0ad
/- accepted add_to_file helper 1 -/
noncomputable def risingProd (y : ℝ) (r : ℕ) : ℝ :=
  ∏ j ∈ Finset.range r, (y + (j : ℝ))

lemma risingProd_pos {y : ℝ} (hy : 0 < y) (r : ℕ) : 0 < risingProd y r := by
  unfold risingProd
  exact Finset.prod_pos fun j hj => by positivity

lemma risingProd_nonneg {y : ℝ} (hy : 0 ≤ y) (r : ℕ) : 0 ≤ risingProd y r := by
  unfold risingProd
  exact Finset.prod_nonneg fun j hj => by positivity

lemma Gamma_add_nat_cast_eq_mul_risingProd {y : ℝ} (hy : 0 < y) (r : ℕ) :
    Real.Gamma (y + (r : ℝ)) = Real.Gamma y * risingProd y r := by
  induction r with
  | zero =>
      simp [risingProd]
  | succ r ih =>
      have hpos : 0 < y + (r : ℝ) := by positivity
      calc
        Real.Gamma (y + ((r + 1 : ℕ) : ℝ))
            = Real.Gamma ((y + (r : ℝ)) + 1) := by
                congr 1
                norm_num [Nat.cast_add, Nat.cast_one]
                ring
        _ = (y + (r : ℝ)) * Real.Gamma (y + (r : ℝ)) := by
                exact Real.Gamma_add_one hpos.ne'
        _ = (y + (r : ℝ)) * (Real.Gamma y * risingProd y r) := by
                rw [ih]
        _ = Real.Gamma y * risingProd y (r + 1) := by
                simp [risingProd, Finset.prod_range_succ, mul_comm, mul_left_comm]

/- accepted add_to_file helper 2 -/
lemma kGamma_ratio_eq_inv_mul_risingProd {k ν : ℝ} (hk : 0 < k) (hν : -k < ν)
    (r : ℕ) :
    (k ^ ((ν + k) / k - 1) * Real.Gamma ((ν + k) / k)) /
        (k ^ (((r : ℝ) * k + ν + k) / k - 1) *
          Real.Gamma (((r : ℝ) * k + ν + k) / k))
      = 1 / (k ^ r * risingProd (ν / k + 1) r) := by
  let y : ℝ := ν / k + 1
  have hy : 0 < y := by
    have hmul : (-1 : ℝ) * k < ν := by
      simpa using hν
    have hνk : -1 < ν / k := (lt_div_iff₀ hk).mpr hmul
    dsimp [y]
    linarith
  have harg1 : (ν + k) / k = y := by
    dsimp [y]
    field_simp [hk.ne']
  have harg2 : ((r : ℝ) * k + ν + k) / k = y + (r : ℝ) := by
    dsimp [y]
    field_simp [hk.ne']
    ring
  have hexp2 : y + (r : ℝ) - 1 = (y - 1) + (r : ℝ) := by ring
  have hΓ : Real.Gamma (y + (r : ℝ)) = Real.Gamma y * risingProd y r :=
    Gamma_add_nat_cast_eq_mul_risingProd hy r
  calc
    (k ^ ((ν + k) / k - 1) * Real.Gamma ((ν + k) / k)) /
        (k ^ (((r : ℝ) * k + ν + k) / k - 1) *
          Real.Gamma (((r : ℝ) * k + ν + k) / k))
        = (k ^ (y - 1) * Real.Gamma y) /
          (k ^ ((y + (r : ℝ)) - 1) * Real.Gamma (y + (r : ℝ))) := by
            rw [harg1, harg2]
    _ = (k ^ (y - 1) * Real.Gamma y) /
          ((k ^ (y - 1) * k ^ (r : ℝ)) *
            (Real.Gamma y * risingProd y r)) := by
            rw [hexp2, Real.rpow_add hk, hΓ]
    _ = 1 / (k ^ r * risingProd y r) := by
            rw [Real.rpow_natCast]
            have hkp : k ^ (y - 1) ≠ 0 := (Real.rpow_pos_of_pos hk _).ne'
            have hΓp : Real.Gamma y ≠ 0 := (Real.Gamma_pos_of_pos hy).ne'
            have hPp : risingProd y r ≠ 0 := (risingProd_pos hy r).ne'
            have hkn : k ^ r ≠ 0 := pow_ne_zero r hk.ne'
            field_simp [hkp, hΓp, hPp, hkn]
    _ = 1 / (k ^ r * risingProd (ν / k + 1) r) := by rfl

/- accepted add_to_file helper 3 -/
lemma kBessel_term_eq {k x ν : ℝ} (hk : 0 < k) (hν : -k < ν) (r : ℕ) :
    (k ^ ((ν + k) / k - 1) * Real.Gamma ((ν + k) / k)) /
        ((k ^ (((r : ℝ) * k + ν + k) / k - 1) *
          Real.Gamma (((r : ℝ) * k + ν + k) / k)) *
          (4 : ℝ) ^ r * (r.factorial : ℝ)) * x ^ (2 * r)
      = x ^ (2 * r) /
        ((4 * k) ^ r * (r.factorial : ℝ) * risingProd (ν / k + 1) r) := by
  have hratio := kGamma_ratio_eq_inv_mul_risingProd hk hν r
  rw [div_mul_eq_div_div, div_mul_eq_div_div, hratio]
  have hP : risingProd (ν / k + 1) r ≠ 0 := by
    have hmul : (-1 : ℝ) * k < ν := by simpa using hν
    have hνk : -1 < ν / k := (lt_div_iff₀ hk).mpr hmul
    have hy : 0 < ν / k + 1 := by linarith
    exact (risingProd_pos hy r).ne'
  have hkpow : k ^ r ≠ 0 := pow_ne_zero r hk.ne'
  have hfour : (4 : ℝ) ^ r ≠ 0 := pow_ne_zero r (by norm_num)
  have hfact : (r.factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero r)
  have h4k : (4 * k) ^ r ≠ 0 := pow_ne_zero r (mul_pos (by norm_num) hk).ne'
  field_simp [hP, hkpow, hfour, hfact, h4k]
  rw [mul_pow]
  ring

/- accepted add_to_file helper 4 -/
lemma risingProd_mono {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z) (r : ℕ) :
    risingProd y r ≤ risingProd z r := by
  unfold risingProd
  exact Finset.prod_le_prod
    (fun j hj => by positivity)
    (fun j hj => by linarith)

lemma kBessel_term_nonneg {k x ν : ℝ} (hk : 0 < k) (hx : 0 ≤ x) (hν : -k < ν) (r : ℕ) :
    0 ≤ (k ^ ((ν + k) / k - 1) * Real.Gamma ((ν + k) / k)) /
        ((k ^ (((r : ℝ) * k + ν + k) / k - 1) *
          Real.Gamma (((r : ℝ) * k + ν + k) / k)) *
          (4 : ℝ) ^ r * (r.factorial : ℝ)) * x ^ (2 * r) := by
  rw [kBessel_term_eq hk hν r]
  have hmul : (-1 : ℝ) * k < ν := by simpa using hν
  have hνk : -1 < ν / k := (lt_div_iff₀ hk).mpr hmul
  have hy : 0 < ν / k + 1 := by linarith
  have hden : 0 < (4 * k) ^ r * (r.factorial : ℝ) * risingProd (ν / k + 1) r :=
    mul_pos (mul_pos (pow_pos (mul_pos (by norm_num) hk) _)
      (by exact_mod_cast Nat.factorial_pos r)) (risingProd_pos hy r)
  exact div_nonneg (pow_nonneg hx _) hden.le

lemma kBessel_term_antitone {k x ν μ : ℝ} (hk : 0 < k) (hx : 0 ≤ x)
    (hν : -k < ν) (hνμ : ν ≤ μ) (r : ℕ) :
    (k ^ ((μ + k) / k - 1) * Real.Gamma ((μ + k) / k)) /
        ((k ^ (((r : ℝ) * k + μ + k) / k - 1) *
          Real.Gamma (((r : ℝ) * k + μ + k) / k)) *
          (4 : ℝ) ^ r * (r.factorial : ℝ)) * x ^ (2 * r)
    ≤ (k ^ ((ν + k) / k - 1) * Real.Gamma ((ν + k) / k)) /
        ((k ^ (((r : ℝ) * k + ν + k) / k - 1) *
          Real.Gamma (((r : ℝ) * k + ν + k) / k)) *
          (4 : ℝ) ^ r * (r.factorial : ℝ)) * x ^ (2 * r) := by
  have hμ : -k < μ := lt_of_lt_of_le hν hνμ
  rw [kBessel_term_eq hk hμ r, kBessel_term_eq hk hν r]
  have hmulν : (-1 : ℝ) * k < ν := by simpa using hν
  have hνk : -1 < ν / k := (lt_div_iff₀ hk).mpr hmulν
  have hyn : 0 < ν / k + 1 := by linarith
  have hmulμ : (-1 : ℝ) * k < μ := by simpa using hμ
  have hμk : -1 < μ / k := (lt_div_iff₀ hk).mpr hmulμ
  have hym : 0 < μ / k + 1 := by linarith
  have hyνμ : ν / k + 1 ≤ μ / k + 1 := by
    have : ν / k ≤ μ / k := div_le_div_of_nonneg_right hνμ hk.le
    linarith
  have hP : risingProd (ν / k + 1) r ≤ risingProd (μ / k + 1) r :=
    risingProd_mono hyn.le hyνμ r
  have hbase : 0 < (4 * k) ^ r * (r.factorial : ℝ) :=
    mul_pos (pow_pos (mul_pos (by norm_num) hk) _)
      (by exact_mod_cast Nat.factorial_pos r)
  have hDν : 0 < (4 * k) ^ r * (r.factorial : ℝ) * risingProd (ν / k + 1) r :=
    mul_pos hbase (risingProd_pos hyn r)
  have hD : (4 * k) ^ r * (r.factorial : ℝ) * risingProd (ν / k + 1) r ≤
      (4 * k) ^ r * (r.factorial : ℝ) * risingProd (μ / k + 1) r :=
    mul_le_mul_of_nonneg_left hP hbase.le
  exact div_le_div_of_nonneg_left (pow_nonneg hx _) hDν hD

/- accepted add_to_file helper 5 -/
lemma factorial_mul_min_pow_le_risingProd {y : ℝ} (hy : 0 < y) (r : ℕ) :
    (r.factorial : ℝ) * (min y 1) ^ r ≤ risingProd y r := by
  let m : ℝ := min y 1
  have hm0 : 0 ≤ m := le_min hy.le zero_le_one
  have hmy : m ≤ y := min_le_left _ _
  have hm1 : m ≤ 1 := min_le_right _ _
  have hfacprod : (∏ j ∈ Finset.range r, ((j : ℝ) + 1)) = (r.factorial : ℝ) := by
    exact_mod_cast Finset.prod_range_add_one_eq_factorial r
  calc
    (r.factorial : ℝ) * m ^ r
        = (∏ j ∈ Finset.range r, m) *
            (∏ j ∈ Finset.range r, ((j : ℝ) + 1)) := by
          rw [hfacprod, Finset.prod_const, Finset.card_range, mul_comm]
    _ = ∏ j ∈ Finset.range r, (m * ((j : ℝ) + 1)) := by
          rw [Finset.prod_mul_distrib]
    _ ≤ risingProd y r := by
          unfold risingProd
          refine Finset.prod_le_prod ?_ ?_
          · intro j hj
            exact mul_nonneg hm0 (by positivity)
          · intro j hj
            have hj0 : 0 ≤ (j : ℝ) := by positivity
            nlinarith

/- accepted add_to_file helper 6 -/
lemma kBessel_term_le_exp_term {k x ν : ℝ} (hk : 0 < k) (hx : 0 ≤ x)
    (hν : -k < ν) (r : ℕ) :
    (k ^ ((ν + k) / k - 1) * Real.Gamma ((ν + k) / k)) /
        ((k ^ (((r : ℝ) * k + ν + k) / k - 1) *
          Real.Gamma (((r : ℝ) * k + ν + k) / k)) *
          (4 : ℝ) ^ r * (r.factorial : ℝ)) * x ^ (2 * r)
      ≤ (x ^ 2 / (4 * k * min (ν / k + 1) 1)) ^ r / (r.factorial : ℝ) := by
  rw [kBessel_term_eq hk hν r]
  have hmul : (-1 : ℝ) * k < ν := by simpa using hν
  have hνk : -1 < ν / k := (lt_div_iff₀ hk).mpr hmul
  have hy : 0 < ν / k + 1 := by linarith
  let m : ℝ := min (ν / k + 1) 1
  have hm : 0 < m := lt_min hy zero_lt_one
  have hlow : (r.factorial : ℝ) * m ^ r ≤ risingProd (ν / k + 1) r :=
    factorial_mul_min_pow_le_risingProd hy r
  have hmP : m ^ r ≤ risingProd (ν / k + 1) r := by
    have hfac1 : (1 : ℝ) ≤ (r.factorial : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos r)
    calc
      m ^ r = 1 * m ^ r := by ring
      _ ≤ (r.factorial : ℝ) * m ^ r :=
          mul_le_mul_of_nonneg_right hfac1 (pow_nonneg hm.le r)
      _ ≤ risingProd (ν / k + 1) r := hlow
  have hA : 0 < (4 * k) ^ r := pow_pos (mul_pos (by norm_num) hk) r
  have hF : 0 < (r.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos r
  have hD0 : 0 < (4 * k) ^ r * (r.factorial : ℝ) * risingProd (ν / k + 1) r :=
    mul_pos (mul_pos hA hF) (risingProd_pos hy r)
  have hB0 : 0 < (4 * k) ^ r * m ^ r * (r.factorial : ℝ) :=
    mul_pos (mul_pos hA (pow_pos hm r)) hF
  have hBD : (4 * k) ^ r * m ^ r * (r.factorial : ℝ) ≤
      (4 * k) ^ r * (r.factorial : ℝ) * risingProd (ν / k + 1) r := by
    have h := mul_le_mul_of_nonneg_left hmP (mul_nonneg hA.le hF.le)
    nlinarith
  have hnum : 0 ≤ (x ^ 2) ^ r := pow_nonneg (sq_nonneg x) r
  calc
    x ^ (2 * r) /
        ((4 * k) ^ r * (r.factorial : ℝ) * risingProd (ν / k + 1) r)
        = (x ^ 2) ^ r /
          ((4 * k) ^ r * (r.factorial : ℝ) * risingProd (ν / k + 1) r) := by
          rw [pow_mul]
    _ ≤ (x ^ 2) ^ r / ((4 * k) ^ r * m ^ r * (r.factorial : ℝ)) :=
          div_le_div_of_nonneg_left hnum hB0 hBD
    _ = (x ^ 2 / (4 * k * m)) ^ r / (r.factorial : ℝ) := by
          rw [div_pow, mul_pow, mul_pow]
          ring
    _ = (x ^ 2 / (4 * k * min (ν / k + 1) 1)) ^ r / (r.factorial : ℝ) := by rfl

lemma summable_kBessel_term {k x ν : ℝ} (hk : 0 < k) (hx : 0 ≤ x) (hν : -k < ν) :
    Summable fun r : ℕ =>
      (k ^ ((ν + k) / k - 1) * Real.Gamma ((ν + k) / k)) /
        ((k ^ (((r : ℝ) * k + ν + k) / k - 1) *
          Real.Gamma (((r : ℝ) * k + ν + k) / k)) *
          (4 : ℝ) ^ r * (r.factorial : ℝ)) * x ^ (2 * r) := by
  exact Summable.of_nonneg_of_le
    (fun r => kBessel_term_nonneg hk hx hν r)
    (fun r => kBessel_term_le_exp_term hk hx hν r)
    (Real.summable_pow_div_factorial _)

/- accepted add_to_file helper 7 -/
lemma Real.rpow_finset_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (a : ℝ) :
    (∏ i ∈ s, f i) ^ a = ∏ i ∈ s, f i ^ a := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        Real.mul_rpow (hf i (Finset.mem_insert_self i s))
          (Finset.prod_nonneg fun j hj => hf j (Finset.mem_insert_of_mem hj)),
        ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

lemma weighted_geomean_div {N B P Q α : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hP : 0 < P) (hQ : 0 < Q)
    (hsum : α + (1 - α) = 1) :
    (N / (B * P)) ^ α * (N / (B * Q)) ^ (1 - α) =
      N / (B * (P ^ α * Q ^ (1 - α))) := by
  rw [Real.div_rpow hN.le (mul_pos hB hP).le α,
    Real.div_rpow hN.le (mul_pos hB hQ).le (1 - α),
    Real.mul_rpow hB.le hP.le, Real.mul_rpow hB.le hQ.le]
  have hNpow : N ^ α * N ^ (1 - α) = N := by
    rw [← Real.rpow_add hN, hsum, Real.rpow_one]
  have hBpow : B ^ α * B ^ (1 - α) = B := by
    rw [← Real.rpow_add hB, hsum, Real.rpow_one]
  have hNα : N ^ α ≠ 0 := (Real.rpow_pos_of_pos hN α).ne'
  have hNβ : N ^ (1 - α) ≠ 0 := (Real.rpow_pos_of_pos hN (1-α)).ne'
  have hBα : B ^ α ≠ 0 := (Real.rpow_pos_of_pos hB α).ne'
  have hBβ : B ^ (1 - α) ≠ 0 := (Real.rpow_pos_of_pos hB (1-α)).ne'
  have hPα : P ^ α ≠ 0 := (Real.rpow_pos_of_pos hP α).ne'
  have hQβ : Q ^ (1 - α) ≠ 0 := (Real.rpow_pos_of_pos hQ (1-α)).ne'
  field_simp [hNα, hNβ, hBα, hBβ, hPα, hQβ]
  rw [hNpow, hBpow]
  ring

/- accepted add_to_file helper 8 -/
lemma weighted_risingProd_le_risingProd {y z α : ℝ} (hy : 0 < y) (hz : 0 < z)
    (hα : 0 ≤ α) (hβ : 0 ≤ 1 - α) (r : ℕ) :
    risingProd y r ^ α * risingProd z r ^ (1 - α) ≤
      risingProd (α * y + (1 - α) * z) r := by
  have hsum : α + (1 - α) = 1 := by ring
  unfold risingProd
  rw [Real.rpow_finset_prod _ _ (fun j hj => by positivity) α,
    Real.rpow_finset_prod _ _ (fun j hj => by positivity) (1 - α),
    ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod ?_ ?_
  · intro j hj
    exact mul_nonneg (Real.rpow_nonneg (by positivity) α)
      (Real.rpow_nonneg (by positivity) (1 - α))
  · intro j hj
    have hfactor : α * (y + (j : ℝ)) + (1 - α) * (z + (j : ℝ)) =
        α * y + (1 - α) * z + (j : ℝ) := by
      nlinarith
    rw [← hfactor]
    exact Real.geom_mean_le_arith_mean2_weighted hα hβ (by positivity) (by positivity) hsum

/- accepted add_to_file helper 9 -/
lemma kBessel_term_logConvex {k x ν₁ ν₂ α : ℝ} (hk : 0 < k) (hx : 0 < x)
    (hν₁ : -k < ν₁) (hν₂ : -k < ν₂) (hα : 0 ≤ α) (hα₁ : α ≤ 1) (r : ℕ) :
    (k ^ (((α * ν₁ + (1 - α) * ν₂) + k) / k - 1) *
          Real.Gamma (((α * ν₁ + (1 - α) * ν₂) + k) / k)) /
        ((k ^ (((r : ℝ) * k + (α * ν₁ + (1 - α) * ν₂) + k) / k - 1) *
          Real.Gamma (((r : ℝ) * k + (α * ν₁ + (1 - α) * ν₂) + k) / k)) *
          (4 : ℝ) ^ r * (r.factorial : ℝ)) * x ^ (2 * r)
      ≤
      ((k ^ ((ν₁ + k) / k - 1) * Real.Gamma ((ν₁ + k) / k)) /
        ((k ^ (((r : ℝ) * k + ν₁ + k) / k - 1) *
          Real.Gamma (((r : ℝ) * k + ν₁ + k) / k)) *
          (4 : ℝ) ^ r * (r.factorial : ℝ)) * x ^ (2 * r)) ^ α *
      ((k ^ ((ν₂ + k) / k - 1) * Real.Gamma ((ν₂ + k) / k)) /
        ((k ^ (((r : ℝ) * k + ν₂ + k) / k - 1) *
          Real.Gamma (((r : ℝ) * k + ν₂ + k) / k)) *
          (4 : ℝ) ^ r * (r.factorial : ℝ)) * x ^ (2 * r)) ^ (1 - α) := by
  have hβ : 0 ≤ 1 - α := by linarith
  have hmul₁ : (-1 : ℝ) * k < ν₁ := by simpa using hν₁
  have hν₁k : -1 < ν₁ / k := (lt_div_iff₀ hk).mpr hmul₁
  have hy₁ : 0 < ν₁ / k + 1 := by linarith
  have hmul₂ : (-1 : ℝ) * k < ν₂ := by simpa using hν₂
  have hν₂k : -1 < ν₂ / k := (lt_div_iff₀ hk).mpr hmul₂
  have hy₂ : 0 < ν₂ / k + 1 := by linarith
  have hmid : -k < α * ν₁ + (1 - α) * ν₂ := by
    by_cases hα0 : α = 0
    · simp [hα0, hν₂]
    · by_cases hα1 : α = 1
      · simp [hα1, hν₁]
      · have hpα : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
        have hltα : α < 1 := lt_of_le_of_ne hα₁ hα1
        have hpβ : 0 < 1 - α := by linarith
        have h1 : α * (-k) < α * ν₁ := mul_lt_mul_of_pos_left hν₁ hpα
        have h2 : (1 - α) * (-k) < (1 - α) * ν₂ :=
          mul_lt_mul_of_pos_left hν₂ hpβ
        have h := add_lt_add h1 h2
        have hleft : α * (-k) + (1 - α) * (-k) = -k := by ring
        rwa [hleft] at h
  have hymid_eq : (α * ν₁ + (1 - α) * ν₂) / k + 1 =
      α * (ν₁ / k + 1) + (1 - α) * (ν₂ / k + 1) := by
    field_simp [hk.ne']
    ring
  rw [kBessel_term_eq hk hmid r, kBessel_term_eq hk hν₁ r, kBessel_term_eq hk hν₂ r]
  rw [hymid_eq]
  let N : ℝ := x ^ (2 * r)
  let B : ℝ := (4 * k) ^ r * (r.factorial : ℝ)
  let P : ℝ := risingProd (ν₁ / k + 1) r
  let Q : ℝ := risingProd (ν₂ / k + 1) r
  have hN : 0 < N := by
    dsimp [N]
    exact pow_pos hx _
  have hB : 0 < B := by
    dsimp [B]
    exact mul_pos (pow_pos (mul_pos (by norm_num) hk) r)
      (by exact_mod_cast Nat.factorial_pos r)
  have hP : 0 < P := by
    dsimp [P]
    exact risingProd_pos hy₁ r
  have hQ : 0 < Q := by
    dsimp [Q]
    exact risingProd_pos hy₂ r
  have hsum : α + (1 - α) = 1 := by ring
  rw [weighted_geomean_div hN hB hP hQ hsum]
  have hG : 0 < P ^ α * Q ^ (1 - α) :=
    mul_pos (Real.rpow_pos_of_pos hP α) (Real.rpow_pos_of_pos hQ (1 - α))
  have hGle : P ^ α * Q ^ (1 - α) ≤
      risingProd (α * (ν₁ / k + 1) + (1 - α) * (ν₂ / k + 1)) r := by
    dsimp [P, Q]
    exact weighted_risingProd_le_risingProd hy₁ hy₂ hα hβ r
  have hDG : 0 < B * (P ^ α * Q ^ (1 - α)) := mul_pos hB hG
  have hD : B * (P ^ α * Q ^ (1 - α)) ≤
      B * risingProd (α * (ν₁ / k + 1) + (1 - α) * (ν₂ / k + 1)) r :=
    mul_le_mul_of_nonneg_left hGle hB.le
  exact div_le_div_of_nonneg_left hN.le hDG hD

/- accepted add_to_file helper 10 -/
lemma tsum_logConvex_of_pointwise {t : ℝ → ℕ → ℝ} {ν₁ ν₂ α : ℝ}
    (hα : 0 < α) (hα₁ : α < 1)
    (hmid : Summable (t (α * ν₁ + (1 - α) * ν₂)))
    (h₁ : Summable (t ν₁)) (h₂ : Summable (t ν₂))
    (hmid_nonneg : ∀ r, 0 ≤ t (α * ν₁ + (1 - α) * ν₂) r)
    (h₁_nonneg : ∀ r, 0 ≤ t ν₁ r) (h₂_nonneg : ∀ r, 0 ≤ t ν₂ r)
    (hpoint : ∀ r, t (α * ν₁ + (1 - α) * ν₂) r ≤
      t ν₁ r ^ α * t ν₂ r ^ (1 - α)) :
    (∑' r : ℕ, t (α * ν₁ + (1 - α) * ν₂) r) ≤
      (∑' r : ℕ, t ν₁ r) ^ α * (∑' r : ℕ, t ν₂ r) ^ (1 - α) := by
  let β : ℝ := 1 - α
  let p : ℝ := 1 / α
  let q : ℝ := 1 / β
  let A : ℝ := (∑' r : ℕ, t ν₁ r) ^ α
  let B : ℝ := (∑' r : ℕ, t ν₂ r) ^ β
  have hβ : 0 < β := by dsimp [β]; linarith
  have hpq : p.HolderConjugate q := by
    dsimp [p, q, β]
    exact Real.holderConjugate_one_div hα (by linarith) (by ring)
  have hT1_nonneg : 0 ≤ ∑' r : ℕ, t ν₁ r := tsum_nonneg h₁_nonneg
  have hT2_nonneg : 0 ≤ ∑' r : ℕ, t ν₂ r := tsum_nonneg h₂_nonneg
  have hαne : α ≠ 0 := hα.ne'
  have hβne : β ≠ 0 := hβ.ne'
  have hpeq : p = α⁻¹ := by dsimp [p]; rw [one_div]
  have hqeq : q = β⁻¹ := by dsimp [q]; rw [one_div]
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Real.rpow_nonneg hT1_nonneg α
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Real.rpow_nonneg hT2_nonneg β
  have hAp : A ^ p = ∑' r : ℕ, t ν₁ r := by
    dsimp [A]
    rw [hpeq, Real.rpow_rpow_inv hT1_nonneg hαne]
  have hBq : B ^ q = ∑' r : ℕ, t ν₂ r := by
    dsimp [B]
    rw [hqeq, Real.rpow_rpow_inv hT2_nonneg hβne]
  have hf_sum : HasSum (fun r : ℕ => (t ν₁ r ^ α) ^ p) (A ^ p) := by
    rw [hAp]
    exact h₁.hasSum.congr_fun fun r => by
      rw [hpeq, Real.rpow_rpow_inv (h₁_nonneg r) hαne]
  have hg_sum : HasSum (fun r : ℕ => (t ν₂ r ^ β) ^ q) (B ^ q) := by
    rw [hBq]
    exact h₂.hasSum.congr_fun fun r => by
      rw [hqeq, Real.rpow_rpow_inv (h₂_nonneg r) hβne]
  obtain ⟨C, hC_nonneg, hC_le, hC_sum⟩ :=
    Real.inner_le_Lp_mul_Lq_hasSum_of_nonneg hpq hA hB
      (fun r => Real.rpow_nonneg (h₁_nonneg r) α)
      (fun r => Real.rpow_nonneg (h₂_nonneg r) β)
      hf_sum hg_sum
  have hC_eq : C = ∑' r : ℕ, t ν₁ r ^ α * t ν₂ r ^ β := hC_sum.tsum_eq.symm
  have hmid_le_C : (∑' r : ℕ, t (α * ν₁ + (1 - α) * ν₂) r) ≤ C := by
    rw [hC_eq]
    exact Summable.tsum_le_tsum hpoint hmid hC_sum.summable
  exact le_trans hmid_le_C hC_le

/- accepted add_to_file helper 11 -/
lemma kBessel_convexCombo_gt {k ν₁ ν₂ α : ℝ} (hk : 0 < k)
    (hν₁ : -k < ν₁) (hν₂ : -k < ν₂) (hα : 0 ≤ α) (hα₁ : α ≤ 1) :
    -k < α * ν₁ + (1 - α) * ν₂ := by
  by_cases hα0 : α = 0
  · simp [hα0, hν₂]
  · by_cases hα1 : α = 1
    · simp [hα1, hν₁]
    · have hpα : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
      have hltα : α < 1 := lt_of_le_of_ne hα₁ hα1
      have hpβ : 0 < 1 - α := by linarith
      have h1 : α * (-k) < α * ν₁ := mul_lt_mul_of_pos_left hν₁ hpα
      have h2 : (1 - α) * (-k) < (1 - α) * ν₂ :=
        mul_lt_mul_of_pos_left hν₂ hpβ
      have h := add_lt_add h1 h2
      have hleft : α * (-k) + (1 - α) * (-k) = -k := by ring
      rwa [hleft] at h

/- verified submission -/
theorem normalized_modified_kBessel_nonincreasing_logConvex
    (k x : ℝ) (hk : 0 < k) (hx : 0 < x) :
    let Γk : ℝ → ℝ := fun z => k ^ (z / k - 1) * Real.Gamma (z / k)
    let 𝓘 : ℝ → ℝ := fun ν => ∑' r : ℕ,
      Γk (ν + k) /
        (Γk ((r : ℝ) * k + ν + k) * (4 : ℝ) ^ r * (r.factorial : ℝ)) * x ^ (2 * r)
    (∀ ⦃ν μ : ℝ⦄, -k < ν → ν ≤ μ → 𝓘 μ ≤ 𝓘 ν) ∧
      (∀ ⦃ν₁ ν₂ α : ℝ⦄, -k < ν₁ → -k < ν₂ → 0 ≤ α → α ≤ 1 →
        𝓘 (α * ν₁ + (1 - α) * ν₂) ≤ 𝓘 ν₁ ^ α * 𝓘 ν₂ ^ (1 - α)) := by
  dsimp only
  constructor
  · intro ν μ hν hνμ
    have hμ : -k < μ := lt_of_lt_of_le hν hνμ
    exact Summable.tsum_le_tsum
      (fun r => kBessel_term_antitone hk hx.le hν hνμ r)
      (summable_kBessel_term hk hx.le hμ)
      (summable_kBessel_term hk hx.le hν)
  · intro ν₁ ν₂ α hν₁ hν₂ hα hα₁
    let t : ℝ → ℕ → ℝ := fun ν r =>
      (k ^ ((ν + k) / k - 1) * Real.Gamma ((ν + k) / k)) /
        ((k ^ (((r : ℝ) * k + ν + k) / k - 1) *
          Real.Gamma (((r : ℝ) * k + ν + k) / k)) *
          (4 : ℝ) ^ r * (r.factorial : ℝ)) * x ^ (2 * r)
    change (∑' r : ℕ, t (α * ν₁ + (1 - α) * ν₂) r) ≤
      (∑' r : ℕ, t ν₁ r) ^ α * (∑' r : ℕ, t ν₂ r) ^ (1 - α)
    by_cases hα0 : α = 0
    · subst α
      simp [t]
    · by_cases hα1 : α = 1
      · subst α
        simp [t]
      · have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
        have hαlt : α < 1 := lt_of_le_of_ne hα₁ hα1
        have hmid : -k < α * ν₁ + (1 - α) * ν₂ :=
          kBessel_convexCombo_gt hk hν₁ hν₂ hα hα₁
        exact tsum_logConvex_of_pointwise (t := t) hαpos hαlt
          (summable_kBessel_term hk hx.le hmid)
          (summable_kBessel_term hk hx.le hν₁)
          (summable_kBessel_term hk hx.le hν₂)
          (fun r => kBessel_term_nonneg hk hx.le hmid r)
          (fun r => kBessel_term_nonneg hk hx.le hν₁ r)
          (fun r => kBessel_term_nonneg hk hx.le hν₂ r)
          (fun r => kBessel_term_logConvex hk hx hν₁ hν₂ hα hα₁ r)

end Rollout_p0496_normalized_modified_kbessel_nonincreasing_

#check_dependency_graph "Rollout_p0496_normalized_modified_kbessel_nonincreasing_.normalized_modified_kBessel_nonincreasing_logConvex" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let Γk := fun z => k ^ (z / k - 1) * Real.Gamma (z / k); let 𝓘 := fun ν => ∑' (r : ℕ), Γk (ν + k) / (Γk (↑r * k + ν + k) * 4 ^ r * ↑r.factorial) * x ^ (2 * r); (∀ ⦃ν μ : ℝ⦄, -k < ν → ν ≤ μ → 𝓘 μ ≤ 𝓘 ν) ∧ ∀ ⦃ν₁ ν₂ α : ℝ⦄, -k < ν₁ → -k < ν₂ → 0 ≤ α → α ≤ 1 → 𝓘 (α * ν₁ + (1 - α) * ν₂) ≤ 𝓘 ν₁ ^ α * 𝓘 ν₂ ^ (1 - α)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hk\",\"statement\":\"0 < k\"},{\"name\":\"hx\",\"statement\":\"0 < x\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0496_normalized_modified_kbessel_nonincreasing_\",\"reconstructedProofSha256\":\"ccc831bc4988a1c40d3bb5e7044e7e9be90f69420dde823eb0b0c1c3569732ef\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p0496_normalized_modified_kbessel_nonincreasing_.normalized_modified_kBessel_nonincreasing_logConvex\",\"topologySha256\":\"76e85da9bebe4ed58125c383835dd52ecbe6599bc93f9169392c1b938160e0ad\"}"

namespace Rollout_p0613_chromaticnumber_cartesianpower

-- graph_id: p0613_chromaticnumber_cartesianpower
-- topology_sha256: ae22701a4b328287dc620e363fc049b384035cf483673f85fda6131a05a68d18
/- verified submission -/
lemma cartesianPower_colorable_of_coloring {n k q : ℕ}
    (G : SimpleGraph (Fin n)) (C : G.Coloring (Fin q)) (hq : q ≠ 0) :
    (SimpleGraph.fromRel (fun x y : Fin k → Fin n =>
      ∃ i : Fin k, G.Adj (x i) (y i) ∧
        ∀ j : Fin k, j ≠ i → x j = y j)).Colorable q := by
  letI : NeZero q := ⟨hq⟩
  let H : SimpleGraph (Fin k → Fin n) :=
    SimpleGraph.fromRel (fun x y : Fin k → Fin n =>
      ∃ i : Fin k, G.Adj (x i) (y i) ∧
        ∀ j : Fin k, j ≠ i → x j = y j)
  let color : H.Coloring (Fin q) :=
    { toFun := fun x => ∑ j : Fin k, C (x j)
      map_rel' := by
        intro x y hxy
        rw [SimpleGraph.fromRel_adj] at hxy
        have hrel : ∃ i : Fin k, G.Adj (x i) (y i) ∧
            ∀ j : Fin k, j ≠ i → x j = y j := by
          rcases hxy with ⟨_, hxy | hxy⟩
          · exact hxy
          · rcases hxy with ⟨i, hi, hrest⟩
            exact ⟨i, hi.symm, fun j hj => (hrest j hj).symm⟩
        rcases hrel with ⟨i, hi, hrest⟩
        show (∑ j : Fin k, C (x j)) ≠ ∑ j : Fin k, C (y j)
        intro hsum
        have htail : (∑ j ∈ (Finset.univ : Finset (Fin k)).erase i, C (x j)) =
            ∑ j ∈ (Finset.univ : Finset (Fin k)).erase i, C (y j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hrest j (Finset.mem_erase.mp hj).1]
        rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin k))
              (fun j => C (x j)) (Finset.mem_univ i),
            ← Finset.sum_erase_add (Finset.univ : Finset (Fin k))
              (fun j => C (y j)) (Finset.mem_univ i),
            htail] at hsum
        exact C.valid hi (add_left_cancel hsum) }
  exact ⟨color⟩

lemma cartesianPower_chromaticNumber_lower {n k : ℕ} (hn : 0 < n) (hk : 1 ≤ k)
    (G : SimpleGraph (Fin n)) :
    G.chromaticNumber ≤
      (SimpleGraph.fromRel (fun x y : Fin k → Fin n =>
        ∃ i : Fin k, G.Adj (x i) (y i) ∧
          ∀ j : Fin k, j ≠ i → x j = y j)).chromaticNumber := by
  let p : Fin k := ⟨0, hk⟩
  let a : Fin n := ⟨0, hn⟩
  let H : SimpleGraph (Fin k → Fin n) :=
    SimpleGraph.fromRel (fun x y : Fin k → Fin n =>
      ∃ i : Fin k, G.Adj (x i) (y i) ∧
        ∀ j : Fin k, j ≠ i → x j = y j)
  let emb (v : Fin n) : Fin k → Fin n := fun j => if j = p then v else a
  let embed : G →g H :=
    { toFun := emb
      map_rel' := by
        intro v w hvw
        rw [SimpleGraph.fromRel_adj]
        constructor
        · intro h
          have hp := congrFun h p
          simp [emb] at hp
          exact hvw.ne hp
        · left
          refine ⟨p, ?_, ?_⟩
          · simpa [emb] using hvw
          · intro j hj
            simp [emb, hj] }
  exact SimpleGraph.chromaticNumber_mono_of_hom embed

theorem chromaticNumber_cartesianPower {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) :
    ∀ k : ℕ, 1 ≤ k →
      (SimpleGraph.fromRel (fun x y : Fin k → Fin n =>
        ∃ i : Fin k, G.Adj (x i) (y i) ∧
          ∀ j : Fin k, j ≠ i → x j = y j)).chromaticNumber =
        G.chromaticNumber := by
  intro k hk
  let q : ℕ := G.chromaticNumber.toNat
  have hcG : G.Colorable q := by
    simpa [q] using SimpleGraph.colorable_chromaticNumber_of_fintype G
  have hq : q ≠ 0 := by
    intro hq
    rw [hq] at hcG
    have hempty : IsEmpty (Fin n) := SimpleGraph.isEmpty_of_colorable_zero hcG
    exact IsEmpty.elim hempty ⟨0, hn⟩
  have hcolor : (SimpleGraph.fromRel (fun x y : Fin k → Fin n =>
      ∃ i : Fin k, G.Adj (x i) (y i) ∧
        ∀ j : Fin k, j ≠ i → x j = y j)).Colorable q := by
    rcases hcG with ⟨C⟩
    exact cartesianPower_colorable_of_coloring G C hq
  have htop : G.chromaticNumber ≠ ⊤ := by
    exact SimpleGraph.chromaticNumber_ne_top_iff_exists.mpr ⟨q, hcG⟩
  have upper : (SimpleGraph.fromRel (fun x y : Fin k → Fin n =>
      ∃ i : Fin k, G.Adj (x i) (y i) ∧
        ∀ j : Fin k, j ≠ i → x j = y j)).chromaticNumber ≤ G.chromaticNumber := by
    have hle := hcolor.chromaticNumber_le
    have hqeq : (q : ℕ∞) = G.chromaticNumber := by
      dsimp [q]
      exact ENat.coe_toNat htop
    rw [hqeq] at hle
    exact hle
  exact le_antisymm upper (cartesianPower_chromaticNumber_lower hn hk G)

end Rollout_p0613_chromaticnumber_cartesianpower

#check_dependency_graph "Rollout_p0613_chromaticnumber_cartesianpower.chromaticNumber_cartesianPower" against "{\"edges\":[{\"conclusion\":{\"name\":\"hcG\",\"statement\":\"G.Colorable q\"},\"graphEdgeId\":\"h_001_hcg\",\"premises\":[],\"rawEdgeId\":\"telescope_6\"},{\"conclusion\":{\"name\":\"hq\",\"statement\":\"q ≠ 0\"},\"graphEdgeId\":\"h_002_hq\",\"premises\":[{\"name\":\"hn\",\"statement\":\"0 < n\"},{\"name\":\"hcG\",\"statement\":\"G.Colorable q\"}],\"rawEdgeId\":\"telescope_7\"},{\"conclusion\":{\"name\":\"htop\",\"statement\":\"G.chromaticNumber ≠ ⊤\"},\"graphEdgeId\":\"h_004_htop\",\"premises\":[{\"name\":\"hcG\",\"statement\":\"G.Colorable q\"}],\"rawEdgeId\":\"telescope_9\"},{\"conclusion\":{\"name\":\"hcolor\",\"statement\":\"(SimpleGraph.fromRel fun x y => ∃ i, G.Adj (x i) (y i) ∧ ∀ (j : Fin k), j ≠ i → x j = y j).Colorable q\"},\"graphEdgeId\":\"h_003_hcolor\",\"premises\":[{\"name\":\"hcG\",\"statement\":\"G.Colorable q\"},{\"name\":\"hq\",\"statement\":\"q ≠ 0\"}],\"rawEdgeId\":\"telescope_8\"},{\"conclusion\":{\"name\":\"upper\",\"statement\":\"(SimpleGraph.fromRel fun x y => ∃ i, G.Adj (x i) (y i) ∧ ∀ (j : Fin k), j ≠ i → x j = y j).chromaticNumber ≤ G.chromaticNumber\"},\"graphEdgeId\":\"h_005_upper\",\"premises\":[{\"name\":\"hcolor\",\"statement\":\"(SimpleGraph.fromRel fun x y => ∃ i, G.Adj (x i) (y i) ∧ ∀ (j : Fin k), j ≠ i → x j = y j).Colorable q\"},{\"name\":\"htop\",\"statement\":\"G.chromaticNumber ≠ ⊤\"}],\"rawEdgeId\":\"telescope_10\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(SimpleGraph.fromRel fun x y => ∃ i, G.Adj (x i) (y i) ∧ ∀ (j : Fin k), j ≠ i → x j = y j).chromaticNumber = G.chromaticNumber\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hn\",\"statement\":\"0 < n\"},{\"name\":\"hk\",\"statement\":\"1 ≤ k\"},{\"name\":\"upper\",\"statement\":\"(SimpleGraph.fromRel fun x y => ∃ i, G.Adj (x i) (y i) ∧ ∀ (j : Fin k), j ≠ i → x j = y j).chromaticNumber ≤ G.chromaticNumber\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0613_chromaticnumber_cartesianpower\",\"reconstructedProofSha256\":\"bcb8d2e0bdd036b6d187d8e253efa05446de627f6eee43e128b9f5d64acce725\",\"selectedEdgeCount\":6,\"theoremName\":\"Rollout_p0613_chromaticnumber_cartesianpower.chromaticNumber_cartesianPower\",\"topologySha256\":\"ae22701a4b328287dc620e363fc049b384035cf483673f85fda6131a05a68d18\"}"
