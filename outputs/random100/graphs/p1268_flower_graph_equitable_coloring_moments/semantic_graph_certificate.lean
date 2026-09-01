import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1268_flower_graph_equitable_coloring_moments
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 62fc5d51e2f8984904db07fbb0ba470440156ede0fd07187201aad0c3ef5f3f5
-- reconstructed_proof_sha256: 6cbdaa3ce12753bec5a1e8f5b3c39103eac821254f2029d25666a14413033484
-- selected_edge_count: 5

/- accepted add_to_file helper 1 -/

abbrev FlowerVertex (n : ℕ) := Unit ⊕ (Fin n ⊕ Fin n)

def flowerRel (n : ℕ) : FlowerVertex n → FlowerVertex n → Prop := fun a b =>
  (∃ i : Fin n, a = Sum.inl () ∧ b = Sum.inr (Sum.inl i)) ∨
  (∃ i : Fin n,
    a = Sum.inr (Sum.inl i) ∧
      b = Sum.inr (Sum.inl ((finRotate n) i))) ∨
  (∃ i : Fin n, a = Sum.inr (Sum.inl i) ∧ b = Sum.inr (Sum.inr i)) ∨
  (∃ i : Fin n, a = Sum.inl () ∧ b = Sum.inr (Sum.inr i))

def flowerGraph (n : ℕ) : SimpleGraph (FlowerVertex n) :=
  SimpleGraph.fromRel (flowerRel n)

def flowerPairColor (n : ℕ) : FlowerVertex n → Fin (n + 1)
  | Sum.inl _ => Fin.last n
  | Sum.inr (Sum.inl i) => i.castSucc
  | Sum.inr (Sum.inr i) => ((finRotate n) i).castSucc

lemma finRotate_ne_self_of_two_le {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    (finRotate n) i ≠ i := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
      intro h
      have hv := congrArg Fin.val h
      rw [coe_finRotate] at hv
      by_cases hi : i = Fin.last m
      · simp [hi] at hv
        omega
      · simp [hi] at hv

lemma flowerPairColor_rel_ne {n : ℕ} (hn : 2 ≤ n) {a b : FlowerVertex n}
    (h : flowerRel n a b) : flowerPairColor n a ≠ flowerPairColor n b := by
  rcases h with ⟨i, ha, hb⟩ | ⟨i, ha, hb⟩ | ⟨i, ha, hb⟩ | ⟨i, ha, hb⟩
  · subst a
    subst b
    exact (Fin.castSucc_ne_last i).symm
  · subst a
    subst b
    exact fun heq => finRotate_ne_self_of_two_le hn i
      (Fin.castSucc_injective n heq).symm
  · subst a
    subst b
    exact fun heq => finRotate_ne_self_of_two_le hn i
      (Fin.castSucc_injective n heq).symm
  · subst a
    subst b
    exact (Fin.castSucc_ne_last ((finRotate n) i)).symm

def flowerPairColoring {n : ℕ} (hn : 2 ≤ n) :
    (flowerGraph n).Coloring (Fin (n + 1)) where
  toFun := flowerPairColor n
  map_rel' := by
    intro a b hab
    rw [flowerGraph, SimpleGraph.fromRel_adj] at hab
    rcases hab with ⟨_, h | h⟩
    · exact flowerPairColor_rel_ne hn h
    · exact (flowerPairColor_rel_ne hn h).symm

lemma flowerPairColoring_surjective {n : ℕ} (hn : 2 ≤ n) :
    Function.Surjective (flowerPairColoring hn) := by
  intro j
  by_cases hj : j = Fin.last n
  · refine ⟨Sum.inl (), ?_⟩
    simp [flowerPairColoring, flowerPairColor, hj]
  · obtain ⟨i, hi⟩ := Fin.eq_castSucc_of_ne_last hj
    refine ⟨Sum.inr (Sum.inl i), ?_⟩
    simp [flowerPairColoring, flowerPairColor, hi]

lemma flowerPairColor_colorClass_last (n : ℕ) :
    Set.ncard {x : FlowerVertex n | flowerPairColor n x = Fin.last n} = 1 := by
  have hset : {x : FlowerVertex n | flowerPairColor n x = Fin.last n} = {Sum.inl ()} := by
    ext x
    cases x with
    | inl u =>
        cases u
        simp [flowerPairColor]
    | inr x =>
        cases x with
        | inl i => simp [flowerPairColor, (Fin.castSucc_ne_last i).symm]
        | inr i => simp [flowerPairColor, (Fin.castSucc_ne_last ((finRotate n) i)).symm]
  rw [hset, Set.ncard_singleton]

lemma flowerPairColor_colorClass_castSucc (n : ℕ) (i : Fin n) :
    Set.ncard {x : FlowerVertex n | flowerPairColor n x = i.castSucc} = 2 := by
  let y : Fin n := (finRotate n).symm i
  have hset : {x : FlowerVertex n | flowerPairColor n x = i.castSucc} =
      {Sum.inr (Sum.inl i), Sum.inr (Sum.inr y)} := by
    ext x
    cases x with
    | inl u =>
        cases u
        simp [flowerPairColor, (Fin.castSucc_ne_last i).symm]
    | inr x =>
        cases x with
        | inl j =>
            simp [flowerPairColor, Fin.castSucc_injective n |>.eq_iff]
        | inr j =>
            simp [flowerPairColor, Fin.castSucc_injective n |>.eq_iff,
              Equiv.apply_eq_iff_eq_symm_apply, y]
  rw [hset]
  exact Set.ncard_pair (by simp)

lemma flowerPairColoring_equitable {n : ℕ} (hn : 2 ≤ n) :
    ∀ i j : Fin (n + 1),
      Nat.dist ((flowerPairColoring hn).colorClass i).ncard
        ((flowerPairColoring hn).colorClass j).ncard ≤ 1 := by
  intro i j
  have hi : ((flowerPairColoring hn).colorClass i).ncard = 1 ∨
      ((flowerPairColoring hn).colorClass i).ncard = 2 := by
    by_cases h : i = Fin.last n
    · left
      simp [SimpleGraph.Coloring.colorClass, flowerPairColoring, h,
        flowerPairColor_colorClass_last]
    · obtain ⟨a, ha⟩ := Fin.eq_castSucc_of_ne_last h
      right
      simp [SimpleGraph.Coloring.colorClass, flowerPairColoring, ← ha,
        flowerPairColor_colorClass_castSucc]
  have hj : ((flowerPairColoring hn).colorClass j).ncard = 1 ∨
      ((flowerPairColoring hn).colorClass j).ncard = 2 := by
    by_cases h : j = Fin.last n
    · left
      simp [SimpleGraph.Coloring.colorClass, flowerPairColoring, h,
        flowerPairColor_colorClass_last]
    · obtain ⟨a, ha⟩ := Fin.eq_castSucc_of_ne_last h
      right
      simp [SimpleGraph.Coloring.colorClass, flowerPairColoring, ← ha,
        flowerPairColor_colorClass_castSucc]
  rcases hi with hi | hi <;> rcases hj with hj | hj <;> rw [hi, hj] <;> decide

/- accepted add_to_file helper 2 -/
lemma flowerGraph_adj_center_rim (n : ℕ) (i : Fin n) :
    (flowerGraph n).Adj (Sum.inl () : FlowerVertex n) (Sum.inr (Sum.inl i)) := by
  rw [flowerGraph, SimpleGraph.fromRel_adj]
  constructor
  · simp
  · left
    left
    exact ⟨i, rfl, rfl⟩

lemma flowerGraph_adj_center_outer (n : ℕ) (i : Fin n) :
    (flowerGraph n).Adj (Sum.inl () : FlowerVertex n) (Sum.inr (Sum.inr i)) := by
  rw [flowerGraph, SimpleGraph.fromRel_adj]
  constructor
  · simp
  · left
    right
    right
    right
    exact ⟨i, rfl, rfl⟩

lemma flowerGraph_center_colorClass_singleton {n : ℕ} {β : Type}
    (f : (flowerGraph n).Coloring β) :
    f.colorClass (f (Sum.inl () : FlowerVertex n)) = {Sum.inl ()} := by
  ext x
  constructor
  · intro hx
    cases x with
    | inl u =>
        cases u
        rfl
    | inr x =>
        cases x with
        | inl i =>
            exfalso
            exact f.valid (flowerGraph_adj_center_rim n i) hx.symm
        | inr i =>
            exfalso
            exact f.valid (flowerGraph_adj_center_outer n i) hx.symm
  · intro hx
    simp at hx
    simp [SimpleGraph.Coloring.colorClass, hx]

lemma FlowerVertex_card (n : ℕ) :
    Fintype.card (FlowerVertex n) = 2 * n + 1 := by
  simp [FlowerVertex]
  omega

lemma Set.ncard_eq_filter_card {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (f : α → β) (b : β) :
    Set.ncard {a : α | f a = b} = (Finset.univ.filter fun a => f a = b).card := by
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext a
  simp

lemma sum_ncard_colorClass {V β : Type} [Fintype V] [DecidableEq V]
    [Fintype β] [DecidableEq β] {G : SimpleGraph V} (f : G.Coloring β) :
    ∑ i : β, (f.colorClass i).ncard = Fintype.card V := by
  have hpoint : ∀ i : β, (f.colorClass i).ncard =
      (Finset.univ.filter fun x : V => f x = i).card := by
    intro i
    exact Set.ncard_eq_filter_card f i
  calc
    ∑ i : β, (f.colorClass i).ncard
        = ∑ i : β, (Finset.univ.filter fun x : V => f x = i).card := by
            exact Finset.sum_congr rfl fun i _ => hpoint i
    _ = ∑ i : β, ∑ x ∈ Finset.univ.filter (fun x : V => f x = i), 1 := by
            simp
    _ = ∑ x : V, 1 := Finset.sum_fiberwise Finset.univ f (fun _ : V => (1 : ℕ))
    _ = Fintype.card V := (Fintype.card_eq_sum_ones (α := V)).symm

lemma flowerGraph_color_lower {n ℓ : ℕ} (f : (flowerGraph n).Coloring (Fin ℓ))
    (hsurj : Function.Surjective f)
    (heq : ∀ i j : Fin ℓ,
      Nat.dist (f.colorClass i).ncard (f.colorClass j).ncard ≤ 1) :
    n + 1 ≤ ℓ := by
  classical
  let s : Fin ℓ → ℕ := fun i => (f.colorClass i).ncard
  have hcenter_set := flowerGraph_center_colorClass_singleton f
  have hcenter : s (f (Sum.inl () : FlowerVertex n)) = 1 := by
    simp [s, hcenter_set]
  have hpos : ∀ i : Fin ℓ, 0 < s i := by
    intro i
    obtain ⟨x, hx⟩ := hsurj i
    apply (Set.ncard_pos).mpr
    exact ⟨x, by simpa [SimpleGraph.Coloring.colorClass, s] using hx⟩
  have hsle : ∀ i : Fin ℓ, s i ≤ 2 := by
    intro i
    have hd := heq (f (Sum.inl () : FlowerVertex n)) i
    change Nat.dist (s (f (Sum.inl () : FlowerVertex n))) (s i) ≤ 1 at hd
    rw [hcenter, Nat.dist] at hd
    have hp := hpos i
    omega
  have hsum := sum_ncard_colorClass f
  have hbound : ∑ i : Fin ℓ, s i ≤ ∑ i : Fin ℓ, 2 := by
    exact Finset.sum_le_sum fun i _ => hsle i
  rw [FlowerVertex_card] at hsum
  change ∑ i : Fin ℓ, s i = 2 * n + 1 at hsum
  have hbound' : ∑ i : Fin ℓ, s i ≤ ℓ * 2 := by
    simpa using hbound
  omega

/- accepted add_to_file helper 3 -/
lemma flowerGraph_min_color_class_sizes {n : ℕ}
    (f : (flowerGraph n).Coloring (Fin (n + 1)))
    (hsurj : Function.Surjective f)
    (heq : ∀ i j : Fin (n + 1),
      Nat.dist (f.colorClass i).ncard (f.colorClass j).ncard ≤ 1)
    (hsort : ∀ i j : Fin (n + 1), i ≤ j →
      (f.colorClass j).ncard ≤ (f.colorClass i).ncard) :
    (∀ i : Fin n, (f.colorClass i.castSucc).ncard = 2) ∧
      (f.colorClass (Fin.last n)).ncard = 1 := by
  classical
  let s : Fin (n + 1) → ℕ := fun i => (f.colorClass i).ncard
  have hcenter_set := flowerGraph_center_colorClass_singleton f
  have hcenter : s (f (Sum.inl () : FlowerVertex n)) = 1 := by
    simp [s, hcenter_set]
  have hpos : ∀ i : Fin (n + 1), 0 < s i := by
    intro i
    obtain ⟨x, hx⟩ := hsurj i
    apply (Set.ncard_pos).mpr
    exact ⟨x, by simpa [SimpleGraph.Coloring.colorClass, s] using hx⟩
  have hs12 : ∀ i : Fin (n + 1), s i = 1 ∨ s i = 2 := by
    intro i
    have hd := heq (f (Sum.inl () : FlowerVertex n)) i
    change Nat.dist (s (f (Sum.inl () : FlowerVertex n))) (s i) ≤ 1 at hd
    rw [hcenter, Nat.dist] at hd
    have hp := hpos i
    omega
  have hsum := sum_ncard_colorClass f
  rw [FlowerVertex_card] at hsum
  change ∑ i : Fin (n + 1), s i = 2 * n + 1 at hsum
  have hdecomp : ∑ i : Fin (n + 1), s i =
      (n + 1) + (Finset.univ.filter fun i => s i = 2).card := by
    calc
      ∑ i : Fin (n + 1), s i
          = ∑ i : Fin (n + 1), (1 + if s i = 2 then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro i _
              rcases hs12 i with hi | hi <;> simp [hi]
      _ = (∑ i : Fin (n + 1), (1 : ℕ)) +
            ∑ i : Fin (n + 1), (if s i = 2 then 1 else 0) := by
              rw [Finset.sum_add_distrib]
      _ = (n + 1) + (Finset.univ.filter fun i => s i = 2).card := by
              simp
  have hfilter : (Finset.univ.filter fun i => s i = 2).card = n := by
    omega
  have hnotcard : (Finset.univ.filter fun i => ¬ s i = 2).card = 1 := by
    have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (p := fun i : Fin (n + 1) => s i = 2)
    have huniv : (Finset.univ : Finset (Fin (n + 1))).card = n + 1 := by simp
    omega
  obtain ⟨i, hi_mem⟩ := Finset.card_pos.mp (by
    rw [hnotcard]
    norm_num : 0 < (Finset.univ.filter fun i => ¬ s i = 2).card)
  have hi_not2 : ¬ s i = 2 := by
    simpa using hi_mem
  have hi1 : s i = 1 := by
    rcases hs12 i with h | h
    · exact h
    · exact False.elim (hi_not2 h)
  have hlast : s (Fin.last n) = 1 := by
    have hle := hsort i (Fin.last n) (Fin.le_last i)
    change s (Fin.last n) ≤ s i at hle
    rw [hi1] at hle
    have hp := hpos (Fin.last n)
    omega
  have hunique : ∀ a b : Fin (n + 1), ¬ s a = 2 → ¬ s b = 2 → a = b := by
    have hle1 : (Finset.univ.filter fun i => ¬ s i = 2).card ≤ 1 := by omega
    have hu := Finset.card_le_one.mp hle1
    intro a b ha hb
    exact hu a (by simpa using ha) b (by simpa using hb)
  have hcast : ∀ a : Fin n, s a.castSucc = 2 := by
    intro a
    by_contra hnot
    have heqind := hunique a.castSucc (Fin.last n) hnot (by omega)
    exact Fin.castSucc_ne_last a heqind
  constructor
  · intro a
    exact hcast a
  · exact hlast

/- accepted add_to_file helper 4 -/
lemma sum_comp_colorClass {V β : Type} [Fintype V] [DecidableEq V]
    [Fintype β] [DecidableEq β] {G : SimpleGraph V}
    (f : G.Coloring β) (Y : β → ℝ) :
    ∑ x : V, Y (f x) = ∑ i : β, ((f.colorClass i).ncard : ℝ) * Y i := by
  have hfib := Finset.sum_fiberwise (s := Finset.univ) (g := f)
    (f := fun x : V => Y (f x))
  calc
    ∑ x : V, Y (f x) = ∑ i : β,
        ∑ x ∈ Finset.univ.filter (fun x : V => f x = i), Y (f x) := hfib.symm
    _ = ∑ i : β, ((Finset.univ.filter fun x : V => f x = i).card : ℝ) * Y i := by
          apply Finset.sum_congr rfl
          intro i _
          have hconst :
              (∑ x ∈ Finset.univ.filter (fun x : V => f x = i), Y (f x)) =
              ∑ x ∈ Finset.univ.filter (fun x : V => f x = i), Y i := by
            apply Finset.sum_congr rfl
            intro x hx
            simp at hx
            simp [hx]
          rw [hconst]
          simp [mul_comm]
    _ = ∑ i : β, ((f.colorClass i).ncard : ℝ) * Y i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← Set.ncard_eq_filter_card f i]
          rfl

lemma uniformPMF_integral_color_comp {V β : Type} [Fintype V] [Nonempty V]
    [DecidableEq V] [Fintype β] [DecidableEq β] {G : SimpleGraph V}
    (f : G.Coloring β) (Y : β → ℝ) :
    @MeasureTheory.integral V ℝ _ _ ⊤
      (@PMF.toMeasure V ⊤ (PMF.uniformOfFintype V)) (fun x => Y (f x)) =
    (∑ i : β, ((f.colorClass i).ncard : ℝ) * Y i) / (Fintype.card V : ℝ) := by
  letI : MeasurableSpace V := ⊤
  rw [PMF.integral_eq_sum]
  have hpoint : ∀ x : V, ((PMF.uniformOfFintype V) x).toReal • Y (f x) =
      ((Fintype.card V : ℝ)⁻¹) * Y (f x) := by
    intro x
    simp [PMF.uniformOfFintype_apply]
  calc
    ∑ a : V, ((PMF.uniformOfFintype V) a).toReal • Y (f a)
        = ∑ a : V, ((Fintype.card V : ℝ)⁻¹) * Y (f a) := by
            exact Finset.sum_congr rfl fun x _ => hpoint x
    _ = ((Fintype.card V : ℝ)⁻¹) * ∑ x : V, Y (f x) := by
            rw [Finset.mul_sum]
    _ = ((Fintype.card V : ℝ)⁻¹) *
          ∑ i : β, ((f.colorClass i).ncard : ℝ) * Y i := by
            rw [sum_comp_colorClass f Y]
    _ = (∑ i : β, ((f.colorClass i).ncard : ℝ) * Y i) / (Fintype.card V : ℝ) := by
            ring

/- accepted add_to_file helper 5 -/
lemma two_mul_sum_range_add_one (n : ℕ) :
    2 * (∑ i ∈ Finset.range n, ((i : ℝ) + 1)) = (n : ℝ) * ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      rw [mul_add, ih]
      push_cast
      ring

lemma six_mul_sum_range_add_one_sq (n : ℕ) :
    6 * (∑ i ∈ Finset.range n, (((i : ℝ) + 1) ^ 2)) =
      (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      rw [mul_add, ih]
      push_cast
      ring_nf

lemma flower_weighted_sum_first {n : ℕ}
    {f : (flowerGraph n).Coloring (Fin (n + 1))}
    (hcast : ∀ i : Fin n, (f.colorClass i.castSucc).ncard = 2)
    (hlast : (f.colorClass (Fin.last n)).ncard = 1) :
    ∑ i : Fin (n + 1), ((f.colorClass i).ncard : ℝ) * ((i.val : ℝ) + 1) =
      ((n : ℝ) + 1) ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  have hfirst :
      (∑ i : Fin n, ((f.colorClass i.castSucc).ncard : ℝ) *
        ((i.castSucc.val : ℝ) + 1)) =
      2 * ∑ i : Fin n, ((i.val : ℝ) + 1) := by
    calc
      ∑ i : Fin n, ((f.colorClass i.castSucc).ncard : ℝ) *
          ((i.castSucc.val : ℝ) + 1)
          = ∑ i : Fin n, 2 * ((i.val : ℝ) + 1) := by
              apply Finset.sum_congr rfl
              intro i _
              simp [hcast i]
      _ = 2 * ∑ i : Fin n, ((i.val : ℝ) + 1) := by
              rw [Finset.mul_sum]
  rw [hfirst]
  have hlastval :
      ((f.colorClass (Fin.last n)).ncard : ℝ) * (((Fin.last n).val : ℝ) + 1) =
      (n : ℝ) + 1 := by
    simp [hlast]
  rw [hlastval]
  rw [Fin.sum_univ_eq_sum_range (fun i => ((i : ℝ) + 1)) n]
  have h2 := two_mul_sum_range_add_one n
  nlinarith

lemma flower_weighted_sum_second {n : ℕ}
    {f : (flowerGraph n).Coloring (Fin (n + 1))}
    (hcast : ∀ i : Fin n, (f.colorClass i.castSucc).ncard = 2)
    (hlast : (f.colorClass (Fin.last n)).ncard = 1) :
    ∑ i : Fin (n + 1), ((f.colorClass i).ncard : ℝ) * (((i.val : ℝ) + 1) ^ 2) =
      ((n : ℝ) ^ 4 + 2 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 + (n : ℝ)) /
        (3 * (2 * (n : ℝ) + 1)) + ((n : ℝ) + 1) ^ 4 / (2 * (n : ℝ) + 1) := by
  rw [Fin.sum_univ_castSucc]
  have hfirst :
      (∑ i : Fin n, ((f.colorClass i.castSucc).ncard : ℝ) *
        (((i.castSucc.val : ℝ) + 1) ^ 2)) =
      2 * ∑ i : Fin n, (((i.val : ℝ) + 1) ^ 2) := by
    calc
      ∑ i : Fin n, ((f.colorClass i.castSucc).ncard : ℝ) *
          (((i.castSucc.val : ℝ) + 1) ^ 2)
          = ∑ i : Fin n, 2 * (((i.val : ℝ) + 1) ^ 2) := by
              apply Finset.sum_congr rfl
              intro i _
              simp [hcast i]
      _ = 2 * ∑ i : Fin n, (((i.val : ℝ) + 1) ^ 2) := by
              rw [Finset.mul_sum]
  rw [hfirst]
  have hlastval :
      ((f.colorClass (Fin.last n)).ncard : ℝ) * ((((Fin.last n).val : ℝ) + 1) ^ 2) =
      ((n : ℝ) + 1) ^ 2 := by
    simp [hlast]
  rw [hlastval]
  rw [Fin.sum_univ_eq_sum_range (fun i => (((i : ℝ) + 1) ^ 2)) n]
  have h6 := six_mul_sum_range_add_one_sq n
  have h2S : 2 * (∑ i ∈ Finset.range n, (((i : ℝ) + 1) ^ 2)) =
      (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / 3 := by
    nlinarith
  rw [h2S]
  have hden : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hden]
  ring

/- accepted add_to_file helper 6 -/
lemma flower_graph_moments_of_min {n : ℕ}
    (f : (flowerGraph n).Coloring (Fin (n + 1)))
    (hsurj : Function.Surjective f)
    (heq : ∀ i j : Fin (n + 1),
      Nat.dist (f.colorClass i).ncard (f.colorClass j).ncard ≤ 1)
    (hsort : ∀ i j : Fin (n + 1), i ≤ j →
      (f.colorClass j).ncard ≤ (f.colorClass i).ncard) :
    let X : FlowerVertex n → ℝ := fun x => (↑((f x).val + 1) : ℝ)
    let μ := @PMF.toMeasure (FlowerVertex n) ⊤ (PMF.uniformOfFintype (FlowerVertex n))
    @MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ X =
        ((n : ℝ) + 1) ^ 2 / (2 * (n : ℝ) + 1) ∧
      @ProbabilityTheory.variance (FlowerVertex n) ⊤ X μ =
        ((n : ℝ) ^ 4 + 2 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 + (n : ℝ)) /
          (3 * (2 * (n : ℝ) + 1) ^ 2) := by
  classical
  let X : FlowerVertex n → ℝ := fun x => (↑((f x).val + 1) : ℝ)
  let μ := @PMF.toMeasure (FlowerVertex n) ⊤ (PMF.uniformOfFintype (FlowerVertex n))
  obtain ⟨hcast, hlast⟩ := flowerGraph_min_color_class_sizes f hsurj heq hsort
  have hweighted1 := flower_weighted_sum_first (f := f) hcast hlast
  have hweighted2 := flower_weighted_sum_second (f := f) hcast hlast
  have hN : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have hmean : @MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ X =
      ((n : ℝ) + 1) ^ 2 / (2 * (n : ℝ) + 1) := by
    have h := uniformPMF_integral_color_comp (V := FlowerVertex n)
      (β := Fin (n + 1)) (G := flowerGraph n) f
      (fun i => ((i.val : ℝ) + 1))
    calc
      @MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ X
          = (∑ i : Fin (n + 1), ((f.colorClass i).ncard : ℝ) *
              ((i.val : ℝ) + 1)) / (Fintype.card (FlowerVertex n) : ℝ) := by
                simpa [X, μ] using h
      _ = ((n : ℝ) + 1) ^ 2 / (2 * (n : ℝ) + 1) := by
              rw [hweighted1, FlowerVertex_card]
              norm_num
  have hsecond : @MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ (fun x => X x ^ 2) =
      ((n : ℝ) ^ 4 + 2 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 + (n : ℝ)) /
          (3 * (2 * (n : ℝ) + 1) ^ 2) +
        ((n : ℝ) + 1) ^ 4 / ((2 * (n : ℝ) + 1) ^ 2) := by
    have h := uniformPMF_integral_color_comp (V := FlowerVertex n)
      (β := Fin (n + 1)) (G := flowerGraph n) f
      (fun i => (((i.val : ℝ) + 1) ^ 2))
    calc
      @MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ (fun x => X x ^ 2)
          = (∑ i : Fin (n + 1), ((f.colorClass i).ncard : ℝ) *
              (((i.val : ℝ) + 1) ^ 2)) / (Fintype.card (FlowerVertex n) : ℝ) := by
                simpa [X, μ] using h
      _ = ((n : ℝ) ^ 4 + 2 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 + (n : ℝ)) /
            (3 * (2 * (n : ℝ) + 1) ^ 2) +
          ((n : ℝ) + 1) ^ 4 / ((2 * (n : ℝ) + 1) ^ 2) := by
            rw [hweighted2, FlowerVertex_card]
            field_simp [hN]
            ring_nf
            norm_num
  have hmem : MeasureTheory.MemLp X 2 μ := by
    exact MeasureTheory.MemLp.of_discrete
  have hvar : @ProbabilityTheory.variance (FlowerVertex n) ⊤ X μ =
      @MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ (fun x => X x ^ 2) -
        (@MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ X) ^ 2 := by
    have hv := ProbabilityTheory.variance_eq_sub (μ := μ) (X := X) hmem
    simpa [pow_two] using hv
  constructor
  · exact hmean
  · calc
      @ProbabilityTheory.variance (FlowerVertex n) ⊤ X μ
          = @MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ (fun x => X x ^ 2) -
              (@MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ X) ^ 2 := hvar
      _ = (((n : ℝ) ^ 4 + 2 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 + (n : ℝ)) /
              (3 * (2 * (n : ℝ) + 1) ^ 2) +
            ((n : ℝ) + 1) ^ 4 / ((2 * (n : ℝ) + 1) ^ 2)) -
            (((n : ℝ) + 1) ^ 2 / (2 * (n : ℝ) + 1)) ^ 2 := by
              rw [hsecond, hmean]
      _ = ((n : ℝ) ^ 4 + 2 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 + (n : ℝ)) /
            (3 * (2 * (n : ℝ) + 1) ^ 2) := by
              field_simp [hN]
              ring

/- verified submission -/
theorem flower_graph_equitable_coloring_moments
    (n k : ℕ) (hn : 3 ≤ n) :
    let V := Unit ⊕ (Fin n ⊕ Fin n)
    let F : SimpleGraph V := SimpleGraph.fromRel fun a b =>
      (∃ i : Fin n, a = Sum.inl () ∧ b = Sum.inr (Sum.inl i)) ∨
      (∃ i : Fin n,
        a = Sum.inr (Sum.inl i) ∧
          b = Sum.inr (Sum.inl ((finRotate n) i))) ∨
      (∃ i : Fin n, a = Sum.inr (Sum.inl i) ∧ b = Sum.inr (Sum.inr i)) ∨
      (∃ i : Fin n, a = Sum.inl () ∧ b = Sum.inr (Sum.inr i))
    ∀ f : F.Coloring (Fin k),
      Function.Surjective f →
      (∀ i j : Fin k,
        Nat.dist (f.colorClass i).ncard (f.colorClass j).ncard ≤ 1) →
      (∀ ℓ : ℕ, ℓ < k →
        ¬ ∃ g : F.Coloring (Fin ℓ),
          Function.Surjective g ∧
          (∀ i j : Fin ℓ,
            Nat.dist (g.colorClass i).ncard (g.colorClass j).ncard ≤ 1)) →
      (∀ i j : Fin k, i ≤ j →
        (f.colorClass j).ncard ≤ (f.colorClass i).ncard) →
      let X : V → ℝ := fun x => (↑((f x).val + 1) : ℝ)
      let μ := @PMF.toMeasure V ⊤ (PMF.uniformOfFintype V)
      @MeasureTheory.integral V ℝ _ _ ⊤ μ X =
          ((n : ℝ) + 1) ^ 2 / (2 * (n : ℝ) + 1) ∧
        @ProbabilityTheory.variance V ⊤ X μ =
          ((n : ℝ) ^ 4 + 2 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 + (n : ℝ)) /
            (3 * (2 * (n : ℝ) + 1) ^ 2) := by
  classical
  intro V F f hsurj heq hmin hsort
  have h2n : 2 ≤ n := by omega
  have hk_lower : n + 1 ≤ k :=
    flowerGraph_color_lower f hsurj heq
  have hk_upper : k ≤ n + 1 := by
    by_contra h
    have hlt : n + 1 < k := Nat.lt_of_not_ge h
    exact hmin (n + 1) hlt
      ⟨flowerPairColoring h2n, flowerPairColoring_surjective h2n,
        flowerPairColoring_equitable h2n⟩
  have hk : k = n + 1 := le_antisymm hk_upper hk_lower
  subst k
  exact flower_graph_moments_of_min f hsurj heq hsort


#check_dependency_graph "flower_graph_equitable_coloring_moments" against "{\"edges\":[{\"conclusion\":{\"name\":\"h2n\",\"statement\":\"2 ≤ n\"},\"graphEdgeId\":\"h_001_h2n\",\"premises\":[{\"name\":\"hn\",\"statement\":\"3 ≤ n\"}],\"rawEdgeId\":\"telescope_10\"},{\"conclusion\":{\"name\":\"hk_lower\",\"statement\":\"n + 1 ≤ k\"},\"graphEdgeId\":\"h_002_hk_lower\",\"premises\":[{\"name\":\"hsurj\",\"statement\":\"Function.Surjective ⇑f\"},{\"name\":\"heq\",\"statement\":\"∀ (i j : Fin k), (f.colorClass i).ncard.dist (f.colorClass j).ncard ≤ 1\"}],\"rawEdgeId\":\"telescope_11\"},{\"conclusion\":{\"name\":\"hk_upper\",\"statement\":\"k ≤ n + 1\"},\"graphEdgeId\":\"h_003_hk_upper\",\"premises\":[{\"name\":\"hmin\",\"statement\":\"∀ ℓ < k, ¬∃ g, Function.Surjective ⇑g ∧ ∀ (i j : Fin ℓ), (g.colorClass i).ncard.dist (g.colorClass j).ncard ≤ 1\"},{\"name\":\"h2n\",\"statement\":\"2 ≤ n\"}],\"rawEdgeId\":\"telescope_12\"},{\"conclusion\":{\"name\":\"hk\",\"statement\":\"k = n + 1\"},\"graphEdgeId\":\"h_004_hk\",\"premises\":[{\"name\":\"hk_lower\",\"statement\":\"n + 1 ≤ k\"},{\"name\":\"hk_upper\",\"statement\":\"k ≤ n + 1\"}],\"rawEdgeId\":\"telescope_13\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let X := fun x => ↑(↑(f x) + 1); let μ := (PMF.uniformOfFintype V).toMeasure; MeasureTheory.integral μ X = (↑n + 1) ^ 2 / (2 * ↑n + 1) ∧ ProbabilityTheory.variance X μ = (↑n ^ 4 + 2 * ↑n ^ 3 + 2 * ↑n ^ 2 + ↑n) / (3 * (2 * ↑n + 1) ^ 2)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hsurj\",\"statement\":\"Function.Surjective ⇑f\"},{\"name\":\"heq\",\"statement\":\"∀ (i j : Fin k), (f.colorClass i).ncard.dist (f.colorClass j).ncard ≤ 1\"},{\"name\":\"hmin\",\"statement\":\"∀ ℓ < k, ¬∃ g, Function.Surjective ⇑g ∧ ∀ (i j : Fin ℓ), (g.colorClass i).ncard.dist (g.colorClass j).ncard ≤ 1\"},{\"name\":\"hsort\",\"statement\":\"∀ (i j : Fin k), i ≤ j → (f.colorClass j).ncard ≤ (f.colorClass i).ncard\"},{\"name\":\"hk_lower\",\"statement\":\"n + 1 ≤ k\"},{\"name\":\"hk_upper\",\"statement\":\"k ≤ n + 1\"},{\"name\":\"hk\",\"statement\":\"k = n + 1\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1268_flower_graph_equitable_coloring_moments\",\"reconstructedProofSha256\":\"6cbdaa3ce12753bec5a1e8f5b3c39103eac821254f2029d25666a14413033484\",\"selectedEdgeCount\":5,\"theoremName\":\"flower_graph_equitable_coloring_moments\",\"topologySha256\":\"62fc5d51e2f8984904db07fbb0ba470440156ede0fd07187201aad0c3ef5f3f5\"}"
