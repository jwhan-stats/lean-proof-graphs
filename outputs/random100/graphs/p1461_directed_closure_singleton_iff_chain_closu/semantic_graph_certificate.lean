import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1461_directed_closure_singleton_iff_chain_closu
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 802c35783f6009a5c5c37cffb5c7f6daf1d69d7d6c18bf81c1aa855e0a067907
-- reconstructed_proof_sha256: 17f67180bd332453eed8f2d165176bfc0015985623cb13a8129711f7b7bb698e
-- selected_edge_count: 1

/- accepted add_to_file helper 1 -/
lemma DirectedOn.exists_upper_of_finset {α : Type*} {r : α → α → Prop} {s : Set α}
    (hs : DirectedOn r s) (hsne : s.Nonempty)
    (htrans : ∀ {a b c : α}, r a b → r b c → r a c) (t : Finset α) :
    ↑t ⊆ s → ∃ z ∈ s, ∀ x ∈ t, r x z := by
  classical
  revert t
  intro t
  refine Finset.induction_on t ?_ ?_
  · intro ht
    rcases hsne with ⟨z, hz⟩
    exact ⟨z, hz, by simp⟩
  · intro x t hx ih ht
    have hts : ↑t ⊆ s := by
      intro y hy
      exact ht (Finset.mem_insert_of_mem hy)
    rcases ih hts with ⟨z, hzs, hz⟩
    have hxs : x ∈ s := ht (Finset.mem_insert_self x t)
    rcases hs x hxs z hzs with ⟨w, hws, hxw, hzw⟩
    refine ⟨w, hws, ?_⟩
    intro y hy
    rw [Finset.mem_insert] at hy
    rcases hy with rfl | hyt
    · exact hxw
    · exact htrans (hz y hyt) hzw

/- accepted add_to_file helper 2 -/
lemma cardinal_mk_sum_finset_lt {α : Type*} {κ : Cardinal}
    (hκ : Cardinal.aleph0 ≤ κ) (h : Cardinal.mk α < κ) :
    Cardinal.mk (α ⊕ Finset α) < κ := by
  by_cases hfin : Finite α
  · haveI := hfin
    exact (Cardinal.mk_lt_aleph0.trans_le hκ)
  · haveI : Infinite α := not_finite_iff_infinite.mp hfin
    have hA : Cardinal.aleph0 ≤ Cardinal.mk α := Cardinal.infinite_iff.mp inferInstance
    calc
      Cardinal.mk (α ⊕ Finset α)
          = Cardinal.lift (Cardinal.mk α) + Cardinal.lift (Cardinal.mk (Finset α)) :=
            Cardinal.mk_sum α (Finset α)
      _ = Cardinal.mk α + Cardinal.mk α := by
            simp [Cardinal.mk_finset_of_infinite]
      _ = Cardinal.mk α := Cardinal.add_eq_self hA
      _ < κ := h

/- accepted add_to_file helper 3 -/
universe u

def BinTree (A : Type u) : Type u :=
  WType (fun a : A ⊕ PUnit.{u+1} => Sum.rec (motive := fun _ => Type u)
    (fun _ => PEmpty.{u+1}) (fun _ => ULift.{u} Bool) a)

def BinTree.branch {A : Type u} : A ⊕ PUnit.{u+1} → Type u :=
  fun a => Sum.rec (motive := fun _ => Type u) (fun _ => PEmpty.{u+1}) (fun _ => ULift.{u} Bool) a

def BinTree.leaf {A : Type u} (a : A) : BinTree A :=
  WType.mk (Sum.inl a) PEmpty.elim

def BinTree.node {A : Type u} (t s : BinTree A) : BinTree A :=
  WType.mk (Sum.inr PUnit.unit) (fun b => if b.down then t else s)

noncomputable def BinTree.value {A : Type u} {α : Type u}
    (leaf : A → α) (node : α → α → α) : BinTree A → α :=
  WType.rec (motive := fun _ => α) (fun a f ih =>
    Sum.rec (motive := fun a' => (BinTree.branch a' → α) → α)
      (fun x ih => leaf x)
      (fun _ ih => node (ih ⟨true⟩) (ih ⟨false⟩))
      a ih)

lemma BinTree.value_node {A : Type u} {α : Type u}
    (leaf : A → α) (node : α → α → α) (t s : BinTree A) :
    BinTree.value leaf node (BinTree.node t s) =
      node (BinTree.value leaf node t) (BinTree.value leaf node s) := rfl

lemma BinTree.value_leaf {A : Type u} {α : Type u}
    (leaf : A → α) (node : α → α → α) (a : A) :
    BinTree.value leaf node (BinTree.leaf a) = leaf a := rfl

lemma BinTree.cardinal_lt {A : Type u} {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 < κ) (hA : Cardinal.mk A < κ) :
    Cardinal.mk (BinTree A) < κ := by
  let Labels : Type u := A ⊕ PUnit.{u+1}
  let Branch : Labels → Type u := fun a =>
    Sum.rec (motive := fun _ => Type u) (fun _ => PEmpty.{u+1}) (fun _ => ULift.{u} Bool) a
  haveI : ∀ a : Labels, Finite (Branch a) := by
    intro a
    cases a <;> simp [Branch] <;> infer_instance
  have hlabels : Cardinal.mk Labels ≤ max (Cardinal.mk A) Cardinal.aleph0 := by
    calc
      Cardinal.mk Labels
          = Cardinal.lift.{u,u} (Cardinal.mk A) +
              Cardinal.lift.{u,u} (Cardinal.mk PUnit.{u+1}) := by
            simp [Labels, Cardinal.mk_sum]
      _ ≤ max (max (Cardinal.lift.{u,u} (Cardinal.mk A))
              (Cardinal.lift.{u,u} (Cardinal.mk PUnit.{u+1})))
            Cardinal.aleph0 :=
            Cardinal.add_le_max _ _
      _ = max (Cardinal.mk A) Cardinal.aleph0 := by
            rw [Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_punit, max_assoc,
              max_eq_right Cardinal.one_le_aleph0]
  have htree := WType.cardinalMk_le_max_aleph0_of_finite (β := Branch)
  change Cardinal.mk (WType Branch) ≤ max (Cardinal.mk Labels) Cardinal.aleph0 at htree
  have : Cardinal.mk (WType Branch) ≤ max (Cardinal.mk A) Cardinal.aleph0 := by
    calc
      Cardinal.mk (WType Branch) ≤ max (Cardinal.mk Labels) Cardinal.aleph0 := htree
      _ ≤ max (max (Cardinal.mk A) Cardinal.aleph0) Cardinal.aleph0 := by
            exact max_le_max_right _ hlabels
      _ = max (Cardinal.mk A) Cardinal.aleph0 := by simp
  exact lt_of_le_of_lt this (max_lt hA hκ)

/- accepted add_to_file helper 4 -/
lemma DirectedOn.exists_directed_superset_card_lt {α : Type u} {r : α → α → Prop}
    {D A : Set α} (hD : DirectedOn r D) (hDne : D.Nonempty)
    (hAD : A ⊆ D)
    {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 < κ) (hAcard : Cardinal.mk A < κ) :
    ∃ E : Set α, A ⊆ E ∧ E ⊆ D ∧ DirectedOn r E ∧ Cardinal.mk E < κ := by
  classical
  rcases hDne with ⟨d0, hd0⟩
  let pairUpper : α → α → α := fun x y =>
    if hx : x ∈ D then
      if hy : y ∈ D then Classical.choose (hD x hx y hy) else d0
    else d0
  have hpair : ∀ {x y : α}, x ∈ D → y ∈ D →
      pairUpper x y ∈ D ∧ r x (pairUpper x y) ∧ r y (pairUpper x y) := by
    intro x y hx hy
    have hspec := Classical.choose_spec (hD x hx y hy)
    simpa [pairUpper, hx, hy] using hspec
  let leaf : A → α := fun a => a
  let value : BinTree A → α := BinTree.value leaf pairUpper
  have hvalue_mem : ∀ t : BinTree A, value t ∈ D := by
    intro t
    induction t using WType.rec with
    | mk a f ih =>
        cases a with
        | inl a =>
            exact hAD a.property
        | inr p =>
            exact (hpair (ih ⟨true⟩) (ih ⟨false⟩)).1
  let E : Set α := Set.range value
  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact ⟨BinTree.leaf ⟨a, ha⟩, rfl⟩
  · intro x hx
    rcases hx with ⟨t, rfl⟩
    exact hvalue_mem t
  · intro x hx y hy
    rcases hx with ⟨t, rfl⟩
    rcases hy with ⟨s, rfl⟩
    refine ⟨value (BinTree.node t s), ⟨BinTree.node t s, rfl⟩, ?_, ?_⟩
    · exact (hpair (hvalue_mem t) (hvalue_mem s)).2.1
    · exact (hpair (hvalue_mem t) (hvalue_mem s)).2.2
  · exact Cardinal.mk_range_le.trans_lt (BinTree.cardinal_lt hκ hAcard)

/- accepted add_to_file helper 5 -/
lemma DirectedOn.exists_chain_cofinal_of_countable {α : Type u} [Preorder α]
    {D : Set α} (hD : DirectedOn (fun x y => x ≤ y) D) (hne : D.Nonempty)
    (hcount : D.Countable) :
    ∃ C : Set α, C ⊆ D ∧ IsChain (fun x y => x ≤ y) C ∧
      ∀ d ∈ D, ∃ c ∈ C, d ≤ c := by
  classical
  rcases hcount.exists_surjective hne with ⟨f, hf⟩
  let step : D → ℕ → D := fun x n =>
    ⟨Classical.choose (hD x x.property (f (n+1)) (f (n+1)).property),
      (Classical.choose_spec (hD x x.property (f (n+1)) (f (n+1)).property)).1⟩
  have hstep : ∀ x n, (step x n).1 ∈ D ∧ x ≤ step x n ∧ f (n+1) ≤ step x n := by
    intro x n
    exact Classical.choose_spec (hD x x.property (f (n+1)) (f (n+1)).property)
  let c : ℕ → D := fun n => Nat.rec (f 0) (fun n x => step x n) n
  have hc_succ : ∀ n, c n ≤ c (n+1) := by
    intro n
    simpa [c] using (hstep (c n) n).2.1
  have hc_mono : Monotone c := monotone_nat_of_le_succ hc_succ
  have hf_le : ∀ n, f n ≤ c n := by
    intro n
    cases n with
    | zero =>
        simp [c]
    | succ n =>
        simpa [c] using (hstep (c n) n).2.2
  have hf_le' : ∀ n, (f n).1 ≤ (c n).1 := by
    intro n
    exact Subtype.coe_le_coe.mpr (hf_le n)
  refine ⟨Set.range fun n => (c n).1, ?_, ?_, ?_⟩
  · intro x hx
    rcases hx with ⟨n, rfl⟩
    exact (c n).property
  · intro x hx y hy hxy
    rcases hx with ⟨n, rfl⟩
    rcases hy with ⟨m, rfl⟩
    rcases le_total n m with hnm | hmn
    · left
      exact Subtype.coe_le_coe.mpr (hc_mono hnm)
    · right
      exact Subtype.coe_le_coe.mpr (hc_mono hmn)
  · intro d hd
    rcases hf ⟨d, hd⟩ with ⟨n, hn⟩
    refine ⟨(c n).1, ⟨n, rfl⟩, ?_⟩
    have hfd : (f n).1 = d := congrArg Subtype.val hn
    calc
      d = (f n).1 := hfd.symm
      _ ≤ (c n).1 := hf_le' n

/- accepted add_to_file helper 6 -/
lemma closure_eq_closure_singleton_of_forall_le {X : Type u} [TopologicalSpace X]
    {D : Set X} {z : X} (hz : z ∈ D)
    (hub : ∀ d ∈ D, (specializationPreorder X).le d z) :
    closure D = closure ({z} : Set X) := by
  letI := specializationPreorder X
  apply Set.Subset.antisymm
  · have hDsub : D ⊆ closure ({z} : Set X) := by
      intro d hd
      rw [closure_singleton_eq_Iic z]
      exact hub d hd
    exact closure_minimal hDsub isClosed_closure
  · exact closure_mono (Set.singleton_subset_iff.mpr hz)

/- accepted add_to_file helper 7 -/
lemma closure_eq_closure_singleton_of_mem_closure_of_forall_le {X : Type u}
    [TopologicalSpace X] {D : Set X} {x : X} (hx : x ∈ closure D)
    (hub : ∀ d ∈ D, (specializationPreorder X).le d x) :
    closure D = closure ({x} : Set X) := by
  letI := specializationPreorder X
  apply Set.Subset.antisymm
  · have hDsub : D ⊆ closure ({x} : Set X) := by
      intro d hd
      rw [closure_singleton_eq_Iic x]
      exact hub d hd
    exact closure_minimal hDsub isClosed_closure
  · exact closure_minimal (Set.singleton_subset_iff.mpr hx) isClosed_closure

/- accepted add_to_file helper 8 -/
lemma exists_closure_singleton_of_chain_of_countable {X : Type u}
    [TopologicalSpace X]
    (hchain : ∀ C : Set X, C.Nonempty →
      IsChain (specializationPreorder X).le C →
      ∃ x : X, closure C = closure ({x} : Set X))
    {D : Set X} (hne : D.Nonempty)
    (hdir : DirectedOn (specializationPreorder X).le D)
    (hcount : D.Countable) :
    ∃ x : X, closure D = closure ({x} : Set X) := by
  letI := specializationPreorder X
  rcases hdir.exists_chain_cofinal_of_countable hne hcount with ⟨C, hCD, hCchain, hcof⟩
  have hCne : C.Nonempty := by
    rcases hne with ⟨d, hd⟩
    rcases hcof d hd with ⟨c, hcC, hdc⟩
    exact ⟨c, hcC⟩
  rcases hchain C hCne hCchain with ⟨x, hxCeq⟩
  have hcupper : ∀ c ∈ C, c ≤ x := by
    intro c hc
    have hccl : c ∈ closure C := subset_closure hc
    rw [hxCeq, closure_singleton_eq_Iic x] at hccl
    exact hccl
  have hxmemC : x ∈ closure C := by
    rw [hxCeq]
    exact subset_closure rfl
  have hxmemD : x ∈ closure D := closure_mono hCD hxmemC
  have hupper : ∀ d ∈ D, d ≤ x := by
    intro d hd
    rcases hcof d hd with ⟨c, hcC, hdc⟩
    exact hdc.trans (hcupper c hcC)
  exact ⟨x, closure_eq_closure_singleton_of_mem_closure_of_forall_le hxmemD hupper⟩

/- accepted add_to_file helper 9 -/
lemma cardinal_mk_sum_punit_lt {α : Type u} {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 < κ) (h : Cardinal.mk α < κ) :
    Cardinal.mk (α ⊕ PUnit.{u+1}) < κ := by
  calc
    Cardinal.mk (α ⊕ PUnit.{u+1})
        = Cardinal.lift.{u,u} (Cardinal.mk α) +
            Cardinal.lift.{u,u} (Cardinal.mk PUnit.{u+1}) := by
          simp [Cardinal.mk_sum]
    _ ≤ max (max (Cardinal.lift.{u,u} (Cardinal.mk α))
            (Cardinal.lift.{u,u} (Cardinal.mk PUnit.{u+1})))
          Cardinal.aleph0 :=
          Cardinal.add_le_max _ _
    _ = max (Cardinal.mk α) Cardinal.aleph0 := by
          rw [Cardinal.lift_id, Cardinal.lift_id, Cardinal.mk_punit, max_assoc,
            max_eq_right Cardinal.one_le_aleph0]
    _ < κ := max_lt h hκ

/- accepted add_to_file helper 10 -/
noncomputable def BinTree.map {A B : Type u} (f : A → B) : BinTree A → BinTree B :=
  WType.rec (motive := fun _ => BinTree B) (fun a children ih =>
    Sum.rec (motive := fun a' => (BinTree.branch a' → BinTree B) → BinTree B)
      (fun a ih => BinTree.leaf (f a))
      (fun _ ih => BinTree.node (ih ⟨true⟩) (ih ⟨false⟩))
      a ih)

lemma BinTree.value_map {A B : Type u} {α : Type u} (f : A → B)
    (leaf : B → α) (node : α → α → α) (t : BinTree A) :
    BinTree.value leaf node (BinTree.map f t) =
      BinTree.value (fun a => leaf (f a)) node t := by
  induction t using WType.rec with
  | mk a children ih =>
      cases a with
      | inl a =>
          rfl
      | inr p =>
          simp only [BinTree.map, BinTree.value, BinTree.node]
          simp
          change node
            (BinTree.value leaf node (BinTree.map f (children ⟨true⟩)))
            (BinTree.value leaf node (BinTree.map f (children ⟨false⟩))) =
          node
            (BinTree.value (fun a => leaf (f a)) node (children ⟨true⟩))
            (BinTree.value (fun a => leaf (f a)) node (children ⟨false⟩))
          rw [ih ⟨true⟩, ih ⟨false⟩]

/- accepted add_to_file helper 11 -/
lemma exists_closure_singleton_of_chain {X : Type u} [TopologicalSpace X]
    (hchain : ∀ C : Set X, C.Nonempty →
      IsChain (specializationPreorder X).le C →
      ∃ x : X, closure C = closure ({x} : Set X)) :
    ∀ D : Set X, D.Nonempty →
      DirectedOn (specializationPreorder X).le D →
      ∃ x : X, closure D = closure ({x} : Set X) := by
  letI := specializationPreorder X
  intro D hne hdir
  have H : ∀ κ : Cardinal.{u}, ∀ S : Set X, Cardinal.mk S = κ →
      S.Nonempty → DirectedOn (fun x y => x ≤ y) S →
      ∃ x : X, closure S = closure ({x} : Set X) := by
    intro κ
    refine Cardinal.lt_wf.induction
      (C := fun κ : Cardinal.{u} => ∀ S : Set X, Cardinal.mk S = κ →
        S.Nonempty → DirectedOn (fun x y => x ≤ y) S →
        ∃ x : X, closure S = closure ({x} : Set X)) κ ?_
    intro κ ih S hmk hSne hSdir
    by_cases hcount : Cardinal.mk S ≤ Cardinal.aleph0
    · exact exists_closure_singleton_of_chain_of_countable hchain hSne hSdir
        ((Cardinal.le_aleph0_iff_set_countable).mp hcount)
    · classical
      have hκ0 : Cardinal.aleph0 < κ := by
        rw [← hmk]
        exact lt_of_not_ge hcount
      let I : Type u := κ.ord.ToType
      have hmkI : Cardinal.mk S = Cardinal.mk I := by
        rw [hmk]
        exact (Cardinal.mk_ord_toType κ).symm
      obtain ⟨e⟩ := Cardinal.eq.mp hmkI
      let d : I → X := fun i => (e.symm i : X)
      let A : I → Set X := fun i => Set.range fun j : Set.Iio i ⊕ PUnit.{u+1} =>
        Sum.rec (motive := fun _ => X)
          (fun j => d j.1) (fun _ => d i) j
      have hAD : ∀ i, A i ⊆ S := by
        intro i x hx
        rcases hx with ⟨j, rfl⟩
        cases j with
        | inl j => exact (e.symm j.1).property
        | inr p => exact (e.symm i).property
      have hAne : ∀ i, (A i).Nonempty := by
        intro i
        refine ⟨d i, ?_⟩
        exact ⟨Sum.inr PUnit.unit, rfl⟩
      have hAcard : ∀ i, Cardinal.mk (A i) < κ := by
        intro i
        have hIio : Cardinal.mk (Set.Iio i) < κ := Cardinal.mk_Iio_toType_ord_lt i
        have hIndex : Cardinal.mk (Set.Iio i ⊕ PUnit.{u+1}) < κ :=
          cardinal_mk_sum_punit_lt hκ0 hIio
        exact Cardinal.mk_range_le.trans_lt hIndex
      rcases hSne with ⟨s0, hs0⟩
      let pairUpper : X → X → X := fun x y =>
        if hx : x ∈ S then
          if hy : y ∈ S then Classical.choose (hSdir x hx y hy) else s0
        else s0
      have hpair : ∀ {x y : X}, x ∈ S → y ∈ S →
          pairUpper x y ∈ S ∧ x ≤ pairUpper x y ∧ y ≤ pairUpper x y := by
        intro x y hx hy
        have hspec := Classical.choose_spec (hSdir x hx y hy)
        simpa [pairUpper, hx, hy] using hspec
      let E : I → Set X := fun i =>
        Set.range (BinTree.value (fun a : A i => (a : X)) pairUpper)
      have hAE : ∀ i, A i ⊆ E i := by
        intro i a ha
        exact ⟨BinTree.leaf ⟨a, ha⟩, rfl⟩
      have hED : ∀ i, E i ⊆ S := by
        intro i x hx
        rcases hx with ⟨t, rfl⟩
        induction t using WType.rec with
        | mk a f ihv =>
            cases a with
            | inl a =>
                exact hAD i a.property
            | inr p =>
                exact (hpair (ihv ⟨true⟩) (ihv ⟨false⟩)).1
      have hEdir : ∀ i, DirectedOn (fun x y => x ≤ y) (E i) := by
        intro i x hx y hy
        rcases hx with ⟨t, rfl⟩
        rcases hy with ⟨s, rfl⟩
        let val : BinTree (A i) → X := BinTree.value (fun a : A i => (a : X)) pairUpper
        have htS : val t ∈ S := hED i ⟨t, rfl⟩
        have hsS : val s ∈ S := hED i ⟨s, rfl⟩
        refine ⟨val (BinTree.node t s), ⟨BinTree.node t s, rfl⟩, ?_, ?_⟩
        · exact (hpair htS hsS).2.1
        · exact (hpair htS hsS).2.2
      have hEcard : ∀ i, Cardinal.mk (E i) < κ := by
        intro i
        exact Cardinal.mk_range_le.trans_lt (BinTree.cardinal_lt hκ0 (hAcard i))
      have hEmono : Monotone E := by
        intro i j hij x hx
        have hAA : A i ⊆ A j := by
          intro a ha
          rcases ha with ⟨k, rfl⟩
          cases k with
          | inl k =>
              refine ⟨Sum.inl ⟨k.1, ?_⟩, rfl⟩
              exact lt_of_lt_of_le k.2 hij
          | inr p =>
              rcases eq_or_lt_of_le hij with rfl | hlt
              · exact ⟨Sum.inr PUnit.unit, rfl⟩
              · exact ⟨Sum.inl ⟨i, hlt⟩, rfl⟩
        rcases hx with ⟨t, rfl⟩
        let inc : A i → A j := fun a => ⟨a.1, hAA a.2⟩
        refine ⟨BinTree.map inc t, ?_⟩
        rw [BinTree.value_map]
      have hEne : ∀ i, (E i).Nonempty := by
        intro i
        exact Set.Nonempty.mono (hAE i) (hAne i)
      choose x hx using fun i => ih (Cardinal.mk (E i)) (hEcard i) (E i) rfl (hEne i) (hEdir i)
      have hxmono : Monotone x := by
        intro i j hij
        have hximem : x i ∈ closure (E i) := by
          rw [hx i]
          exact subset_closure rfl
        have hxiclj : x i ∈ closure (E j) := closure_mono (hEmono hij) hximem
        rw [hx j, closure_singleton_eq_Iic] at hxiclj
        exact hxiclj
      have hIne : Nonempty I := ⟨e ⟨s0, hs0⟩⟩
      let C : Set X := Set.range x
      have hCne : C.Nonempty := by
        rcases hIne with ⟨i⟩
        exact ⟨x i, ⟨i, rfl⟩⟩
      have hCchain : IsChain (fun x1 x2 => x1 ≤ x2) C := by
        intro a ha b hb hab
        rcases ha with ⟨i, rfl⟩
        rcases hb with ⟨j, rfl⟩
        rcases le_total i j with hij | hji
        · left
          exact hxmono hij
        · right
          exact hxmono hji
      rcases hchain C hCne hCchain with ⟨z, hzCeq⟩
      have hrange_subset_closureS : Set.range x ⊆ closure S := by
        intro y hy
        rcases hy with ⟨i, rfl⟩
        have hximem : x i ∈ closure (E i) := by
          rw [hx i]
          exact subset_closure rfl
        exact closure_mono (hED i) hximem
      have hzmemS : z ∈ closure S := by
        have hzmemC : z ∈ closure C := by
          rw [hzCeq]
          exact subset_closure rfl
        simpa [closure_closure] using closure_mono hrange_subset_closureS hzmemC
      have hrangeupper : ∀ y ∈ Set.range x, y ≤ z := by
        intro y hy
        have hycl : y ∈ closure C := subset_closure hy
        rw [hzCeq, closure_singleton_eq_Iic z] at hycl
        exact hycl
      have hEupper : ∀ i, ∀ y ∈ E i, y ≤ x i := by
        intro i y hy
        have hycl : y ∈ closure (E i) := subset_closure hy
        rw [hx i, closure_singleton_eq_Iic] at hycl
        exact hycl
      have hSupper : ∀ y ∈ S, y ≤ z := by
        intro y hy
        let i : I := e ⟨y, hy⟩
        have hyA : y ∈ A i := by
          refine ⟨Sum.inr PUnit.unit, ?_⟩
          simp [A, d, i]
        have hyE : y ∈ E i := hAE i hyA
        exact (hEupper i y hyE).trans (hrangeupper (x i) ⟨i, rfl⟩)
      exact ⟨z, closure_eq_closure_singleton_of_mem_closure_of_forall_le hzmemS hSupper⟩
  exact H (Cardinal.mk D) D rfl hne hdir

/- verified submission -/
theorem directed_closure_singleton_iff_chain_closure_singleton
    (X : Type*) [TopologicalSpace X] [T0Space X] :
    (∀ D : Set X, D.Nonempty →
      DirectedOn (specializationPreorder X).le D →
      ∃! x : X, closure D = closure ({x} : Set X)) ↔
    (∀ C : Set X, C.Nonempty →
      IsChain (specializationPreorder X).le C →
      ∃! x : X, closure C = closure ({x} : Set X)) := by
  constructor
  · intro h C hCne hCchain
    exact h C hCne hCchain.directedOn
  · intro h D hDne hDdir
    have hex : ∃ x : X, closure D = closure ({x} : Set X) := by
      apply exists_closure_singleton_of_chain _ D hDne hDdir
      intro C hCne hCchain
      exact (h C hCne hCchain).exists
    rcases hex with ⟨x, hx⟩
    refine ⟨x, hx, ?_⟩
    intro y hy
    apply Inseparable.eq
    apply (inseparable_iff_closure_eq).mpr
    rw [← hx]
    exact hy.symm


#check_dependency_graph "directed_closure_singleton_iff_chain_closure_singleton" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(∀ (D : Set X), D.Nonempty → DirectedOn LE.le D → ∃! x, closure D = closure {x}) ↔ ∀ (C : Set X), C.Nonempty → IsChain LE.le C → ∃! x, closure C = closure {x}\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"T0Space X\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1461_directed_closure_singleton_iff_chain_closu\",\"reconstructedProofSha256\":\"17f67180bd332453eed8f2d165176bfc0015985623cb13a8129711f7b7bb698e\",\"selectedEdgeCount\":1,\"theoremName\":\"directed_closure_singleton_iff_chain_closure_singleton\",\"topologySha256\":\"802c35783f6009a5c5c37cffb5c7f6daf1d69d7d6c18bf81c1aa855e0a067907\"}"
