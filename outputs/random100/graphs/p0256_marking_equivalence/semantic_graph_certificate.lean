import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p0256_marking_equivalence
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: acea382a18f4676772634e4c125bc3b8781d6f109529629ba6e047944a7af310
-- reconstructed_proof_sha256: f546a85dd85832b60512ac83157f0aedb52d1218b94f5f6f282d4041f4f8af85
-- selected_edge_count: 1

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


#check_dependency_graph "marking_equivalence" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"Relation.ReflTransGen Move μ ν\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hn\",\"statement\":\"0 < n\"},{\"name\":\"hμ\",\"statement\":\"irreducible μ\"},{\"name\":\"hν\",\"statement\":\"irreducible ν\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0256_marking_equivalence\",\"reconstructedProofSha256\":\"f546a85dd85832b60512ac83157f0aedb52d1218b94f5f6f282d4041f4f8af85\",\"selectedEdgeCount\":1,\"theoremName\":\"marking_equivalence\",\"topologySha256\":\"acea382a18f4676772634e4c125bc3b8781d6f109529629ba6e047944a7af310\"}"
