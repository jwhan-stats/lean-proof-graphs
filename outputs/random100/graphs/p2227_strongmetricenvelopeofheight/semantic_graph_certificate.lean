import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p2227_strongmetricenvelopeofheight
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 0c7a7e1ae1d7e6f1a427f32a3d41f791bd3bd2dbc65bf4ed5fae4de7739626f6
-- reconstructed_proof_sha256: 964d5827dbfe76c5223cd0228076320fa62b8063e8b6c94499060e9ec639c56f
-- selected_edge_count: 1

/- accepted add_to_file helper 1 -/
lemma finprod_sum_elim {ι κ M : Type*} [CommMonoid M]
    (f : ι → M) (g : κ → M)
    (hf : Function.HasFiniteMulSupport f)
    (hg : Function.HasFiniteMulSupport g) :
    (∏ᶠ x : ι ⊕ κ, Sum.elim f g x) =
      (∏ᶠ i, f i) * ∏ᶠ j, g j := by
  classical
  let s := hf.toFinset
  let t := hg.toFinset
  have hsub : Function.mulSupport (Sum.elim f g) ⊆ ↑(s.disjSum t) := by
    intro x hx
    cases x with
    | inl i =>
        have hi : i ∈ s := by
          have hi' : i ∈ hf.toFinset := (hf.mem_toFinset).2 hx
          simpa [s] using hi'
        simp [Finset.mem_disjSum, hi]
    | inr j =>
        have hj : j ∈ t := by
          have hj' : j ∈ hg.toFinset := (hg.mem_toFinset).2 hx
          simpa [t] using hj'
        simp [Finset.mem_disjSum, hj]
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  rw [Finset.prod_sumElim]
  rw [finprod_eq_prod_of_mulSupport_subset f (s:=s) (by
    intro i hi
    have hi' : i ∈ hf.toFinset := by simpa [s] using hi
    simpa [s] using (hf.mem_toFinset).1 hi'),
    finprod_eq_prod_of_mulSupport_subset g (s:=t) (by
    intro j hj
    have hj' : j ∈ hg.toFinset := by simpa [t] using hj
    simpa [t] using (hg.mem_toFinset).1 hj')]

noncomputable def pnatInterleaveEquiv : ℕ+ ≃ ℕ+ ⊕ ℕ+ :=
  Equiv.pnatEquivNat.trans
    (Equiv.natSumNatEquivNat.symm.trans
      ((Equiv.pnatEquivNat.symm).sumCongr Equiv.pnatEquivNat.symm))

lemma hasFiniteMulSupport_interleave {M : Type*} [One M]
    {a b : ℕ+ → M}
    (ha : Function.HasFiniteMulSupport a)
    (hb : Function.HasFiniteMulSupport b) :
    Function.HasFiniteMulSupport
      (fun n : ℕ+ ↦ Sum.elim a b (pnatInterleaveEquiv n)) := by
  classical
  have hsum : Function.HasFiniteMulSupport (Sum.elim a b) := by
    apply (Set.Finite.union
      (Set.Finite.image (α:=ℕ+) (s:=Function.mulSupport a) Sum.inl ha)
      (Set.Finite.image (α:=ℕ+) (s:=Function.mulSupport b) Sum.inr hb)).subset
    intro x hx
    cases x with
    | inl i =>
        exact Set.mem_union_left _ ⟨i, (Function.mem_mulSupport).1 hx, rfl⟩
    | inr j =>
        exact Set.mem_union_right _ ⟨j, (Function.mem_mulSupport).1 hx, rfl⟩
  simpa [Function.comp_def] using hsum.fun_comp_of_injective pnatInterleaveEquiv.injective

lemma finprod_interleave {M : Type*} [CommMonoid M]
    {a b : ℕ+ → M}
    (ha : Function.HasFiniteMulSupport a)
    (hb : Function.HasFiniteMulSupport b) :
    (∏ᶠ n : ℕ+, Sum.elim a b (pnatInterleaveEquiv n)) =
      (∏ᶠ n, a n) * ∏ᶠ n, b n := by
  exact (finprod_comp (g := Sum.elim a b) pnatInterleaveEquiv
    pnatInterleaveEquiv.bijective).trans (finprod_sum_elim a b ha hb)

lemma finite_range_apply_of_hasFiniteMulSupport {M : Type*} [One M]
    {a : ℕ+ → M} (ha : Function.HasFiniteMulSupport a) (f : M → ℝ) :
    Set.Finite (Set.range fun n : ℕ+ ↦ f (a n)) := by
  classical
  apply (Set.Finite.union
    (Set.Finite.image (α:=ℕ+) (β:=ℝ) (s:=Function.mulSupport a)
      (fun n : ℕ+ ↦ f (a n)) ha)
    (Set.finite_singleton (f 1))).subset
  rintro y ⟨n, rfl⟩
  by_cases hn : a n = 1
  · exact Set.mem_union_right _ (by simpa [hn])
  · exact Set.mem_union_left _
      (Set.mem_image_of_mem (fun m : ℕ+ ↦ f (a m)) ((Function.mem_mulSupport).2 hn))

lemma bddAbove_range_apply_of_hasFiniteMulSupport {M : Type*} [One M]
    {a : ℕ+ → M} (ha : Function.HasFiniteMulSupport a) (f : M → ℝ) :
    BddAbove (Set.range fun n : ℕ+ ↦ f (a n)) :=
  (finite_range_apply_of_hasFiniteMulSupport ha f).bddAbove

/- accepted add_to_file helper 2 -/
lemma sSup_range_interleave {G : Type*} [One G]
    {a b : ℕ+ → G}
    (ha : Function.HasFiniteMulSupport a)
    (hb : Function.HasFiniteMulSupport b)
    (f : G → ℝ) :
    sSup (Set.range fun n : ℕ+ ↦
        f (Sum.elim a b (pnatInterleaveEquiv n))) =
      max (sSup (Set.range fun n : ℕ+ ↦ f (a n)))
        (sSup (Set.range fun n : ℕ+ ↦ f (b n))) := by
  classical
  let e := pnatInterleaveEquiv
  have hrange :
      Set.range (fun n : ℕ+ ↦ f (Sum.elim a b (e n))) =
        Set.range (fun n : ℕ+ ↦ f (a n)) ∪
          Set.range (fun n : ℕ+ ↦ f (b n)) := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      cases he : e n with
      | inl i =>
          exact Or.inl ⟨i, by simpa [he]⟩
      | inr j =>
          exact Or.inr ⟨j, by simpa [he]⟩
    · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
      · obtain ⟨n, hn⟩ := e.surjective (Sum.inl i)
        exact ⟨n, by simp [hn]⟩
      · obtain ⟨n, hn⟩ := e.surjective (Sum.inr j)
        exact ⟨n, by simp [hn]⟩
  rw [hrange]
  rw [csSup_union
    (bddAbove_range_apply_of_hasFiniteMulSupport ha f)
    (Set.range_nonempty _)
    (bddAbove_range_apply_of_hasFiniteMulSupport hb f)
    (Set.range_nonempty _)]

/- accepted add_to_file helper 3 -/
def pnatSingle {M : Type*} [One M] (x : M) : ℕ+ → M :=
  fun n ↦ if n = 1 then x else 1

lemma hasFiniteMulSupport_pnatSingle {M : Type*} [One M] (x : M) :
    Function.HasFiniteMulSupport (pnatSingle x) := by
  classical
  apply (Set.finite_singleton (1 : ℕ+)).subset
  intro n hn
  by_cases h : n = 1
  · simpa [h]
  · exfalso
    exact hn (by simp [pnatSingle, h])

lemma finprod_pnatSingle {M : Type*} [CommMonoid M] (x : M) :
    (∏ᶠ n : ℕ+, pnatSingle x n) = x := by
  classical
  have hsub : Function.mulSupport (pnatSingle x) ⊆ ↑({1} : Finset ℕ+) := by
    intro n hn
    by_cases h : n = 1
    · simpa [h]
    · exfalso
      exact hn (by simp [pnatSingle, h])
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  simp [pnatSingle]

lemma sSup_range_apply_pnatSingle {G : Type*} [One G]
    (f : G → ℝ) (x : G)
    (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) :
    sSup (Set.range fun n : ℕ+ ↦ f (pnatSingle x n)) = f x := by
  classical
  have hrange : Set.range (fun n : ℕ+ ↦ f (pnatSingle x n)) = {f x, f 1} := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      by_cases h : n = 1
      · simp [pnatSingle, h]
      · simp [pnatSingle, h]
    · rintro (rfl | rfl)
      · exact ⟨1, by simp [pnatSingle]⟩
      · exact ⟨2, by simp [pnatSingle]⟩
  rw [hrange, csSup_pair]
  have h : f 1 ≤ f x := by simpa [hf_one] using hf_lower x
  exact max_eq_left h

/- accepted add_to_file helper 4 -/
noncomputable abbrev heightEnvOne {G : Type*} [CommMonoid G] (f : G → ℝ) (α : G) : ℝ :=
  sInf {r : ℝ | ∃ a : ℕ+ → G,
    Function.HasFiniteMulSupport a ∧
    (∏ᶠ n, a n) = α ∧
    (∏ᶠ n, f (a n)) = r}

noncomputable abbrev heightEnvInf {G : Type*} [CommMonoid G] (f : G → ℝ) (α : G) : ℝ :=
  sInf {r : ℝ | ∃ a : ℕ+ → G,
    Function.HasFiniteMulSupport a ∧
    (∏ᶠ n, a n) = α ∧
    sSup (Set.range fun n : ℕ+ ↦ f (a n)) = r}

lemma one_le_finprod_apply_of_hasFiniteMulSupport {G : Type*} [One G]
    {a : ℕ+ → G} (ha : Function.HasFiniteMulSupport a)
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) :
    1 ≤ ∏ᶠ n : ℕ+, f (a n) := by
  classical
  let s := ha.toFinset
  have hsub : Function.mulSupport (fun n : ℕ+ ↦ f (a n)) ⊆ ↑s := by
    intro n hn
    have hnfa : f (a n) ≠ 1 := (Function.mem_mulSupport).1 hn
    by_contra hns
    have hna : a n = 1 := by
      by_contra hna
      exact hns (by
        have : n ∈ ha.toFinset := (ha.mem_toFinset).2 ((Function.mem_mulSupport).2 hna)
        simpa [s] using this)
    exact hnfa (by simp [hna, hf_one])
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  exact Finset.one_le_prod (fun n _ ↦ hf_lower (a n))

lemma one_le_sSup_range_apply_of_hasFiniteMulSupport {G : Type*} [One G]
    {a : ℕ+ → G} (ha : Function.HasFiniteMulSupport a)
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) :
    1 ≤ sSup (Set.range fun n : ℕ+ ↦ f (a n)) := by
  classical
  obtain ⟨n, hn⟩ := ha.exists_notMem
  have han : a n = 1 := by
    by_contra h
    exact hn ((Function.mem_mulSupport).2 h)
  have hmem : f (a n) ∈ Set.range fun n : ℕ+ ↦ f (a n) := ⟨n, rfl⟩
  have hle := le_csSup (bddAbove_range_apply_of_hasFiniteMulSupport ha f) hmem
  simpa [han, hf_one] using hle

lemma heightEnvOne_nonempty {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    {r : ℝ | ∃ a : ℕ+ → G,
      Function.HasFiniteMulSupport a ∧
      (∏ᶠ n, a n) = α ∧
      (∏ᶠ n, f (a n)) = r}.Nonempty := by
  classical
  refine ⟨f α, pnatSingle α, hasFiniteMulSupport_pnatSingle α,
    finprod_pnatSingle α, ?_⟩
  have hsub : Function.mulSupport (fun n : ℕ+ ↦ f (pnatSingle α n)) ⊆
      ↑({1} : Finset ℕ+) := by
    intro n hn
    by_cases h : n = 1
    · simpa [h]
    · exfalso
      exact (Function.mem_mulSupport).1 hn (by simp [pnatSingle, h, hf_one])
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  simp [pnatSingle]

lemma heightEnvInf_nonempty {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    {r : ℝ | ∃ a : ℕ+ → G,
      Function.HasFiniteMulSupport a ∧
      (∏ᶠ n, a n) = α ∧
      sSup (Set.range fun n : ℕ+ ↦ f (a n)) = r}.Nonempty := by
  exact ⟨f α, pnatSingle α, hasFiniteMulSupport_pnatSingle α,
    finprod_pnatSingle α, sSup_range_apply_pnatSingle f α hf_lower hf_one⟩

/- accepted add_to_file helper 5 -/
lemma heightEnvOne_bddBelow {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    BddBelow {r : ℝ | ∃ a : ℕ+ → G,
      Function.HasFiniteMulSupport a ∧
      (∏ᶠ n, a n) = α ∧
      (∏ᶠ n, f (a n)) = r} := by
  refine ⟨1, ?_⟩
  rintro r ⟨a, ha, -, hprod⟩
  rw [← hprod]
  exact one_le_finprod_apply_of_hasFiniteMulSupport ha f hf_lower hf_one

lemma heightEnvInf_bddBelow {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    BddBelow {r : ℝ | ∃ a : ℕ+ → G,
      Function.HasFiniteMulSupport a ∧
      (∏ᶠ n, a n) = α ∧
      sSup (Set.range fun n : ℕ+ ↦ f (a n)) = r} := by
  refine ⟨1, ?_⟩
  rintro r ⟨a, ha, -, hsup⟩
  rw [← hsup]
  exact one_le_sSup_range_apply_of_hasFiniteMulSupport ha f hf_lower hf_one

lemma one_le_heightEnvInf {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    1 ≤ heightEnvInf f α := by
  apply le_csInf (heightEnvInf_nonempty f hf_lower hf_one α)
  rintro r ⟨a, ha, -, hsup⟩
  rw [← hsup]
  exact one_le_sSup_range_apply_of_hasFiniteMulSupport ha f hf_lower hf_one

lemma heightEnvInf_le_self {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    heightEnvInf f α ≤ f α := by
  apply csInf_le (heightEnvInf_bddBelow f hf_lower hf_one α)
  exact ⟨pnatSingle α, hasFiniteMulSupport_pnatSingle α, finprod_pnatSingle α,
    sSup_range_apply_pnatSingle f α hf_lower hf_one⟩

/- accepted add_to_file helper 6 -/
lemma heightEnvInf_le_inv_of_inv {G : Type*} [CommGroup G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1)
    (hf_inv : ∀ α : G, f α⁻¹ = f α) (α : G) :
    heightEnvInf f α⁻¹ ≤ heightEnvInf f α := by
  apply le_csInf (heightEnvInf_nonempty f hf_lower hf_one α)
  rintro r ⟨a, ha, hprod, hsup⟩
  apply csInf_le (heightEnvInf_bddBelow f hf_lower hf_one α⁻¹)
  refine ⟨a⁻¹, ha.inv, ?_, ?_⟩
  · change (∏ᶠ n : ℕ+, (a n)⁻¹) = α⁻¹
    rw [finprod_inv_distrib, hprod]
  · rw [← hsup]
    congr 1
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, by simp [hf_inv]⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, by simp [hf_inv]⟩

lemma heightEnvInf_inv {G : Type*} [CommGroup G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1)
    (hf_inv : ∀ α : G, f α⁻¹ = f α) (α : G) :
    heightEnvInf f α⁻¹ = heightEnvInf f α := by
  apply le_antisymm
  · exact heightEnvInf_le_inv_of_inv f hf_lower hf_one hf_inv α
  · simpa using heightEnvInf_le_inv_of_inv f hf_lower hf_one hf_inv α⁻¹

lemma heightEnvInf_one {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) :
    heightEnvInf f 1 = 1 := by
  apply le_antisymm
  · simpa [hf_one] using heightEnvInf_le_self f hf_lower hf_one (1 : G)
  · exact one_le_heightEnvInf f hf_lower hf_one 1

/- accepted add_to_file helper 7 -/
lemma heightEnvInf_mul {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1)
    (α β : G) :
    heightEnvInf f (α * β) ≤ max (heightEnvInf f α) (heightEnvInf f β) := by
  classical
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨r, ⟨a, ha, hpa, hsa⟩, hrlt⟩ :=
    exists_lt_of_csInf_lt (heightEnvInf_nonempty f hf_lower hf_one α)
      (lt_add_of_pos_right (heightEnvInf f α) hε)
  obtain ⟨s, ⟨b, hb, hpb, hsb⟩, hslt⟩ :=
    exists_lt_of_csInf_lt (heightEnvInf_nonempty f hf_lower hf_one β)
      (lt_add_of_pos_right (heightEnvInf f β) hε)
  let c : ℕ+ → G := fun n ↦ Sum.elim a b (pnatInterleaveEquiv n)
  have hc : Function.HasFiniteMulSupport c := hasFiniteMulSupport_interleave ha hb
  have hprod : (∏ᶠ n, c n) = α * β := by
    rw [finprod_interleave ha hb, hpa, hpb]
  have hsup : sSup (Set.range fun n : ℕ+ ↦ f (c n)) = max r s := by
    rw [← hsa, ← hsb]
    exact sSup_range_interleave ha hb f
  have hupper : heightEnvInf f (α * β) ≤ max r s := by
    apply csInf_le (heightEnvInf_bddBelow f hf_lower hf_one (α * β))
    exact ⟨c, hc, hprod, hsup⟩
  have hlt : max r s < max (heightEnvInf f α) (heightEnvInf f β) + ε := by
    calc
      max r s < max (heightEnvInf f α + ε) (heightEnvInf f β + ε) :=
        max_lt_max hrlt hslt
      _ = max (heightEnvInf f α) (heightEnvInf f β) + ε := max_add_add_right _ _ _
  exact hupper.trans hlt.le

/- accepted add_to_file helper 8 -/
lemma single_le_finset_prod_of_one_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → ℝ) (hg : ∀ i, 1 ≤ g i)
    {i : ι} (hi : i ∈ s) :
    g i ≤ ∏ j ∈ s, g j := by
  have hrest : 1 ≤ ∏ j ∈ s.erase i, g j :=
    Finset.one_le_prod (fun j _ ↦ hg j)
  have hgi0 : 0 ≤ g i := zero_le_one.trans (hg i)
  calc
    g i ≤ g i * ∏ j ∈ s.erase i, g j := le_mul_of_one_le_right hgi0 hrest
    _ = ∏ j ∈ s, g j := Finset.mul_prod_erase s g hi

lemma sSup_range_apply_le_finprod_apply_of_hasFiniteMulSupport {G : Type*} [One G]
    {a : ℕ+ → G} (ha : Function.HasFiniteMulSupport a)
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) :
    sSup (Set.range fun n : ℕ+ ↦ f (a n)) ≤ ∏ᶠ n : ℕ+, f (a n) := by
  classical
  let s := ha.toFinset
  have hsub : Function.mulSupport (fun n : ℕ+ ↦ f (a n)) ⊆ ↑s := by
    intro n hn
    have hnfa : f (a n) ≠ 1 := (Function.mem_mulSupport).1 hn
    by_contra hns
    have hna : a n = 1 := by
      by_contra hna
      exact hns (by
        have : n ∈ ha.toFinset := (ha.mem_toFinset).2 ((Function.mem_mulSupport).2 hna)
        simpa [s] using this)
    exact hnfa (by simp [hna, hf_one])
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨n, rfl⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  by_cases hn : a n = 1
  · change f (a n) ≤ ∏ i ∈ s, f (a i)
    rw [hn, hf_one]
    exact Finset.one_le_prod (fun m _ ↦ hf_lower (a m))
  · have hns : n ∈ s := by
      have : n ∈ ha.toFinset := (ha.mem_toFinset).2 ((Function.mem_mulSupport).2 hn)
      simpa [s] using this
    exact single_le_finset_prod_of_one_le s (fun m ↦ f (a m))
      (fun m ↦ hf_lower (a m)) hns

lemma heightEnvInf_le_heightEnvOne {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    heightEnvInf f α ≤ heightEnvOne f α := by
  apply le_csInf (heightEnvOne_nonempty f hf_lower hf_one α)
  rintro r ⟨a, ha, hprod, hval⟩
  rw [← hval]
  have hInf_le_sup : heightEnvInf f α ≤ sSup (Set.range fun n : ℕ+ ↦ f (a n)) := by
    apply csInf_le (heightEnvInf_bddBelow f hf_lower hf_one α)
    exact ⟨a, ha, hprod, rfl⟩
  exact hInf_le_sup.trans
    (sSup_range_apply_le_finprod_apply_of_hasFiniteMulSupport ha f hf_lower hf_one)

/- accepted add_to_file helper 9 -/
lemma strong_apply_finprod_le_sSup_range_apply {G : Type*} [CommMonoid G]
    {a : ℕ+ → G} (ha : Function.HasFiniteMulSupport a)
    (σ : G → ℝ) (hσ_lower : ∀ α : G, 1 ≤ σ α) (hσ_one : σ 1 = 1)
    (hσ_mul : ∀ α β : G, σ (α * β) ≤ max (σ α) (σ β)) :
    σ (∏ᶠ n : ℕ+, a n) ≤ sSup (Set.range fun n : ℕ+ ↦ σ (a n)) := by
  classical
  let s := ha.toFinset
  have hsub : Function.mulSupport a ⊆ ↑s := by
    intro n hn
    have : n ∈ ha.toFinset := (ha.mem_toFinset).2 hn
    simpa [s] using this
  rw [finprod_eq_prod_of_mulSupport_subset a hsub]
  have hbdd : BddAbove (Set.range fun n : ℕ+ ↦ σ (a n)) :=
    bddAbove_range_apply_of_hasFiniteMulSupport ha σ
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty]
      obtain ⟨n, hn⟩ := ha.exists_notMem
      have han : a n = 1 := by
        by_contra h
        exact hn ((Function.mem_mulSupport).2 h)
      exact le_csSup hbdd ⟨n, by simp [han]⟩
  | insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (hσ_mul (a i) (∏ x ∈ s, a x)).trans
        (max_le (le_csSup hbdd ⟨i, rfl⟩) ih)

lemma sSup_range_mono {G : Type*} [One G]
    {a : ℕ+ → G} (ha : Function.HasFiniteMulSupport a)
    {σ f : G → ℝ} (hσf : ∀ α : G, σ α ≤ f α) :
    sSup (Set.range fun n : ℕ+ ↦ σ (a n)) ≤
      sSup (Set.range fun n : ℕ+ ↦ f (a n)) := by
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨n, rfl⟩
  exact (hσf (a n)).trans
    (le_csSup (bddAbove_range_apply_of_hasFiniteMulSupport ha f) ⟨n, rfl⟩)

lemma strong_le_heightEnvInf {G : Type*} [CommMonoid G]
    (σ f : G → ℝ)
    (hσ_lower : ∀ α : G, 1 ≤ σ α) (hσ_one : σ 1 = 1)
    (hσ_mul : ∀ α β : G, σ (α * β) ≤ max (σ α) (σ β))
    (hσf : ∀ α : G, σ α ≤ f α)
    (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    σ α ≤ heightEnvInf f α := by
  apply le_csInf (heightEnvInf_nonempty f hf_lower hf_one α)
  rintro r ⟨a, ha, hprod, hsup⟩
  rw [← hsup]
  calc
    σ α = σ (∏ᶠ n : ℕ+, a n) := by rw [hprod]
    _ ≤ sSup (Set.range fun n : ℕ+ ↦ σ (a n)) :=
      strong_apply_finprod_le_sSup_range_apply ha σ hσ_lower hσ_one hσ_mul
    _ ≤ sSup (Set.range fun n : ℕ+ ↦ f (a n)) := sSup_range_mono ha hσf

/- accepted add_to_file helper 10 -/
lemma heightEnvOne_le_self {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    heightEnvOne f α ≤ f α := by
  classical
  apply csInf_le (heightEnvOne_bddBelow f hf_lower hf_one α)
  refine ⟨pnatSingle α, hasFiniteMulSupport_pnatSingle α, finprod_pnatSingle α, ?_⟩
  have hsub : Function.mulSupport (fun n : ℕ+ ↦ f (pnatSingle α n)) ⊆
      ↑({1} : Finset ℕ+) := by
    intro n hn
    by_cases h : n = 1
    · simpa [h]
    · exfalso
      exact (Function.mem_mulSupport).1 hn (by simp [pnatSingle, h, hf_one])
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  simp [pnatSingle]

lemma one_le_heightEnvOne {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    1 ≤ heightEnvOne f α := by
  apply le_csInf (heightEnvOne_nonempty f hf_lower hf_one α)
  rintro r ⟨a, ha, -, hprod⟩
  rw [← hprod]
  exact one_le_finprod_apply_of_hasFiniteMulSupport ha f hf_lower hf_one

lemma heightEnvOne_one {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) :
    heightEnvOne f 1 = 1 := by
  apply le_antisymm
  · simpa [hf_one] using heightEnvOne_le_self f hf_lower hf_one (1 : G)
  · exact one_le_heightEnvOne f hf_lower hf_one 1

lemma heightEnvInf_eq_self_of_strong {G : Type*} [CommMonoid G]
    (f : G → ℝ)
    (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1)
    (hf_mul : ∀ α β : G, f (α * β) ≤ max (f α) (f β)) :
    heightEnvInf f = f := by
  funext α
  apply le_antisymm
  · exact heightEnvInf_le_self f hf_lower hf_one α
  · exact strong_le_heightEnvInf f f hf_lower hf_one hf_mul
      (fun β ↦ le_rfl) hf_lower hf_one α

lemma heightEnvOne_eq_self_of_strong {G : Type*} [CommMonoid G]
    (f : G → ℝ)
    (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1)
    (hf_mul : ∀ α β : G, f (α * β) ≤ max (f α) (f β)) :
    heightEnvOne f = f := by
  funext α
  apply le_antisymm
  · exact heightEnvOne_le_self f hf_lower hf_one α
  · calc
      f α = heightEnvInf f α := by
        rw [heightEnvInf_eq_self_of_strong f hf_lower hf_one hf_mul]
      _ ≤ heightEnvOne f α := heightEnvInf_le_heightEnvOne f hf_lower hf_one α

lemma heightEnvInf_mono {G : Type*} [CommMonoid G]
    {f g : G → ℝ}
    (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1)
    (hg_lower : ∀ α : G, 1 ≤ g α) (hg_one : g 1 = 1)
    (hfg : ∀ α : G, f α ≤ g α) (α : G) :
    heightEnvInf f α ≤ heightEnvInf g α := by
  apply le_csInf (heightEnvInf_nonempty g hg_lower hg_one α)
  rintro r ⟨a, ha, hprod, hsup⟩
  rw [← hsup]
  have hleft : heightEnvInf f α ≤ sSup (Set.range fun n : ℕ+ ↦ f (a n)) := by
    apply csInf_le (heightEnvInf_bddBelow f hf_lower hf_one α)
    exact ⟨a, ha, hprod, rfl⟩
  exact hleft.trans (sSup_range_mono ha hfg)

lemma heightEnvInf_heightEnvOne_eq_heightEnvInf {G : Type*} [CommMonoid G]
    (f : G → ℝ)
    (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) :
    heightEnvInf f = heightEnvInf (heightEnvOne f) := by
  funext α
  apply le_antisymm
  · exact strong_le_heightEnvInf (heightEnvInf f) (heightEnvOne f)
      (one_le_heightEnvInf f hf_lower hf_one)
      (heightEnvInf_one f hf_lower hf_one)
      (heightEnvInf_mul f hf_lower hf_one)
      (heightEnvInf_le_heightEnvOne f hf_lower hf_one)
      (one_le_heightEnvOne f hf_lower hf_one)
      (heightEnvOne_one f hf_lower hf_one)
      α
  · exact heightEnvInf_mono
      (one_le_heightEnvOne f hf_lower hf_one)
      (heightEnvOne_one f hf_lower hf_one)
      hf_lower hf_one
      (heightEnvOne_le_self f hf_lower hf_one) α

/- verified submission -/
theorem strongMetricEnvelopeOfHeight
    {G : Type*} [CommGroup G] (ρ : G → ℝ)
    (hρ_lower : ∀ α : G, 1 ≤ ρ α)
    (hρ_one : ρ 1 = 1)
    (hρ_inv : ∀ α : G, ρ α⁻¹ = ρ α) :
    let envelopeOne : (G → ℝ) → G → ℝ := fun f α ↦
      sInf {r : ℝ | ∃ a : ℕ+ → G,
        Function.HasFiniteMulSupport a ∧
        (∏ᶠ n, a n) = α ∧
        (∏ᶠ n, f (a n)) = r}
    let envelopeInf : (G → ℝ) → G → ℝ := fun f α ↦
      sInf {r : ℝ | ∃ a : ℕ+ → G,
        Function.HasFiniteMulSupport a ∧
        (∏ᶠ n, a n) = α ∧
        sSup (Set.range fun n : ℕ+ ↦ f (a n)) = r}
    ((∀ α : G, 1 ≤ envelopeInf ρ α) ∧
      envelopeInf ρ 1 = 1 ∧
      (∀ α : G, envelopeInf ρ α⁻¹ = envelopeInf ρ α) ∧
      (∀ α β : G,
        envelopeInf ρ (α * β) ≤ max (envelopeInf ρ α) (envelopeInf ρ β))) ∧
    (∀ α : G, envelopeInf ρ α ≤ envelopeOne ρ α) ∧
    (∀ σ : G → ℝ,
      ((∀ α : G, 1 ≤ σ α) ∧
        σ 1 = 1 ∧
        (∀ α : G, σ α⁻¹ = σ α) ∧
        (∀ α β : G, σ (α * β) ≤ max (σ α) (σ β))) →
      (∀ α : G, σ α ≤ ρ α) →
      ∀ α : G, σ α ≤ envelopeInf ρ α) ∧
    (ρ = envelopeInf ρ ↔
      (∀ α : G, 1 ≤ ρ α) ∧
      ρ 1 = 1 ∧
      (∀ α : G, ρ α⁻¹ = ρ α) ∧
      (∀ α β : G, ρ (α * β) ≤ max (ρ α) (ρ β))) ∧
    (envelopeInf ρ = envelopeInf (envelopeOne ρ) ∧
      envelopeInf (envelopeOne ρ) = envelopeOne (envelopeInf ρ) ∧
      envelopeOne (envelopeInf ρ) = envelopeInf (envelopeInf ρ)) := by
  refine ⟨⟨one_le_heightEnvInf ρ hρ_lower hρ_one,
    heightEnvInf_one ρ hρ_lower hρ_one,
    heightEnvInf_inv ρ hρ_lower hρ_one hρ_inv,
    heightEnvInf_mul ρ hρ_lower hρ_one⟩,
    heightEnvInf_le_heightEnvOne ρ hρ_lower hρ_one,
    ?_, ?_, ?_⟩
  · intro σ hσ hσρ α
    rcases hσ with ⟨hσ_lower, hσ_one, -, hσ_mul⟩
    exact strong_le_heightEnvInf σ ρ hσ_lower hσ_one hσ_mul hσρ
      hρ_lower hρ_one α
  · constructor
    · intro h
      refine ⟨hρ_lower, hρ_one, hρ_inv, ?_⟩
      intro α β
      rw [h]
      exact heightEnvInf_mul ρ hρ_lower hρ_one α β
    · rintro ⟨hρ_lower', hρ_one', -, hρ_mul⟩
      exact (heightEnvInf_eq_self_of_strong ρ hρ_lower' hρ_one' hρ_mul).symm
  · refine ⟨heightEnvInf_heightEnvOne_eq_heightEnvInf ρ hρ_lower hρ_one, ?_, ?_⟩
    · have h₁ := heightEnvInf_heightEnvOne_eq_heightEnvInf ρ hρ_lower hρ_one
      have h₂ := heightEnvOne_eq_self_of_strong (heightEnvInf ρ)
        (one_le_heightEnvInf ρ hρ_lower hρ_one)
        (heightEnvInf_one ρ hρ_lower hρ_one)
        (heightEnvInf_mul ρ hρ_lower hρ_one)
      exact h₁.symm.trans h₂.symm
    · have h₁ := heightEnvOne_eq_self_of_strong (heightEnvInf ρ)
        (one_le_heightEnvInf ρ hρ_lower hρ_one)
        (heightEnvInf_one ρ hρ_lower hρ_one)
        (heightEnvInf_mul ρ hρ_lower hρ_one)
      have h₂ := heightEnvInf_eq_self_of_strong (heightEnvInf ρ)
        (one_le_heightEnvInf ρ hρ_lower hρ_one)
        (heightEnvInf_one ρ hρ_lower hρ_one)
        (heightEnvInf_mul ρ hρ_lower hρ_one)
      exact h₁.trans h₂.symm


#check_dependency_graph "strongMetricEnvelopeOfHeight" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"((∀ (α : G), 1 ≤ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ α) ∧ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ 1 = 1 ∧ (∀ (α : G), (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ α⁻¹ = (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ α) ∧ ∀ (α β : G), (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ (α * β) ≤ max ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ α) ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ β)) ∧ (∀ (α : G), (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ α ≤ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ ∏ᶠ (n : ℕ+), f (a n) = r}) ρ α) ∧ (∀ (σ : G → ℝ), ((∀ (α : G), 1 ≤ σ α) ∧ σ 1 = 1 ∧ (∀ (α : G), σ α⁻¹ = σ α) ∧ ∀ (α β : G), σ (α * β) ≤ max (σ α) (σ β)) → (∀ (α : G), σ α ≤ ρ α) → ∀ (α : G), σ α ≤ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ α) ∧ (ρ = (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ ↔ (∀ (α : G), 1 ≤ ρ α) ∧ ρ 1 = 1 ∧ (∀ (α : G), ρ α⁻¹ = ρ α) ∧ ∀ (α β : G), ρ (α * β) ≤ max (ρ α) (ρ β)) ∧ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ = (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ ∏ᶠ (n : ℕ+), f (a n) = r}) ρ) ∧ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ ∏ᶠ (n : ℕ+), f (a n) = r}) ρ) = (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ ∏ᶠ (n : ℕ+), f (a n) = r}) ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ) ∧ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ ∏ᶠ (n : ℕ+), f (a n) = r}) ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ) = (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hρ_lower\",\"statement\":\"∀ (α : G), 1 ≤ ρ α\"},{\"name\":\"hρ_one\",\"statement\":\"ρ 1 = 1\"},{\"name\":\"hρ_inv\",\"statement\":\"∀ (α : G), ρ α⁻¹ = ρ α\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2227_strongmetricenvelopeofheight\",\"reconstructedProofSha256\":\"964d5827dbfe76c5223cd0228076320fa62b8063e8b6c94499060e9ec639c56f\",\"selectedEdgeCount\":1,\"theoremName\":\"strongMetricEnvelopeOfHeight\",\"topologySha256\":\"0c7a7e1ae1d7e6f1a427f32a3d41f791bd3bd2dbc65bf4ed5fae4de7739626f6\"}"
