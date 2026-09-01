import Mathlib

/- accepted add_to_file helper 1 -/
noncomputable def treeHeight (τ : Finset (List ℕ)) : ℕ := τ.sup List.length

lemma treeHeight_le {τ : Finset (List ℕ)} {v : List ℕ} (hv : v ∈ τ) :
    v.length ≤ treeHeight τ := by
  exact Finset.le_sup (f := List.length) hv

def subtree (τ : Finset (List ℕ)) (v : List ℕ) : Finset (List ℕ) :=
  τ.filter (fun x => v <+: x)

lemma subtree_eq_insert_biUnion
    (τ : Finset (List ℕ)) (k : List ℕ → ℕ)
    (hprefix : ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    {v : List ℕ} (hv : v ∈ τ) :
    subtree τ v =
      insert v ((Finset.Icc 1 (k v)).biUnion (fun m => subtree τ (v ++ [m]))) := by
  ext x
  constructor
  · intro hx
    have hxτ : x ∈ τ := (Finset.mem_filter.mp hx).1
    have hpre : v <+: x := (Finset.mem_filter.mp hx).2
    rcases hpre with ⟨t, rfl⟩
    cases t with
    | nil =>
        simp
    | cons a rest =>
        have hprefix_child : v ++ [a] <+: v ++ (a :: rest) := by
          refine ⟨rest, ?_⟩
          simp [List.append_assoc]
        have hchildmem : v ++ [a] ∈ τ := hprefix hxτ hprefix_child
        have ha : 1 ≤ a ∧ a ≤ k v := (hchildren v hv a).mp hchildmem
        simp [subtree, Finset.mem_biUnion, ha, hxτ]
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_Icc] at hx
    rcases hx with rfl | ⟨m, hm, hmsub⟩
    · simp [subtree, hv]
    · have hmpre : v <+: v ++ [m] := by
        refine ⟨[m], ?_⟩
        simp
      have hxpre : v ++ [m] <+: x := (Finset.mem_filter.mp hmsub).2
      have hxτ : x ∈ τ := (Finset.mem_filter.mp hmsub).1
      exact Finset.mem_filter.mpr ⟨hxτ, hmpre.trans hxpre⟩

/- accepted add_to_file helper 2 -/
lemma subtree_children_disjoint
    (τ : Finset (List ℕ)) (k : List ℕ → ℕ) (v : List ℕ) :
    (↑(Finset.Icc 1 (k v)) : Set ℕ).PairwiseDisjoint
      (fun m => subtree τ (v ++ [m])) := by
  intro a ha b hb hne
  rw [Function.onFun]
  apply Finset.disjoint_left.mpr
  intro x hxa hxb
  have hpa : v ++ [a] <+: x := (Finset.mem_filter.mp hxa).2
  have hpb : v ++ [b] <+: x := (Finset.mem_filter.mp hxb).2
  have hcomp := List.prefix_or_prefix_of_prefix hpa hpb
  have hlen : (v ++ [a]).length = (v ++ [b]).length := by simp
  have hchild : v ++ [a] = v ++ [b] := by
    rcases hcomp with hp | hp
    · exact hp.eq_of_length hlen
    · exact (hp.eq_of_length hlen.symm).symm
  have hsingle : [a] = [b] := List.append_right_injective v hchild
  have hab : a = b := by simpa using hsingle
  exact hne hab

lemma subtree_parent_not_mem_children_biUnion
    (τ : Finset (List ℕ)) (k : List ℕ → ℕ) (v : List ℕ) :
    v ∉ (Finset.Icc 1 (k v)).biUnion (fun m => subtree τ (v ++ [m])) := by
  intro hv
  simp only [Finset.mem_biUnion, Finset.mem_Icc] at hv
  rcases hv with ⟨m, hm, hmsub⟩
  have hpre : v ++ [m] <+: v := (Finset.mem_filter.mp hmsub).2
  have hlen := hpre.length_le
  simp at hlen

lemma subtree_sum_rec
    (τ : Finset (List ℕ)) (k : List ℕ → ℕ)
    (hprefix : ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    {v : List ℕ} (hv : v ∈ τ)
    (ih : ∀ m : ℕ, 1 ≤ m → m ≤ k v →
      (∑ x ∈ subtree τ (v ++ [m]), ((k x : ℤ) - 1)) = -1) :
    (∑ x ∈ subtree τ v, ((k x : ℤ) - 1)) = -1 := by
  rw [subtree_eq_insert_biUnion τ k hprefix hchildren hv]
  rw [Finset.sum_insert (subtree_parent_not_mem_children_biUnion τ k v)]
  rw [Finset.sum_biUnion (subtree_children_disjoint τ k v)]
  have hsum : (∑ m ∈ Finset.Icc 1 (k v),
      ∑ x ∈ subtree τ (v ++ [m]), ((k x : ℤ) - 1)) =
      ∑ m ∈ Finset.Icc 1 (k v), (-1 : ℤ) := by
    apply Finset.sum_congr rfl
    intro m hm
    have hm' : 1 ≤ m ∧ m ≤ k v := Finset.mem_Icc.mp hm
    exact ih m hm'.1 hm'.2
  rw [hsum]
  simp
  ring

/- accepted add_to_file helper 3 -/
lemma subtree_weight_sum_gap
    (τ : Finset (List ℕ)) (k : List ℕ → ℕ)
    (hprefix : ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v) :
    ∀ n : ℕ, ∀ {v : List ℕ}, v ∈ τ → treeHeight τ - v.length ≤ n →
      (∑ x ∈ subtree τ v, ((k x : ℤ) - 1)) = -1 := by
  intro n
  induction n with
  | zero =>
      intro v hv hgap
      have hk : k v = 0 := by
        by_contra hne
        have hpos : 0 < k v := Nat.pos_of_ne_zero hne
        have hchild : v ++ [1] ∈ τ := (hchildren v hv 1).mpr ⟨le_rfl, hpos⟩
        have hlechild := treeHeight_le hchild
        have hle : treeHeight τ ≤ v.length := by
          have hzero : treeHeight τ - v.length = 0 := Nat.le_zero.mp hgap
          exact (Nat.sub_eq_zero_iff_le).mp hzero
        have hlen : (v ++ [1]).length = v.length + 1 := by simp
        omega
      exact subtree_sum_rec τ k hprefix hchildren hv (by
        intro m hm1 hmk
        omega)
  | succ n ihn =>
      intro v hv hgap
      exact subtree_sum_rec τ k hprefix hchildren hv (by
        intro m hm1 hmk
        have hchild : v ++ [m] ∈ τ := (hchildren v hv m).mpr ⟨hm1, hmk⟩
        have hlechild := treeHeight_le hchild
        have hlen : (v ++ [m]).length = v.length + 1 := by simp
        apply ihn hchild
        omega)

lemma subtree_weight_sum
    (τ : Finset (List ℕ)) (k : List ℕ → ℕ)
    (hprefix : ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    {v : List ℕ} (hv : v ∈ τ) :
    (∑ x ∈ subtree τ v, ((k x : ℤ) - 1)) = -1 := by
  exact subtree_weight_sum_gap τ k hprefix hchildren
    (treeHeight τ - v.length) hv le_rfl

/- accepted add_to_file helper 4 -/
def finPred {N : ℕ} (j : Fin N) (hj : 0 < j.val) : Fin N :=
  ⟨j.val - 1, by
    have hN := j.isLt
    omega⟩

lemma finPred_succ_eq_castSucc {N : ℕ} (j : Fin N) (hj : 0 < j.val) :
    (finPred j hj).succ = j.castSucc := by
  apply Fin.ext
  simp [finPred]
  omega

lemma mem_Icc_finPred_iff {N : ℕ} {i r j : Fin N} (hj : 0 < j.val) :
    r ∈ Finset.Icc i (finPred j hj) ↔ i ≤ r ∧ r < j := by
  simp [finPred]
  intro hir
  show r.val ≤ j.val - 1 ↔ r.val < j.val
  omega

/- accepted add_to_file helper 5 -/
lemma W_diff_eq_sum_interval
    {N : ℕ} {τ : Finset (List ℕ)} {k : List ℕ → ℕ}
    {u : Fin N ≃ {v : List ℕ // v ∈ τ}}
    {W : Fin (N + 1) → ℤ}
    (hWstep : ∀ r : Fin N,
      W r.succ = W r.castSucc + (k (u r).1 : ℤ) - 1)
    {i j : Fin N} (hij : i < j) (hj : 0 < j.val) :
    W j.castSucc - W i.castSucc =
      ∑ r ∈ Finset.Icc i (finPred j hj),
        ((k (u r).1 : ℤ) - 1) := by
  have hle : i ≤ finPred j hj := by
    change i.val ≤ (finPred j hj).val
    simp [finPred]
    have : i.val < j.val := hij
    omega
  have htel := Fin.sum_Icc_sub hle W
  calc
    W j.castSucc - W i.castSucc
        = ∑ r ∈ Finset.Icc i (finPred j hj), (W r.succ - W r.castSucc) := by
            rw [htel, finPred_succ_eq_castSucc]
    _ = ∑ r ∈ Finset.Icc i (finPred j hj),
          ((k (u r).1 : ℤ) - 1) := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [hWstep r]
            ring

/- accepted add_to_file helper 6 -/
lemma lex_sandwich_prefix :
    ∀ {a c x : List ℕ}, a <+: c →
      List.Lex (fun p q : ℕ => p < q) a x →
      List.Lex (fun p q : ℕ => p < q) x c → a <+: x := by
  intro a
  induction a with
  | nil =>
      intro c x hac hax hxc
      exact List.nil_prefix
  | cons a as ih =>
      intro c x hac hax hxc
      rcases hac with ⟨t, rfl⟩
      cases x with
      | nil =>
          cases hax
      | cons b bs =>
          cases hax with
          | rel hab =>
              cases hxc with
              | rel hba => omega
              | cons htail => omega
          | cons htail =>
              have htailxc : List.Lex (fun p q : ℕ => p < q) bs (as ++ t) := by
                cases hxc with
                | rel hba => omega
                | cons h => exact h
              have hprefix_as : as <+: as ++ t := by
                refine ⟨t, rfl⟩
              have hp := ih (c := as ++ t) (x := bs) hprefix_as htail htailxc
              rcases hp with ⟨s, hs⟩
              refine ⟨s, ?_⟩
              simpa using congrArg (fun z => a :: z) hs

lemma lex_append_left_cancel {s x y : List ℕ} :
    List.Lex (fun a b : ℕ => a < b) (s ++ x) (s ++ y) →
    List.Lex (fun a b : ℕ => a < b) x y := by
  induction s generalizing x y with
  | nil =>
      intro h
      exact h
  | cons a s ih =>
      intro h
      have h' : List.Lex (fun p q : ℕ => p < q)
          (a :: (s ++ x)) (a :: (s ++ y)) := by
        simpa using h
      cases h' with
      | rel hrel => omega
      | cons htail => exact ih htail

lemma lex_append_left_iff (s x y : List ℕ) :
    List.Lex (fun a b : ℕ => a < b) (s ++ x) (s ++ y) ↔
      List.Lex (fun a b : ℕ => a < b) x y := by
  constructor
  · exact lex_append_left_cancel
  · intro h
    exact List.Lex.append_left _ h s

lemma lex_interval_image
    {N : ℕ} {τ : Finset (List ℕ)}
    {u : Fin N ≃ {v : List ℕ // v ∈ τ}}
    (hlex : ∀ a b : Fin N, a < b ↔
      List.Lex (fun x y : ℕ => x < y) (u a).1 (u b).1)
    {i j : Fin N} (hj : 0 < j.val) :
    (Finset.Icc i (finPred j hj)).image (fun r => (u r).1) =
      τ.filter (fun x =>
        (x = (u i).1 ∨ List.Lex (fun a b : ℕ => a < b) (u i).1 x) ∧
        List.Lex (fun a b : ℕ => a < b) x (u j).1) := by
  ext x
  constructor
  · intro hx
    simp only [Finset.mem_image] at hx
    rcases hx with ⟨r, hr, rfl⟩
    have hrb := (mem_Icc_finPred_iff (i := i) (r := r) (j := j) hj).mp hr
    have hlower : (u r).1 = (u i).1 ∨
        List.Lex (fun a b : ℕ => a < b) (u i).1 (u r).1 := by
      rcases eq_or_lt_of_le hrb.1 with heq | hlt
      · left
        rw [heq]
      · right
        exact (hlex i r).mp hlt
    have hupper : List.Lex (fun a b : ℕ => a < b) (u r).1 (u j).1 :=
      (hlex r j).mp hrb.2
    exact Finset.mem_filter.mpr ⟨(u r).2, ⟨hlower, hupper⟩⟩
  · intro hx
    have hxτ : x ∈ τ := (Finset.mem_filter.mp hx).1
    have hbounds := (Finset.mem_filter.mp hx).2
    let r : Fin N := u.symm ⟨x, hxτ⟩
    have hur : u r = ⟨x, hxτ⟩ := Equiv.apply_symm_apply u ⟨x, hxτ⟩
    have hurl : (u r).1 = x := congrArg Subtype.val hur
    have hir : i ≤ r := by
      rcases hbounds.1 with heq | hlt
      · have hsub : u i = ⟨x, hxτ⟩ := by
          apply Subtype.ext
          exact heq.symm
        have hfi : i = r := by
          apply u.injective
          rw [hsub, hur]
        rw [hfi]
      · have hlt' : i < r := by
          apply (hlex i r).mpr
          rw [hurl]
          exact hlt
        exact le_of_lt hlt'
    have hrj : r < j := by
      apply (hlex r j).mpr
      rw [hurl]
      exact hbounds.2
    refine Finset.mem_image.mpr ⟨r, ?_, ?_⟩
    · exact (mem_Icc_finPred_iff (i := i) (r := r) (j := j) hj).mpr ⟨hir, hrj⟩
    · exact hurl

/- accepted add_to_file helper 7 -/
lemma lex_interval_parent_child
    (τ : Finset (List ℕ)) (k : List ℕ → ℕ)
    (hprefix : ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    {a : List ℕ} (ha : a ∈ τ) {m : ℕ} (hm : 1 ≤ m ∧ m ≤ k a) :
    τ.filter (fun x =>
        (x = a ∨ List.Lex (fun p q : ℕ => p < q) a x) ∧
        List.Lex (fun p q : ℕ => p < q) x (a ++ [m])) =
      insert a ((Finset.Icc 1 (m - 1)).biUnion
        (fun q => subtree τ (a ++ [q]))) := by
  ext x
  constructor
  · intro hx
    have hxτ : x ∈ τ := (Finset.mem_filter.mp hx).1
    have hb := (Finset.mem_filter.mp hx).2
    rcases hb.1 with heq | hlower
    · simp [heq]
    · have hac : a <+: a ++ [m] := by
        refine ⟨[m], ?_⟩
        simp
      have hpre : a <+: x := lex_sandwich_prefix hac hlower hb.2
      rcases hpre with ⟨t, rfl⟩
      cases t with
      | nil =>
          have haa : List.Lex (fun p q : ℕ => p < q) a a := by
            simpa using hlower
          exact (List.lex_irrefl (fun n : ℕ => lt_irrefl n) a haa).elim
      | cons q rest =>
          have hprefix_child : a ++ [q] <+: a ++ (q :: rest) := by
            refine ⟨rest, ?_⟩
            simp [List.append_assoc]
          have hchildτ : a ++ [q] ∈ τ := hprefix hxτ hprefix_child
          have hqvalid : 1 ≤ q ∧ q ≤ k a := (hchildren a ha q).mp hchildτ
          have hqlex : List.Lex (fun p q : ℕ => p < q) (q :: rest) [m] := by
            apply lex_append_left_cancel
            simpa using hb.2
          have hqm : q < m := by
            cases hqlex with
            | rel h => exact h
            | cons h => cases h
          have hqle : q ≤ m - 1 := by omega
          simp [subtree, Finset.mem_biUnion, hqvalid, hqle, hxτ]
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_Icc] at hx
    rcases hx with heq | ⟨q, hq, hsub⟩
    · rw [heq]
      have hbase : List.Lex (fun p q : ℕ => p < q) [] [m] := List.Lex.nil
      have hupper := List.Lex.append_left _ hbase a
      exact Finset.mem_filter.mpr ⟨ha, ⟨Or.inl rfl, by simpa using hupper⟩⟩
    · have hxτ : x ∈ τ := (Finset.mem_filter.mp hsub).1
      have hchildpre : a ++ [q] <+: x := (Finset.mem_filter.mp hsub).2
      have hqm : q < m := by omega
      have hlower : List.Lex (fun p q : ℕ => p < q) a x := by
        rcases hchildpre with ⟨rest, rfl⟩
        have hbase : List.Lex (fun p q : ℕ => p < q) [] (q :: rest) := List.Lex.nil
        have hlex := List.Lex.append_left _ hbase a
        simpa [List.append_assoc] using hlex
      have hupper : List.Lex (fun p q : ℕ => p < q) x (a ++ [m]) := by
        rcases hchildpre with ⟨rest, rfl⟩
        have htail : List.Lex (fun p q : ℕ => p < q) (q :: rest) [m] :=
          List.Lex.rel hqm
        have hlex := List.Lex.append_left _ htail a
        simpa [List.append_assoc] using hlex
      exact Finset.mem_filter.mpr ⟨hxτ, ⟨Or.inr hlower, hupper⟩⟩

/- accepted add_to_file helper 8 -/
lemma lex_interval_parent_child_weight_sum
    (τ : Finset (List ℕ)) (k : List ℕ → ℕ)
    (hprefix : ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    {a : List ℕ} (ha : a ∈ τ) {m : ℕ} (hm : 1 ≤ m ∧ m ≤ k a) :
    (∑ x ∈ τ.filter (fun x =>
        (x = a ∨ List.Lex (fun p q : ℕ => p < q) a x) ∧
        List.Lex (fun p q : ℕ => p < q) x (a ++ [m])),
      ((k x : ℤ) - 1)) = (k a : ℤ) - m := by
  rw [lex_interval_parent_child τ k hprefix hchildren ha hm]
  have hnotmem : a ∉ (Finset.Icc 1 (m - 1)).biUnion
      (fun q => subtree τ (a ++ [q])) := by
    intro hmem
    have hbig : a ∈ (Finset.Icc 1 (k a)).biUnion
        (fun q => subtree τ (a ++ [q])) := by
      simp only [Finset.mem_biUnion, Finset.mem_Icc] at hmem ⊢
      rcases hmem with ⟨q, hq, hsub⟩
      exact ⟨q, ⟨hq.1, by omega⟩, hsub⟩
    exact subtree_parent_not_mem_children_biUnion τ k a hbig
  have hsub : (↑(Finset.Icc 1 (m - 1)) : Set ℕ) ⊆
      (↑(Finset.Icc 1 (k a)) : Set ℕ) := by
    intro q hq
    simp only [Finset.mem_coe, Finset.mem_Icc] at hq ⊢
    omega
  have hdisj := Set.Pairwise.mono hsub (subtree_children_disjoint τ k a)
  rw [Finset.sum_insert hnotmem]
  rw [Finset.sum_biUnion hdisj]
  have hsum : (∑ q ∈ Finset.Icc 1 (m - 1),
      ∑ x ∈ subtree τ (a ++ [q]), ((k x : ℤ) - 1)) =
      ∑ q ∈ Finset.Icc 1 (m - 1), (-1 : ℤ) := by
    apply Finset.sum_congr rfl
    intro q hq
    have hq' : 1 ≤ q ∧ q ≤ m - 1 := Finset.mem_Icc.mp hq
    have hqle : q ≤ k a := by omega
    have hchild : a ++ [q] ∈ τ := (hchildren a ha q).mpr ⟨hq'.1, hqle⟩
    exact subtree_weight_sum τ k hprefix hchildren hchild
  rw [hsum]
  simp
  have hmcast : (((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1) := by omega
  rw [hmcast]
  ring

/- accepted add_to_file helper 9 -/
lemma W_parent_child_gap
    {N : ℕ} {τ : Finset (List ℕ)} {k : List ℕ → ℕ}
    (hprefix : ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    {u : Fin N ≃ {v : List ℕ // v ∈ τ}}
    (hlex : ∀ a b : Fin N, a < b ↔
      List.Lex (fun x y : ℕ => x < y) (u a).1 (u b).1)
    {W : Fin (N + 1) → ℤ}
    (hWstep : ∀ r : Fin N,
      W r.succ = W r.castSucc + (k (u r).1 : ℤ) - 1)
    {i t : Fin N} (hit : i < t) {m : ℕ}
    (ht : (u t).1 = (u i).1 ++ [m]) :
    W t.castSucc - W i.castSucc = (k (u i).1 : ℤ) - m := by
  have htval : 0 < t.val := by
    have : i.val < t.val := hit
    omega
  have hchildτ : (u i).1 ++ [m] ∈ τ := by
    rw [← ht]
    exact (u t).2
  have hm : 1 ≤ m ∧ m ≤ k (u i).1 :=
    (hchildren (u i).1 (u i).2 m).mp hchildτ
  let s := Finset.Icc i (finPred t htval)
  have hW := W_diff_eq_sum_interval (u := u) hWstep hit htval
  have himage := lex_interval_image (u := u) hlex (i := i) (j := t) htval
  have hinj : Set.InjOn (fun r : Fin N => (u r).1) (↑s : Set (Fin N)) := by
    intro a ha b hb h
    apply u.injective
    apply Subtype.ext
    exact h
  calc
    W t.castSucc - W i.castSucc
        = ∑ r ∈ s, ((k (u r).1 : ℤ) - 1) := hW
    _ = ∑ x ∈ s.image (fun r : Fin N => (u r).1), ((k x : ℤ) - 1) := by
          exact (Finset.sum_image (s := s) (g := fun r : Fin N => (u r).1)
            (f := fun x : List ℕ => (k x : ℤ) - 1) hinj).symm
    _ = ∑ x ∈ τ.filter (fun x =>
          (x = (u i).1 ∨ List.Lex (fun a b : ℕ => a < b) (u i).1 x) ∧
          List.Lex (fun a b : ℕ => a < b) x (u t).1),
          ((k x : ℤ) - 1) := by
          rw [← himage]
    _ = (k (u i).1 : ℤ) - m := by
          rw [ht]
          exact lex_interval_parent_child_weight_sum τ k hprefix hchildren (u i).2 hm

/- accepted add_to_file helper 10 -/
def loopGraph (τ : Finset (List ℕ)) (k : List ℕ → ℕ) :
    SimpleGraph {v : List ℕ // v ∈ τ} :=
  SimpleGraph.fromRel fun x y =>
    (∃ (p : List ℕ) (m : ℕ), p ∈ τ ∧ 1 ≤ m ∧ m < k p ∧
      x.1 = p ++ [m] ∧ y.1 = p ++ [m + 1]) ∨
    (0 < k x.1 ∧ (y.1 = x.1 ++ [1] ∨ y.1 = x.1 ++ [k x.1]))

/- accepted add_to_file helper 11 -/
lemma loop_adj_parent_last
    (τ : Finset (List ℕ)) (k : List ℕ → ℕ)
    {p : List ℕ} (hp : p ∈ τ) (hkp : 0 < k p)
    (hchild : p ++ [k p] ∈ τ) :
    (loopGraph τ k).Adj ⟨p, hp⟩ ⟨p ++ [k p], hchild⟩ := by
  rw [loopGraph, SimpleGraph.fromRel_adj]
  constructor
  · intro h
    have hval : p = p ++ [k p] := congrArg Subtype.val h
    have hlen := congrArg List.length hval
    simp at hlen
  · left
    right
    exact ⟨hkp, Or.inr rfl⟩

lemma loop_adj_sibling
    (τ : Finset (List ℕ)) (k : List ℕ → ℕ)
    {p : List ℕ} (hp : p ∈ τ) {m : ℕ}
    (hm1 : 1 ≤ m) (hmk : m < k p)
    (hmchild : p ++ [m] ∈ τ) (hnextchild : p ++ [m + 1] ∈ τ) :
    (loopGraph τ k).Adj ⟨p ++ [m], hmchild⟩ ⟨p ++ [m + 1], hnextchild⟩ := by
  rw [loopGraph, SimpleGraph.fromRel_adj]
  constructor
  · intro h
    have hval : p ++ [m] = p ++ [m + 1] := congrArg Subtype.val h
    have hsingle : [m] = [m + 1] := List.append_right_injective p hval
    have : m = m + 1 := by simpa using hsingle
    omega
  · left
    left
    exact ⟨p, m, hp, hm1, hmk, rfl, rfl⟩

/- accepted add_to_file helper 12 -/
lemma loop_parent_child_walk_gap
    (τ : Finset (List ℕ)) (k : List ℕ → ℕ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    {p : List ℕ} (hp : p ∈ τ) :
    ∀ d m : ℕ, 1 ≤ m → m ≤ k p → k p - m = d →
      ∃ hchild : p ++ [m] ∈ τ,
        ∃ w : (loopGraph τ k).Walk ⟨p, hp⟩ ⟨p ++ [m], hchild⟩,
          w.length = k p - m + 1 := by
  intro d
  induction d with
  | zero =>
      intro m hm1 hmk hgap
      have hm : m = k p := by omega
      subst m
      have hkp : 0 < k p := by omega
      have hchild : p ++ [k p] ∈ τ :=
        (hchildren p hp (k p)).mpr ⟨hkp, le_rfl⟩
      refine ⟨hchild, SimpleGraph.Walk.cons
        (loop_adj_parent_last τ k hp hkp hchild) SimpleGraph.Walk.nil, ?_⟩
      simp
  | succ d ih =>
      intro m hm1 hmk hgap
      have hmlt : m < k p := by omega
      have hchild : p ++ [m] ∈ τ := (hchildren p hp m).mpr ⟨hm1, hmk⟩
      have hgapnext : k p - (m + 1) = d := by omega
      rcases ih (m + 1) (by omega) (by omega) hgapnext with ⟨hnext, w, hw⟩
      have hadj := (loop_adj_sibling τ k hp hm1 hmlt hchild hnext).symm
      refine ⟨hchild, w.concat hadj, ?_⟩
      rw [SimpleGraph.Walk.length_concat, hw]
      omega

lemma loop_parent_child_walk
    (τ : Finset (List ℕ)) (k : List ℕ → ℕ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    {p : List ℕ} (hp : p ∈ τ) {m : ℕ} (hm1 : 1 ≤ m) (hmk : m ≤ k p) :
    ∃ hchild : p ++ [m] ∈ τ,
      ∃ w : (loopGraph τ k).Walk ⟨p, hp⟩ ⟨p ++ [m], hchild⟩,
        w.length = k p - m + 1 := by
  exact loop_parent_child_walk_gap τ k hchildren hp
    (k p - m) m hm1 hmk rfl

lemma loop_dist_parent_child
    (τ : Finset (List ℕ)) (k : List ℕ → ℕ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    {p : List ℕ} (hp : p ∈ τ) {m : ℕ} (hm1 : 1 ≤ m) (hmk : m ≤ k p)
    (hchild : p ++ [m] ∈ τ) :
    (loopGraph τ k).dist ⟨p, hp⟩ ⟨p ++ [m], hchild⟩ ≤ k p - m + 1 := by
  rcases loop_parent_child_walk τ k hchildren hp hm1 hmk with ⟨hchild', w, hw⟩
  have hdist := SimpleGraph.dist_le w
  rw [hw] at hdist
  exact hdist

/- accepted add_to_file helper 13 -/
lemma loop_dist_le_W_depth_gap
    {N : ℕ} {τ : Finset (List ℕ)} {k : List ℕ → ℕ}
    (hprefix : ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    {u : Fin N ≃ {v : List ℕ // v ∈ τ}}
    (hlex : ∀ a b : Fin N, a < b ↔
      List.Lex (fun x y : ℕ => x < y) (u a).1 (u b).1)
    {W : Fin (N + 1) → ℤ}
    (hWstep : ∀ r : Fin N,
      W r.succ = W r.castSucc + (k (u r).1 : ℤ) - 1) :
    ∀ n : ℕ, ∀ {i j : Fin N}, i ≤ j →
      (u i).1 <+: (u j).1 →
      (u j).1.length - (u i).1.length ≤ n →
      (((loopGraph τ k).dist (u i) (u j) : ℕ) : ℤ) ≤
        W j.castSucc - W i.castSucc +
          ((u j).1.length : ℤ) - ((u i).1.length : ℤ) := by
  intro n
  induction n with
  | zero =>
      intro i j hij hpre hgap
      have hle_len : (u j).1.length ≤ (u i).1.length := by
        have hz : (u j).1.length - (u i).1.length = 0 := Nat.le_zero.mp hgap
        exact (Nat.sub_eq_zero_iff_le).mp hz
      have hge_len : (u i).1.length ≤ (u j).1.length := hpre.length_le
      have hlen : (u i).1.length = (u j).1.length := by omega
      have hlist : (u i).1 = (u j).1 := hpre.eq_of_length hlen
      have hsub : u i = u j := Subtype.ext hlist
      have hfin : i = j := u.injective hsub
      subst j
      simp
  | succ n ihn =>
      intro i j hij hpre hgap
      by_cases hfin : i = j
      · subst j
        simp
      · have hit : i < j := lt_of_le_of_ne hij hfin
        rcases hpre with ⟨tail, htail⟩
        cases tail with
        | nil =>
            have hlist : (u i).1 = (u j).1 := by
              simpa using htail
            have hsub : u i = u j := Subtype.ext hlist
            exact (hfin (u.injective hsub)).elim
        | cons m rest =>
            have huj : (u j).1 = (u i).1 ++ m :: rest := by
              simpa using htail.symm
            let c := (u i).1 ++ [m]
            have hcpre_j : c <+: (u j).1 := by
              rw [huj]
              refine ⟨rest, ?_⟩
              simp [c, List.append_assoc]
            have hc : c ∈ τ := hprefix (u j).2 hcpre_j
            have hm : 1 ≤ m ∧ m ≤ k (u i).1 :=
              (hchildren (u i).1 (u i).2 m).mp hc
            let t : Fin N := u.symm ⟨c, hc⟩
            have hutsub : u t = ⟨c, hc⟩ := Equiv.apply_symm_apply u ⟨c, hc⟩
            have hut : (u t).1 = c := congrArg Subtype.val hutsub
            have hparentlex : List.Lex (fun p q : ℕ => p < q) (u i).1 c := by
              have hbase : List.Lex (fun p q : ℕ => p < q) [] [m] := List.Lex.nil
              have h := List.Lex.append_left _ hbase (u i).1
              simpa [c] using h
            have hit_t : i < t := by
              apply (hlex i t).mpr
              rw [hut]
              exact hparentlex
            have htj : t ≤ j := by
              by_cases hteq : t = j
              · rw [hteq]
              · have hchildlex_j : List.Lex (fun p q : ℕ => p < q) c (u j).1 := by
                  rw [huj]
                  cases rest with
                  | nil =>
                      have hjt : (u j).1 = c := by
                        simp [huj, c]
                      have hjsub : u j = ⟨c, hc⟩ := Subtype.ext hjt
                      have hjtfin : j = t := by
                        apply u.injective
                        rw [hjsub, hutsub]
                      exact (hteq hjtfin.symm).elim
                  | cons q rest2 =>
                      have hbase : List.Lex (fun p q : ℕ => p < q) [] (q :: rest2) := List.Lex.nil
                      have h := List.Lex.append_left _ hbase c
                      simpa [c, List.append_assoc] using h
                have htltj : t < j := by
                  apply (hlex t j).mpr
                  rw [hut]
                  exact hchildlex_j
                exact le_of_lt htltj
            have htpre_j : (u t).1 <+: (u j).1 := by
              rw [hut]
              exact hcpre_j
            have hgap_t : (u j).1.length - (u t).1.length ≤ n := by
              have hlt : (u t).1.length = (u i).1.length + 1 := by
                simp [hut, c]
              omega
            have hrec := ihn (i := t) (j := j) htj htpre_j hgap_t
            have hWgap := W_parent_child_gap hprefix hchildren (u := u) hlex
              (W := W) hWstep hit_t (m := m) hut
            have hlocalNat := loop_dist_parent_child τ k hchildren (u i).2 hm.1 hm.2 hc
            have htarget : ⟨c, hc⟩ = u t := hutsub.symm
            rw [htarget] at hlocalNat
            rcases loop_parent_child_walk τ k hchildren (u i).2 hm.1 hm.2 with ⟨hc', w, hw⟩
            have htarget' : ⟨c, hc'⟩ = u t := by
              apply Subtype.ext
              exact hut.symm
            rw [htarget'] at w
            have hreach := w.reachable
            have htri := hreach.dist_triangle_left (u j)
            have htriZ : (((loopGraph τ k).dist (u i) (u j) : ℕ) : ℤ) ≤
                (((loopGraph τ k).dist (u i) (u t) : ℕ) : ℤ) +
                (((loopGraph τ k).dist (u t) (u j) : ℕ) : ℤ) := by
              exact_mod_cast htri
            have hlocalZ : (((loopGraph τ k).dist (u i) (u t) : ℕ) : ℤ) ≤
                (k (u i).1 : ℤ) - m + 1 := by
              have h0 : (((loopGraph τ k).dist (u i) (u t) : ℕ) : ℤ) ≤
                  (((k (u i).1 - m + 1 : ℕ) : ℤ)) := by
                exact_mod_cast hlocalNat
              have h1 : (((k (u i).1 - m + 1 : ℕ) : ℤ)) =
                  (k (u i).1 : ℤ) - m + 1 := by
                omega
              rwa [h1] at h0
            have hlen_t : ((u t).1.length : ℤ) - ((u i).1.length : ℤ) = 1 := by
              have hlt : (u t).1.length = (u i).1.length + 1 := by
                simp [hut, c]
              rw [hlt]
              norm_num
            linarith

/- accepted add_to_file helper 14 -/
lemma loop_reachable_of_prefix_gap
    {τ : Finset (List ℕ)} {k : List ℕ → ℕ}
    (hprefix : ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v) :
    ∀ n : ℕ, ∀ {a b : {v : List ℕ // v ∈ τ}},
      a.1 <+: b.1 → b.1.length - a.1.length ≤ n →
      (loopGraph τ k).Reachable a b := by
  intro n
  induction n with
  | zero =>
      intro a b hpre hgap
      have hle_len : b.1.length ≤ a.1.length := by
        have hz : b.1.length - a.1.length = 0 := Nat.le_zero.mp hgap
        exact (Nat.sub_eq_zero_iff_le).mp hz
      have hge_len : a.1.length ≤ b.1.length := hpre.length_le
      have hlen : a.1.length = b.1.length := by omega
      have hlist : a.1 = b.1 := hpre.eq_of_length hlen
      have hab : a = b := Subtype.ext hlist
      cases hab
      exact SimpleGraph.Reachable.refl (G := loopGraph τ k) a
  | succ n ihn =>
      intro a b hpre hgap
      rcases hpre with ⟨tail, htail⟩
      cases tail with
      | nil =>
          have hlist : a.1 = b.1 := by simpa using htail
          have hab : a = b := Subtype.ext hlist
          cases hab
          exact SimpleGraph.Reachable.refl (G := loopGraph τ k) a
      | cons m rest =>
          have hb : b.1 = a.1 ++ m :: rest := by
            simpa using htail.symm
          let c := a.1 ++ [m]
          have hcpre_b : c <+: b.1 := by
            rw [hb]
            refine ⟨rest, ?_⟩
            simp [c, List.append_assoc]
          have hc : c ∈ τ := hprefix b.2 hcpre_b
          have hm : 1 ≤ m ∧ m ≤ k a.1 :=
            (hchildren a.1 a.2 m).mp hc
          let cvertex : {v : List ℕ // v ∈ τ} := ⟨c, hc⟩
          have hcpre_b' : cvertex.1 <+: b.1 := hcpre_b
          have hgap_c : b.1.length - cvertex.1.length ≤ n := by
            have hclen : cvertex.1.length = a.1.length + 1 := by
              simp [cvertex, c]
            omega
          have hrec := ihn (a := cvertex) (b := b) hcpre_b' hgap_c
          rcases loop_parent_child_walk τ k hchildren a.2 hm.1 hm.2 with ⟨hc', w, hw⟩
          have htarget : ⟨c, hc'⟩ = cvertex := rfl
          rw [htarget] at w
          exact w.reachable.trans hrec

lemma loop_reachable_of_prefix
    {τ : Finset (List ℕ)} {k : List ℕ → ℕ}
    (hprefix : ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    {a b : {v : List ℕ // v ∈ τ}} (hpre : a.1 <+: b.1) :
    (loopGraph τ k).Reachable a b := by
  exact loop_reachable_of_prefix_gap hprefix hchildren
    (b.1.length - a.1.length) hpre le_rfl

lemma loop_dist_le_W_depth
    {N : ℕ} {τ : Finset (List ℕ)} {k : List ℕ → ℕ}
    (hprefix : ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    {u : Fin N ≃ {v : List ℕ // v ∈ τ}}
    (hlex : ∀ a b : Fin N, a < b ↔
      List.Lex (fun x y : ℕ => x < y) (u a).1 (u b).1)
    {W : Fin (N + 1) → ℤ}
    (hWstep : ∀ r : Fin N,
      W r.succ = W r.castSucc + (k (u r).1 : ℤ) - 1)
    {i j : Fin N} (hij : i ≤ j) (hpre : (u i).1 <+: (u j).1) :
    (((loopGraph τ k).dist (u i) (u j) : ℕ) : ℤ) ≤
      W j.castSucc - W i.castSucc +
        ((u j).1.length : ℤ) - ((u i).1.length : ℤ) := by
  exact loop_dist_le_W_depth_gap hprefix hchildren (u := u) hlex (W := W) hWstep
    ((u j).1.length - (u i).1.length) hij hpre le_rfl

/- verified submission -/
theorem looptree_height_bound
    (N : ℕ)
    (τ : Finset (List ℕ))
    (k : List ℕ → ℕ)
    (hroot : [] ∈ τ)
    (hprefix : ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    (u : Fin N ≃ {v : List ℕ // v ∈ τ})
    (hlex : ∀ a b : Fin N, a < b ↔
      List.Lex (fun x y : ℕ => x < y) (u a).1 (u b).1)
    (W : Fin (N + 1) → ℤ)
    (hWzero : W 0 = 0)
    (hWstep : ∀ r : Fin N,
      W r.succ = W r.castSucc + (k (u r).1 : ℤ) - 1) :
    let H : Fin N → ℕ := fun r => (u r).1.length
    let Loop : SimpleGraph {v : List ℕ // v ∈ τ} :=
      SimpleGraph.fromRel fun x y =>
        (∃ (p : List ℕ) (m : ℕ), p ∈ τ ∧ 1 ≤ m ∧ m < k p ∧
          x.1 = p ++ [m] ∧ y.1 = p ++ [m + 1]) ∨
        (0 < k x.1 ∧ (y.1 = x.1 ++ [1] ∨ y.1 = x.1 ++ [k x.1]))
    let Hb : Fin N → ℕ := fun r => Loop.dist ⟨[], hroot⟩ (u r)
    ∀ i j : Fin N, i < j → (u i).1 <+: (u j).1 →
      |(Hb i : ℤ) - (Hb j : ℤ)| ≤
        W j.castSucc - W i.castSucc + (H j : ℤ) - (H i : ℤ) := by
  intro H Loop Hb i j hij hpre
  have hreach : Loop.Reachable (u i) (u j) :=
    loop_reachable_of_prefix hprefix hchildren hpre
  have hdist : (((Loop.dist (u i) (u j) : ℕ) : ℤ)) ≤
      W j.castSucc - W i.castSucc + (H j : ℤ) - (H i : ℤ) := by
    exact loop_dist_le_W_depth hprefix hchildren (u := u) hlex
      (W := W) hWstep (le_of_lt hij) hpre
  have htri_i := hreach.dist_triangle_left ⟨[], hroot⟩
  have htri_j := hreach.symm.dist_triangle_left ⟨[], hroot⟩
  have hcomm : Loop.dist (u j) (u i) = Loop.dist (u i) (u j) :=
    SimpleGraph.dist_comm
  have htri_iZ : ((Loop.dist (u i) ⟨[], hroot⟩ : ℕ) : ℤ) ≤
      ((Loop.dist (u i) (u j) : ℕ) : ℤ) +
        ((Loop.dist (u j) ⟨[], hroot⟩ : ℕ) : ℤ) := by
    exact_mod_cast htri_i
  have htri_jZ : ((Loop.dist (u j) ⟨[], hroot⟩ : ℕ) : ℤ) ≤
      ((Loop.dist (u i) (u j) : ℕ) : ℤ) +
        ((Loop.dist (u i) ⟨[], hroot⟩ : ℕ) : ℤ) := by
    have htri_j' : Loop.dist (u j) ⟨[], hroot⟩ ≤
        Loop.dist (u i) (u j) + Loop.dist (u i) ⟨[], hroot⟩ := by
      simpa [hcomm] using htri_j
    exact_mod_cast htri_j'
  have hdist_i : Loop.dist (u i) ⟨[], hroot⟩ = Loop.dist ⟨[], hroot⟩ (u i) :=
    SimpleGraph.dist_comm
  have hdist_j : Loop.dist (u j) ⟨[], hroot⟩ = Loop.dist ⟨[], hroot⟩ (u j) :=
    SimpleGraph.dist_comm
  rw [hdist_i] at htri_iZ
  rw [hdist_j] at htri_jZ
  change |((Loop.dist ⟨[], hroot⟩ (u i) : ℕ) : ℤ) -
      ((Loop.dist ⟨[], hroot⟩ (u j) : ℕ) : ℤ)| ≤
      W j.castSucc - W i.castSucc + (((u j).1.length : ℕ) : ℤ) -
        (((u i).1.length : ℕ) : ℤ)
  rw [abs_le]
  constructor <;> linarith
