import Mathlib

/- accepted add_to_file helper 1 -/
lemma list_prod_one_lt_of_forall_one_lt
    {G : Type*} [Group G] {r : G → G → Prop}
    (hsto : IsStrictTotalOrder G r)
    (hright : ∀ a b c : G, r a b ↔ r (a * c) (b * c))
    {l : List G} (hne : l ≠ []) (hpos : ∀ a ∈ l, r 1 a) :
    r 1 l.prod := by
  induction l with
  | nil => exact (hne rfl).elim
  | cons a l ih =>
      by_cases hl : l = []
      · subst l
        simpa using hpos a (by simp)
      · have ha : r 1 a := hpos a (by simp)
        have htail : r 1 l.prod := ih hl (fun b hb => hpos b (List.mem_cons_of_mem a hb))
        have hmul : r l.prod (a * l.prod) := by
          have h := (hright 1 a l.prod).mp ha
          simpa using h
        have hprod : r 1 (a * l.prod) := hsto.trans 1 l.prod (a * l.prod) htail hmul
        simpa [List.prod_cons] using hprod

lemma list_prod_lt_one_of_forall_lt_one
    {G : Type*} [Group G] {r : G → G → Prop}
    (hsto : IsStrictTotalOrder G r)
    (hright : ∀ a b c : G, r a b ↔ r (a * c) (b * c))
    {l : List G} (hne : l ≠ []) (hneg : ∀ a ∈ l, r a 1) :
    r l.prod 1 := by
  induction l with
  | nil => exact (hne rfl).elim
  | cons a l ih =>
      by_cases hl : l = []
      · subst l
        simpa using hneg a (by simp)
      · have ha : r a 1 := hneg a (by simp)
        have htail : r l.prod 1 := ih hl (fun b hb => hneg b (List.mem_cons_of_mem a hb))
        have hmul : r (a * l.prod) l.prod := by
          have h := (hright a 1 l.prod).mp ha
          simpa using h
        have hprod : r (a * l.prod) 1 := hsto.trans (a * l.prod) l.prod 1 hmul htail
        simpa [List.prod_cons] using hprod

/- accepted add_to_file helper 2 -/
lemma conj_mul_iff
    {G : Type*} [Group G] {r : G → G → Prop}
    (hleft : ∀ a b c : G, r a b ↔ r (c * a) (c * b))
    (hright : ∀ a b c : G, r a b ↔ r (a * c) (b * c))
    (x a b : G) :
    r (x⁻¹ * a * x) (x⁻¹ * b * x) ↔ r a b := by
  constructor
  · intro h
    have hmiddle : r (a * x) (b * x) := by
      have htransformed : r (x⁻¹ * (a * x)) (x⁻¹ * (b * x)) := by
        simpa [mul_assoc] using h
      exact (hleft (a * x) (b * x) x⁻¹).mpr htransformed
    exact (hright a b x).mpr hmiddle
  · intro h
    have hmiddle : r (a * x) (b * x) := (hright a b x).mp h
    have htransformed : r (x⁻¹ * (a * x)) (x⁻¹ * (b * x)) :=
      (hleft (a * x) (b * x) x⁻¹).mp hmiddle
    simpa [mul_assoc] using htransformed

/- verified submission -/
theorem not_biorderable_of_product_conjugates_eq_one
    {G : Type*} [Group G]
    (h : ∃ (g : G) (k : ℕ) (x : Fin k → G),
      g ≠ 1 ∧ 1 ≤ k ∧ (List.ofFn (fun i => (x i)⁻¹ * g * x i)).prod = 1) :
    ¬ ∃ r : G → G → Prop,
      IsStrictTotalOrder G r ∧
        (∀ a b c : G, r a b ↔ r (c * a) (c * b)) ∧
        (∀ a b c : G, r a b ↔ r (a * c) (b * c)) := by
  rintro ⟨r, hsto, hleft, hright⟩
  rcases h with ⟨g, k, x, hg, hk, hprod⟩
  let l : List G := List.ofFn (fun i => (x i)⁻¹ * g * x i)
  have hne : l ≠ [] := by
    dsimp [l]
    rw [List.ofFn_eq_nil_iff]
    omega
  have hside : r 1 g ∨ r g 1 := by
    by_cases hpos : r 1 g
    · exact Or.inl hpos
    · right
      by_contra hneg
      have heq : 1 = g := hsto.trichotomous 1 g hpos hneg
      exact hg heq.symm
  cases hside with
  | inl hpos =>
      have hall : ∀ a ∈ l, r 1 a := by
        intro a ha
        rcases List.mem_ofFn.mp ha with ⟨i, hi⟩
        have hci : r 1 ((x i)⁻¹ * g * x i) := by
          have hc := conj_mul_iff hleft hright (x i) 1 g
          simpa using hc.mpr hpos
        simpa [l, hi] using hci
      have hprodside : r 1 l.prod :=
        list_prod_one_lt_of_forall_one_lt hsto hright hne hall
      rw [show l.prod = 1 from hprod] at hprodside
      exact hsto.irrefl 1 hprodside
  | inr hneg =>
      have hall : ∀ a ∈ l, r a 1 := by
        intro a ha
        rcases List.mem_ofFn.mp ha with ⟨i, hi⟩
        have hci : r ((x i)⁻¹ * g * x i) 1 := by
          have hc := conj_mul_iff hleft hright (x i) g 1
          simpa using hc.mpr hneg
        simpa [l, hi] using hci
      have hprodside : r l.prod 1 :=
        list_prod_lt_one_of_forall_lt_one hsto hright hne hall
      rw [show l.prod = 1 from hprod] at hprodside
      exact hsto.irrefl 1 hprodside
