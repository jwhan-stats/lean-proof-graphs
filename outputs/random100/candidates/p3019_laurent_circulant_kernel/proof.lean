import Mathlib

/- accepted add_to_file helper 1 -/
lemma eq_of_forall_sub_natCast_zmod
    {m a : ℕ} [NeZero m] {α : Type*} {v : ZMod m → α}
    (hcop : Nat.Coprime a m)
    (h : ∀ i : ZMod m, v i = v (i - (a : ZMod m))) :
    ∀ i j : ZMod m, v i = v j := by
  let u : ZMod m := a
  have hu : IsUnit u := by
    dsimp [u]
    exact (ZMod.isUnit_iff_coprime a m).2 hcop
  have hiter : ∀ (c : ℕ) (i : ZMod m), v i = v (i - (c : ZMod m) * u) := by
    intro c
    induction c with
    | zero =>
        intro i
        simp
    | succ c hc =>
        intro i
        calc
          v i = v (i - (c : ZMod m) * u) := hc i
          _ = v ((i - (c : ZMod m) * u) - u) := h _
          _ = v (i - ((c + 1 : ℕ) : ZMod m) * u) := by
            congr 1
            simp [Nat.cast_add, add_mul]
            ring
  intro i j
  let c : ℕ := (((i - j) * u⁻¹).val)
  have hcast : (c : ZMod m) = (i - j) * u⁻¹ := by
    dsimp [c]
    simpa using (ZMod.natCast_val ((i - j) * u⁻¹) : (((i - j) * u⁻¹).val : ZMod m) = ((i - j) * u⁻¹).cast)
  have hcu : (c : ZMod m) * u = i - j := by
    rw [hcast]
    calc
      ((i - j) * u⁻¹) * u = (i - j) * (u⁻¹ * u) := by ring
      _ = i - j := by rw [ZMod.inv_mul_of_unit u hu]; ring
  calc
    v i = v (i - (c : ZMod m) * u) := hiter c i
    _ = v j := by
      rw [hcu]
      congr 1
      abel

/- accepted add_to_file helper 2 -/
noncomputable def laurentCirculantB
    (a b : ℕ) [NeZero (a + b)] (ε : ℤ) :
    Matrix (ZMod (a + b)) (ZMod (a + b)) (LaurentPolynomial ℤ) := fun i j =>
  if i - j = ((-(a : ℤ) : ℤ) : ZMod (a + b)) then
    LaurentPolynomial.C ε * LaurentPolynomial.T 1
  else if i - j ∈ (Finset.Ico 1 a).image
      (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a + b))) then
    1 + LaurentPolynomial.C ε * LaurentPolynomial.T 1
  else if i - j = 0 then
    1 - LaurentPolynomial.C ε * LaurentPolynomial.T 1
  else if i - j ∈ (Finset.Ico 1 a).image
      (fun k : ℕ => (k : ZMod (a + b))) then
    -1 - LaurentPolynomial.C ε * LaurentPolynomial.T 1
  else if i - j = (a : ZMod (a + b)) then
    -1
  else
    0

/- accepted add_to_file helper 3 -/
lemma sum_ite_eq_image_ite
    {ι α R : Type*} [DecidableEq ι] [DecidableEq α] [Semiring R]
    (s : Finset ι) (f : ι → α) (d : α)
    (hinj : Set.InjOn f s) :
    (∑ k ∈ s, (if d = f k then (1 : R) else 0)) =
      if d ∈ s.image f then 1 else 0 := by
  by_cases hd : d ∈ s.image f
  · rw [if_pos hd]
    rcases Finset.mem_image.mp hd with ⟨k, hk, hkd⟩
    rw [Finset.sum_eq_single_of_mem k hk]
    · rw [← hkd]
      simp
    · intro l hl hlk
      have hfl : f l ≠ d := by
        intro hfl
        apply hlk
        apply hinj hl hk
        rw [hfl, hkd]
      rw [if_neg]
      exact ne_comm.mp hfl
  · rw [if_neg hd]
    apply Finset.sum_eq_zero
    intro k hk
    have hne : d ≠ f k := by
      intro h
      exact hd (Finset.mem_image.mpr ⟨k, hk, h.symm⟩)
    rw [if_neg hne]

/- accepted add_to_file helper 4 -/
lemma zmod_natCast_injOn_Ico_one
    {m a : ℕ} [NeZero m] (ham : a < m) :
    Set.InjOn (fun k : ℕ => (k : ZMod m)) (Finset.Ico 1 a) := by
  intro k hk l hl hkl
  have hklt : k < m := lt_trans (Finset.mem_Ico.mp hk).2 ham
  have hllt : l < m := lt_trans (Finset.mem_Ico.mp hl).2 ham
  have hmod : k % m = l % m := (ZMod.natCast_eq_natCast_iff' k l m).mp hkl
  rwa [Nat.mod_eq_of_lt hklt, Nat.mod_eq_of_lt hllt] at hmod

lemma zmod_int_sub_natCast_injOn_Ico_one
    {m a : ℕ} [NeZero m] (ham : a < m) :
    Set.InjOn
      (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod m))
      (Finset.Ico 1 a) := by
  intro k hk l hl hkl
  have hcast : (k : ZMod m) = (l : ZMod m) := by
    have h := congrArg (fun z : ZMod m => z + (a : ZMod m)) hkl
    simpa using h
  exact zmod_natCast_injOn_Ico_one ham hk hl hcast

/- accepted add_to_file helper 5 -/
lemma zmod_intCast_ne_of_abs_sub_lt {m : ℕ} [NeZero m] {x y : ℤ}
    (hdiff : |x - y| < (m : ℤ)) (hxy : x ≠ y) :
    (x : ZMod m) ≠ (y : ZMod m) := by
  intro h
  have hmod : x ≡ y [ZMOD (m : ℤ)] :=
    (ZMod.intCast_eq_intCast_iff x y m).mp h
  have hdvd : (m : ℤ) ∣ y - x := Int.modEq_iff_dvd.mp hmod
  have hzero : y - x = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd hdvd
    rw [abs_sub_comm]
    exact hdiff
  exact hxy (by omega)

/- accepted add_to_file helper 6 -/
lemma zmod_neg_a_not_mem_shift_image
    (a b : ℕ) [NeZero (a+b)] :
    (((-(a : ℤ) : ℤ) : ZMod (a+b)) ∉
      (Finset.Ico 1 a).image (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))) := by
  intro h
  rcases Finset.mem_image.mp h with ⟨k,hk,hka⟩
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have hk2 : k < a := (Finset.mem_Ico.mp hk).2
  have hne := zmod_intCast_ne_of_abs_sub_lt (m:=a+b)
    (x:=-(a:ℤ)) (y:=(k:ℤ)-(a:ℤ)) ?_ ?_
  · exact hne hka.symm
  · have hrewrite : (-(a : ℤ) : ℤ) - ((k : ℤ) - (a : ℤ)) = -(k : ℤ) := by ring
    rw [hrewrite, abs_neg]
    norm_num
    omega
  · omega

lemma zmod_neg_a_ne_zero (a b : ℕ) [NeZero (a+b)] (ha : 0 < a) (hab : a < b) :
    (((-(a : ℤ) : ℤ) : ZMod (a+b)) ≠ 0) := by
  have hneInt : (((-(a : ℤ) : ℤ) : ZMod (a+b)) ≠ ((0 : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b) (x:=-(a:ℤ)) (y:=0)
    · rw [sub_zero, abs_neg]
      norm_num
      omega
    · omega
  simpa using hneInt

lemma zmod_neg_a_not_mem_nat_image
    (a b : ℕ) [NeZero (a+b)] (hab : a < b) :
    (((-(a : ℤ) : ℤ) : ZMod (a+b)) ∉
      (Finset.Ico 1 a).image (fun k : ℕ => (k : ZMod (a+b)))) := by
  intro h
  rcases Finset.mem_image.mp h with ⟨k,hk,hka⟩
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have hk2 : k < a := (Finset.mem_Ico.mp hk).2
  have hneInt : (((-(a : ℤ) : ℤ) : ZMod (a+b)) ≠ (((k : ℤ) : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b) (x:=-(a:ℤ)) (y:=(k:ℤ))
    · have hrewrite : (-(a : ℤ) : ℤ) - (k : ℤ) = -(((a + k : ℕ) : ℤ)) := by
        norm_num
        ring
      rw [hrewrite, abs_neg]
      have hnonneg : 0 ≤ (((a + k : ℕ) : ℤ)) := by positivity
      rw [abs_of_nonneg hnonneg]
      have hlt : a + k < a + b := by omega
      exact_mod_cast hlt
    · omega
  have hne : (((-(a : ℤ) : ℤ) : ZMod (a+b)) ≠ (k : ZMod (a+b))) := by
    simpa using hneInt
  exact hne hka.symm

lemma zmod_neg_a_ne_a (a b : ℕ) [NeZero (a+b)] (ha : 0 < a) (hab : a < b) :
    (((-(a : ℤ) : ℤ) : ZMod (a+b)) ≠ (a : ZMod (a+b))) := by
  have hneInt : (((-(a : ℤ) : ℤ) : ZMod (a+b)) ≠ (((a : ℤ) : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b) (x:=-(a:ℤ)) (y:=(a:ℤ))
    · have hrewrite : (-(a : ℤ) : ℤ) - (a : ℤ) = -(((2 * a : ℕ) : ℤ)) := by
        norm_num
        ring
      rw [hrewrite, abs_neg]
      have hnonneg : 0 ≤ (((2 * a : ℕ) : ℤ)) := by positivity
      rw [abs_of_nonneg hnonneg]
      have hlt : 2 * a < a + b := by omega
      exact_mod_cast hlt
    · omega
  simpa using hneInt

/- accepted add_to_file helper 7 -/
lemma zmod_shift_image_ne_zero
    (a b : ℕ) [NeZero (a+b)] {d : ZMod (a+b)}
    (hd : d ∈ (Finset.Ico 1 a).image
      (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))) :
    d ≠ 0 := by
  rcases Finset.mem_image.mp hd with ⟨k,hk,rfl⟩
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have hk2 : k < a := (Finset.mem_Ico.mp hk).2
  have hneInt : ((((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)) ≠ ((0 : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b)
      (x:=(k:ℤ)-(a:ℤ)) (y:=0)
    · rw [sub_zero]
      have hrewrite : (k : ℤ) - (a : ℤ) = -(((a - k : ℕ) : ℤ)) := by
        omega
      rw [hrewrite, abs_neg]
      have hnonneg : 0 ≤ (((a - k : ℕ) : ℤ)) := by positivity
      rw [abs_of_nonneg hnonneg]
      have hknat : a - k < a + b := by omega
      exact_mod_cast hknat
    · omega
  simpa using hneInt

lemma zmod_shift_image_disjoint_nat_image
    (a b : ℕ) [NeZero (a+b)] (hab : a < b) {d : ZMod (a+b)}
    (hd : d ∈ (Finset.Ico 1 a).image
      (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))) :
    d ∉ (Finset.Ico 1 a).image (fun k : ℕ => (k : ZMod (a+b))) := by
  rcases Finset.mem_image.mp hd with ⟨k,hk,rfl⟩
  intro hP
  rcases Finset.mem_image.mp hP with ⟨l,hl,hkl⟩
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have hk2 : k < a := (Finset.mem_Ico.mp hk).2
  have hl1 : 1 ≤ l := (Finset.mem_Ico.mp hl).1
  have hl2 : l < a := (Finset.mem_Ico.mp hl).2
  have hneInt : ((((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)) ≠ (((l : ℤ) : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b)
      (x:=(k:ℤ)-(a:ℤ)) (y:=(l:ℤ))
    · have hrewrite : ((k : ℤ) - (a : ℤ)) - (l : ℤ) =
          -((((a + l) - k : ℕ) : ℤ)) := by
        omega
      rw [hrewrite, abs_neg]
      have hnonneg : 0 ≤ ((((a + l) - k : ℕ) : ℤ)) := by positivity
      rw [abs_of_nonneg hnonneg]
      have hlt : (a + l) - k < a + b := by omega
      exact_mod_cast hlt
    · omega
  have hne : ((((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)) ≠ (l : ZMod (a+b))) := by
    simpa using hneInt
  exact hne hkl.symm

lemma zmod_shift_image_ne_a
    (a b : ℕ) [NeZero (a+b)] (hab : a < b) {d : ZMod (a+b)}
    (hd : d ∈ (Finset.Ico 1 a).image
      (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))) :
    d ≠ (a : ZMod (a+b)) := by
  rcases Finset.mem_image.mp hd with ⟨k,hk,rfl⟩
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have hk2 : k < a := (Finset.mem_Ico.mp hk).2
  have hneInt : ((((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)) ≠ (((a : ℤ) : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b)
      (x:=(k:ℤ)-(a:ℤ)) (y:=(a:ℤ))
    · have hrewrite : ((k : ℤ) - (a : ℤ)) - (a : ℤ) =
          -(((2 * a - k : ℕ) : ℤ)) := by
        omega
      rw [hrewrite, abs_neg]
      have hnonneg : 0 ≤ (((2 * a - k : ℕ) : ℤ)) := by positivity
      rw [abs_of_nonneg hnonneg]
      have hlt : 2 * a - k < a + b := by omega
      exact_mod_cast hlt
    · omega
  simpa using hneInt

/- accepted add_to_file helper 8 -/
lemma zmod_zero_not_mem_nat_image
    (a b : ℕ) [NeZero (a+b)] :
    (0 : ZMod (a+b)) ∉
      (Finset.Ico 1 a).image (fun k : ℕ => (k : ZMod (a+b))) := by
  intro h
  rcases Finset.mem_image.mp h with ⟨k,hk,hka⟩
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have hk2 : k < a := (Finset.mem_Ico.mp hk).2
  have hneInt : (((0 : ℤ) : ZMod (a+b)) ≠ (((k : ℤ) : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b)
      (x:=0) (y:=(k:ℤ))
    · rw [zero_sub, abs_neg]
      norm_num
      omega
    · omega
  have hne : (0 : ZMod (a+b)) ≠ (k : ZMod (a+b)) := by
    simpa using hneInt
  exact hne hka.symm

lemma zmod_zero_ne_a (a b : ℕ) [NeZero (a+b)] (ha : 0 < a) (hab : a < b) :
    (0 : ZMod (a+b)) ≠ (a : ZMod (a+b)) := by
  have hneInt : (((0 : ℤ) : ZMod (a+b)) ≠ (((a : ℤ) : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b) (x:=0) (y:=(a:ℤ))
    · rw [zero_sub, abs_neg]
      norm_num
      omega
    · omega
  simpa using hneInt

lemma zmod_nat_image_ne_a
    (a b : ℕ) [NeZero (a+b)] {d : ZMod (a+b)}
    (hd : d ∈ (Finset.Ico 1 a).image (fun k : ℕ => (k : ZMod (a+b)))) :
    d ≠ (a : ZMod (a+b)) := by
  rcases Finset.mem_image.mp hd with ⟨k,hk,rfl⟩
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have hk2 : k < a := (Finset.mem_Ico.mp hk).2
  have hneInt : ((((k : ℤ) : ℤ) : ZMod (a+b)) ≠ (((a : ℤ) : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b)
      (x:=(k:ℤ)) (y:=(a:ℤ))
    · have hrewrite : (k : ℤ) - (a : ℤ) = -(((a - k : ℕ) : ℤ)) := by
        omega
      rw [hrewrite, abs_neg]
      have hnonneg : 0 ≤ (((a - k : ℕ) : ℤ)) := by positivity
      rw [abs_of_nonneg hnonneg]
      have hlt : a - k < a + b := by omega
      exact_mod_cast hlt
    · omega
  have hne : ((k : ZMod (a+b)) ≠ (a : ZMod (a+b))) := by
    simpa using hneInt
  exact hne

/- accepted add_to_file helper 9 -/
lemma zmod_a_not_mem_shift_image
    (a b : ℕ) [NeZero (a+b)] (hab : a < b) :
    (a : ZMod (a+b)) ∉
      (Finset.Ico 1 a).image
        (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b))) := by
  intro h
  exact zmod_shift_image_ne_a a b hab h rfl

lemma zmod_a_not_mem_nat_image
    (a b : ℕ) [NeZero (a+b)] :
    (a : ZMod (a+b)) ∉
      (Finset.Ico 1 a).image (fun k : ℕ => (k : ZMod (a+b))) := by
  intro h
  exact zmod_nat_image_ne_a a b h rfl

/- accepted add_to_file helper 10 -/
lemma zmod_zero_not_mem_shift_image
    (a b : ℕ) [NeZero (a+b)] :
    (0 : ZMod (a+b)) ∉
      (Finset.Ico 1 a).image
        (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b))) := by
  intro h
  exact zmod_shift_image_ne_zero a b h rfl

/- accepted add_to_file helper 11 -/
lemma laurentCirculantB_eq_sum
    (a b : ℕ) [NeZero (a + b)] (ha : 0 < a) (hab : a < b) (ε : ℤ) :
    let t : LaurentPolynomial ℤ := LaurentPolynomial.C ε * LaurentPolynomial.T 1
    let D : ZMod (a+b) → Matrix (ZMod (a+b)) (ZMod (a+b)) (LaurentPolynomial ℤ) :=
      fun c i j => if i - j = c then 1 else 0
    laurentCirculantB a b ε =
      t • D (((-(a : ℤ) : ℤ) : ZMod (a+b))) +
      (1 + t) • (∑ k ∈ Finset.Ico 1 a, D (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b))) +
      (1 - t) • D 0 +
      (-1 - t) • (∑ k ∈ Finset.Ico 1 a, D (k : ZMod (a+b))) +
      (-1) • D (a : ZMod (a+b)) := by
  intro t D
  apply Matrix.ext
  intro i j
  have ham : a < a + b := Nat.lt_add_of_pos_right (Nat.lt_trans ha hab)
  simp only [laurentCirculantB, D, Matrix.add_apply, Matrix.smul_apply]
  rw [Matrix.sum_apply i j (Finset.Ico 1 a)
    (fun x => (fun i j => if i - j = (((x : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)) then (1:LaurentPolynomial ℤ) else 0))]
  rw [Matrix.sum_apply i j (Finset.Ico 1 a)
    (fun x => (fun i j => if i - j = (x : ZMod (a+b)) then (1:LaurentPolynomial ℤ) else 0))]
  rw [sum_ite_eq_image_ite (Finset.Ico 1 a)
    (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b))) (i-j)
    (zmod_int_sub_natCast_injOn_Ico_one ham)]
  rw [sum_ite_eq_image_ite (Finset.Ico 1 a)
    (fun k : ℕ => (k : ZMod (a+b))) (i-j)
    (zmod_natCast_injOn_Ico_one ham)]
  by_cases hA : i - j = (((-(a : ℤ) : ℤ) : ZMod (a+b)))
  · have hN := zmod_neg_a_not_mem_shift_image a b
    have hZ := zmod_neg_a_ne_zero a b ha hab
    have hP := zmod_neg_a_not_mem_nat_image a b hab
    have hAp := zmod_neg_a_ne_a a b ha hab
    simp only [hA, hN, hZ, hP, hAp, if_true, if_false, smul_eq_mul, mul_one, mul_zero,
      add_zero, zero_add, neg_mul, one_mul]
    ring
  · by_cases hN : i - j ∈ (Finset.Ico 1 a).image
        (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))
    · have hZ : i - j ≠ 0 := zmod_shift_image_ne_zero a b hN
      have hP : i - j ∉ (Finset.Ico 1 a).image (fun k : ℕ => (k : ZMod (a+b))) :=
        zmod_shift_image_disjoint_nat_image a b hab hN
      have hAp : i - j ≠ (a : ZMod (a+b)) := zmod_shift_image_ne_a a b hab hN
      simp only [hA, hN, hZ, hP, hAp, if_true, if_false, smul_eq_mul, mul_one, mul_zero,
        add_zero, zero_add, neg_mul, one_mul]
      ring
    · by_cases hZ : i - j = 0
      · have hA0 : (0 : ZMod (a+b)) ≠ (((-(a : ℤ) : ℤ) : ZMod (a+b))) :=
          (zmod_neg_a_ne_zero a b ha hab).symm
        have hN0 := zmod_zero_not_mem_shift_image a b
        have hP0 := zmod_zero_not_mem_nat_image a b
        have hAp0 := zmod_zero_ne_a a b ha hab
        simp only [hZ, hA0, hN0, hP0, hAp0, if_true, if_false, smul_eq_mul, mul_one, mul_zero,
          add_zero, zero_add, neg_mul, one_mul]
        ring
      · by_cases hP : i - j ∈ (Finset.Ico 1 a).image (fun k : ℕ => (k : ZMod (a+b)))
        · have hAp : i - j ≠ (a : ZMod (a+b)) := zmod_nat_image_ne_a a b hP
          simp only [hA, hN, hZ, hP, hAp, if_true, if_false, smul_eq_mul, mul_one, mul_zero,
            add_zero, zero_add, neg_mul, one_mul]
          ring
        · by_cases hAp : i - j = (a : ZMod (a+b))
          · have hA' : (a : ZMod (a+b)) ≠ (((-(a : ℤ) : ℤ) : ZMod (a+b))) :=
              (zmod_neg_a_ne_a a b ha hab).symm
            have hN' := zmod_a_not_mem_shift_image a b hab
            have hZ' := (zmod_zero_ne_a a b ha hab).symm
            have hP' := zmod_a_not_mem_nat_image a b
            simp only [hAp, hA', hN', hZ', hP', if_true, if_false, smul_eq_mul, mul_one, mul_zero,
              add_zero, zero_add, neg_mul, one_mul]
            ring
          · simp only [hA, hN, hZ, hP, hAp, if_true, if_false, smul_eq_mul, mul_one, mul_zero,
              add_zero, zero_add, neg_mul, one_mul]
            ring

/- accepted add_to_file helper 12 -/
lemma zmod_diag_mulVec {m : ℕ} [NeZero m] {R : Type*} [Ring R]
    (c : ZMod m) (v : ZMod m → R) (i : ZMod m) :
    Matrix.mulVec ((fun i j : ZMod m => if i - j = c then (1 : R) else 0) :
      Matrix (ZMod m) (ZMod m) R) v i =
      v (i - c) := by
  rw [Matrix.mulVec]
  simp [dotProduct]
  rw [Finset.sum_eq_single (i - c)]
  · simp
  · intro x _ hx
    have hne : i - x ≠ c := by
      intro h
      apply hx
      rw [← h]
      abel
    simp [hne]
  · simp

/- accepted add_to_file helper 13 -/
lemma zmod_shift_interval_sum
    (a b : ℕ) [NeZero (a+b)] (ha : 0 < a)
    (v : ZMod (a+b) → LaurentPolynomial ℤ) (r : ZMod (a+b)) :
    (∑ k ∈ Finset.Ico 1 a,
      v (r - (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))) =
    ∑ j ∈ Finset.range (a-1), v (r + ((j + 1 : ℕ) : ZMod (a+b))) := by
  let m := a - 1
  let g : ℕ → LaurentPolynomial ℤ := fun z => v (r + ((z + 1 : ℕ) : ZMod (a+b)))
  have hpoint :
      (∑ k ∈ Finset.Ico 1 a,
        v (r - (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))) =
      ∑ j ∈ Finset.range m, g (m - 1 - j) := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < a - 1 := Finset.mem_range.mp hj
    dsimp [g, m] at hj ⊢
    have hnat : a - 1 - 1 - j + 1 = a - 1 - j := by omega
    rw [hnat]
    congr 1
    rw [Nat.cast_sub (by omega : j ≤ a - 1)]
    rw [Nat.cast_sub (by omega : 1 ≤ a)]
    push_cast
    abel
  rw [hpoint]
  simpa [g, m] using (Finset.sum_range_reflect g m)

/- accepted add_to_file helper 14 -/
lemma zmod_window_pos_sum
    (a b : ℕ) [NeZero (a+b)]
    (v : ZMod (a+b) → LaurentPolynomial ℤ) (r : ZMod (a+b)) :
    (∑ k ∈ Finset.Ico 1 (a+1),
      v ((r + (a : ZMod (a+b))) - (k : ZMod (a+b)))) =
    ∑ j ∈ Finset.range a, v (r + (j : ZMod (a+b))) := by
  let g : ℕ → LaurentPolynomial ℤ := fun z => v (r + (z : ZMod (a+b)))
  have hpoint :
      (∑ k ∈ Finset.Ico 1 (a+1),
        v ((r + (a : ZMod (a+b))) - (k : ZMod (a+b)))) =
      ∑ j ∈ Finset.range a, g (a - 1 - j) := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < a := Finset.mem_range.mp hj
    dsimp [g]
    congr 1
    rw [Nat.cast_sub (by omega : j ≤ a - 1)]
    rw [Nat.cast_sub (by omega : 1 ≤ a)]
    push_cast
    abel
  rw [hpoint]
  simpa [g] using (Finset.sum_range_reflect g a)

/- accepted add_to_file helper 15 -/
lemma zmod_window_pos_succ_sum
    (a b : ℕ) [NeZero (a+b)]
    (v : ZMod (a+b) → LaurentPolynomial ℤ) (r : ZMod (a+b)) :
    (∑ k ∈ Finset.Ico 1 (a+1),
      v ((r + (a : ZMod (a+b)) + 1) - (k : ZMod (a+b)))) =
    ∑ j ∈ Finset.range a, v (r + ((j + 1 : ℕ) : ZMod (a+b))) := by
  let g : ℕ → LaurentPolynomial ℤ := fun z => v (r + ((z + 1 : ℕ) : ZMod (a+b)))
  have hpoint :
      (∑ k ∈ Finset.Ico 1 (a+1),
        v ((r + (a : ZMod (a+b)) + 1) - (k : ZMod (a+b)))) =
      ∑ j ∈ Finset.range a, g (a - 1 - j) := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < a := Finset.mem_range.mp hj
    dsimp [g]
    have hnat : a - 1 - j + 1 = a - j := by omega
    rw [hnat]
    congr 1
    rw [Nat.cast_sub (by omega : j ≤ a)]
    push_cast
    abel
  rw [hpoint]
  simpa [g] using (Finset.sum_range_reflect g a)

/- accepted add_to_file helper 16 -/
lemma zmod_window_neg_sum
    (a b : ℕ) [NeZero (a+b)]
    (v : ZMod (a+b) → LaurentPolynomial ℤ) (r : ZMod (a+b)) :
    (∑ k ∈ Finset.Ico 1 (a+1), v (r - (k : ZMod (a+b)))) =
      ∑ j ∈ Finset.range a, v (r - ((j + 1 : ℕ) : ZMod (a+b))) := by
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  norm_num [Nat.add_comm]

/- accepted add_to_file helper 17 -/
lemma zmod_window_neg_succ_sum
    (a b : ℕ) [NeZero (a+b)]
    (v : ZMod (a+b) → LaurentPolynomial ℤ) (r : ZMod (a+b)) :
    (∑ k ∈ Finset.Ico 1 (a+1), v ((r + 1) - (k : ZMod (a+b)))) =
      ∑ j ∈ Finset.range a, v (r - (j : ZMod (a+b))) := by
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  push_cast
  abel

/- accepted add_to_file helper 18 -/
lemma laurentCirculantB_mulVec_factor
    (a b : ℕ) [NeZero (a + b)] (ha : 0 < a) (hab : a < b) (ε : ℤ)
    (v : ZMod (a+b) → LaurentPolynomial ℤ) (r : ZMod (a+b)) :
    let t : LaurentPolynomial ℤ := LaurentPolynomial.C ε * LaurentPolynomial.T 1
    let w : ZMod (a+b) → LaurentPolynomial ℤ := fun x =>
      ∑ k ∈ Finset.Ico 1 (a+1), v (x - (k : ZMod (a+b)))
    (laurentCirculantB a b ε).mulVec v r =
      (w (r + (a : ZMod (a+b))) - w r) +
        t * (w (r + (a : ZMod (a+b)) + 1) - w (r + 1)) := by
  intro t w
  have hdirect :
      (laurentCirculantB a b ε).mulVec v r =
      t * v (r - (((-(a : ℤ) : ℤ) : ZMod (a+b)))) +
      (1 + t) * (∑ k ∈ Finset.Ico 1 a,
        v (r - (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))) +
      (1 - t) * v r +
      (-1 - t) * (∑ k ∈ Finset.Ico 1 a,
        v (r - (k : ZMod (a+b)))) +
      (-1) * v (r - (a : ZMod (a+b))) := by
    let D : ZMod (a+b) → Matrix (ZMod (a+b)) (ZMod (a+b)) (LaurentPolynomial ℤ) :=
      fun c i j => if i - j = c then 1 else 0
    have hB := laurentCirculantB_eq_sum a b ha hab ε
    rw [show laurentCirculantB a b ε =
        t • D (((-(a : ℤ) : ℤ) : ZMod (a+b))) +
        (1 + t) • (∑ k ∈ Finset.Ico 1 a, D (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b))) +
        (1 - t) • D 0 +
        (-1 - t) • (∑ k ∈ Finset.Ico 1 a, D (k : ZMod (a+b))) +
        (-1) • D (a : ZMod (a+b)) from hB]
    simp [D, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sum_mulVec, zmod_diag_mulVec]
    rw [Matrix.neg_mulVec]
    change - Matrix.mulVec ((fun i j : ZMod (a+b) => if i - j = (a : ZMod (a+b)) then (1 : LaurentPolynomial ℤ) else 0) :
        Matrix (ZMod (a+b)) (ZMod (a+b)) (LaurentPolynomial ℤ)) v r = -v (r - (a : ZMod (a+b)))
    rw [zmod_diag_mulVec]
  have hNmid :
      (∑ k ∈ Finset.Ico 1 a,
        v (r - (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))) =
      ∑ j ∈ Finset.range (a-1), v (r + ((j + 1 : ℕ) : ZMod (a+b))) :=
    zmod_shift_interval_sum a b ha v r
  have hPmid :
      (∑ k ∈ Finset.Ico 1 a, v (r - (k : ZMod (a+b)))) =
      ∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b))) := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    norm_num [Nat.add_comm]
  have hS0 :
      (∑ j ∈ Finset.range a, v (r + (j : ZMod (a+b)))) =
      (∑ j ∈ Finset.range (a-1), v (r + ((j + 1 : ℕ) : ZMod (a+b)))) + v r := by
    have ha1 : a = (a - 1) + 1 := by omega
    have hrange : Finset.range a = Finset.range ((a - 1) + 1) := congrArg Finset.range ha1
    calc
      (∑ j ∈ Finset.range a, v (r + (j : ZMod (a+b))))
          = ∑ j ∈ Finset.range ((a - 1) + 1), v (r + (j : ZMod (a+b))) := by rw [hrange]
      _ = (∑ j ∈ Finset.range (a-1), v (r + ((j + 1 : ℕ) : ZMod (a+b)))) + v r := by
          rw [Finset.sum_range_succ']
          simp
  have hS1 :
      (∑ j ∈ Finset.range a, v (r + ((j + 1 : ℕ) : ZMod (a+b)))) =
      (∑ j ∈ Finset.range (a-1), v (r + ((j + 1 : ℕ) : ZMod (a+b)))) +
        v (r + (a : ZMod (a+b))) := by
    have ha1 : a = (a - 1) + 1 := by omega
    have hrange : Finset.range a = Finset.range ((a - 1) + 1) := congrArg Finset.range ha1
    calc
      (∑ j ∈ Finset.range a, v (r + ((j + 1 : ℕ) : ZMod (a+b))))
          = ∑ j ∈ Finset.range ((a - 1) + 1), v (r + ((j + 1 : ℕ) : ZMod (a+b))) := by rw [hrange]
      _ = (∑ j ∈ Finset.range (a-1), v (r + ((j + 1 : ℕ) : ZMod (a+b)))) +
            v (r + (a : ZMod (a+b))) := by
          rw [Finset.sum_range_succ]
          congr 1
          congr 1
          have hnat : a - 1 + 1 = a := by omega
          exact congrArg (fun z : ZMod (a+b) => r + z)
            (congrArg (fun n : ℕ => (n : ZMod (a+b))) hnat)
  have hT0 :
      (∑ j ∈ Finset.range a, v (r - ((j + 1 : ℕ) : ZMod (a+b)))) =
      (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) +
        v (r - (a : ZMod (a+b))) := by
    have ha1 : a = (a - 1) + 1 := by omega
    have hrange : Finset.range a = Finset.range ((a - 1) + 1) := congrArg Finset.range ha1
    calc
      (∑ j ∈ Finset.range a, v (r - ((j + 1 : ℕ) : ZMod (a+b))))
          = ∑ j ∈ Finset.range ((a - 1) + 1), v (r - ((j + 1 : ℕ) : ZMod (a+b))) := by rw [hrange]
      _ = (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) +
            v (r - (a : ZMod (a+b))) := by
          rw [Finset.sum_range_succ]
          congr 1
          congr 1
          have hnat : a - 1 + 1 = a := by omega
          exact congrArg (fun z : ZMod (a+b) => r - z)
            (congrArg (fun n : ℕ => (n : ZMod (a+b))) hnat)
  have hT1 :
      (∑ j ∈ Finset.range a, v (r - (j : ZMod (a+b)))) =
      v r + (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) := by
    have ha1 : a = (a - 1) + 1 := by omega
    have hrange : Finset.range a = Finset.range ((a - 1) + 1) := congrArg Finset.range ha1
    calc
      (∑ j ∈ Finset.range a, v (r - (j : ZMod (a+b))))
          = ∑ j ∈ Finset.range ((a - 1) + 1), v (r - (j : ZMod (a+b))) := by rw [hrange]
      _ = (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) + v r := by
          rw [Finset.sum_range_succ']
          simp
      _ = v r + (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) := by
          rw [add_comm]
  calc
    (laurentCirculantB a b ε).mulVec v r = _ := hdirect
    _ = (w (r + (a : ZMod (a+b))) - w r) +
        t * (w (r + (a : ZMod (a+b)) + 1) - w (r + 1)) := by
      dsimp [w]
      rw [zmod_window_pos_sum, zmod_window_neg_sum,
        zmod_window_pos_succ_sum, zmod_window_neg_succ_sum]
      rw [hS0, hS1, hT0, hT1, hNmid, hPmid]
      have hend : r - (((-(a : ℤ) : ℤ) : ZMod (a+b))) = r + (a : ZMod (a+b)) := by
        push_cast
        ring
      rw [hend]
      ring

/- accepted add_to_file helper 19 -/
lemma zmod_recur_eq_zero
    {m : ℕ} [NeZero m] {R : Type*} [CommRing R] [IsDomain R]
    {t : R} {x : ZMod m → R}
    (h : ∀ r : ZMod m, x r + t * x (r + 1) = 0)
    (ht : t ^ m ≠ (-1 : R) ^ m) :
    ∀ r : ZMod m, x r = 0 := by
  have hiter : ∀ (c : ℕ) (r : ZMod m),
      t ^ c * x (r + (c : ZMod m)) = (-1 : R) ^ c * x r := by
    intro c
    induction c with
    | zero =>
        intro r
        simp
    | succ c hc =>
        intro r
        have hstep : t * x ((r + (c : ZMod m)) + 1) = - x (r + (c : ZMod m)) :=
          eq_neg_of_add_eq_zero_right (h (r + (c : ZMod m)))
        have hindex : r + (((c + 1 : ℕ) : ZMod m)) = (r + (c : ZMod m)) + 1 := by
          simp [Nat.cast_add]
          ring
        calc
          t ^ (c + 1) * x (r + (((c + 1 : ℕ) : ZMod m)))
              = (t ^ c * t) * x ((r + (c : ZMod m)) + 1) := by
                rw [pow_succ, hindex]
          _ = t ^ c * (t * x ((r + (c : ZMod m)) + 1)) := by rw [mul_assoc]
          _ = t ^ c * (- x (r + (c : ZMod m))) := by rw [hstep]
          _ = - (t ^ c * x (r + (c : ZMod m))) := by ring
          _ = - ((-1 : R) ^ c * x r) := by rw [hc r]
          _ = (-1 : R) ^ (c + 1) * x r := by
                rw [pow_succ]
                ring
  intro r
  have hm := hiter m r
  have hcast : ((m : ZMod m) = 0) := by simp
  rw [hcast, add_zero] at hm
  have hprod : (t ^ m - (-1 : R) ^ m) * x r = 0 := by
    rw [sub_mul]
    rw [hm]
    ring
  have hcoeff : t ^ m - (-1 : R) ^ m ≠ 0 := sub_ne_zero.mpr ht
  exact (mul_eq_zero.mp hprod).resolve_left hcoeff

/- accepted add_to_file helper 20 -/
lemma laurent_neg_one_t_pow_ne
    (m n : ℕ) [NeZero m] :
    let t : LaurentPolynomial ℤ := LaurentPolynomial.C ((-1 : ℤ) ^ n) * LaurentPolynomial.T 1
    t ^ m ≠ (-1 : LaurentPolynomial ℤ) ^ m := by
  intro t
  have hε : ((-1 : ℤ) ^ n) ≠ 0 := by norm_num
  have hpow : t ^ m =
      LaurentPolynomial.C (((-1 : ℤ) ^ n) ^ m) * LaurentPolynomial.T (m : ℤ) := by
    dsimp [t]
    rw [mul_pow, map_pow, LaurentPolynomial.T_pow]
    simp
  have hdeg1 : (t ^ m).degree = (m : ℤ) := by
    rw [hpow]
    exact LaurentPolynomial.degree_C_mul_T (m : ℤ) (((-1 : ℤ) ^ n) ^ m)
      (pow_ne_zero m hε)
  have hconst : (-1 : LaurentPolynomial ℤ) ^ m =
      LaurentPolynomial.C (((-1 : ℤ) ^ m)) := by
    simp
  have hdeg2 : ((-1 : LaurentPolynomial ℤ) ^ m).degree = 0 := by
    rw [hconst]
    exact LaurentPolynomial.degree_C (pow_ne_zero m (by norm_num : (-1 : ℤ) ≠ 0))
  intro ht
  have hmdeg : (m : ℤ) = (0 : WithBot ℤ) := by
    calc
      (m : ℤ) = (t ^ m).degree := hdeg1.symm
      _ = ((-1 : LaurentPolynomial ℤ) ^ m).degree := congrArg LaurentPolynomial.degree ht
      _ = 0 := hdeg2
  have hmpos : (0 : WithBot ℤ) < (m : ℤ) := by
    have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    exact_mod_cast hm
  rw [hmdeg] at hmpos
  exact (lt_irrefl (0 : WithBot ℤ)) hmpos

/- accepted add_to_file helper 21 -/
lemma zmod_window_succ_sub
    (a b : ℕ) [NeZero (a+b)] (ha : 0 < a)
    (v : ZMod (a+b) → LaurentPolynomial ℤ) (r : ZMod (a+b)) :
    (∑ k ∈ Finset.Ico 1 (a+1), v ((r + 1) - (k : ZMod (a+b)))) -
      (∑ k ∈ Finset.Ico 1 (a+1), v (r - (k : ZMod (a+b)))) =
    v r - v (r - (a : ZMod (a+b))) := by
  rw [zmod_window_neg_succ_sum, zmod_window_neg_sum]
  have hT0 :
      (∑ j ∈ Finset.range a, v (r - ((j + 1 : ℕ) : ZMod (a+b)))) =
      (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) +
        v (r - (a : ZMod (a+b))) := by
    have ha1 : a = (a - 1) + 1 := by omega
    have hrange : Finset.range a = Finset.range ((a - 1) + 1) := congrArg Finset.range ha1
    calc
      (∑ j ∈ Finset.range a, v (r - ((j + 1 : ℕ) : ZMod (a+b))))
          = ∑ j ∈ Finset.range ((a - 1) + 1), v (r - ((j + 1 : ℕ) : ZMod (a+b))) := by rw [hrange]
      _ = (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) +
            v (r - (a : ZMod (a+b))) := by
          rw [Finset.sum_range_succ]
          congr 1
          congr 1
          have hnat : a - 1 + 1 = a := by omega
          exact congrArg (fun z : ZMod (a+b) => r - z)
            (congrArg (fun n : ℕ => (n : ZMod (a+b))) hnat)
  have hT1 :
      (∑ j ∈ Finset.range a, v (r - (j : ZMod (a+b)))) =
      v r + (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) := by
    have ha1 : a = (a - 1) + 1 := by omega
    have hrange : Finset.range a = Finset.range ((a - 1) + 1) := congrArg Finset.range ha1
    calc
      (∑ j ∈ Finset.range a, v (r - (j : ZMod (a+b))))
          = ∑ j ∈ Finset.range ((a - 1) + 1), v (r - (j : ZMod (a+b))) := by rw [hrange]
      _ = (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) + v r := by
          rw [Finset.sum_range_succ']
          simp
      _ = v r + (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) := by
          rw [add_comm]
  rw [hT0, hT1]
  ring

/- verified submission -/
theorem laurent_circulant_kernel
    (a b n : ℕ) (ha : 0 < a) (hab : a < b) (hab_coprime : Nat.Coprime a b)
    (hn : 3 ≤ n) :
    let _ : NeZero (a + b) := ⟨Nat.ne_of_gt (Nat.add_pos_left ha b)⟩
    let R := LaurentPolynomial ℤ
    let ε : ℤ := (-1) ^ n
    let q : R := LaurentPolynomial.T 1
    let B : Matrix (ZMod (a + b)) (ZMod (a + b)) R := fun i j =>
      if i - j = ((-(a : ℤ) : ℤ) : ZMod (a + b)) then
        LaurentPolynomial.C ε * q
      else if i - j ∈ (Finset.Ico 1 a).image
          (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a + b))) then
        1 + LaurentPolynomial.C ε * q
      else if i - j = 0 then
        1 - LaurentPolynomial.C ε * q
      else if i - j ∈ (Finset.Ico 1 a).image
          (fun k : ℕ => (k : ZMod (a + b))) then
        -1 - LaurentPolynomial.C ε * q
      else if i - j = (a : ZMod (a + b)) then
        -1
      else
        0
    ∀ v : ZMod (a + b) → R, B.mulVec v = 0 → ∀ i j, v i = v j := by
  intro hNe R ε q B v hv i j
  have hv' : (laurentCirculantB a b ε).mulVec v = 0 := by
    change B.mulVec v = 0
    exact hv
  let t : LaurentPolynomial ℤ := LaurentPolynomial.C ε * LaurentPolynomial.T 1
  let w : ZMod (a+b) → LaurentPolynomial ℤ := fun x =>
    ∑ k ∈ Finset.Ico 1 (a+1), v (x - (k : ZMod (a+b)))
  let x : ZMod (a+b) → LaurentPolynomial ℤ := fun r =>
    w (r + (a : ZMod (a+b))) - w r
  have hrec : ∀ r : ZMod (a+b), x r + t * x (r + 1) = 0 := by
    intro r
    have hfac := laurentCirculantB_mulVec_factor a b ha hab ε v r
    have hidx : r + (a : ZMod (a+b)) + 1 = (r + 1) + (a : ZMod (a+b)) := by abel
    calc
      x r + t * x (r + 1) =
          (w (r + (a : ZMod (a+b))) - w r) +
            t * (w (r + (a : ZMod (a+b)) + 1) - w (r + 1)) := by
            show (w (r + (a : ZMod (a+b))) - w r) +
                t * (w ((r + 1) + (a : ZMod (a+b))) - w (r + 1)) =
              (w (r + (a : ZMod (a+b))) - w r) +
                t * (w (r + (a : ZMod (a+b)) + 1) - w (r + 1))
            rw [hidx]
      _ = (laurentCirculantB a b ε).mulVec v r := hfac.symm
      _ = 0 := congrFun hv' r
  have ht : t ^ (a+b) ≠ (-1 : LaurentPolynomial ℤ) ^ (a+b) := by
    simpa [t, ε] using laurent_neg_one_t_pow_ne (a+b) n
  have hx : ∀ r : ZMod (a+b), x r = 0 :=
    zmod_recur_eq_zero hrec ht
  have hcop : Nat.Coprime a (a+b) := by
    exact Nat.coprime_self_add_right.2 hab_coprime
  have hwinv : ∀ r : ZMod (a+b), w r = w (r - (a : ZMod (a+b))) := by
    intro r
    have hxr := hx (r - (a : ZMod (a+b)))
    have h := sub_eq_zero.mp hxr
    have hidx : (r - (a : ZMod (a+b))) + (a : ZMod (a+b)) = r := by abel
    rw [hidx] at h
    exact h
  have hweq : ∀ i j : ZMod (a+b), w i = w j :=
    eq_of_forall_sub_natCast_zmod hcop hwinv
  have hvinv : ∀ r : ZMod (a+b), v r = v (r - (a : ZMod (a+b))) := by
    intro r
    have hdiff : w (r+1) - w r = 0 := sub_eq_zero.mpr (hweq (r+1) r)
    have htel := zmod_window_succ_sub a b ha v r
    have hzero : v r - v (r - (a : ZMod (a+b))) = 0 := by
      calc
        v r - v (r - (a : ZMod (a+b))) = w (r+1) - w r := by
          show v r - v (r - (a : ZMod (a+b))) =
            (∑ k ∈ Finset.Ico 1 (a+1), v ((r + 1) - (k : ZMod (a+b)))) -
              (∑ k ∈ Finset.Ico 1 (a+1), v (r - (k : ZMod (a+b))))
          exact htel.symm
        _ = 0 := hdiff
    exact sub_eq_zero.mp hzero
  exact eq_of_forall_sub_natCast_zmod hcop hvinv i j
