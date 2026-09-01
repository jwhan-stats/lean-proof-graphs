import Mathlib

/- accepted add_to_file helper 1 -/
lemma graded_proj_eq_of_mem
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {m n : ℕ} {x : T} (hx : x ∈ 𝒯 m) :
    GradedAlgebra.proj 𝒯 n x = if m = n then x else 0 := by
  classical
  rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem 𝒯 hx]
  by_cases h : m = n
  · subst h
    simp
  · simp [DirectSum.of_apply, h]

lemma graded_proj_self
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {n : ℕ} {x : T} (hx : x ∈ 𝒯 n) :
    GradedAlgebra.proj 𝒯 n x = x := by
  simpa using graded_proj_eq_of_mem 𝒯 (m := n) (n := n) hx

lemma graded_proj_mem
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (n : ℕ) (x : T) :
    GradedAlgebra.proj 𝒯 n x ∈ 𝒯 n := by
  classical
  rw [GradedAlgebra.proj_apply]
  exact (((DirectSum.decompose 𝒯) x) n).property

/- accepted add_to_file helper 2 -/
lemma graded_proj_eq_zero_of_mem_iSup_fin
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {n m : ℕ} (hnm : n ≤ m) {x : T}
    (hx : x ∈ ⨆ i : Fin n, 𝒯 (i : ℕ)) :
    GradedAlgebra.proj 𝒯 m x = 0 := by
  classical
  rw [Submodule.mem_iSup] at hx
  apply hx (LinearMap.ker (GradedAlgebra.proj 𝒯 m))
  intro i y hy
  rw [LinearMap.mem_ker, graded_proj_eq_of_mem 𝒯 hy]
  have hne : (i : ℕ) ≠ m := by
    omega
  simp [hne]

/- accepted add_to_file helper 3 -/
lemma graded_mem_iSup_fin_of_proj_eq_zero
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {n : ℕ} {x : T}
    (hx : ∀ m : ℕ, n ≤ m → GradedAlgebra.proj 𝒯 m x = 0) :
    x ∈ ⨆ i : Fin n, 𝒯 (i : ℕ) := by
  classical
  let d := DirectSum.decompose 𝒯 x
  have hsum : (∑ i ∈ d.support, ((d i) : T)) = x := by
    simpa [d] using DirectSum.sum_support_decompose 𝒯 x
  rw [← hsum]
  apply Submodule.sum_mem
  intro i hi
  have hlt : i < n := by
    by_contra hnot
    have hni : n ≤ i := Nat.le_of_not_gt hnot
    have hproj : GradedAlgebra.proj 𝒯 i x = 0 := hx i hni
    have hdi : d i = 0 := by
      apply Subtype.ext
      simpa [d, GradedAlgebra.proj_apply] using hproj
    have : i ∉ d.support := (DFinsupp.notMem_support_iff).2 hdi
    exact this hi
  exact le_iSup (fun j : Fin n => 𝒯 (j : ℕ)) ⟨i, hlt⟩ ((d i).property)

/- accepted add_to_file helper 4 -/
lemma graded_sub_proj_two_mem_iSup_fin_two
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {x : T} (hx : x ∈ ⨆ i : Fin 3, 𝒯 (i : ℕ)) :
    x - GradedAlgebra.proj 𝒯 2 x ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ) := by
  classical
  apply graded_mem_iSup_fin_of_proj_eq_zero 𝒯 (n := 2)
  intro m hm
  by_cases h2 : m = 2
  · subst h2
    rw [map_sub, graded_proj_self 𝒯 (n := 2)
      (x := GradedAlgebra.proj 𝒯 2 x) (graded_proj_mem 𝒯 2 x)]
    simp
  · have hm3 : 3 ≤ m := by omega
    have hxm : GradedAlgebra.proj 𝒯 m x = 0 :=
      graded_proj_eq_zero_of_mem_iSup_fin 𝒯 hm3 hx
    have hpm : GradedAlgebra.proj 𝒯 m (GradedAlgebra.proj 𝒯 2 x) = 0 := by
      rw [graded_proj_eq_of_mem 𝒯 (graded_proj_mem 𝒯 2 x)]
      have h2' : 2 ≠ m := fun h => h2 h.symm
      simp [h2']
    rw [map_sub, hxm, hpm, sub_zero]

/- accepted add_to_file helper 5 -/
lemma graded_proj_two_mul_of_mem_two
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (a s b : T) (hs : s ∈ 𝒯 2) :
    GradedAlgebra.proj 𝒯 2 (a * s * b) =
      GradedAlgebra.proj 𝒯 0 a * s * GradedAlgebra.proj 𝒯 0 b := by
  classical
  let da := DirectSum.decompose 𝒯 a
  let db := DirectSum.decompose 𝒯 b
  have ha : (∑ i ∈ da.support, ((da i) : T)) = a := by
    simpa [da] using DirectSum.sum_support_decompose 𝒯 a
  have hb : (∑ j ∈ db.support, ((db j) : T)) = b := by
    simpa [db] using DirectSum.sum_support_decompose 𝒯 b
  have hterm (i j : ℕ) :
      GradedAlgebra.proj 𝒯 2 (((da i : T) * s) * (db j : T)) =
        if i = 0 ∧ j = 0 then ((da i : T) * s) * (db j : T) else 0 := by
    have hmem : ((da i : T) * s) * (db j : T) ∈ 𝒯 (i + 2 + j) := by
      exact SetLike.mul_mem_graded
        (SetLike.mul_mem_graded (da i).property hs) (db j).property
    rw [graded_proj_eq_of_mem 𝒯 hmem]
    by_cases hij : i + 2 + j = 2
    · have hi : i = 0 := by omega
      have hj : j = 0 := by omega
      simp [hij, hi, hj]
    · have hnot : ¬ (i = 0 ∧ j = 0) := by
        rintro ⟨hi, hj⟩
        omega
      simp [hij, hnot]
  have hsum :
      (∑ i ∈ da.support, ∑ j ∈ db.support,
          GradedAlgebra.proj 𝒯 2 (((da i : T) * s) * (db j : T))) =
        ((da 0 : T) * s) * (db 0 : T) := by
    simp_rw [hterm]
    let f := fun i : ℕ => ∑ j ∈ db.support,
      (if i = 0 ∧ j = 0 then ((da i : T) * s) * (db j : T) else 0)
    have hinner : f 0 = ((da 0 : T) * s) * (db 0 : T) := by
      dsimp [f]
      apply Finset.sum_eq_single 0
      · intro j hj hj0
        simp [hj0]
      · intro h0
        have hdb : db 0 = 0 := (DFinsupp.notMem_support_iff).1 h0
        simp [hdb]
    calc
      (∑ i ∈ da.support, ∑ j ∈ db.support,
          if i = 0 ∧ j = 0 then ((da i : T) * s) * (db j : T) else 0)
          = f 0 := by
        apply Finset.sum_eq_single 0
        · intro i hi hi0
          dsimp [f]
          apply Finset.sum_eq_zero
          intro j hj
          simp [hi0]
        · intro h0
          dsimp [f]
          apply Finset.sum_eq_zero
          intro j hj
          have hda : da 0 = 0 := (DFinsupp.notMem_support_iff).1 h0
          by_cases hj0 : j = 0
          · simp [hj0, hda]
          · simp [hj0]
      _ = ((da 0 : T) * s) * (db 0 : T) := hinner
  calc
    GradedAlgebra.proj 𝒯 2 (a * s * b)
        = GradedAlgebra.proj 𝒯 2
            (∑ i ∈ da.support, ∑ j ∈ db.support,
              ((da i : T) * s) * (db j : T)) := by
          rw [← ha, ← hb]
          rw [Finset.sum_mul, Finset.sum_mul_sum]
    _ = ∑ i ∈ da.support,
          GradedAlgebra.proj 𝒯 2
            (∑ j ∈ db.support, ((da i : T) * s) * (db j : T)) := by
          rw [map_sum]
    _ = ∑ i ∈ da.support, ∑ j ∈ db.support,
          GradedAlgebra.proj 𝒯 2 (((da i : T) * s) * (db j : T)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [map_sum]
    _ = ((da 0 : T) * s) * (db 0 : T) := hsum
    _ = GradedAlgebra.proj 𝒯 0 a * s * GradedAlgebra.proj 𝒯 0 b := by
          have ha0 : GradedAlgebra.proj 𝒯 0 a = (da 0 : T) := by
            simp [GradedAlgebra.proj_apply, da]
          have hb0 : GradedAlgebra.proj 𝒯 0 b = (db 0 : T) := by
            simp [GradedAlgebra.proj_apply, db]
          rw [ha0, hb0]

/- accepted add_to_file helper 6 -/
lemma graded_span_degree_two_low_components
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (S : Set T) (hS : S ⊆ 𝒯 2)
    {x : T} (hx : x ∈ TwoSidedIdeal.span S) :
    ∀ i < 2, (DirectSum.decompose 𝒯 x) i = 0 := by
  classical
  refine TwoSidedIdeal.span_induction
    (p := fun x _ => ∀ i < 2, (DirectSum.decompose 𝒯 x) i = 0)
    ?_ ?_ ?_ ?_ ?_ ?_ hx
  · intro x hx i hi
    rw [DirectSum.decompose_of_mem 𝒯 (hS hx)]
    have hne : 2 ≠ i := by omega
    simp [DirectSum.of_apply, hne]
  · intro i hi
    simp
  · intro x y hx hy ihx ihy i hi
    simp [ihx i hi, ihy i hi]
  · intro x hx ihx i hi
    rw [DirectSum.decompose_neg]
    change - (((DirectSum.decompose 𝒯) x) i) = 0
    rw [ihx i hi, neg_zero]
  · intro a x hx ihx i hi
    rw [DirectSum.decompose_mul]
    exact mul_apply_eq_zero (A := 𝒯)
      (m := 0) (n := 2)
      (by intro j hj; omega)
      ihx hi
  · intro b x hx ihx i hi
    rw [DirectSum.decompose_mul]
    exact mul_apply_eq_zero (A := 𝒯)
      (m := 2) (n := 0)
      ihx
      (by intro j hj; omega)
      (by simpa using hi)

/- accepted add_to_file helper 7 -/
lemma graded_proj_two_mul_left_eq_of_low
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (a x : T)
    (hlow : ∀ i < 2, (DirectSum.decompose 𝒯 x) i = 0) :
    GradedAlgebra.proj 𝒯 2 (a * x) =
      GradedAlgebra.proj 𝒯 2 (a * GradedAlgebra.proj 𝒯 2 x) := by
  classical
  let d := DirectSum.decompose 𝒯 x
  have hsum : (∑ i ∈ d.support, ((d i) : T)) = x := by
    simpa [d] using DirectSum.sum_support_decompose 𝒯 x
  have hterm_zero_of_ne (i : ℕ) (hi : i ≠ 2) :
      GradedAlgebra.proj 𝒯 2 (a * (d i : T)) = 0 := by
    by_cases hlt : i < 2
    · have hdi : d i = 0 := by
        simpa [d] using hlow i hlt
      simp [hdi]
    · have hgt : 2 < i := by omega
      have hcomp : ((DirectSum.decompose 𝒯) (a * (d i : T))) 2 = 0 := by
        rw [DirectSum.decompose_mul, DirectSum.decompose_of_mem 𝒯 (d i).property]
        exact mul_apply_eq_zero (A := 𝒯)
          (m := 0) (n := i)
          (by intro j hj; omega)
          (by
            intro j hj
            have hne : i ≠ j := by omega
            simp [DirectSum.of_apply, hne])
          (by simpa using hgt)
      rw [GradedAlgebra.proj_apply, hcomp]
      rfl
  have hsum_single :
      (∑ i ∈ d.support, GradedAlgebra.proj 𝒯 2 (a * (d i : T))) =
        GradedAlgebra.proj 𝒯 2 (a * (d 2 : T)) := by
    apply Finset.sum_eq_single 2
    · intro i hi hi2
      exact hterm_zero_of_ne i hi2
    · intro h2
      have hd2 : d 2 = 0 := (DFinsupp.notMem_support_iff).1 h2
      simp [hd2]
  calc
    GradedAlgebra.proj 𝒯 2 (a * x)
        = GradedAlgebra.proj 𝒯 2 (a * ∑ i ∈ d.support, ((d i) : T)) := by
          rw [hsum]
    _ = ∑ i ∈ d.support, GradedAlgebra.proj 𝒯 2 (a * (d i : T)) := by
          rw [Finset.mul_sum, map_sum]
    _ = GradedAlgebra.proj 𝒯 2 (a * (d 2 : T)) := hsum_single
    _ = GradedAlgebra.proj 𝒯 2 (a * GradedAlgebra.proj 𝒯 2 x) := by
          rw [GradedAlgebra.proj_apply]
          simp [d]

lemma graded_proj_two_mul_right_eq_of_low
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (x b : T)
    (hlow : ∀ i < 2, (DirectSum.decompose 𝒯 x) i = 0) :
    GradedAlgebra.proj 𝒯 2 (x * b) =
      GradedAlgebra.proj 𝒯 2 (GradedAlgebra.proj 𝒯 2 x * b) := by
  classical
  let d := DirectSum.decompose 𝒯 x
  have hsum : (∑ i ∈ d.support, ((d i) : T)) = x := by
    simpa [d] using DirectSum.sum_support_decompose 𝒯 x
  have hterm_zero_of_ne (i : ℕ) (hi : i ≠ 2) :
      GradedAlgebra.proj 𝒯 2 ((d i : T) * b) = 0 := by
    by_cases hlt : i < 2
    · have hdi : d i = 0 := by
        simpa [d] using hlow i hlt
      simp [hdi]
    · have hgt : 2 < i := by omega
      have hcomp : ((DirectSum.decompose 𝒯) ((d i : T) * b)) 2 = 0 := by
        rw [DirectSum.decompose_mul, DirectSum.decompose_of_mem 𝒯 (d i).property]
        exact mul_apply_eq_zero (A := 𝒯)
          (m := i) (n := 0)
          (by
            intro j hj
            have hne : i ≠ j := by omega
            simp [DirectSum.of_apply, hne])
          (by intro j hj; omega)
          (by simpa using hgt)
      rw [GradedAlgebra.proj_apply, hcomp]
      rfl
  have hsum_single :
      (∑ i ∈ d.support, GradedAlgebra.proj 𝒯 2 ((d i : T) * b)) =
        GradedAlgebra.proj 𝒯 2 ((d 2 : T) * b) := by
    apply Finset.sum_eq_single 2
    · intro i hi hi2
      exact hterm_zero_of_ne i hi2
    · intro h2
      have hd2 : d 2 = 0 := (DFinsupp.notMem_support_iff).1 h2
      simp [hd2]
  calc
    GradedAlgebra.proj 𝒯 2 (x * b)
        = GradedAlgebra.proj 𝒯 2 ((∑ i ∈ d.support, ((d i) : T)) * b) := by
          rw [hsum]
    _ = ∑ i ∈ d.support, GradedAlgebra.proj 𝒯 2 ((d i : T) * b) := by
          rw [Finset.sum_mul, map_sum]
    _ = GradedAlgebra.proj 𝒯 2 ((d 2 : T) * b) := hsum_single
    _ = GradedAlgebra.proj 𝒯 2 (GradedAlgebra.proj 𝒯 2 x * b) := by
          rw [GradedAlgebra.proj_apply]
          simp [d]

/- accepted add_to_file helper 8 -/
lemma graded_degree_two_mem_span_of_degree_two_generators
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (S : Set T) (hS : S ⊆ 𝒯 2)
    {z : T} (hz₂ : z ∈ 𝒯 2)
    (hz : z ∈ TwoSidedIdeal.span S) :
    z ∈ AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ s ∈ S, ∃ b ∈ 𝒯 0, x = a * s * b} := by
  classical
  let C : AddSubgroup T := AddSubgroup.closure
    {x : T | ∃ a ∈ 𝒯 0, ∃ s ∈ S, ∃ b ∈ 𝒯 0, x = a * s * b}
  have hproj_left (a c : T) (hc : c ∈ C) :
      GradedAlgebra.proj 𝒯 2 (a * c) ∈ C := by
    induction hc using AddSubgroup.closure_induction with
    | mem x hx =>
        rcases hx with ⟨u, hu, s, hsS, v, hv, rfl⟩
        have hrewrite :
            GradedAlgebra.proj 𝒯 2 (a * (u * s * v)) =
              GradedAlgebra.proj 𝒯 0 (a * u) * s * GradedAlgebra.proj 𝒯 0 v := by
          simpa [mul_assoc] using
            graded_proj_two_mul_of_mem_two 𝒯 (a * u) s v (hS hsS)
        rw [hrewrite]
        apply AddSubgroup.subset_closure
        exact ⟨GradedAlgebra.proj 𝒯 0 (a * u), graded_proj_mem 𝒯 0 (a * u),
          s, hsS, GradedAlgebra.proj 𝒯 0 v, graded_proj_mem 𝒯 0 v, rfl⟩
    | zero =>
        simp
    | add x y hx hy ihx ihy =>
        rw [mul_add, map_add]
        exact C.add_mem ihx ihy
    | neg x hx ihx =>
        rw [mul_neg, map_neg]
        exact C.neg_mem ihx
  have hproj_right (c b : T) (hc : c ∈ C) :
      GradedAlgebra.proj 𝒯 2 (c * b) ∈ C := by
    induction hc using AddSubgroup.closure_induction with
    | mem x hx =>
        rcases hx with ⟨u, hu, s, hsS, v, hv, rfl⟩
        have hrewrite :
            GradedAlgebra.proj 𝒯 2 ((u * s * v) * b) =
              GradedAlgebra.proj 𝒯 0 u * s * GradedAlgebra.proj 𝒯 0 (v * b) := by
          simpa [mul_assoc] using
            graded_proj_two_mul_of_mem_two 𝒯 u s (v * b) (hS hsS)
        rw [hrewrite]
        apply AddSubgroup.subset_closure
        exact ⟨GradedAlgebra.proj 𝒯 0 u, graded_proj_mem 𝒯 0 u,
          s, hsS, GradedAlgebra.proj 𝒯 0 (v * b), graded_proj_mem 𝒯 0 (v * b), rfl⟩
    | zero =>
        simp
    | add x y hx hy ihx ihy =>
        rw [add_mul, map_add]
        exact C.add_mem ihx ihy
    | neg x hx ihx =>
        rw [neg_mul, map_neg]
        exact C.neg_mem ihx
  have hproj : GradedAlgebra.proj 𝒯 2 z ∈ C := by
    refine TwoSidedIdeal.span_induction
      (p := fun x _ => GradedAlgebra.proj 𝒯 2 x ∈ C)
      ?_ ?_ ?_ ?_ ?_ ?_ hz
    · intro x hx
      rw [graded_proj_self 𝒯 (hS hx)]
      apply AddSubgroup.subset_closure
      exact ⟨1, SetLike.GradedOne.one_mem, x, hx, 1, SetLike.GradedOne.one_mem, by simp⟩
    · simp
    · intro x y hx hy ihx ihy
      rw [map_add]
      exact C.add_mem ihx ihy
    · intro x hx ihx
      rw [map_neg]
      exact C.neg_mem ihx
    · intro a x hx ihx
      rw [graded_proj_two_mul_left_eq_of_low 𝒯 a x
        (graded_span_degree_two_low_components 𝒯 S hS hx)]
      exact hproj_left a (GradedAlgebra.proj 𝒯 2 x) ihx
    · intro b x hx ihx
      rw [graded_proj_two_mul_right_eq_of_low 𝒯 x b
        (graded_span_degree_two_low_components 𝒯 S hS hx)]
      exact hproj_right (GradedAlgebra.proj 𝒯 2 x) b ihx
  rwa [graded_proj_self 𝒯 hz₂] at hproj

/- accepted add_to_file helper 9 -/
lemma graded_proj_mul_left_of_mem_zero
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {a b : T} (ha : a ∈ 𝒯 0) (i : ℕ) :
    GradedAlgebra.proj 𝒯 i (a * b) =
      a * GradedAlgebra.proj 𝒯 i b := by
  classical
  rw [GradedAlgebra.proj_apply, GradedAlgebra.proj_apply,
    DirectSum.coe_decompose_mul_of_left_mem_zero 𝒯 ha]

lemma graded_proj_mul_right_of_mem_zero
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {a b : T} (hb : b ∈ 𝒯 0) (i : ℕ) :
    GradedAlgebra.proj 𝒯 i (a * b) =
      GradedAlgebra.proj 𝒯 i a * b := by
  classical
  rw [GradedAlgebra.proj_apply, GradedAlgebra.proj_apply,
    DirectSum.coe_decompose_mul_of_right_mem_zero 𝒯 hb]

lemma graded_iSup_fin_two_mul_mem_zero
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {a d b : T} (ha : a ∈ 𝒯 0) (hb : b ∈ 𝒯 0)
    (hd : d ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ)) :
    a * d * b ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ) := by
  classical
  apply graded_mem_iSup_fin_of_proj_eq_zero 𝒯 (n := 2)
  intro m hm
  rw [graded_proj_mul_right_of_mem_zero 𝒯 hb,
    graded_proj_mul_left_of_mem_zero 𝒯 ha,
    graded_proj_eq_zero_of_mem_iSup_fin 𝒯 hm hd]
  simp

/- accepted add_to_file helper 10 -/
lemma graded_homogeneous_mem_span_degree_two_eq_zero_of_lt
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (S : Set T) (hS : S ⊆ 𝒯 2)
    {n : ℕ} (hn : n < 2) {x : T}
    (hxn : x ∈ 𝒯 n)
    (hx : x ∈ TwoSidedIdeal.span S) :
    x = 0 := by
  classical
  have hd : (DirectSum.decompose 𝒯 x) n = 0 :=
    graded_span_degree_two_low_components 𝒯 S hS hx n hn
  have hp : GradedAlgebra.proj 𝒯 n x = 0 := by
    rw [GradedAlgebra.proj_apply, hd]
    rfl
  rwa [graded_proj_self 𝒯 hxn] at hp

lemma graded_sub_proj_one_mem_iSup_fin_one
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {x : T} (hx : x ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ)) :
    x - GradedAlgebra.proj 𝒯 1 x ∈ ⨆ i : Fin 1, 𝒯 (i : ℕ) := by
  classical
  apply graded_mem_iSup_fin_of_proj_eq_zero 𝒯 (n := 1)
  intro m hm
  by_cases h1 : m = 1
  · subst h1
    rw [map_sub, graded_proj_self 𝒯 (n := 1)
      (x := GradedAlgebra.proj 𝒯 1 x) (graded_proj_mem 𝒯 1 x)]
    simp
  · have hm2 : 2 ≤ m := by omega
    have hxm : GradedAlgebra.proj 𝒯 m x = 0 :=
      graded_proj_eq_zero_of_mem_iSup_fin 𝒯 hm2 hx
    have hpm : GradedAlgebra.proj 𝒯 m (GradedAlgebra.proj 𝒯 1 x) = 0 := by
      rw [graded_proj_eq_of_mem 𝒯 (graded_proj_mem 𝒯 1 x)]
      have h1' : 1 ≠ m := fun h => h1 h.symm
      simp [h1']
    rw [map_sub, hxm, hpm, sub_zero]

lemma graded_mem_iSup_fin_one
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {x : T} (hx : x ∈ ⨆ i : Fin 1, 𝒯 (i : ℕ)) :
    x ∈ 𝒯 0 := by
  rw [Submodule.mem_iSup] at hx
  apply hx (𝒯 0)
  intro i
  have hi : i = 0 := by omega
  subst hi
  exact le_rfl

/- accepted add_to_file helper 11 -/
lemma pbw_low_ideal_eq_zero
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (P : Set T) (I : TwoSidedIdeal T)
    (hPI : TwoSidedIdeal.span P = I)
    (hPpbw : ∀ (n : ℕ) (x : T), x ∈ 𝒯 n →
      (x ∈ TwoSidedIdeal.span ((GradedAlgebra.proj 𝒯 2) '' P) ↔
        ∃ y ∈ I, x - y ∈ (⨆ i : Fin n, 𝒯 (i : ℕ))))
    {z : T} (hzI : z ∈ I)
    (hzF : z ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ)) :
    z = 0 := by
  classical
  let J : TwoSidedIdeal T :=
    TwoSidedIdeal.span ((GradedAlgebra.proj 𝒯 2) '' P)
  have hJhom : ((GradedAlgebra.proj 𝒯 2) '' P : Set T) ⊆ 𝒯 2 := by
    rintro x ⟨p, hp, rfl⟩
    exact graded_proj_mem 𝒯 2 p
  have hz₁ : GradedAlgebra.proj 𝒯 1 z = 0 := by
    have hz₁mem : GradedAlgebra.proj 𝒯 1 z ∈ 𝒯 1 :=
      graded_proj_mem 𝒯 1 z
    have hsub : z - GradedAlgebra.proj 𝒯 1 z ∈ ⨆ i : Fin 1, 𝒯 (i : ℕ) :=
      graded_sub_proj_one_mem_iSup_fin_one 𝒯 hzF
    have hdiff : GradedAlgebra.proj 𝒯 1 z - z ∈ ⨆ i : Fin 1, 𝒯 (i : ℕ) := by
      have hneg := (⨆ i : Fin 1, 𝒯 (i : ℕ)).neg_mem hsub
      convert hneg using 1
      abel
    have hz₁J : GradedAlgebra.proj 𝒯 1 z ∈ J := by
      exact (hPpbw 1 (GradedAlgebra.proj 𝒯 1 z) hz₁mem).2 ⟨z, hzI, hdiff⟩
    exact graded_homogeneous_mem_span_degree_two_eq_zero_of_lt 𝒯
      ((GradedAlgebra.proj 𝒯 2) '' P) hJhom (by norm_num : 1 < 2)
      hz₁mem hz₁J
  have hzF₁ : z ∈ ⨆ i : Fin 1, 𝒯 (i : ℕ) := by
    have hsub : z - GradedAlgebra.proj 𝒯 1 z ∈ ⨆ i : Fin 1, 𝒯 (i : ℕ) :=
      graded_sub_proj_one_mem_iSup_fin_one 𝒯 hzF
    simpa [hz₁] using hsub
  have hz₀ : z ∈ 𝒯 0 := graded_mem_iSup_fin_one 𝒯 hzF₁
  have hzJ : z ∈ J := by
    exact (hPpbw 0 z hz₀).2 ⟨z, hzI, by simp⟩
  exact graded_homogeneous_mem_span_degree_two_eq_zero_of_lt 𝒯
    ((GradedAlgebra.proj 𝒯 2) '' P) hJhom (by norm_num : 0 < 2)
    hz₀ hzJ

/- accepted add_to_file helper 12 -/
lemma tzero_bimodule_closure_subset_ideal
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (S : Set T) (I : TwoSidedIdeal T) (hS : S ⊆ I)
    {x : T}
    (hx : x ∈ AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ s ∈ S, ∃ b ∈ 𝒯 0, x = a * s * b}) :
    x ∈ I := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
      rcases hx with ⟨a, ha, s, hs, b, hb, rfl⟩
      exact TwoSidedIdeal.mul_mem_right I (a * s) b
        (TwoSidedIdeal.mul_mem_left I a s (hS hs))
  | zero =>
      exact TwoSidedIdeal.zero_mem I
  | add x y hx hy ihx ihy =>
      exact TwoSidedIdeal.add_mem I ihx ihy
  | neg x hx ihx =>
      exact TwoSidedIdeal.neg_mem I ihx

/- accepted add_to_file helper 13 -/
lemma degree_two_generator_closure_approx
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (Q : Set T)
    (hQ₂ : Q ⊆ (⨆ i : Fin 3, 𝒯 (i : ℕ)))
    {x : T}
    (hx : x ∈ AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ ((GradedAlgebra.proj 𝒯 2) '' Q),
        ∃ b ∈ 𝒯 0, x = a * q * b}) :
    ∃ y ∈ AddSubgroup.closure
        {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b},
      x - y ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ) := by
  classical
  let B : AddSubgroup T := AddSubgroup.closure
    {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b}
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
      rcases hx with ⟨a, ha, r, hr, b, hb, rfl⟩
      rcases hr with ⟨q, hq, rfl⟩
      refine ⟨a * q * b, ?_, ?_⟩
      · apply AddSubgroup.subset_closure
        exact ⟨a, ha, q, hq, b, hb, rfl⟩
      · have hlow : GradedAlgebra.proj 𝒯 2 q - q ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ) := by
          have hqF : q ∈ ⨆ i : Fin 3, 𝒯 (i : ℕ) := by
            have hqFset := hQ₂ hq
            rw [Set.iSup_eq_iUnion] at hqFset
            rw [Set.mem_iUnion] at hqFset
            rcases hqFset with ⟨i, hqi⟩
            exact le_iSup (fun j : Fin 3 => 𝒯 (j : ℕ)) i hqi
          have h := graded_sub_proj_two_mem_iSup_fin_two 𝒯 hqF
          have hneg := (⨆ i : Fin 2, 𝒯 (i : ℕ)).neg_mem h
          convert hneg using 1
          abel
        have := graded_iSup_fin_two_mul_mem_zero 𝒯 ha hb hlow
        convert this using 1
        rw [mul_sub, sub_mul]
  | zero =>
      exact ⟨0, B.zero_mem, by simp⟩
  | add x y hx hy ihx ihy =>
      rcases ihx with ⟨x', hx'B, hxx'⟩
      rcases ihy with ⟨y', hy'B, hyy'⟩
      refine ⟨x' + y', B.add_mem hx'B hy'B, ?_⟩
      have hsum := (⨆ i : Fin 2, 𝒯 (i : ℕ)).add_mem hxx' hyy'
      convert hsum using 1
      abel
  | neg x hx ihx =>
      rcases ihx with ⟨x', hx'B, hxx'⟩
      refine ⟨-x', B.neg_mem hx'B, ?_⟩
      have hneg := (⨆ i : Fin 2, 𝒯 (i : ℕ)).neg_mem hxx'
      convert hneg using 1
      abel

/- accepted add_to_file helper 14 -/
lemma pbw_generators_subset_tzero_bimodule_closure
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (P Q : Set T) (I : TwoSidedIdeal T)
    (hP₂ : P ⊆ (⨆ i : Fin 3, 𝒯 (i : ℕ)))
    (hQ₂ : Q ⊆ (⨆ i : Fin 3, 𝒯 (i : ℕ)))
    (hPI : TwoSidedIdeal.span P = I)
    (hQI : TwoSidedIdeal.span Q = I)
    (hPpbw : ∀ (n : ℕ) (x : T), x ∈ 𝒯 n →
      (x ∈ TwoSidedIdeal.span ((GradedAlgebra.proj 𝒯 2) '' P) ↔
        ∃ y ∈ I, x - y ∈ (⨆ i : Fin n, 𝒯 (i : ℕ))))
    (hQpbw : ∀ (n : ℕ) (x : T), x ∈ 𝒯 n →
      (x ∈ TwoSidedIdeal.span ((GradedAlgebra.proj 𝒯 2) '' Q) ↔
        ∃ y ∈ I, x - y ∈ (⨆ i : Fin n, 𝒯 (i : ℕ)))) :
    P ⊆ AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b} := by
  classical
  intro p hp
  have hpFset := hP₂ hp
  have hpF : p ∈ ⨆ i : Fin 3, 𝒯 (i : ℕ) := by
    rw [Set.iSup_eq_iUnion] at hpFset
    rw [Set.mem_iUnion] at hpFset
    rcases hpFset with ⟨i, hpi⟩
    exact le_iSup (fun j : Fin 3 => 𝒯 (j : ℕ)) i hpi
  have hpI : p ∈ I := by
    have h : p ∈ TwoSidedIdeal.span P := TwoSidedIdeal.subset_span hp
    rwa [hPI] at h
  have hp₂mem : GradedAlgebra.proj 𝒯 2 p ∈ 𝒯 2 :=
    graded_proj_mem 𝒯 2 p
  have hp₂diff : GradedAlgebra.proj 𝒯 2 p - p ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ) := by
    have h := graded_sub_proj_two_mem_iSup_fin_two 𝒯 hpF
    have hneg := (⨆ i : Fin 2, 𝒯 (i : ℕ)).neg_mem h
    convert hneg using 1
    abel
  have hp₂J : GradedAlgebra.proj 𝒯 2 p ∈
      TwoSidedIdeal.span ((GradedAlgebra.proj 𝒯 2) '' Q) := by
    exact (hQpbw 2 (GradedAlgebra.proj 𝒯 2 p) hp₂mem).2 ⟨p, hpI, hp₂diff⟩
  have hQhom : ((GradedAlgebra.proj 𝒯 2) '' Q : Set T) ⊆ 𝒯 2 := by
    rintro x ⟨q, hq, rfl⟩
    exact graded_proj_mem 𝒯 2 q
  have hp₂C : GradedAlgebra.proj 𝒯 2 p ∈ AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ ((GradedAlgebra.proj 𝒯 2) '' Q),
        ∃ b ∈ 𝒯 0, x = a * q * b} := by
    exact graded_degree_two_mem_span_of_degree_two_generators 𝒯
      ((GradedAlgebra.proj 𝒯 2) '' Q) hQhom hp₂mem hp₂J
  rcases degree_two_generator_closure_approx 𝒯 Q hQ₂ hp₂C with
    ⟨y, hyB, hp₂y⟩
  have hpyF : p - y ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ) := by
    have hpminus : p - GradedAlgebra.proj 𝒯 2 p ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ) :=
      graded_sub_proj_two_mem_iSup_fin_two 𝒯 hpF
    have hsum := (⨆ i : Fin 2, 𝒯 (i : ℕ)).add_mem hpminus hp₂y
    convert hsum using 1
    abel
  have hQIset : Q ⊆ I := by
    intro q hq
    have h : q ∈ TwoSidedIdeal.span Q := TwoSidedIdeal.subset_span hq
    rwa [hQI] at h
  have hyI : y ∈ I :=
    tzero_bimodule_closure_subset_ideal 𝒯 Q I hQIset hyB
  have hpyI : p - y ∈ I := TwoSidedIdeal.sub_mem I hpI hyI
  have hpy : p - y = 0 := pbw_low_ideal_eq_zero 𝒯 P I hPI hPpbw hpyI hpyF
  have hp_eq : p = y := sub_eq_zero.mp hpy
  rwa [hp_eq]

/- accepted add_to_file helper 15 -/
lemma tzero_bimodule_closure_mul_mem_zero
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (S : Set T) {a x b : T} (ha : a ∈ 𝒯 0) (hb : b ∈ 𝒯 0)
    (hx : x ∈ AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ s ∈ S, ∃ b ∈ 𝒯 0, x = a * s * b}) :
    a * x * b ∈ AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ s ∈ S, ∃ b ∈ 𝒯 0, x = a * s * b} := by
  let C : AddSubgroup T := AddSubgroup.closure
    {x : T | ∃ a ∈ 𝒯 0, ∃ s ∈ S, ∃ b ∈ 𝒯 0, x = a * s * b}
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
      rcases hx with ⟨u, hu, s, hs, v, hv, rfl⟩
      apply AddSubgroup.subset_closure
      refine ⟨a * u, ?_, s, hs, v * b, ?_, ?_⟩
      · exact SetLike.mul_mem_graded ha hu
      · exact SetLike.mul_mem_graded hv hb
      · simp [mul_assoc]
  | zero =>
      simp
  | add x y hx hy ihx ihy =>
      rw [mul_add, add_mul]
      exact C.add_mem ihx ihy
  | neg x hx ihx =>
      rw [mul_neg, neg_mul]
      exact C.neg_mem ihx

lemma tzero_bimodule_closure_le_of_generators_subset
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (P Q : Set T)
    (h : P ⊆ AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b}) :
    AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ p ∈ P, ∃ b ∈ 𝒯 0, x = a * p * b} ≤
    AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b} := by
  rw [AddSubgroup.closure_le]
  intro x hx
  rcases hx with ⟨a, ha, p, hp, b, hb, rfl⟩
  exact tzero_bimodule_closure_mul_mem_zero 𝒯 Q ha hb (h hp)

/- verified submission -/
theorem pbw_filtered_quadratic_relations_unique
    (k T : Type*) [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (P Q : Set T) (I : TwoSidedIdeal T)
    (hP₂ : P ⊆ (⨆ i : Fin 3, 𝒯 (i : ℕ)))
    (hQ₂ : Q ⊆ (⨆ i : Fin 3, 𝒯 (i : ℕ)))
    (hPI : TwoSidedIdeal.span P = I)
    (hQI : TwoSidedIdeal.span Q = I)
    (hPpbw : ∀ (n : ℕ) (x : T), x ∈ 𝒯 n →
      (x ∈ TwoSidedIdeal.span ((GradedAlgebra.proj 𝒯 2) '' P) ↔
        ∃ y ∈ I, x - y ∈ (⨆ i : Fin n, 𝒯 (i : ℕ))))
    (hQpbw : ∀ (n : ℕ) (x : T), x ∈ 𝒯 n →
      (x ∈ TwoSidedIdeal.span ((GradedAlgebra.proj 𝒯 2) '' Q) ↔
        ∃ y ∈ I, x - y ∈ (⨆ i : Fin n, 𝒯 (i : ℕ)))) :
    AddSubgroup.closure {x : T | ∃ a ∈ 𝒯 0, ∃ p ∈ P, ∃ b ∈ 𝒯 0, x = a * p * b} =
        AddSubgroup.closure {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b} ∧
      (((∃ M : AddSubgroup T, (M : Set T) = P ∧
          (∀ (a : 𝒯 0) (x : T), x ∈ M → (a : T) * x ∈ M) ∧
          (∀ (a : 𝒯 0) (x : T), x ∈ M → x * (a : T) ∈ M)) ∧
        (∃ N : AddSubgroup T, (N : Set T) = Q ∧
          (∀ (a : 𝒯 0) (x : T), x ∈ N → (a : T) * x ∈ N) ∧
          (∀ (a : 𝒯 0) (x : T), x ∈ N → x * (a : T) ∈ N))) → P = Q) := by
  classical
  let A : AddSubgroup T := AddSubgroup.closure
    {x : T | ∃ a ∈ 𝒯 0, ∃ p ∈ P, ∃ b ∈ 𝒯 0, x = a * p * b}
  let B : AddSubgroup T := AddSubgroup.closure
    {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b}
  have hPsub : P ⊆ B := by
    simpa [B] using pbw_generators_subset_tzero_bimodule_closure
      𝒯 P Q I hP₂ hQ₂ hPI hQI hPpbw hQpbw
  have hQsub : Q ⊆ A := by
    simpa [A] using pbw_generators_subset_tzero_bimodule_closure
      𝒯 Q P I hQ₂ hP₂ hQI hPI hQpbw hPpbw
  have hAleB : A ≤ B := by
    simpa [A, B] using tzero_bimodule_closure_le_of_generators_subset 𝒯 P Q hPsub
  have hBleA : B ≤ A := by
    simpa [A, B] using tzero_bimodule_closure_le_of_generators_subset 𝒯 Q P hQsub
  have hAB : A = B := le_antisymm hAleB hBleA
  constructor
  · simpa [A, B] using hAB
  · intro hclosed
    rcases hclosed with ⟨hPclosed, hQclosed⟩
    rcases hPclosed with ⟨M, hMP, hMleft, hMright⟩
    rcases hQclosed with ⟨N, hNQ, hNleft, hNright⟩
    have hgenP : {x : T | ∃ a ∈ 𝒯 0, ∃ p ∈ P, ∃ b ∈ 𝒯 0, x = a * p * b} ⊆
        (M : Set T) := by
      intro x hx
      rcases hx with ⟨a, ha, p, hp, b, hb, rfl⟩
      have hpM : p ∈ M := by
        have hpMset : p ∈ (M : Set T) := by
          rw [hMP]
          exact hp
        exact hpMset
      exact hMright ⟨b, hb⟩ ((a : T) * p)
        (hMleft ⟨a, ha⟩ p hpM)
    have hAleM : A ≤ M := by
      have h : AddSubgroup.closure
          {x : T | ∃ a ∈ 𝒯 0, ∃ p ∈ P, ∃ b ∈ 𝒯 0, x = a * p * b} ≤ M :=
        (AddSubgroup.closure_le M).2 hgenP
      simpa [A] using h
    have hMleA : M ≤ A := by
      intro x hx
      have hxP : x ∈ P := by
        have hxset : x ∈ (M : Set T) := hx
        rw [hMP] at hxset
        exact hxset
      apply AddSubgroup.subset_closure
      exact ⟨1, SetLike.GradedOne.one_mem, x, hxP, 1,
        SetLike.GradedOne.one_mem, by simp⟩
    have hAM : A = M := le_antisymm hAleM hMleA
    have hgenQ : {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b} ⊆
        (N : Set T) := by
      intro x hx
      rcases hx with ⟨a, ha, q, hq, b, hb, rfl⟩
      have hqN : q ∈ N := by
        have hqNset : q ∈ (N : Set T) := by
          rw [hNQ]
          exact hq
        exact hqNset
      exact hNright ⟨b, hb⟩ ((a : T) * q)
        (hNleft ⟨a, ha⟩ q hqN)
    have hBleN : B ≤ N := by
      have h : AddSubgroup.closure
          {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b} ≤ N :=
        (AddSubgroup.closure_le N).2 hgenQ
      simpa [B] using h
    have hNleB : N ≤ B := by
      intro x hx
      have hxQ : x ∈ Q := by
        have hxset : x ∈ (N : Set T) := hx
        rw [hNQ] at hxset
        exact hxset
      apply AddSubgroup.subset_closure
      exact ⟨1, SetLike.GradedOne.one_mem, x, hxQ, 1,
        SetLike.GradedOne.one_mem, by simp⟩
    have hBN : B = N := le_antisymm hBleN hNleB
    have hPAsets : P = (A : Set T) := by
      calc
        P = (M : Set T) := hMP.symm
        _ = (A : Set T) := congrArg (fun X : AddSubgroup T => (X : Set T)) hAM.symm
    have hQBsets : Q = (B : Set T) := by
      calc
        Q = (N : Set T) := hNQ.symm
        _ = (B : Set T) := congrArg (fun X : AddSubgroup T => (X : Set T)) hBN.symm
    calc
      P = (A : Set T) := hPAsets
      _ = (B : Set T) := congrArg (fun X : AddSubgroup T => (X : Set T)) hAB
      _ = Q := hQBsets.symm
