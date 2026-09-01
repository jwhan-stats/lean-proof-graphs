import Mathlib

/- accepted add_to_file helper 1 -/
lemma graded_exists_finset_decomp
    (G K A : Type*) [Group G] [Field K] [AddCommGroup A] [Module K A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤) (z : A) :
    ∃ s : Finset G, ∃ f : G → A,
      (∀ i ∈ s, f i ∈ 𝒜 i) ∧ ∑ i ∈ s, f i = z := by
  classical
  let e := h_direct.1.linearEquiv h_direct.2
  let d : Π₀ i : G, 𝒜 i := e.symm z
  refine ⟨d.support, fun i => (d i : A), ?_, ?_⟩
  · intro i hi
    exact (d i).property
  · have hz : e d = z := e.apply_symm_apply z
    rw [iSupIndep.linearEquiv_apply, DFinsupp.sumAddHom_apply] at hz
    simpa [DFinsupp.sum, d] using hz

/- accepted add_to_file helper 2 -/
namespace GradedSimpleProof

def sandwichLeftAnn
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A) (a : A) : Submodule K A where
  carrier := {y | ∀ (k : G) (x : A), x ∈ 𝒜 k → a * x * y = 0}
  zero_mem' := by
    intro k x hx
    simp
  add_mem' {y z} hy hz := by
    intro k x hx
    rw [mul_add, hy k x hx, hz k x hx, add_zero]
  smul_mem' c {y} hy := by
    intro k x hx
    rw [mul_smul_comm, hy k x hx, smul_zero]

end GradedSimpleProof

/- accepted add_to_file helper 3 -/
namespace GradedSimpleProof

lemma sandwichLeftAnn_graded
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤)
    (h_mul : ∀ {g h : G} {x y : A}, x ∈ 𝒜 g → y ∈ 𝒜 h → x * y ∈ 𝒜 (g * h))
    {g : G} {a : A} (ha : a ∈ 𝒜 g) :
    iSup (fun i : G => 𝒜 i ⊓ sandwichLeftAnn G K A 𝒜 a) =
      sandwichLeftAnn G K A 𝒜 a := by
  apply le_antisymm
  · apply iSup_le
    intro i
    exact inf_le_right
  · intro y hy
    obtain ⟨s, f, hf, hsum⟩ := graded_exists_finset_decomp G K A 𝒜 h_direct y
    rw [Submodule.mem_iSup]
    intro N hN
    have hcomp : ∀ i ∈ s, f i ∈ sandwichLeftAnn G K A 𝒜 a := by
      intro i hi k x hx
      let c : G := g * k
      have hq : iSupIndep (fun j : G => 𝒜 (c * j)) :=
        h_direct.1.comp (mul_right_injective c)
      have hzero : ∑ j ∈ s, a * x * f j = 0 := by
        calc
          ∑ j ∈ s, a * x * f j = (a * x) * (∑ j ∈ s, f j) := by
            rw [Finset.mul_sum]
          _ = a * x * y := by rw [hsum]
          _ = 0 := hy k x hx
      have hmem : ∀ j ∈ s, a * x * f j ∈ 𝒜 (c * j) := by
        intro j hj
        exact h_mul (h_mul ha hx) (hf j hj)
      exact (iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero
        (fun j : G => 𝒜 (c * j))).1 hq s (fun j => a * x * f j) hmem hzero i hi
    rw [← hsum]
    exact N.sum_mem (fun i hi => hN i ⟨hf i hi, hcomp i hi⟩)

end GradedSimpleProof

/- accepted add_to_file helper 4 -/
namespace GradedSimpleProof

lemma sandwichLeftAnn_left_ideal
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤)
    (a r : A) {y : A}
    (hy : y ∈ sandwichLeftAnn G K A 𝒜 a) :
    r * y ∈ sandwichLeftAnn G K A 𝒜 a := by
  intro k x hx
  obtain ⟨s, f, hf, hsum⟩ := graded_exists_finset_decomp G K A 𝒜 h_direct (x * r)
  calc
    a * x * (r * y) = a * (x * r) * y := by simp [mul_assoc]
    _ = a * (∑ i ∈ s, f i) * y := by rw [← hsum]
    _ = ∑ i ∈ s, a * f i * y := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact hy i (f i) (hf i hi)

lemma sandwichLeftAnn_right_ideal
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (a r : A) {y : A}
    (hy : y ∈ sandwichLeftAnn G K A 𝒜 a) :
    y * r ∈ sandwichLeftAnn G K A 𝒜 a := by
  intro k x hx
  rw [← mul_assoc (a * x) y r, hy k x hx, zero_mul]

end GradedSimpleProof

/- accepted add_to_file helper 5 -/
namespace GradedSimpleProof

def tripleLeftAnn
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A) : Submodule K A where
  carrier := {z | ∀ (k : G) (x : A), x ∈ 𝒜 k →
    ∀ (l : G) (y : A), y ∈ 𝒜 l → z * x * y = 0}
  zero_mem' := by
    intro k x hx l y hy
    simp
  add_mem' {z w} hz hw := by
    intro k x hx l y hy
    rw [add_mul, add_mul, hz k x hx l y hy, hw k x hx l y hy, add_zero]
  smul_mem' c {z} hz := by
    intro k x hx l y hy
    rw [smul_mul_assoc, smul_mul_assoc, hz k x hx l y hy, smul_zero]

end GradedSimpleProof

/- accepted add_to_file helper 6 -/
namespace GradedSimpleProof

lemma tripleLeftAnn_graded
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤)
    (h_mul : ∀ {g h : G} {x y : A}, x ∈ 𝒜 g → y ∈ 𝒜 h → x * y ∈ 𝒜 (g * h)) :
    iSup (fun i : G => 𝒜 i ⊓ tripleLeftAnn G K A 𝒜) =
      tripleLeftAnn G K A 𝒜 := by
  apply le_antisymm
  · apply iSup_le
    intro i
    exact inf_le_right
  · intro z hz
    obtain ⟨s, f, hf, hsum⟩ := graded_exists_finset_decomp G K A 𝒜 h_direct z
    rw [Submodule.mem_iSup]
    intro N hN
    have hcomp : ∀ i ∈ s, f i ∈ tripleLeftAnn G K A 𝒜 := by
      intro i hi k x hx l y hy
      have hinj : Function.Injective (fun j : G => (j * k) * l) :=
        (mul_left_injective l).comp (mul_left_injective k)
      have hq : iSupIndep (fun j : G => 𝒜 ((j * k) * l)) :=
        h_direct.1.comp hinj
      have hzero : ∑ j ∈ s, f j * x * y = 0 := by
        calc
          ∑ j ∈ s, f j * x * y = (∑ j ∈ s, f j) * x * y := by
            rw [Finset.sum_mul, Finset.sum_mul]
          _ = z * x * y := by rw [hsum]
          _ = 0 := hz k x hx l y hy
      have hmem : ∀ j ∈ s, f j * x * y ∈ 𝒜 ((j * k) * l) := by
        intro j hj
        exact h_mul (h_mul (hf j hj) hx) hy
      exact (iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero
        (fun j : G => 𝒜 ((j * k) * l))).1 hq s
        (fun j => f j * x * y) hmem hzero i hi
    rw [← hsum]
    exact N.sum_mem (fun i hi => hN i ⟨hf i hi, hcomp i hi⟩)

end GradedSimpleProof

/- accepted add_to_file helper 7 -/
namespace GradedSimpleProof

lemma tripleLeftAnn_left_ideal
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A) (r : A) {z : A}
    (hz : z ∈ tripleLeftAnn G K A 𝒜) :
    r * z ∈ tripleLeftAnn G K A 𝒜 := by
  intro k x hx l y hy
  calc
    r * z * x * y = r * (z * x * y) := by simp [mul_assoc]
    _ = 0 := by rw [hz k x hx l y hy, mul_zero]

lemma tripleLeftAnn_right_ideal
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤)
    (r : A) {z : A}
    (hz : z ∈ tripleLeftAnn G K A 𝒜) :
    z * r ∈ tripleLeftAnn G K A 𝒜 := by
  intro k x hx l y hy
  obtain ⟨s, f, hf, hsum⟩ := graded_exists_finset_decomp G K A 𝒜 h_direct (r * x)
  calc
    z * r * x * y = z * (r * x) * y := by simp [mul_assoc]
    _ = z * (∑ i ∈ s, f i) * y := by rw [← hsum]
    _ = ∑ i ∈ s, z * f i * y := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact hz i (f i) (hf i hi) l y hy

end GradedSimpleProof

/- accepted add_to_file helper 8 -/
namespace GradedSimpleProof

def homogeneousProductSet
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A] [Module K A]
    (𝒜 : G → Submodule K A) : Set A :=
  {p | ∃ (i : G) (x : A), x ∈ 𝒜 i ∧ ∃ (j : G) (y : A), y ∈ 𝒜 j ∧ p = x * y}

def homogeneousProductSubmodule
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A] [Module K A]
    (𝒜 : G → Submodule K A) : Submodule K A :=
  Submodule.span K (homogeneousProductSet G K A 𝒜)

lemma mem_homogeneousProductSubmodule
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A] [Module K A]
    (𝒜 : G → Submodule K A)
    {i j : G} {x y : A} (hx : x ∈ 𝒜 i) (hy : y ∈ 𝒜 j) :
    x * y ∈ homogeneousProductSubmodule G K A 𝒜 := by
  apply Submodule.subset_span
  exact ⟨i, x, hx, j, y, hy, rfl⟩

end GradedSimpleProof

/- accepted add_to_file helper 9 -/
namespace GradedSimpleProof

lemma homogeneousProductSubmodule_left_ideal
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤)
    (r : A) {p : A} (hp : p ∈ homogeneousProductSubmodule G K A 𝒜) :
    r * p ∈ homogeneousProductSubmodule G K A 𝒜 := by
  unfold homogeneousProductSubmodule at hp ⊢
  refine Submodule.span_induction (fun q hq => ?_) ?_ ?_ ?_ hp
  · obtain ⟨i, x, hx, j, y, hy, rfl⟩ := hq
    obtain ⟨s, f, hf, hsum⟩ := graded_exists_finset_decomp G K A 𝒜 h_direct (r * x)
    have hEq : r * (x * y) = ∑ n ∈ s, f n * y := by
      calc
        r * (x * y) = (r * x) * y := by simp [mul_assoc]
        _ = (∑ n ∈ s, f n) * y := by rw [← hsum]
        _ = ∑ n ∈ s, f n * y := by rw [Finset.sum_mul]
    rw [hEq]
    apply Submodule.sum_mem
    intro n hn
    exact mem_homogeneousProductSubmodule G K A 𝒜 (hf n hn) hy
  · simp
  · intro q₁ q₂ hq₁ hq₂ h₁ h₂
    rw [mul_add]
    exact (Submodule.span K (homogeneousProductSet G K A 𝒜)).add_mem h₁ h₂
  · intro c q hq h
    rw [mul_smul_comm]
    exact (Submodule.span K (homogeneousProductSet G K A 𝒜)).smul_mem c h

end GradedSimpleProof

/- accepted add_to_file helper 10 -/
namespace GradedSimpleProof

lemma homogeneousProductSubmodule_right_ideal
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤)
    (r : A) {p : A} (hp : p ∈ homogeneousProductSubmodule G K A 𝒜) :
    p * r ∈ homogeneousProductSubmodule G K A 𝒜 := by
  unfold homogeneousProductSubmodule at hp ⊢
  refine Submodule.span_induction (fun q hq => ?_) ?_ ?_ ?_ hp
  · obtain ⟨i, x, hx, j, y, hy, rfl⟩ := hq
    obtain ⟨s, f, hf, hsum⟩ := graded_exists_finset_decomp G K A 𝒜 h_direct (y * r)
    have hEq : (x * y) * r = ∑ n ∈ s, x * f n := by
      calc
        (x * y) * r = x * (y * r) := by rw [mul_assoc]
        _ = x * (∑ n ∈ s, f n) := by rw [← hsum]
        _ = ∑ n ∈ s, x * f n := by rw [Finset.mul_sum]
    rw [hEq]
    apply Submodule.sum_mem
    intro n hn
    exact mem_homogeneousProductSubmodule G K A 𝒜 hx (hf n hn)
  · simp
  · intro q₁ q₂ hq₁ hq₂ h₁ h₂
    rw [add_mul]
    exact (Submodule.span K (homogeneousProductSet G K A 𝒜)).add_mem h₁ h₂
  · intro c q hq h
    rw [smul_mul_assoc]
    exact (Submodule.span K (homogeneousProductSet G K A 𝒜)).smul_mem c h

end GradedSimpleProof

/- accepted add_to_file helper 11 -/
namespace GradedSimpleProof

lemma homogeneousProductSubmodule_graded
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_mul : ∀ {g h : G} {x y : A}, x ∈ 𝒜 g → y ∈ 𝒜 h → x * y ∈ 𝒜 (g * h)) :
    iSup (fun i : G => 𝒜 i ⊓ homogeneousProductSubmodule G K A 𝒜) =
      homogeneousProductSubmodule G K A 𝒜 := by
  apply le_antisymm
  · apply iSup_le
    intro i
    exact inf_le_right
  · unfold homogeneousProductSubmodule
    rw [Submodule.span_le]
    intro p hp
    obtain ⟨i, x, hx, j, y, hy, rfl⟩ := hp
    apply Submodule.mem_iSup_of_mem (i * j)
    exact ⟨h_mul hx hy, mem_homogeneousProductSubmodule G K A 𝒜 hx hy⟩

end GradedSimpleProof

/- accepted add_to_file helper 12 -/
namespace GradedSimpleProof

lemma mul_eq_zero_of_mem_homogeneousProductSubmodule
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (hH : tripleLeftAnn G K A 𝒜 = ⊤)
    (u : A) {p : A} (hp : p ∈ homogeneousProductSubmodule G K A 𝒜) :
    u * p = 0 := by
  unfold homogeneousProductSubmodule at hp
  refine Submodule.span_induction (fun q hq => ?_) ?_ ?_ ?_ hp
  · obtain ⟨i, x, hx, j, y, hy, rfl⟩ := hq
    have huH : u ∈ tripleLeftAnn G K A 𝒜 := by
      rw [hH]
      exact Submodule.mem_top
    rw [← mul_assoc]
    exact huH i x hx j y hy
  · simp
  · intro q₁ q₂ hq₁ hq₂ h₁ h₂
    rw [mul_add, h₁, h₂, add_zero]
  · intro c q hq h
    rw [mul_smul_comm, h, smul_zero]

end GradedSimpleProof

/- accepted add_to_file helper 13 -/
namespace GradedSimpleProof

lemma exists_homogeneous_mul_ne_zero
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤)
    (h_nonzero_mul : ∃ x y : A, x * y ≠ 0) :
    ∃ (i : G) (x : A), x ∈ 𝒜 i ∧
      ∃ (j : G) (y : A), y ∈ 𝒜 j ∧ x * y ≠ 0 := by
  obtain ⟨u, v, huv⟩ := h_nonzero_mul
  obtain ⟨su, fu, hfu, hsumu⟩ := graded_exists_finset_decomp G K A 𝒜 h_direct u
  obtain ⟨sv, fv, hfv, hsumv⟩ := graded_exists_finset_decomp G K A 𝒜 h_direct v
  have hprod_sum : (∑ i ∈ su, ∑ j ∈ sv, fu i * fv j) = u * v := by
    calc
      (∑ i ∈ su, ∑ j ∈ sv, fu i * fv j) =
          (∑ i ∈ su, fu i) * (∑ j ∈ sv, fv j) := by
        symm
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = u * v := by rw [hsumu, hsumv]
  have hsum_ne : (∑ i ∈ su, ∑ j ∈ sv, fu i * fv j) ≠ 0 := by
    rwa [hprod_sum]
  obtain ⟨i, hi, hinner⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  obtain ⟨j, hj, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hinner
  exact ⟨i, fu i, hfu i hi, j, fv j, hfv j hj, hp⟩

end GradedSimpleProof

/- verified submission -/
theorem graded_simple_mul_nonzero
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤)
    (h_mul : ∀ {g h : G} {x y : A}, x ∈ 𝒜 g → y ∈ 𝒜 h → x * y ∈ 𝒜 (g * h))
    (h_nonzero_mul : ∃ x y : A, x * y ≠ 0)
    (h_simple : ∀ I : Submodule K A,
      (∀ (r : A) {x : A}, x ∈ I → r * x ∈ I) →
      (∀ (r : A) {x : A}, x ∈ I → x * r ∈ I) →
      iSup (fun g => 𝒜 g ⊓ I) = I → I = ⊥ ∨ I = ⊤)
    {g h : G} {a b : A} (ha : a ∈ 𝒜 g) (hb : b ∈ 𝒜 h)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    ∃ k : G, ∃ x : A, x ∈ 𝒜 k ∧ a * x * b ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  let J : Submodule K A := GradedSimpleProof.sandwichLeftAnn G K A 𝒜 a
  have hbJ : b ∈ J := hcon
  have hJ := h_simple J
    (fun r {x} hx => GradedSimpleProof.sandwichLeftAnn_left_ideal G K A 𝒜 h_direct a r hx)
    (fun r {x} hx => GradedSimpleProof.sandwichLeftAnn_right_ideal G K A 𝒜 a r hx)
    (GradedSimpleProof.sandwichLeftAnn_graded G K A 𝒜 h_direct h_mul ha)
  have hJtop : J = ⊤ := by
    rcases hJ with hJbot | hJtop
    · have hbzero : b = 0 := by
        have hbJ' : b ∈ (⊥ : Submodule K A) := by
          rwa [← hJbot]
        simpa using hbJ'
      exact (hb0 hbzero).elim
    · exact hJtop
  let H : Submodule K A := GradedSimpleProof.tripleLeftAnn G K A 𝒜
  have haH : a ∈ H := by
    intro k x hx l y hy
    have hyJ : y ∈ J := by
      rw [hJtop]
      exact Submodule.mem_top
    exact hyJ k x hx
  have hH := h_simple H
    (fun r {x} hx => GradedSimpleProof.tripleLeftAnn_left_ideal G K A 𝒜 r hx)
    (fun r {x} hx => GradedSimpleProof.tripleLeftAnn_right_ideal G K A 𝒜 h_direct r hx)
    (GradedSimpleProof.tripleLeftAnn_graded G K A 𝒜 h_direct h_mul)
  have hHtop : H = ⊤ := by
    rcases hH with hHbot | hHtop
    · have hazero : a = 0 := by
        have haH' : a ∈ (⊥ : Submodule K A) := by
          rwa [← hHbot]
        simpa using haH'
      exact (ha0 hazero).elim
    · exact hHtop
  let P : Submodule K A := GradedSimpleProof.homogeneousProductSubmodule G K A 𝒜
  obtain ⟨i, x, hx, j, y, hy, hxy⟩ :=
    GradedSimpleProof.exists_homogeneous_mul_ne_zero G K A 𝒜 h_direct h_nonzero_mul
  have hxyP : x * y ∈ P :=
    GradedSimpleProof.mem_homogeneousProductSubmodule G K A 𝒜 hx hy
  have hP := h_simple P
    (fun r {z} hz => GradedSimpleProof.homogeneousProductSubmodule_left_ideal G K A 𝒜 h_direct r hz)
    (fun r {z} hz => GradedSimpleProof.homogeneousProductSubmodule_right_ideal G K A 𝒜 h_direct r hz)
    (GradedSimpleProof.homogeneousProductSubmodule_graded G K A 𝒜 h_mul)
  have hPtop : P = ⊤ := by
    rcases hP with hPbot | hPtop
    · have hxyzero : x * y = 0 := by
        have hxyP' : x * y ∈ (⊥ : Submodule K A) := by
          rwa [← hPbot]
        simpa using hxyP'
      exact (hxy hxyzero).elim
    · exact hPtop
  obtain ⟨u, v, huv⟩ := h_nonzero_mul
  have hvP : v ∈ P := by
    rw [hPtop]
    exact Submodule.mem_top
  have huvzero : u * v = 0 :=
    GradedSimpleProof.mul_eq_zero_of_mem_homogeneousProductSubmodule G K A 𝒜 hHtop u hvP
  exact huv huvzero
