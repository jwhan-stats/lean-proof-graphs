import Mathlib

/- accepted add_to_file helper 1 -/
def booleanCoeffRank (n : ℤ) : ℕ := (2 * n - 1).natAbs

lemma booleanCoeffRank_reflect (n : ℤ) (hn : ¬ (n = 0 ∨ n = 1)) :
    booleanCoeffRank (if 2 ≤ n then 2 - n else -n) < booleanCoeffRank n := by
  by_cases h : 2 ≤ n
  · simp [booleanCoeffRank, h]
    have hl : ((2 * (2 - n) - 1).natAbs : ℤ) = -(2 * (2 - n) - 1) := by
      have hnon : 0 ≤ -(2 * (2 - n) - 1) := by omega
      have habs := Int.natAbs_of_nonneg hnon
      rwa [Int.natAbs_neg] at habs
    have hr : ((2 * n - 1).natAbs : ℤ) = 2 * n - 1 := by
      exact Int.natAbs_of_nonneg (by omega)
    omega
  · simp [booleanCoeffRank, h]
    have hnlt : n < 0 := by omega
    have hl : ((2 * -n - 1).natAbs : ℤ) = 2 * -n - 1 := by
      exact Int.natAbs_of_nonneg (by omega)
    have hr : ((2 * n - 1).natAbs : ℤ) = -(2 * n - 1) := by
      have hnon : 0 ≤ -(2 * n - 1) := by omega
      have habs := Int.natAbs_of_nonneg hnon
      rwa [Int.natAbs_neg] at habs
    omega

lemma subgroup_le_sup_of_set_prod {U A : Type*} [Group U] [AddCommGroup A]
    (W : A → Subgroup U)
    (hprod : ∀ x y : A,
      (W x : Set U) ⊆ Set.image2 (fun g h : U => g * h) (W y : Set U)
        (W (2 • y - x) : Set U))
    (x y : A) :
    W x ≤ W y ⊔ W (2 • y - x) := by
  rw [← SetLike.coe_subset_coe]
  intro g hg
  rcases hprod x y hg with ⟨g₁, hg₁, g₂, hg₂, rfl⟩
  exact Subgroup.mul_mem _
    (SetLike.le_def.mp le_sup_left hg₁)
    (SetLike.le_def.mp le_sup_right hg₂)

/- accepted add_to_file helper 2 -/
lemma subgroup_le_boolean_iSup_of_int_coeffs {U A : Type*} [Group U] [AddCommGroup A]
    {m : ℕ} (a : Fin m → A) (W : A → Subgroup U)
    (hprod : ∀ x y : A,
      (W x : Set U) ⊆ Set.image2 (fun g h : U => g * h) (W y : Set U)
        (W (2 • y - x) : Set U))
    (n : Fin m → ℤ) :
    W (∑ i, n i • a i) ≤ ⨆ s : Finset (Fin m), W (∑ i ∈ s, a i) := by
  let rank : (Fin m → ℤ) → ℕ := fun c => ∑ i, booleanCoeffRank (c i)
  refine (InvImage.wf rank Nat.lt_wfRel.wf).fix
    (C := fun c : Fin m → ℤ =>
      W (∑ i, c i • a i) ≤ ⨆ s : Finset (Fin m), W (∑ i ∈ s, a i))
    (fun n ih => ?_) n
  have base_of_boolean : ∀ c : Fin m → ℤ, (∀ i, c i = 0 ∨ c i = 1) →
      W (∑ i, c i • a i) ≤ ⨆ s : Finset (Fin m), W (∑ i ∈ s, a i) := by
    intro c hc
    have hsum : (∑ i, c i • a i) =
        ∑ i ∈ Finset.univ.filter (fun i => c i = 1), a i := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      rcases hc i with h | h <;> simp [h]
    rw [hsum]
    exact le_iSup (fun s : Finset (Fin m) => W (∑ i ∈ s, a i))
      (Finset.univ.filter fun i => c i = 1)
  by_cases hb : ∀ i, n i = 0 ∨ n i = 1
  · exact base_of_boolean n hb
  · push_neg at hb
    rcases hb with ⟨j, hj⟩
    have hjnot : ¬ (n j = 0 ∨ n j = 1) := by
      intro h
      rcases h with h | h
      · exact hj.1 h
      · exact hj.2 h
    let b : Fin m → ℤ := fun i =>
      if h : n i = 0 ∨ n i = 1 then n i else if 2 ≤ n i then 1 else 0
    let n' : Fin m → ℤ := fun i => 2 * b i - n i
    have hb01 : ∀ i, b i = 0 ∨ b i = 1 := by
      intro i
      by_cases hgood : n i = 0 ∨ n i = 1
      · simpa [b, hgood] using hgood
      · by_cases htwo : 2 ≤ n i
        · simp [b, hgood, htwo]
        · simp [b, hgood, htwo]
    have hcoord_le : ∀ i, booleanCoeffRank (n' i) ≤ booleanCoeffRank (n i) := by
      intro i
      by_cases hgood : n i = 0 ∨ n i = 1
      · have hn'i : n' i = n i := by
          simp [n', b, hgood]
          ring
        rw [hn'i]
      · have hlt := booleanCoeffRank_reflect (n i) hgood
        by_cases htwo : 2 ≤ n i
        · have hn'i : n' i = 2 - n i := by
            simp [n', b, hgood, htwo]
          rw [hn'i]
          simpa [htwo] using le_of_lt hlt
        · have hn'i : n' i = -n i := by
            simp [n', b, hgood, htwo]
          rw [hn'i]
          simpa [htwo] using le_of_lt hlt
    have hcoord_j : booleanCoeffRank (n' j) < booleanCoeffRank (n j) := by
      have hlt := booleanCoeffRank_reflect (n j) hjnot
      by_cases htwo : 2 ≤ n j
      · have hn'j : n' j = 2 - n j := by
          simp [n', b, hjnot, htwo]
        rw [hn'j]
        simpa [htwo] using hlt
      · have hn'j : n' j = -n j := by
          simp [n', b, hjnot, htwo]
        rw [hn'j]
        simpa [htwo] using hlt
    have hrank : rank n' < rank n := by
      dsimp [rank]
      exact Finset.sum_lt_sum (fun i hi => hcoord_le i) ⟨j, Finset.mem_univ j, hcoord_j⟩
    have hz : W (∑ i, n' i • a i) ≤ ⨆ s : Finset (Fin m), W (∑ i ∈ s, a i) :=
      ih n' hrank
    have hy : W (∑ i, b i • a i) ≤ ⨆ s : Finset (Fin m), W (∑ i ∈ s, a i) :=
      base_of_boolean b hb01
    have hlin : (∑ i, n' i • a i) =
        2 • (∑ i, b i • a i) - ∑ i, n i • a i := by
      trans ∑ i, ((2 * b i) • a i - n i • a i)
      · apply Finset.sum_congr rfl
        intro i hi
        rw [sub_smul]
      · rw [Finset.sum_sub_distrib]
        congr 1
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [show 2 * b i = b i + b i by ring, add_smul, two_nsmul]
    have hx_sup := subgroup_le_sup_of_set_prod W hprod
      (∑ i, n i • a i) (∑ i, b i • a i)
    rw [← hlin] at hx_sup
    exact hx_sup.trans (sup_le hy hz)

/- verified submission -/
theorem subgroup_iSup_eq_boolean_iSup
    {U A : Type*} [Group U] [AddCommGroup A] {m : ℕ}
    (a : Fin m → A) (W : A → Subgroup U)
    (hgen : AddSubgroup.closure (Set.range a) = ⊤)
    (hcomm : ∀ x : A, commutator U ≤ W x)
    (hprod : ∀ x y : A,
      (W x : Set U) ⊆ Set.image2 (fun g h : U => g * h) (W y : Set U)
        (W (2 • y - x) : Set U)) :
    (⨆ x : A, W x) = ⨆ s : Finset (Fin m), W (∑ i ∈ s, a i) := by
  apply le_antisymm
  · apply iSup_le
    intro x
    have hx : x ∈ AddSubgroup.closure (Set.range a) := by
      rw [hgen]
      trivial
    rcases AddSubgroup.mem_closure_range_iff.mp hx with ⟨c, hc⟩
    rw [Finsupp.sum_zsmul] at hc
    rw [hc]
    exact subgroup_le_boolean_iSup_of_int_coeffs a W hprod c
  · apply iSup_le
    intro s
    exact le_iSup (fun x : A => W x) (∑ i ∈ s, a i)
