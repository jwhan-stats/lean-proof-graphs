import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1299_convexpolytope_trace_latticeembedding
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 05c80beeafdb73c7eb8a5d1fdb49b2806e9f9882af8cd90b50f37d0303868e47
-- reconstructed_proof_sha256: d2e8da6d1a6e2bda5ee7fdc2b245db64d06e568a7aea01be31cda195b9818b8c
-- selected_edge_count: 3

/- accepted add_to_file helper 1 -/
lemma Convex.sum_mem_divisionRing
    {R E ι : Type*} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup E] [Module R E]
    {s : Set E} (hs : Convex R s) {t : Finset ι} {w : ι → R} {z : ι → E}
    (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1)
    (hz : ∀ i ∈ t, z i ∈ s) :
    ∑ i ∈ t, w i • z i ∈ s := by
  classical
  induction t using Finset.induction generalizing w with
  | empty =>
      simp at h₁
  | insert i t hi ih =>
      have hsum : w i + ∑ j ∈ t, w j = 1 := by
        simpa [hi] using h₁
      by_cases hwi : w i = 1
      · have hsumt : ∑ j ∈ t, w j = 0 := by
          have : 1 + ∑ j ∈ t, w j = 1 := by simpa [hwi] using hsum
          exact add_eq_left.mp this
        have hzero : ∀ j ∈ t, w j = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => h₀ j (Finset.mem_insert_of_mem hj))).mp hsumt
        have hweighted_zero : ∑ j ∈ t, w j • z j = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          rw [hzero j hj, zero_smul]
        have hzmem : z i ∈ s := hz i (Finset.mem_insert_self i t)
        rw [Finset.sum_insert hi, hweighted_zero, hwi, one_smul, add_zero]
        exact hzmem
      · set r : R := ∑ j ∈ t, w j with hrdef
        have hrnonneg : 0 ≤ r := by
          rw [hrdef]
          exact Finset.sum_nonneg (fun j hj => h₀ j (Finset.mem_insert_of_mem hj))
        have hwile : w i ≤ 1 := by
          rw [← hsum]
          exact le_add_of_nonneg_right hrnonneg
        have hwilt : w i < 1 := lt_of_le_of_ne hwile hwi
        have hsum' : r + w i = 1 := by
          simpa [hrdef, add_comm] using hsum
        have hr_eq : r = 1 - w i := eq_sub_of_add_eq hsum'
        have hwi_eq : w i = 1 - r := eq_sub_of_add_eq hsum
        have hrle : r ≤ 1 := by
          rw [← hsum']
          exact le_add_of_nonneg_right (h₀ i (Finset.mem_insert_self i t))
        have hrpos : 0 < r := by
          rw [hr_eq]
          exact sub_pos.mpr hwilt
        let w' : ι → R := fun j => r⁻¹ * w j
        have hw'₀ : ∀ j ∈ t, 0 ≤ w' j := by
          intro j hj
          exact mul_nonneg (inv_nonneg.mpr hrnonneg)
            (h₀ j (Finset.mem_insert_of_mem hj))
        have hw'₁ : ∑ j ∈ t, w' j = 1 := by
          calc
            ∑ j ∈ t, w' j = r⁻¹ * r := by
              rw [hrdef]
              exact (Finset.mul_sum t w r⁻¹).symm
            _ = 1 := inv_mul_cancel₀ hrpos.ne'
        have hy : ∑ j ∈ t, w' j • z j ∈ s :=
          ih (fun j hj => hw'₀ j hj) hw'₁ (fun j hj => hz j (Finset.mem_insert_of_mem hj))
        have hrest : ∑ j ∈ t, w j • z j = r • ∑ j ∈ t, w' j • z j := by
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          calc
            w j • z j = ((r * r⁻¹) * w j) • z j := by
              rw [mul_inv_cancel₀ hrpos.ne', one_mul]
            _ = (r * (r⁻¹ * w j)) • z j := by rw [mul_assoc]
            _ = r • ((r⁻¹ * w j) • z j) := mul_smul r (r⁻¹ * w j) (z j)
            _ = r • (w' j • z j) := rfl
        rw [Finset.sum_insert hi, hrest, hwi_eq]
        exact hs (hz i (Finset.mem_insert_self i t)) hy (sub_nonneg.mpr hrle) hrnonneg
          (sub_add_cancel 1 r)

/- accepted add_to_file helper 2 -/
lemma convexHull_eq_divisionRing
    {R E : Type*} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup E] [Module R E] (s : Set E) :
    convexHull R s =
      {x | ∃ (ι : Type) (t : Finset ι) (w : ι → R) (z : ι → E),
        (∀ i ∈ t, 0 ≤ w i) ∧ (∑ i ∈ t, w i = 1) ∧
        (∀ i ∈ t, z i ∈ s) ∧ (∑ i ∈ t, w i • z i) = x} := by
  classical
  apply Set.Subset.antisymm
  · apply convexHull_min
    · intro x hx
      refine ⟨PUnit, {PUnit.unit}, fun _ => 1, fun _ => x, ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · simpa using hx
      · simp
    · intro x hx y hy a b ha hb hab
      rcases hx with ⟨ιx, tx, wx, zx, hwx₀, hwx₁, hzx, hxeq⟩
      rcases hy with ⟨ιy, ty, wy, zy, hwy₀, hwy₁, hzy, hyeq⟩
      refine ⟨ιx ⊕ ιy, tx.disjSum ty,
        Sum.elim (fun i => a * wx i) (fun j => b * wy j), Sum.elim zx zy,
        ?_, ?_, ?_, ?_⟩
      · intro k hk
        rcases Finset.mem_disjSum.mp hk with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
        · exact mul_nonneg ha (hwx₀ i hi)
        · exact mul_nonneg hb (hwy₀ j hj)
      · simp only [Finset.sum_disjSum, Sum.elim_inl, Sum.elim_inr]
        rw [← Finset.mul_sum tx wx a, hwx₁]
        rw [← Finset.mul_sum ty wy b, hwy₁]
        simpa using hab
      · intro k hk
        rcases Finset.mem_disjSum.mp hk with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
        · exact hzx i hi
        · exact hzy j hj
      · calc
          (∑ k ∈ tx.disjSum ty,
              Sum.elim (fun i => a * wx i) (fun j => b * wy j) k • Sum.elim zx zy k)
              = a • (∑ i ∈ tx, wx i • zx i) + b • (∑ j ∈ ty, wy j • zy j) := by
                simp only [Finset.sum_disjSum, Sum.elim_inl, Sum.elim_inr]
                congr 1
                · rw [Finset.smul_sum]
                  apply Finset.sum_congr rfl
                  intro i hi
                  exact mul_smul a (wx i) (zx i)
                · rw [Finset.smul_sum]
                  apply Finset.sum_congr rfl
                  intro j hj
                  exact mul_smul b (wy j) (zy j)
          _ = a • x + b • y := by rw [hxeq, hyeq]
  · intro x hx
    rcases hx with ⟨ι, t, w, z, hw₀, hw₁, hz, hxeq⟩
    rw [← hxeq]
    exact Convex.sum_mem_divisionRing (convex_convexHull R s) hw₀ hw₁
      (fun i hi => subset_convexHull R s (hz i hi))

/- accepted add_to_file helper 3 -/
lemma mem_convexHull_finset_divisionRing
    {R E : Type*} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup E] [Module R E] {s : Finset E} {x : E} :
    x ∈ convexHull R (↑s : Set E) ↔
      ∃ w : E → R, (∀ y ∈ s, 0 ≤ w y) ∧ (∑ y ∈ s, w y = 1) ∧
        (∑ y ∈ s, w y • y) = x := by
  classical
  constructor
  · intro hx
    rw [convexHull_eq_divisionRing (↑s : Set E)] at hx
    rcases hx with ⟨ι, t, u, z, hu₀, hu₁, hz, hxeq⟩
    let w : E → R := fun y => ∑ i ∈ t.filter (fun i => z i = y), u i
    refine ⟨w, ?_, ?_, ?_⟩
    · intro y hy
      exact Finset.sum_nonneg (fun i hi => hu₀ i (Finset.mem_filter.mp hi).1)
    · calc
        ∑ y ∈ s, w y = ∑ y ∈ s, ∑ i ∈ t.filter (fun i => z i = y), u i := rfl
        _ = ∑ i ∈ t, u i := by
          exact Finset.sum_fiberwise_of_maps_to (fun i hi => by simpa using hz i hi) u
        _ = 1 := hu₁
    · calc
        ∑ y ∈ s, w y • y
            = ∑ y ∈ s, ∑ i ∈ t.filter (fun i => z i = y), u i • z i := by
              apply Finset.sum_congr rfl
              intro y hy
              calc
                w y • y = (∑ i ∈ t.filter (fun i => z i = y), u i) • y := rfl
                _ = ∑ i ∈ t.filter (fun i => z i = y), u i • y := Finset.sum_smul
                _ = ∑ i ∈ t.filter (fun i => z i = y), u i • z i := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [Finset.mem_filter] at hi
                  rw [hi.2]
        _ = ∑ i ∈ t, u i • z i := by
          exact Finset.sum_fiberwise_of_maps_to (fun i hi => by simpa using hz i hi)
            (fun i => u i • z i)
        _ = x := hxeq
  · intro hx
    rcases hx with ⟨w, hw₀, hw₁, hxeq⟩
    rw [← hxeq]
    exact Convex.sum_mem_divisionRing (convex_convexHull R (↑s : Set E)) hw₀ hw₁
      (fun y hy => subset_convexHull R (↑s : Set E) (by simpa using hy))

/- accepted add_to_file helper 4 -/
lemma exists_convexCombination_coeff_lt_one_divisionRing
    {R E : Type*} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup E] [Module R E]
    {s : Finset E} {a p : E} (ha : a ∈ s)
    (hp : p ∈ convexHull R (↑s : Set E)) (hpa : p ≠ a) :
    ∃ w : E → R, (∀ y ∈ s, 0 ≤ w y) ∧ (∑ y ∈ s, w y = 1) ∧
      (∑ y ∈ s, w y • y) = p ∧ w a < 1 := by
  classical
  rcases (mem_convexHull_finset_divisionRing.mp hp) with ⟨w, hw₀, hw₁, hwp⟩
  refine ⟨w, hw₀, hw₁, hwp, ?_⟩
  have hwale : w a ≤ 1 := by
    calc
      w a ≤ ∑ y ∈ s, w y := Finset.single_le_sum hw₀ ha
      _ = 1 := hw₁
  refine lt_of_le_of_ne hwale ?_
  intro hwa
  have herase_sum : ∑ y ∈ s.erase a, w y = 0 := by
    have h := Finset.sum_erase_add s w ha
    rw [hwa, hw₁] at h
    exact add_eq_right.mp h
  have hzero : ∀ y ∈ s.erase a, w y = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun y hy => hw₀ y (Finset.mem_of_mem_erase hy))).mp herase_sum
  have hsum_single : ∑ y ∈ s, w y • y = w a • a := by
    apply Finset.sum_eq_single_of_mem a ha
    intro y hy hya
    have hyerase : y ∈ s.erase a := Finset.mem_erase.mpr ⟨hya, hy⟩
    rw [hzero y hyerase, zero_smul]
  have : p = a := by
    rw [← hwp, hsum_single, hwa, one_smul]
  exact hpa this

/- accepted add_to_file helper 5 -/
lemma mem_convexHull_erase_of_combination_self_divisionRing
    {R E : Type*} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup E] [Module R E] [DecidableEq E]
    {s : Finset E} {a : E} (ha : a ∈ s) {w : E → R}
    (hw₀ : ∀ y ∈ s, 0 ≤ w y) (hw₁ : ∑ y ∈ s, w y = 1)
    (hwa : w a < 1) (hsum : ∑ y ∈ s, w y • y = a) :
    a ∈ convexHull R (↑(s.erase a) : Set E) := by
  classical
  set r : R := 1 - w a with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]
    exact sub_pos.mpr hwa
  let v : E → R := fun y => r⁻¹ * w y
  have hv₀ : ∀ y ∈ s.erase a, 0 ≤ v y := by
    intro y hy
    exact mul_nonneg (inv_nonneg.mpr hrpos.le)
      (hw₀ y (Finset.mem_of_mem_erase hy))
  have hsum_erase_w : ∑ y ∈ s.erase a, w y = r := by
    rw [hrdef, Finset.sum_erase_eq_sub ha, hw₁]
  have hv₁ : ∑ y ∈ s.erase a, v y = 1 := by
    calc
      ∑ y ∈ s.erase a, v y = r⁻¹ * ∑ y ∈ s.erase a, w y := by
        exact (Finset.mul_sum (s.erase a) w r⁻¹).symm
      _ = r⁻¹ * r := by rw [hsum_erase_w]
      _ = 1 := inv_mul_cancel₀ hrpos.ne'
  have hweighted_erase : ∑ y ∈ s.erase a, w y • y = r • a := by
    have hdecomp := Finset.sum_erase_add s (fun y => w y • y) ha
    rw [hsum] at hdecomp
    calc
      ∑ y ∈ s.erase a, w y • y = a - w a • a := eq_sub_of_add_eq hdecomp
      _ = (1 : R) • a - w a • a := by rw [one_smul]
      _ = (1 - w a) • a := (sub_smul (1 : R) (w a) a).symm
      _ = r • a := rfl
  have hvsum : ∑ y ∈ s.erase a, v y • y = a := by
    calc
      ∑ y ∈ s.erase a, v y • y
          = ∑ y ∈ s.erase a, r⁻¹ • (w y • y) := by
            apply Finset.sum_congr rfl
            intro y hy
            exact mul_smul r⁻¹ (w y) y
      _ = r⁻¹ • ∑ y ∈ s.erase a, w y • y := (Finset.smul_sum).symm
      _ = r⁻¹ • (r • a) := by rw [hweighted_erase]
      _ = (r⁻¹ * r) • a := (mul_smul r⁻¹ r a).symm
      _ = a := by rw [inv_mul_cancel₀ hrpos.ne', one_smul]
  exact mem_convexHull_finset_divisionRing.mpr ⟨v, hv₀, hv₁, hvsum⟩

/- accepted add_to_file helper 6 -/
lemma mem_convexHull_erase_of_mem_openSegment_left_ne_divisionRing
    {R E : Type*} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup E] [Module R E] [DecidableEq E]
    {s : Finset E} {a x₁ x₂ : E} (ha : a ∈ s)
    (hx₁ : x₁ ∈ convexHull R (↑s : Set E))
    (hx₂ : x₂ ∈ convexHull R (↑s : Set E))
    (hseg : a ∈ openSegment R x₁ x₂) (hx₁a : x₁ ≠ a) :
    a ∈ convexHull R (↑(s.erase a) : Set E) := by
  classical
  rcases hseg with ⟨c₁, c₂, hc₁, hc₂, hcsum, hcombo⟩
  rcases exists_convexCombination_coeff_lt_one_divisionRing ha hx₁ hx₁a with
    ⟨w₁, hw₁₀, hw₁₁, hw₁sum, hw₁a⟩
  rcases (mem_convexHull_finset_divisionRing.mp hx₂) with ⟨w₂, hw₂₀, hw₂₁, hw₂sum⟩
  let u : E → R := fun y => c₁ * w₁ y + c₂ * w₂ y
  have hu₀ : ∀ y ∈ s, 0 ≤ u y := by
    intro y hy
    exact add_nonneg (mul_nonneg hc₁.le (hw₁₀ y hy))
      (mul_nonneg hc₂.le (hw₂₀ y hy))
  have hu₁ : ∑ y ∈ s, u y = 1 := by
    calc
      ∑ y ∈ s, u y = ∑ y ∈ s, (c₁ * w₁ y + c₂ * w₂ y) := rfl
      _ = 1 := by
        rw [Finset.sum_add_distrib]
        rw [← Finset.mul_sum s w₁ c₁, hw₁₁]
        rw [← Finset.mul_sum s w₂ c₂, hw₂₁]
        simpa using hcsum
  have hw₂a : w₂ a ≤ 1 := by
    calc
      w₂ a ≤ ∑ y ∈ s, w₂ y := Finset.single_le_sum hw₂₀ ha
      _ = 1 := hw₂₁
  have hua : u a < 1 := by
    calc
      u a = c₁ * w₁ a + c₂ * w₂ a := rfl
      _ < c₁ * 1 + c₂ * 1 :=
        add_lt_add_of_lt_of_le
          (mul_lt_mul_of_pos_left hw₁a hc₁)
          (mul_le_mul_of_nonneg_left hw₂a hc₂.le)
      _ = 1 := by simpa using hcsum
  have husum : ∑ y ∈ s, u y • y = a := by
    calc
      ∑ y ∈ s, u y • y = ∑ y ∈ s, (c₁ * w₁ y + c₂ * w₂ y) • y := rfl
      _ = ∑ y ∈ s, (c₁ • (w₁ y • y) + c₂ • (w₂ y • y)) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [add_smul, mul_smul, mul_smul]
      _ = c₁ • (∑ y ∈ s, w₁ y • y) + c₂ • (∑ y ∈ s, w₂ y • y) := by
        rw [Finset.sum_add_distrib, Finset.smul_sum, Finset.smul_sum]
      _ = c₁ • x₁ + c₂ • x₂ := by rw [hw₁sum, hw₂sum]
      _ = a := hcombo
  exact mem_convexHull_erase_of_combination_self_divisionRing ha hu₀ hu₁ hua husum

/- accepted add_to_file helper 7 -/
lemma convexHull_erase_eq_of_not_extremePoint_divisionRing
    {R E : Type*} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup E] [Module R E] [DecidableEq E]
    {s : Finset E} {a : E} (ha : a ∈ s)
    (hne : a ∉ Set.extremePoints R (convexHull R (↑s : Set E))) :
    convexHull R (↑(s.erase a) : Set E) = convexHull R (↑s : Set E) := by
  classical
  have haP : a ∈ convexHull R (↑s : Set E) :=
    subset_convexHull R (↑s : Set E) (by simpa using ha)
  rw [mem_extremePoints] at hne
  push Not at hne
  rcases hne haP with ⟨x₁, hx₁, x₂, hx₂, hseg, hnot⟩
  have hamem : a ∈ convexHull R (↑(s.erase a) : Set E) := by
    by_cases hx₁a : x₁ = a
    · have hx₂a : x₂ ≠ a := hnot hx₁a
      have hseg' : a ∈ openSegment R x₂ x₁ := by
        rwa [openSegment_symm]
      exact mem_convexHull_erase_of_mem_openSegment_left_ne_divisionRing
        ha hx₂ hx₁ hseg' hx₂a
    · exact mem_convexHull_erase_of_mem_openSegment_left_ne_divisionRing
        ha hx₁ hx₂ hseg hx₁a
  apply Set.Subset.antisymm
  · exact convexHull_mono (by intro y hy; simpa using (Finset.erase_subset a s hy))
  · apply convexHull_min
    · intro y hy
      by_cases hya : y = a
      · rwa [hya]
      · apply subset_convexHull R (↑(s.erase a) : Set E)
        exact (Finset.mem_erase (a := y) (b := a) (s := s)).mpr
          ⟨hya, by simpa using hy⟩
    · exact convex_convexHull R (↑(s.erase a) : Set E)

/- accepted add_to_file helper 8 -/
lemma convexHull_subset_convexHull_of_extremePoints_subset_divisionRing
    {R E : Type*} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup E] [Module R E] [DecidableEq E]
    {C : Set E} (s : Finset E)
    (hC : C ⊆ convexHull R (↑s : Set E))
    (hext : Set.extremePoints R (convexHull R (↑s : Set E)) ⊆ C) :
    convexHull R (↑s : Set E) ⊆ convexHull R C := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
      by_cases hall : ∀ a ∈ s, a ∈ C
      · exact convexHull_mono (by
          intro a ha
          exact hall a (by simpa using ha))
      · push Not at hall
        rcases hall with ⟨a, ha, haC⟩
        have haext : a ∉ Set.extremePoints R (convexHull R (↑s : Set E)) := by
          intro h
          exact haC (hext h)
        have herase : convexHull R (↑(s.erase a) : Set E) =
            convexHull R (↑s : Set E) :=
          convexHull_erase_eq_of_not_extremePoint_divisionRing ha haext
        have hC_erase : C ⊆ convexHull R (↑(s.erase a) : Set E) := by
          rw [herase]
          exact hC
        have hext_erase :
            Set.extremePoints R (convexHull R (↑(s.erase a) : Set E)) ⊆ C := by
          rw [herase]
          exact hext
        have hsub := ih (s.erase a) (Finset.erase_ssubset ha) hC_erase hext_erase
        rw [← herase]
        exact hsub

/- verified submission -/
theorem convexPolytope_trace_latticeEmbedding
    {F V L : Type*} [DivisionRing F] [LinearOrder F] [IsStrictOrderedRing F]
    [AddCommGroup V] [Module F V] [Lattice L]
    (φ : L → Set V) (Ω : Set V)
    (hpoly : ∀ x : L, ∃ A : Set V, A.Finite ∧ convexHull F A = φ x)
    (hinj : Function.Injective φ)
    (hmeet : ∀ x y : L, φ (x ⊓ y) = φ x ∩ φ y)
    (hjoin : ∀ x y : L, φ (x ⊔ y) = convexHull F (φ x ∪ φ y))
    (hextreme : ∀ x : L, Set.extremePoints F (φ x) ⊆ Ω) :
    let ψ : L → Set V := fun x => φ x ∩ Ω
    Function.Injective ψ ∧
      (∀ x : L, Ω ∩ convexHull F (ψ x) = ψ x) ∧
      (∀ x y : L, ψ (x ⊓ y) = ψ x ∩ ψ y) ∧
      (∀ x y : L, ψ (x ⊔ y) = Ω ∩ convexHull F (ψ x ∪ ψ y)) ∧
      ∀ x : L, convexHull F (ψ x) = φ x := by
  classical
  let ψ : L → Set V := fun x => φ x ∩ Ω
  have hconv : ∀ x : L, convexHull F (ψ x) = φ x := by
    intro x
    rcases hpoly x with ⟨A, hAfin, hA⟩
    let s : Finset V := hAfin.toFinset
    have hsA : (↑s : Set V) = A := hAfin.coe_toFinset
    have hφ : φ x = convexHull F (↑s : Set V) := by
      rw [hsA, ← hA]
    have hψ_sub : ψ x ⊆ convexHull F (↑s : Set V) := by
      intro p hp
      rw [← hφ]
      exact hp.1
    have hext_sub :
        Set.extremePoints F (convexHull F (↑s : Set V)) ⊆ ψ x := by
      intro p hp
      constructor
      · rw [hφ]
        exact extremePoints_subset hp
      · apply hextreme x
        simpa [hφ] using hp
    have hsub : convexHull F (↑s : Set V) ⊆ convexHull F (ψ x) :=
      convexHull_subset_convexHull_of_extremePoints_subset_divisionRing s hψ_sub hext_sub
    have hrev : convexHull F (ψ x) ⊆ convexHull F (↑s : Set V) := by
      apply convexHull_min hψ_sub
      exact convex_convexHull F (↑s : Set V)
    calc
      convexHull F (ψ x) = convexHull F (↑s : Set V) :=
        Set.Subset.antisymm hrev hsub
      _ = φ x := hφ.symm
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    apply hinj
    rw [← hconv x, ← hconv y, hxy]
  refine ⟨hψinj, ?_, ?_, ?_, hconv⟩
  · intro x
    rw [hconv x]
    ext p
    simp [and_comm]
  · intro x y
    ext p
    simp [hmeet, and_assoc, and_left_comm, and_comm]
  · intro x y
    have hunion : convexHull F (ψ x ∪ ψ y) = convexHull F (φ x ∪ φ y) := by
      apply Set.Subset.antisymm
      · apply convexHull_min
        · intro p hp
          rcases hp with hp | hp
          · exact subset_convexHull F (φ x ∪ φ y) (Or.inl hp.1)
          · exact subset_convexHull F (φ x ∪ φ y) (Or.inr hp.1)
        · exact convex_convexHull F (φ x ∪ φ y)
      · apply convexHull_min
        · intro p hp
          rcases hp with hp | hp
          · have hp' : p ∈ convexHull F (ψ x) := by
              rw [hconv x]
              exact hp
            exact convexHull_mono Set.subset_union_left hp'
          · have hp' : p ∈ convexHull F (ψ y) := by
              rw [hconv y]
              exact hp
            exact convexHull_mono Set.subset_union_right hp'
        · exact convex_convexHull F (ψ x ∪ ψ y)
    change φ (x ⊔ y) ∩ Ω = Ω ∩ convexHull F (ψ x ∪ ψ y)
    rw [hjoin, hunion]
    ext p
    simp [and_comm]


#check_dependency_graph "convexPolytope_trace_latticeEmbedding" against "{\"edges\":[{\"conclusion\":{\"name\":\"hconv\",\"statement\":\"∀ (x : L), (convexHull F) (ψ x) = φ x\"},\"graphEdgeId\":\"h_001_hconv\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"IsStrictOrderedRing F\"},{\"name\":\"hpoly\",\"statement\":\"∀ (x : L), ∃ A, A.Finite ∧ (convexHull F) A = φ x\"},{\"name\":\"hextreme\",\"statement\":\"∀ (x : L), Set.extremePoints F (φ x) ⊆ Ω\"}],\"rawEdgeId\":\"telescope_17\"},{\"conclusion\":{\"name\":\"hψinj\",\"statement\":\"Function.Injective ψ\"},\"graphEdgeId\":\"h_002_h_inj\",\"premises\":[{\"name\":\"hinj\",\"statement\":\"Function.Injective φ\"},{\"name\":\"hconv\",\"statement\":\"∀ (x : L), (convexHull F) (ψ x) = φ x\"}],\"rawEdgeId\":\"telescope_18\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(Function.Injective fun x => φ x ∩ Ω) ∧ (∀ (x : L), Ω ∩ (convexHull F) ((fun x => φ x ∩ Ω) x) = (fun x => φ x ∩ Ω) x) ∧ (∀ (x y : L), (fun x => φ x ∩ Ω) (x ⊓ y) = (fun x => φ x ∩ Ω) x ∩ (fun x => φ x ∩ Ω) y) ∧ (∀ (x y : L), (fun x => φ x ∩ Ω) (x ⊔ y) = Ω ∩ (convexHull F) ((fun x => φ x ∩ Ω) x ∪ (fun x => φ x ∩ Ω) y)) ∧ ∀ (x : L), (convexHull F) ((fun x => φ x ∩ Ω) x) = φ x\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hmeet\",\"statement\":\"∀ (x y : L), φ (x ⊓ y) = φ x ∩ φ y\"},{\"name\":\"hjoin\",\"statement\":\"∀ (x y : L), φ (x ⊔ y) = (convexHull F) (φ x ∪ φ y)\"},{\"name\":\"hconv\",\"statement\":\"∀ (x : L), (convexHull F) (ψ x) = φ x\"},{\"name\":\"hψinj\",\"statement\":\"Function.Injective ψ\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1299_convexpolytope_trace_latticeembedding\",\"reconstructedProofSha256\":\"d2e8da6d1a6e2bda5ee7fdc2b245db64d06e568a7aea01be31cda195b9818b8c\",\"selectedEdgeCount\":3,\"theoremName\":\"convexPolytope_trace_latticeEmbedding\",\"topologySha256\":\"05c80beeafdb73c7eb8a5d1fdb49b2806e9f9882af8cd90b50f37d0303868e47\"}"
