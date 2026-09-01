import Mathlib

/- Generated only to amortize Mathlib loading during graph export. -/

namespace Rollout_p2161_cell_entropy_inequality_for_semidiscrete_f

/- verified submission -/
theorem cell_entropy_inequality_for_semidiscrete_finite_volume_scheme
    {ι κ : Type*} [DecidableEq ι] [Fintype κ]
    (N : Finset ι)
    (V : ℝ) (hV : 0 < V)
    (A δ ε : ι → ℝ)
    (hA : ∀ r ∈ N, 0 ≤ A r)
    (hδ : ∀ r ∈ N, 0 < δ r)
    (hε : ∀ r ∈ N, 0 ≤ ε r)
    (qNeighbor : ι → κ → ℝ) (q : κ → ℝ)
    (T : ℝ) (hT : 0 < T)
    (H : ι → Matrix κ κ ℝ)
    (hH : ∀ r ∈ N, (H r).PosSemidef)
    (ρSNeighbor : ι → ℝ) (ρS : ℝ)
    (D : ι → ℝ) (dρSdt : ℝ) :
    let Δq : ι → κ → ℝ := fun r => qNeighbor r - q
    let entropyProduction : ι → ℝ := fun r =>
      ε r * dotProduct (Δq r) ((H r).mulVec (Δq r)) / (2 * T * δ r)
    let g : ι → ℝ := fun r => ε r * (ρSNeighbor r - ρS) / δ r
    dρSdt = (1 / V) * ∑ r ∈ N, A r * (-D r + g r + entropyProduction r) →
      dρSdt + (1 / V) * ∑ r ∈ N, A r * D r -
        (1 / V) * ∑ r ∈ N, A r * g r ≥ 0 := by
  intro Δq entropyProduction g hd
  have hprod : ∀ r ∈ N, 0 ≤ entropyProduction r := by
    intro r hr
    have hquad : 0 ≤ dotProduct (Δq r) ((H r).mulVec (Δq r)) := by
      simpa using (hH r hr).dotProduct_mulVec_nonneg (Δq r)
    have hden : 0 < 2 * T * δ r := by
      exact mul_pos (mul_pos (by norm_num) hT) (hδ r hr)
    exact div_nonneg (mul_nonneg (hε r hr) hquad) hden.le
  have hsum :
      ∑ r ∈ N, A r * (-D r + g r + entropyProduction r)
        = -∑ r ∈ N, A r * D r + ∑ r ∈ N, A r * g r +
            ∑ r ∈ N, A r * entropyProduction r := by
    simp_rw [mul_add, mul_neg]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  calc
    dρSdt + (1 / V) * ∑ r ∈ N, A r * D r -
        (1 / V) * ∑ r ∈ N, A r * g r
        = (1 / V) * ∑ r ∈ N, A r * entropyProduction r := by
          rw [hd, hsum]
          ring
    _ ≥ 0 := by
      exact mul_nonneg (one_div_nonneg.mpr hV.le)
        (Finset.sum_nonneg (fun r hr => mul_nonneg (hA r hr) (hprod r hr)))

end Rollout_p2161_cell_entropy_inequality_for_semidiscrete_f

namespace Rollout_p1521_orbit_contained_free_action_restrict_measu

/- verified submission -/

open scoped Pointwise

lemma smul_eq_of_smul_eq_smul_of_stabilizer_bot
    {G X : Type*} [Group G] [MulAction G X]
    (hfree : ∀ x : X, MulAction.stabilizer G x = ⊥)
    {x : X} {a b : G} (h : a • x = b • x) : a = b := by
  have hmem : b⁻¹ * a ∈ MulAction.stabilizer G x := by
    rw [MulAction.mem_stabilizer_iff]
    calc
      (b⁻¹ * a) • x = b⁻¹ • (a • x) := by simp [mul_smul]
      _ = b⁻¹ • (b • x) := by rw [h]
      _ = x := by simp
  rw [hfree x] at hmem
  have hone : b⁻¹ * a = 1 := Subgroup.mem_bot.mp hmem
  exact (inv_mul_eq_one.mp hone).symm

theorem orbit_contained_free_action_restrict_measure_preserving
    {Γ Δ Y : Type*} [Group Γ] [Group Δ] [Countable Γ] [Countable Δ]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    [MulAction Γ Y] [MulAction Δ Y]
    [MeasurableConstSMul Γ Y] [MeasurableConstSMul Δ Y]
    (hc_free : ∀ y : Y, MulAction.stabilizer Γ y = ⊥)
    (hd_free : ∀ y : Y, MulAction.stabilizer Δ y = ⊥)
    (horbit : ∀ (δ : Δ) (y : Y), ∃ γ : Γ, δ • y = γ • y)
    (A : Set Y) (hA_meas : MeasurableSet A)
    (hA_inv : ∀ δ : Δ, (fun y : Y => δ • y) '' A = A)
    (μ : MeasureTheory.Measure Y) [MeasureTheory.IsProbabilityMeasure μ]
    [MeasureTheory.SMulInvariantMeasure Γ Y μ]
    (hμA : μ A = 1) :
    ∀ (δ : Δ) (B : Set Y), MeasurableSet B → B ⊆ A →
      μ ((fun y : Y => δ • y) '' B) = μ B := by
  letI := upgradeStandardBorel Y
  intro δ B hB hBA
  let S : Γ → Set Y := fun γ ↦ {y | δ • y = γ • y}
  have hS_meas : ∀ γ : Γ, MeasurableSet (S γ) := by
    intro γ
    exact measurableSet_eq_fun
      (MeasurableConstSMul.measurable_const_smul δ)
      (MeasurableConstSMul.measurable_const_smul γ)
  have hB_eq : B = ⋃ γ : Γ, B ∩ S γ := by
    ext y
    constructor
    · intro hy
      rcases horbit δ y with ⟨γ, hγ⟩
      exact Set.mem_iUnion.2 ⟨γ, hy, hγ⟩
    · intro hy
      rcases Set.mem_iUnion.1 hy with ⟨γ, hy⟩
      exact hy.1
  have hC_meas : ∀ γ : Γ, MeasurableSet (B ∩ S γ) := by
    intro γ
    exact hB.inter (hS_meas γ)
  have hC_disjoint : Pairwise (Function.onFun Disjoint fun γ : Γ ↦ B ∩ S γ) := by
    intro γ₁ γ₂ hne
    rw [Function.onFun, Set.disjoint_left]
    intro y hy₁ hy₂
    apply hne
    exact smul_eq_of_smul_eq_smul_of_stabilizer_bot hc_free
      (hy₁.2.symm.trans hy₂.2)
  have himage_eq :
      (fun y : Y ↦ δ • y) '' B = ⋃ γ : Γ, γ • (B ∩ S γ) := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hyB, hyx⟩
      rcases horbit δ y with ⟨γ, hγ⟩
      apply Set.mem_iUnion.2
      use γ
      rw [Set.mem_smul_set]
      exact ⟨y, ⟨hyB, hγ⟩, hγ ▸ hyx⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨γ, hxγ⟩
      rw [Set.mem_smul_set] at hxγ
      rcases hxγ with ⟨y, hy, hyx⟩
      exact ⟨y, hy.1, hy.2.trans hyx⟩
  have hT_meas : ∀ γ : Γ, MeasurableSet (γ • (B ∩ S γ)) := by
    intro γ
    exact (hC_meas γ).const_smul γ
  have hT_disjoint :
      Pairwise (Function.onFun Disjoint fun γ : Γ ↦ γ • (B ∩ S γ)) := by
    intro γ₁ γ₂ hne
    rw [Function.onFun, Set.disjoint_left]
    intro x hx₁ hx₂
    rw [Set.mem_smul_set] at hx₁ hx₂
    rcases hx₁ with ⟨y₁, hy₁, hx₁⟩
    rcases hx₂ with ⟨y₂, hy₂, hx₂⟩
    have hy : y₁ = y₂ := by
      apply smul_left_cancel δ
      calc
        δ • y₁ = γ₁ • y₁ := hy₁.2
        _ = x := hx₁
        _ = γ₂ • y₂ := hx₂.symm
        _ = δ • y₂ := hy₂.2.symm
    apply hne
    subst y₂
    exact smul_eq_of_smul_eq_smul_of_stabilizer_bot hc_free
      (by
        calc
          γ₁ • y₁ = x := hx₁
          _ = γ₂ • y₁ := hx₂.symm)
  calc
    μ ((fun y : Y ↦ δ • y) '' B)
        = μ (⋃ γ : Γ, γ • (B ∩ S γ)) := by rw [himage_eq]
    _ = ∑' γ : Γ, μ (γ • (B ∩ S γ)) :=
        MeasureTheory.measure_iUnion hT_disjoint hT_meas
    _ = ∑' γ : Γ, μ (B ∩ S γ) := by
        simp [MeasureTheory.measure_smul]
    _ = μ (⋃ γ : Γ, B ∩ S γ) :=
        (MeasureTheory.measure_iUnion hC_disjoint hC_meas).symm
    _ = μ B := by rw [← hB_eq]

end Rollout_p1521_orbit_contained_free_action_restrict_measu

namespace Rollout_p1747_parbelos_area_and_vertex_parallelogram

/- accepted add_to_file helper 1 -/

open MeasureTheory Set

noncomputable def parbelosParallelogramMap (u w : ℝ × ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  (LinearMap.fst ℝ ℝ ℝ).smulRight u + (LinearMap.snd ℝ ℝ ℝ).smulRight w

noncomputable def parbelosParallelogramAffineMap (C u w : ℝ × ℝ) : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) :=
  AffineMap.const ℝ (ℝ × ℝ) C + (parbelosParallelogramMap u w).toAffineMap

lemma parbelosParallelogramMap_det (u w : ℝ × ℝ) :
    LinearMap.det (parbelosParallelogramMap u w) = u.1 * w.2 - w.1 * u.2 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ)]
  rw [Matrix.det_fin_two]
  simp [parbelosParallelogramMap, LinearMap.toMatrix_apply, Module.Basis.finTwoProd_zero,
    Module.Basis.finTwoProd_one]

lemma parbelos_unit_square_hull_eq_Icc :
    convexHull ℝ ({(0 : ℝ × ℝ), (1, 0), (1, 1), (0, 1)} : Set (ℝ × ℝ)) =
      Set.Icc (0, 0) (1, 1) := by
  have hprod :
      ({(0 : ℝ × ℝ), (1, 0), (1, 1), (0, 1)} : Set (ℝ × ℝ)) =
        ({(0 : ℝ), (1 : ℝ)} : Set ℝ) ×ˢ ({(0 : ℝ), (1 : ℝ)} : Set ℝ) := by
    ext p
    constructor
    · intro hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp
    · intro hp
      rcases hp with ⟨hp1, hp2⟩
      simp at hp1 hp2
      rcases hp1 with h1 | h1 <;> rcases hp2 with h2 | h2
      · left; ext <;> simp [h1, h2]
      · right; right; right; ext <;> simp [h1, h2]
      · right; left; ext <;> simp [h1, h2]
      · right; right; left; ext <;> simp [h1, h2]
  rw [hprod, convexHull_prod, convexHull_pair,
    segment_eq_Icc (zero_le_one : (0 : ℝ) ≤ 1), Set.Icc_prod_Icc]

lemma parbelos_volume_unit_square_hull :
    volume (convexHull ℝ ({(0 : ℝ × ℝ), (1, 0), (1, 1), (0, 1)} : Set (ℝ × ℝ))) = 1 := by
  rw [parbelos_unit_square_hull_eq_Icc]
  rw [← Set.Icc_prod_Icc]
  rw [Measure.volume_eq_prod]
  rw [Measure.prod_prod]
  simp [Real.volume_Icc]

lemma parbelosParallelogramAffineMap_image_hull (C u w : ℝ × ℝ) :
    parbelosParallelogramAffineMap C u w ''
      convexHull ℝ ({(0 : ℝ × ℝ), (1, 0), (1, 1), (0, 1)} : Set (ℝ × ℝ)) =
      convexHull ℝ ({C, C + u, C + u + w, C + w} : Set (ℝ × ℝ)) := by
  rw [AffineMap.image_convexHull]
  congr 1
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases hq with rfl | rfl | rfl | rfl <;>
      simp [parbelosParallelogramAffineMap, parbelosParallelogramMap, add_assoc]
  · intro hp
    rcases hp with rfl | rfl | rfl | rfl
    · refine ⟨(0, 0), by simp, ?_⟩
      simp [parbelosParallelogramAffineMap, parbelosParallelogramMap]
    · refine ⟨(1, 0), by simp, ?_⟩
      simp [parbelosParallelogramAffineMap, parbelosParallelogramMap]
    · refine ⟨(1, 1), by simp, ?_⟩
      simp [parbelosParallelogramAffineMap, parbelosParallelogramMap, add_assoc]
    · refine ⟨(0, 1), by simp, ?_⟩
      simp [parbelosParallelogramAffineMap, parbelosParallelogramMap]

lemma parbelos_volume_hull_parallelogram (C u w : ℝ × ℝ) :
    volume (convexHull ℝ ({C, C + u, C + u + w, C + w} : Set (ℝ × ℝ))) =
      ENNReal.ofReal |u.1 * w.2 - w.1 * u.2| := by
  let Q : Set (ℝ × ℝ) :=
    convexHull ℝ ({(0 : ℝ × ℝ), (1, 0), (1, 1), (0, 1)} : Set (ℝ × ℝ))
  let A : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) := parbelosParallelogramMap u w
  have hset : convexHull ℝ ({C, C + u, C + u + w, C + w} : Set (ℝ × ℝ)) =
      (AffineMap.const ℝ (ℝ × ℝ) C + A.toAffineMap) '' Q := by
    symm
    exact parbelosParallelogramAffineMap_image_hull C u w
  rw [hset]
  have hcomp :
      (AffineMap.const ℝ (ℝ × ℝ) C + A.toAffineMap) '' Q =
        (fun p => C + p) '' (A '' Q) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨A q, ⟨q, hq, rfl⟩, by rfl⟩
    · rintro ⟨q, ⟨r, hr, rfl⟩, rfl⟩
      exact ⟨r, hr, by rfl⟩
  rw [hcomp]
  have htrans : volume ((fun p : ℝ × ℝ => C + p) '' (A '' Q)) = volume (A '' Q) := by
    have h := measure_preimage_add (μ := volume) C ((fun p : ℝ × ℝ => C + p) '' (A '' Q))
    have hpre : (fun p : ℝ × ℝ => C + p) ⁻¹'
        ((fun p : ℝ × ℝ => C + p) '' (A '' Q)) = A '' Q := by
      exact Set.preimage_image_eq _ (add_right_injective C)
    rw [hpre] at h
    exact h.symm
  rw [htrans]
  rw [Measure.addHaar_image_linearMap]
  have hA : LinearMap.det A = u.1 * w.2 - w.1 * u.2 := by
    exact parbelosParallelogramMap_det u w
  have hQ : volume Q = 1 := by
    exact parbelos_volume_unit_square_hull
  rw [hA, hQ]
  simp

lemma parbelos_volume_between_Icc
    {l u : ℝ} (hlu : l ≤ u) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x ∈ Set.Icc l u, f x ≤ g x) :
    volume {p : ℝ × ℝ | l ≤ p.1 ∧ p.1 ≤ u ∧ f p.1 ≤ p.2 ∧ p.2 ≤ g p.1} =
      ENNReal.ofReal (∫ x in l..u, g x - f x) := by
  let S : Set (ℝ × ℝ) := {p | l ≤ p.1 ∧ p.1 ≤ u ∧ f p.1 ≤ p.2 ∧ p.2 ≤ g p.1}
  have hS : MeasurableSet S := by
    dsimp [S]
    measurability
  change volume S = ENNReal.ofReal (∫ x in l..u, g x - f x)
  rw [Measure.volume_eq_prod]
  rw [Measure.prod_apply hS]
  have hsec : ∀ x : ℝ,
      volume (Prod.mk x ⁻¹' S) =
        (Set.Icc l u).indicator (fun x => ENNReal.ofReal (g x - f x)) x := by
    intro x
    by_cases hx : x ∈ Set.Icc l u
    · have hpre : Prod.mk x ⁻¹' S = Set.Icc (f x) (g x) := by
        ext y
        constructor
        · intro hy
          exact hy.2.2
        · intro hy
          exact ⟨hx.1, hx.2, hy⟩
      rw [hpre, Set.indicator_of_mem hx, Real.volume_Icc]
    · have hpre : Prod.mk x ⁻¹' S = (∅ : Set ℝ) := by
        ext y
        constructor
        · intro hy
          exact (hx ⟨hy.1, hy.2.1⟩).elim
        · intro hy
          cases hy
      rw [hpre, Set.indicator_of_notMem hx]
      simp
  rw [lintegral_congr hsec]
  rw [lintegral_indicator measurableSet_Icc]
  have hfi : Integrable (fun x => g x - f x) (volume.restrict (Set.Icc l u)) := by
    exact (hg.sub hf).integrableOn_Icc
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc l u)] fun x => g x - f x := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact sub_nonneg.mpr (hfg x hx)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfi hnn]
  congr 1
  have hintegral :
      (∫ x, g x - f x ∂(volume.restrict (Set.Icc l u))) =
        ∫ x in l..u, g x - f x := by
    calc
      (∫ x, g x - f x ∂(volume.restrict (Set.Icc l u))) =
          ∫ x in Set.Icc l u, g x - f x := by rfl
      _ = ∫ x in Set.Ioc l u, g x - f x := by
        exact integral_Icc_eq_integral_Ioc' (μ := volume) (by simp)
      _ = ∫ x in l..u, g x - f x := by
        exact (intervalIntegral.integral_of_le hlu).symm
  exact hintegral

/- accepted add_to_file helper 2 -/
lemma parbelos_region_volume_explicit
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b < 2 * a) :
    volume {p : ℝ × ℝ |
      (0 ≤ p.1 ∧ p.1 ≤ 2 * b ∧
        b / 2 - (p.1 - b) ^ 2 / (2 * b) ≤ p.2 ∧
        p.2 ≤ a - (p.1 - 2 * a) ^ 2 / (4 * a)) ∨
      (2 * b ≤ p.1 ∧ p.1 ≤ 4 * a ∧
        (2 * a - b) / 2 - (p.1 - (2 * a + b)) ^ 2 / (2 * (2 * a - b)) ≤ p.2 ∧
        p.2 ≤ a - (p.1 - 2 * a) ^ 2 / (4 * a))} =
      ENNReal.ofReal (4 * b * (2 * a - b) / 3) := by
  let U : ℝ → ℝ := fun x => a - (x - 2 * a) ^ 2 / (4 * a)
  let L : ℝ → ℝ := fun x => b / 2 - (x - b) ^ 2 / (2 * b)
  let R : ℝ → ℝ := fun x =>
    (2 * a - b) / 2 - (x - (2 * a + b)) ^ 2 / (2 * (2 * a - b))
  let P₁ : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 2 * b ∧ L p.1 ≤ p.2 ∧ p.2 ≤ U p.1}
  let P₂ : Set (ℝ × ℝ) :=
    {p | 2 * b ≤ p.1 ∧ p.1 ≤ 4 * a ∧ R p.1 ≤ p.2 ∧ p.2 ≤ U p.1}
  set c : ℝ := 2 * a - b
  have hcpos : 0 < c := by
    dsimp [c]
    exact sub_pos.mpr hba
  have hc : c ≠ 0 := ne_of_gt hcpos
  have hcdef : c = 2 * a - b := rfl
  have hUcont : Continuous U := by
    dsimp [U]
    continuity
  have hLcont : Continuous L := by
    dsimp [L]
    continuity
  have hRcont : Continuous R := by
    dsimp [R]
    continuity
  have hUL : ∀ x : ℝ, U x - L x = (c / (4 * a * b)) * x ^ 2 := by
    intro x
    dsimp [U, L]
    field_simp [ha.ne', hb.ne']
    rw [hcdef]
    ring
  have hUR : ∀ x : ℝ, U x - R x = (b / (4 * a * c)) * (4 * a - x) ^ 2 := by
    intro x
    dsimp [U, R]
    rw [← hcdef]
    field_simp [ha.ne', hc]
    rw [hcdef]
    ring
  have hUL_nonneg : ∀ x : ℝ, 0 ≤ U x - L x := by
    intro x
    rw [hUL x]
    positivity
  have hUR_nonneg : ∀ x : ℝ, 0 ≤ U x - R x := by
    intro x
    rw [hUR x]
    positivity
  have hI₁ : ∫ x in (0 : ℝ)..(2 * b), U x - L x = 2 * b ^ 2 * c / (3 * a) := by
    calc
      ∫ x in (0 : ℝ)..(2 * b), U x - L x
          = ∫ x in (0 : ℝ)..(2 * b), (c / (4 * a * b)) * x ^ 2 := by
            apply intervalIntegral.integral_congr
            intro x hx
            exact hUL x
      _ = 2 * b ^ 2 * c / (3 * a) := by
            rw [intervalIntegral.integral_const_mul, integral_pow]
            field_simp [ha.ne', hb.ne']
            ring
  have hI₂ : ∫ x in (2 * b)..(4 * a), U x - R x = 2 * b * c ^ 2 / (3 * a) := by
    calc
      ∫ x in (2 * b)..(4 * a), U x - R x
          = ∫ x in (2 * b)..(4 * a), (b / (4 * a * c)) * (4 * a - x) ^ 2 := by
            apply intervalIntegral.integral_congr
            intro x hx
            exact hUR x
      _ = ∫ x in (0 : ℝ)..(4 * a - 2 * b), (b / (4 * a * c)) * x ^ 2 := by
            have hsub :=
              intervalIntegral.integral_comp_sub_left
                (a := 2 * b) (b := 4 * a)
                (f := fun x : ℝ => (b / (4 * a * c)) * x ^ 2) (d := 4 * a)
            convert hsub using 2 <;> ring
      _ = 2 * b * c ^ 2 / (3 * a) := by
            rw [intervalIntegral.integral_const_mul, integral_pow]
            field_simp [ha.ne', hc]
            rw [hcdef]
            ring
  have hP₁vol : volume P₁ = ENNReal.ofReal (∫ x in (0 : ℝ)..(2 * b), U x - L x) := by
    apply parbelos_volume_between_Icc
    · positivity
    · exact hLcont
    · exact hUcont
    · intro x hx
      exact sub_nonneg.mp (hUL_nonneg x)
  have hP₂vol : volume P₂ = ENNReal.ofReal (∫ x in (2 * b)..(4 * a), U x - R x) := by
    apply parbelos_volume_between_Icc
    · nlinarith
    · exact hRcont
    · exact hUcont
    · intro x hx
      exact sub_nonneg.mp (hUR_nonneg x)
  have hP₂meas : MeasurableSet P₂ := by
    dsimp [P₂, U, R]
    measurability
  have hline : volume ({p : ℝ × ℝ | p.1 = 2 * b}) = 0 := by
    have hset : ({p : ℝ × ℝ | p.1 = 2 * b}) = ({2 * b} : Set ℝ) ×ˢ Set.univ := by
      ext p
      simp
    rw [hset, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hinter : volume (P₁ ∩ P₂) = 0 := by
    apply measure_mono_null _ hline
    intro p hp
    exact le_antisymm hp.1.2.1 hp.2.1
  have hPunion : volume (P₁ ∪ P₂) = volume P₁ + volume P₂ := by
    have h := measure_union_add_inter (μ := volume) P₁ hP₂meas
    rw [hinter, add_zero] at h
    exact h
  change volume (P₁ ∪ P₂) = ENNReal.ofReal (4 * b * (2 * a - b) / 3)
  rw [hPunion, hP₁vol, hP₂vol, hI₁, hI₂]
  have hI₁_nonneg : 0 ≤ 2 * b ^ 2 * c / (3 * a) := by positivity
  have hI₂_nonneg : 0 ≤ 2 * b * c ^ 2 / (3 * a) := by positivity
  rw [← ENNReal.ofReal_add hI₁_nonneg hI₂_nonneg]
  congr 1
  rw [hcdef]
  field_simp [ha.ne']
  ring

/- verified submission -/
theorem parbelos_area_and_vertex_parallelogram
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b < 2 * a) :
    let C₁ : ℝ × ℝ := (0, 0)
    let C₂ : ℝ × ℝ := (2 * b, 0)
    let C₃ : ℝ × ℝ := (4 * a, 0)
    let U : ℝ → ℝ := fun x => a - (x - 2 * a) ^ 2 / (4 * a)
    let L : ℝ → ℝ := fun x => b / 2 - (x - b) ^ 2 / (2 * b)
    let R : ℝ → ℝ := fun x => (2 * a - b) / 2 - (x - (2 * a + b)) ^ 2 / (2 * (2 * a - b))
    let P : Set (ℝ × ℝ) := {p | (0 ≤ p.1 ∧ p.1 ≤ 2 * b ∧ L p.1 ≤ p.2 ∧ p.2 ≤ U p.1) ∨
      (2 * b ≤ p.1 ∧ p.1 ≤ 4 * a ∧ R p.1 ≤ p.2 ∧ p.2 ≤ U p.1)}
    let V₁ : ℝ × ℝ := (b, b / 2)
    let V₂ : ℝ × ℝ := (2 * a, a)
    let V₃ : ℝ × ℝ := (2 * a + b, a - b / 2)
    (V₁ - C₂ = V₂ - V₃ ∧ V₂ - V₁ = V₃ - C₂) ∧
      MeasureTheory.volume P = (4 / 3 : ENNReal) * MeasureTheory.volume (convexHull ℝ ({C₂, V₁, V₂, V₃} : Set (ℝ × ℝ))) := by
  dsimp
  constructor
  · constructor
    · ext <;> ring
    · ext <;> ring
  · rw [parbelos_region_volume_explicit a b ha hb hba]
    let C : ℝ × ℝ := (2 * b, 0)
    let u : ℝ × ℝ := (2 * a + b, a - b / 2) - (2 * b, 0)
    let w : ℝ × ℝ := (b, b / 2) - (2 * b, 0)
    have hpoints :
        ({(2 * b, 0), (b, b / 2), (2 * a, a), (2 * a + b, a - b / 2)} : Set (ℝ × ℝ)) =
          ({C, C + u, C + u + w, C + w} : Set (ℝ × ℝ)) := by
      ext p
      simp [C, u, w]
      constructor
      · intro hp
        rcases hp with rfl | rfl | rfl | rfl
        · left; rfl
        · right; right; right; ext <;> ring
        · right; right; left; ext <;> ring
        · right; left; ext <;> ring
      · intro hp
        rcases hp with rfl | rfl | rfl | rfl
        · left; rfl
        · right; right; right; ext <;> ring
        · right; right; left; ext <;> ring
        · right; left; ext <;> ring
    rw [hpoints, parbelos_volume_hull_parallelogram C u w]
    have hc : 0 ≤ b * (2 * a - b) := by
      have hcpos : 0 ≤ 2 * a - b := le_of_lt (sub_pos.mpr hba)
      exact mul_nonneg (le_of_lt hb) hcpos
    have hdet : u.1 * w.2 - w.1 * u.2 = b * (2 * a - b) := by
      dsimp [u, w]
      ring
    rw [hdet, abs_of_nonneg hc]
    have h43 : (4 / 3 : ENNReal) = ENNReal.ofReal ((4 / 3 : ℝ)) := by
      rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 3 by norm_num)]
      norm_num
    rw [h43, (ENNReal.ofReal_mul (show (0 : ℝ) ≤ (4 / 3) by norm_num)).symm]
    congr 1
    ring

end Rollout_p1747_parbelos_area_and_vertex_parallelogram

namespace Rollout_p2049_scaling_implies_a_cone_distance

/- accepted add_to_file helper 1 -/
section ConeDistanceHelpers

variable {C X : Type*} [MetricSpace C]
variable (q : X × NNReal → C)

lemma cone_unit_dist_sq_mem_Icc
    (hbound : ∀ (x₀ x₁ : X), x₀ ≠ x₁ →
      0 < dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ∧
        dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ≤ 4)
    (x y : X) :
    dist (q (x, 1)) (q (y, 1)) ^ 2 ∈ Set.Icc (0 : ℝ) 4 := by
  by_cases hxy : x = y
  · subst y
    simp
  · exact ⟨(hbound x y hxy).1.le, (hbound x y hxy).2⟩

lemma cone_angle_mem_Icc (x y : X) :
    Real.arccos (1 - dist (q (x, 1)) (q (y, 1)) ^ 2 / 2) ∈
      Set.Icc (0 : ℝ) Real.pi := by
  exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

lemma cone_cos_angle
    (hbound : ∀ (x₀ x₁ : X), x₀ ≠ x₁ →
      0 < dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ∧
        dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ≤ 4)
    (x y : X) :
    Real.cos (Real.arccos (1 - dist (q (x, 1)) (q (y, 1)) ^ 2 / 2)) =
      1 - dist (q (x, 1)) (q (y, 1)) ^ 2 / 2 := by
  have h := cone_unit_dist_sq_mem_Icc (C:=C) (X:=X) q hbound x y
  rw [Set.mem_Icc] at h
  apply Real.cos_arccos
  · linarith
  · linarith

lemma cone_angle_self (x : X) :
    Real.arccos (1 - dist (q (x, 1)) (q (x, 1)) ^ 2 / 2) = 0 := by
  simp

lemma cone_angle_comm (x y : X) :
    Real.arccos (1 - dist (q (x, 1)) (q (y, 1)) ^ 2 / 2) =
      Real.arccos (1 - dist (q (y, 1)) (q (x, 1)) ^ 2 / 2) := by
  rw [dist_comm]

lemma cone_angle_eq_zero_iff
    (hbound : ∀ (x₀ x₁ : X), x₀ ≠ x₁ →
      0 < dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ∧
        dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ≤ 4)
    (x y : X) :
    Real.arccos (1 - dist (q (x, 1)) (q (y, 1)) ^ 2 / 2) = 0 ↔ x = y := by
  constructor
  · intro hθ
    by_contra hxy
    have hb := hbound x y hxy
    have hcos := cone_cos_angle (C:=C) (X:=X) q hbound x y
    rw [hθ, Real.cos_zero] at hcos
    nlinarith
  · intro hxy
    subst y
    exact cone_angle_self (C:=C) q x

lemma cone_dist_sq
    (hscale : ∀ (x₀ x₁ : X) (r₀ r₁ : NNReal),
      dist (q (x₀, r₀)) (q (x₁, r₁)) ^ 2 =
        (r₀ : ℝ) * (r₁ : ℝ) * dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 +
          ((r₀ : ℝ) - (r₁ : ℝ)) ^ 2)
    (hbound : ∀ (x₀ x₁ : X), x₀ ≠ x₁ →
      0 < dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ∧
        dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ≤ 4)
    (x y : X) (r s : NNReal) :
    dist (q (x, r)) (q (y, s)) ^ 2 =
      (r : ℝ) ^ 2 + (s : ℝ) ^ 2 -
        2 * (r : ℝ) * (s : ℝ) *
          Real.cos (Real.arccos (1 - dist (q (x, 1)) (q (y, 1)) ^ 2 / 2)) := by
  rw [hscale x y r s, cone_cos_angle (C:=C) (X:=X) q hbound x y]
  ring

end ConeDistanceHelpers

/- accepted add_to_file helper 2 -/
lemma cone_path_sq_eq_aux (A B L M : ℝ)
    (hA : 0 < Real.sin A)
    (hL : L ^ 2 = (Real.sin B / Real.sin A)^2 +
      (Real.sin (A+B)/(2*Real.sin A))^2 -
      2*(Real.sin B / Real.sin A)*(Real.sin (A+B)/(2*Real.sin A))*Real.cos A)
    (hM : M ^ 2 = (Real.sin (A+B)/(2*Real.sin A))^2 + 1 -
      2*(Real.sin (A+B)/(2*Real.sin A))*1*Real.cos B) :
    L ^ 2 = M ^ 2 := by
  rw [hL,hM]
  field_simp [ne_of_gt hA]
  rw [Real.sin_add A B]
  nlinarith [Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B]

lemma cone_path_sum_sq_aux (A B L : ℝ)
    (hA : 0 < Real.sin A)
    (hL : L ^ 2 = (Real.sin B / Real.sin A)^2 +
      (Real.sin (A+B)/(2*Real.sin A))^2 -
      2*(Real.sin B / Real.sin A)*(Real.sin (A+B)/(2*Real.sin A))*Real.cos A) :
    (L + L)^2 = (Real.sin B / Real.sin A)^2 + 1 -
      2*(Real.sin B / Real.sin A)*1*Real.cos (A+B) := by
  rw [Real.sin_add A B] at hL
  field_simp [ne_of_gt hA] at hL
  rw [Real.cos_add A B]
  rw [show (L + L)^2 = 4 * L^2 by ring]
  field_simp [ne_of_gt hA]
  nlinarith [hL, Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B]

/- accepted add_to_file helper 3 -/
section ConeDistanceTriangle

variable {C X : Type*} [MetricSpace C]
variable (q : X × NNReal → C)

lemma cone_angle_triangle
    (hscale : ∀ (x₀ x₁ : X) (r₀ r₁ : NNReal),
      dist (q (x₀, r₀)) (q (x₁, r₁)) ^ 2 =
        (r₀ : ℝ) * (r₁ : ℝ) * dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 +
          ((r₀ : ℝ) - (r₁ : ℝ)) ^ 2)
    (hbound : ∀ (x₀ x₁ : X), x₀ ≠ x₁ →
      0 < dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ∧
        dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ≤ 4)
    (x y z : X) :
    Real.arccos (1 - dist (q (x, 1)) (q (z, 1)) ^ 2 / 2) ≤
      Real.arccos (1 - dist (q (x, 1)) (q (y, 1)) ^ 2 / 2) +
        Real.arccos (1 - dist (q (y, 1)) (q (z, 1)) ^ 2 / 2) := by
  by_cases hxy : x = y
  · subst y
    rw [cone_angle_self (C:=C) q x]
    simp
  by_cases hyz : y = z
  · subst z
    rw [cone_angle_self (C:=C) q y]
    simp
  let a := Real.arccos (1 - dist (q (x, 1)) (q (y, 1)) ^ 2 / 2)
  let b := Real.arccos (1 - dist (q (y, 1)) (q (z, 1)) ^ 2 / 2)
  let c := Real.arccos (1 - dist (q (x, 1)) (q (z, 1)) ^ 2 / 2)
  have haI : a ∈ Set.Icc (0 : ℝ) Real.pi := cone_angle_mem_Icc (C:=C) q x y
  have hbI : b ∈ Set.Icc (0 : ℝ) Real.pi := cone_angle_mem_Icc (C:=C) q y z
  have hcI : c ∈ Set.Icc (0 : ℝ) Real.pi := cone_angle_mem_Icc (C:=C) q x z
  rw [Set.mem_Icc] at haI hbI hcI
  have hane : a ≠ 0 := by
    intro ha
    exact hxy ((cone_angle_eq_zero_iff (C:=C) q hbound x y).mp ha)
  have hbne : b ≠ 0 := by
    intro hb
    exact hyz ((cone_angle_eq_zero_iff (C:=C) q hbound y z).mp hb)
  have hapos : 0 < a := lt_of_le_of_ne haI.1 (Ne.symm hane)
  have hbpos : 0 < b := lt_of_le_of_ne hbI.1 (Ne.symm hbne)
  by_cases hsum : Real.pi ≤ a + b
  · exact le_trans hcI.2 hsum
  · have hslt : a + b < Real.pi := lt_of_not_ge hsum
    by_contra hcle
    have hgt : a + b < c := lt_of_not_ge hcle
    have hspos : 0 < a + b := add_pos hapos hbpos
    have halt : a < Real.pi := by nlinarith
    have hblt : b < Real.pi := by nlinarith
    have hsinA : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi hapos halt
    have hsinB : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hbpos hblt
    have hsinS : 0 < Real.sin (a + b) := Real.sin_pos_of_pos_of_lt_pi hspos hslt
    let rv : ℝ := Real.sin b / Real.sin a
    let tv : ℝ := Real.sin (a + b) / (2 * Real.sin a)
    have hrvpos : 0 < rv := div_pos hsinB hsinA
    have htvpos : 0 < tv := div_pos hsinS (by positivity)
    let r : NNReal := ⟨rv, le_of_lt hrvpos⟩
    let t : NNReal := ⟨tv, le_of_lt htvpos⟩
    let D : ℝ := dist (q (x, r)) (q (z, 1))
    let L : ℝ := dist (q (x, r)) (q (y, t))
    let M : ℝ := dist (q (y, t)) (q (z, 1))
    have htri : D ≤ L + M := dist_triangle _ _ _
    have hD : D ^ 2 = rv ^ 2 + (1 : ℝ) ^ 2 -
        2 * rv * (1 : ℝ) * Real.cos c := by
      have h := cone_dist_sq (C:=C) q hscale hbound x z r 1
      change D ^ 2 = (r : ℝ) ^ 2 + ((1 : NNReal) : ℝ) ^ 2 -
        2 * (r : ℝ) * (((1 : NNReal) : ℝ)) * Real.cos c at h
      simpa [rv] using h
    have hL : L ^ 2 = rv ^ 2 + tv ^ 2 -
        2 * rv * tv * Real.cos a := by
      have h := cone_dist_sq (C:=C) q hscale hbound x y r t
      change L ^ 2 = (r : ℝ) ^ 2 + (t : ℝ) ^ 2 -
        2 * (r : ℝ) * (t : ℝ) * Real.cos a at h
      simpa [rv, tv] using h
    have hM : M ^ 2 = tv ^ 2 + (1 : ℝ) ^ 2 -
        2 * tv * (1 : ℝ) * Real.cos b := by
      have h := cone_dist_sq (C:=C) q hscale hbound y z t 1
      change M ^ 2 = (t : ℝ) ^ 2 + ((1 : NNReal) : ℝ) ^ 2 -
        2 * (t : ℝ) * (((1 : NNReal) : ℝ)) * Real.cos b at h
      simpa [tv] using h
    have hL' : L ^ 2 = (Real.sin b / Real.sin a)^2 +
        (Real.sin (a+b)/(2*Real.sin a))^2 -
        2*(Real.sin b / Real.sin a)*(Real.sin (a+b)/(2*Real.sin a))*Real.cos a := by
      simpa [rv, tv] using hL
    have hM' : M ^ 2 = (Real.sin (a+b)/(2*Real.sin a))^2 + 1 -
        2*(Real.sin (a+b)/(2*Real.sin a))*1*Real.cos b := by
      simpa [tv] using hM
    have hsqLM : L ^ 2 = M ^ 2 :=
      cone_path_sq_eq_aux a b L M hsinA hL' hM'
    have hLM : L = M := by
      have habs := (sq_eq_sq_iff_abs_eq_abs L M).mp hsqLM
      rwa [abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg] at habs
    have hsumsq' := cone_path_sum_sq_aux a b L hsinA hL'
    have hsumsq : (L + M) ^ 2 = rv ^ 2 + 1 -
        2 * rv * (1 : ℝ) * Real.cos (a + b) := by
      rw [show M = L from hLM.symm]
      simpa [rv] using hsumsq'
    have htri_sq : D ^ 2 ≤ (L + M) ^ 2 :=
      pow_le_pow_left₀ dist_nonneg htri 2
    rw [hsumsq] at htri_sq
    have hcoss : Real.cos c < Real.cos (a + b) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (le_of_lt hspos) hcI.2 hgt
    have hDgt : rv ^ 2 + 1 - 2 * rv * (1 : ℝ) * Real.cos (a + b) < D ^ 2 := by
      rw [hD]
      have hmul := mul_lt_mul_of_pos_left hcoss hrvpos
      nlinarith
    nlinarith

end ConeDistanceTriangle

/- verified submission -/
theorem scaling_implies_a_cone_distance
    {C X : Type*} [MetricSpace C]
    (q : X × NNReal → C)
    (hq : Function.Surjective q)
    (hscale : ∀ (x₀ x₁ : X) (r₀ r₁ : NNReal),
      dist (q (x₀, r₀)) (q (x₁, r₁)) ^ 2 =
        (r₀ : ℝ) * (r₁ : ℝ) * dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 +
          ((r₀ : ℝ) - (r₁ : ℝ)) ^ 2)
    (hbound : ∀ (x₀ x₁ : X), x₀ ≠ x₁ →
      0 < dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ∧
        dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ≤ 4) :
    let d_X : X × X → ℝ := fun p =>
      Real.arccos (1 - dist (q (p.1, 1)) (q (p.2, 1)) ^ 2 / 2);
    (∀ x₀ x₁ : X, d_X (x₀, x₁) ∈ Set.Icc (0 : ℝ) Real.pi) ∧
      (∃ m : MetricSpace X, ∀ x₀ x₁ : X,
        @dist X m.toPseudoMetricSpace.toDist x₀ x₁ = d_X (x₀, x₁)) ∧
      ∀ (x₀ x₁ : X) (r₀ r₁ : NNReal),
        dist (q (x₀, r₀)) (q (x₁, r₁)) ^ 2 =
          (r₀ : ℝ) ^ 2 + (r₁ : ℝ) ^ 2 -
            2 * (r₀ : ℝ) * (r₁ : ℝ) * Real.cos (d_X (x₀, x₁)) := by
  let dX : X × X → ℝ := fun p =>
    Real.arccos (1 - dist (q (p.1, 1)) (q (p.2, 1)) ^ 2 / 2)
  change (∀ x₀ x₁ : X, dX (x₀, x₁) ∈ Set.Icc (0 : ℝ) Real.pi) ∧
    (∃ m : MetricSpace X, ∀ x₀ x₁ : X,
      @dist X m.toPseudoMetricSpace.toDist x₀ x₁ = dX (x₀, x₁)) ∧
    ∀ (x₀ x₁ : X) (r₀ r₁ : NNReal),
      dist (q (x₀, r₀)) (q (x₁, r₁)) ^ 2 =
        (r₀ : ℝ) ^ 2 + (r₁ : ℝ) ^ 2 -
          2 * (r₀ : ℝ) * (r₁ : ℝ) * Real.cos (dX (x₀, x₁))
  let θ : X → X → ℝ := fun x y => dX (x, y)
  have hself : ∀ x : X, θ x x = 0 := by
    intro x
    exact cone_angle_self (C:=C) q x
  have hcomm : ∀ x y : X, θ x y = θ y x := by
    intro x y
    exact cone_angle_comm (C:=C) q x y
  have htriangle : ∀ x y z : X, θ x z ≤ θ x y + θ y z := by
    intro x y z
    exact cone_angle_triangle (C:=C) q hscale hbound x y z
  letI dinst : Dist X := ⟨θ⟩
  letI pms : PseudoMetricSpace X := {
    dist_self := hself
    dist_comm := hcomm
    dist_triangle := htriangle
  }
  let ms : MetricSpace X := MetricSpace.mk (by
    intro x y hxy
    exact (cone_angle_eq_zero_iff (C:=C) q hbound x y).mp hxy)
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    exact cone_angle_mem_Icc (C:=C) q x y
  · refine ⟨ms, ?_⟩
    intro x y
    rfl
  · intro x y r s
    exact cone_dist_sq (C:=C) q hscale hbound x y r s

end Rollout_p2049_scaling_implies_a_cone_distance

namespace Rollout_p1067_complex_exp_modulus_bounds

/- verified submission -/
theorem complex_exp_modulus_bounds :
  let f : ℂ → ℂ := fun z => z + 1 + Complex.exp (-z)
  ∀ z : ℂ, -z.re ≥ ‖z‖ / 2 ∧ -z.re ≥ 3 →
    (1 / 2) * Real.exp (-z.re) ≤ ‖f z‖ ∧
      ‖f z‖ ≤ 2 * Real.exp (-z.re) := by
  intro f z hz
  have hx3 : 3 ≤ -z.re := hz.2
  have hnormz : ‖z‖ ≤ 2 * (-z.re) := by
    have h := hz.1
    nlinarith
  have hexp : 4 * (-z.re) + 2 ≤ Real.exp (-z.re) := by
    have hsum := Real.sum_le_exp_of_nonneg (show 0 ≤ -z.re by linarith) 5
    norm_num [Finset.sum_range_succ] at hsum
    nlinarith [sq_nonneg ((-z.re) - 3), sq_nonneg (-z.re)]
  have hz1 : ‖z + 1‖ ≤ (1 / 2) * Real.exp (-z.re) := by
    calc
      ‖z + 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_add_le z 1
      _ = ‖z‖ + 1 := by simp
      _ ≤ (1 / 2) * Real.exp (-z.re) := by
        nlinarith [Real.exp_nonneg (-z.re)]
  have hnormexp : ‖Complex.exp (-z)‖ = Real.exp (-z.re) := by
    simpa using Complex.norm_exp (-z)
  have hlower_core :
      (1 / 2) * Real.exp (-z.re) ≤ ‖z + 1 + Complex.exp (-z)‖ := by
    have hrev := norm_sub_le_norm_add (Complex.exp (-z)) (z + 1)
    rw [hnormexp] at hrev
    have hrev' : Real.exp (-z.re) - ‖z + 1‖ ≤ ‖z + 1 + Complex.exp (-z)‖ := by
      simpa [add_comm, add_left_comm, add_assoc] using hrev
    nlinarith [Real.exp_nonneg (-z.re)]
  have hupper_core :
      ‖z + 1 + Complex.exp (-z)‖ ≤ 2 * Real.exp (-z.re) := by
    have htri := norm_add_le (z + 1) (Complex.exp (-z))
    rw [hnormexp] at htri
    nlinarith [Real.exp_nonneg (-z.re)]
  exact ⟨hlower_core, hupper_core⟩

end Rollout_p1067_complex_exp_modulus_bounds

namespace Rollout_p1335_quarter_stratifiable_diagonal_isgdelta_and

/- verified submission -/
theorem quarter_stratifiable_diagonal_isGDelta_and_countable_pseudocharacter
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (g : ℕ → X → Set X)
    (hg_open : ∀ n a, IsOpen (g n a))
    (hg_cover : ∀ n, ⋃ a, g n a = Set.univ)
    (hg_converges : ∀ (x : X) (a : ℕ → X),
      (∀ n, x ∈ g n (a n)) → Filter.Tendsto a Filter.atTop (nhds x)) :
    (∃ G : ℕ → Set (X × X),
      (∀ n, IsOpen (G n)) ∧
      Set.diagonal X = ⋂ n, G n) ∧
    ∀ x : X, ∃ V : ℕ → Set X,
      (∀ n, IsOpen (V n) ∧ x ∈ V n) ∧
      ⋂ n, V n = {x} := by
  classical
  constructor
  · refine ⟨fun n => ⋃ a, (g n a) ×ˢ (g n a), ?_, ?_⟩
    · intro n
      exact isOpen_iUnion fun a => (hg_open n a).prod (hg_open n a)
    · ext p
      constructor
      · intro hp
        rw [Set.mem_diagonal_iff] at hp
        rw [Set.mem_iInter]
        intro n
        have hc : p.1 ∈ ⋃ a, g n a := by
          rw [hg_cover n]
          trivial
        rw [Set.mem_iUnion] at hc
        rcases hc with ⟨a, hpa⟩
        rw [Set.mem_iUnion]
        exact ⟨a, by
          rw [Set.mem_prod]
          exact ⟨hpa, by simpa [hp] using hpa⟩⟩
      · intro hp
        rw [Set.mem_diagonal_iff]
        have hchoice : ∀ n, ∃ a, p.1 ∈ g n a ∧ p.2 ∈ g n a := by
          intro n
          have hpn : p ∈ ⋃ a, (g n a) ×ˢ (g n a) := Set.mem_iInter.mp hp n
          rw [Set.mem_iUnion] at hpn
          rcases hpn with ⟨a, hpa⟩
          exact ⟨a, Set.mem_prod.mp hpa⟩
        choose a ha using hchoice
        have hlim₁ := hg_converges p.1 a fun n => (ha n).1
        have hlim₂ := hg_converges p.2 a fun n => (ha n).2
        exact tendsto_nhds_unique hlim₁ hlim₂
  · intro x
    have hchoice : ∀ n, ∃ a, x ∈ g n a := by
      intro n
      have hx : x ∈ ⋃ a, g n a := by
        rw [hg_cover n]
        trivial
      rw [Set.mem_iUnion] at hx
      exact hx
    choose a ha using hchoice
    refine ⟨fun n => g n (a n), ?_, ?_⟩
    · intro n
      exact ⟨hg_open n (a n), ha n⟩
    · ext y
      constructor
      · intro hy
        have hy' : ∀ n, y ∈ g n (a n) := Set.mem_iInter.mp hy
        have hlimy := hg_converges y a hy'
        have hlimx := hg_converges x a ha
        have hyx : y = x := tendsto_nhds_unique hlimy hlimx
        simpa [hyx]
      · intro hy
        have hyx : y = x := by simpa using hy
        rw [Set.mem_iInter]
        intro n
        simpa [hyx] using ha n

end Rollout_p1335_quarter_stratifiable_diagonal_isgdelta_and

namespace Rollout_p2581_looptree_height_bound

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

end Rollout_p2581_looptree_height_bound

namespace Rollout_p1089_logarithmic_average_bound

/- accepted add_to_file helper 1 -/
lemma sum_range_mul_eq_sum_filter {M : Type*} [AddCommMonoid M]
    (m N : ℕ) (hm : 0 < m) (f : {n : ℕ // 0 < n} → M) :
    (∑ k ∈ Finset.range (N / m),
        f ⟨m * (k + 1), Nat.mul_pos hm (Nat.zero_lt_succ k)⟩)
      =
    ∑ j ∈ Finset.range N,
      if m ∣ j + 1 then f ⟨j + 1, Nat.zero_lt_succ j⟩ else 0 := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij
    (fun k _ => m * (k + 1) - 1) ?_ ?_ ?_ ?_
  · intro k hk
    have hk1 : k + 1 ≤ N / m := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
    have hmul : m * (k + 1) ≤ N := by
      simpa [mul_comm] using Nat.mul_le_of_le_div m (k + 1) N hk1
    have hpos : 0 < m * (k + 1) := Nat.mul_pos hm (Nat.zero_lt_succ k)
    have hj : m * (k + 1) - 1 < N := Nat.sub_one_lt_of_le hpos hmul
    simp [Finset.mem_filter, Finset.mem_range, hj, Nat.sub_add_cancel hpos]
  · intro k₁ hk₁ k₂ hk₂ h
    have h₁ : 0 < m * (k₁ + 1) := Nat.mul_pos hm (Nat.zero_lt_succ k₁)
    have h₂ : 0 < m * (k₂ + 1) := Nat.mul_pos hm (Nat.zero_lt_succ k₂)
    have hs : m * (k₁ + 1) = m * (k₂ + 1) := by
      have := congrArg (· + 1) h
      simpa [Nat.sub_add_cancel h₁, Nat.sub_add_cancel h₂] using this
    have hk : k₁ + 1 = k₂ + 1 := Nat.mul_left_cancel hm hs
    exact Nat.succ.inj hk
  · intro j hj
    have hjmem := Finset.mem_filter.mp hj
    have hjr : j < N := Finset.mem_range.mp hjmem.1
    have hd : m ∣ j + 1 := hjmem.2
    rcases hd with ⟨t, ht⟩
    have htpos : 0 < t := by
      by_contra htz
      have ht0 : t = 0 := Nat.eq_zero_of_not_pos htz
      have : j + 1 = 0 := by simpa [ht0] using ht
      exact Nat.succ_ne_zero j this
    have htmul : m * t ≤ N := by
      have : j + 1 ≤ N := Nat.succ_le_of_lt hjr
      rw [ht] at this
      exact this
    have htdiv : t ≤ N / m := (Nat.le_div_iff_mul_le hm).mpr (by simpa [mul_comm] using htmul)
    refine ⟨t - 1, Finset.mem_range.mpr (Nat.sub_one_lt_of_le htpos htdiv), ?_⟩
    have hsucc : t - 1 + 1 = t := Nat.sub_add_cancel htpos
    change m * (t - 1 + 1) - 1 = j
    rw [hsucc]
    omega
  · intro k hk
    have hpos : 0 < m * (k + 1) := Nat.mul_pos hm (Nat.zero_lt_succ k)
    simp [Nat.sub_add_cancel hpos]

/- accepted add_to_file helper 2 -/
lemma period_weight_square_avg
    (B : Finset {n : ℕ // 0 < n}) (hB : B.Nonempty) :
    let q : ℕ := ∏ m ∈ B, m.1
    let S : ℝ := ∑ m ∈ B, 1 / (m.1 : ℝ)
    (q : ℝ)⁻¹ *
      (∑ j ∈ Finset.range q,
        (1 - (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) / S) ^ 2)
      =
    S⁻¹ ^ 2 *
      (∑ m ∈ B, ∑ n ∈ B,
        (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - 1 := by
  classical
  intro q S
  have hq : 0 < q := Finset.prod_pos (fun m _ => m.2)
  have hS : 0 < S := by
    apply Finset.sum_pos _ hB
    intro m hm
    exact one_div_pos.mpr (by exact_mod_cast m.2)
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hSR : S ≠ 0 := hS.ne'
  have hdvd : ∀ m ∈ B, m.1 ∣ q := fun m hm => Finset.dvd_prod_of_mem (fun x => x.1) hm
  have hsum_d :
      (∑ j ∈ Finset.range q, ∑ m ∈ B,
          if m.1 ∣ j + 1 then (1 : ℝ) else 0)
        = (q : ℝ) * S := by
    rw [Finset.sum_comm]
    trans ∑ m ∈ B, (((q / m.1 : ℕ) : ℝ))
    · refine Finset.sum_congr rfl ?_
      intro m hm
      rw [Finset.sum_boole, Nat.card_multiples]
    · change (∑ m ∈ B, (((q / m.1 : ℕ) : ℝ))) =
        (q : ℝ) * (∑ m ∈ B, 1 / (m.1 : ℝ))
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro m hm
      have hmR : (m.1 : ℝ) ≠ 0 := by exact_mod_cast m.2.ne'
      rw [Nat.cast_div (hdvd m hm) hmR]
      field_simp [hmR]
  have hsum_d_card :
      (∑ j ∈ Finset.range q,
          (((B.filter fun m => m.1 ∣ j + 1).card : ℝ)))
        = (q : ℝ) * S := by
    trans ∑ j ∈ Finset.range q, ∑ m ∈ B,
      if m.1 ∣ j + 1 then (1 : ℝ) else 0
    · refine Finset.sum_congr rfl ?_
      intro j hj
      rw [← Finset.sum_boole]
    · exact hsum_d
  have hsum_dsq :
      (∑ j ∈ Finset.range q,
          (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) ^ 2)
        =
      ∑ m ∈ B, ∑ n ∈ B, (((q / Nat.lcm m.1 n.1 : ℕ) : ℝ)) := by
    calc
      (∑ j ∈ Finset.range q,
          (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) ^ 2)
          =
        ∑ j ∈ Finset.range q,
          (∑ m ∈ B, ∑ n ∈ B,
            if Nat.lcm m.1 n.1 ∣ j + 1 then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [sq, Finset.sum_mul_sum]
            refine Finset.sum_congr rfl ?_
            intro m hm
            refine Finset.sum_congr rfl ?_
            intro n hn
            by_cases hlm : Nat.lcm m.1 n.1 ∣ j + 1
            · have hm : m.1 ∣ j + 1 := (Nat.lcm_dvd_iff.mp hlm).1
              have hn : n.1 ∣ j + 1 := (Nat.lcm_dvd_iff.mp hlm).2
              simp [hlm, hm, hn]
            · have hnot : ¬ (m.1 ∣ j + 1 ∧ n.1 ∣ j + 1) := by
                intro h
                exact hlm (Nat.lcm_dvd_iff.mpr h)
              by_cases hm : m.1 ∣ j + 1
              · by_cases hn : n.1 ∣ j + 1
                · exact False.elim (hnot ⟨hm, hn⟩)
                · simp [hm, hn, hlm]
              · simp [hm, hlm]
      _ = ∑ m ∈ B, ∑ n ∈ B,
            (∑ j ∈ Finset.range q,
              if Nat.lcm m.1 n.1 ∣ j + 1 then (1 : ℝ) else 0) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro m hm
            rw [Finset.sum_comm]
      _ = ∑ m ∈ B, ∑ n ∈ B, (((q / Nat.lcm m.1 n.1 : ℕ) : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            refine Finset.sum_congr rfl ?_
            intro n hn
            rw [Finset.sum_boole, Nat.card_multiples]
  have hlcm_cast : ∀ m ∈ B, ∀ n ∈ B,
      (((q / Nat.lcm m.1 n.1 : ℕ) : ℝ))
        = (q : ℝ) * ((Nat.gcd m.1 n.1 : ℝ) / ((m.1 : ℝ) * (n.1 : ℝ))) := by
    intro m hm n hn
    have hmpos : (m.1 : ℝ) ≠ 0 := by exact_mod_cast m.2.ne'
    have hnpos : (n.1 : ℝ) ≠ 0 := by exact_mod_cast n.2.ne'
    have hgcdpos_nat : 0 < Nat.gcd m.1 n.1 := Nat.gcd_pos_of_pos_left n.1 m.2
    have hlcmpos_nat : 0 < Nat.lcm m.1 n.1 := Nat.lcm_pos m.2 n.2
    have hlcmdvd : Nat.lcm m.1 n.1 ∣ q := by
      exact Nat.lcm_dvd_iff.mpr ⟨hdvd m hm, hdvd n hn⟩
    have hlcmR : ((Nat.lcm m.1 n.1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast hlcmpos_nat.ne'
    rw [Nat.cast_div hlcmdvd hlcmR]
    have hgl : (Nat.gcd m.1 n.1 : ℝ) * (Nat.lcm m.1 n.1 : ℝ)
        = (m.1 : ℝ) * (n.1 : ℝ) := by
      exact_mod_cast Nat.gcd_mul_lcm m.1 n.1
    field_simp [hlcmR, hmpos, hnpos]
    linarith [hgl]
  have hsum_dsq' :
      (∑ j ∈ Finset.range q,
          (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) ^ 2)
        =
      (q : ℝ) *
      (∑ m ∈ B, ∑ n ∈ B,
        (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) := by
    rw [hsum_dsq]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro m hm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [hlcm_cast m hm n hn]
    have hgcomm : Nat.gcd m.1 n.1 = Nat.gcd n.1 m.1 := Nat.gcd_comm m.1 n.1
    rw [hgcomm]
    ring
  calc
    (q : ℝ)⁻¹ *
        (∑ j ∈ Finset.range q,
          (1 - (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) / S) ^ 2)
        =
      (q : ℝ)⁻¹ *
        (∑ j ∈ Finset.range q,
          (1 - 2 / S *
            (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0)
            +
            (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) ^ 2 / S ^ 2)) := by
          refine congrArg _ ?_
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ = (q : ℝ)⁻¹ *
          ((q : ℝ) - 2 / S * ((q : ℝ) * S)
            + ((q : ℝ) *
              (∑ m ∈ B, ∑ n ∈ B,
                (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ)))) / S ^ 2) := by
          congr 1
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          congr 1
          · congr 1
            · simp
            · first
              | calc
                  (∑ j ∈ Finset.range q,
                      2 / S * (∑ m ∈ B,
                        if m.1 ∣ j + 1 then (1 : ℝ) else 0))
                      =
                    2 / S *
                      (∑ j ∈ Finset.range q, ∑ m ∈ B,
                        if m.1 ∣ j + 1 then (1 : ℝ) else 0) := by
                      rw [← Finset.mul_sum]
                  _ = 2 / S * ((q : ℝ) * S) := by
                      rw [hsum_d]
              | calc
                  (∑ j ∈ Finset.range q,
                      2 / S * (((B.filter fun m => m.1 ∣ j + 1).card : ℝ)))
                      =
                    2 / S *
                      (∑ j ∈ Finset.range q,
                        (((B.filter fun m => m.1 ∣ j + 1).card : ℝ))) := by
                      rw [← Finset.mul_sum]
                  _ = 2 / S * ((q : ℝ) * S) := by
                      rw [hsum_d_card]
          · congr 1
            calc
              (∑ j ∈ Finset.range q,
                  (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) ^ 2 / S ^ 2)
                  =
                (∑ j ∈ Finset.range q,
                  (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) ^ 2) / S ^ 2 := by
                  rw [← Finset.sum_div]
              _ =
                ((q : ℝ) *
                  (∑ m ∈ B, ∑ n ∈ B,
                    (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ)))) / S ^ 2 := by
                  rw [hsum_dsq']
    _ = S⁻¹ ^ 2 *
          (∑ m ∈ B, ∑ n ∈ B,
            (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - 1 := by
          field_simp [hqR, hSR] <;> ring

/- accepted add_to_file helper 3 -/
lemma nested_log_avg_gcd
    (B : Finset {n : ℕ // 0 < n}) (hB : B.Nonempty) :
    let S : ℝ := ∑ m ∈ B, 1 / (m.1 : ℝ)
    (∑ m ∈ B,
        ((∑ n ∈ B, ((Nat.gcd n.1 m.1 : ℝ) - 1) / (n.1 : ℝ)) / S)
          / (m.1 : ℝ)) / S
      =
    S⁻¹ ^ 2 *
      (∑ m ∈ B, ∑ n ∈ B,
        (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - 1 := by
  classical
  intro S
  have hS : 0 < S := by
    apply Finset.sum_pos _ hB
    intro m hm
    exact one_div_pos.mpr (by exact_mod_cast m.2)
  have hS0 : S ≠ 0 := hS.ne'
  have h_inner : ∀ m ∈ B,
      (∑ n ∈ B, ((Nat.gcd n.1 m.1 : ℝ) - 1) / (n.1 : ℝ))
        = (∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S := by
    intro m hm
    calc
      (∑ n ∈ B, ((Nat.gcd n.1 m.1 : ℝ) - 1) / (n.1 : ℝ))
          = ∑ n ∈ B,
            ((Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ) - 1 / (n.1 : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            ring
      _ = (∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S := by
            rw [Finset.sum_sub_distrib]
  have h_factor :
      (∑ m ∈ B,
          (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / S)
            / (m.1 : ℝ)) / S
        =
      S⁻¹ ^ 2 * ∑ m ∈ B,
        (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / (m.1 : ℝ)) := by
    calc
      (∑ m ∈ B,
          (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / S)
            / (m.1 : ℝ)) / S
          =
        ∑ m ∈ B,
          ((((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / S)
            / (m.1 : ℝ)) / S := by
          rw [Finset.sum_div]
      _ =
        ∑ m ∈ B,
          S⁻¹ ^ 2 *
            (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / (m.1 : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          ring
      _ = S⁻¹ ^ 2 * ∑ m ∈ B,
          (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / (m.1 : ℝ)) := by
          rw [← Finset.mul_sum]
  have h_split :
      (∑ m ∈ B,
          (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / (m.1 : ℝ)))
        =
      (∑ m ∈ B, ∑ n ∈ B,
          (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - S ^ 2 := by
    calc
      (∑ m ∈ B,
          (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / (m.1 : ℝ)))
          =
        ∑ m ∈ B,
          (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) / (m.1 : ℝ))
            - S / (m.1 : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          ring
      _ =
        (∑ m ∈ B,
            ((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) / (m.1 : ℝ)))
          - ∑ m ∈ B, S / (m.1 : ℝ) := by
          rw [Finset.sum_sub_distrib]
      _ =
      (∑ m ∈ B, ∑ n ∈ B,
          (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - S ^ 2 := by
          congr 1
          · refine Finset.sum_congr rfl ?_
            intro m hm
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl ?_
            intro n hn
            ring
          · calc
              (∑ m ∈ B, S / (m.1 : ℝ))
                  = S * (∑ m ∈ B, 1 / (m.1 : ℝ)) := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl ?_
                  intro m hm
                  ring
              _ = S ^ 2 := by
                  change S * S = S ^ 2
                  ring
  have hcancel : S⁻¹ ^ 2 * S ^ 2 = 1 := by
    have h : S⁻¹ * S = 1 := inv_mul_cancel₀ hS0
    calc
      S⁻¹ ^ 2 * S ^ 2 = (S⁻¹ * S) ^ 2 := by ring
      _ = 1 ^ 2 := by rw [h]
      _ = 1 := by norm_num
  calc
    (∑ m ∈ B,
        ((∑ n ∈ B, ((Nat.gcd n.1 m.1 : ℝ) - 1) / (n.1 : ℝ)) / S)
          / (m.1 : ℝ)) / S
        =
      (∑ m ∈ B,
        (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / S)
          / (m.1 : ℝ)) / S := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro m hm
        rw [h_inner m hm]
    _ = S⁻¹ ^ 2 * ∑ m ∈ B,
          (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / (m.1 : ℝ)) :=
        h_factor
    _ = S⁻¹ ^ 2 *
          ((∑ m ∈ B, ∑ n ∈ B,
            (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - S ^ 2) := by
        rw [h_split]
    _ = S⁻¹ ^ 2 *
          (∑ m ∈ B, ∑ n ∈ B,
            (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - 1 := by
        calc
          S⁻¹ ^ 2 *
              ((∑ m ∈ B, ∑ n ∈ B,
                (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - S ^ 2)
              =
            S⁻¹ ^ 2 *
              (∑ m ∈ B, ∑ n ∈ B,
                (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ)))
              - S⁻¹ ^ 2 * S ^ 2 := by
            ring
          _ = S⁻¹ ^ 2 *
              (∑ m ∈ B, ∑ n ∈ B,
                (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - 1 := by
            rw [hcancel]

/- accepted add_to_file helper 4 -/
lemma sum_range_blocks_le
    (f W : ℕ → ℝ) (q Q r : ℕ)
    (hW : ∀ j, 0 ≤ W j)
    (hblock : ∀ i j, j < q → f (i * q + j) ≤ W j)
    (htail : ∀ j, j < r → f (Q * q + j) ≤ W j)
    (hr : r ≤ q) :
    (∑ j ∈ Finset.range (Q * q + r), f j) ≤ (Q + 1 : ℝ) * ∑ j ∈ Finset.range q, W j := by
  classical
  have hfull : ∀ Q : ℕ,
      (∑ j ∈ Finset.range (Q * q), f j) ≤ (Q : ℝ) * ∑ j ∈ Finset.range q, W j := by
    intro Q
    induction Q with
    | zero => simp
    | succ Q ih =>
        rw [Nat.succ_mul, Finset.sum_range_add]
        calc
          (∑ j ∈ Finset.range (Q * q), f j) +
              (∑ j ∈ Finset.range q, f (Q * q + j))
              ≤ (Q : ℝ) * (∑ j ∈ Finset.range q, W j) +
                  (∑ j ∈ Finset.range q, W j) := by
                exact add_le_add ih (Finset.sum_le_sum (fun j hj => hblock Q j (Finset.mem_range.mp hj)))
          _ = ((Q + 1 : ℕ) : ℝ) * ∑ j ∈ Finset.range q, W j := by
                norm_num
                ring
  rw [Finset.sum_range_add]
  calc
    (∑ j ∈ Finset.range (Q * q), f j) +
        (∑ j ∈ Finset.range r, f (Q * q + j))
        ≤ (Q : ℝ) * (∑ j ∈ Finset.range q, W j) +
            (∑ j ∈ Finset.range q, W j) := by
          refine add_le_add (hfull Q) ?_
          calc
            (∑ j ∈ Finset.range r, f (Q * q + j))
                ≤ ∑ j ∈ Finset.range r, W j :=
                Finset.sum_le_sum (fun j hj => htail j (Finset.mem_range.mp hj))
            _ ≤ ∑ j ∈ Finset.range q, W j := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro j hj
                  exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) hr)
                · intro j hj _
                  exact hW j
    _ = (Q + 1 : ℝ) * ∑ j ∈ Finset.range q, W j := by
          ring

/- accepted add_to_file helper 5 -/
lemma weighted_prefix_bound_generic
    (a : {n : ℕ // 0 < n} → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (q : ℕ) (hq : 0 < q) (w : ℕ → ℝ)
    (hperiod : ∀ i j, w (i * q + j) = w j)
    (N : ℕ) (hN : 0 < N) :
    let T : ℝ := ∑ j ∈ Finset.range q, |w j|
    ‖(N : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
        a ⟨j + 1, Nat.zero_lt_succ j⟩ * (w j : ℂ)‖
      ≤
    Real.sqrt ((q : ℝ)⁻¹ * ∑ j ∈ Finset.range q, (w j) ^ 2) + T / N := by
  classical
  intro T
  let Q : ℕ := N / q
  let r : ℕ := N % q
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hqr : N = Q * q + r := by
    calc
      N = q * (N / q) + N % q := (Nat.div_add_mod N q).symm
      _ = Q * q + r := by
        dsimp [Q, r]
        rw [mul_comm]
  have hr : r ≤ q := by
    exact le_of_lt (Nat.mod_lt N hq)
  have hTnonneg : 0 ≤ T := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hterm : ∀ i j, j < q →
      ‖a ⟨(i * q + j) + 1, Nat.zero_lt_succ _⟩ * (w (i * q + j) : ℂ)‖ ≤ |w j| := by
    intro i j hj
    rw [hperiod i j]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg _) (ha _)
  have hterm_tail : ∀ j, j < r →
      ‖a ⟨(Q * q + j) + 1, Nat.zero_lt_succ _⟩ * (w (Q * q + j) : ℂ)‖ ≤ |w j| := by
    intro j hj
    rw [hperiod Q j]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg _) (ha _)
  have hsum_norm :
      (∑ j ∈ Finset.range N,
          ‖a ⟨j + 1, Nat.zero_lt_succ j⟩ * (w j : ℂ)‖)
        ≤ (Q + 1 : ℝ) * T := by
    conv_lhs => rw [hqr]
    exact sum_range_blocks_le
      (fun j => ‖a ⟨j + 1, Nat.zero_lt_succ j⟩ * (w j : ℂ)‖)
      (fun j => |w j|) q Q r
      (fun j => abs_nonneg _) hterm hterm_tail hr
  have hmain0 :
      ‖(N : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
          a ⟨j + 1, Nat.zero_lt_succ j⟩ * (w j : ℂ)‖
        ≤ (N : ℝ)⁻¹ * ((Q + 1 : ℝ) * T) := by
    rw [norm_mul]
    have hn : ‖(N : ℂ)⁻¹‖ = (N : ℝ)⁻¹ := by
      simp [norm_inv]
    rw [hn]
    exact mul_le_mul_of_nonneg_left
      ((norm_sum_le _ _).trans hsum_norm)
      (inv_nonneg.mpr (by positivity))
  have hQle : (Q : ℝ) / N ≤ 1 / q := by
    have hmul : Q * q ≤ N := Nat.div_mul_le_self N q
    have hmulR : (Q : ℝ) * q ≤ N := by exact_mod_cast hmul
    have hqposR : (0 : ℝ) < q := by exact_mod_cast hq
    have hNposR : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_le_div_iff₀ hNposR hqposR]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmulR
  have hfactor :
      (N : ℝ)⁻¹ * ((Q + 1 : ℝ) * T) ≤ (1 / q + 1 / N) * T := by
    have hfrac : ((Q + 1 : ℝ)) / N ≤ 1 / q + 1 / N := by
      calc
        ((Q + 1 : ℝ)) / N = (Q : ℝ) / N + 1 / N := by ring
        _ ≤ 1 / q + 1 / N := add_le_add hQle le_rfl
    calc
      (N : ℝ)⁻¹ * ((Q + 1 : ℝ) * T)
          = ((Q + 1 : ℝ) / N) * T := by ring
      _ ≤ (1 / q + 1 / N) * T :=
          mul_le_mul_of_nonneg_right hfrac hTnonneg
  have hcs : T / q ≤
      Real.sqrt ((q : ℝ)⁻¹ * ∑ j ∈ Finset.range q, (w j) ^ 2) := by
    have hsq := sq_sum_le_card_mul_sum_sq (s := Finset.range q) (f := fun j => |w j|)
    have hsq' : T ^ 2 ≤ (q : ℝ) * ∑ j ∈ Finset.range q, (w j) ^ 2 := by
      simpa [T, sq_abs] using hsq
    apply Real.le_sqrt_of_sq_le
    calc
      (T / q) ^ 2 = T ^ 2 / (q : ℝ) ^ 2 := by ring
      _ ≤ ((q : ℝ) * ∑ j ∈ Finset.range q, (w j) ^ 2) / (q : ℝ) ^ 2 := by
          exact div_le_div_of_nonneg_right hsq' (sq_nonneg _)
      _ = (q : ℝ)⁻¹ * ∑ j ∈ Finset.range q, (w j) ^ 2 := by
          field_simp [hqR]
  calc
    ‖(N : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
        a ⟨j + 1, Nat.zero_lt_succ j⟩ * (w j : ℂ)‖
        ≤ (N : ℝ)⁻¹ * ((Q + 1 : ℝ) * T) := hmain0
    _ ≤ (1 / q + 1 / N) * T := hfactor
    _ = T / q + T / N := by ring
    _ ≤ Real.sqrt ((q : ℝ)⁻¹ * ∑ j ∈ Finset.range q, (w j) ^ 2) + T / N :=
        add_le_add hcs le_rfl

/- accepted add_to_file helper 6 -/
lemma local_average_mul_approx
    (a : {n : ℕ // 0 < n} → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (m N : ℕ) (hm : 0 < m) (hN : 0 < N) :
    let A : ℕ → ({n : ℕ // 0 < n} → ℂ) → ℂ := fun M c ↦
      (M : ℂ)⁻¹ * ∑ k ∈ Finset.range M, c ⟨k + 1, Nat.zero_lt_succ k⟩
    ‖A (N / m) (fun k ↦ a ⟨m * k.1, Nat.mul_pos hm k.2⟩) / (m : ℂ)
        - (N : ℂ)⁻¹ * ∑ k ∈ Finset.range (N / m),
            a ⟨m * (k + 1), Nat.mul_pos hm (Nat.zero_lt_succ k)⟩‖
      ≤ 1 / (N : ℝ) := by
  classical
  intro A
  let q : ℕ := N / m
  by_cases hq : q = 0
  · simp [A, q, hq]
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    let X : ℂ := ∑ k ∈ Finset.range q,
      a ⟨m * (k + 1), Nat.mul_pos hm (Nat.zero_lt_succ k)⟩
    have hrewrite :
        A q (fun k ↦ a ⟨m * k.1, Nat.mul_pos hm k.2⟩) / (m : ℂ)
          - (N : ℂ)⁻¹ * X
        =
        (((q : ℂ)⁻¹ / (m : ℂ) - (N : ℂ)⁻¹) * X) := by
      simp [A, X]
      ring
    have hX : ‖X‖ ≤ q := by
      calc
        ‖X‖ ≤ ∑ k ∈ Finset.range q,
            ‖a ⟨m * (k + 1), Nat.mul_pos hm (Nat.zero_lt_succ k)⟩‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.range q, (1 : ℝ) := Finset.sum_le_sum (fun k _ => ha _)
        _ = q := by simp
    have hqm : q * m ≤ N := Nat.div_mul_le_self N m
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have hqposr : (0 : ℝ) < q := by exact_mod_cast hqpos
    have hNposr : (0 : ℝ) < N := by exact_mod_cast hN
    have hdelta :
        ((q : ℂ)⁻¹ / (m : ℂ) - (N : ℂ)⁻¹)
          =
        (((((N - q * m : ℕ) : ℝ) / (((q : ℝ) * m) * N)) : ℝ) : ℂ) := by
      have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hqpos.ne'
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have hcast : (((N - q * m : ℕ) : ℝ)) = (N : ℝ) - (q : ℝ) * m := by
        simpa [Nat.cast_mul] using
          (Nat.cast_sub hqm : (((N - q*m:ℕ):ℝ)) = (N:ℝ) - (q*m:ℕ))
      have hreal : ((q : ℝ)⁻¹ / m - (N : ℝ)⁻¹)
          = (((N - q*m:ℕ):ℝ)) / ((q:ℝ)*m*N) := by
        rw [hcast]
        field_simp [hq0, hm0, hN0]
      rw [show ((q : ℂ)⁻¹ / (m : ℂ) - (N : ℂ)⁻¹)
          = ((((q : ℝ)⁻¹ / m - (N : ℝ)⁻¹) : ℝ) : ℂ) by simp]
      exact congrArg Complex.ofReal hreal
    have hbound :
        (q : ℝ) * ‖((q : ℂ)⁻¹ / (m : ℂ) - (N : ℂ)⁻¹)‖ ≤ 1 / N := by
      rw [hdelta, Complex.norm_real, Real.norm_eq_abs]
      have hnon : 0 ≤ (((N - q * m : ℕ) : ℝ) / (((q : ℝ) * m) * N)) := by positivity
      rw [abs_of_nonneg hnon]
      have hcast : (((N - q * m : ℕ) : ℝ)) = (N : ℝ) - (q : ℝ) * m := by
        simpa [Nat.cast_mul] using
          (Nat.cast_sub hqm : (((N - q*m:ℕ):ℝ)) = (N:ℝ) - (q*m:ℕ))
      rw [hcast]
      calc
        q * ((N - q * m) / (q * m * N))
            = ((N : ℝ) - q * m) / (m * N) := by
              field_simp [hqposr.ne', hmpos.ne', hNposr.ne']
        _ ≤ 1 / N := by
              rw [div_le_iff₀ (mul_pos hmpos hNposr)]
              field_simp [hNposr.ne']
              have hmod : N - q * m = N % m := by
                dsimp [q]
                rw [Nat.mod_eq_sub_mul_div]
                rw [mul_comm]
              have hlt : N - q * m < m := by
                rw [hmod]
                exact Nat.mod_lt N hm
              have hltR : (N : ℝ) - q * m < m := by
                rw [← hcast]
                exact_mod_cast hlt
              linarith
    calc
      ‖A q (fun k ↦ a ⟨m * k.1, Nat.mul_pos hm k.2⟩) / (m : ℂ)
          - (N : ℂ)⁻¹ * X‖
          = ‖((q : ℂ)⁻¹ / (m : ℂ) - (N : ℂ)⁻¹) * X‖ := by rw [hrewrite]
      _ ≤ ‖((q : ℂ)⁻¹ / (m : ℂ) - (N : ℂ)⁻¹)‖ * ‖X‖ := norm_mul_le _ _
      _ ≤ ‖((q : ℂ)⁻¹ / (m : ℂ) - (N : ℂ)⁻¹)‖ * q :=
          mul_le_mul_of_nonneg_left hX (norm_nonneg _)
      _ = (q : ℝ) * ‖((q : ℂ)⁻¹ / (m : ℂ) - (N : ℂ)⁻¹)‖ := by ring
      _ ≤ 1 / N := hbound

/- accepted add_to_file helper 7 -/
lemma global_local_approx
    (B : Finset {n : ℕ // 0 < n}) (hB : B.Nonempty)
    (a : {n : ℕ // 0 < n} → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (N : ℕ) (hN : 0 < N) :
    let A : ℕ → ({n : ℕ // 0 < n} → ℂ) → ℂ := fun M c ↦
      (M : ℂ)⁻¹ * ∑ k ∈ Finset.range M, c ⟨k + 1, Nat.zero_lt_succ k⟩
    let S : ℝ := ∑ m ∈ B, 1 / (m.1 : ℝ)
    let Sℂ : ℂ := ∑ m ∈ B, 1 / (m.1 : ℂ)
    let actual : ℂ := ∑ m ∈ B,
      A (N / m.1) (fun k ↦ a ⟨m.1 * k.1, Nat.mul_pos m.2 k.2⟩) / (m.1 : ℂ)
    let ideal : ℂ := ∑ m ∈ B,
      (N : ℂ)⁻¹ * ∑ k ∈ Finset.range (N / m.1),
        a ⟨m.1 * (k + 1), Nat.mul_pos m.2 (Nat.zero_lt_succ k)⟩
    ‖(A N a - actual / Sℂ) - (A N a - ideal / Sℂ)‖
      ≤ (B.card : ℝ) / ((N : ℝ) * S) := by
  classical
  intro A S Sℂ actual ideal
  have hS : 0 < S := by
    apply Finset.sum_pos _ hB
    intro m hm
    exact one_div_pos.mpr (by exact_mod_cast m.2)
  have hScast : Sℂ = (S : ℂ) := by
    simp [Sℂ, S]
  have hdiff :
      (A N a - actual / Sℂ) - (A N a - ideal / Sℂ)
        = (ideal - actual) / Sℂ := by
    ring
  rw [hdiff, hScast]
  have hnormden : ‖(S : ℂ)‖ = S := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS]
  rw [norm_div, hnormden]
  have hsum :
      ‖ideal - actual‖ ≤ (B.card : ℝ) / N := by
    calc
      ‖ideal - actual‖ ≤ ∑ m ∈ B,
          ‖(N : ℂ)⁻¹ * ∑ k ∈ Finset.range (N / m.1),
              a ⟨m.1 * (k + 1), Nat.mul_pos m.2 (Nat.zero_lt_succ k)⟩
            -
            A (N / m.1) (fun k ↦ a ⟨m.1 * k.1, Nat.mul_pos m.2 k.2⟩) / (m.1 : ℂ)‖ := by
            simpa [ideal, actual, Finset.sum_sub_distrib] using
              (norm_sum_le B (fun m =>
                (N : ℂ)⁻¹ * ∑ k ∈ Finset.range (N / m.1),
                  a ⟨m.1 * (k + 1), Nat.mul_pos m.2 (Nat.zero_lt_succ k)⟩
                -
                A (N / m.1) (fun k ↦ a ⟨m.1 * k.1, Nat.mul_pos m.2 k.2⟩) / (m.1 : ℂ)))
      _ ≤ ∑ m ∈ B, 1 / (N : ℝ) := by
            refine Finset.sum_le_sum ?_
            intro m hm
            rw [norm_sub_rev]
            exact local_average_mul_approx a ha m.1 N m.2 hN
      _ = (B.card : ℝ) / N := by
            rw [Finset.sum_const]
            simp [nsmul_eq_mul]
            ring
  have hSnonneg : 0 ≤ S := le_of_lt hS
  calc
    ‖ideal - actual‖ / S ≤ ((B.card : ℝ) / N) / S :=
      div_le_div_of_nonneg_right hsum hSnonneg
    _ = (B.card : ℝ) / ((N : ℝ) * S) := by ring

/- accepted add_to_file helper 8 -/
lemma weighted_prefix_eq
    (B : Finset {n : ℕ // 0 < n})
    (a : {n : ℕ // 0 < n} → ℂ)
    (N : ℕ) :
    let A : ℕ → ({n : ℕ // 0 < n} → ℂ) → ℂ := fun M c ↦
      (M : ℂ)⁻¹ * ∑ k ∈ Finset.range M, c ⟨k + 1, Nat.zero_lt_succ k⟩
    let S : ℝ := ∑ m ∈ B, 1 / (m.1 : ℝ)
    let Sℂ : ℂ := ∑ m ∈ B, 1 / (m.1 : ℂ)
    let ideal : ℂ := ∑ m ∈ B,
      (N : ℂ)⁻¹ * ∑ k ∈ Finset.range (N / m.1),
        a ⟨m.1 * (k + 1), Nat.mul_pos m.2 (Nat.zero_lt_succ k)⟩
    let w : ℕ → ℝ := fun j ↦
      1 - (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) / S
    A N a - ideal / Sℂ
      =
    (N : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
      a ⟨j + 1, Nat.zero_lt_succ j⟩ * (w j : ℂ) := by
  classical
  intro A S Sℂ ideal w
  have hScast : Sℂ = (S : ℂ) := by
    simp [Sℂ, S]
  have hlocal : ∀ m ∈ B,
      (∑ k ∈ Finset.range (N / m.1),
          a ⟨m.1 * (k + 1), Nat.mul_pos m.2 (Nat.zero_lt_succ k)⟩)
        =
      ∑ j ∈ Finset.range N,
        if m.1 ∣ j + 1 then a ⟨j + 1, Nat.zero_lt_succ j⟩ else 0 := by
    intro m hm
    exact sum_range_mul_eq_sum_filter m.1 N m.2 a
  have hideal :
      ideal =
        (N : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
          a ⟨j + 1, Nat.zero_lt_succ j⟩ *
            ((∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) : ℂ) := by
    calc
      ideal = ∑ m ∈ B, (N : ℂ)⁻¹ *
          (∑ j ∈ Finset.range N,
            if m.1 ∣ j + 1 then a ⟨j + 1, Nat.zero_lt_succ j⟩ else 0) := by
          refine Finset.sum_congr (M := ℂ) rfl ?_
          intro m hm
          rw [hlocal m hm]
      _ = (N : ℂ)⁻¹ * ∑ m ∈ B, ∑ j ∈ Finset.range N,
          (if m.1 ∣ j + 1 then a ⟨j + 1, Nat.zero_lt_succ j⟩ else 0) := by
          rw [Finset.mul_sum]
      _ = (N : ℂ)⁻¹ * ∑ j ∈ Finset.range N, ∑ m ∈ B,
          (if m.1 ∣ j + 1 then a ⟨j + 1, Nat.zero_lt_succ j⟩ else 0) := by
          exact congrArg _ (Finset.sum_comm (s := B) (t := Finset.range N)
            (f := fun m j => if m.1 ∣ j + 1 then a ⟨j + 1, Nat.zero_lt_succ j⟩ else 0))
      _ = (N : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
          a ⟨j + 1, Nat.zero_lt_succ j⟩ *
            ((∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) : ℂ) := by
          refine congrArg _ ?_
          refine Finset.sum_congr (M := ℂ) rfl ?_
          intro j hj
          rw [Finset.mul_sum]
          refine Finset.sum_congr (M := ℂ) rfl ?_
          intro m hm
          by_cases h : m.1 ∣ j + 1 <;> simp [h]
  let X : ℕ → ℂ := fun j => a ⟨j + 1, Nat.zero_lt_succ j⟩
  let Y : ℕ → ℂ := fun j =>
    a ⟨j + 1, Nat.zero_lt_succ j⟩ *
      ((∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) : ℂ)
  have hsub :
      (∑ j ∈ Finset.range N, (X j - Y j / (S : ℂ)))
        = (∑ j ∈ Finset.range N, X j) - ∑ j ∈ Finset.range N, Y j / (S : ℂ) := by
    exact Finset.sum_sub_distrib (ι := ℕ) (G := ℂ) (s := Finset.range N)
      (f := X) (g := fun j => Y j / (S : ℂ))
  have hdiv :
      ((∑ j ∈ Finset.range N, Y j) / (S : ℂ))
        = ∑ j ∈ Finset.range N, Y j / (S : ℂ) := by
    exact Finset.sum_div (ι := ℕ) (K := ℂ) (s := Finset.range N)
      (f := Y) (a := (S : ℂ))
  have hweighted :
      (∑ j ∈ Finset.range N, X j * (w j : ℂ))
        = (∑ j ∈ Finset.range N, X j) - (S : ℂ)⁻¹ * ∑ j ∈ Finset.range N, Y j := by
    calc
      (∑ j ∈ Finset.range N, X j * (w j : ℂ))
          = ∑ j ∈ Finset.range N, (X j - Y j / (S : ℂ)) := by
            refine Finset.sum_congr (M := ℂ) rfl ?_
            intro j hj
            simp [X, Y, w]
            ring
      _ = (∑ j ∈ Finset.range N, X j) - ∑ j ∈ Finset.range N, Y j / (S : ℂ) := hsub
      _ = (∑ j ∈ Finset.range N, X j) - (∑ j ∈ Finset.range N, Y j) / (S : ℂ) := by
            rw [hdiv]
      _ = (∑ j ∈ Finset.range N, X j) - (S : ℂ)⁻¹ * ∑ j ∈ Finset.range N, Y j := by
            ring
  rw [hideal, hScast, hweighted]
  change ((N : ℂ)⁻¹ * ∑ j ∈ Finset.range N, X j)
      - (((N : ℂ)⁻¹ * ∑ j ∈ Finset.range N, Y j) / (S : ℂ))
      =
    (N : ℂ)⁻¹ *
      ((∑ j ∈ Finset.range N, X j) - (S : ℂ)⁻¹ * ∑ j ∈ Finset.range N, Y j)
  ring

/- verified submission -/
theorem logarithmic_average_bound
    (B : Finset {n : ℕ // 0 < n}) (hB : B.Nonempty)
    (a : {n : ℕ // 0 < n} → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) :
    let A : ℕ → ({n : ℕ // 0 < n} → ℂ) → ℂ := fun N c ↦
      (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, c ⟨k + 1, Nat.zero_lt_succ k⟩
    let Lℂ : ({n : ℕ // 0 < n} → ℂ) → ℂ := fun h ↦
      (∑ m ∈ B, h m / (m.1 : ℂ)) / (∑ m ∈ B, 1 / (m.1 : ℂ))
    let Lℝ : ({n : ℕ // 0 < n} → ℝ) → ℝ := fun h ↦
      (∑ m ∈ B, h m / (m.1 : ℝ)) / (∑ m ∈ B, 1 / (m.1 : ℝ))
    Filter.limsup
        (fun N : ℕ ↦ ‖A N a - Lℂ (fun m ↦
          A (N / m.1) (fun k ↦ a ⟨m.1 * k.1, Nat.mul_pos m.2 k.2⟩))‖)
        Filter.atTop ≤
      Real.sqrt (Lℝ (fun m ↦ Lℝ (fun n ↦ (Nat.gcd n.1 m.1 : ℝ) - 1))) := by
  classical
  intro A Lℂ Lℝ
  let q : ℕ := ∏ m ∈ B, m.1
  let S : ℝ := ∑ m ∈ B, 1 / (m.1 : ℝ)
  let Sℂ : ℂ := ∑ m ∈ B, 1 / (m.1 : ℂ)
  let w : ℕ → ℝ := fun j ↦
    1 - (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) / S
  let T : ℝ := ∑ j ∈ Finset.range q, |w j|
  let target : ℝ := Lℝ (fun m ↦ Lℝ (fun n ↦ (Nat.gcd n.1 m.1 : ℝ) - 1))
  let K : ℝ := T + (B.card : ℝ) / S
  have hq : 0 < q := Finset.prod_pos (fun m _ => m.2)
  have hS : 0 < S := by
    apply Finset.sum_pos _ hB
    intro m hm
    exact one_div_pos.mpr (by exact_mod_cast m.2)
  have hT : 0 ≤ T := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hperiod : ∀ i j, w (i * q + j) = w j := by
    intro i j
    dsimp [w]
    congr 2
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hmq : m.1 ∣ q := Finset.dvd_prod_of_mem (fun x => x.1) hm
    have hmiq : m.1 ∣ i * q := dvd_trans hmq (dvd_mul_left q i)
    have hiff : m.1 ∣ i * q + j + 1 ↔ m.1 ∣ j + 1 := by
      have h := Nat.dvd_add_iff_right hmiq (n := j + 1)
      simpa [add_assoc, add_comm, add_left_comm] using h.symm
    simp [hiff]
  have htarget_period :
      target =
        (q : ℝ)⁻¹ * ∑ j ∈ Finset.range q, (w j) ^ 2 := by
    have hp := period_weight_square_avg B hB
    have hn := nested_log_avg_gcd B hB
    dsimp [target, Lℝ, q, S, w]
    rw [hp, hn]
  have hboundN : ∀ N, 0 < N →
      ‖A N a - Lℂ (fun m ↦
          A (N / m.1) (fun k ↦ a ⟨m.1 * k.1, Nat.mul_pos m.2 k.2⟩))‖
        ≤ Real.sqrt target + K / N := by
    intro N hN
    let actual : ℂ := Lℂ (fun m ↦
      A (N / m.1) (fun k ↦ a ⟨m.1 * k.1, Nat.mul_pos m.2 k.2⟩))
    let ideal : ℂ := ∑ m ∈ B,
      (N : ℂ)⁻¹ * ∑ k ∈ Finset.range (N / m.1),
        a ⟨m.1 * (k + 1), Nat.mul_pos m.2 (Nat.zero_lt_succ k)⟩
    let adj : ℂ := A N a - ideal / Sℂ
    have happ :
        ‖(A N a - actual) - adj‖ ≤ (B.card : ℝ) / ((N : ℝ) * S) := by
      have hg := global_local_approx B hB a ha N hN
      dsimp [actual, adj, ideal, Lℂ, Sℂ, A] at *
      exact hg
    have hadj :
        adj = (N : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
          a ⟨j + 1, Nat.zero_lt_succ j⟩ * (w j : ℂ) := by
      have hw := weighted_prefix_eq B a N
      dsimp [adj, ideal, S, Sℂ, w, A] at *
      exact hw
    have hweighted :
        ‖adj‖ ≤ Real.sqrt target + T / N := by
      have hp := weighted_prefix_bound_generic a ha q hq w hperiod N hN
      dsimp [T] at hp
      rw [hadj]
      calc
        ‖(N : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
            a ⟨j + 1, Nat.zero_lt_succ j⟩ * (w j : ℂ)‖
            ≤ Real.sqrt ((q : ℝ)⁻¹ * ∑ j ∈ Finset.range q, (w j) ^ 2) + T / N := hp
        _ = Real.sqrt target + T / N := by rw [htarget_period]
    have htri :
        ‖A N a - actual‖ ≤ ‖adj‖ + ‖(A N a - actual) - adj‖ := by
      calc
        ‖A N a - actual‖ = ‖adj + ((A N a - actual) - adj)‖ := by
          congr 1
          abel
        _ ≤ ‖adj‖ + ‖(A N a - actual) - adj‖ := norm_add_le _ _
    calc
      ‖A N a - actual‖ ≤ ‖adj‖ + ‖(A N a - actual) - adj‖ := htri
      _ ≤ (Real.sqrt target + T / N) + (B.card : ℝ) / ((N : ℝ) * S) :=
          add_le_add hweighted happ
      _ = Real.sqrt target + K / N := by
          dsimp [K]
          field_simp [hS.ne']
          ring
  have hmain : ∀ ε : ℝ, 0 < ε →
      Filter.limsup
        (fun N : ℕ ↦ ‖A N a - Lℂ (fun m ↦
          A (N / m.1) (fun k ↦ a ⟨m.1 * k.1, Nat.mul_pos m.2 k.2⟩))‖)
        Filter.atTop ≤ Real.sqrt target + ε := by
    intro ε hε
    have hlim : Filter.Tendsto (fun N : ℕ => K / (N : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat K
    have hsmall : ∀ᶠ N : ℕ in Filter.atTop, K / (N : ℝ) < ε :=
      hlim.eventually_lt_const hε
    have hpos : ∀ᶠ N : ℕ in Filter.atTop, 0 < N :=
      (Filter.eventually_ge_atTop 1).mono (fun N hN => hN)
    have hev : ∀ᶠ N : ℕ in Filter.atTop,
        ‖A N a - Lℂ (fun m ↦
          A (N / m.1) (fun k ↦ a ⟨m.1 * k.1, Nat.mul_pos m.2 k.2⟩))‖
          ≤ Real.sqrt target + ε := by
      filter_upwards [hpos, hsmall] with N hN hs
      exact (hboundN N hN).trans (add_le_add le_rfl hs.le)
    exact Filter.limsup_le_of_le
      (Filter.isCoboundedUnder_le_of_eventually_le Filter.atTop
        (Filter.Eventually.of_forall (fun N => norm_nonneg _))) hev
  exact le_of_forall_pos_le_add hmain

end Rollout_p1089_logarithmic_average_bound

namespace Rollout_p0613_chromaticnumber_cartesianpower

/- verified submission -/
lemma cartesianPower_colorable_of_coloring {n k q : ℕ}
    (G : SimpleGraph (Fin n)) (C : G.Coloring (Fin q)) (hq : q ≠ 0) :
    (SimpleGraph.fromRel (fun x y : Fin k → Fin n =>
      ∃ i : Fin k, G.Adj (x i) (y i) ∧
        ∀ j : Fin k, j ≠ i → x j = y j)).Colorable q := by
  letI : NeZero q := ⟨hq⟩
  let H : SimpleGraph (Fin k → Fin n) :=
    SimpleGraph.fromRel (fun x y : Fin k → Fin n =>
      ∃ i : Fin k, G.Adj (x i) (y i) ∧
        ∀ j : Fin k, j ≠ i → x j = y j)
  let color : H.Coloring (Fin q) :=
    { toFun := fun x => ∑ j : Fin k, C (x j)
      map_rel' := by
        intro x y hxy
        rw [SimpleGraph.fromRel_adj] at hxy
        have hrel : ∃ i : Fin k, G.Adj (x i) (y i) ∧
            ∀ j : Fin k, j ≠ i → x j = y j := by
          rcases hxy with ⟨_, hxy | hxy⟩
          · exact hxy
          · rcases hxy with ⟨i, hi, hrest⟩
            exact ⟨i, hi.symm, fun j hj => (hrest j hj).symm⟩
        rcases hrel with ⟨i, hi, hrest⟩
        show (∑ j : Fin k, C (x j)) ≠ ∑ j : Fin k, C (y j)
        intro hsum
        have htail : (∑ j ∈ (Finset.univ : Finset (Fin k)).erase i, C (x j)) =
            ∑ j ∈ (Finset.univ : Finset (Fin k)).erase i, C (y j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hrest j (Finset.mem_erase.mp hj).1]
        rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin k))
              (fun j => C (x j)) (Finset.mem_univ i),
            ← Finset.sum_erase_add (Finset.univ : Finset (Fin k))
              (fun j => C (y j)) (Finset.mem_univ i),
            htail] at hsum
        exact C.valid hi (add_left_cancel hsum) }
  exact ⟨color⟩

lemma cartesianPower_chromaticNumber_lower {n k : ℕ} (hn : 0 < n) (hk : 1 ≤ k)
    (G : SimpleGraph (Fin n)) :
    G.chromaticNumber ≤
      (SimpleGraph.fromRel (fun x y : Fin k → Fin n =>
        ∃ i : Fin k, G.Adj (x i) (y i) ∧
          ∀ j : Fin k, j ≠ i → x j = y j)).chromaticNumber := by
  let p : Fin k := ⟨0, hk⟩
  let a : Fin n := ⟨0, hn⟩
  let H : SimpleGraph (Fin k → Fin n) :=
    SimpleGraph.fromRel (fun x y : Fin k → Fin n =>
      ∃ i : Fin k, G.Adj (x i) (y i) ∧
        ∀ j : Fin k, j ≠ i → x j = y j)
  let emb (v : Fin n) : Fin k → Fin n := fun j => if j = p then v else a
  let embed : G →g H :=
    { toFun := emb
      map_rel' := by
        intro v w hvw
        rw [SimpleGraph.fromRel_adj]
        constructor
        · intro h
          have hp := congrFun h p
          simp [emb] at hp
          exact hvw.ne hp
        · left
          refine ⟨p, ?_, ?_⟩
          · simpa [emb] using hvw
          · intro j hj
            simp [emb, hj] }
  exact SimpleGraph.chromaticNumber_mono_of_hom embed

theorem chromaticNumber_cartesianPower {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) :
    ∀ k : ℕ, 1 ≤ k →
      (SimpleGraph.fromRel (fun x y : Fin k → Fin n =>
        ∃ i : Fin k, G.Adj (x i) (y i) ∧
          ∀ j : Fin k, j ≠ i → x j = y j)).chromaticNumber =
        G.chromaticNumber := by
  intro k hk
  let q : ℕ := G.chromaticNumber.toNat
  have hcG : G.Colorable q := by
    simpa [q] using SimpleGraph.colorable_chromaticNumber_of_fintype G
  have hq : q ≠ 0 := by
    intro hq
    rw [hq] at hcG
    have hempty : IsEmpty (Fin n) := SimpleGraph.isEmpty_of_colorable_zero hcG
    exact IsEmpty.elim hempty ⟨0, hn⟩
  have hcolor : (SimpleGraph.fromRel (fun x y : Fin k → Fin n =>
      ∃ i : Fin k, G.Adj (x i) (y i) ∧
        ∀ j : Fin k, j ≠ i → x j = y j)).Colorable q := by
    rcases hcG with ⟨C⟩
    exact cartesianPower_colorable_of_coloring G C hq
  have htop : G.chromaticNumber ≠ ⊤ := by
    exact SimpleGraph.chromaticNumber_ne_top_iff_exists.mpr ⟨q, hcG⟩
  have upper : (SimpleGraph.fromRel (fun x y : Fin k → Fin n =>
      ∃ i : Fin k, G.Adj (x i) (y i) ∧
        ∀ j : Fin k, j ≠ i → x j = y j)).chromaticNumber ≤ G.chromaticNumber := by
    have hle := hcolor.chromaticNumber_le
    have hqeq : (q : ℕ∞) = G.chromaticNumber := by
      dsimp [q]
      exact ENat.coe_toNat htop
    rw [hqeq] at hle
    exact hle
  exact le_antisymm upper (cartesianPower_chromaticNumber_lower hn hk G)

end Rollout_p0613_chromaticnumber_cartesianpower

namespace Rollout_p1494_p_adic_solenoid_only_periodic_point

/- accepted add_to_file helper 1 -/
lemma solenoid_iterate_apply (k m : ℕ) (z : ℕ → ℂ) (n : ℕ) :
    ((fun w : ℕ → ℂ => fun n => w n ^ k)^[m] z) n = z n ^ k ^ m := by
  induction m generalizing z with
  | zero =>
      simp
  | succ m ih =>
      rw [Function.iterate_succ_apply]
      rw [ih (fun n => z n ^ k)]
      simp [pow_succ, pow_mul, mul_comm]

lemma pow_sub_one_eq_one_of_pow_eq_self
    (a : ℂ) (ha : a ≠ 0) {K : ℕ} (hK : 0 < K) (h : a ^ K = a) :
    a ^ (K - 1) = 1 := by
  have hK' : K = K - 1 + 1 := (Nat.succ_pred_eq_of_pos hK).symm
  have hpow : a ^ (K - 1) * a = a ^ K := by
    rw [← pow_succ, ← hK']
  have hmul : a ^ (K - 1) * a = 1 * a := by
    calc
      a ^ (K - 1) * a = a ^ K := hpow
      _ = a := h
      _ = 1 * a := by rw [one_mul]
  exact mul_right_cancel₀ ha hmul

lemma prime_power_order_forward
    (z : ℕ → ℂ) (P : ℕ → ℕ)
    (hcompat : ∀ n, z n = z (n + 1) ^ P n)
    {p a N j : ℕ} (hle : N ≤ j)
    (hdiv : p ^ a ∣ orderOf (z N)) :
    p ^ a ∣ orderOf (z j) := by
  induction hle with
  | refl => exact hdiv
  | step hle ih =>
      rename_i n
      have hpow_dvd : orderOf (z (n + 1) ^ P n) ∣ orderOf (z (n + 1)) :=
        orderOf_pow_dvd (P n)
      have hord_eq : orderOf (z n) = orderOf (z (n + 1) ^ P n) := by
        rw [hcompat n]
      exact dvd_trans ih (hord_eq.symm ▸ hpow_dvd)

lemma prime_power_order_of_prime_power
    (x : ℂ) {p a : ℕ} (hp : Nat.Prime p) (ha : 0 < a)
    (h : p ^ a ∣ orderOf (x ^ p)) :
    p ^ (a + 1) ∣ orderOf x := by
  have hd : p ^ a ∣ orderOf x := dvd_trans h (orderOf_pow_dvd p)
  have hp_dvd : p ∣ orderOf x :=
    dvd_trans (dvd_pow_self p (Nat.ne_of_gt ha)) hd
  have hgcd : Nat.gcd (orderOf x) p = p := Nat.gcd_eq_right hp_dvd
  have hquot : p ^ a ∣ orderOf x / p := by
    have h' := h
    rw [orderOf_pow' x hp.ne_zero, hgcd] at h'
    exact h'
  obtain ⟨c, hc⟩ := hp_dvd
  have hc_div : p * c / p = c := Nat.mul_div_cancel_left c hp.pos
  have hdivc : p ^ a ∣ c := by
    have h' := hquot
    rw [hc, hc_div] at h'
    exact h'
  obtain ⟨b, hb⟩ := hdivc
  use b
  rw [hc, hb]
  ring

lemma exists_prime_power_order_forward
    (P : ℕ → ℕ)
    (hP_recurrent : ∀ q, Nat.Prime q → ∀ N, ∃ n, N ≤ n ∧ P n = q)
    (z : ℕ → ℂ)
    (hcompat : ∀ n, z n = z (n + 1) ^ P n)
    {p : ℕ} (hp : Nat.Prime p)
    (a N : ℕ) (hdiv : p ∣ orderOf (z N)) :
    ∃ M, p ^ (a + 1) ∣ orderOf (z M) := by
  induction a generalizing N with
  | zero =>
      exact ⟨N, by simpa using hdiv⟩
  | succ a ih =>
      obtain ⟨M, hM⟩ := ih N hdiv
      obtain ⟨j, hMj, hPj⟩ := hP_recurrent p hp M
      have hdivj : p ^ (a + 1) ∣ orderOf (z j) :=
        prime_power_order_forward z P hcompat hMj hM
      have hdivpow : p ^ (a + 1) ∣ orderOf (z (j + 1) ^ p) := by
        rw [hcompat j, hPj] at hdivj
        exact hdivj
      have hnext : p ^ (a + 1 + 1) ∣ orderOf (z (j + 1)) :=
        prime_power_order_of_prime_power (z (j + 1)) hp (Nat.succ_pos a) hdivpow
      exact ⟨j + 1, hnext⟩

/- verified submission -/
theorem p_adic_solenoid_only_periodic_point
    (P : ℕ → ℕ)
    (hP_prime : ∀ n, Nat.Prime (P n))
    (hP_recurrent : ∀ q, Nat.Prime q → ∀ N, ∃ n, N ≤ n ∧ P n = q)
    (k : ℕ) (hk : 2 ≤ k) :
    ∀ z : ℕ → ℂ,
      ((∀ n, ‖z n‖ = 1) ∧
        ∀ n, z n = z (n + 1) ^ P n) →
      ((∃ m, 0 < m ∧
          Function.IsPeriodicPt (fun w : ℕ → ℂ => fun n => w n ^ k) m z) ↔
        z = fun _ => 1) := by
  intro z hz
  obtain ⟨hznorm, hcompat⟩ := hz
  constructor
  · rintro ⟨m, hm, hper⟩
    funext n
    have hKtwo : 2 ≤ k ^ m := by
      calc
        2 ≤ 2 ^ m := Nat.le_self_pow (Nat.ne_of_gt hm) 2
        _ ≤ k ^ m := Nat.pow_le_pow_left hk m
    have hKpos : 0 < k ^ m := by omega
    have ht : 0 < k ^ m - 1 := by omega
    have hfix : (fun w : ℕ → ℂ => fun n => w n ^ k)^[m] z = z := hper
    have hcoord : ∀ n, z n ^ k ^ m = z n := by
      intro n
      have hn := congrFun hfix n
      rwa [solenoid_iterate_apply k m z n] at hn
    have hroot : ∀ n, z n ^ (k ^ m - 1) = 1 := by
      intro n
      have hzne : z n ≠ 0 := by
        intro hz0
        have hnorm := hznorm n
        rw [hz0] at hnorm
        norm_num at hnorm
      exact pow_sub_one_eq_one_of_pow_eq_self (z n) hzne hKpos (hcoord n)
    by_contra hzn
    have hord_ne_one : orderOf (z n) ≠ 1 := by
      intro hord
      exact hzn (orderOf_eq_one_iff.mp hord)
    obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hord_ne_one
    obtain ⟨M, hM⟩ :=
      exists_prime_power_order_forward P hP_recurrent z hcompat hr (k ^ m - 1) n hrdvd
    have hfin : IsOfFinOrder (z M) := by
      exact isOfFinOrder_iff_pow_eq_one.mpr ⟨k ^ m - 1, ht, hroot M⟩
    have hordMpos : 0 < orderOf (z M) := orderOf_pos_iff.mpr hfin
    have hpow_le : r ^ (k ^ m - 1 + 1) ≤ orderOf (z M) :=
      Nat.le_of_dvd hordMpos hM
    have horder_le : orderOf (z M) ≤ k ^ m - 1 :=
      orderOf_le_of_pow_eq_one ht (hroot M)
    have hpow_le_t : r ^ (k ^ m - 1 + 1) ≤ k ^ m - 1 :=
      le_trans hpow_le horder_le
    have hbig : k ^ m - 1 < r ^ (k ^ m - 1 + 1) := by
      exact lt_trans (Nat.lt_succ_self (k ^ m - 1)) (Nat.lt_pow_self hr.two_le)
    exact (not_lt_of_ge hpow_le_t) hbig
  · intro hz1
    refine ⟨1, Nat.one_pos, ?_⟩
    rw [hz1]
    simp [Function.IsPeriodicPt, Function.IsFixedPt]

end Rollout_p1494_p_adic_solenoid_only_periodic_point

namespace Rollout_p2920_proposition_3_8

/- accepted add_to_file helper 1 -/
structure PW where
  val : Polynomial ℤ

def PW.equiv : PW ≃ Polynomial ℤ where
  toFun := PW.val
  invFun := PW.mk
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; rfl

noncomputable instance : CommRing PW := Equiv.commRing PW.equiv

noncomputable def PW.ringEquiv : PW ≃+* Polynomial ℤ := Equiv.ringEquiv PW.equiv

noncomputable def polyToPW : Polynomial ℤ →+* PW := PW.ringEquiv.symm.toRingHom

lemma polyToPW_injective : Function.Injective polyToPW :=
  RingEquiv.injective PW.ringEquiv.symm

noncomputable def weightK : ℕ → ℕ → PW :=
  fun _ j => if j = 1 then polyToPW (-Polynomial.X) else 0

noncomputable def weightE : ℕ → ℕ → PW :=
  fun _ j => if j = 1 then -1 else 0

noncomputable def weightP : ℕ → ℕ → PW :=
  fun _ _ => polyToPW (1 - Polynomial.X)

/- accepted add_to_file helper 2 -/
instance : TopologicalSpace PW := ⊥
instance : DiscreteTopology PW := ⟨rfl⟩

/- accepted add_to_file helper 3 -/
open PowerSeries.WithPiTopology

lemma partition_factor_E (i : ℕ) :
    (1 : PowerSeries PW) +
        ∑' j : ℕ, weightE (i + 1) (j + 1) •
          (PowerSeries.X : PowerSeries PW) ^ ((i + 1) * (j + 1))
      = 1 - (PowerSeries.X : PowerSeries PW) ^ (i + 1) := by
  rw [tsum_eq_single 0]
  · simp [weightE, pow_succ]
    rw [sub_eq_add_neg]
  · intro j hj
    have h : j + 1 ≠ 1 := by omega
    change ((if j + 1 = 1 then (-1 : PW) else 0) •
      (PowerSeries.X : PowerSeries PW) ^ ((i + 1) * (j + 1))) = 0
    rw [if_neg h, zero_smul]

/- accepted add_to_file helper 4 -/
lemma partition_factor_P (i : ℕ) :
    (1 : PowerSeries PW) +
        ∑' j : ℕ, weightP (i + 1) (j + 1) •
          (PowerSeries.X : PowerSeries PW) ^ ((i + 1) * (j + 1))
      =
    1 + polyToPW (1 - Polynomial.X) •
      ((PowerSeries.X : PowerSeries PW) ^ (i + 1) *
        ∑' j : ℕ, ((PowerSeries.X : PowerSeries PW) ^ (i + 1)) ^ j) := by
  let u : PowerSeries PW := PowerSeries.X ^ (i + 1)
  let c : PW := polyToPW (1 - Polynomial.X)
  have hu : PowerSeries.constantCoeff u = 0 := by
    simp [u]
  have hS : Summable fun j : ℕ => u ^ j :=
    PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero hu
  have hshift : ∑' j : ℕ, u * u ^ j = u * ∑' j : ℕ, u ^ j :=
    (hS.hasSum.mul_left u).tsum_eq
  have hscalar : ∑' j : ℕ, (PowerSeries.C c) * (u * u ^ j) =
      (PowerSeries.C c) * (u * ∑' j : ℕ, u ^ j) := by
    have hs : Summable fun j : ℕ => u * u ^ j := hS.mul_left u
    calc
      ∑' j : ℕ, (PowerSeries.C c) * (u * u ^ j)
          = (PowerSeries.C c) * ∑' j : ℕ, u * u ^ j :=
            (hs.hasSum.mul_left (PowerSeries.C c)).tsum_eq
      _ = (PowerSeries.C c) * (u * ∑' j : ℕ, u ^ j) := by rw [hshift]
  have hcongr : (∑' j : ℕ, weightP (i + 1) (j + 1) •
      (PowerSeries.X : PowerSeries PW) ^ ((i + 1) * (j + 1))) =
      ∑' j : ℕ, (PowerSeries.C c) * (u * u ^ j) := by
    apply tsum_congr
    intro j
    have hexp : (i + 1) * (j + 1) = (i + 1) + (i + 1) * j := by
      rw [Nat.mul_succ, Nat.add_comm]
    rw [weightP]
    rw [PowerSeries.smul_eq_C_mul]
    rw [hexp, pow_add, ← pow_mul]
  rw [hcongr, hscalar]
  change 1 + PowerSeries.C c * (u * ∑' j : ℕ, u ^ j) = _
  rw [PowerSeries.smul_eq_C_mul]

/- accepted add_to_file helper 5 -/
lemma partition_factor_K (i : ℕ) :
    (1 : PowerSeries PW) +
        ∑' j : ℕ, weightK (i + 1) (j + 1) •
          (PowerSeries.X : PowerSeries PW) ^ ((i + 1) * (j + 1))
      = 1 - polyToPW Polynomial.X •
          (PowerSeries.X : PowerSeries PW) ^ (i + 1) := by
  rw [tsum_eq_single 0]
  · simp [weightK, pow_succ]
    rw [sub_eq_add_neg]
  · intro j hj
    have h : j + 1 ≠ 1 := by omega
    change ((if j + 1 = 1 then polyToPW (-Polynomial.X) else 0) •
      (PowerSeries.X : PowerSeries PW) ^ ((i + 1) * (j + 1))) = 0
    rw [if_neg h, zero_smul]

/- accepted add_to_file helper 6 -/
lemma partition_factor_mul (i : ℕ) :
    ((1 : PowerSeries PW) +
        ∑' j : ℕ, weightE (i + 1) (j + 1) •
          (PowerSeries.X : PowerSeries PW) ^ ((i + 1) * (j + 1))) *
      ((1 : PowerSeries PW) +
        ∑' j : ℕ, weightP (i + 1) (j + 1) •
          (PowerSeries.X : PowerSeries PW) ^ ((i + 1) * (j + 1)))
    =
    (1 : PowerSeries PW) +
        ∑' j : ℕ, weightK (i + 1) (j + 1) •
          (PowerSeries.X : PowerSeries PW) ^ ((i + 1) * (j + 1)) := by
  rw [partition_factor_E, partition_factor_P, partition_factor_K]
  let u : PowerSeries PW := PowerSeries.X ^ (i + 1)
  let a : PowerSeries PW := PowerSeries.C (polyToPW Polynomial.X)
  let S : PowerSeries PW := ∑' j : ℕ, u ^ j
  have hu : PowerSeries.constantCoeff u = 0 := by simp [u]
  have hgeom : (1 - u) * S = 1 :=
    PowerSeries.WithPiTopology.one_sub_mul_tsum_pow_of_constantCoeff_eq_zero hu
  change (1 - u) * (1 + polyToPW (1 - Polynomial.X) • (u * S)) =
    1 - polyToPW Polynomial.X • u
  rw [PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul]
  have hc : PowerSeries.C (polyToPW (1 - Polynomial.X)) = 1 - a := by
    simp [a]
  rw [hc]
  change (1 - u) * (1 + (1 - a) * (u * S)) = 1 - a * u
  calc
    (1 - u) * (1 + (1 - a) * (u * S))
        = (1 - u) + (1 - a) * (u * ((1 - u) * S)) := by ring
    _ = (1 - u) + (1 - a) * u := by rw [hgeom]; ring
    _ = 1 - a * u := by ring

/- accepted add_to_file helper 7 -/
lemma genFun_weightK_eq :
    Nat.Partition.genFun weightK =
      Nat.Partition.genFun weightE * Nat.Partition.genFun weightP := by
  apply HasProd.unique (Nat.Partition.hasProd_genFun (R := PW) weightK)
  convert (Nat.Partition.hasProd_genFun (R := PW) weightE).mul
    (Nat.Partition.hasProd_genFun (R := PW) weightP) using 1
  funext i
  exact (partition_factor_mul i).symm

/- accepted add_to_file helper 8 -/
lemma toFinsupp_prod_weightK {m : ℕ} (ρ : Nat.Partition m) :
    (Multiset.toFinsupp ρ.parts).prod weightK =
      if ρ.parts.Nodup then
        polyToPW ((-Polynomial.X : Polynomial ℤ) ^ ρ.parts.toFinset.card)
      else 0 := by
  by_cases h : ρ.parts.Nodup
  · simp [h]
    rw [Finsupp.prod, Multiset.toFinsupp_support]
    rw [← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro a ha
    have hmem : a ∈ ρ.parts := by
      exact Multiset.mem_toFinset.mp ha
    have hcount : Multiset.count a ρ.parts = 1 :=
      Multiset.count_eq_one_of_mem h hmem
    simp [weightK, Multiset.toFinsupp_apply, hcount]
  · simp [h]
    rw [Finsupp.prod, Multiset.toFinsupp_support]
    rw [Multiset.nodup_iff_count_le_one] at h
    push_neg at h
    rcases h with ⟨a, ha⟩
    have hapos : a ∈ ρ.parts.toFinset := by
      rw [Multiset.mem_toFinset]
      by_contra hnot
      have hcount0 : Multiset.count a ρ.parts = 0 :=
        Multiset.count_eq_zero_of_notMem hnot
      omega
    have hcountne : Multiset.count a ρ.parts ≠ 1 := by omega
    apply Finset.prod_eq_zero hapos
    simp [weightK, Multiset.toFinsupp_apply, hcountne]

/- accepted add_to_file helper 9 -/
noncomputable def kappaPoly (m : ℕ) (ρ : Nat.Partition m) : Polynomial ℤ :=
  if ρ.parts.Nodup then (-Polynomial.X : Polynomial ℤ) ^ ρ.parts.toFinset.card else 0

lemma toFinsupp_prod_weightP {m : ℕ} (ρ : Nat.Partition m) :
    (Multiset.toFinsupp ρ.parts).prod weightP =
      polyToPW ((1 - Polynomial.X : Polynomial ℤ) ^ ρ.parts.toFinset.card) := by
  rw [Finsupp.prod, Multiset.toFinsupp_support]
  rw [← Finset.prod_const]
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro a ha
  simp [weightP]

/- accepted add_to_file helper 10 -/
lemma toFinsupp_prod_weightE {m : ℕ} (ρ : Nat.Partition m) :
    (Multiset.toFinsupp ρ.parts).prod weightE =
      polyToPW (Polynomial.C (Polynomial.eval 1 (kappaPoly m ρ))) := by
  by_cases h : ρ.parts.Nodup
  · simp [h, kappaPoly]
    rw [Finsupp.prod, Multiset.toFinsupp_support]
    rw [← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro a ha
    have hmem : a ∈ ρ.parts := Multiset.mem_toFinset.mp ha
    have hcount : Multiset.count a ρ.parts = 1 :=
      Multiset.count_eq_one_of_mem h hmem
    simp [weightE, Multiset.toFinsupp_apply, hcount]
  · simp [h, kappaPoly]
    rw [Finsupp.prod, Multiset.toFinsupp_support]
    rw [Multiset.nodup_iff_count_le_one] at h
    push_neg at h
    rcases h with ⟨a, ha⟩
    have hapos : a ∈ ρ.parts.toFinset := by
      rw [Multiset.mem_toFinset]
      by_contra hnot
      have hcount0 : Multiset.count a ρ.parts = 0 :=
        Multiset.count_eq_zero_of_notMem hnot
      omega
    have hcountne : Multiset.count a ρ.parts ≠ 1 := by omega
    apply Finset.prod_eq_zero hapos
    simp [weightE, Multiset.toFinsupp_apply, hcountne]

/- accepted add_to_file helper 11 -/
lemma coeff_genFun_weightK (k : ℕ) :
    (PowerSeries.coeff k) (Nat.Partition.genFun weightK) =
      polyToPW (∑ ρ : Nat.Partition k, kappaPoly k ρ) := by
  simp [Nat.Partition.genFun, kappaPoly, toFinsupp_prod_weightK]
  apply Finset.sum_congr rfl
  intro ρ hρ
  by_cases h : ρ.parts.Nodup <;> simp [h]

lemma coeff_genFun_weightP (k : ℕ) :
    (PowerSeries.coeff k) (Nat.Partition.genFun weightP) =
      polyToPW (∑ ρ : Nat.Partition k,
        (1 - Polynomial.X : Polynomial ℤ) ^ ρ.parts.toFinset.card) := by
  simp [Nat.Partition.genFun, toFinsupp_prod_weightP]

lemma coeff_genFun_weightE (k : ℕ) :
    (PowerSeries.coeff k) (Nat.Partition.genFun weightE) =
      polyToPW (Polynomial.C (∑ ρ : Nat.Partition k,
        Polynomial.eval 1 (kappaPoly k ρ))) := by
  simp [Nat.Partition.genFun, toFinsupp_prod_weightE]

/- accepted add_to_file helper 12 -/
noncomputable def localK (k : ℕ) : Polynomial ℤ :=
  ∑ ρ : Nat.Partition k, kappaPoly k ρ

noncomputable def localP (k : ℕ) : Polynomial ℤ :=
  ∑ ρ : Nat.Partition k,
    (1 - Polynomial.X : Polynomial ℤ) ^ ρ.parts.toFinset.card

noncomputable def localE (k : ℕ) : ℤ :=
  ∑ ρ : Nat.Partition k, Polynomial.eval 1 (kappaPoly k ρ)

/- accepted add_to_file helper 13 -/
lemma local_identity (k : ℕ) :
    localK k =
      ∑ r ∈ Finset.range (k + 1),
        Polynomial.C (localE r) * localP (k - r) := by
  apply polyToPW_injective
  have hcoeff := congrArg (PowerSeries.coeff k) genFun_weightK_eq
  rw [coeff_genFun_weightK] at hcoeff
  rw [PowerSeries.coeff_mul] at hcoeff
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => (PowerSeries.coeff a) (Nat.Partition.genFun weightE) *
      (PowerSeries.coeff b) (Nat.Partition.genFun weightP)) k] at hcoeff
  simp_rw [coeff_genFun_weightE, coeff_genFun_weightP] at hcoeff
  simp only [localK]
  calc
    polyToPW (∑ ρ : Nat.Partition k, kappaPoly k ρ)
        = ∑ r ∈ Finset.range (k + 1),
          polyToPW (Polynomial.C (localE r)) * polyToPW (localP (k - r)) := by
          simpa [localE, localP] using hcoeff
    _ = polyToPW (∑ r ∈ Finset.range (k + 1),
          Polynomial.C (localE r) * localP (k - r)) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro r hr
          simp

/- accepted add_to_file helper 14 -/
lemma bounded_sum_eq_antidiagonalTuple {M : Type*} [AddCommMonoid M]
    (n a : ℕ) (F : (Fin n → ℕ) → M) :
    (∑ s : Fin n → Fin (a + 1),
      if h : (∑ i, (s i : ℕ)) = a then F (fun i => (s i : ℕ)) else 0)
    =
    ∑ t ∈ Finset.Nat.antidiagonalTuple n a, F t := by
  rw [Finset.sum_dite]
  simp
  apply Finset.sum_bij
    (i := fun s _ => fun i => (s.1 i : ℕ))
  · intro s hs
    rw [Finset.Nat.mem_antidiagonalTuple]
    exact (Finset.mem_filter.mp s.2).2
  · intro s hs t ht hst
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact congrFun hst i
  · intro t ht
    rw [Finset.Nat.mem_antidiagonalTuple] at ht
    have hle : ∀ i : Fin n, t i ≤ a := by
      intro i
      rw [← ht]
      exact Finset.single_le_sum (fun j _ => Nat.zero_le (t j)) (Finset.mem_univ i)
    refine ⟨⟨fun i => ⟨t i, Nat.lt_succ_of_le (hle i)⟩, ?_⟩, Finset.mem_attach _ _, ?_⟩
    · simpa using ht
    · rfl
  · intro s hs
    rfl

/- accepted add_to_file helper 15 -/
lemma finsuppAntidiag_range_sum_eq_antidiagonalTuple {M : Type*} [CommSemiring M]
    (n a : ℕ) (F : ℕ → M) :
    (∑ l ∈ (Finset.range n).finsuppAntidiag a,
      ∏ i ∈ Finset.range n, F (l i))
    =
    ∑ t ∈ Finset.Nat.antidiagonalTuple n a, ∏ i, F (t i) := by
  apply Finset.sum_bij
    (i := fun l _ => fun i : Fin n => l i)
  · intro l hl
    rw [Finset.Nat.mem_antidiagonalTuple]
    have hlm := (Finset.mem_finsuppAntidiag.mp hl).1
    rw [Fin.sum_univ_eq_sum_range (f := fun i : ℕ => l i) n]
    exact hlm
  · intro l₁ hl₁ l₂ hl₂ h
    apply Finsupp.ext
    intro m
    by_cases hm : m < n
    · exact congrFun h ⟨m, hm⟩
    · have hm1 : m ∉ l₁.support := by
        intro hmem
        exact hm (Finset.mem_range.mp ((Finset.mem_finsuppAntidiag.mp hl₁).2 hmem))
      have hm2 : m ∉ l₂.support := by
        intro hmem
        exact hm (Finset.mem_range.mp ((Finset.mem_finsuppAntidiag.mp hl₂).2 hmem))
      have hz1 : l₁ m = 0 := by
        by_contra hz
        exact hm1 ((Finsupp.mem_support_iff).2 hz)
      have hz2 : l₂ m = 0 := by
        by_contra hz
        exact hm2 ((Finsupp.mem_support_iff).2 hz)
      rw [hz1, hz2]
  · intro t ht
    let l : ℕ →₀ ℕ := Finsupp.onFinset (Finset.range n)
      (fun m => if hm : m < n then t ⟨m, hm⟩ else 0) (by
        intro m hm
        rw [Finset.mem_range]
        by_contra hmn
        simp [hmn] at hm)
    refine ⟨l, ?_, ?_⟩
    · rw [Finset.mem_finsuppAntidiag]
      constructor
      · rw [Finset.Nat.mem_antidiagonalTuple] at ht
        calc
          (Finset.range n).sum (⇑l)
              = ∑ m ∈ Finset.range n,
                  (if hm : m < n then t ⟨m, hm⟩ else 0) := by
                  apply Finset.sum_congr rfl
                  intro m hm
                  simp [l]
          _ = ∑ i : Fin n, t i :=
                (Finset.sum_fin_eq_sum_range (fun i : Fin n => t i)).symm
          _ = a := ht
      · exact Finsupp.support_onFinset_subset
    · funext i
      simp [l, i.2]
  · intro l hl
    rw [Fin.prod_univ_eq_prod_range (f := fun i : ℕ => F (l i)) n]

/- accepted add_to_file helper 16 -/
noncomputable def convPoly (F : ℕ → Polynomial ℤ) (n a : ℕ) : Polynomial ℤ :=
  ∑ s : Fin n → Fin (a + 1),
    if h : (∑ i, (s i : ℕ)) = a then
      ∏ i, F (s i : ℕ)
    else 0

noncomputable def convInt (E : ℕ → ℤ) (n a : ℕ) : ℤ :=
  ∑ s : Fin n → Fin (a + 1),
    if h : (∑ i, (s i : ℕ)) = a then
      ∏ i, E (s i : ℕ)
    else 0

/- accepted add_to_file helper 17 -/
lemma coeff_mk_pow (F : ℕ → Polynomial ℤ) (n a : ℕ) :
    (PowerSeries.coeff a)
      ((PowerSeries.mk F : PowerSeries (Polynomial ℤ)) ^ n)
      = convPoly F n a := by
  rw [PowerSeries.coeff_pow]
  simp_rw [PowerSeries.coeff_mk]
  rw [finsuppAntidiag_range_sum_eq_antidiagonalTuple]
  rw [← bounded_sum_eq_antidiagonalTuple n a
    (F := fun t => ∏ i : Fin n, F (t i))]
  rfl

lemma coeff_mkC_pow (E : ℕ → ℤ) (n a : ℕ) :
    (PowerSeries.coeff a)
      ((PowerSeries.mk (fun a => Polynomial.C (E a)) : PowerSeries (Polynomial ℤ)) ^ n)
      = Polynomial.C (convInt E n a) := by
  rw [PowerSeries.coeff_pow]
  simp_rw [PowerSeries.coeff_mk]
  rw [finsuppAntidiag_range_sum_eq_antidiagonalTuple n a
    (F := fun m => Polynomial.C (E m))]
  rw [← bounded_sum_eq_antidiagonalTuple n a
    (F := fun t => ∏ i : Fin n, Polynomial.C (E (t i)))]
  simp [convInt]

/- accepted add_to_file helper 18 -/
lemma series_local_identity :
    (PowerSeries.mk localK : PowerSeries (Polynomial ℤ)) =
      (PowerSeries.mk (fun a => Polynomial.C (localE a)) : PowerSeries (Polynomial ℤ)) *
        (PowerSeries.mk localP : PowerSeries (Polynomial ℤ)) := by
  apply PowerSeries.ext
  intro a
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun r b => (PowerSeries.coeff r)
      (PowerSeries.mk (fun a => Polynomial.C (localE a)) : PowerSeries (Polynomial ℤ)) *
      (PowerSeries.coeff b) (PowerSeries.mk localP : PowerSeries (Polynomial ℤ))) a]
  simp_rw [PowerSeries.coeff_mk]
  exact local_identity a

/- accepted add_to_file helper 19 -/
lemma conv_identity (n k : ℕ) :
    convPoly localK n k =
      ∑ r ∈ Finset.range (k + 1),
        Polynomial.C (convInt localE n r) * convPoly localP n (k - r) := by
  have h := congrArg (fun A : PowerSeries (Polynomial ℤ) => A ^ n) series_local_identity
  have hc := congrArg (PowerSeries.coeff k) h
  rw [coeff_mk_pow] at hc
  change convPoly localK n k =
    (PowerSeries.coeff k)
      (((PowerSeries.mk (fun a => Polynomial.C (localE a)) : PowerSeries (Polynomial ℤ)) *
        (PowerSeries.mk localP : PowerSeries (Polynomial ℤ))) ^ n) at hc
  rw [mul_pow] at hc
  rw [PowerSeries.coeff_mul] at hc
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun r b => (PowerSeries.coeff r)
      ((PowerSeries.mk (fun a => Polynomial.C (localE a)) : PowerSeries (Polynomial ℤ)) ^ n) *
      (PowerSeries.coeff b)
      ((PowerSeries.mk localP : PowerSeries (Polynomial ℤ)) ^ n)) k] at hc
  simp_rw [coeff_mkC_pow, coeff_mk_pow] at hc
  exact hc

/- accepted add_to_file helper 20 -/
lemma epsilon_eq_conv (n a : ℕ) :
    (∑ s : Fin n → Fin (a + 1),
      if h : (∑ i, (s i : ℕ)) = a then
        ∑ p : (i : Fin n) → Nat.Partition (s i : ℕ),
          ∏ i, kappaPoly (s i : ℕ) (p i)
      else 0)
    = convPoly localK n a := by
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h : (∑ i, (s i : ℕ)) = a
  · simp [h, localK]
    rw [Finset.prod_univ_sum]
    rw [Fintype.piFinset_univ]
  · simp [h]

lemma pp_eq_conv (n a : ℕ) :
    (∑ s : Fin n → Fin (a + 1),
      if h : (∑ i, (s i : ℕ)) = a then
        ∑ ρ : (i : Fin n) → Nat.Partition (s i : ℕ),
          (1 - Polynomial.X : Polynomial ℤ) ^
            (∑ i, (ρ i).parts.toFinset.card)
      else 0)
    = convPoly localP n a := by
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h : (∑ i, (s i : ℕ)) = a
  · simp [h, localP]
    rw [Finset.prod_univ_sum]
    rw [Fintype.piFinset_univ]
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [Finset.prod_pow_eq_pow_sum]
  · simp [h]

/- accepted add_to_file helper 21 -/
lemma eval_localK (a : ℕ) :
    Polynomial.eval 1 (localK a) = localE a := by
  change (Polynomial.evalRingHom 1) (∑ ρ : Nat.Partition a, kappaPoly a ρ) = localE a
  rw [map_sum]
  rfl

lemma eval_conv_localK (n a : ℕ) :
    Polynomial.eval 1 (convPoly localK n a) = convInt localE n a := by
  change (Polynomial.evalRingHom 1) (convPoly localK n a) = convInt localE n a
  rw [convPoly]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h : (∑ i, (s i : ℕ)) = a
  · simp [h]
    apply Finset.prod_congr rfl
    intro i hi
    exact eval_localK (s i : ℕ)
  · simp [h]

/- verified submission -/
theorem proposition_3_8 (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    let κ : (m : ℕ) → Nat.Partition m → Polynomial ℤ := fun _ ρ =>
      if ρ.parts.Nodup then
        (-Polynomial.X : Polynomial ℤ) ^ ρ.parts.toFinset.card
      else 0
    let ε : ℕ → Polynomial ℤ := fun a =>
      ∑ s : Fin n → Fin (a + 1),
        if h : (∑ i, (s i : ℕ)) = a then
          ∑ p : (i : Fin n) → Nat.Partition (s i : ℕ),
            ∏ i, κ (s i : ℕ) (p i)
        else 0
    let pp : ℕ → Polynomial ℤ := fun a =>
      ∑ s : Fin n → Fin (a + 1),
        if h : (∑ i, (s i : ℕ)) = a then
          ∑ ρ : (i : Fin n) → Nat.Partition (s i : ℕ),
            (1 - Polynomial.X : Polynomial ℤ) ^
              (∑ i, (ρ i).parts.toFinset.card)
        else 0
    let ε₁ : ℕ → ℤ := fun a => Polynomial.eval 1 (ε a)
    ε k = ∑ r ∈ Finset.range (k + 1), Polynomial.C (ε₁ r) * pp (k - r) := by
  dsimp only
  have heval : ∀ r : ℕ,
      Polynomial.eval 1
          (∑ s : Fin n → Fin (r + 1),
            if h : (∑ i, (s i : ℕ)) = r then
              ∑ p : (i : Fin n) → Nat.Partition (s i : ℕ),
                ∏ i, if (p i).parts.Nodup then
                  (-Polynomial.X : Polynomial ℤ) ^ (p i).parts.toFinset.card
                else 0
            else 0)
        = convInt localE n r := by
    intro r
    change Polynomial.eval 1
        (∑ s : Fin n → Fin (r + 1),
          if h : (∑ i, (s i : ℕ)) = r then
            ∑ p : (i : Fin n) → Nat.Partition (s i : ℕ),
              ∏ i, kappaPoly (s i : ℕ) (p i)
          else 0)
      = convInt localE n r
    rw [epsilon_eq_conv]
    exact eval_conv_localK n r
  change (∑ s : Fin n → Fin (k + 1),
      if h : (∑ i, (s i : ℕ)) = k then
        ∑ p : (i : Fin n) → Nat.Partition (s i : ℕ),
          ∏ i, kappaPoly (s i : ℕ) (p i)
      else 0)
    =
    ∑ r ∈ Finset.range (k + 1),
      Polynomial.C
          (Polynomial.eval 1
            (∑ s : Fin n → Fin (r + 1),
              if h : (∑ i, (s i : ℕ)) = r then
                ∑ p : (i : Fin n) → Nat.Partition (s i : ℕ),
                  ∏ i, kappaPoly (s i : ℕ) (p i)
              else 0)) *
        ∑ s : Fin n → Fin ((k - r) + 1),
          if h : (∑ i, (s i : ℕ)) = k - r then
            ∑ ρ : (i : Fin n) → Nat.Partition (s i : ℕ),
              (1 - Polynomial.X : Polynomial ℤ) ^
                (∑ i, (ρ i).parts.toFinset.card)
          else 0
  rw [epsilon_eq_conv]
  rw [conv_identity]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← heval r]
  congr 1
  exact (pp_eq_conv n (k - r)).symm

end Rollout_p2920_proposition_3_8

namespace Rollout_p1151_strict_convex_modular_fixed_point

/- accepted add_to_file helper 1 -/
lemma modular_scale_le
    {X : Type*} (w : NNReal → X → X → ENNReal)
    (hself : ∀ (l : NNReal), 0 < l → ∀ x : X, w l x x = 0)
    (hconv : ∀ (l m : NNReal), 0 < l → 0 < m → ∀ x y z : X,
      w (l + m) x y ≤ ((l : ENNReal) / (l + m)) * w l x z +
        ((m : ENNReal) / (l + m)) * w m y z)
    {l s : NNReal} (hl : 0 < l) (hls : l ≤ s) (x y : X) :
    w s x y ≤ ((l : ENNReal) / (s : ENNReal)) * w l x y := by
  rcases eq_or_lt_of_le hls with rfl | hlt
  · have h0 : (l : ENNReal) ≠ 0 := by exact_mod_cast ne_of_gt hl
    have htop : (l : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    simp [ENNReal.div_self h0 htop]
  · let d : NNReal := s - l
    have hd : 0 < d := tsub_pos_of_lt hlt
    have hsd : l + d = s := add_tsub_cancel_of_le hls
    have h := hconv l d hl hd x y y
    rw [hsd, hself d hd y, mul_zero, add_zero] at h
    rw [← ENNReal.coe_add, hsd] at h
    exact h

lemma ennreal_add_coe_mul_div_sub_self {d : ENNReal} {k : NNReal}
    (hk : (k : ENNReal) < 1) :
    d + (k : ENNReal) * (d / (1 - (k : ENNReal))) =
      d / (1 - (k : ENNReal)) := by
  let e : ENNReal := 1 - (k : ENNReal)
  have he0 : e ≠ 0 := by
    dsimp [e]
    exact ne_of_gt (tsub_pos_of_lt hk)
  have het : e ≠ ⊤ := by
    dsimp [e]
    exact ENNReal.sub_ne_top (by simp)
  have hek : e + (k : ENNReal) = 1 := by
    dsimp [e]
    exact tsub_add_cancel_of_le hk.le
  have hinv : e * e⁻¹ = 1 := ENNReal.mul_inv_cancel he0 het
  calc
    d + (k : ENNReal) * (d / e)
        = d * 1 + (k : ENNReal) * (d * e⁻¹) := by rw [div_eq_mul_inv, mul_one]
    _ = d * (e * e⁻¹) + (k : ENNReal) * (d * e⁻¹) := by rw [hinv]
    _ = e * (d * e⁻¹) + (k : ENNReal) * (d * e⁻¹) := by
          congr 1
          calc
            d * (e * e⁻¹) = (d * e) * e⁻¹ := by rw [mul_assoc]
            _ = (e * d) * e⁻¹ := by rw [mul_comm d e]
            _ = e * (d * e⁻¹) := by rw [mul_assoc]
    _ = (e + (k : ENNReal)) * (d * e⁻¹) := by rw [add_mul]
    _ = d / e := by rw [hek, one_mul, div_eq_mul_inv]

/- accepted add_to_file helper 2 -/
lemma tendsto_ennreal_const_mul_pow_min_zero {C : ENNReal} (hC : C ≠ ⊤)
    {k : NNReal} (hk : k < 1) :
    Filter.Tendsto (fun p : ℕ × ℕ => C * (k : ENNReal) ^ min p.1 p.2)
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
  have hmin : Filter.Tendsto (fun p : ℕ × ℕ => min p.1 p.2)
      (Filter.atTop ×ˢ Filter.atTop) Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro N
    filter_upwards [Filter.tendsto_fst.eventually_ge_atTop N,
      Filter.tendsto_snd.eventually_ge_atTop N] with p hp1 hp2
    exact le_min hp1 hp2
  have hpow : Filter.Tendsto (fun n : ℕ => (k : ℝ) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (NNReal.coe_nonneg k) (by exact_mod_cast hk)
  have hreal : Filter.Tendsto
      (fun p : ℕ × ℕ => C.toReal * (k : ℝ) ^ min p.1 p.2)
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
    simpa using Filter.Tendsto.const_mul C.toReal (hpow.comp hmin)
  have hreal' : Filter.Tendsto
      (fun p : ℕ × ℕ => (C * (k : ENNReal) ^ min p.1 p.2).toReal)
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
    convert hreal using 1
    ext p
    simp [ENNReal.toReal_mul, ← ENNReal.coe_pow]
  exact (ENNReal.tendsto_toReal_zero_iff (fun p => by
    exact ENNReal.mul_ne_top hC (by
      rw [← ENNReal.coe_pow]
      exact ENNReal.coe_ne_top))).1 hreal'

/- accepted add_to_file helper 3 -/
lemma modular_fixed_point_of_displacement
    {X : Type*} (b : X) (w : NNReal → X → X → ENNReal)
    (hself : ∀ (l : NNReal), 0 < l → ∀ x : X, w l x x = 0)
    (hsymm : ∀ (l : NNReal), 0 < l → ∀ x y : X, w l x y = w l y x)
    (hstrict : ∀ x y : X, (∃ l : NNReal, 0 < l ∧ w l x y = 0) → x = y)
    (hconv : ∀ (l m : NNReal), 0 < l → 0 < m → ∀ x y z : X,
      w (l + m) x y ≤ ((l : ENNReal) / (l + m)) * w l x z +
        ((m : ENNReal) / (l + m)) * w m y z)
    (hcomplete : ∀ (x : ℕ → {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤})
      (l : NNReal), 0 < l →
      Filter.Tendsto (fun p : ℕ × ℕ => w l (x p.1) (x p.2))
        (Filter.atTop ×ˢ Filter.atTop) (nhds 0) →
      ∃ y : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
        Filter.Tendsto (fun n => w l (x n) y) Filter.atTop (nhds 0))
    (T : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤} →
      {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤})
    {k L : NNReal} (hk0 : 0 < k) (hk1 : k < 1) (hL0 : 0 < L)
    (hcontr : ∀ x y : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
      ∀ l : NNReal, 0 < l → l ≤ L → w (k * l) (T x) (T y) ≤ w l x y)
    (x0 : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤})
    (hdisp : w ((1 - (1 + k) / 2) * L) x0 (T x0) < ⊤) :
    ∃ y : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
      T y = y ∧
      Filter.Tendsto (fun n : ℕ => w L ((T^[n]) x0) y)
        Filter.atTop (nhds 0) := by
  let q : NNReal := (1 + k) / 2
  let r : NNReal := k / q
  let a : NNReal := (1 - q) * L
  let lam : ℕ → NNReal := fun n => a * q ^ n
  let S : ℕ → NNReal := fun n => L * q ^ n
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hkq : k < q := by dsimp [q]; nlinarith [hk0, hk1]
  have hq1 : q < 1 := by dsimp [q]; nlinarith [hk1]
  have hr1 : r < 1 := by dsimp [r]; rw [div_lt_one hq0]; exact hkq
  have hqr : q * r = k := by
    dsimp [r]; rw [mul_comm]; exact div_mul_cancel₀ k (ne_of_gt hq0)
  have ha0 : 0 < a := by dsimp [a]; exact mul_pos (tsub_pos_of_lt hq1) hL0
  have hlam0 : ∀ n, 0 < lam n := by intro n; dsimp [lam]; exact mul_pos ha0 (pow_pos hq0 n)
  have hlam_le : ∀ n, lam n ≤ L := by
    intro n
    have h1 : 1 - q ≤ (1 : NNReal) := tsub_le_self
    have h2 : q ^ n ≤ (1 : NNReal) := pow_le_one₀ hq0.le hq1.le
    dsimp [lam, a]
    calc
      (1 - q) * L * q ^ n ≤ (1 - q) * L * 1 := mul_le_mul_left' h2 ((1 - q) * L)
      _ ≤ (1 : NNReal) * L * 1 := mul_le_mul_right' (mul_le_mul_right' h1 L) 1
      _ = L := by ring
  have hS0 : ∀ n, 0 < S n := by intro n; dsimp [S]; exact mul_pos hL0 (pow_pos hq0 n)
  have hS_le : ∀ n, S n ≤ L := by
    intro n
    dsimp [S]
    calc
      L * q ^ n ≤ L * 1 := mul_le_mul_left' (pow_le_one₀ hq0.le hq1.le) L
      _ = L := mul_one L
  have hS_add : ∀ n, lam n + S (n + 1) = S n := by
    intro n
    dsimp [lam, S, a]
    calc
      (1 - q) * L * q ^ n + L * q ^ (n + 1)
          = ((1 - q) + q) * L * q ^ n := by rw [pow_succ]; ring
      _ = L * q ^ n := by rw [tsub_add_cancel_of_le hq1.le]; ring
  let d0 : ENNReal := w a x0 (T x0)
  have hd0 : d0 ≠ ⊤ := ne_of_lt hdisp
  have hgeom : ∀ n : ℕ,
      w (lam n) ((T^[n]) x0) ((T^[n + 1]) x0) ≤ d0 * (r : ENNReal) ^ n := by
    intro n
    induction n with
    | zero => simp [lam, a, d0]
    | succ n ih =>
        have hscale : w (lam (n + 1)) ((T^[n + 1]) x0) ((T^[n + 2]) x0) ≤
            (((k * lam n : NNReal) : ENNReal) / (lam (n + 1) : ENNReal)) *
              w (k * lam n) ((T^[n + 1]) x0) ((T^[n + 2]) x0) := by
          apply modular_scale_le w hself hconv
          · exact mul_pos hk0 (hlam0 n)
          · dsimp [lam]
            calc
              k * (a * q ^ n) ≤ q * (a * q ^ n) := by gcongr
              _ = a * q ^ (n + 1) := by rw [pow_succ]; ring
        have hcoeff : (((k * lam n : NNReal) : ENNReal) / (lam (n + 1) : ENNReal)) =
            (r : ENNReal) := by
          have hnext : (lam (n + 1) : ENNReal) = (q : ENNReal) * (lam n : ENNReal) := by
            dsimp [lam]; rw [pow_succ]; ring
          have hk_eq : (k : ENNReal) = (q : ENNReal) * (r : ENNReal) := by
            rw [← ENNReal.coe_mul, hqr]
          have hden : (q : ENNReal) * (lam n : ENNReal) ≠ 0 := by
            exact mul_ne_zero (by exact_mod_cast ne_of_gt hq0)
              (by exact_mod_cast ne_of_gt (hlam0 n))
          have hdenTop : (q : ENNReal) * (lam n : ENNReal) ≠ ⊤ :=
            ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
          calc
            (((k * lam n : NNReal) : ENNReal) / (lam (n + 1) : ENNReal))
                = ((k : ENNReal) * (lam n : ENNReal)) / ((q : ENNReal) * (lam n : ENNReal)) := by
                    rw [ENNReal.coe_mul, hnext]
            _ = (((q : ENNReal) * (r : ENNReal)) * (lam n : ENNReal)) /
                    ((q : ENNReal) * (lam n : ENNReal)) := by rw [hk_eq]
            _ = (r : ENNReal) := by
                    calc
                      (((q : ENNReal) * (r : ENNReal)) * (lam n : ENNReal)) /
                          ((q : ENNReal) * (lam n : ENNReal))
                          = (r : ENNReal) * ((q : ENNReal) * (lam n : ENNReal)) /
                              ((q : ENNReal) * (lam n : ENNReal)) := by ring
                      _ = (r : ENNReal) * 1 := by
                            rw [mul_div_assoc, ENNReal.div_self hden hdenTop]
                      _ = (r : ENNReal) := mul_one _
        have hctr0 := hcontr ((T^[n]) x0) ((T^[n + 1]) x0) (lam n) (hlam0 n) (hlam_le n)
        have hctr : w (k * lam n) ((T^[n + 1]) x0) ((T^[n + 2]) x0) ≤
            w (lam n) ((T^[n]) x0) ((T^[n + 1]) x0) := by
          simpa [Function.iterate_succ_apply'] using hctr0
        calc
          w (lam (n + 1)) ((T^[n + 1]) x0) ((T^[n + 2]) x0)
              ≤ (r : ENNReal) * w (k * lam n) ((T^[n + 1]) x0) ((T^[n + 2]) x0) := by
                  rw [← hcoeff]; exact hscale
          _ ≤ (r : ENNReal) * w (lam n) ((T^[n]) x0) ((T^[n + 1]) x0) :=
                  mul_le_mul_left' hctr _
          _ ≤ (r : ENNReal) * (d0 * (r : ENNReal) ^ n) := mul_le_mul_left' ih _
          _ = d0 * (r : ENNReal) ^ (n + 1) := by rw [pow_succ]; ring
  let C : ENNReal := d0 / (1 - (k : ENNReal))
  have hCeq : d0 + (k : ENNReal) * C = C := by
    dsimp [C]
    exact ennreal_add_coe_mul_div_sub_self (by exact_mod_cast hk1)
  have hCne : C ≠ ⊤ := by
    dsimp [C]
    apply ENNReal.div_ne_top hd0
    exact ne_of_gt (tsub_pos_of_lt (by exact_mod_cast hk1 : (k : ENNReal) < 1))
  have hlam_le_S : ∀ n, lam n ≤ S n := by
    intro n
    have haL : a ≤ L := by
      dsimp [a]
      calc
        (1 - q) * L ≤ 1 * L := mul_le_mul_right' tsub_le_self L
        _ = L := one_mul L
    dsimp [lam, S]
    exact mul_le_mul_right' haL (q ^ n)
  have hSratio : ∀ n, ((S (n + 1) : ENNReal) / (S n : ENNReal)) = (q : ENNReal) := by
    intro n
    have hnext : (S (n + 1) : ENNReal) = (q : ENNReal) * (S n : ENNReal) := by
      dsimp [S]; rw [pow_succ]; ring
    have hden : (S n : ENNReal) ≠ 0 := by exact_mod_cast ne_of_gt (hS0 n)
    have hdenTop : (S n : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    calc
      ((S (n + 1) : ENNReal) / (S n : ENNReal))
          = ((q : ENNReal) * (S n : ENNReal)) / (S n : ENNReal) := by rw [hnext]
      _ = (q : ENNReal) * ((S n : ENNReal) / (S n : ENNReal)) := by rw [mul_div_assoc]
      _ = (q : ENNReal) := by rw [ENNReal.div_self hden hdenTop, mul_one]
  have hpath : ∀ N n : ℕ,
      w (S n) ((T^[n]) x0) ((T^[n + N]) x0) ≤ C * (r : ENNReal) ^ n := by
    intro N
    induction N with
    | zero =>
        intro n
        simp [hself (S n) (hS0 n)]
    | succ N ih =>
        intro n
        have hcv0 := hconv (lam n) (S (n + 1)) (hlam0 n) (hS0 (n + 1))
          ((T^[n]) x0) ((T^[n + (N + 1)]) x0) ((T^[n + 1]) x0)
        rw [← ENNReal.coe_add, hS_add n] at hcv0
        have hcv : w (S n) ((T^[n]) x0) ((T^[n + (N + 1)]) x0) ≤
            ((lam n : ENNReal) / (S n : ENNReal)) *
              w (lam n) ((T^[n]) x0) ((T^[n + 1]) x0) +
            ((S (n + 1) : ENNReal) / (S n : ENNReal)) *
              w (S (n + 1)) ((T^[n + (N + 1)]) x0) ((T^[n + 1]) x0) := by
          simpa [hS_add n, Function.iterate_succ_apply'] using hcv0
        have hfirst : ((lam n : ENNReal) / (S n : ENNReal)) ≤ 1 := by
          have hdiv : lam n / S n ≤ (1 : NNReal) :=
            div_le_one_of_le₀ (hlam_le_S n) (zero_le _)
          rw [← ENNReal.coe_div (ne_of_gt (hS0 n))]
          exact_mod_cast hdiv
        have hidx : n + (N + 1) = (n + 1) + N := by omega
        have hs : w (S (n + 1)) ((T^[n + (N + 1)]) x0) ((T^[n + 1]) x0) =
            w (S (n + 1)) ((T^[n + 1]) x0) ((T^[n + (N + 1)]) x0) :=
          hsymm (S (n + 1)) (hS0 (n + 1)) _ _
        have hih : w (S (n + 1)) ((T^[n + 1]) x0) ((T^[n + (N + 1)]) x0) ≤
            C * (r : ENNReal) ^ (n + 1) := by
          simpa [hidx] using ih (n + 1)
        calc
          w (S n) ((T^[n]) x0) ((T^[n + (N + 1)]) x0)
              ≤ ((lam n : ENNReal) / (S n : ENNReal)) *
                  w (lam n) ((T^[n]) x0) ((T^[n + 1]) x0) +
                ((S (n + 1) : ENNReal) / (S n : ENNReal)) *
                  w (S (n + 1)) ((T^[n + (N + 1)]) x0) ((T^[n + 1]) x0) := hcv
          _ ≤ 1 * (d0 * (r : ENNReal) ^ n) +
                (q : ENNReal) * (C * (r : ENNReal) ^ (n + 1)) := by
                apply add_le_add
                · exact mul_le_mul hfirst (hgeom n) (zero_le _) (zero_le _)
                · rw [hSratio n, hs]
                  exact mul_le_mul_left' hih _
          _ = d0 * (r : ENNReal) ^ n +
                (q : ENNReal) * (C * (r : ENNReal) ^ (n + 1)) := by rw [one_mul]
          _ = (d0 + (k : ENNReal) * C) * (r : ENNReal) ^ n := by
                have hqrE : (q : ENNReal) * (r : ENNReal) = (k : ENNReal) := by
                  rw [← ENNReal.coe_mul, hqr]
                have h : (q : ENNReal) * (C * (r : ENNReal) ^ (n + 1)) =
                    ((k : ENNReal) * C) * (r : ENNReal) ^ n := by
                  calc
                    (q : ENNReal) * (C * (r : ENNReal) ^ (n + 1))
                        = ((q : ENNReal) * (r : ENNReal)) *
                            (C * (r : ENNReal) ^ n) := by rw [pow_succ]; ring
                    _ = ((k : ENNReal) * C) * (r : ENNReal) ^ n := by rw [hqrE]; ring
                rw [h, add_mul]
          _ = C * (r : ENNReal) ^ n := by rw [hCeq]
  have hSratioL : ∀ n, ((S n : ENNReal) / (L : ENNReal)) = (q : ENNReal) ^ n := by
    intro n
    dsimp [S]
    have h0 : (L : ENNReal) ≠ 0 := by exact_mod_cast ne_of_gt hL0
    have ht : (L : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    calc
      (L : ENNReal) * (q : ENNReal) ^ n / (L : ENNReal)
          = (q : ENNReal) ^ n * ((L : ENNReal) / (L : ENNReal)) := by
            rw [mul_comm ((L : ENNReal)) ((q : ENNReal) ^ n), mul_div_assoc]
      _ = (q : ENNReal) ^ n := by rw [ENNReal.div_self h0 ht, mul_one]
  have hpair_left : ∀ n m : ℕ, n ≤ m →
      w L ((T^[n]) x0) ((T^[m]) x0) ≤ C * (k : ENNReal) ^ n := by
    intro n m hnm
    have hp0 := hpath (m - n) n
    have hsum : n + (m - n) = m := Nat.add_sub_of_le hnm
    have hp : w (S n) ((T^[n]) x0) ((T^[m]) x0) ≤ C * (r : ENNReal) ^ n := by
      simpa [hsum] using hp0
    have hsc := modular_scale_le w hself hconv (hS0 n) (hS_le n)
      ((T^[n]) x0) ((T^[m]) x0)
    have hqrpow : (q : ENNReal) ^ n * (C * (r : ENNReal) ^ n) =
        C * (k : ENNReal) ^ n := by
      have h : (q : ENNReal) ^ n * (r : ENNReal) ^ n = (k : ENNReal) ^ n := by
        rw [← ENNReal.coe_pow, ← ENNReal.coe_pow, ← ENNReal.coe_mul, ← mul_pow, hqr,
          ENNReal.coe_pow]
      calc
        (q : ENNReal) ^ n * (C * (r : ENNReal) ^ n)
            = C * ((q : ENNReal) ^ n * (r : ENNReal) ^ n) := by ring
        _ = C * (k : ENNReal) ^ n := by rw [h]
    calc
      w L ((T^[n]) x0) ((T^[m]) x0)
          ≤ ((S n : ENNReal) / (L : ENNReal)) *
              w (S n) ((T^[n]) x0) ((T^[m]) x0) := hsc
      _ = (q : ENNReal) ^ n * w (S n) ((T^[n]) x0) ((T^[m]) x0) := by
            rw [hSratioL n]
      _ ≤ (q : ENNReal) ^ n * (C * (r : ENNReal) ^ n) :=
            mul_le_mul_left' hp _
      _ = C * (k : ENNReal) ^ n := hqrpow
  have hpair : ∀ p : ℕ × ℕ,
      w L ((T^[p.1]) x0) ((T^[p.2]) x0) ≤ C * (k : ENNReal) ^ min p.1 p.2 := by
    intro p
    rcases le_total p.1 p.2 with h | h
    · simpa [min_eq_left h] using hpair_left p.1 p.2 h
    · have hs : w L ((T^[p.1]) x0) ((T^[p.2]) x0) =
          w L ((T^[p.2]) x0) ((T^[p.1]) x0) := hsymm L hL0 _ _
      calc
        w L ((T^[p.1]) x0) ((T^[p.2]) x0)
            = w L ((T^[p.2]) x0) ((T^[p.1]) x0) := hs
        _ ≤ C * (k : ENNReal) ^ p.2 := hpair_left p.2 p.1 h
        _ = C * (k : ENNReal) ^ min p.1 p.2 := by rw [min_eq_right h]
  have hupper : Filter.Tendsto
      (fun p : ℕ × ℕ => C * (k : ENNReal) ^ min p.1 p.2)
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0) :=
    tendsto_ennreal_const_mul_pow_min_zero hCne hk1
  have hCauchy : Filter.Tendsto
      (fun p : ℕ × ℕ => w L ((T^[p.1]) x0) ((T^[p.2]) x0))
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun p => zero_le _) hpair
  rcases hcomplete (fun n => (T^[n]) x0) L hL0 hCauchy with ⟨y, hlim⟩
  have hlim_yx : Filter.Tendsto (fun n : ℕ => w L y ((T^[n]) x0))
      Filter.atTop (nhds 0) := by
    convert hlim using 1
    ext n
    exact hsymm L hL0 _ _
  have htail : Filter.Tendsto (fun n : ℕ => w L y ((T^[n + 1]) x0))
      Filter.atTop (nhds 0) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2 hlim_yx
  have hctr_le : ∀ n : ℕ,
      w (k * L) (T y) ((T^[n + 1]) x0) ≤ w L y ((T^[n]) x0) := by
    intro n
    have hc := hcontr y ((T^[n]) x0) L hL0 le_rfl
    simpa [Function.iterate_succ_apply'] using hc
  have hctr_lim : Filter.Tendsto
      (fun n : ℕ => w (k * L) (T y) ((T^[n + 1]) x0))
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim_yx
      (fun n => zero_le _) hctr_le
  let s : NNReal := k * L + L
  have hs0 : 0 < s := by dsimp [s]; exact add_pos (mul_pos hk0 hL0) hL0
  let A : ENNReal := ((k * L : NNReal) : ENNReal) /
    (((k * L : NNReal) : ENNReal) + (L : ENNReal))
  let B : ENNReal := (L : ENNReal) /
    (((k * L : NNReal) : ENNReal) + (L : ENNReal))
  have hden : (((k * L : NNReal) : ENNReal) + (L : ENNReal)) ≠ 0 := by
    rw [← ENNReal.coe_add]
    exact_mod_cast ne_of_gt hs0
  have hAne : A ≠ ⊤ := by
    dsimp [A]
    exact ENNReal.div_ne_top ENNReal.coe_ne_top hden
  have hBne : B ≠ ⊤ := by
    dsimp [B]
    exact ENNReal.div_ne_top ENNReal.coe_ne_top hden
  have hA_lim : Filter.Tendsto
      (fun n : ℕ => A * w (k * L) (T y) ((T^[n + 1]) x0))
      Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hctr_lim (Or.inr hAne)
  have hB_lim : Filter.Tendsto
      (fun n : ℕ => B * w L y ((T^[n + 1]) x0))
      Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul htail (Or.inr hBne)
  have hsum_lim : Filter.Tendsto
      (fun n : ℕ => A * w (k * L) (T y) ((T^[n + 1]) x0) +
        B * w L y ((T^[n + 1]) x0))
      Filter.atTop (nhds 0) := by
    simpa using hA_lim.add hB_lim
  have hfix_le : ∀ n : ℕ,
      w s (T y) y ≤ A * w (k * L) (T y) ((T^[n + 1]) x0) +
        B * w L y ((T^[n + 1]) x0) := by
    intro n
    exact hconv (k * L) L (mul_pos hk0 hL0) hL0 (T y) y ((T^[n + 1]) x0)
  have hfix_seq : Filter.Tendsto (fun _ : ℕ => w s (T y) y)
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum_lim
      (fun n => zero_le _) hfix_le
  have hfix_zero : w s (T y) y = 0 := (tendsto_const_nhds_iff).1 hfix_seq
  have hfix_val : (T y : X) = (y : X) :=
    hstrict (T y) y ⟨s, hs0, hfix_zero⟩
  have hfix : T y = y := Subtype.ext hfix_val
  exact ⟨y, hfix, hlim⟩

/- accepted add_to_file helper 4 -/
lemma ennreal_eq_zero_of_le_coe_mul_self {d : ENNReal} (hd : d ≠ ⊤)
    {k : NNReal} (hk : k < 1) (h : d ≤ (k : ENNReal) * d) : d = 0 := by
  have hprod : (k : ENNReal) * d ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hd
  have hr : d.toReal ≤ (k : ℝ) * d.toReal := by
    have hr0 := (ENNReal.toReal_le_toReal hd hprod).2 h
    simpa [ENNReal.toReal_mul] using hr0
  have hz : d.toReal = 0 := by
    nlinarith [ENNReal.toReal_nonneg (a := d)]
  exact (ENNReal.toReal_eq_zero_iff d).1 hz |>.resolve_right hd

/- verified submission -/
theorem strict_convex_modular_fixed_point
    {X : Type*} (b : X) (w : NNReal → X → X → ENNReal)
    (hself : ∀ (l : NNReal), 0 < l → ∀ x : X, w l x x = 0)
    (hsymm : ∀ (l : NNReal), 0 < l → ∀ x y : X, w l x y = w l y x)
    (hstrict : ∀ x y : X, (∃ l : NNReal, 0 < l ∧ w l x y = 0) → x = y)
    (hconv : ∀ (l m : NNReal), 0 < l → 0 < m → ∀ x y z : X,
      w (l + m) x y ≤ ((l : ENNReal) / (l + m)) * w l x z +
        ((m : ENNReal) / (l + m)) * w m y z)
    (hcomplete : ∀ (x : ℕ → {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤})
      (l : NNReal), 0 < l →
      Filter.Tendsto (fun p : ℕ × ℕ => w l (x p.1) (x p.2))
        (Filter.atTop ×ˢ Filter.atTop) (nhds 0) →
      ∃ y : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
        Filter.Tendsto (fun n => w l (x n) y) Filter.atTop (nhds 0))
    (T : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤} →
      {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤})
    (hcontractive : ∃ k L : NNReal, 0 < k ∧ k < 1 ∧ 0 < L ∧
      ∀ x y : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
        ∀ l : NNReal, 0 < l → l ≤ L → w (k * l) (T x) (T y) ≤ w l x y) :
    ((∀ l : NNReal, 0 < l →
        ∃ x : {x : X // ∃ m : NNReal, 0 < m ∧ w m x b < ⊤},
          w l x (T x) < ⊤) →
      ∃ x : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤}, T x = x) ∧
    ((∀ l : NNReal, 0 < l →
        ∀ x y : {x : X // ∃ m : NNReal, 0 < m ∧ w m x b < ⊤}, w l x y < ⊤) →
      ∃ xstar : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
        T xstar = xstar ∧
        (∀ y : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
          T y = y → y = xstar) ∧
        ∀ x : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
          ∃ l : NNReal, 0 < l ∧
            Filter.Tendsto (fun n : ℕ => w l ((T^[n]) x) xstar)
              Filter.atTop (nhds 0)) := by
  constructor
  · intro hdisp
    rcases hcontractive with ⟨k, L, hk0, hk1, hL0, hcontr⟩
    let a : NNReal := (1 - (1 + k) / 2) * L
    have ha0 : 0 < a := by
      dsimp [a]
      have h : (1 + k) / 2 < 1 := by nlinarith [hk1]
      exact mul_pos (tsub_pos_of_lt h) hL0
    rcases hdisp a ha0 with ⟨x0, hx0⟩
    rcases modular_fixed_point_of_displacement b w hself hsymm hstrict hconv
        hcomplete T hk0 hk1 hL0 hcontr x0 hx0 with ⟨y, hy, -⟩
    exact ⟨y, hy⟩
  · intro hfinite
    rcases hcontractive with ⟨k, L, hk0, hk1, hL0, hcontr⟩
    let a : NNReal := (1 - (1 + k) / 2) * L
    have ha0 : 0 < a := by
      dsimp [a]
      have h : (1 + k) / 2 < 1 := by nlinarith [hk1]
      exact mul_pos (tsub_pos_of_lt h) hL0
    have hbw : w L b b < ⊤ := by
      rw [hself L hL0 b]
      exact ENNReal.zero_lt_top
    let xb : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤} :=
      ⟨b, ⟨L, hL0, hbw⟩⟩
    have hxb : w a xb (T xb) < ⊤ := hfinite a ha0 xb (T xb)
    rcases modular_fixed_point_of_displacement b w hself hsymm hstrict hconv
        hcomplete T hk0 hk1 hL0 hcontr xb hxb with ⟨xstar, hstar, -⟩
    have huniq : ∀ y : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
        T y = y → y = xstar := by
      intro y hy
      let d : ENNReal := w L y xstar
      have hdne : d ≠ ⊤ := by
        dsimp [d]
        exact ne_of_lt (hfinite L hL0 y xstar)
      have hctr0 := hcontr y xstar L hL0 le_rfl
      have hctr : w (k * L) y xstar ≤ d := by
        simpa [d, hy, hstar] using hctr0
      have hkL : 0 < k * L := mul_pos hk0 hL0
      have hkL_le : k * L ≤ L := by
        calc
          k * L ≤ 1 * L := mul_le_mul_right' hk1.le L
          _ = L := one_mul L
      have hsc := modular_scale_le w hself hconv hkL hkL_le y xstar
      have hcoef : (((k * L : NNReal) : ENNReal) / (L : ENNReal)) = (k : ENNReal) := by
        have h0 : (L : ENNReal) ≠ 0 := by exact_mod_cast ne_of_gt hL0
        have ht : (L : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
        calc
          (((k * L : NNReal) : ENNReal) / (L : ENNReal))
              = ((k : ENNReal) * (L : ENNReal)) / (L : ENNReal) := by
                  rw [ENNReal.coe_mul]
          _ = (k : ENNReal) * ((L : ENNReal) / (L : ENNReal)) := by
                  rw [mul_div_assoc]
          _ = (k : ENNReal) := by
                  rw [ENNReal.div_self h0 ht, mul_one]
      have hdself : d ≤ (k : ENNReal) * d := by
        calc
          d = w L y xstar := rfl
          _ ≤ (((k * L : NNReal) : ENNReal) / (L : ENNReal)) *
                w (k * L) y xstar := hsc
          _ = (k : ENNReal) * w (k * L) y xstar := by rw [hcoef]
          _ ≤ (k : ENNReal) * d := mul_le_mul_left' hctr _
      have hdzero : d = 0 := ennreal_eq_zero_of_le_coe_mul_self hdne hk1 hdself
      have hval : (y : X) = (xstar : X) :=
        hstrict y xstar ⟨L, hL0, hdzero⟩
      exact Subtype.ext hval
    refine ⟨xstar, hstar, huniq, ?_⟩
    intro x
    have hx : w a x (T x) < ⊤ := hfinite a ha0 x (T x)
    rcases modular_fixed_point_of_displacement b w hself hsymm hstrict hconv
        hcomplete T hk0 hk1 hL0 hcontr x hx with ⟨y, hy, hlim⟩
    have hyx : y = xstar := huniq y hy
    exact ⟨L, hL0, by simpa [hyx] using hlim⟩

end Rollout_p1151_strict_convex_modular_fixed_point

namespace Rollout_p0824_finite_category_mobius_zero

/- verified submission -/

open CategoryTheory

theorem finite_category_mobius_zero
    {A : Type u} [CategoryTheory.Category.{v, u} A] [Fintype A]
    [DecidableEq A] [∀ a b : A, Fintype (a ⟶ b)]
    (μ : A → A → ℚ)
    (hμζ : ∀ a c : A,
      ∑ b : A, μ a b * (Fintype.card (b ⟶ c) : ℚ) =
        if a = c then 1 else 0)
    (hζμ : ∀ a c : A,
      ∑ b : A, (Fintype.card (a ⟶ b) : ℚ) * μ b c =
        if a = c then 1 else 0)
    {a b : A} (hab : IsEmpty (a ⟶ b)) :
    μ a b = 0 := by
  let ζ : Matrix A A ℚ := fun i j => (Fintype.card (i ⟶ j) : ℚ)
  let M : Matrix A A ℚ := fun i j => μ i j
  have hMZ : M * ζ = 1 := by
    ext i j
    simpa [M, ζ, Matrix.mul_apply] using hμζ i j
  have hZM : ζ * M = 1 := by
    ext i j
    simpa [M, ζ, Matrix.mul_apply] using hζμ i j
  letI : Invertible ζ := invertibleOfRightInverse ζ M hZM
  let label : A → Bool := fun x => decide (Fintype.card (x ⟶ b) = 0)
  have hζtri : ζ.BlockTriangular label := by
    intro i j hlt
    by_contra hijζ
    have hcard : Fintype.card (i ⟶ j) ≠ 0 := by
      intro hcard
      apply hijζ
      simp [ζ, hcard]
    have hij : Nonempty (i ⟶ j) :=
      Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hcard)
    have hjfalse : label j = false := (Bool.lt_iff.mp hlt).1
    have hitrue : label i = true := (Bool.lt_iff.mp hlt).2
    have hjcard : Fintype.card (j ⟶ b) ≠ 0 := by
      intro hjcard
      simp [label, hjcard] at hjfalse
    have hjreach : Nonempty (j ⟶ b) :=
      Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hjcard)
    have hicard : Fintype.card (i ⟶ b) = 0 := by
      by_contra hicard
      simp [label, hicard] at hitrue
    have hinreach : ¬ Nonempty (i ⟶ b) := by
      intro hi
      have hpos : 0 < Fintype.card (i ⟶ b) := Fintype.card_pos
      omega
    exact hinreach ⟨hij.some ≫ hjreach.some⟩
  have hμtri : (ζ⁻¹).BlockTriangular label :=
    Matrix.blockTriangular_inv_of_blockTriangular hζtri
  have hinv : ζ⁻¹ = M := Matrix.inv_eq_left_inv hMZ
  have hbcard : Fintype.card (b ⟶ b) ≠ 0 := by
    have hb : Nonempty (b ⟶ b) := ⟨𝟙 b⟩
    exact Fintype.card_ne_zero
  have hlt : label b < label a := by
    rw [Bool.lt_iff]
    constructor
    · simp [label, hbcard]
    · simp [label]
  have hzero : (ζ⁻¹) a b = 0 := hμtri hlt
  have : M a b = 0 := by
    simpa [hinv] using hzero
  simpa [M] using this

end Rollout_p0824_finite_category_mobius_zero

namespace Rollout_p2604_diagonal_convergence_of_sequences

/- verified submission -/

open Filter Topology

theorem diagonal_convergence_of_sequences
    {E : Type*} [MetricSpace E]
    (a : ℕ → ℕ → E) (aInf : ℕ → E) (aInfInf : E)
    (ha : ∀ m : ℕ, Filter.Tendsto (a m) Filter.atTop (nhds (aInf m)))
    (hInf : Filter.Tendsto aInf Filter.atTop (nhds aInfInf)) :
    ∃ b : ℕ → ℕ,
      Monotone b ∧
      Filter.Tendsto b Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun n : ℕ => a (b n) n) Filter.atTop (nhds aInfInf) := by
  choose N hN using fun (m : ℕ) (k : ℕ) =>
    Metric.tendsto_atTop.mp (ha m) (1 / ((k : ℝ) + 1))
      (one_div_pos.mpr (Nat.cast_add_one_pos k))
  let A : ℕ → ℕ := fun m =>
    max m ((Finset.range (m + 1)).sup fun k => N m k)
  let b : ℕ → ℕ := fun n => Nat.findGreatest (fun m => A m ≤ n) n
  have hbmono : Monotone b := by
    intro m n hmn
    dsimp [b]
    calc
      Nat.findGreatest (fun k => A k ≤ m) m
          ≤ Nat.findGreatest (fun k => A k ≤ m) n :=
        Nat.findGreatest_mono_right (fun k => A k ≤ m) hmn
      _ ≤ Nat.findGreatest (fun k => A k ≤ n) n :=
        Nat.findGreatest_mono_left (fun k hk => le_trans hk hmn) n
  have hbtop : Filter.Tendsto b Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop_iff_of_monotone hbmono]
    intro m
    refine ⟨A m, ?_⟩
    dsimp [b]
    exact Nat.le_findGreatest (P := fun k => A k ≤ A m) (le_max_left _ _) le_rfl
  refine ⟨b, hbmono, hbtop, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_one_div_lt (K := ℝ) (show 0 < ε / 2 by positivity)
  obtain ⟨L, hL⟩ := Metric.tendsto_atTop.mp hInf (ε / 2) (by positivity)
  obtain ⟨Nb, hNb⟩ := Filter.tendsto_atTop_atTop.mp hbtop (max K L)
  refine ⟨max (A 0) Nb, ?_⟩
  intro n hn
  have hA0n : A 0 ≤ n := le_trans (le_max_left _ _) hn
  have hAbn : A (b n) ≤ n := by
    dsimp [b]
    exact Nat.findGreatest_spec (P := fun m => A m ≤ n) (Nat.zero_le n) hA0n
  have hbn_ge : max K L ≤ b n := hNb n (le_trans (le_max_right _ _) hn)
  have hKb : K ≤ b n := le_trans (le_max_left _ _) hbn_ge
  have hLb : L ≤ b n := le_trans (le_max_right _ _) hbn_ge
  have hNA : N (b n) (b n) ≤ A (b n) := by
    have hmem : b n ∈ Finset.range (b n + 1) := by simp
    have hs := Finset.le_sup (s := Finset.range (b n + 1))
      (f := fun k => N (b n) k) hmem
    dsimp [A]
    exact le_trans hs (le_max_right _ _)
  have hfirst : dist (a (b n) n) (aInf (b n)) < 1 / ((b n : ℝ) + 1) :=
    hN (b n) (b n) n (le_trans hNA hAbn)
  have hcast : (K : ℝ) + 1 ≤ (b n : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ hKb
  have hrec : 1 / ((b n : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1) :=
    one_div_le_one_div_of_le (Nat.cast_add_one_pos K) hcast
  have hfirst' : dist (a (b n) n) (aInf (b n)) < ε / 2 :=
    lt_trans (lt_of_lt_of_le hfirst hrec) hK
  have hsecond : dist (aInf (b n)) aInfInf < ε / 2 := hL (b n) hLb
  calc
    dist (a (b n) n) aInfInf
        ≤ dist (a (b n) n) (aInf (b n)) + dist (aInf (b n)) aInfInf :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hfirst' hsecond
    _ = ε := by ring

end Rollout_p2604_diagonal_convergence_of_sequences

namespace Rollout_p1180_inversealong_units

/- verified submission -/
lemma rightIdeal_subset_of_units
    {R : Type*} [Ring R] {b d : R} (u v : Rˣ)
    (h : Set.range (fun y : R => b * y) ⊆ Set.range (fun y : R => d * y)) :
    Set.range (fun y : R => ((u : R) * b * (v : R)) * y) ⊆
      Set.range (fun y : R => ((u : R) * d * (v : R)) * y) := by
  intro z hz
  rcases hz with ⟨y, rfl⟩
  have hb : b * ((v : R) * y) ∈ Set.range (fun y : R => d * y) := by
    exact h ⟨((v : R) * y), rfl⟩
  rcases hb with ⟨w, hw⟩
  use (((v⁻¹ : Rˣ) : R) * w)
  simpa [mul_assoc] using congrArg (fun t : R => (u : R) * t) hw

lemma rightIdeal_eq_of_units
    {R : Type*} [Ring R] {b d : R} (u v : Rˣ)
    (h : Set.range (fun y : R => b * y) = Set.range (fun y : R => d * y)) :
    Set.range (fun y : R => ((u : R) * b * (v : R)) * y) =
      Set.range (fun y : R => ((u : R) * d * (v : R)) * y) := by
  apply Set.Subset.antisymm
  · exact rightIdeal_subset_of_units u v (subset_of_eq h)
  · exact rightIdeal_subset_of_units u v (subset_of_eq h.symm)

lemma leftIdeal_subset_of_units
    {R : Type*} [Ring R] {b d : R} (u v : Rˣ)
    (h : Set.range (fun y : R => y * b) ⊆ Set.range (fun y : R => y * d)) :
    Set.range (fun y : R => y * ((u : R) * b * (v : R))) ⊆
      Set.range (fun y : R => y * ((u : R) * d * (v : R))) := by
  intro z hz
  rcases hz with ⟨y, rfl⟩
  have hb : ((y * (u : R)) * b) ∈ Set.range (fun y : R => y * d) := by
    exact h ⟨(y * (u : R)), rfl⟩
  rcases hb with ⟨w, hw⟩
  use w * (((u⁻¹ : Rˣ) : R))
  simpa [mul_assoc] using congrArg (fun t : R => t * (v : R)) hw

lemma leftIdeal_eq_of_units
    {R : Type*} [Ring R] {b d : R} (u v : Rˣ)
    (h : Set.range (fun y : R => y * b) = Set.range (fun y : R => y * d)) :
    Set.range (fun y : R => y * ((u : R) * b * (v : R))) =
      Set.range (fun y : R => y * ((u : R) * d * (v : R))) := by
  apply Set.Subset.antisymm
  · exact leftIdeal_subset_of_units u v (subset_of_eq h)
  · exact leftIdeal_subset_of_units u v (subset_of_eq h.symm)

theorem inverseAlong_units
    {R : Type*} [Ring R] {a b d : R} (r s : Rˣ)
    (h_inner : b * a * b = b)
    (h_right : Set.range (fun y : R => b * y) = Set.range (fun y : R => d * y))
    (h_left : Set.range (fun y : R => y * b) = Set.range (fun y : R => y * d)) :
    (((r : R) * b * ((s⁻¹ : Rˣ) : R)) *
          ((s : R) * a * ((r⁻¹ : Rˣ) : R)) *
          ((r : R) * b * ((s⁻¹ : Rˣ) : R)) =
        (r : R) * b * ((s⁻¹ : Rˣ) : R)) ∧
      Set.range (fun y : R => ((r : R) * b * ((s⁻¹ : Rˣ) : R)) * y) =
        Set.range (fun y : R => ((r : R) * d * ((s⁻¹ : Rˣ) : R)) * y) ∧
      Set.range (fun y : R => y * ((r : R) * b * ((s⁻¹ : Rˣ) : R))) =
        Set.range (fun y : R => y * ((r : R) * d * ((s⁻¹ : Rˣ) : R))) := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      ((r : R) * b * ((s⁻¹ : Rˣ) : R)) *
          ((s : R) * a * ((r⁻¹ : Rˣ) : R)) *
          ((r : R) * b * ((s⁻¹ : Rˣ) : R))
          = (r : R) * (b * a * b) * ((s⁻¹ : Rˣ) : R) := by
            simp [mul_assoc]
      _ = (r : R) * b * ((s⁻¹ : Rˣ) : R) := by
            simp [h_inner, mul_assoc]
  · exact rightIdeal_eq_of_units r s⁻¹ h_right
  · exact leftIdeal_eq_of_units r s⁻¹ h_left

end Rollout_p1180_inversealong_units

namespace Rollout_p2697_finite_field_normalized_one_cocycle_iff

/- verified submission -/
theorem finite_field_normalized_one_cocycle_iff
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≡ 1 [MOD q])
    (ν : (ZMod p)ˣ) (hν : orderOf ν = q)
    (α : ZMod q → GaloisField p 2) (hα : α ≠ 0) :
    (α 0 = 0 ∧
      ∀ x y : ZMod q,
        α (x + y) =
          α x + (algebraMap (ZMod p) (GaloisField p 2) (ν : ZMod p)) ^ x.val * α y) ↔
      ∃ r : GaloisField p 2, r ≠ 0 ∧ α 0 = 0 ∧
        ∀ x : ZMod q, x ≠ 0 →
          α x = r * ∑ j ∈ Finset.range x.val,
            (algebraMap (ZMod p) (GaloisField p 2) (ν : ZMod p)) ^ j := by
  classical
  let t : GaloisField p 2 := algebraMap (ZMod p) (GaloisField p 2) (ν : ZMod p)
  let S : ℕ → GaloisField p 2 := fun n => ∑ j ∈ Finset.range n, t ^ j
  constructor
  · intro h
    rcases h with ⟨h0, hcoc⟩
    have hform_nat : ∀ n : ℕ, n ≤ q → α (n : ZMod q) = α 1 * S n := by
      intro n
      induction n with
      | zero =>
          intro hn
          simp [S, h0]
      | succ n ih =>
          intro hn
          have hnq : n < q := Nat.lt_of_succ_le hn
          have ih' : α (n : ZMod q) = α 1 * S n := ih (Nat.le_of_lt hnq)
          calc
            α ((n + 1 : ℕ) : ZMod q) = α ((n : ZMod q) + 1) := by
              norm_num
            _ = α (n : ZMod q) + t ^ ((n : ZMod q).val) * α 1 := hcoc (n : ZMod q) 1
            _ = α 1 * S n + t ^ n * α 1 := by
              rw [ZMod.val_cast_of_lt hnq, ih']
            _ = α 1 * S (n + 1) := by
              simp [S, Finset.sum_range_succ]
              ring
    have hform : ∀ x : ZMod q, α x = α 1 * S x.val := by
      intro x
      have hx := hform_nat x.val (Nat.le_of_lt (ZMod.val_lt x))
      rwa [ZMod.natCast_zmod_val x] at hx
    refine ⟨α 1, ?_, h0, ?_⟩
    · by_contra hr
      apply hα
      funext x
      have hx := hform x
      rw [hr] at hx
      simpa using hx
    · intro x hx
      simpa [S] using hform x
  · intro h
    rcases h with ⟨r, hr, h0, hformne⟩
    have htpow : t ^ q = 1 := by
      have hνpow : (ν : ZMod p) ^ q = 1 := by
        have hu : ν ^ q = 1 := by
          rw [← hν]
          exact pow_orderOf_eq_one ν
        exact congrArg Units.val hu
      calc
        t ^ q = algebraMap (ZMod p) (GaloisField p 2) ((ν : ZMod p) ^ q) := by
          simp [t, map_pow]
        _ = 1 := by
          rw [hνpow]
          simp
    have htne : t ≠ 1 := by
      intro ht
      have hmap : algebraMap (ZMod p) (GaloisField p 2) (ν : ZMod p) =
          algebraMap (ZMod p) (GaloisField p 2) 1 := by
        simpa [t] using ht
      have hcoerce : (ν : ZMod p) = 1 :=
        (RingHom.injective (algebraMap (ZMod p) (GaloisField p 2))) hmap
      have hunit : ν = 1 := Units.ext hcoerce
      have hqeq : q = 1 := by
        rw [← hν, hunit]
        exact orderOf_one
      exact (Fact.out : Nat.Prime q).ne_one hqeq
    have hqsum : S q = 0 := by
      have hg := geom_sum_eq (x := t) htne q
      rw [htpow] at hg
      simpa [S] using hg
    have hsplit : ∀ m n : ℕ, S (m+n) = S m + t^m * S n := by
      intro m n
      dsimp [S]
      rw [Finset.sum_range_add]
      rw [Finset.mul_sum]
      apply congrArg ((∑ j ∈ Finset.range m, t ^ j) + ·)
      apply Finset.sum_congr rfl
      intro z hz
      rw [pow_add]
    have hgeom : ∀ x y : ZMod q,
        S (x+y).val = S x.val + t ^ x.val * S y.val := by
      intro x y
      by_cases hover : q ≤ x.val + y.val
      · have hval : (x + y).val = x.val + y.val - q := ZMod.val_add_of_le hover
        have hdecomp : x.val + y.val = q + (x + y).val := by
          rw [hval]
          omega
        calc
          S (x+y).val = S (q + (x+y).val) := by
            rw [hsplit q (x+y).val, hqsum, htpow]
            simp
          _ = S (x.val + y.val) := by
            rw [← hdecomp]
          _ = S x.val + t ^ x.val * S y.val := hsplit x.val y.val
      · have hlt : x.val + y.val < q := Nat.lt_of_not_ge hover
        have hval : (x+y).val = x.val+y.val := by
          rw [ZMod.val_add, Nat.mod_eq_of_lt hlt]
        rw [hval]
        exact hsplit x.val y.val
    have hall : ∀ z : ZMod q, α z = r * S z.val := by
      intro z
      by_cases hz : z = 0
      · rw [hz, h0]
        simp [S]
      · simpa [S] using hformne z hz
    constructor
    · exact h0
    · intro x y
      calc
        α (x+y) = r * S (x+y).val := hall (x+y)
        _ = r * (S x.val + t ^ x.val * S y.val) := by
          rw [hgeom x y]
        _ = α x + t ^ x.val * α y := by
          rw [hall x, hall y]
          ring

end Rollout_p2697_finite_field_normalized_one_cocycle_iff

namespace Rollout_p1226_continuous_quadratic_form_delta_semidefini

/- accepted add_to_file helper 1 -/

/-- A fresh copy of a real vector space, used to equip it with a new pre-inner product. -/
structure QuadraticPreHilbert (X : Type u) [AddCommGroup X] [Module ℝ X] where
  val : X

namespace QuadraticPreHilbert

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

def equiv : QuadraticPreHilbert X ≃ X where
  toFun := val
  invFun := mk
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; rfl

instance : AddCommGroup (QuadraticPreHilbert X) := equiv.addCommGroup
instance : Module ℝ (QuadraticPreHilbert X) := Equiv.module ℝ equiv

@[simp] theorem val_zero : (0 : QuadraticPreHilbert X).val = 0 := rfl
@[simp] theorem val_add (x y : QuadraticPreHilbert X) : (x + y).val = x.val + y.val := rfl
@[simp] theorem val_smul (r : ℝ) (x : QuadraticPreHilbert X) : (r • x).val = r • x.val := rfl

/-- The pre-inner product associated with the symmetrization of a continuous bilinear form. -/
@[implicit_reducible]
noncomputable def preCore (bp : X →L[ℝ] X →L[ℝ] ℝ)
    (hnonneg : ∀ x : X, 0 ≤ (bp x x + bp x x) / 2) :
    PreInnerProductSpace.Core ℝ (QuadraticPreHilbert X) where
  inner x y := (bp x.val y.val + bp y.val x.val) / 2
  conj_inner_symm x y := by
    simp [add_comm]
  re_inner_nonneg x := hnonneg x.val
  add_left x y z := by
    simp [map_add]
    ring_nf
  smul_left x y r := by
    simp [map_smul]
    ring_nf

end QuadraticPreHilbert

/- accepted add_to_file helper 2 -/
lemma dominated_bilinear_abs_le_avg
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : X → ℝ) (T : X →L[ℝ] (X →L[ℝ] ℝ))
    (hTq : ∀ x : X, q x = T x x)
    (hTsymm : ∀ x y : X, T x y = T y x)
    (bp : X →L[ℝ] X →L[ℝ] ℝ)
    (hdom : ∀ x : X, |q x| ≤ bp x x)
    (x y : X) :
    |T x y| ≤ (bp x x + bp y y) / 2 := by
  have hpol : T (x+y) (x+y) - T (x-y) (x-y) = 4 * T x y := by
    simp [map_add, map_sub, hTsymm x y]
    ring
  have hpsum : bp (x+y) (x+y) + bp (x-y) (x-y) =
      2 * (bp x x + bp y y) := by
    simp [map_add, map_sub]
    ring
  have hplus : |T (x+y) (x+y)| ≤ bp (x+y) (x+y) := by
    simpa [hTq] using hdom (x+y)
  have hminus : |T (x-y) (x-y)| ≤ bp (x-y) (x-y) := by
    simpa [hTq] using hdom (x-y)
  have hsub : |T (x+y) (x+y) - T (x-y) (x-y)| ≤
      bp (x+y) (x+y) + bp (x-y) (x-y) := by
    calc
      |T (x+y) (x+y) - T (x-y) (x-y)|
          ≤ |T (x+y) (x+y)| + |T (x-y) (x-y)| := abs_sub _ _
      _ ≤ bp (x+y) (x+y) + bp (x-y) (x-y) := add_le_add hplus hminus
  rw [hpol, hpsum] at hsub
  have habs4 : |4 * T x y| = 4 * |T x y| := by norm_num [abs_of_nonneg]
  rw [habs4] at hsub
  nlinarith [abs_nonneg (T x y)]

/- accepted add_to_file helper 3 -/
lemma dominated_bilinear_abs_le_sqrt_mul
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : X → ℝ) (T : X →L[ℝ] (X →L[ℝ] ℝ))
    (hTq : ∀ x : X, q x = T x x)
    (hTsymm : ∀ x y : X, T x y = T y x)
    (bp : X →L[ℝ] X →L[ℝ] ℝ)
    (hdom : ∀ x : X, |q x| ≤ bp x x)
    (x y : X) :
    |T x y| ≤ Real.sqrt (bp x x) * Real.sqrt (bp y y) := by
  have hpx : 0 ≤ bp x x := le_trans (abs_nonneg _) (hdom x)
  have hpy : 0 ≤ bp y y := le_trans (abs_nonneg _) (hdom y)
  by_cases hx0 : bp x x = 0
  · by_contra hz
    have hzne : |T x y| ≠ 0 := by
      intro hzero
      apply hz
      rw [hzero]
      positivity
    have hzpos : 0 < |T x y| := lt_of_le_of_ne' (abs_nonneg _) hzne
    let r : ℝ := (bp y y / 2 + 1) / |T x y|
    have hrpos : 0 < r := by positivity
    have hb := dominated_bilinear_abs_le_avg q T hTq hTsymm bp hdom (r • x) y
    simp [hx0, map_smul, abs_mul, abs_of_pos hrpos] at hb
    have hreq : r * |T x y| = bp y y / 2 + 1 := by
      dsimp [r]
      field_simp [ne_of_gt hzpos]
    nlinarith [hpy]
  · by_cases hy0 : bp y y = 0
    · by_contra hz
      have hzne : |T x y| ≠ 0 := by
        intro hzero
        apply hz
        rw [hzero]
        positivity
      have hzpos : 0 < |T x y| := lt_of_le_of_ne' (abs_nonneg _) hzne
      let r : ℝ := (bp x x / 2 + 1) / |T x y|
      have hrpos : 0 < r := by positivity
      have hb := dominated_bilinear_abs_le_avg q T hTq hTsymm bp hdom x (r • y)
      simp [hy0, map_smul, abs_mul, abs_of_pos hrpos] at hb
      have hreq : r * |T x y| = bp x x / 2 + 1 := by
        dsimp [r]
        field_simp [ne_of_gt hzpos]
      nlinarith [hpx]
    · have hxpos : 0 < bp x x := lt_of_le_of_ne hpx (Ne.symm hx0)
      have hypos : 0 < bp y y := lt_of_le_of_ne hpy (Ne.symm hy0)
      let a : ℝ := Real.sqrt (bp x x)
      let b : ℝ := Real.sqrt (bp y y)
      let r : ℝ := Real.sqrt (bp y y / bp x x)
      have hapos : 0 < a := Real.sqrt_pos.mpr hxpos
      have hbpos : 0 < b := Real.sqrt_pos.mpr hypos
      have hrpos : 0 < r := Real.sqrt_pos.mpr (div_pos hypos hxpos)
      have hbasic := dominated_bilinear_abs_le_avg q T hTq hTsymm bp hdom (r • x) y
      simp [map_smul, abs_mul, abs_of_pos hrpos] at hbasic
      have hrsq : r ^ 2 * bp x x = bp y y := by
        dsimp [r]
        rw [Real.sq_sqrt (div_nonneg hpy hpx)]
        field_simp [ne_of_gt hxpos]
      have hscale : r * |T x y| ≤ bp y y := by
        nlinarith
      have hsqrtdiv : r = b / a := by
        dsimp [r, b, a]
        exact Real.sqrt_div hpy (bp x x)
      have hmul : a * r = b := by
        rw [hsqrtdiv]
        field_simp [ne_of_gt hapos]
      have hleft : b * |T x y| ≤ a * (b * b) := by
        have h := mul_le_mul_of_nonneg_left hscale (le_of_lt hapos)
        calc
          b * |T x y| = a * (r * |T x y|) := by
            conv_lhs => rw [← hmul]
            ring
          _ ≤ a * bp y y := h
          _ = a * (b * b) := by
            dsimp [b]
            rw [Real.mul_self_sqrt hpy]
      exact le_of_mul_le_mul_right (by
        calc
          |T x y| * b = b * |T x y| := mul_comm _ _
          _ ≤ a * (b * b) := hleft
          _ = (a * b) * b := by ring) hbpos

/- accepted add_to_file helper 4 -/
lemma dominated_implies_hilbert_factorization
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (q : X → ℝ)
    (T : X →L[ℝ] (X →L[ℝ] ℝ))
    (hTq : ∀ x : X, q x = T x x)
    (hTsymm : ∀ x y : X, T x y = T y x)
    (p : X → ℝ) (bp : X →L[ℝ] X →L[ℝ] ℝ)
    (hp : ∀ x : X, p x = bp x x)
    (hdomp : ∀ x : X, |q x| ≤ p x) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
        (_ : CompleteSpace H) (A : X →L[ℝ] H) (B : H →L[ℝ] (X →L[ℝ] ℝ)),
      T = B.comp A := by
  have hdom : ∀ x : X, |q x| ≤ bp x x := by
    intro x
    simpa [hp x] using hdomp x
  have hnonneg : ∀ x : X, 0 ≤ (bp x x + bp x x) / 2 := by
    intro x
    have hx : 0 ≤ bp x x := le_trans (abs_nonneg _) (hdom x)
    nlinarith
  let E := QuadraticPreHilbert X
  letI core : PreInnerProductSpace.Core ℝ E := QuadraticPreHilbert.preCore bp hnonneg
  letI semi : SeminormedAddCommGroup E :=
    InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜:=ℝ) (F:=E)
  letI ips : InnerProductSpace ℝ E := InnerProductSpace.ofCore core
  let toE : X →ₗ[ℝ] E := {
    toFun := QuadraticPreHilbert.mk
    map_add' := by intro x y; rfl
    map_smul' := by intro r x; rfl }
  have hbound : ∀ x : X, ‖toE x‖ ≤ Real.sqrt ‖bp‖ * ‖x‖ := by
    intro x
    have hnorm : ‖toE x‖ = Real.sqrt (bp x x) := by
      change ‖(QuadraticPreHilbert.mk x : QuadraticPreHilbert X)‖ = Real.sqrt (bp x x)
      have h : ‖(QuadraticPreHilbert.mk x : QuadraticPreHilbert X)‖ =
          Real.sqrt ((bp x x + bp x x) / 2) := rfl
      rw [h]
      ring_nf
    have habs : |bp x x| ≤ ‖bp x‖ * ‖x‖ := ContinuousLinearMap.le_opNorm (bp x) x
    have hbp : ‖bp x‖ ≤ ‖bp‖ * ‖x‖ := ContinuousLinearMap.le_opNorm bp x
    have hple : bp x x ≤ ‖bp‖ * (‖x‖ * ‖x‖) := by
      calc
        bp x x ≤ |bp x x| := le_abs_self _
        _ ≤ ‖bp x‖ * ‖x‖ := habs
        _ ≤ (‖bp‖ * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right hbp (norm_nonneg _)
        _ = ‖bp‖ * (‖x‖ * ‖x‖) := by ring
    calc
      ‖toE x‖ = Real.sqrt (bp x x) := hnorm
      _ ≤ Real.sqrt (‖bp‖ * (‖x‖ * ‖x‖)) := Real.sqrt_le_sqrt hple
      _ = Real.sqrt ‖bp‖ * ‖x‖ := by
        rw [Real.sqrt_mul (norm_nonneg bp) (‖x‖ * ‖x‖),
          Real.sqrt_mul_self (norm_nonneg x)]
  let A0 : X →L[ℝ] E := LinearMap.mkContinuous toE (Real.sqrt ‖bp‖) hbound
  let Tlin : E →ₗ[ℝ] (X →L[ℝ] ℝ) := {
    toFun := fun e => T e.val
    map_add' := by
      intro e f
      change T (e.val + f.val) = T e.val + T f.val
      exact map_add T e.val f.val
    map_smul' := by
      intro r e
      change T (r • e.val) = r • T e.val
      exact map_smul T r e.val }
  have hTbound : ∀ e : E, ‖Tlin e‖ ≤ Real.sqrt ‖bp‖ * ‖e‖ := by
    intro e
    have hpoint : ∀ y : X,
        ‖T e.val y‖ ≤ (Real.sqrt ‖bp‖ * Real.sqrt (bp e.val e.val)) * ‖y‖ := by
      intro y
      have hc := dominated_bilinear_abs_le_sqrt_mul q T hTq hTsymm bp hdom e.val y
      have hyb := hbound y
      have hnormy : ‖toE y‖ = Real.sqrt (bp y y) := by
        change ‖(QuadraticPreHilbert.mk y : QuadraticPreHilbert X)‖ =
          Real.sqrt (bp y y)
        have h : ‖(QuadraticPreHilbert.mk y : QuadraticPreHilbert X)‖ =
            Real.sqrt ((bp y y + bp y y) / 2) := rfl
        rw [h]
        ring_nf
      rw [hnormy] at hyb
      calc
        ‖T e.val y‖ = |T e.val y| := Real.norm_eq_abs _
        _ ≤ Real.sqrt (bp e.val e.val) * Real.sqrt (bp y y) := hc
        _ ≤ Real.sqrt (bp e.val e.val) * (Real.sqrt ‖bp‖ * ‖y‖) :=
          mul_le_mul_of_nonneg_left hyb (Real.sqrt_nonneg _)
        _ = (Real.sqrt ‖bp‖ * Real.sqrt (bp e.val e.val)) * ‖y‖ := by ring
    have hop := ContinuousLinearMap.opNorm_le_bound (T e.val)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hpoint
    have hnorme : ‖e‖ = Real.sqrt (bp e.val e.val) := by
      change ‖(QuadraticPreHilbert.mk e.val : QuadraticPreHilbert X)‖ =
        Real.sqrt (bp e.val e.val)
      have h : ‖(QuadraticPreHilbert.mk e.val : QuadraticPreHilbert X)‖ =
          Real.sqrt ((bp e.val e.val + bp e.val e.val) / 2) := rfl
      rw [h]
      ring_nf
    calc
      ‖Tlin e‖ ≤ Real.sqrt ‖bp‖ * Real.sqrt (bp e.val e.val) := hop
      _ = Real.sqrt ‖bp‖ * ‖e‖ := by rw [← hnorme]
  let Tpre : E →L[ℝ] (X →L[ℝ] ℝ) :=
    LinearMap.mkContinuous Tlin (Real.sqrt ‖bp‖) hTbound
  have hTpre_norm : ‖Tpre‖ ≤ Real.sqrt ‖bp‖ :=
    LinearMap.mkContinuous_norm_le Tlin (Real.sqrt_nonneg _) hTbound
  have hf : ∀ e f : E, Inseparable e f → Tpre e = Tpre f := by
    intro e f h
    have hnorm0 : ‖e - f‖ = 0 := by
      have hd := h.dist_eq_zero
      rwa [dist_eq_norm] at hd
    have hle : ‖Tpre e - Tpre f‖ ≤ 0 := by
      calc
        ‖Tpre e - Tpre f‖ = ‖Tpre (e - f)‖ := by simp
        _ ≤ ‖Tpre‖ * ‖e - f‖ := ContinuousLinearMap.le_opNorm Tpre (e-f)
        _ ≤ Real.sqrt ‖bp‖ * ‖e - f‖ :=
          mul_le_mul_of_nonneg_right hTpre_norm (norm_nonneg _)
        _ = 0 := by simp [hnorm0]
    exact eq_of_sub_eq_zero (norm_le_zero_iff.mp hle)
  let Tq : SeparationQuotient E →L[ℝ] (X →L[ℝ] ℝ) :=
    SeparationQuotient.liftCLM Tpre hf
  let Q := SeparationQuotient E
  let H := UniformSpace.Completion Q
  let eCompl : Q →L[ℝ] H := UniformSpace.Completion.toComplL
  have hdense : DenseRange eCompl := by
    change DenseRange (UniformSpace.Completion.toComplL (𝕜:=ℝ) (E:=Q))
    simpa [UniformSpace.Completion.coe_toComplL] using
      (UniformSpace.Completion.isDenseInducing_toCompl Q).dense
  have huniform : IsUniformInducing eCompl := by
    change IsUniformInducing (UniformSpace.Completion.toComplL (𝕜:=ℝ) (E:=Q))
    simpa [UniformSpace.Completion.coe_toComplL] using
      (UniformSpace.Completion.isUniformEmbedding_coe Q).isUniformInducing
  let mkQ : E →L[ℝ] Q := SeparationQuotient.mkCLM ℝ E
  let A : X →L[ℝ] H := eCompl.comp (mkQ.comp A0)
  let B : H →L[ℝ] (X →L[ℝ] ℝ) := Tq.extend eCompl
  refine ⟨H, inferInstance, inferInstance, inferInstance, A, B, ?_⟩
  ext x y
  change T x y = (B (A x)) y
  have hAx : A x = eCompl (mkQ (A0 x)) := rfl
  rw [hAx]
  have hB := ContinuousLinearMap.extend_eq Tq hdense huniform (mkQ (A0 x))
  rw [hB]
  have hmk : mkQ (A0 x) = SeparationQuotient.mk (A0 x) := by
    exact SeparationQuotient.mkCLM_apply ℝ E (A0 x)
  rw [hmk]
  change ((SeparationQuotient.liftCLM Tpre hf) (SeparationQuotient.mk (A0 x))) y =
    T x y
  rw [SeparationQuotient.liftCLM_mk]
  simp [Tpre, Tlin, A0, toE]

/- accepted add_to_file helper 5 -/
lemma hilbert_factorization_implies_dominated
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (q : X → ℝ)
    (T : X →L[ℝ] (X →L[ℝ] ℝ))
    (hTq : ∀ x : X, q x = T x x)
    (hfact : ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
        (_ : CompleteSpace H) (A : X →L[ℝ] H) (B : H →L[ℝ] (X →L[ℝ] ℝ)),
      T = B.comp A) :
    ∃ p : X → ℝ,
      (∃ bp : X →L[ℝ] X →L[ℝ] ℝ, ∀ x : X, p x = bp x x) ∧
      (∀ x : X, |q x| ≤ p x) := by
  rcases hfact with ⟨H, instH, instIH, instCH, A, B, hT⟩
  let RieszSymm : StrongDual ℝ H →L[ℝ] H :=
    ((InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv).toContinuousLinearMap
  let C : X →L[ℝ] H := RieszSymm.comp B.flip
  have hC : ∀ x y : X, B (A x) y = inner ℝ (C y) (A x) := by
    intro x y
    have h := InnerProductSpace.toDual_symm_apply (𝕜:=ℝ) (E:=H)
      (x:=A x) (y:=B.flip y)
    change B (A x) y = inner ℝ (RieszSymm (B.flip y)) (A x)
    exact h.symm
  let innerH : H →L[ℝ] H →L[ℝ] ℝ := innerSL ℝ
  let bp : X →L[ℝ] X →L[ℝ] ℝ :=
    (1/2 : ℝ) • (((innerH.comp A).flip.comp A) +
      ((innerH.comp C).flip.comp C))
  refine ⟨fun x => bp x x, ⟨bp, fun x => rfl⟩, ?_⟩
  intro x
  have hq : q x = inner ℝ (C x) (A x) := by
    rw [hTq, hT]
    exact hC x x
  have hnorm : |inner ℝ (C x) (A x)| ≤
      (‖A x‖ ^ 2 + ‖C x‖ ^ 2) / 2 := by
    calc
      |inner ℝ (C x) (A x)| ≤ ‖C x‖ * ‖A x‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖A x‖ ^ 2 + ‖C x‖ ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖C x‖ - ‖A x‖), norm_nonneg (C x), norm_nonneg (A x)]
  have hp : bp x x = (‖A x‖ ^ 2 + ‖C x‖ ^ 2) / 2 := by
    simp [bp]
    change 2⁻¹ * inner ℝ (A x) (A x) + 2⁻¹ * inner ℝ (C x) (C x) =
      (‖A x‖ ^ 2 + ‖C x‖ ^ 2) / 2
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  rw [hq]
  change |inner ℝ (C x) (A x)| ≤ bp x x
  rw [hp]
  exact hnorm

/- verified submission -/
theorem continuous_quadratic_form_delta_semidefinite_iff_hilbert_factorization
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (q : X → ℝ)
    (hq : ∃ b : X →L[ℝ] X →L[ℝ] ℝ, ∀ x : X, q x = b x x)
    (T : X →L[ℝ] (X →L[ℝ] ℝ))
    (hTq : ∀ x : X, q x = T x x)
    (hTsymm : ∀ x y : X, T x y = T y x) :
    ((∃ q₁ q₂ : X → ℝ,
        (∃ b₁ : X →L[ℝ] X →L[ℝ] ℝ, ∀ x : X, q₁ x = b₁ x x) ∧
        (∃ b₂ : X →L[ℝ] X →L[ℝ] ℝ, ∀ x : X, q₂ x = b₂ x x) ∧
        (∀ x : X, 0 ≤ q₁ x) ∧
        (∀ x : X, 0 ≤ q₂ x) ∧
        (∀ x : X, q x = q₁ x - q₂ x)) ↔
      (∃ p : X → ℝ,
        (∃ bp : X →L[ℝ] X →L[ℝ] ℝ, ∀ x : X, p x = bp x x) ∧
        (∀ x : X, |q x| ≤ p x))) ∧
    ((∃ p : X → ℝ,
        (∃ bp : X →L[ℝ] X →L[ℝ] ℝ, ∀ x : X, p x = bp x x) ∧
        (∀ x : X, |q x| ≤ p x)) ↔
      (∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
          (_ : CompleteSpace H) (A : X →L[ℝ] H) (B : H →L[ℝ] (X →L[ℝ] ℝ)),
        T = B.comp A)) := by
  constructor
  · constructor
    · rintro ⟨q₁, q₂, hq₁, hq₂, hq₁pos, hq₂pos, hqdiff⟩
      rcases hq₁ with ⟨b₁, hb₁⟩
      rcases hq₂ with ⟨b₂, hb₂⟩
      refine ⟨fun x => q₁ x + q₂ x, ?_, ?_⟩
      · refine ⟨b₁ + b₂, ?_⟩
        intro x
        simp [hb₁ x, hb₂ x]
      · intro x
        rw [hqdiff x]
        calc
          |q₁ x - q₂ x| ≤ |q₁ x| + |q₂ x| := abs_sub _ _
          _ = q₁ x + q₂ x := by
            rw [abs_of_nonneg (hq₁pos x), abs_of_nonneg (hq₂pos x)]
    · rintro ⟨p, hbp, hdom⟩
      rcases hbp with ⟨bp, hp⟩
      refine ⟨fun x => (p x + q x) / 2, fun x => (p x - q x) / 2, ?_, ?_, ?_, ?_, ?_⟩
      · refine ⟨(1/2 : ℝ) • (bp + T), ?_⟩
        intro x
        simp [hp x, hTq x]
        ring
      · refine ⟨(1/2 : ℝ) • (bp - T), ?_⟩
        intro x
        simp [hp x, hTq x]
        ring
      · intro x
        have hqabs := abs_le.mp (hdom x)
        nlinarith
      · intro x
        have hqabs := abs_le.mp (hdom x)
        nlinarith
      · intro x
        ring
  · constructor
    · rintro ⟨p, ⟨bp, hp⟩, hdom⟩
      exact dominated_implies_hilbert_factorization q T hTq hTsymm p bp hp hdom
    · intro hfact
      exact hilbert_factorization_implies_dominated q T hTq hfact

end Rollout_p1226_continuous_quadratic_form_delta_semidefini

namespace Rollout_p2342_c0singlezero_apply

/- verified submission -/
noncomputable def c0SingleZero {E : Type*} [TopologicalSpace E] [Zero E] (x : E) :
    ZeroAtInftyContinuousMap ℕ E where
  toFun n := if n = 0 then x else 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    apply HasCompactSupport.is_zero_at_infty
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_singleton (x := (0 : ℕ)))
    intro n hn
    by_cases h0 : n = 0
    · exact Set.mem_singleton_iff.mpr h0
    · exfalso
      exact hn (by simp [h0])

@[simp] theorem c0SingleZero_apply {E : Type*} [TopologicalSpace E] [Zero E] (x : E) (n : ℕ) :
    c0SingleZero x n = (if n = 0 then x else 0) := rfl

theorem no_implementing_star_hom
    {A : Type*} [CStarAlgebra A] [Nontrivial A]
    (α : A →⋆ₙₐ[ℂ] A)
    (hα : α 1 = 1)
    (hessential : ∀ a : A,
      (∀ x : (⊥ : NonUnitalStarSubalgebra ℂ A).comap α, a * (x : A) = 0) → a = 0) :
    let I := (⊥ : NonUnitalStarSubalgebra ℂ A).comap α
    letI : ContinuousStar I :=
      ⟨(continuous_star.comp continuous_subtype_val).subtype_mk _⟩
    let B := A × ZeroAtInftyContinuousMap ℕ I
    ¬ ∃ β : B →⋆ₙₐ[ℂ] B, ∀ b b' : B,
      (β b * b').1 = α b.1 * b'.1 ∧
      (↑((β b * b').2 0) : A) = α b.1 * ↑(b'.2 0) ∧
      ∀ n : ℕ, (↑((β b * b').2 (n + 1)) : A) =
        (↑(b.2 n) : A) * ↑(b'.2 (n + 1)) := by
  dsimp only
  intro h
  rcases h with ⟨β, hβ⟩
  letI : ContinuousStar ((⊥ : NonUnitalStarSubalgebra ℂ A).comap α) :=
    ⟨(continuous_star.comp continuous_subtype_val).subtype_mk _⟩
  let I := (⊥ : NonUnitalStarSubalgebra ℂ A).comap α
  let b0 : A × ZeroAtInftyContinuousMap ℕ I := (1, 0)
  let d : I := (β b0).2 0
  have hleft : ∀ x : I, ((d : A) * (x : A)) = (x : A) := by
    intro x
    let bx : A × ZeroAtInftyContinuousMap ℕ I := (0, c0SingleZero x)
    have hx := (hβ b0 bx).2.1
    simpa [b0, bx, d, hα] using hx
  have hd_eq : (d : A) = 1 := by
    have hzero : ∀ x : (⊥ : NonUnitalStarSubalgebra ℂ A).comap α,
        (((d : A) - 1) * (x : A)) = 0 := by
      intro x
      rw [sub_mul, one_mul, hleft x, sub_self]
    exact sub_eq_zero.mp (hessential ((d : A) - 1) hzero)
  have hdα : α (d : A) = 0 := by
    have hmem : α (d : A) ∈ (⊥ : NonUnitalStarSubalgebra ℂ A) :=
      (NonUnitalStarSubalgebra.mem_comap (⊥ : NonUnitalStarSubalgebra ℂ A) α (d : A)).mp d.property
    exact NonUnitalStarAlgebra.mem_bot.mp hmem
  have h10 : (1 : A) = 0 := by
    calc
      (1 : A) = α 1 := hα.symm
      _ = α (d : A) := by rw [hd_eq]
      _ = 0 := hdα
  exact one_ne_zero h10

end Rollout_p2342_c0singlezero_apply

namespace Rollout_p1479_completion_preserves_finite_one_point_exte

/- accepted add_to_file helper 1 -/
lemma completion_diam_eq
    (A : Type*) [MetricSpace A] :
    Metric.diam (Set.univ : Set (UniformSpace.Completion A)) =
      Metric.diam (Set.univ : Set A) := by
  have hclosure : closure (Set.range (UniformSpace.Completion.coe' : A → UniformSpace.Completion A)) = Set.univ :=
    UniformSpace.Completion.denseRange_coe.closure_range
  calc
    Metric.diam (Set.univ : Set (UniformSpace.Completion A))
        = Metric.diam (closure (Set.range (UniformSpace.Completion.coe' : A → UniformSpace.Completion A))) := by
          rw [hclosure]
    _ = Metric.diam (Set.range (UniformSpace.Completion.coe' : A → UniformSpace.Completion A)) :=
          Metric.diam_closure _
    _ = Metric.diam (Set.univ : Set A) :=
          UniformSpace.Completion.coe_isometry.diam_range

lemma dist_le_one_of_diam_one
    {X : Type*} [PseudoMetricSpace X]
    (h : Metric.diam (Set.univ : Set X) = 1) (x y : X) :
    dist x y ≤ 1 := by
  have hed : Metric.ediam (Set.univ : Set X) ≠ ⊤ := by
    intro he
    simp [Metric.diam, he] at h
  exact (Metric.dist_le_diam_of_mem' hed (Set.mem_univ x) (Set.mem_univ y)).trans_eq h

lemma exists_extension_on_range
    {A : Type*} [MetricSpace A]
    (hext : ∀ (F : Set A), F.Finite →
      ∀ f : F → Set.Icc (0 : ℝ) 1,
        (∀ x y : F,
          |(f x : ℝ) - (f y : ℝ)| ≤ dist (x : A) (y : A) ∧
            dist (x : A) (y : A) ≤ (f x : ℝ) + (f y : ℝ)) →
        ∃ z : A, ∀ x : F, dist z (x : A) = (f x : ℝ))
    {ι : Type*} [Finite ι] {a : ι → A} (ha : Function.Injective a)
    (r : ι → Set.Icc (0 : ℝ) 1)
    (hcompat : ∀ i j : ι,
      |(r i : ℝ) - (r j : ℝ)| ≤ dist (a i) (a j) ∧
        dist (a i) (a j) ≤ (r i : ℝ) + (r j : ℝ)) :
    ∃ z : A, ∀ i : ι, dist z (a i) = (r i : ℝ) := by
  classical
  let idx : Set.range a → ι := fun y => Classical.choose y.2
  let rr : Set.range a → Set.Icc (0 : ℝ) 1 := fun y => r (idx y)
  have hidx : ∀ y : Set.range a, a (idx y) = y.1 := by
    intro y
    exact Classical.choose_spec y.2
  obtain ⟨z, hz⟩ := hext (Set.range a) (Set.finite_range a) rr (by
    intro x y
    simpa [rr, idx, hidx x, hidx y] using hcompat (idx x) (idx y))
  refine ⟨z, fun i => ?_⟩
  have hmem : a i ∈ Set.range a := Set.mem_range_self i
  have hz' := hz ⟨a i, hmem⟩
  have hid : idx ⟨a i, hmem⟩ = i := ha (hidx ⟨a i, hmem⟩)
  simpa [rr, hid] using hz'

/- accepted add_to_file helper 2 -/
lemma exists_isometric_approx_fin
    {A : Type*} [MetricSpace A]
    (hext : ∀ (F : Set A), F.Finite →
      ∀ f : F → Set.Icc (0 : ℝ) 1,
        (∀ x y : F,
          |(f x : ℝ) - (f y : ℝ)| ≤ dist (x : A) (y : A) ∧
            dist (x : A) (y : A) ≤ (f x : ℝ) + (f y : ℝ)) →
        ∃ z : A, ∀ x : F, dist z (x : A) = (f x : ℝ))
    (hdiamX : Metric.diam (Set.univ : Set (UniformSpace.Completion A)) = 1) :
    ∀ (n : ℕ) (x : Fin n → UniformSpace.Completion A),
      Function.Injective x → ∀ {ε : ℝ}, 0 < ε →
        ∃ a : Fin n → A,
          (∀ i, dist ((a i : UniformSpace.Completion A)) (x i) < ε) ∧
          (∀ i j, dist (a i) (a j) = dist (x i) (x j)) := by
  intro n
  induction n with
  | zero =>
      intro x hx ε hε
      refine ⟨fun i => i.elim0, ?_, ?_⟩
      · intro i; exact i.elim0
      · intro i; exact i.elim0
  | succ n ih =>
      intro x hx ε hε
      by_cases hn : n = 0
      · subst n
        obtain ⟨b, hb⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt
          (x 0) hε
        refine ⟨fun _ => b, ?_, ?_⟩
        · intro i
          have hi : i = 0 := by
            ext
            omega
          subst i
          rw [dist_comm ((b : UniformSpace.Completion A)) (x 0)]
          exact hb
        · intro i j
          have hi : i = 0 := by
            ext
            omega
          have hj : j = 0 := by
            ext
            omega
          subst i
          subst j
          simp
      · haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
        let D : Fin n → ℝ := fun j => dist (x j.castSucc) (x (Fin.last n))
        obtain ⟨j0, -, hmin⟩ := Finset.exists_min_image Finset.univ D Finset.univ_nonempty
        let m : ℝ := D j0
        have hmpos : 0 < m := by
          dsimp [m, D]
          rw [dist_pos]
          intro hxy
          exact Fin.castSucc_ne_last j0 (hx hxy)
        have hmle : ∀ j : Fin n, m ≤ D j := fun j => hmin j (Finset.mem_univ j)
        have hmle_one : m ≤ 1 := by
          dsimp [m, D]
          exact dist_le_one_of_diam_one hdiamX (x j0.castSucc) (x (Fin.last n))
        let ρ : ℝ := min (m / 2) (ε / 2)
        have hρpos : 0 < ρ := by positivity
        have hρle_mhalf : ρ ≤ m / 2 := min_le_left _ _
        have hρle_ehalf : ρ ≤ ε / 2 := min_le_right _ _
        have hρle_one : ρ ≤ 1 := by linarith
        let c : ℝ := ρ / 4
        have hcpos : 0 < c := by positivity
        have hxres : Function.Injective (fun j : Fin n => x j.castSucc) := by
          intro i j h
          exact Fin.castSucc_injective n (hx h)
        obtain ⟨aold, haold_approx, haold_dist⟩ := ih
          (fun j : Fin n => x j.castSucc) hxres hcpos
        obtain ⟨b, hb⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt
          (x (Fin.last n)) hcpos
        have haold_inj : Function.Injective aold := by
          intro i j h
          have hd : dist (x i.castSucc) (x j.castSucc) = 0 := by
            rw [← haold_dist i j, h, dist_self]
          have hxij : x i.castSucc = x j.castSucc := dist_eq_zero.mp hd
          exact Fin.castSucc_injective n (hx hxij)
        have herr : ∀ j : Fin n,
            |dist (aold j) b - D j| < ρ / 2 := by
          intro j
          have hupper : dist (aold j) b < D j + ρ / 2 := by
            have h1 : dist ((aold j : UniformSpace.Completion A)) ((b : UniformSpace.Completion A)) ≤
                dist ((aold j : UniformSpace.Completion A)) (x j.castSucc) +
                  dist (x j.castSucc) ((b : UniformSpace.Completion A)) :=
              dist_triangle _ _ _
            have h2 : dist (x j.castSucc) ((b : UniformSpace.Completion A)) ≤
                dist (x j.castSucc) (x (Fin.last n)) +
                  dist (x (Fin.last n)) ((b : UniformSpace.Completion A)) :=
              dist_triangle _ _ _
            have hA := haold_approx j
            rw [UniformSpace.Completion.dist_eq (aold j) b] at h1
            dsimp [D, c] at *
            linarith
          have hlower : D j < dist (aold j) b + ρ / 2 := by
            have h1 : dist (x j.castSucc) (x (Fin.last n)) ≤
                dist (x j.castSucc) ((aold j : UniformSpace.Completion A)) +
                  dist ((aold j : UniformSpace.Completion A)) (x (Fin.last n)) :=
              dist_triangle _ _ _
            have h2 : dist ((aold j : UniformSpace.Completion A)) (x (Fin.last n)) ≤
                dist ((aold j : UniformSpace.Completion A)) ((b : UniformSpace.Completion A)) +
                  dist ((b : UniformSpace.Completion A)) (x (Fin.last n)) :=
              dist_triangle _ _ _
            have hA := haold_approx j
            have hA' : dist (x j.castSucc) ((aold j : UniformSpace.Completion A)) < c := by
              rw [dist_comm (x j.castSucc) ((aold j : UniformSpace.Completion A))]
              exact hA
            have hB' : dist ((b : UniformSpace.Completion A)) (x (Fin.last n)) < c := by
              rw [dist_comm ((b : UniformSpace.Completion A)) (x (Fin.last n))]
              exact hb
            rw [UniformSpace.Completion.dist_eq (aold j) b] at h2
            dsimp [D, c] at *
            linarith
          rw [abs_lt]
          constructor <;> linarith
        have hρle_Dhalf : ∀ j : Fin n, ρ ≤ D j / 2 := by
          intro j
          have hmj := hmle j
          linarith
        have hab_pos : ∀ j : Fin n, 0 < dist (aold j) b := by
          intro j
          have hlt := (abs_lt.mp (herr j)).1
          have hDj : 0 < D j := lt_of_lt_of_le hmpos (hmle j)
          have hρD := hρle_Dhalf j
          linarith
        let g : Option (Fin n) → A := fun
          | none => b
          | some j => aold j
        have hg_inj : Function.Injective g := by
          intro p q hpq
          cases p with
          | none =>
              cases q with
              | none => rfl
              | some j =>
                  have h : dist (aold j) b = 0 := by
                    dsimp [g] at hpq
                    rw [← hpq, dist_self]
                  exact False.elim ((ne_of_gt (hab_pos j)) h)
          | some i =>
              cases q with
              | none =>
                  have h : dist (aold i) b = 0 := by
                    dsimp [g] at hpq
                    rw [hpq, dist_self]
                  exact False.elim ((ne_of_gt (hab_pos i)) h)
              | some j =>
                  dsimp [g] at hpq
                  exact congrArg some (haold_inj hpq)
        let r : Option (Fin n) → Set.Icc (0 : ℝ) 1 := fun
          | none => ⟨ρ, ⟨le_of_lt hρpos, hρle_one⟩⟩
          | some j => ⟨D j, ⟨dist_nonneg, dist_le_one_of_diam_one hdiamX _ _⟩⟩
        have hcompat : ∀ p q : Option (Fin n),
            |(r p : ℝ) - (r q : ℝ)| ≤ dist (g p) (g q) ∧
              dist (g p) (g q) ≤ (r p : ℝ) + (r q : ℝ) := by
          intro p q
          cases p with
          | none =>
              cases q with
              | none =>
                  simp [g, r, hρpos.le]
              | some j =>
                  have herr' : |dist b (aold j) - D j| < ρ / 2 := by
                    rw [dist_comm b (aold j)]
                    exact herr j
                  have hlt := abs_lt.mp herr'
                  have hρD := hρle_Dhalf j
                  constructor
                  · rw [abs_sub_le_iff]
                    change ρ - D j ≤ dist b (aold j) ∧ D j - ρ ≤ dist b (aold j)
                    constructor <;> linarith [hlt.1, hlt.2, hρD, hρpos.le,
                      (dist_nonneg : 0 ≤ dist b (aold j))]
                  · change dist b (aold j) ≤ ρ + D j
                    linarith
          | some i =>
              cases q with
              | none =>
                  have hlt := abs_lt.mp (herr i)
                  have hρD := hρle_Dhalf i
                  constructor
                  · rw [abs_sub_le_iff]
                    change D i - ρ ≤ dist (aold i) b ∧ ρ - D i ≤ dist (aold i) b
                    constructor <;> linarith [hlt.1, hlt.2, hρD, hρpos.le,
                      (dist_nonneg : 0 ≤ dist (aold i) b)]
                  · change dist (aold i) b ≤ D i + ρ
                    linarith
              | some j =>
                  constructor
                  · rw [abs_sub_le_iff]
                    change D i - D j ≤ dist (aold i) (aold j) ∧
                      D j - D i ≤ dist (aold i) (aold j)
                    rw [haold_dist i j]
                    constructor
                    · have htri := dist_triangle (x i.castSucc) (x j.castSucc) (x (Fin.last n))
                      dsimp [D] at htri ⊢
                      linarith
                    · have htri := dist_triangle (x j.castSucc) (x i.castSucc) (x (Fin.last n))
                      have htri' : dist (x j.castSucc) (x (Fin.last n)) ≤
                          dist (x i.castSucc) (x j.castSucc) +
                            dist (x i.castSucc) (x (Fin.last n)) := by
                        rw [dist_comm (x j.castSucc) (x i.castSucc)] at htri
                        exact htri
                      dsimp [D] at htri' ⊢
                      linarith
                  · change dist (aold i) (aold j) ≤ D i + D j
                    rw [haold_dist i j]
                    have htri := dist_triangle (x i.castSucc) (x (Fin.last n)) (x j.castSucc)
                    have htri' : dist (x i.castSucc) (x j.castSucc) ≤
                        dist (x i.castSucc) (x (Fin.last n)) +
                          dist (x j.castSucc) (x (Fin.last n)) := by
                      rw [dist_comm (x (Fin.last n)) (x j.castSucc)] at htri
                      exact htri
                    dsimp [D] at htri' ⊢
                    linarith
        obtain ⟨z, hz⟩ := exists_extension_on_range hext hg_inj r hcompat
        let anew : Fin (n + 1) → A := Fin.lastCases z aold
        have hanew_approx : ∀ i : Fin (n + 1),
            dist ((anew i : UniformSpace.Completion A)) (x i) < ε := by
          intro i
          refine Fin.lastCases ?_ ?_ i
          · have hzb : dist z b = ρ := by
              simpa [r] using hz none
            have h1 : dist ((z : UniformSpace.Completion A)) (x (Fin.last n)) ≤
                dist ((z : UniformSpace.Completion A)) ((b : UniformSpace.Completion A)) +
                  dist ((b : UniformSpace.Completion A)) (x (Fin.last n)) :=
              dist_triangle _ _ _
            rw [UniformSpace.Completion.dist_eq z b] at h1
            have hb' : dist ((b : UniformSpace.Completion A)) (x (Fin.last n)) < c := by
              rw [dist_comm ((b : UniformSpace.Completion A)) (x (Fin.last n))]
              exact hb
            have hgoal : dist ((z : UniformSpace.Completion A)) (x (Fin.last n)) < ε := by
              dsimp [c] at *
              linarith
            simpa only [anew, Fin.lastCases_last] using hgoal
          · intro j
            have hA := haold_approx j
            have hgoal : dist ((aold j : UniformSpace.Completion A)) (x j.castSucc) < ε := by
              dsimp [c] at hA
              linarith
            simpa only [anew, Fin.lastCases_castSucc] using hgoal
        have hanew_dist : ∀ i j : Fin (n + 1),
            dist (anew i) (anew j) = dist (x i) (x j) := by
          intro i j
          refine Fin.lastCases ?_ ?_ i
          · refine Fin.lastCases ?_ ?_ j
            · simp only [anew, Fin.lastCases_last, dist_self]
            · intro k
              have hzk : dist z (aold k) = D k := by
                simpa [r] using hz (some k)
              simp only [anew, Fin.lastCases_last, Fin.lastCases_castSucc]
              rw [hzk]
              exact dist_comm (x k.castSucc) (x (Fin.last n))
          · intro k
            refine Fin.lastCases ?_ ?_ j
            · have hzk : dist z (aold k) = D k := by
                simpa [r] using hz (some k)
              simp only [anew, Fin.lastCases_last, Fin.lastCases_castSucc]
              rw [dist_comm (aold k) z, hzk]
            · intro l
              simp only [anew, Fin.lastCases_castSucc]
              exact haold_dist k l
        refine ⟨anew, hanew_approx, hanew_dist⟩

/- accepted add_to_file helper 3 -/
lemma completion_extension_fin
    {A : Type*} [MetricSpace A]
    (hext : ∀ (F : Set A), F.Finite →
      ∀ f : F → Set.Icc (0 : ℝ) 1,
        (∀ x y : F,
          |(f x : ℝ) - (f y : ℝ)| ≤ dist (x : A) (y : A) ∧
            dist (x : A) (y : A) ≤ (f x : ℝ) + (f y : ℝ)) →
        ∃ z : A, ∀ x : F, dist z (x : A) = (f x : ℝ))
    (hdiamX : Metric.diam (Set.univ : Set (UniformSpace.Completion A)) = 1)
    {n : ℕ} (x : Fin n → UniformSpace.Completion A) (hx : Function.Injective x)
    (r : Fin n → Set.Icc (0 : ℝ) 1)
    (hcompat : ∀ i j : Fin n,
      |(r i : ℝ) - (r j : ℝ)| ≤ dist (x i) (x j) ∧
        dist (x i) (x j) ≤ (r i : ℝ) + (r j : ℝ)) :
    ∃ z : UniformSpace.Completion A, ∀ i : Fin n,
      dist z (x i) = (r i : ℝ) := by
  classical
  by_cases hn : n = 0
  · subst n
    let e : (∅ : Set A) → Set.Icc (0 : ℝ) 1 := fun y => ⟨0, by norm_num⟩
    obtain ⟨a, -⟩ := hext ∅ Set.finite_empty e (by
      intro y
      exact False.elim y.2)
    exact ⟨(a : UniformSpace.Completion A), fun i => i.elim0⟩
  · haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    by_cases hzero : ∃ i : Fin n, (r i : ℝ) = 0
    · obtain ⟨i, hi⟩ := hzero
      refine ⟨x i, fun j => ?_⟩
      have hpair := hcompat i j
      have hle : (r j : ℝ) ≤ dist (x i) (x j) := by
        have h := hpair.1
        rw [hi, zero_sub, abs_neg, abs_of_nonneg (r j).2.1] at h
        exact h
      have hge : dist (x i) (x j) ≤ (r j : ℝ) := by
        simpa [hi] using hpair.2
      exact le_antisymm hge hle
    · have hrpos : ∀ i : Fin n, 0 < (r i : ℝ) := by
        intro i
        exact lt_of_le_of_ne (r i).2.1 (by
          intro h
          exact hzero ⟨i, h.symm⟩)
      obtain ⟨i0, hi0⟩ := Finite.exists_min (fun i : Fin n => (r i : ℝ))
      let R : ℝ := r i0
      have hRpos : 0 < R := hrpos i0
      have hRle : ∀ i : Fin n, R ≤ (r i : ℝ) := hi0
      have hRle_one : R ≤ 1 := (r i0).2.2
      let δ : ℕ → ℝ := fun k => R / 2 / 2 ^ k
      have hδpos : ∀ k, 0 < δ k := by
        intro k
        dsimp [δ]
        positivity
      have hδsucc : ∀ k, δ (k + 1) = δ k / 2 := by
        intro k
        dsimp [δ]
        ring_nf
      have hδle_halfR : ∀ k, δ k ≤ R / 2 := by
        intro k
        induction k with
        | zero =>
            dsimp [δ]
            linarith
        | succ k ih =>
            rw [hδsucc]
            linarith
      have hδlt_r : ∀ k i, δ k < (r i : ℝ) := by
        intro k i
        have h1 := hδle_halfR k
        have h2 := hRle i
        have h3 := hrpos i
        linarith
      have hδle_one : ∀ k, δ k ≤ 1 := by
        intro k
        have h1 := hδle_halfR k
        linarith
      let ε : ℕ → ℝ := fun k => δ k / 8
      have hεpos : ∀ k, 0 < ε k := fun k => by positivity
      have hex : ∀ k : ℕ, ∃ a : Fin n → A,
          (∀ i, dist ((a i : UniformSpace.Completion A)) (x i) < ε k) ∧
          (∀ i j, dist (a i) (a j) = dist (x i) (x j)) := by
        intro k
        exact exists_isometric_approx_fin hext hdiamX n x hx (hεpos k)
      let a : ℕ → Fin n → A := fun k => Classical.choose (hex k)
      have ha : ∀ k,
          (∀ i, dist (((a k) i : UniformSpace.Completion A)) (x i) < ε k) ∧
          (∀ i j, dist ((a k) i) ((a k) j) = dist (x i) (x j)) := by
        intro k
        exact Classical.choose_spec (hex k)
      have ha_inj : ∀ k, Function.Injective (a k) := by
        intro k i j h
        have hd : dist (x i) (x j) = 0 := by
          rw [← (ha k).2 i j, h, dist_self]
        exact hx (dist_eq_zero.mp hd)
      have hcompatA : ∀ k i j,
          |(r i : ℝ) - (r j : ℝ)| ≤ dist ((a k) i) ((a k) j) ∧
            dist ((a k) i) ((a k) j) ≤ (r i : ℝ) + (r j : ℝ) := by
        intro k i j
        simpa [(ha k).2 i j] using hcompat i j
      obtain ⟨z0, hz0⟩ := exists_extension_on_range hext (ha_inj 0) r (hcompatA 0)
      have step : ∀ k (z : A), (∀ i, dist z ((a k) i) = (r i : ℝ)) →
          ∃ w : A, dist w z = δ k ∧
            ∀ i, dist w ((a (k + 1)) i) = (r i : ℝ) := by
        intro k z hz
        have herr : ∀ i, |dist z ((a (k + 1)) i) - (r i : ℝ)| < δ k / 4 := by
          intro i
          have hold : dist ((z : UniformSpace.Completion A)) (((a k) i : UniformSpace.Completion A)) =
              (r i : ℝ) := by
            rw [UniformSpace.Completion.dist_eq]
            exact hz i
          have hupper : dist z ((a (k + 1)) i) < (r i : ℝ) + δ k / 4 := by
            have h1 : dist ((z : UniformSpace.Completion A)) (((a (k + 1)) i : UniformSpace.Completion A)) ≤
                dist ((z : UniformSpace.Completion A)) (x i) +
                  dist (x i) (((a (k + 1)) i : UniformSpace.Completion A)) :=
              dist_triangle _ _ _
            have h2 : dist ((z : UniformSpace.Completion A)) (x i) ≤
                dist ((z : UniformSpace.Completion A)) (((a k) i : UniformSpace.Completion A)) +
                  dist (((a k) i : UniformSpace.Completion A)) (x i) :=
              dist_triangle _ _ _
            have hnew' : dist (x i) (((a (k + 1)) i : UniformSpace.Completion A)) < ε (k+1) := by
              rw [dist_comm (x i) (((a (k+1)) i : UniformSpace.Completion A))]
              exact (ha (k+1)).1 i
            have hold' : dist (((a k) i : UniformSpace.Completion A)) (x i) < ε k :=
              (ha k).1 i
            rw [UniformSpace.Completion.dist_eq z ((a (k+1)) i)] at h1
            rw [hold] at h2
            have hs := hδsucc k
            have hδp := hδpos k
            dsimp [ε] at *
            linarith
          have hlower : (r i : ℝ) < dist z ((a (k + 1)) i) + δ k / 4 := by
            have h1 : dist ((z : UniformSpace.Completion A)) (((a k) i : UniformSpace.Completion A)) ≤
                dist ((z : UniformSpace.Completion A)) (x i) +
                  dist (x i) (((a k) i : UniformSpace.Completion A)) :=
              dist_triangle _ _ _
            have h2 : dist ((z : UniformSpace.Completion A)) (x i) ≤
                dist ((z : UniformSpace.Completion A)) (((a (k + 1)) i : UniformSpace.Completion A)) +
                  dist (((a (k + 1)) i : UniformSpace.Completion A)) (x i) :=
              dist_triangle _ _ _
            have hold' : dist (x i) (((a k) i : UniformSpace.Completion A)) < ε k := by
              rw [dist_comm (x i) (((a k) i : UniformSpace.Completion A))]
              exact (ha k).1 i
            have hnew' : dist (((a (k + 1)) i : UniformSpace.Completion A)) (x i) < ε (k+1) :=
              (ha (k+1)).1 i
            rw [hold] at h1
            rw [UniformSpace.Completion.dist_eq z ((a (k+1)) i)] at h2
            have hs := hδsucc k
            have hδp := hδpos k
            dsimp [ε] at *
            linarith
          rw [abs_lt]
          constructor <;> linarith
        have hdistpos : ∀ i, 0 < dist z ((a (k + 1)) i) := by
          intro i
          have hlt := (abs_lt.mp (herr i)).1
          have hδr := hδlt_r k i
          have hδp := hδpos k
          linarith
        let g : Option (Fin n) → A := fun
          | none => z
          | some i => (a (k + 1)) i
        have hg_inj : Function.Injective g := by
          intro p q hpq
          cases p with
          | none =>
              cases q with
              | none => rfl
              | some i =>
                  have h : dist z ((a (k+1)) i) = 0 := by
                    dsimp [g] at hpq
                    rw [← hpq, dist_self]
                  exact False.elim ((ne_of_gt (hdistpos i)) h)
          | some i =>
              cases q with
              | none =>
                  have h : dist z ((a (k+1)) i) = 0 := by
                    dsimp [g] at hpq
                    rw [hpq, dist_self]
                  exact False.elim ((ne_of_gt (hdistpos i)) h)
              | some j =>
                  dsimp [g] at hpq
                  exact congrArg some ((ha_inj (k+1)) hpq)
        let rr : Option (Fin n) → Set.Icc (0 : ℝ) 1 := fun
          | none => ⟨δ k, ⟨(hδpos k).le, hδle_one k⟩⟩
          | some i => r i
        have hcompg : ∀ p q : Option (Fin n),
            |(rr p : ℝ) - (rr q : ℝ)| ≤ dist (g p) (g q) ∧
              dist (g p) (g q) ≤ (rr p : ℝ) + (rr q : ℝ) := by
          intro p q
          cases p with
          | none =>
              cases q with
              | none =>
                  simp [g, rr, (hδpos k).le]
              | some i =>
                  have hlt := abs_lt.mp (herr i)
                  have hδr := hδlt_r k i
                  constructor
                  · rw [abs_sub_le_iff]
                    change δ k - (r i : ℝ) ≤ dist z ((a (k+1)) i) ∧
                      (r i : ℝ) - δ k ≤ dist z ((a (k+1)) i)
                    constructor <;> linarith [hlt.1, hlt.2, hδr,
                      (dist_nonneg : 0 ≤ dist z ((a (k+1)) i))]
                  · change dist z ((a (k+1)) i) ≤ δ k + (r i : ℝ)
                    linarith
          | some i =>
              cases q with
              | none =>
                  have herr' : |dist ((a (k+1)) i) z - (r i : ℝ)| < δ k / 4 := by
                    rw [dist_comm ((a (k+1)) i) z]
                    exact herr i
                  have hlt := abs_lt.mp herr'
                  have hδr := hδlt_r k i
                  constructor
                  · rw [abs_sub_le_iff]
                    change (r i : ℝ) - δ k ≤ dist ((a (k+1)) i) z ∧
                      δ k - (r i : ℝ) ≤ dist ((a (k+1)) i) z
                    constructor <;> linarith [hlt.1, hlt.2, hδr,
                      (dist_nonneg : 0 ≤ dist ((a (k+1)) i) z)]
                  · change dist ((a (k+1)) i) z ≤ (r i : ℝ) + δ k
                    linarith
              | some j =>
                  simpa [g, rr, (ha (k+1)).2 i j] using hcompat i j
        obtain ⟨w, hw⟩ := exists_extension_on_range hext hg_inj rr hcompg
        refine ⟨w, ?_, ?_⟩
        · simpa [rr] using hw none
        · intro i
          simpa [rr] using hw (some i)
      let next : ℕ → A → A := fun k z =>
        if hz : (∀ i, dist z ((a k) i) = (r i : ℝ)) then
          Classical.choose (step k z hz)
        else z
      let zseq : ℕ → A := Nat.rec (motive := fun _ => A) z0 (fun k z => next k z)
      have hzsolves : ∀ k i, dist (zseq k) ((a k) i) = (r i : ℝ) := by
        intro k
        induction k with
        | zero =>
            intro i
            exact hz0 i
        | succ k ih =>
            change ∀ i, dist (next k (zseq k)) ((a (k+1)) i) = (r i : ℝ)
            dsimp [next]
            rw [dif_pos ih]
            exact (Classical.choose_spec (step k (zseq k) ih)).2
      have hzstep : ∀ k, dist (zseq (k + 1)) (zseq k) = δ k := by
        intro k
        change dist (next k (zseq k)) (zseq k) = δ k
        dsimp [next]
        rw [dif_pos (hzsolves k)]
        exact (Classical.choose_spec (step k (zseq k) (hzsolves k))).1
      have hsummableδ : Summable δ := by
        dsimp [δ]
        exact summable_geometric_two' R
      let y : ℕ → UniformSpace.Completion A := fun k => (zseq k : UniformSpace.Completion A)
      have hsummableY : Summable (fun k => dist (y k) (y (k+1))) := by
        have hfun : (fun k => dist (y k) (y (k+1))) = δ := by
          funext k
          calc dist (y k) (y (k+1))
              = dist (zseq k) (zseq (k+1)) := by
                  dsimp [y]
                  exact UniformSpace.Completion.dist_eq _ _
          _ = dist (zseq (k+1)) (zseq k) := dist_comm _ _
          _ = δ k := hzstep k
        rw [hfun]
        exact hsummableδ
      have hcauchy : CauchySeq y := cauchySeq_of_summable_dist hsummableY
      obtain ⟨z, hzlim⟩ := cauchySeq_tendsto_of_complete hcauchy
      refine ⟨z, fun i => ?_⟩
      have hδzero : Filter.Tendsto δ Filter.atTop (nhds 0) :=
        hsummableδ.tendsto_atTop_zero
      have hεzero : Filter.Tendsto ε Filter.atTop (nhds 0) := by
        simpa [ε] using hδzero.div_const 8
      have happrox_tendsto : Filter.Tendsto
          (fun k => (((a k) i : UniformSpace.Completion A))) Filter.atTop (nhds (x i)) := by
        rw [tendsto_iff_dist_tendsto_zero]
        exact squeeze_zero (fun k => dist_nonneg) (fun k => ((ha k).1 i).le) hεzero
      have hdist_tendsto : Filter.Tendsto
          (fun k => dist (y k) (((a k) i : UniformSpace.Completion A)))
          Filter.atTop (nhds (dist z (x i))) :=
        hzlim.dist happrox_tendsto
      have hterm_tendsto : Filter.Tendsto
          (fun k => dist (y k) (((a k) i : UniformSpace.Completion A)))
          Filter.atTop (nhds (r i : ℝ)) := by
        apply Filter.Tendsto.congr' _ tendsto_const_nhds
        exact Filter.Eventually.of_forall (fun k => by
          have heq : dist (y k) (((a k) i : UniformSpace.Completion A)) = (r i : ℝ) := by
            calc dist (y k) (((a k) i : UniformSpace.Completion A))
                = dist (zseq k) ((a k) i) := by
                    dsimp [y]
                    exact UniformSpace.Completion.dist_eq _ _
            _ = (r i : ℝ) := hzsolves k i
          exact heq.symm)
      exact tendsto_nhds_unique hdist_tendsto hterm_tendsto

/- verified submission -/
theorem completion_preserves_finite_one_point_extension
    (A : Type*) [MetricSpace A]
    (hdiam : Metric.diam (Set.univ : Set A) = 1)
    (hext : ∀ (F : Set A), F.Finite →
      ∀ f : F → Set.Icc (0 : ℝ) 1,
        (∀ x y : F,
          |(f x : ℝ) - (f y : ℝ)| ≤ dist (x : A) (y : A) ∧
            dist (x : A) (y : A) ≤ (f x : ℝ) + (f y : ℝ)) →
        ∃ z : A, ∀ x : F, dist z (x : A) = (f x : ℝ)) :
    Metric.diam (Set.univ : Set (UniformSpace.Completion A)) = 1 ∧
      ∀ (F : Set (UniformSpace.Completion A)), F.Finite →
        ∀ f : F → Set.Icc (0 : ℝ) 1,
          (∀ x y : F,
            |(f x : ℝ) - (f y : ℝ)| ≤
                dist (x : UniformSpace.Completion A) (y : UniformSpace.Completion A) ∧
              dist (x : UniformSpace.Completion A) (y : UniformSpace.Completion A) ≤
                (f x : ℝ) + (f y : ℝ)) →
          ∃ z : UniformSpace.Completion A, ∀ x : F,
            dist z (x : UniformSpace.Completion A) = (f x : ℝ) := by
  classical
  have hdiamX : Metric.diam (Set.univ : Set (UniformSpace.Completion A)) = 1 := by
    rw [completion_diam_eq A, hdiam]
  refine ⟨hdiamX, ?_⟩
  intro F hF f hcompat
  letI := hF.fintype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin F
  let x : Fin n → UniformSpace.Completion A := fun i => (e.symm i : UniformSpace.Completion A)
  have hx : Function.Injective x := by
    intro i j h
    apply e.symm.injective
    exact Subtype.ext h
  let r : Fin n → Set.Icc (0 : ℝ) 1 := fun i => f (e.symm i)
  have hcompatFin : ∀ i j : Fin n,
      |(r i : ℝ) - (r j : ℝ)| ≤ dist (x i) (x j) ∧
        dist (x i) (x j) ≤ (r i : ℝ) + (r j : ℝ) := by
    intro i j
    exact hcompat (e.symm i) (e.symm j)
  obtain ⟨z, hz⟩ := completion_extension_fin hext hdiamX x hx r hcompatFin
  refine ⟨z, fun y => ?_⟩
  have hy := hz (e y)
  simpa [x, r] using hy

end Rollout_p1479_completion_preserves_finite_one_point_exte

namespace Rollout_p1994_quantitative_equivalence_of_plumpness_and_

/- accepted add_to_file helper 1 -/
lemma exists_dyadic_level
    {δ B₀ r : ℝ} (m : ℤ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hB₀ : 0 < B₀) (hr : 0 < r)
    (hrR : r ≤ B₀ * δ ^ (m - 1)) :
    ∃ k : ℤ, m ≤ k ∧ B₀ * δ ^ k ≤ r ∧ r ≤ B₀ * δ ^ (k - 1) := by
  let a : ℝ := δ⁻¹
  have ha : 1 < a := by
    dsimp [a]
    exact (one_lt_inv₀ hδ0).2 hδ1
  have hscale0 : 0 < B₀ * δ ^ (m - 1) := by
    positivity
  have hx : 1 ≤ (B₀ * δ ^ (m - 1)) / r := by
    rw [one_le_div hr]
    exact hrR
  obtain ⟨n, hn₁, hn₂⟩ := exists_nat_pow_near hx ha
  refine ⟨m + n, by omega, ?_, ?_⟩
  · have hn₂' := hn₂
    rw [show a ^ (n + 1) = (δ ^ ((n : ℤ) + 1))⁻¹ by
      have hcast : ((n : ℤ) + 1) = (((n + 1 : ℕ) : ℤ)) := by norm_num
      rw [hcast, zpow_natCast]
      simp [a]] at hn₂'
    have hq : 0 < δ ^ ((n : ℤ) + 1) := by positivity
    have hlt : B₀ * δ ^ (m - 1) * δ ^ ((n : ℤ) + 1) < r := by
      have h1 : B₀ * δ ^ (m - 1) < (δ ^ ((n : ℤ) + 1))⁻¹ * r :=
        (div_lt_iff₀ hr).1 hn₂'
      exact (lt_inv_mul_iff₀' hq).1 h1
    have hprod : δ ^ (m - 1) * δ ^ ((n : ℤ) + 1) = δ ^ (m + n) := by
      rw [← zpow_add₀ hδ0.ne']
      congr 1
      omega
    have hlt' : B₀ * δ ^ (m + n) < r := by
      rw [← hprod]
      nlinarith
    exact hlt'.le
  · have hn₁' := hn₁
    rw [show a ^ n = (δ ^ (n : ℤ))⁻¹ by
      simp [a, zpow_natCast]] at hn₁'
    have hq : 0 < δ ^ (n : ℤ) := by positivity
    have hle0 : (δ ^ (n : ℤ))⁻¹ * r ≤ B₀ * δ ^ (m - 1) :=
      (le_div_iff₀ hr).1 hn₁'
    have hle : r ≤ (B₀ * δ ^ (m - 1)) * δ ^ (n : ℤ) :=
      (inv_mul_le_iff₀' hq).1 hle0
    have hprod : δ ^ (m - 1) * δ ^ (n : ℤ) = δ ^ (m + n - 1) := by
      rw [← zpow_add₀ hδ0.ne']
      congr 1
      omega
    rw [show m + n - 1 = m + (n : ℤ) - 1 by omega] at hprod
    rw [← hprod]
    nlinarith

/- verified submission -/
theorem quantitative_equivalence_of_plumpness_and_dyadic_plumpness
    {X : Type*} [MetricSpace X] (E : Set X) :
    (∀ (R b : ℝ), 0 < R → 0 < b → b < 1 →
      (∀ y ∈ E, ∀ r : ℝ, 0 < r → r ≤ R →
        ∃ z : X, Metric.ball z (b * r) ⊆ Metric.ball y r ∩ E) →
      ∀ (δ : ℝ) (m : ℤ) (b₀ B₀ : ℝ),
        0 < δ → δ < 1 → 0 < b₀ → b₀ ≤ B₀ →
        b₀ / B₀ ≤ b → B₀ * δ ^ m ≤ R →
        ∀ y ∈ E, ∀ k : ℤ, m ≤ k →
          ∃ z : X, Metric.ball z (b₀ * δ ^ k) ⊆
            Metric.ball y (B₀ * δ ^ k) ∩ E) ∧
    (∀ (δ : ℝ) (m : ℤ) (b₀ B₀ : ℝ),
      0 < δ → δ < 1 → 0 < b₀ → b₀ ≤ B₀ →
      (∀ y ∈ E, ∀ k : ℤ, m ≤ k →
        ∃ z : X, Metric.ball z (b₀ * δ ^ k) ⊆
          Metric.ball y (B₀ * δ ^ k) ∩ E) →
      ∀ (R b : ℝ), 0 < R → 0 < b → b < 1 →
        b ≤ δ * b₀ / B₀ → R ≤ B₀ * δ ^ (m - 1) →
        ∀ y ∈ E, ∀ r : ℝ, 0 < r → r ≤ R →
          ∃ z : X, Metric.ball z (b * r) ⊆ Metric.ball y r ∩ E) := by
  constructor
  · intro R b hR hb hb1 hplump δ m b₀ B₀ hδ0 hδ1 hb₀ hb₀B₀ hratio hscale
    intro y hy k hk
    have hB₀ : 0 < B₀ := lt_of_lt_of_le hb₀ hb₀B₀
    have hr : 0 < B₀ * δ ^ k := by positivity
    have hpow : δ ^ k ≤ δ ^ m :=
      zpow_le_zpow_right_of_le_one₀ hδ0 hδ1.le hk
    have hrR : B₀ * δ ^ k ≤ R := by
      have hmul : B₀ * δ ^ k ≤ B₀ * δ ^ m :=
        mul_le_mul_of_nonneg_left hpow hB₀.le
      exact hmul.trans hscale
    obtain ⟨z, hz⟩ := hplump y hy (B₀ * δ ^ k) hr hrR
    refine ⟨z, ?_⟩
    have hbB : b₀ ≤ b * B₀ := by
      have := (div_le_iff₀ hB₀).1 hratio
      nlinarith
    have hb_radius : b₀ * δ ^ k ≤ b * (B₀ * δ ^ k) := by
      have hnonneg : 0 ≤ δ ^ k := by positivity
      have hmul := mul_le_mul_of_nonneg_right hbB hnonneg
      nlinarith
    exact (Metric.ball_subset_ball hb_radius).trans hz
  · intro δ m b₀ B₀ hδ0 hδ1 hb₀ hb₀B₀ hdyadic R b hR hb hb1 hbratio hRscale
    intro y hy r hr hrR
    have hB₀ : 0 < B₀ := lt_of_lt_of_le hb₀ hb₀B₀
    have hrscale : r ≤ B₀ * δ ^ (m - 1) := hrR.trans hRscale
    obtain ⟨k, hk, hk_low, hk_high⟩ :=
      exists_dyadic_level m hδ0 hδ1 hB₀ hr hrscale
    obtain ⟨z, hz⟩ := hdyadic y hy k hk
    refine ⟨z, ?_⟩
    have hbB : b * B₀ ≤ δ * b₀ :=
      (le_div_iff₀ hB₀).1 hbratio
    have hb_radius : b * r ≤ b₀ * δ ^ k := by
      have h1 : b * r ≤ b * (B₀ * δ ^ (k - 1)) :=
        mul_le_mul_of_nonneg_left hk_high hb.le
      have hpow : δ * δ ^ (k - 1) = δ ^ k := by
        nth_rewrite 1 [← zpow_one δ]
        rw [← zpow_add₀ hδ0.ne']
        congr 1
        omega
      have hnonneg : 0 ≤ δ ^ (k - 1) := by positivity
      have h2 : b * (B₀ * δ ^ (k - 1)) ≤ δ * b₀ * δ ^ (k - 1) := by
        have hmul := mul_le_mul_of_nonneg_right hbB hnonneg
        nlinarith
      have h3 : δ * b₀ * δ ^ (k - 1) = b₀ * δ ^ k := by
        calc
          δ * b₀ * δ ^ (k - 1) = b₀ * (δ * δ ^ (k - 1)) := by ring
          _ = b₀ * δ ^ k := by rw [hpow]
      exact h1.trans (h2.trans_eq h3)
    intro x hx
    have hxdy := hz ((Metric.ball_subset_ball hb_radius) hx)
    exact ⟨(Metric.ball_subset_ball hk_low) hxdy.1, hxdy.2⟩

end Rollout_p1994_quantitative_equivalence_of_plumpness_and_

namespace Rollout_p1639_relative_commuting_probability_le

/- accepted add_to_file helper 1 -/
open scoped BigOperators

lemma natCard_commute_pairs_eq_sum {M : Type*} [Group M] [Fintype M] (L : Subgroup M) :
    Nat.card {p : L × M // Commute (p.1 : M) p.2} =
      ∑ x : M, Nat.card {l : L // Commute (l : M) x} := by
  classical
  let e : {p : L × M // Commute (p.1 : M) p.2} ≃
      (Σ x : M, {l : L // Commute (l : M) x}) :=
    { toFun := fun p => ⟨p.1.2, ⟨p.1.1, p.2⟩⟩
      invFun := fun q => ⟨⟨q.2.1, q.1⟩, q.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  rw [Nat.card_eq_fintype_card, Fintype.card_congr e, Fintype.card_sigma]
  congr with x
  exact (Nat.card_eq_fintype_card (α := {l : L // Commute (l : M) x})).symm

lemma coset_centralizer_sum_le_commute_pairs
    {G : Type*} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] [Fintype N]
    (I : Subgroup N) [Fintype I] (x : G) :
    ∑ n : N, Nat.card {i : I // Commute ((i : N) : G) (x * (n : G))} ≤
      Nat.card {p : I × N // Commute (p.1 : N) p.2} := by
  classical
  let base : I → N := fun i =>
    if h : ∃ n : N, Commute ((i : N) : G) (x * (n : G)) then
      Classical.choose h
    else 1
  have hbase : ∀ (i : I) {n : N},
      Commute ((i : N) : G) (x * (n : G)) →
      Commute ((i : N) : G) (x * (base i : G)) := by
    intro i n hn
    dsimp [base]
    rw [dif_pos (show ∃ n : N, Commute ((i : N) : G) (x * (n : G)) from ⟨n, hn⟩)]
    exact Classical.choose_spec (show ∃ n : N, Commute ((i : N) : G) (x * (n : G)) from ⟨n, hn⟩)
  have conj_of_comm : ∀ (i : I) {n : N},
      Commute ((i : N) : G) (x * (n : G)) →
      (n : G) * ((i : N) : G) =
        x⁻¹ * ((i : N) : G) * x * (n : G) := by
    intro i n hn
    calc
      (n : G) * ((i : N) : G) = x⁻¹ * ((x * (n : G)) * ((i : N) : G)) := by group
      _ = x⁻¹ * (((i : N) : G) * (x * (n : G))) := by rw [hn.eq]
      _ = x⁻¹ * ((i : N) : G) * x * (n : G) := by group
  have commute_diff : ∀ (i : I) {n : N},
      Commute ((i : N) : G) (x * (n : G)) →
      Commute ((base i)⁻¹ * n : N) (i : N) := by
    intro i n hn
    have hb := hbase i hn
    have hnG := conj_of_comm i hn
    have hbG := conj_of_comm i hb
    have hbG' : (base i : G)⁻¹ * (x⁻¹ * ((i : N) : G) * x) =
        ((i : N) : G) * (base i : G)⁻¹ := by
      calc
        (base i : G)⁻¹ * (x⁻¹ * ((i : N) : G) * x)
            = (base i : G)⁻¹ *
                ((x⁻¹ * ((i : N) : G) * x) * (base i : G)) *
                (base i : G)⁻¹ := by group
        _ = (base i : G)⁻¹ * ((base i : G) * ((i : N) : G)) *
              (base i : G)⁻¹ := by rw [← hbG]
        _ = ((i : N) : G) * (base i : G)⁻¹ := by group
    have hdG : (((base i)⁻¹ * n : N) : G) * ((i : N) : G) =
        ((i : N) : G) * (((base i)⁻¹ * n : N) : G) := by
      calc
        (((base i)⁻¹ * n : N) : G) * ((i : N) : G)
            = (base i : G)⁻¹ * ((n : G) * ((i : N) : G)) := by
              simp; group
        _ = (base i : G)⁻¹ *
              (x⁻¹ * ((i : N) : G) * x * (n : G)) := by rw [hnG]
        _ = ((base i : G)⁻¹ * (x⁻¹ * ((i : N) : G) * x)) * (n : G) := by group
        _ = (((i : N) : G) * (base i : G)⁻¹) * (n : G) := by rw [hbG']
        _ = ((i : N) : G) * (((base i)⁻¹ * n : N) : G) := by
              simp; group
    show ((base i)⁻¹ * n : N) * (i : N) = (i : N) * ((base i)⁻¹ * n : N)
    exact Subtype.ext hdG
  let F : (Σ n : N, {i : I // Commute ((i : N) : G) (x * (n : G))}) →
      {p : I × N // Commute (p.1 : N) p.2} :=
    fun q => ⟨⟨q.2.1, (base q.2.1)⁻¹ * q.1⟩, (commute_diff q.2.1 q.2.2).symm⟩
  have hF : Function.Injective F := by
    intro a b hab
    rcases a with ⟨n, i, hi⟩
    rcases b with ⟨m, j, hj⟩
    have hp : ((i, (base i)⁻¹ * n) : I × N) =
        (j, (base j)⁻¹ * m) := congrArg Subtype.val hab
    have hij : i = j := congrArg Prod.fst hp
    subst j
    have hnm : n = m := mul_left_cancel (congrArg Prod.snd hp)
    subst m
    rfl
  calc
    ∑ n : N, Nat.card {i : I // Commute ((i : N) : G) (x * (n : G))}
        = Nat.card (Σ n : N, {i : I // Commute ((i : N) : G) (x * (n : G))}) := by
          rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
          congr with n
          exact Nat.card_eq_fintype_card (α := {i : I // Commute ((i : N) : G) (x * (n : G))})
    _ ≤ Nat.card {p : I × N // Commute (p.1 : N) p.2} := by
          rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
          exact Fintype.card_le_of_injective F hF

/- accepted add_to_file helper 2 -/
lemma centralizer_card_le_map_mul_comap
    {G Q : Type*} [Group G] [Group Q] [Fintype G] [Fintype Q]
    (f : G →* Q) (K : Subgroup G) [Fintype K]
    [Fintype (K.map f)] [Fintype (K.comap f.ker.subtype)] (x : G) :
    Nat.card {k : K // Commute (k : G) x} ≤
      Nat.card {u : K.map f // Commute (u : Q) (f x)} *
        Nat.card {i : K.comap f.ker.subtype // Commute ((i : f.ker) : G) x} := by
  classical
  let A := {k : K // Commute (k : G) x}
  let B := {u : K.map f // Commute (u : Q) (f x)}
  let I := {i : K.comap f.ker.subtype // Commute ((i : f.ker) : G) x}
  let im : A → B := fun a =>
    ⟨⟨f (a.1 : G), Subgroup.mem_map_of_mem f a.1.2⟩, a.2.map f⟩
  let base : B → A := fun b =>
    if h : ∃ a : A, im a = b then
      Classical.choose h
    else ⟨1, by simp⟩
  have hbase : ∀ (b : B), (∃ a : A, im a = b) →
      im (base b) = b ∧ Commute ((base b : K) : G) x := by
    intro b hb
    dsimp [base]
    rw [dif_pos hb]
    exact ⟨Classical.choose_spec hb, (Classical.choose hb).2⟩
  let dfun : A → f.ker := fun a =>
    ⟨(a.1 : G) * ((base (im a) : K) : G)⁻¹, by
      obtain ⟨him, _⟩ := hbase (im a) ⟨a, rfl⟩
      rw [MonoidHom.mem_ker]
      have himv : f ((base (im a) : K) : G) = f (a.1 : G) := by
        have := congrArg (fun z : B => (z.1 : Q)) him
        simpa [im] using this
      simp [map_mul, map_inv, himv]⟩
  let jfun : A → K.comap f.ker.subtype := fun a =>
    ⟨dfun a, by
      change ((dfun a : f.ker) : G) ∈ K
      dsimp [dfun]
      exact K.mul_mem a.1.2 (K.inv_mem (base (im a)).1.2)⟩
  let F : A → B × I := fun a =>
    ⟨im a, ⟨jfun a, by
      obtain ⟨_, hcomm⟩ := hbase (im a) ⟨a, rfl⟩
      exact a.2.mul_left ((hcomm.symm.inv_right).symm)⟩⟩
  have hF : Function.Injective F := by
    intro a b hab
    have him : im a = im b := congrArg Prod.fst hab
    have hbaseeq : base (im a) = base (im b) := congrArg base him
    have hival : jfun a = jfun b := by
      have := congrArg Subtype.val (congrArg Prod.snd hab)
      simpa [F] using this
    have hd : ((dfun a : f.ker) : G) = ((dfun b : f.ker) : G) := by
      have := congrArg (fun z : K.comap f.ker.subtype => ((z : f.ker) : G)) hival
      simpa [jfun] using this
    have hmul :
        (a.1 : G) * ((base (im a) : K) : G)⁻¹ =
          (b.1 : G) * ((base (im b) : K) : G)⁻¹ := by
      simpa [dfun] using hd
    have hG : (a.1 : G) = (b.1 : G) := by
      calc
        (a.1 : G) = ((a.1 : G) * ((base (im a) : K) : G)⁻¹) *
            ((base (im a) : K) : G) := by group
        _ = ((b.1 : G) * ((base (im b) : K) : G)⁻¹) *
              ((base (im a) : K) : G) := by rw [hmul]
        _ = ((b.1 : G) * ((base (im b) : K) : G)⁻¹) *
              ((base (im b) : K) : G) := by rw [hbaseeq]
        _ = (b.1 : G) := by group
    apply Subtype.ext
    exact Subtype.ext hG
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  calc
    Fintype.card A ≤ Fintype.card (B × I) := Fintype.card_le_of_injective F hF
    _ = Fintype.card B * Fintype.card I := Fintype.card_prod B I

/- accepted add_to_file helper 3 -/
lemma commute_pairs_card_le_quotient_mul_comap
    {G : Type*} [Group G] [Fintype G]
    (N K : Subgroup G) [N.Normal] [Fintype (G ⧸ N)] :
    let π : G →* G ⧸ N := QuotientGroup.mk' N
    let Kbar : Subgroup (G ⧸ N) := K.map π
    Nat.card {p : K × G // Commute (p.1 : G) p.2} ≤
      Nat.card {p : Kbar × (G ⧸ N) // Commute (p.1 : G ⧸ N) p.2} *
        Nat.card {p : (K.comap N.subtype) × N // Commute (p.1 : N) p.2} := by
  classical
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  let Kbar : Subgroup (G ⧸ N) := K.map π
  let I : Subgroup N := K.comap N.subtype
  let cA : G → ℕ := fun x => Nat.card {k : K // Commute (k : G) x}
  let cB : G ⧸ N → ℕ := fun q =>
    Nat.card {u : Kbar // Commute (u : G ⧸ N) q}
  let cI : G → ℕ := fun x =>
    Nat.card {i : I // Commute ((i : N) : G) x}
  have hpoint : ∀ x : G, cA x ≤ cB (π x) * cI x := by
    intro x
    have h := centralizer_card_le_map_mul_comap π K x
    rw [show π.ker = N by simp [π, QuotientGroup.ker_mk']] at h
    exact h
  let lift : G ⧸ N → G := fun q => Classical.choose (QuotientGroup.mk'_surjective N q)
  have hlift : ∀ q : G ⧸ N, π (lift q) = q :=
    fun q => Classical.choose_spec (QuotientGroup.mk'_surjective N q)
  let efib : ∀ q : G ⧸ N, {x : G // π x = q} ≃ N := fun q =>
    { toFun := fun x =>
        ⟨(lift q)⁻¹ * (x : G), by
          rw [← QuotientGroup.eq_one_iff (N := N)]
          change π ((lift q)⁻¹ * (x : G)) = 1
          simp [map_mul, map_inv, hlift q, x.property]⟩
      invFun := fun n =>
        ⟨lift q * (n : G), by
          simp [π, map_mul, hlift q]⟩
      left_inv := fun x => by
        apply Subtype.ext
        group
      right_inv := fun n => by
        apply Subtype.ext
        group }
  have hfiber_sum : ∀ q : G ⧸ N,
      (∑ z : {x : G // π x = q}, cI (z : G)) =
        ∑ n : N, cI (lift q * (n : G)) := by
    intro q
    exact (Fintype.sum_equiv (efib q).symm
      (fun n : N => cI (lift q * (n : G)))
      (fun z : {x : G // π x = q} => cI (z : G))
      (fun n => rfl)).symm
  have hcoset : ∀ q : G ⧸ N,
      (∑ z : {x : G // π x = q}, cI (z : G)) ≤
        Nat.card {p : I × N // Commute (p.1 : N) p.2} := by
    intro q
    rw [hfiber_sum q]
    exact coset_centralizer_sum_le_commute_pairs N I (lift q)
  calc
    Nat.card {p : K × G // Commute (p.1 : G) p.2}
        = ∑ x : G, cA x := natCard_commute_pairs_eq_sum K
    _ ≤ ∑ x : G, cB (π x) * cI x := by
          exact Finset.sum_le_sum (fun x _ => hpoint x)
    _ = ∑ q : G ⧸ N, ∑ z : {x : G // π x = q}, cB (π (z : G)) * cI (z : G) := by
          exact (Fintype.sum_fiberwise π (fun x : G => cB (π x) * cI x)).symm
    _ = ∑ q : G ⧸ N, ∑ z : {x : G // π x = q}, cB q * cI (z : G) := by
          congr with q
          congr with z
          rw [z.property]
    _ = ∑ q : G ⧸ N, cB q * (∑ z : {x : G // π x = q}, cI (z : G)) := by
          congr with q
          rw [Finset.mul_sum]
    _ ≤ ∑ q : G ⧸ N, cB q *
          Nat.card {p : I × N // Commute (p.1 : N) p.2} := by
          exact Finset.sum_le_sum (fun q _ => mul_le_mul_left' (hcoset q) (cB q))
    _ = (∑ q : G ⧸ N, cB q) *
          Nat.card {p : I × N // Commute (p.1 : N) p.2} := by
          rw [Finset.sum_mul]
    _ = Nat.card {p : Kbar × (G ⧸ N) // Commute (p.1 : G ⧸ N) p.2} *
          Nat.card {p : I × N // Commute (p.1 : N) p.2} := by
          rw [natCard_commute_pairs_eq_sum Kbar]

/- accepted add_to_file helper 4 -/
lemma card_comap_mul_card_map_quotient
    {G : Type*} [Group G]
    (N K : Subgroup G) [N.Normal] :
    let π : G →* G ⧸ N := QuotientGroup.mk' N
    Nat.card (K.comap N.subtype) * Nat.card (K.map π) = Nat.card K := by
  classical
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  let I : Subgroup N := K.comap N.subtype
  let J : Subgroup K := N.subgroupOf K
  have hrel : N.relIndex K = Nat.card (K.map π) := by
    have h := Subgroup.relIndex_ker K π
    rw [show π.ker = N by simp [π, QuotientGroup.ker_mk']] at h
    exact h
  have hIeq : Nat.card I = Nat.card J := by
    let e : I ≃ J :=
      { toFun := fun i => ⟨⟨(i.1 : G), i.2⟩, i.1.2⟩
        invFun := fun j => ⟨⟨(j.1 : G), j.2⟩, j.1.2⟩
        left_inv := fun i => rfl
        right_inv := fun j => rfl }
    exact Nat.card_congr e
  have hJ : Nat.card J * J.index = Nat.card K := Subgroup.card_mul_index J
  calc
    Nat.card I * Nat.card (K.map π) = Nat.card J * N.relIndex K := by
      rw [hIeq, hrel]
    _ = Nat.card J * J.index := rfl
    _ = Nat.card K := hJ

/- verified submission -/
theorem relative_commuting_probability_le
    {G : Type*} [Group G] [Finite G]
    (N K : Subgroup G) [N.Normal] :
    let π : G →* G ⧸ N := QuotientGroup.mk' N
    let Kbar : Subgroup (G ⧸ N) := K.map π
    (Nat.card {p : K × G // Commute (p.1 : G) p.2} : ℚ) /
        ((Nat.card K : ℚ) * (Nat.card G : ℚ)) ≤
      ((Nat.card {p : Kbar × (G ⧸ N) // Commute (p.1 : G ⧸ N) p.2} : ℚ) /
          ((Nat.card Kbar : ℚ) * (Nat.card (G ⧸ N) : ℚ))) *
        ((Nat.card {p : (K.comap N.subtype) × N // Commute (p.1 : N) p.2} : ℚ) /
          ((Nat.card (K.comap N.subtype) : ℚ) * (Nat.card N : ℚ))) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (G ⧸ N) := Fintype.ofFinite (G ⧸ N)
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  let Kbar : Subgroup (G ⧸ N) := K.map π
  let I : Subgroup N := K.comap N.subtype
  let A : ℕ := Nat.card {p : K × G // Commute (p.1 : G) p.2}
  let B : ℕ := Nat.card {p : Kbar × (G ⧸ N) // Commute (p.1 : G ⧸ N) p.2}
  let C : ℕ := Nat.card {p : I × N // Commute (p.1 : N) p.2}
  have hnat : A ≤ B * C := by
    simpa [A, B, C, π, Kbar, I] using
      commute_pairs_card_le_quotient_mul_comap N K
  have hK : Nat.card I * Nat.card Kbar = Nat.card K := by
    simpa [I, Kbar, π] using card_comap_mul_card_map_quotient N K
  have hG : Nat.card (G ⧸ N) * Nat.card N = Nat.card G :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup N).symm
  have hden : (Nat.card K : ℚ) * (Nat.card G : ℚ) =
      ((Nat.card Kbar : ℚ) * (Nat.card (G ⧸ N) : ℚ)) *
        ((Nat.card I : ℚ) * (Nat.card N : ℚ)) := by
    have hdenNat : Nat.card K * Nat.card G =
        (Nat.card Kbar * Nat.card (G ⧸ N)) * (Nat.card I * Nat.card N) := by
      rw [← hK, ← hG]
      ring
    exact_mod_cast hdenNat
  have hnum : (A : ℚ) ≤ ((B * C : ℕ) : ℚ) := by
    exact_mod_cast hnat
  have hnonneg : 0 ≤ (Nat.card K : ℚ) * (Nat.card G : ℚ) := by
    positivity
  have hfactor : ((B : ℚ) /
        ((Nat.card Kbar : ℚ) * (Nat.card (G ⧸ N) : ℚ))) *
      ((C : ℚ) / ((Nat.card I : ℚ) * (Nat.card N : ℚ))) =
      ((B * C : ℕ) : ℚ) / ((Nat.card K : ℚ) * (Nat.card G : ℚ)) := by
    rw [div_mul_div_comm]
    have hnumcast : (B : ℚ) * (C : ℚ) = ((B * C : ℕ) : ℚ) := by
      norm_num
    have hdencast : ((Nat.card Kbar : ℚ) * (Nat.card (G ⧸ N) : ℚ)) *
        ((Nat.card I : ℚ) * (Nat.card N : ℚ)) =
        (Nat.card K : ℚ) * (Nat.card G : ℚ) := hden.symm
    rw [hnumcast, hdencast]
  calc
    (A : ℚ) / ((Nat.card K : ℚ) * (Nat.card G : ℚ)) ≤
        ((B * C : ℕ) : ℚ) / ((Nat.card K : ℚ) * (Nat.card G : ℚ)) :=
      div_le_div_of_nonneg_right hnum hnonneg
    _ = ((B : ℚ) /
          ((Nat.card Kbar : ℚ) * (Nat.card (G ⧸ N) : ℚ))) *
        ((C : ℚ) / ((Nat.card I : ℚ) * (Nat.card N : ℚ))) := hfactor.symm
    _ = ((Nat.card {p : Kbar × (G ⧸ N) // Commute (p.1 : G ⧸ N) p.2} : ℚ) /
          ((Nat.card Kbar : ℚ) * (Nat.card (G ⧸ N) : ℚ))) *
        ((Nat.card {p : (K.comap N.subtype) × N // Commute (p.1 : N) p.2} : ℚ) /
          ((Nat.card (K.comap N.subtype) : ℚ) * (Nat.card N : ℚ))) := rfl

end Rollout_p1639_relative_commuting_probability_le

namespace Rollout_p0332_weighted_pointwise_inequality_on_circle

/- accepted add_to_file helper 1 -/

lemma sqrt_integral_sin_sq_half_le_pi_abs_sin {y : ℝ} (hy0 : 0 ≤ y) (hyπ : y ≤ Real.pi) :
    Real.sqrt (∫ t in (0:ℝ)..y, Real.sin (t / 2) ^ 2) ≤
      Real.pi * |Real.sin (y / 2)| := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have hpt : ∀ t ∈ Set.Icc 0 y, Real.sin (t / 2) ^ 2 ≤ (t / 2) ^ 2 := by
      intro t ht
      exact Real.sin_sq_le_sq
    have hsint : IntervalIntegrable (fun t : ℝ => Real.sin (t / 2) ^ 2) MeasureTheory.volume 0 y := by
      exact (Real.continuous_sin.comp (continuous_id.div_const 2)).pow 2 |>.intervalIntegrable 0 y
    have htint : IntervalIntegrable (fun t : ℝ => (t / 2) ^ 2) MeasureTheory.volume 0 y := by
      exact (continuous_id.div_const 2).pow 2 |>.intervalIntegrable 0 y
    have hA : ∫ t in (0:ℝ)..y, Real.sin (t / 2) ^ 2 ≤ ∫ t in (0:ℝ)..y, (t / 2) ^ 2 :=
      intervalIntegral.integral_mono_on hy0 hsint htint hpt
    have hcalc : ∫ t in (0:ℝ)..y, (t / 2) ^ 2 = y ^ 3 / 12 := by
      have hcongr : Set.EqOn (fun t : ℝ => (t / 2) ^ 2) (fun t => (1 / 4 : ℝ) * t ^ 2) (Set.uIcc 0 y) := by
        intro t ht
        ring
      calc
        ∫ t in (0:ℝ)..y, (t / 2) ^ 2 = ∫ t in (0:ℝ)..y, (1 / 4 : ℝ) * t ^ 2 :=
          intervalIntegral.integral_congr hcongr
        _ = (1 / 4 : ℝ) * ∫ t in (0:ℝ)..y, t ^ 2 := by
          rw [intervalIntegral.integral_const_mul]
        _ = y ^ 3 / 12 := by
          rw [integral_pow]
          ring
    have hjordan0 : (2 / Real.pi) * |y / 2| ≤ |Real.sin (y / 2)| := by
      apply Real.mul_abs_le_abs_sin
      rw [abs_of_nonneg (by positivity : 0 ≤ y / 2)]
      nlinarith [Real.pi_pos]
    have hpi_lower : y ≤ Real.pi * |Real.sin (y / 2)| := by
      have habs : |y / 2| = y / 2 := abs_of_nonneg (by positivity)
      rw [habs] at hjordan0
      have hpi : 0 < Real.pi := Real.pi_pos
      have hmul := mul_le_mul_of_nonneg_left hjordan0 (le_of_lt hpi)
      field_simp at hmul ⊢
      nlinarith
    have hy_le_twelve : y ≤ 12 := by
      nlinarith [Real.pi_lt_four, hyπ]
    calc
      ∫ t in (0:ℝ)..y, Real.sin (t / 2) ^ 2 ≤ y ^ 3 / 12 := by
        rw [hcalc] at hA
        exact hA
      _ ≤ y ^ 2 := by
        nlinarith [sq_nonneg y, hy0, hy_le_twelve]
      _ ≤ (Real.pi * |Real.sin (y / 2)|) ^ 2 := by
        have hnonneg2 : 0 ≤ y := hy0
        nlinarith [mul_self_le_mul_self hnonneg2 hpi_lower]

lemma interval_deriv_norm_le_sqrt_weighted_mul_sqrt_sin_sq {f : ℝ → ℝ} {a b : ℝ}
    (hAC : AbsolutelyContinuousOnInterval f (-Real.pi) Real.pi)
    (hW : MeasureTheory.IntegrableOn
      (fun t : ℝ => |deriv f t| ^ 2 / Real.sin (t / 2) ^ 2)
      (Set.Icc (-Real.pi) Real.pi))
    (hab : a ≤ b) (ha : -Real.pi ≤ a) (hb : b ≤ Real.pi) :
    |∫ t in a..b, deriv f t| ≤
      Real.sqrt (∫ t in Set.Icc (-Real.pi) Real.pi,
        |deriv f t| ^ 2 / Real.sin (t / 2) ^ 2) *
      Real.sqrt (∫ t in a..b, Real.sin (t / 2) ^ 2) := by
  let w : ℝ → ℝ := fun t => |deriv f t| ^ 2 / Real.sin (t / 2) ^ 2
  let v : ℝ → ℝ := fun t => deriv f t / Real.sin (t / 2)
  let s : Set ℝ := Set.Ioc a b
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict s
  let A : ℝ := ∫ t in a..b, Real.sin (t / 2) ^ 2
  let I : ℝ := ∫ t in Set.Icc (-Real.pi) Real.pi, w t
  have hπ : -Real.pi ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hsub : Set.uIcc a b ⊆ Set.uIcc (-Real.pi) Real.pi := by
    rw [Set.uIcc_of_le hab, Set.uIcc_of_le hπ]
    exact Set.Icc_subset_Icc ha hb
  have hACab : AbsolutelyContinuousOnInterval f a b := hAC.mono hsub
  have hderab : IntervalIntegrable (deriv f) MeasureTheory.volume a b :=
    hACab.intervalIntegrable_deriv
  have hnorm : |∫ t in a..b, deriv f t| ≤ ∫ t in a..b, |deriv f t| := by
    simpa [Real.norm_eq_abs] using
      (intervalIntegral.norm_integral_le_integral_norm (μ := MeasureTheory.volume)
        (f := fun t : ℝ => deriv f t) hab)
  have hderAES : MeasureTheory.AEStronglyMeasurable (deriv f) μ := by
    simpa [s, μ] using hderab.aestronglyMeasurable
  have hsinCont : Continuous fun t : ℝ => Real.sin (t / 2) :=
    Real.continuous_sin.comp (continuous_id.div_const 2)
  have hsinAES : MeasureTheory.AEStronglyMeasurable (fun t : ℝ => Real.sin (t / 2)) μ :=
    hsinCont.aestronglyMeasurable
  have hvAES : MeasureTheory.AEStronglyMeasurable v μ := by
    simpa [v] using hderAES.div₀ hsinAES
  have hIoc_subset : Set.Ioc a b ⊆ Set.Icc (-Real.pi) Real.pi := by
    intro t ht
    constructor
    · exact le_trans ha (le_of_lt ht.1)
    · exact le_trans ht.2 hb
  have hWsub : MeasureTheory.IntegrableOn w (Set.Ioc a b) := by
    simpa [w] using hW.mono_set hIoc_subset
  have hwsq (d q : ℝ) : |d| ^ 2 / q ^ 2 = (d / q) ^ 2 := by
    by_cases hq : q = 0
    · simp [hq]
    · field_simp [hq]
      rw [sq_abs]
  have hvnormsq (d q : ℝ) : ‖d / q‖ ^ (2 : ℝ) = |d| ^ 2 / q ^ 2 := by
    calc
      ‖d / q‖ ^ (2 : ℝ) = ‖d / q‖ ^ 2 := by norm_num
      _ = |d| ^ 2 / q ^ 2 := by
        rw [Real.norm_eq_abs, abs_div, div_pow]
        simp [sq_abs]
  have hv2int : MeasureTheory.Integrable (fun t => v t ^ 2) μ := by
    have hEqOn : Set.EqOn w (fun t => v t ^ 2) (Set.Ioc a b) := by
      intro t ht
      simp only [w, v]
      exact hwsq (deriv f t) (Real.sin (t / 2))
    have hOn : MeasureTheory.IntegrableOn (fun t => v t ^ 2) (Set.Ioc a b) :=
      hWsub.congr_fun hEqOn measurableSet_Ioc
    simpa [μ, s] using hOn.integrable
  have hvMem : MeasureTheory.MemLp v 2 μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq hvAES).2 hv2int
  have hvMem' : MeasureTheory.MemLp v (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hvMem
  have hgMem0 : MeasureTheory.MemLp (fun t : ℝ => Real.sin (t / 2)) 2 μ := by
    apply MeasureTheory.MemLp.of_bound hsinAES 1
    filter_upwards with t
    rw [Real.norm_eq_abs]
    exact Real.abs_sin_le_one _
  have hgMem : MeasureTheory.MemLp (fun t : ℝ => Real.sin (t / 2)) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hgMem0
  have hholder := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq (μ := μ)
    (f := v) (g := fun t : ℝ => Real.sin (t / 2)) (p := (2 : ℝ)) (q := (2 : ℝ))
    (by exact ⟨by norm_num, by norm_num, by norm_num⟩) hvMem' hgMem
  have hprod_ae : (fun t : ℝ => ‖v t‖ * ‖Real.sin (t / 2)‖) =ᵐ[μ]
      fun t => ‖deriv f t‖ := by
    filter_upwards [MeasureTheory.Measure.ae_ne μ 0,
      MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t htne ht
    have ht_lower : -Real.pi < t := lt_of_le_of_lt ha ht.1
    have hsinne : Real.sin (t / 2) ≠ 0 := by
      intro hzero
      have hlow : -Real.pi < t / 2 := by nlinarith [ht_lower, Real.pi_pos]
      have hhigh : t / 2 < Real.pi := by nlinarith [ht.2, hb, Real.pi_pos]
      have htzero : t = 0 := by
        have hhalf : t / 2 = 0 := (Real.sin_eq_zero_iff_of_lt_of_lt hlow hhigh).mp hzero
        linarith
      exact htne htzero
    simp only [v]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, ← abs_mul,
      div_mul_cancel₀ _ hsinne]
  have hprodint : (∫ t, ‖v t‖ * ‖Real.sin (t / 2)‖ ∂μ) =
      ∫ t in a..b, |deriv f t| := by
    calc
      (∫ t, ‖v t‖ * ‖Real.sin (t / 2)‖ ∂μ) = ∫ t, ‖deriv f t‖ ∂μ :=
        MeasureTheory.integral_congr_ae hprod_ae
      _ = ∫ t in Set.Ioc a b, |deriv f t| := by
        simp [μ, s, Real.norm_eq_abs]
      _ = ∫ t in a..b, |deriv f t| := by
        rw [← intervalIntegral.integral_of_le hab]
  have hfirst_int : (∫ t, ‖v t‖ ^ (2 : ℝ) ∂μ) ≤ I := by
    have hnonneg : 0 ≤ᵐ[MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi)] w := by
      filter_upwards with t
      simp [w]
      positivity
    have hmono : (∫ t in Set.Ioc a b, w t) ≤ I := by
      unfold I w
      exact MeasureTheory.setIntegral_mono_set hW hnonneg
        (show Set.Ioc a b ≤ᵐ[MeasureTheory.volume] Set.Icc (-Real.pi) Real.pi from
          Filter.Eventually.of_forall hIoc_subset)
    have hEqOn : Set.EqOn (fun t => ‖v t‖ ^ (2 : ℝ)) w (Set.Ioc a b) := by
      intro t ht
      simp only [w, v]
      exact hvnormsq (deriv f t) (Real.sin (t / 2))
    calc
      (∫ t, ‖v t‖ ^ (2 : ℝ) ∂μ) = ∫ t in Set.Ioc a b, w t := by
        rw [show (∫ t, ‖v t‖ ^ (2 : ℝ) ∂μ) = ∫ t in Set.Ioc a b, ‖v t‖ ^ (2 : ℝ) by rfl]
        exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hEqOn
      _ ≤ I := hmono
  have hfactor1 : (∫ t, ‖v t‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤ Real.sqrt I := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt hfirst_int
  have hsecond_int : (∫ t, ‖Real.sin (t / 2)‖ ^ (2 : ℝ) ∂μ) = A := by
    calc
      (∫ t, ‖Real.sin (t / 2)‖ ^ (2 : ℝ) ∂μ)
          = ∫ t in Set.Ioc a b, Real.sin (t / 2) ^ 2 := by
            rw [show (∫ t, ‖Real.sin (t / 2)‖ ^ (2 : ℝ) ∂μ) =
              ∫ t in Set.Ioc a b, ‖Real.sin (t / 2)‖ ^ (2 : ℝ) by rfl]
            apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
            intro t ht
            change ‖Real.sin (t / 2)‖ ^ 2 = Real.sin (t / 2) ^ 2
            rw [Real.norm_eq_abs]
            simp [sq_abs]
      _ = A := by
        simp only [A]
        rw [← intervalIntegral.integral_of_le hab]
  have hfactor2 : (∫ t, ‖Real.sin (t / 2)‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) ≤ Real.sqrt A := by
    rw [hsecond_int, ← Real.sqrt_eq_rpow]
  have hfactor2_nonneg : 0 ≤ (∫ t, ‖Real.sin (t / 2)‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    positivity
  calc
    |∫ t in a..b, deriv f t| ≤ ∫ t in a..b, |deriv f t| := hnorm
    _ = ∫ t, ‖v t‖ * ‖Real.sin (t / 2)‖ ∂μ := hprodint.symm
    _ ≤ (∫ t, ‖v t‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (∫ t, ‖Real.sin (t / 2)‖ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hholder
    _ ≤ Real.sqrt I * Real.sqrt A :=
      mul_le_mul hfactor1 hfactor2 hfactor2_nonneg (Real.sqrt_nonneg I)
    _ = Real.sqrt (∫ t in Set.Icc (-Real.pi) Real.pi,
        |deriv f t| ^ 2 / Real.sin (t / 2) ^ 2) *
        Real.sqrt (∫ t in a..b, Real.sin (t / 2) ^ 2) := by
      simp [I, A, w]

lemma pointwise_weighted_bound_on_circle {f : ℝ → ℝ} {x : ℝ}
    (hAC : AbsolutelyContinuousOnInterval f (-Real.pi) Real.pi)
    (hf0 : f 0 = 0)
    (hW : MeasureTheory.IntegrableOn
      (fun t : ℝ => |deriv f t| ^ 2 / Real.sin (t / 2) ^ 2)
      (Set.Icc (-Real.pi) Real.pi))
    (hxl : -Real.pi ≤ x) (hxu : x ≤ Real.pi) :
    |f x| ≤ Real.pi * |Real.sin (x / 2)| *
      Real.sqrt (∫ t in Set.Icc (-Real.pi) Real.pi,
        |deriv f t| ^ 2 / Real.sin (t / 2) ^ 2) := by
  let I : ℝ := ∫ t in Set.Icc (-Real.pi) Real.pi,
    |deriv f t| ^ 2 / Real.sin (t / 2) ^ 2
  rcases le_total 0 x with hx0 | hx0
  · have hπ : -Real.pi ≤ Real.pi := by nlinarith [Real.pi_pos]
    have hsub : Set.uIcc 0 x ⊆ Set.uIcc (-Real.pi) Real.pi := by
      rw [Set.uIcc_of_le hx0, Set.uIcc_of_le hπ]
      exact Set.Icc_subset_Icc (neg_nonpos.mpr Real.pi_nonneg) hxu
    have hACx : AbsolutelyContinuousOnInterval f 0 x := hAC.mono hsub
    have hftc : ∫ t in (0:ℝ)..x, deriv f t = f x := by
      have h := hACx.integral_deriv_eq_sub
      rw [hf0] at h
      simpa using h
    have hcs : |f x| ≤ Real.sqrt I *
        Real.sqrt (∫ t in (0:ℝ)..x, Real.sin (t / 2) ^ 2) := by
      have h := interval_deriv_norm_le_sqrt_weighted_mul_sqrt_sin_sq hAC hW hx0
        (neg_nonpos.mpr Real.pi_nonneg) hxu
      rw [hftc] at h
      simpa [I] using h
    have hkernel := sqrt_integral_sin_sq_half_le_pi_abs_sin hx0 hxu
    calc
      |f x| ≤ Real.sqrt I *
        Real.sqrt (∫ t in (0:ℝ)..x, Real.sin (t / 2) ^ 2) := hcs
      _ ≤ Real.sqrt I * (Real.pi * |Real.sin (x / 2)|) :=
        mul_le_mul_of_nonneg_left hkernel (Real.sqrt_nonneg I)
      _ = Real.pi * |Real.sin (x / 2)| * Real.sqrt I := by
        ring
      _ = Real.pi * |Real.sin (x / 2)| *
          Real.sqrt (∫ t in Set.Icc (-Real.pi) Real.pi,
            |deriv f t| ^ 2 / Real.sin (t / 2) ^ 2) := by
        simp [I]
  · have hy0 : 0 ≤ -x := by linarith
    have hyπ : -x ≤ Real.pi := by linarith
    have hπ : -Real.pi ≤ Real.pi := by nlinarith [Real.pi_pos]
    have hsub : Set.uIcc x 0 ⊆ Set.uIcc (-Real.pi) Real.pi := by
      rw [Set.uIcc_of_le hx0, Set.uIcc_of_le hπ]
      exact Set.Icc_subset_Icc hxl (by positivity)
    have hACx : AbsolutelyContinuousOnInterval f x 0 := hAC.mono hsub
    have hftc : ∫ t in x..0, deriv f t = -f x := by
      have h := hACx.integral_deriv_eq_sub
      rw [hf0] at h
      simpa using h
    have hsin_even : ∫ t in x..0, Real.sin (t / 2) ^ 2 =
        ∫ t in (0:ℝ)..(-x), Real.sin (t / 2) ^ 2 := by
      have hcomp := intervalIntegral.integral_comp_neg
        (fun t : ℝ => Real.sin (t / 2) ^ 2) (a := x) (b := 0)
      have hcongr : Set.EqOn (fun t : ℝ => Real.sin (-t / 2) ^ 2)
          (fun t : ℝ => Real.sin (t / 2) ^ 2) (Set.uIcc x 0) := by
        intro t ht
        change Real.sin (-t / 2) ^ 2 = Real.sin (t / 2) ^ 2
        have : Real.sin (-t / 2) = -Real.sin (t / 2) := by
          rw [show -t / 2 = -(t / 2) by ring, Real.sin_neg]
        rw [this, neg_sq]
      calc
        ∫ t in x..0, Real.sin (t / 2) ^ 2 =
            ∫ t in x..0, Real.sin (-t / 2) ^ 2 := by
          exact (intervalIntegral.integral_congr hcongr).symm
        _ = ∫ t in -0..-x, Real.sin (t / 2) ^ 2 := hcomp
        _ = ∫ t in (0:ℝ)..(-x), Real.sin (t / 2) ^ 2 := by simp
    have hcs : |f x| ≤ Real.sqrt I *
        Real.sqrt (∫ t in x..0, Real.sin (t / 2) ^ 2) := by
      have h := interval_deriv_norm_le_sqrt_weighted_mul_sqrt_sin_sq hAC hW hx0 hxl
        (by positivity)
      rw [hftc, abs_neg] at h
      simpa [I] using h
    have hkernel := sqrt_integral_sin_sq_half_le_pi_abs_sin hy0 hyπ
    have hsin_abs : |Real.sin ((-x) / 2)| = |Real.sin (x / 2)| := by
      rw [show (-x) / 2 = -(x / 2) by ring, Real.sin_neg, abs_neg]
    rw [hsin_abs] at hkernel
    calc
      |f x| ≤ Real.sqrt I *
        Real.sqrt (∫ t in x..0, Real.sin (t / 2) ^ 2) := hcs
      _ = Real.sqrt I *
        Real.sqrt (∫ t in (0:ℝ)..(-x), Real.sin (t / 2) ^ 2) := by
        rw [hsin_even]
      _ ≤ Real.sqrt I * (Real.pi * |Real.sin (x / 2)|) :=
        mul_le_mul_of_nonneg_left hkernel (Real.sqrt_nonneg I)
      _ = Real.pi * |Real.sin (x / 2)| * Real.sqrt I := by
        ring
      _ = Real.pi * |Real.sin (x / 2)| *
          Real.sqrt (∫ t in Set.Icc (-Real.pi) Real.pi,
            |deriv f t| ^ 2 / Real.sin (t / 2) ^ 2) := by
        simp [I]

/- verified submission -/
theorem weighted_pointwise_inequality_on_circle :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : ℝ → ℝ,
        Function.Periodic f (2 * Real.pi) →
        AbsolutelyContinuousOnInterval f (-Real.pi) Real.pi →
        f 0 = 0 →
        MeasureTheory.IntegrableOn
          (fun x : ℝ => |deriv f x| ^ 2 / Real.sin (x / 2) ^ 2)
          (Set.Icc (-Real.pi) Real.pi) →
        essSup
            (fun x : ℝ => |f x| / |Real.sin (x / 2)|)
            (MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi)) ≤
          C * Real.sqrt
            (∫ x in Set.Icc (-Real.pi) Real.pi,
              |deriv f x| ^ 2 / Real.sin (x / 2) ^ 2) := by
  refine ⟨Real.pi, Real.pi_pos, ?_⟩
  intro f hperiodic hAC hf0 hW
  let I : ℝ := ∫ x in Set.Icc (-Real.pi) Real.pi,
    |deriv f x| ^ 2 / Real.sin (x / 2) ^ 2
  let μ : MeasureTheory.Measure ℝ :=
    MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi)
  let B : ℝ := Real.pi * Real.sqrt I
  change essSup (fun x : ℝ => |f x| / |Real.sin (x / 2)|) μ ≤ B
  have hI_nonneg : 0 ≤ I := by
    dsimp [I]
    apply MeasureTheory.integral_nonneg
    intro x
    positivity
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hpoint : ∀ x ∈ Set.Icc (-Real.pi) Real.pi,
      |f x| / |Real.sin (x / 2)| ≤ B := by
    intro x hx
    have hbound : |f x| ≤ Real.pi * |Real.sin (x / 2)| * Real.sqrt I := by
      simpa [I] using pointwise_weighted_bound_on_circle hAC hf0 hW hx.1 hx.2
    by_cases hs : Real.sin (x / 2) = 0
    · have hle0 : |f x| ≤ 0 := by
        simpa [hs] using hbound
      have hfx0 : f x = 0 := by
        have habs0 : |f x| = 0 := le_antisymm hle0 (abs_nonneg _)
        exact abs_eq_zero.mp habs0
      have hzero : |f x| / |Real.sin (x / 2)| = 0 := by
        simp [hfx0, hs]
      rw [hzero]
      exact hB_nonneg
    · have hden : 0 < |Real.sin (x / 2)| := abs_pos.mpr hs
      rw [div_le_iff₀ hden]
      calc
        |f x| ≤ Real.pi * |Real.sin (x / 2)| * Real.sqrt I := hbound
        _ = (Real.pi * Real.sqrt I) * |Real.sin (x / 2)| := by ring
        _ = B * |Real.sin (x / 2)| := by rfl
  haveI : (MeasureTheory.ae μ).NeBot := by
    rw [MeasureTheory.ae_neBot]
    intro hμ
    change MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi) = 0 at hμ
    have hs : MeasureTheory.volume (Set.Icc (-Real.pi) Real.pi) = 0 :=
      MeasureTheory.Measure.restrict_eq_zero.mp hμ
    rw [Real.volume_Icc] at hs
    have hle := ENNReal.ofReal_eq_zero.mp hs
    nlinarith [Real.pi_pos]
  have hbelow : Filter.IsBoundedUnder (fun x y : ℝ => x ≥ y) (MeasureTheory.ae μ)
      (fun x : ℝ => |f x| / |Real.sin (x / 2)|) := by
    apply Filter.isBoundedUnder_of
    exact ⟨0, fun x => by positivity⟩
  have hcob : Filter.IsCoboundedUnder (fun x y : ℝ => x ≤ y) (MeasureTheory.ae μ)
      (fun x : ℝ => |f x| / |Real.sin (x / 2)|) := by
    simpa using hbelow.isCoboundedUnder_flip
  have hbound_ae : (fun x : ℝ => |f x| / |Real.sin (x / 2)|) ≤ᵐ[μ] fun _ => B := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with x hx
    exact hpoint x hx
  exact Filter.limsup_le_of_le (hf := hcob) hbound_ae

end Rollout_p0332_weighted_pointwise_inequality_on_circle

namespace Rollout_p2625_probability_measure_open_unit_interval_uni

/- accepted add_to_file helper 1 -/
lemma exp_sub_one_le_mul_exp {z : ℝ} (hz : 0 < z) : Real.exp z - 1 ≤ z * Real.exp z := by
  have hs := convexOn_exp.slope_le_of_hasDerivAt (by simp) (by simp) hz (Real.hasDerivAt_exp z)
  dsimp [slope] at hs
  simp at hs
  have h2 := mul_le_mul_of_nonneg_left hs hz.le
  field_simp [hz.ne'] at h2
  simpa [mul_comm, mul_left_comm, mul_assoc] using h2

lemma kernel_nonneg_and_bound {t y : ℝ} (ht : 0 ≤ t) (hy0 : 0 < y) (hy1 : y ≤ 1) :
    0 ≤ (Real.exp (t * y) - 1) / y ∧
      (Real.exp (t * y) - 1) / y ≤ t * Real.exp t := by
  have hzy : 0 ≤ t * y := mul_nonneg ht hy0.le
  have hnonneg : 0 ≤ (Real.exp (t * y) - 1) / y := by
    exact div_nonneg (sub_nonneg.mpr (Real.one_le_exp hzy)) hy0.le
  refine ⟨hnonneg, ?_⟩
  by_cases hz : t * y = 0
  · rw [hz]
    simp only [Real.exp_zero, sub_self, zero_div]
    exact mul_nonneg ht (Real.exp_nonneg t)
  · have hzpos : 0 < t * y := lt_of_le_of_ne' hzy hz
    have hexp1 := exp_sub_one_le_mul_exp hzpos
    have htle : t * y ≤ t := by
      nth_rewrite 2 [← mul_one t]
      exact mul_le_mul_of_nonneg_left hy1 ht
    have hexp2 : Real.exp (t * y) ≤ Real.exp t := Real.exp_le_exp.mpr htle
    have hnum : Real.exp (t * y) - 1 ≤ (t * y) * Real.exp t := by
      calc
        Real.exp (t * y) - 1 ≤ (t * y) * Real.exp (t * y) := hexp1
        _ ≤ (t * y) * Real.exp t := mul_le_mul_of_nonneg_left hexp2 hzy
    calc
      (Real.exp (t * y) - 1) / y ≤ ((t * y) * Real.exp t) / y :=
        div_le_div_of_nonneg_right hnum hy0.le
      _ = t * Real.exp t := by
        field_simp [hy0.ne']

/- accepted add_to_file helper 2 -/
lemma kernel_integrable
    (μ : MeasureTheory.Measure (Set.Ioo (0 : ℝ) 1)) [MeasureTheory.IsProbabilityMeasure μ]
    {t : ℝ} (ht : 0 ≤ t) :
    MeasureTheory.Integrable
      (fun x : Set.Ioo (0 : ℝ) 1 =>
        (Real.exp (t * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ))) μ := by
  have hcont : Continuous (fun x : Set.Ioo (0 : ℝ) 1 =>
      (Real.exp (t * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ))) := by
    apply Continuous.div
    · continuity
    · continuity
    · intro x
      have hx1 : (x : ℝ) < 1 := x.2.2
      exact sub_ne_zero.mpr (ne_of_gt hx1)
  refine MeasureTheory.Integrable.of_mem_Icc 0 (t * Real.exp t) hcont.aemeasurable ?_
  filter_upwards with x
  have hy0 : 0 < 1 - (x : ℝ) := sub_pos.mpr x.2.2
  have hy1 : 1 - (x : ℝ) ≤ 1 := by
    have hx0 : 0 < (x : ℝ) := x.2.1
    linarith
  exact kernel_nonneg_and_bound ht hy0 hy1

/- accepted add_to_file helper 3 -/
lemma F_continuousOn_Icc
    (μ : MeasureTheory.Measure (Set.Ioo (0 : ℝ) 1)) [MeasureTheory.IsProbabilityMeasure μ] :
    ContinuousOn
      (fun t : ℝ => ∫ x : Set.Ioo (0 : ℝ) 1,
        (Real.exp (t * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ)
      (Set.Icc 0 1) := by
  apply MeasureTheory.continuousOn_of_dominated
      (bound := fun _ : Set.Ioo (0 : ℝ) 1 => Real.exp 1) (s := Set.Icc (0:ℝ) 1)
  · intro t ht
    exact (kernel_integrable μ ht.1).aestronglyMeasurable
  · intro t ht
    filter_upwards with x
    have hy0 : 0 < 1 - (x : ℝ) := sub_pos.mpr x.2.2
    have hy1 : 1 - (x : ℝ) ≤ 1 := by
      have hx0 : 0 < (x : ℝ) := x.2.1
      linarith
    have hb := kernel_nonneg_and_bound ht.1 hy0 hy1
    have htexp : t * Real.exp t ≤ Real.exp 1 := by
      have ht1 : t ≤ 1 := ht.2
      calc
        t * Real.exp t ≤ 1 * Real.exp 1 := by
          exact mul_le_mul ht1 (Real.exp_le_exp.mpr ht1) (Real.exp_nonneg t) zero_le_one
        _ = Real.exp 1 := one_mul _
    rw [Real.norm_of_nonneg hb.1]
    exact le_trans hb.2 htexp
  · exact MeasureTheory.integrable_const (Real.exp 1)
  · filter_upwards with x
    have hx1 : (x : ℝ) < 1 := x.2.2
    have hcont : Continuous fun t : ℝ =>
        (Real.exp (t * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) := by
      apply Continuous.div
      · continuity
      · continuity
      · intro t
        exact sub_ne_zero.mpr (ne_of_gt hx1)
    exact hcont.continuousOn

/- accepted add_to_file helper 4 -/
lemma F_quarter_lt_one
    (μ : MeasureTheory.Measure (Set.Ioo (0 : ℝ) 1)) [MeasureTheory.IsProbabilityMeasure μ] :
    (∫ x : Set.Ioo (0 : ℝ) 1,
      (Real.exp ((1/4 : ℝ) * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ) < 1 := by
  let c : ℝ := (1/4 : ℝ) * Real.exp (1/4 : ℝ)
  have hle : (∫ x : Set.Ioo (0 : ℝ) 1,
      (Real.exp ((1/4 : ℝ) * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ) ≤
      ∫ _x : Set.Ioo (0 : ℝ) 1, c ∂μ := by
    apply MeasureTheory.integral_mono_ae
    · exact kernel_integrable μ (by norm_num)
    · exact MeasureTheory.integrable_const c
    · filter_upwards with x
      have hy0 : 0 < 1 - (x : ℝ) := sub_pos.mpr x.2.2
      have hy1 : 1 - (x : ℝ) ≤ 1 := by
        have hx0 : 0 < (x : ℝ) := x.2.1
        linarith
      exact (kernel_nonneg_and_bound (by norm_num : (0:ℝ) ≤ 1/4) hy0 hy1).2
  have hconst : ∫ _x : Set.Ioo (0 : ℝ) 1, c ∂μ = c := by
    rw [MeasureTheory.integral_const]
    simp [MeasureTheory.Measure.real, MeasureTheory.IsProbabilityMeasure.measure_univ]
  have hc : c < 1 := by
    dsimp [c]
    have hexp : Real.exp (1/4 : ℝ) < 4/3 := by
      have h := Real.exp_bound_div_one_sub_of_interval'
        (by norm_num : (0:ℝ) < 1/4) (by norm_num : (1/4:ℝ) < 1)
      norm_num at h ⊢
      exact h
    nlinarith [Real.exp_nonneg (1/4 : ℝ)]
  exact lt_of_le_of_lt (by simpa [hconst] using hle) hc

/- accepted add_to_file helper 5 -/
lemma F_one_gt_one
    (μ : MeasureTheory.Measure (Set.Ioo (0 : ℝ) 1)) [MeasureTheory.IsProbabilityMeasure μ] :
    1 < (∫ x : Set.Ioo (0 : ℝ) 1,
      (Real.exp ((1 : ℝ) * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ) := by
  let d : Set.Ioo (0 : ℝ) 1 → ℝ := fun x =>
    (Real.exp ((1 : ℝ) * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) - 1
  have hd_pos : ∀ x, 0 < d x := by
    intro x
    dsimp [d]
    have hy : 0 < 1 - (x : ℝ) := sub_pos.mpr x.2.2
    have hexp : 1 - (x : ℝ) + 1 < Real.exp (1 - (x : ℝ)) :=
      Real.add_one_lt_exp (sub_ne_zero.mpr (ne_of_gt x.2.2))
    have hratio : 1 < (Real.exp (1 - (x : ℝ)) - 1) / (1 - (x : ℝ)) := by
      rw [lt_div_iff₀ hy]
      linarith
    simpa [one_mul] using sub_pos.mpr hratio
  have hd_nonneg : 0 ≤ d := fun x => (hd_pos x).le
  have hf1 : MeasureTheory.Integrable
      (fun x : Set.Ioo (0 : ℝ) 1 =>
        (Real.exp ((1 : ℝ) * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ))) μ :=
    kernel_integrable μ zero_le_one
  have hd_int : MeasureTheory.Integrable d μ := by
    dsimp [d]
    exact hf1.sub (MeasureTheory.integrable_const 1)
  have hd_int_pos : 0 < ∫ x : Set.Ioo (0 : ℝ) 1, d x ∂μ := by
    rw [MeasureTheory.integral_pos_iff_support_of_nonneg hd_nonneg hd_int]
    have hsupp : Function.support d = Set.univ := by
      ext x
      simp [Function.support, ne_of_gt (hd_pos x)]
    rw [hsupp, MeasureTheory.IsProbabilityMeasure.measure_univ]
    norm_num
  have hdecomp : (∫ x : Set.Ioo (0 : ℝ) 1, d x ∂μ) =
      (∫ x : Set.Ioo (0 : ℝ) 1,
        (Real.exp ((1 : ℝ) * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ) - 1 := by
    dsimp [d]
    rw [MeasureTheory.integral_sub hf1 (MeasureTheory.integrable_const 1)]
    congr 1
    rw [MeasureTheory.integral_const]
    simp [MeasureTheory.Measure.real, MeasureTheory.IsProbabilityMeasure.measure_univ]
  linarith

/- accepted add_to_file helper 6 -/
lemma F_strictMono_on_nonneg
    (μ : MeasureTheory.Measure (Set.Ioo (0 : ℝ) 1)) [MeasureTheory.IsProbabilityMeasure μ]
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a < b) :
    (∫ x : Set.Ioo (0 : ℝ) 1,
      (Real.exp (a * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ) <
    (∫ x : Set.Ioo (0 : ℝ) 1,
      (Real.exp (b * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ) := by
  let d : Set.Ioo (0 : ℝ) 1 → ℝ := fun x =>
    (Real.exp (b * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) -
      (Real.exp (a * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ))
  have hd_pos : ∀ x, 0 < d x := by
    intro x
    dsimp [d]
    have hy : 0 < 1 - (x : ℝ) := sub_pos.mpr x.2.2
    have harg : a * (1 - (x : ℝ)) < b * (1 - (x : ℝ)) :=
      mul_lt_mul_of_pos_right hab hy
    have hexp : Real.exp (a * (1 - (x : ℝ))) < Real.exp (b * (1 - (x : ℝ))) :=
      Real.exp_lt_exp_of_lt harg
    have hnum : Real.exp (a * (1 - (x : ℝ))) - 1 <
        Real.exp (b * (1 - (x : ℝ))) - 1 := sub_lt_sub_right hexp 1
    exact sub_pos.mpr (div_lt_div_of_pos_right hnum hy)
  have hd_nonneg : 0 ≤ d := fun x => (hd_pos x).le
  have hfa : MeasureTheory.Integrable
      (fun x : Set.Ioo (0 : ℝ) 1 =>
        (Real.exp (a * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ))) μ :=
    kernel_integrable μ ha
  have hfb : MeasureTheory.Integrable
      (fun x : Set.Ioo (0 : ℝ) 1 =>
        (Real.exp (b * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ))) μ :=
    kernel_integrable μ hb
  have hd_int : MeasureTheory.Integrable d μ := by
    dsimp [d]
    exact hfb.sub hfa
  have hd_int_pos : 0 < ∫ x : Set.Ioo (0 : ℝ) 1, d x ∂μ := by
    rw [MeasureTheory.integral_pos_iff_support_of_nonneg hd_nonneg hd_int]
    have hsupp : Function.support d = Set.univ := by
      ext x
      simp [Function.support, ne_of_gt (hd_pos x)]
    rw [hsupp, MeasureTheory.IsProbabilityMeasure.measure_univ]
    norm_num
  have hdecomp : (∫ x : Set.Ioo (0 : ℝ) 1, d x ∂μ) =
      (∫ x : Set.Ioo (0 : ℝ) 1,
        (Real.exp (b * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ) -
      (∫ x : Set.Ioo (0 : ℝ) 1,
        (Real.exp (a * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ) := by
    dsimp [d]
    exact MeasureTheory.integral_sub hfb hfa
  linarith

/- verified submission -/
theorem probability_measure_open_unit_interval_unique_solution
    (μ : MeasureTheory.Measure (Set.Ioo (0 : ℝ) 1)) [MeasureTheory.IsProbabilityMeasure μ] :
    ∃ s : ℝ,
      0 < s ∧
        s < 1 ∧
          (∫ x, (Real.exp (s * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ) = 1 ∧
            ∀ t : ℝ,
              0 < t →
                (∫ x, (Real.exp (t * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ) = 1 →
                  t = s := by
  let F : ℝ → ℝ := fun t : ℝ =>
    ∫ x : Set.Ioo (0 : ℝ) 1,
      (Real.exp (t * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ
  have hcontIcc : ContinuousOn F (Set.Icc (1/4 : ℝ) 1) := by
    have hcont := F_continuousOn_Icc μ
    apply hcont.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · exact ht.2
  have hF14 : F (1/4 : ℝ) < 1 := by
    exact F_quarter_lt_one μ
  have hF1 : 1 < F 1 := by
    exact F_one_gt_one μ
  have h1mem : (1 : ℝ) ∈ Set.Ioo (F (1/4 : ℝ)) (F 1) := ⟨hF14, hF1⟩
  have himage := intermediate_value_Ioo (by norm_num : (1/4 : ℝ) ≤ 1) hcontIcc h1mem
  rcases himage with ⟨s, hsI, hsF⟩
  have hs0 : 0 < s := by linarith [hsI.1]
  have hs1 : s < 1 := hsI.2
  have hs_eq : (∫ x : Set.Ioo (0 : ℝ) 1,
      (Real.exp (s * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ) = 1 := by
    exact hsF
  refine ⟨s, hs0, hs1, hs_eq, ?_⟩
  intro t ht0 ht_eq
  rcases lt_trichotomy t s with hts | hts | hts
  · have hstrict := F_strictMono_on_nonneg μ ht0.le hs0.le hts
    rw [ht_eq, hs_eq] at hstrict
    exact (lt_irrefl (1 : ℝ) hstrict).elim
  · exact hts
  · have hstrict := F_strictMono_on_nonneg μ hs0.le ht0.le hts
    rw [ht_eq, hs_eq] at hstrict
    exact (lt_irrefl (1 : ℝ) hstrict).elim

end Rollout_p2625_probability_measure_open_unit_interval_uni

namespace Rollout_p3186_simple_selection_adjusted_control

/- accepted add_to_file helper 1 -/
noncomputable section

namespace SimpleSelectionAdjustedControl

abbrev PTuple (m : ℕ) (n : Fin m → ℕ) : Type :=
  (i : Fin m) → (Fin (n i) → Set.Icc (0 : ℝ) 1)

def contribution
    (m : ℕ) (q : ℝ) (n : Fin m → ℕ)
    (S : PTuple m n → Finset (Fin m))
    (C : (i : Fin m) → ℝ → (Fin (n i) → Set.Icc (0 : ℝ) 1) → ℝ)
    (i : Fin m) (x : PTuple m n) : ℝ :=
  if i ∈ S x then
    C i (((S x).card : ℝ) * q / (m : ℝ)) (x i) / ((S x).card : ℝ)
  else 0

def totalContribution
    (m : ℕ) (q : ℝ) (n : Fin m → ℕ)
    (S : PTuple m n → Finset (Fin m))
    (C : (i : Fin m) → ℝ → (Fin (n i) → Set.Icc (0 : ℝ) 1) → ℝ)
    (x : PTuple m n) : ℝ :=
  ∑ i : Fin m, contribution m q n S C i x

def selectedAverage
    (m : ℕ) (q : ℝ) (n : Fin m → ℕ)
    (S : PTuple m n → Finset (Fin m))
    (C : (i : Fin m) → ℝ → (Fin (n i) → Set.Icc (0 : ℝ) 1) → ℝ)
    (x : PTuple m n) : ℝ :=
  if (S x).card = 0 then 0
  else
    (∑ i ∈ S x,
      C i (((S x).card : ℝ) * q / (m : ℝ)) (x i)) /
      ((S x).card : ℝ)

lemma measurable_selection
    {m : ℕ} {n : Fin m → ℕ}
    [MeasurableSpace (Finset (Fin m))] [MeasurableSingletonClass (Finset (Fin m))]
    {S : PTuple m n → Finset (Fin m)}
    (hS : ∀ s, MeasurableSet (S ⁻¹' {s})) : Measurable S := by
  intro t _ht
  have ht : t.Finite := Set.toFinite t
  have hpre : S ⁻¹' t = ⋃ s ∈ t, S ⁻¹' {s} := by
    ext x
    simp
  rw [hpre]
  exact MeasurableSet.biUnion ht.countable (fun s _ => hS s)

lemma contribution_measurable
    {m : ℕ} {q : ℝ} {n : Fin m → ℕ}
    [MeasurableSpace (Finset (Fin m))] [MeasurableSingletonClass (Finset (Fin m))]
    {S : PTuple m n → Finset (Fin m)}
    {C : (i : Fin m) → ℝ → (Fin (n i) → Set.Icc (0 : ℝ) 1) → ℝ}
    (hS : ∀ s, MeasurableSet (S ⁻¹' {s}))
    (hC : ∀ i α, Measurable (C i α))
    (i : Fin m) :
    Measurable (contribution m q n S C i) := by
  classical
  let level : ℕ → ℝ := fun r => (r : ℝ) * q / (m : ℝ)
  let term : ℕ → PTuple m n → ℝ := fun r x =>
    if i ∈ S x ∧ (S x).card = r then C i (level r) (x i) / (r : ℝ) else 0
  have hSm : Measurable S := measurable_selection hS
  have hterm : ∀ r, Measurable (term r) := by
    intro r
    have hset : MeasurableSet {x : PTuple m n | i ∈ S x ∧ (S x).card = r} := by
      have hmem : MeasurableSet {x : PTuple m n | i ∈ S x} :=
        hSm (Set.Finite.measurableSet (Set.toFinite {s : Finset (Fin m) | i ∈ s}))
      have hcard : MeasurableSet {x : PTuple m n | (S x).card = r} :=
        hSm (Set.Finite.measurableSet (Set.toFinite {s : Finset (Fin m) | s.card = r}))
      exact hmem.inter hcard
    have hCi : Measurable fun x : PTuple m n => C i (level r) (x i) :=
      (hC i (level r)).comp (measurable_pi_apply i)
    exact Measurable.ite hset (hCi.div_const (r : ℝ)) measurable_const
  have hsum : Measurable fun x : PTuple m n =>
      ∑ r ∈ Finset.range (m + 1), term r x :=
    Finset.measurable_sum _ (fun r _ => hterm r)
  have hEq : ∀ x : PTuple m n,
      contribution m q n S C i x = ∑ r ∈ Finset.range (m + 1), term r x := by
    intro x
    by_cases hi : i ∈ S x
    · have hle : (S x).card ≤ m := by
        simpa using Finset.card_le_univ (S x)
      have hmem : (S x).card ∈ Finset.range (m + 1) := by
        exact Finset.mem_range_succ_iff.mpr hle
      rw [Finset.sum_eq_single ((S x).card)]
      · simp [contribution, term, level, hi]
      · intro r _hr hne
        by_cases hr : (S x).card = r
        · exact False.elim (hne hr.symm)
        · simp [term, hr]
      · intro hnot
        exact False.elim (hnot hmem)
    · simp [contribution, term, hi]
  have hfun : contribution m q n S C i = fun x : PTuple m n =>
      ∑ r ∈ Finset.range (m + 1), term r x := funext hEq
  rw [hfun]
  exact hsum

lemma contribution_nonneg
    {m : ℕ} {q : ℝ} {n : Fin m → ℕ}
    {S : PTuple m n → Finset (Fin m)}
    {C : (i : Fin m) → ℝ → (Fin (n i) → Set.Icc (0 : ℝ) 1) → ℝ}
    (hC_nonneg : ∀ i α p, 0 ≤ C i α p)
    (i : Fin m) (x : PTuple m n) :
    0 ≤ contribution m q n S C i x := by
  by_cases hi : i ∈ S x
  · have hcard : 0 < ((S x).card : ℝ) := by
      exact Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨i, hi⟩)
    simp [contribution, hi]
    exact div_nonneg (hC_nonneg i _ _) hcard.le
  · simp [contribution, hi]

lemma totalContribution_nonneg
    {m : ℕ} {q : ℝ} {n : Fin m → ℕ}
    {S : PTuple m n → Finset (Fin m)}
    {C : (i : Fin m) → ℝ → (Fin (n i) → Set.Icc (0 : ℝ) 1) → ℝ}
    (hC_nonneg : ∀ i α p, 0 ≤ C i α p)
    (x : PTuple m n) :
    0 ≤ totalContribution m q n S C x := by
  exact Finset.sum_nonneg (fun i _ => contribution_nonneg hC_nonneg i x)

lemma totalContribution_measurable
    {m : ℕ} {q : ℝ} {n : Fin m → ℕ}
    [MeasurableSpace (Finset (Fin m))] [MeasurableSingletonClass (Finset (Fin m))]
    {S : PTuple m n → Finset (Fin m)}
    {C : (i : Fin m) → ℝ → (Fin (n i) → Set.Icc (0 : ℝ) 1) → ℝ}
    (hS : ∀ s, MeasurableSet (S ⁻¹' {s}))
    (hC : ∀ i α, Measurable (C i α)) :
    Measurable (totalContribution m q n S C) := by
  exact Finset.measurable_sum _ (fun i _ => contribution_measurable hS hC i)

lemma selectedAverage_eq_totalContribution
    {m : ℕ} {q : ℝ} {n : Fin m → ℕ}
    {S : PTuple m n → Finset (Fin m)}
    {C : (i : Fin m) → ℝ → (Fin (n i) → Set.Icc (0 : ℝ) 1) → ℝ}
    (x : PTuple m n) :
    selectedAverage m q n S C x = totalContribution m q n S C x := by
  classical
  by_cases h0 : (S x).card = 0
  · have hs : S x = ∅ := Finset.card_eq_zero.mp h0
    simp [selectedAverage, totalContribution, contribution, hs]
  · let f : Fin m → ℝ := fun i =>
      if i ∈ S x then
        C i (((S x).card : ℝ) * q / (m : ℝ)) (x i) / ((S x).card : ℝ)
      else 0
    have hA : (∑ i ∈ S x, f i) = ∑ i : Fin m, f i := by
      refine Finset.sum_subset (Finset.subset_univ (S x)) ?_
      intro i _hi_univ hi_not
      simp [f, hi_not]
    have hB : (∑ i ∈ S x, f i) =
        ∑ i ∈ S x,
          C i (((S x).card : ℝ) * q / (m : ℝ)) (x i) / ((S x).card : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [f, hi]
    have hsum : totalContribution m q n S C x =
        ∑ i ∈ S x,
          C i (((S x).card : ℝ) * q / (m : ℝ)) (x i) / ((S x).card : ℝ) := by
      exact hA.symm.trans hB
    rw [selectedAverage, if_neg h0, hsum]
    exact Finset.sum_div (S x)
      (fun i => C i (((S x).card : ℝ) * q / (m : ℝ)) (x i))
      ((S x).card : ℝ)

end SimpleSelectionAdjustedControl

end

/- accepted add_to_file helper 2 -/
namespace SimpleSelectionAdjustedControl

lemma lintegral_contribution_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0 < m)
    (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (n : Fin m → ℕ)
    (P : (i : Fin m) → Ω → (Fin (n i) → Set.Icc (0 : ℝ) 1))
    (hP_measurable : ∀ i, Measurable (P i))
    (S : PTuple m n → Finset (Fin m))
    (hS_measurable : ∀ s, MeasurableSet (S ⁻¹' {s}))
    (hS_simple : ∀ (i : Fin m) x y,
      (∀ j, j ≠ i → x j = y j) →
        i ∈ S x → i ∈ S y → (S x).card = (S y).card)
    (C : (i : Fin m) → ℝ → (Fin (n i) → Set.Icc (0 : ℝ) 1) → ℝ)
    (hC_measurable : ∀ i α, Measurable (C i α))
    (hC_nonnegative : ∀ i α p, 0 ≤ C i α p)
    (hC_valid : ∀ (i : Fin m) (α : ℝ), α ∈ Set.Icc (0 : ℝ) 1 →
      MeasureTheory.Integrable (fun ω => C i α (P i ω)) μ ∧
        ∫ ω, C i α (P i ω) ∂μ ≤ α)
    (i : Fin m) :
    ∫⁻ x, ENNReal.ofReal (contribution m q n S C i x)
      ∂MeasureTheory.Measure.pi (fun j => μ.map (P j)) ≤ ENNReal.ofReal (q / (m : ℝ)) := by
  classical
  letI : MeasurableSpace (Finset (Fin m)) := ⊤
  letI : MeasurableSingletonClass (Finset (Fin m)) :=
    ⟨fun s => by simp⟩
  let ν : (j : Fin m) → MeasureTheory.Measure (Fin (n j) → Set.Icc (0 : ℝ) 1) :=
    fun j => μ.map (P j)
  have hνprob : ∀ j, MeasureTheory.IsProbabilityMeasure (ν j) := by
    intro j
    exact MeasureTheory.Measure.isProbabilityMeasure_map (hP_measurable j).aemeasurable
  haveI : ∀ j, MeasureTheory.IsProbabilityMeasure (ν j) := hνprob
  haveI : ∀ j, MeasureTheory.SigmaFinite (ν j) := fun j => inferInstance
  have hf : Measurable fun x : PTuple m n =>
      ENNReal.ofReal (contribution m q n S C i x) :=
    ENNReal.measurable_ofReal.comp (contribution_measurable hS_measurable hC_measurable i)
  have hg : Measurable fun _ : PTuple m n => ENNReal.ofReal (q / (m : ℝ)) :=
    measurable_const
  have hconst_lint :
      (∫⁻ _p, ENNReal.ofReal (q / (m : ℝ)) ∂ν i) =
        ENNReal.ofReal (q / (m : ℝ)) := by
    calc
      (∫⁻ _p, ENNReal.ofReal (q / (m : ℝ)) ∂ν i)
          = ENNReal.ofReal (q / (m : ℝ)) * (ν i) Set.univ :=
            MeasureTheory.lintegral_const _
      _ = ENNReal.ofReal (q / (m : ℝ)) := by simp
  have hfg :
      (∫⋯∫⁻_{i},
          (fun x : PTuple m n => ENNReal.ofReal (contribution m q n S C i x)) ∂ν) ≤
        ∫⋯∫⁻_{i}, (fun _ : PTuple m n => ENNReal.ofReal (q / (m : ℝ))) ∂ν := by
    rw [MeasureTheory.lmarginal_singleton, MeasureTheory.lmarginal_singleton]
    intro x
    by_cases hsel : ∃ p : Fin (n i) → Set.Icc (0 : ℝ) 1,
        i ∈ S (Function.update x i p)
    · rcases hsel with ⟨p0, hp0⟩
      let r : ℕ := (S (Function.update x i p0)).card
      let α : ℝ := (r : ℝ) * q / (m : ℝ)
      have hrpos_nat : 0 < r := Finset.card_pos.mpr ⟨i, hp0⟩
      have hrpos : 0 < (r : ℝ) := Nat.cast_pos.mpr hrpos_nat
      have hrle : (r : ℝ) ≤ (m : ℝ) := by
        have hle : r ≤ m := by
          simpa [r] using Finset.card_le_univ (S (Function.update x i p0))
        exact_mod_cast hle
      rcases Set.mem_Icc.mp hq with ⟨hq0, hq1⟩
      have hmpos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
      have hα : α ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg (mul_nonneg (Nat.cast_nonneg r) hq0) (Nat.cast_nonneg m)
        · rw [div_le_iff₀ hmpos]
          nlinarith
      have hconst_card : ∀ p,
          i ∈ S (Function.update x i p) →
          (S (Function.update x i p)).card = r := by
        intro p hp
        have hout : ∀ j, j ≠ i →
            Function.update x i p0 j = Function.update x i p j := by
          intro j hj
          simp [Function.update, hj]
        exact (hS_simple i (Function.update x i p0) (Function.update x i p)
          hout hp0 hp).symm
      have hpoint : ∀ p : Fin (n i) → Set.Icc (0 : ℝ) 1,
          contribution m q n S C i (Function.update x i p) ≤ C i α p / (r : ℝ) := by
        intro p
        by_cases hp : i ∈ S (Function.update x i p)
        · have hcard := hconst_card p hp
          have hlevel : (((S (Function.update x i p)).card : ℝ) * q / (m : ℝ)) = α := by
            simp [α, hcard]
          have heq :
              contribution m q n S C i (Function.update x i p) =
                C i α p / (r : ℝ) := by
            calc
              contribution m q n S C i (Function.update x i p)
                  = if i ∈ S (Function.update x i p) then
                      C i (((S (Function.update x i p)).card : ℝ) * q / (m : ℝ))
                        (Function.update x i p i) /
                        ((S (Function.update x i p)).card : ℝ)
                    else 0 := rfl
              _ = C i (((S (Function.update x i p)).card : ℝ) * q / (m : ℝ))
                    (Function.update x i p i) /
                    ((S (Function.update x i p)).card : ℝ) := if_pos hp
              _ = C i α p / ((S (Function.update x i p)).card : ℝ) := by
                    rw [hlevel, Function.update_self]
              _ = C i α p / (r : ℝ) := by rw [hcard]
          exact le_of_eq heq
        · have hCnonneg : 0 ≤ C i α p / (r : ℝ) :=
            div_nonneg (hC_nonnegative i α p) hrpos.le
          simp [contribution, hp, hCnonneg]
      have hvalid_source := hC_valid i α hα
      have hCint : MeasureTheory.Integrable (fun p => C i α p) (ν i) := by
        dsimp [ν]
        exact (MeasureTheory.integrable_map_measure
          (hC_measurable i α).aestronglyMeasurable
          (hP_measurable i).aemeasurable).2 hvalid_source.1
      have hint_eq :
          (∫ p, C i α p ∂ν i) = ∫ ω, C i α (P i ω) ∂μ := by
        dsimp [ν]
        exact MeasureTheory.integral_map (hP_measurable i).aemeasurable
          (hC_measurable i α).aestronglyMeasurable
      have hCbound : (∫ p, C i α p ∂ν i) ≤ α := by
        rw [hint_eq]
        exact hvalid_source.2
      have hCdiv_int : MeasureTheory.Integrable (fun p => C i α p / (r : ℝ)) (ν i) :=
        hCint.div_const (r : ℝ)
      have hCdiv_nonneg : 0 ≤ᵐ[ν i] fun p => C i α p / (r : ℝ) :=
        Filter.Eventually.of_forall (fun p =>
          div_nonneg (hC_nonnegative i α p) hrpos.le)
      have hlin_eq :
          (∫⁻ p, ENNReal.ofReal (C i α p / (r : ℝ)) ∂ν i) =
            ENNReal.ofReal (∫ p, C i α p / (r : ℝ) ∂ν i) := by
        exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hCdiv_int hCdiv_nonneg).symm
      have hreal_bound : (∫ p, C i α p / (r : ℝ) ∂ν i) ≤ α / (r : ℝ) := by
        rw [MeasureTheory.integral_div]
        exact div_le_div_of_nonneg_right hCbound hrpos.le
      have hαeq : α / (r : ℝ) = q / (m : ℝ) := by
        have hrm : (r : ℝ) ≠ 0 := hrpos.ne'
        have hmm : (m : ℝ) ≠ 0 := hmpos.ne'
        dsimp [α]
        field_simp [hrm, hmm]
      have hinner_le :
          (∫⁻ p, ENNReal.ofReal (contribution m q n S C i (Function.update x i p)) ∂ν i) ≤
            ENNReal.ofReal (q / (m : ℝ)) := by
        calc
          (∫⁻ p, ENNReal.ofReal (contribution m q n S C i (Function.update x i p)) ∂ν i)
              ≤ ∫⁻ p, ENNReal.ofReal (C i α p / (r : ℝ)) ∂ν i := by
                exact MeasureTheory.lintegral_mono (fun p =>
                  ENNReal.ofReal_le_ofReal (hpoint p))
          _ = ENNReal.ofReal (∫ p, C i α p / (r : ℝ) ∂ν i) := hlin_eq
          _ ≤ ENNReal.ofReal (α / (r : ℝ)) := ENNReal.ofReal_le_ofReal hreal_bound
          _ = ENNReal.ofReal (q / (m : ℝ)) := by rw [hαeq]
      calc
        (∫⁻ p, ENNReal.ofReal (contribution m q n S C i (Function.update x i p)) ∂ν i)
            ≤ ENNReal.ofReal (q / (m : ℝ)) := hinner_le
        _ = ∫⁻ _p, ENNReal.ofReal (q / (m : ℝ)) ∂ν i := hconst_lint.symm
    · have hzero : ∀ p : Fin (n i) → Set.Icc (0 : ℝ) 1,
          contribution m q n S C i (Function.update x i p) = 0 := by
        intro p
        have hp : ¬ i ∈ S (Function.update x i p) := by
          intro hp
          exact hsel ⟨p, hp⟩
        simp [contribution, hp]
      calc
        (∫⁻ p, ENNReal.ofReal (contribution m q n S C i (Function.update x i p)) ∂ν i)
            ≤ ENNReal.ofReal (q / (m : ℝ)) := by simp [hzero]
        _ = ∫⁻ _p, ENNReal.ofReal (q / (m : ℝ)) ∂ν i := hconst_lint.symm
  simpa [ν] using
    MeasureTheory.lintegral_le_of_lmarginal_le {i} hf hg hfg

end SimpleSelectionAdjustedControl

/- accepted add_to_file helper 3 -/
namespace SimpleSelectionAdjustedControl

lemma lintegral_totalContribution_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0 < m)
    (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (n : Fin m → ℕ)
    (P : (i : Fin m) → Ω → (Fin (n i) → Set.Icc (0 : ℝ) 1))
    (hP_measurable : ∀ i, Measurable (P i))
    (S : PTuple m n → Finset (Fin m))
    (hS_measurable : ∀ s, MeasurableSet (S ⁻¹' {s}))
    (hS_simple : ∀ (i : Fin m) x y,
      (∀ j, j ≠ i → x j = y j) →
        i ∈ S x → i ∈ S y → (S x).card = (S y).card)
    (C : (i : Fin m) → ℝ → (Fin (n i) → Set.Icc (0 : ℝ) 1) → ℝ)
    (hC_measurable : ∀ i α, Measurable (C i α))
    (hC_nonnegative : ∀ i α p, 0 ≤ C i α p)
    (hC_valid : ∀ (i : Fin m) (α : ℝ), α ∈ Set.Icc (0 : ℝ) 1 →
      MeasureTheory.Integrable (fun ω => C i α (P i ω)) μ ∧
        ∫ ω, C i α (P i ω) ∂μ ≤ α) :
    ∫⁻ x, ENNReal.ofReal (totalContribution m q n S C x)
      ∂MeasureTheory.Measure.pi (fun j => μ.map (P j)) ≤ ENNReal.ofReal q := by
  classical
  letI : MeasurableSpace (Finset (Fin m)) := ⊤
  letI : MeasurableSingletonClass (Finset (Fin m)) :=
    ⟨fun s => by simp⟩
  have hofsum : ∀ x : PTuple m n,
      ENNReal.ofReal (totalContribution m q n S C x) =
        ∑ i : Fin m, ENNReal.ofReal (contribution m q n S C i x) := by
    intro x
    exact ENNReal.ofReal_sum_of_nonneg (fun i _ =>
      contribution_nonneg hC_nonnegative i x)
  have hfun_eq :
      (fun x : PTuple m n => ENNReal.ofReal (totalContribution m q n S C x)) =
        fun x => ∑ i : Fin m, ENNReal.ofReal (contribution m q n S C i x) :=
    funext hofsum
  have hmeas : ∀ i ∈ Finset.univ,
      Measurable fun x : PTuple m n =>
        ENNReal.ofReal (contribution m q n S C i x) := by
    intro i _hi
    exact ENNReal.measurable_ofReal.comp
      (contribution_measurable hS_measurable hC_measurable i)
  have hle : ∀ i : Fin m,
      ∫⁻ x, ENNReal.ofReal (contribution m q n S C i x)
        ∂MeasureTheory.Measure.pi (fun j => μ.map (P j)) ≤
          ENNReal.ofReal (q / (m : ℝ)) := by
    intro i
    exact lintegral_contribution_le μ m hm q hq n P hP_measurable S
      hS_measurable hS_simple C hC_measurable hC_nonnegative hC_valid i
  rcases Set.mem_Icc.mp hq with ⟨hq0, _hq1⟩
  have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hmne : (m : ℝ) ≠ 0 := (Nat.cast_pos.mpr hm).ne'
  have hsumq : (∑ _i : Fin m, q / (m : ℝ)) = q := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [nsmul_eq_mul]
    field_simp [hmne]
  have hconst_sum :
      (∑ _i : Fin m, ENNReal.ofReal (q / (m : ℝ))) = ENNReal.ofReal q := by
    calc
      (∑ _i : Fin m, ENNReal.ofReal (q / (m : ℝ)))
          = ENNReal.ofReal (∑ _i : Fin m, q / (m : ℝ)) := by
              symm
              exact ENNReal.ofReal_sum_of_nonneg (fun _ _ =>
                div_nonneg hq0 hmnonneg)
      _ = ENNReal.ofReal q := by rw [hsumq]
  rw [hfun_eq, MeasureTheory.lintegral_finset_sum Finset.univ hmeas]
  calc
    (∑ i : Fin m,
        ∫⁻ x, ENNReal.ofReal (contribution m q n S C i x)
          ∂MeasureTheory.Measure.pi (fun j => μ.map (P j)))
        ≤ ∑ _i : Fin m, ENNReal.ofReal (q / (m : ℝ)) :=
          Finset.sum_le_sum (fun i _ => hle i)
    _ = ENNReal.ofReal q := hconst_sum

end SimpleSelectionAdjustedControl

/- verified submission -/
theorem simple_selection_adjusted_control
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0 < m)
    (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (n : Fin m → ℕ)
    (P : (i : Fin m) → Ω → (Fin (n i) → Set.Icc (0 : ℝ) 1))
    (hP_measurable : ∀ i, Measurable (P i))
    (hP_independent : ProbabilityTheory.iIndepFun P μ)
    (S : ((i : Fin m) → (Fin (n i) → Set.Icc (0 : ℝ) 1)) → Finset (Fin m))
    (hS_measurable : ∀ s, MeasurableSet (S ⁻¹' {s}))
    (hS_simple : ∀ (i : Fin m) x y,
      (∀ j, j ≠ i → x j = y j) →
        i ∈ S x → i ∈ S y → (S x).card = (S y).card)
    (C : (i : Fin m) → ℝ → (Fin (n i) → Set.Icc (0 : ℝ) 1) → ℝ)
    (hC_measurable : ∀ i α, Measurable (C i α))
    (hC_nonnegative : ∀ i α p, 0 ≤ C i α p)
    (hC_countable : (Set.range
      (fun z : Σ i : Fin m, ℝ × (Fin (n i) → Set.Icc (0 : ℝ) 1) =>
        C z.1 z.2.1 z.2.2)).Countable)
    (hC_valid : ∀ (i : Fin m) (α : ℝ), α ∈ Set.Icc (0 : ℝ) 1 →
      MeasureTheory.Integrable (fun ω => C i α (P i ω)) μ ∧
        ∫ ω, C i α (P i ω) ∂μ ≤ α) :
    ∫ ω,
      if (S (fun i => P i ω)).card = 0 then 0
      else
        (∑ i ∈ S (fun j => P j ω),
          C i (((S (fun j => P j ω)).card : ℝ) * q / (m : ℝ)) (P i ω)) /
          ((S (fun i => P i ω)).card : ℝ) ∂μ ≤ q := by
  classical
  letI : MeasurableSpace (Finset (Fin m)) := ⊤
  letI : MeasurableSingletonClass (Finset (Fin m)) :=
    ⟨fun s => by simp⟩
  let F : Ω → SimpleSelectionAdjustedControl.PTuple m n := fun ω i => P i ω
  let Y : SimpleSelectionAdjustedControl.PTuple m n → ℝ :=
    SimpleSelectionAdjustedControl.totalContribution m q n S C
  have hF_measurable : Measurable F := by
    exact measurable_pi_lambda _ hP_measurable
  have hY_measurable : Measurable Y := by
    exact SimpleSelectionAdjustedControl.totalContribution_measurable
      hS_measurable hC_measurable
  have hYF_measurable : Measurable fun ω => Y (F ω) :=
    hY_measurable.comp hF_measurable
  have hY_nonneg : 0 ≤ᵐ[μ] fun ω => Y (F ω) :=
    Filter.Eventually.of_forall (fun ω =>
      SimpleSelectionAdjustedControl.totalContribution_nonneg hC_nonnegative (F ω))
  have hintegral_eq :
      (∫ ω, Y (F ω) ∂μ) =
        (∫⁻ ω, ENNReal.ofReal (Y (F ω)) ∂μ).toReal := by
    exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae hY_nonneg
      hYF_measurable.aestronglyMeasurable
  have hfun :
      (fun ω =>
        if (S (fun i => P i ω)).card = 0 then 0
        else
          (∑ i ∈ S (fun j => P j ω),
            C i (((S (fun j => P j ω)).card : ℝ) * q / (m : ℝ)) (P i ω)) /
            ((S (fun i => P i ω)).card : ℝ)) =
        fun ω => Y (F ω) := by
    funext ω
    change SimpleSelectionAdjustedControl.selectedAverage m q n S C (F ω) = Y (F ω)
    exact SimpleSelectionAdjustedControl.selectedAverage_eq_totalContribution (F ω)
  have hνprob : ∀ j,
      MeasureTheory.IsProbabilityMeasure (μ.map (P j)) := by
    intro j
    exact MeasureTheory.Measure.isProbabilityMeasure_map
      (hP_measurable j).aemeasurable
  haveI : ∀ j, MeasureTheory.IsProbabilityMeasure (μ.map (P j)) := hνprob
  have hjoint_infinite :
      μ.map F = MeasureTheory.Measure.infinitePi fun j => μ.map (P j) := by
    exact (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
      hP_measurable).mp hP_independent
  have hjoint :
      μ.map F = MeasureTheory.Measure.pi fun j => μ.map (P j) := by
    calc
      μ.map F = MeasureTheory.Measure.infinitePi fun j => μ.map (P j) :=
        hjoint_infinite
      _ = MeasureTheory.Measure.pi fun j => μ.map (P j) :=
        MeasureTheory.Measure.infinitePi_eq_pi _
  have hYenn_measurable : Measurable fun x => ENNReal.ofReal (Y x) :=
    ENNReal.measurable_ofReal.comp hY_measurable
  have hlintegral_map :
      (∫⁻ x, ENNReal.ofReal (Y x) ∂μ.map F) =
        ∫⁻ ω, ENNReal.ofReal (Y (F ω)) ∂μ := by
    exact MeasureTheory.lintegral_map hYenn_measurable hF_measurable
  have hlintegral_source_pi :
      (∫⁻ ω, ENNReal.ofReal (Y (F ω)) ∂μ) =
        ∫⁻ x, ENNReal.ofReal (Y x)
          ∂MeasureTheory.Measure.pi (fun j => μ.map (P j)) := by
    rw [← hlintegral_map, hjoint]
  have hpi_bound :
      (∫⁻ x, ENNReal.ofReal (Y x)
        ∂MeasureTheory.Measure.pi (fun j => μ.map (P j))) ≤ ENNReal.ofReal q := by
    exact SimpleSelectionAdjustedControl.lintegral_totalContribution_le
      μ m hm q hq n P hP_measurable S hS_measurable hS_simple C
      hC_measurable hC_nonnegative hC_valid
  rcases Set.mem_Icc.mp hq with ⟨hq0, _hq1⟩
  have htoReal_bound :
      (∫⁻ ω, ENNReal.ofReal (Y (F ω)) ∂μ).toReal ≤ q := by
    calc
      (∫⁻ ω, ENNReal.ofReal (Y (F ω)) ∂μ).toReal
          = (∫⁻ x, ENNReal.ofReal (Y x)
              ∂MeasureTheory.Measure.pi (fun j => μ.map (P j))).toReal := by
              rw [hlintegral_source_pi]
      _ ≤ (ENNReal.ofReal q).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hpi_bound
      _ = q := ENNReal.toReal_ofReal hq0
  rw [hfun, hintegral_eq]
  exact htoReal_bound

end Rollout_p3186_simple_selection_adjusted_control

namespace Rollout_p0130_affinesemigroup_normal_equiv

/- accepted add_to_file helper 1 -/
noncomputable def affineSemigroupBasis
    (d : ℕ) (hd : 1 ≤ d) (a : Fin d → Fin d → ℕ)
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ))) :
    Module.Basis (Fin d) ℝ (Fin d → ℝ) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  exact @basisOfLinearIndependentOfCardEqFinrank ℝ (Fin d → ℝ) _ _ _ (Fin d) this _
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)) haLI (by
        rw [Module.finrank_pi, Fintype.card_fin])

lemma affineSemigroupBasis_apply
    (d : ℕ) (hd : 1 ≤ d) (a : Fin d → Fin d → ℕ)
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ))) (i : Fin d) :
    affineSemigroupBasis d hd a haLI i = fun j => (a i j : ℝ) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  simp [affineSemigroupBasis]

lemma affineSemigroup_sum_coords
    {d : ℕ} {hd : 1 ≤ d} {a : Fin d → Fin d → ℕ}
    {haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ))}
    {x : Fin d → ℝ} {c : Fin d → ℝ}
    (hx : x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))) :
    ∀ i, (affineSemigroupBasis d hd a haLI).repr x i = c i := by
  intro i
  subst x
  let b := affineSemigroupBasis d hd a haLI
  have hb : ∀ k, b k = fun j : Fin d => (a k j : ℝ) := by
    intro k
    exact affineSemigroupBasis_apply d hd a haLI k
  have hsum : (∑ k, c k • (fun j : Fin d => (a k j : ℝ))) =
      (Finsupp.linearCombination ℝ (fun k => b k))
        (Finsupp.equivFunOnFinite.symm c) := by
    rw [Finsupp.linearCombination_apply]
    rw [Finsupp.sum_fintype]
    · simp [hb]
    · intro j
      simp
  rw [hsum, Module.Basis.repr_linearCombination]
  simp

abbrev affineSemigroupNatToInt (d : ℕ) : (Fin d → ℕ) → (Fin d → ℤ) :=
  fun u j => (u j : ℤ)

abbrev affineSemigroupNatToReal (d : ℕ) : (Fin d → ℕ) → (Fin d → ℝ) :=
  fun u j => (u j : ℝ)

abbrev affineSemigroupIntToReal (d : ℕ) : (Fin d → ℤ) → (Fin d → ℝ) :=
  fun u j => (u j : ℝ)

lemma affineSemigroup_S_coord_nonneg
    {d : ℕ} (hd : 1 ≤ d)
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    {haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ))}
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ)))
    {w : Fin d → ℕ} (hw : w ∈ S) (i : Fin d) :
    0 ≤ (affineSemigroupBasis d hd a haLI).repr
      (affineSemigroupNatToReal d w) i := by
  have hmem : affineSemigroupNatToReal d w ∈
      ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
        (S : Set (Fin d → ℕ))) := by
    exact ⟨w, hw, rfl⟩
  have hhull : affineSemigroupNatToReal d w ∈
      ConvexCone.hull ℝ
        ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
          (S : Set (Fin d → ℕ))) :=
    ConvexCone.subset_hull hmem
  rcases (hcone _ ).mp hhull with ⟨c, hc, hx⟩
  rw [affineSemigroup_sum_coords hx i]
  exact hc i

/- accepted add_to_file helper 2 -/
def affineSemigroupCone (d : ℕ) (a : Fin d → Fin d → ℕ) : Set (Fin d → ℝ) :=
  {x | ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
    x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))}

def affineSemigroupRelintCone (d : ℕ) (a : Fin d → Fin d → ℕ) : Set (Fin d → ℝ) :=
  {x | ∃ c : Fin d → ℝ, (∀ i, 0 < c i) ∧
    x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))}

def affineSemigroupFundamentalParallelepiped
    (d : ℕ) (a : Fin d → Fin d → ℕ) : Set (Fin d → ℝ) :=
  {x | ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i ∧ c i < 1) ∧
    x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))}

def affineSemigroupApery (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) (a : Fin d → Fin d → ℕ) :
    Set (Fin d → ℕ) :=
  {w | w ∈ S ∧ ∀ i, ¬∃ s : Fin d → ℕ, s ∈ S ∧ w = s + a i}

def affineSemigroupG (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) : Set (Fin d → ℤ) :=
  {z | ∃ u : Fin d → ℕ, u ∈ S ∧
    ∃ v : Fin d → ℕ, v ∈ S ∧
      z = affineSemigroupNatToInt d u - affineSemigroupNatToInt d v}

def affineSemigroupNormal (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) (a : Fin d → Fin d → ℕ) : Prop :=
  affineSemigroupNatToInt d '' (S : Set (Fin d → ℕ)) =
    affineSemigroupG d S ∩
      {z | affineSemigroupIntToReal d z ∈ affineSemigroupCone d a}

/- accepted add_to_file helper 3 -/
lemma affineSemigroup_normal_implies_condition4
    {d : ℕ} (hd : 1 ≤ d)
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haS : ∀ i, a i ∈ S)
    {haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ))}
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ)))
    (hnormal : affineSemigroupNormal d S a)
    {w : Fin d → ℕ} (hw : w ∈ affineSemigroupApery d S a) :
    affineSemigroupNatToReal d w ∈
      affineSemigroupFundamentalParallelepiped d a := by
  rcases hw with ⟨hwS, hnopred⟩
  have hmem : affineSemigroupNatToReal d w ∈
      ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
        (S : Set (Fin d → ℕ))) := by
    exact ⟨w, hwS, rfl⟩
  have hhull : affineSemigroupNatToReal d w ∈
      ConvexCone.hull ℝ
        ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
          (S : Set (Fin d → ℕ))) :=
    ConvexCone.subset_hull hmem
  rcases (hcone _ ).mp hhull with ⟨c, hc, hx⟩
  refine ⟨c, ?_, hx⟩
  intro i
  refine ⟨hc i, ?_⟩
  by_contra hlt
  have hci : 1 ≤ c i := le_of_not_gt hlt
  let z : Fin d → ℤ :=
    affineSemigroupNatToInt d w - affineSemigroupNatToInt d (a i)
  let dc : Fin d → ℝ := fun k => c k - (if k = i then 1 else 0)
  have hdc : ∀ k, 0 ≤ dc k := by
    intro k
    by_cases hk : k = i
    · simp [dc, hk, sub_nonneg.mpr hci]
    · simp [dc, hk, hc k]
  have hzreal : affineSemigroupIntToReal d z =
      affineSemigroupNatToReal d w - affineSemigroupNatToReal d (a i) := by
    funext j
    simp [z, affineSemigroupIntToReal, affineSemigroupNatToInt,
      affineSemigroupNatToReal, Int.cast_sub]
  have hzC : affineSemigroupIntToReal d z ∈ affineSemigroupCone d a := by
    refine ⟨dc, hdc, ?_⟩
    rw [hzreal, hx]
    simp [dc, Finset.sum_sub_distrib, sub_smul]
  have hzG : z ∈ affineSemigroupG d S := by
    refine ⟨w, hwS, a i, haS i, rfl⟩
  have hzimage : z ∈ affineSemigroupNatToInt d '' (S : Set (Fin d → ℕ)) := by
    change z ∈ affineSemigroupNatToInt d '' (S : Set (Fin d → ℕ))
    rw [hnormal]
    exact ⟨hzG, hzC⟩
  rcases hzimage with ⟨s, hsS, hsz⟩
  have hws : w = s + a i := by
    funext j
    have hpoint := congrFun hsz j
    change (s j : ℤ) = (w j : ℤ) - (a i j : ℤ) at hpoint
    have hnat : s j + a i j = w j := by
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_add]
      omega
    simpa [hnat]
  exact hnopred i ⟨s, hsS, hws⟩

/- accepted add_to_file helper 4 -/
def affineSemigroupLeS (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) :
    (Fin d → ℕ) → (Fin d → ℕ) → Prop :=
  fun u v => ∃ s : Fin d → ℕ, s ∈ S ∧ v = u + s

def affineSemigroupMaximalApery (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) (a : Fin d → Fin d → ℕ) :
    (Fin d → ℕ) → Prop :=
  fun m => m ∈ affineSemigroupApery d S a ∧
    ∀ w, w ∈ affineSemigroupApery d S a →
      affineSemigroupLeS d S m w → affineSemigroupLeS d S w m

def affineSemigroupQF (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) (a : Fin d → Fin d → ℕ) :
    Set (Fin d → ℤ) :=
  {f | ∃ m, affineSemigroupMaximalApery d S a m ∧
    f = affineSemigroupNatToInt d m -
      ∑ i, affineSemigroupNatToInt d (a i)}

def affineSemigroupCondition2 (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) (a : Fin d → Fin d → ℕ) : Prop :=
  ∀ f, f ∈ affineSemigroupQF d S a →
    -f ∈ affineSemigroupNatToInt d '' (S : Set (Fin d → ℕ)) ∧
      affineSemigroupIntToReal d (-f) ∈ affineSemigroupRelintCone d a

def affineSemigroupCondition3 (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) (a : Fin d → Fin d → ℕ) : Prop :=
  ∀ f, f ∈ affineSemigroupQF d S a →
    affineSemigroupIntToReal d (-f) ∈ affineSemigroupRelintCone d a

def affineSemigroupCondition4 (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) (a : Fin d → Fin d → ℕ) : Prop :=
  ∀ w, w ∈ affineSemigroupApery d S a →
    affineSemigroupNatToReal d w ∈
      affineSemigroupFundamentalParallelepiped d a

/- accepted add_to_file helper 5 -/
lemma affineSemigroup_normal_implies_condition2
    {d : ℕ} (hd : 1 ≤ d)
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haS : ∀ i, a i ∈ S)
    {haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ))}
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ)))
    (hnormal : affineSemigroupNormal d S a) :
    affineSemigroupCondition2 d S a := by
  intro f hf
  rcases hf with ⟨m, hm, rfl⟩
  rcases hm.1 with ⟨hmS, hmnopred⟩
  have hcond4 := affineSemigroup_normal_implies_condition4
    (d := d) (hd := hd) (S := S) (a := a) (haLI := haLI)
    haS hcone hnormal hm.1
  rcases hcond4 with ⟨c, hc, hxm⟩
  let q : Fin d → ℝ := fun i => 1 - c i
  have hq : ∀ i, 0 < q i := by
    intro i
    exact sub_pos.mpr (hc i).2
  have hsumaS : (∑ i, a i) ∈ S := by
    exact S.sum_mem (fun i hi => haS i)
  have hcastsum : affineSemigroupNatToInt d (∑ i, a i) =
      ∑ i, affineSemigroupNatToInt d (a i) := by
    funext j
    simp [affineSemigroupNatToInt]
  have hneg :
      -(affineSemigroupNatToInt d m - ∑ i, affineSemigroupNatToInt d (a i)) =
        ∑ i, affineSemigroupNatToInt d (a i) - affineSemigroupNatToInt d m := by
    abel
  have hG : -(affineSemigroupNatToInt d m -
      ∑ i, affineSemigroupNatToInt d (a i)) ∈ affineSemigroupG d S := by
    rw [hneg, ← hcastsum]
    exact ⟨∑ i, a i, hsumaS, m, hmS, rfl⟩
  have hreal :
      affineSemigroupIntToReal d
        (-(affineSemigroupNatToInt d m -
          ∑ i, affineSemigroupNatToInt d (a i))) =
        ∑ i, q i • (fun j : Fin d => (a i j : ℝ)) := by
    rw [hneg]
    funext j
    simp [affineSemigroupIntToReal, affineSemigroupNatToInt,
      affineSemigroupNatToReal, q]
    have hmcoord := congrFun hxm j
    simp [affineSemigroupNatToReal] at hmcoord
    rw [hmcoord]
    simp [Finset.sum_sub_distrib, sub_mul]
  have hrel :
      affineSemigroupIntToReal d
        (-(affineSemigroupNatToInt d m -
          ∑ i, affineSemigroupNatToInt d (a i))) ∈
        affineSemigroupRelintCone d a := by
    exact ⟨q, hq, hreal⟩
  have hC :
      affineSemigroupIntToReal d
        (-(affineSemigroupNatToInt d m -
          ∑ i, affineSemigroupNatToInt d (a i))) ∈
        affineSemigroupCone d a := by
    rcases hrel with ⟨r, hr, hx⟩
    exact ⟨r, fun i => le_of_lt (hr i), hx⟩
  have himage :
      -(affineSemigroupNatToInt d m -
        ∑ i, affineSemigroupNatToInt d (a i)) ∈
        affineSemigroupNatToInt d '' (S : Set (Fin d → ℕ)) := by
    change -(affineSemigroupNatToInt d m -
        ∑ i, affineSemigroupNatToInt d (a i)) ∈
      affineSemigroupNatToInt d '' (S : Set (Fin d → ℕ))
    rw [hnormal]
    exact ⟨hG, hC⟩
  exact ⟨himage, hrel⟩

/- accepted add_to_file helper 6 -/
lemma affineSemigroup_exists_apery_reduction
    {d : ℕ}
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    {s : Fin d → ℕ} (hs : s ∈ S) :
    ∃ w : Fin d → ℕ, ∃ n : Fin d → ℕ,
      w ∈ affineSemigroupApery d S a ∧
        s = w + ∑ i, n i • a i := by
  let total : (Fin d → ℕ) → ℕ := fun u => ∑ j, u j
  have step : ∀ N : ℕ, ∀ t : Fin d → ℕ, t ∈ S → total t = N →
      ∃ w : Fin d → ℕ, ∃ n : Fin d → ℕ,
        w ∈ affineSemigroupApery d S a ∧
          t = w + ∑ i, n i • a i := by
    intro N
    refine Nat.strong_induction_on N ?_
    intro N ih t htS htN
    by_cases hAp : ∀ i, ¬∃ p : Fin d → ℕ, p ∈ S ∧ t = p + a i
    · exact ⟨t, 0, ⟨htS, hAp⟩, by simp⟩
    · have hbad : ∃ i, ∃ p : Fin d → ℕ, p ∈ S ∧ t = p + a i := by
        push Not at hAp
        rcases hAp with ⟨i, hi⟩
        exact ⟨i, hi⟩
      rcases hbad with ⟨i, p, hpS, htp⟩
      have haneq : a i ≠ 0 := by
        intro hz
        have hrealne := haLI.ne_zero i
        apply hrealne
        funext j
        simp [hz]
      have hapos : 0 < total (a i) := by
        have hex : ∃ j, a i j ≠ 0 := by
          by_contra hnone
          push Not at hnone
          apply haneq
          funext j
          exact hnone j
        rcases hex with ⟨j, hj⟩
        exact Finset.sum_pos' (fun k hk => Nat.zero_le _)
          ⟨j, Finset.mem_univ j, Nat.pos_of_ne_zero hj⟩
      have htot : total t = total p + total (a i) := by
        rw [htp]
        simp [total, Finset.sum_add_distrib]
      have hlt : total p < N := by
        omega
      have hpN : total p = total p := rfl
      rcases ih (total p) hlt p hpS hpN with ⟨w, n, hw, hpw⟩
      refine ⟨w, fun k => n k + (if k = i then 1 else 0), hw, ?_⟩
      rw [htp, hpw]
      have hsumif : (∑ k, (if k = i then (1 : ℕ) else 0) • a k) = a i := by
        simp
      calc
        (w + ∑ k, n k • a k) + a i
            = w + (∑ k, n k • a k + a i) := by abel
        _ = w + (∑ k, n k • a k + ∑ k, (if k = i then (1 : ℕ) else 0) • a k) := by
          rw [hsumif]
        _ = w + ∑ k, (n k + (if k = i then 1 else 0)) • a k := by
          rw [← Finset.sum_add_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          simp [add_smul]
  exact step (total s) s hs rfl

/- accepted add_to_file helper 7 -/
def affineSemigroupIntCastLinear (d : ℕ) :
    (Fin d → ℤ) →ₗ[ℤ] (Fin d → ℝ) where
  toFun := affineSemigroupIntToReal d
  map_add' := by
    intro x y
    funext j
    simp [affineSemigroupIntToReal]
  map_smul' := by
    intro z x
    funext j
    simp [affineSemigroupIntToReal]

/- accepted add_to_file helper 8 -/
lemma affineSemigroup_int_linearIndependent
    {d : ℕ} {a : Fin d → Fin d → ℕ}
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ))) :
    LinearIndependent ℤ
      (fun i : Fin d => affineSemigroupNatToInt d (a i)) := by
  have hzreal : LinearIndependent ℤ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)) := by
    refine LinearIndependent.restrict_scalars ?_ haLI
    simpa using (Int.cast_injective (α := ℝ))
  refine LinearIndependent.of_comp (affineSemigroupIntCastLinear d) ?_
  simpa [affineSemigroupIntCastLinear, affineSemigroupIntToReal,
    affineSemigroupNatToInt] using hzreal

/- accepted add_to_file helper 9 -/
def affineSemigroupIntegerLattice
    (d : ℕ) (a : Fin d → Fin d → ℕ) : Submodule ℤ (Fin d → ℤ) :=
  Submodule.span ℤ
    (Set.range (fun i : Fin d => affineSemigroupNatToInt d (a i)))

/- accepted add_to_file helper 10 -/
lemma affineSemigroup_finite_quotient_integerLattice
    {d : ℕ} {a : Fin d → Fin d → ℕ}
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ))) :
    Finite ((Fin d → ℤ) ⧸ affineSemigroupIntegerLattice d a) := by
  refine Submodule.finiteQuotientOfFreeOfRankEq
    (affineSemigroupIntegerLattice d a) ?_
  rw [affineSemigroupIntegerLattice,
    finrank_span_eq_card (affineSemigroup_int_linearIndependent haLI),
    Module.finrank_pi, Fintype.card_fin]

/- accepted add_to_file helper 11 -/
lemma affineSemigroup_exists_positive_nsmul_mem_integerLattice
    {d : ℕ} {a : Fin d → Fin d → ℕ}
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    (z : Fin d → ℤ) :
    ∃ n : ℕ, 0 < n ∧ n • z ∈ affineSemigroupIntegerLattice d a := by
  haveI : Finite ((Fin d → ℤ) ⧸ affineSemigroupIntegerLattice d a) :=
    affineSemigroup_finite_quotient_integerLattice haLI
  let q : (Fin d → ℤ) ⧸ affineSemigroupIntegerLattice d a :=
    Submodule.Quotient.mk (p := affineSemigroupIntegerLattice d a) z
  refine ⟨addOrderOf q, addOrderOf_pos q, ?_⟩
  have hq : addOrderOf q • q = 0 := addOrderOf_nsmul_eq_zero q
  have hmk : Submodule.Quotient.mk (p := affineSemigroupIntegerLattice d a)
      (addOrderOf q • z) =
      (0 : (Fin d → ℤ) ⧸ affineSemigroupIntegerLattice d a) := by
    change addOrderOf q •
        (Submodule.Quotient.mk (p := affineSemigroupIntegerLattice d a) z) = 0
    exact hq
  exact (Submodule.Quotient.mk_eq_zero (affineSemigroupIntegerLattice d a)).mp hmk

/- accepted add_to_file helper 12 -/
lemma affineSemigroup_exists_S_sub_mem_integerLattice
    {d : ℕ} {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    {z : Fin d → ℤ} (hz : z ∈ affineSemigroupG d S) :
    ∃ s : Fin d → ℕ, s ∈ S ∧
      z - affineSemigroupNatToInt d s ∈ affineSemigroupIntegerLattice d a := by
  rcases hz with ⟨u, huS, v, hvS, rfl⟩
  rcases affineSemigroup_exists_positive_nsmul_mem_integerLattice haLI
      (affineSemigroupNatToInt d v) with ⟨N, hNpos, hNH⟩
  let s : Fin d → ℕ := u + (N - 1) • v
  have hsS : s ∈ S := S.add_mem huS (S.nsmul_mem hvS (N - 1))
  refine ⟨s, hsS, ?_⟩
  have hcast : affineSemigroupNatToInt d s =
      affineSemigroupNatToInt d u +
        (N - 1) • affineSemigroupNatToInt d v := by
    funext j
    simp [s, affineSemigroupNatToInt]
  have hzcalc :
      (affineSemigroupNatToInt d u - affineSemigroupNatToInt d v) -
          affineSemigroupNatToInt d s =
        -(N • affineSemigroupNatToInt d v) := by
    rw [hcast]
    have hN : N - 1 + 1 = N := Nat.sub_one_add_one_eq_of_pos hNpos
    have hNv : N • affineSemigroupNatToInt d v =
        (N - 1) • affineSemigroupNatToInt d v +
          affineSemigroupNatToInt d v := by
      nth_rewrite 1 [← hN]
      rw [add_nsmul, one_nsmul]
    rw [hNv]
    abel
  rw [hzcalc]
  exact Submodule.neg_mem _ hNH

/- accepted add_to_file helper 13 -/
lemma affineSemigroup_nat_sum_a_mem_integerLattice
    {d : ℕ} {a : Fin d → Fin d → ℕ} (n : Fin d → ℕ) :
    affineSemigroupNatToInt d (∑ i, n i • a i) ∈
      affineSemigroupIntegerLattice d a := by
  rw [affineSemigroupIntegerLattice]
  have hsum : affineSemigroupNatToInt d (∑ i, n i • a i) =
      ∑ i, n i • affineSemigroupNatToInt d (a i) := by
    funext j
    simp [affineSemigroupNatToInt]
  rw [hsum]
  exact Submodule.sum_mem _ (fun i hi =>
    (Submodule.span ℤ
      (Set.range (fun i : Fin d => affineSemigroupNatToInt d (a i)))).toAddSubmonoid.nsmul_mem
      (Submodule.subset_span ⟨i, rfl⟩) (n i))

lemma affineSemigroup_exists_apery_int_coords_of_G
    {d : ℕ} {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    {z : Fin d → ℤ} (hz : z ∈ affineSemigroupG d S) :
    ∃ w : Fin d → ℕ, w ∈ affineSemigroupApery d S a ∧
      ∃ k : Fin d → ℤ,
        z - affineSemigroupNatToInt d w =
          ∑ i, k i • affineSemigroupNatToInt d (a i) := by
  rcases affineSemigroup_exists_S_sub_mem_integerLattice haLI hz with
    ⟨s, hsS, hzsub⟩
  rcases affineSemigroup_exists_apery_reduction haLI hsS with
    ⟨w, n, hw, hsw⟩
  have hsdiff :
      affineSemigroupNatToInt d s - affineSemigroupNatToInt d w ∈
        affineSemigroupIntegerLattice d a := by
    rw [hsw]
    have hcast :
        affineSemigroupNatToInt d (w + ∑ i, n i • a i) -
            affineSemigroupNatToInt d w =
          affineSemigroupNatToInt d (∑ i, n i • a i) := by
      funext j
      simp [affineSemigroupNatToInt]
    rw [hcast]
    exact affineSemigroup_nat_sum_a_mem_integerLattice n
  have hzw : z - affineSemigroupNatToInt d w ∈
      affineSemigroupIntegerLattice d a := by
    have hsum := Submodule.add_mem _ hzsub hsdiff
    convert hsum using 1
    abel
  rw [affineSemigroupIntegerLattice,
    Submodule.mem_span_range_iff_exists_fun] at hzw
  rcases hzw with ⟨k, hk⟩
  exact ⟨w, hw, k, hk.symm⟩

/- accepted add_to_file helper 14 -/
lemma affineSemigroup_image_subset_G_inter_cone
    {d : ℕ}
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))) :
    affineSemigroupNatToInt d '' (S : Set (Fin d → ℕ)) ⊆
      affineSemigroupG d S ∩
        {z | affineSemigroupIntToReal d z ∈ affineSemigroupCone d a} := by
  rintro z ⟨s, hsS, rfl⟩
  constructor
  · refine ⟨s, hsS, 0, S.zero_mem, ?_⟩
    funext j
    simp [affineSemigroupNatToInt]
  · have hmem : affineSemigroupNatToReal d s ∈
        ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
          (S : Set (Fin d → ℕ))) := by
      exact ⟨s, hsS, rfl⟩
    have hhull : affineSemigroupNatToReal d s ∈ ConvexCone.hull ℝ
        ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
          (S : Set (Fin d → ℕ))) :=
      ConvexCone.subset_hull hmem
    have hreal : affineSemigroupIntToReal d (affineSemigroupNatToInt d s) =
        affineSemigroupNatToReal d s := by
      funext j
      simp [affineSemigroupIntToReal, affineSemigroupNatToInt,
        affineSemigroupNatToReal]
    change affineSemigroupIntToReal d (affineSemigroupNatToInt d s) ∈
      affineSemigroupCone d a
    rw [hreal]
    exact (hcone _).mp hhull

/- accepted add_to_file helper 15 -/
lemma affineSemigroup_condition4_implies_normal
    {d : ℕ} (hd : 1 ≤ d)
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haS : ∀ i, a i ∈ S)
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ)))
    (hcond4 : affineSemigroupCondition4 d S a) :
    affineSemigroupNormal d S a := by
  apply Set.Subset.antisymm (affineSemigroup_image_subset_G_inter_cone hcone)
  rintro z ⟨hzG, hzC⟩
  rcases affineSemigroup_exists_apery_int_coords_of_G haLI hzG with
    ⟨w, hwAp, k, hzwk⟩
  rcases hcond4 w hwAp with ⟨c, hc, hxw⟩
  rcases hzC with ⟨q, hq, hxz⟩
  have hHreal : affineSemigroupIntToReal d
        (z - affineSemigroupNatToInt d w) =
      ∑ i, (k i : ℝ) • (fun j : Fin d => (a i j : ℝ)) := by
    rw [hzwk]
    funext j
    simp [affineSemigroupIntToReal, affineSemigroupNatToInt]
  have hknonneg : ∀ i, 0 ≤ k i := by
    intro i
    have hqcoord := affineSemigroup_sum_coords
      (d := d) (hd := hd) (a := a) (haLI := haLI) hxz i
    have hwcoord := affineSemigroup_sum_coords
      (d := d) (hd := hd) (a := a) (haLI := haLI) hxw i
    have hkcoord := affineSemigroup_sum_coords
      (d := d) (hd := hd) (a := a) (haLI := haLI) hHreal i
    have hdiffcast : affineSemigroupIntToReal d
          (z - affineSemigroupNatToInt d w) =
        affineSemigroupIntToReal d z - affineSemigroupNatToReal d w := by
      funext j
      simp [affineSemigroupIntToReal, affineSemigroupNatToInt,
        affineSemigroupNatToReal, Int.cast_sub]
    have hqck : q i - c i = (k i : ℝ) := by
      calc
        q i - c i
            = ((affineSemigroupBasis d hd a haLI).repr
                (affineSemigroupIntToReal d z) i) -
              ((affineSemigroupBasis d hd a haLI).repr
                (affineSemigroupNatToReal d w) i) := by
                  rw [hqcoord, hwcoord]
        _ = ((affineSemigroupBasis d hd a haLI).repr
              (affineSemigroupIntToReal d z -
                affineSemigroupNatToReal d w) i) := by
              simp
        _ = ((affineSemigroupBasis d hd a haLI).repr
              (affineSemigroupIntToReal d
                (z - affineSemigroupNatToInt d w)) i) := by
              rw [hdiffcast]
        _ = (k i : ℝ) := hkcoord
    have hkgt : (-1 : ℝ) < (k i : ℝ) := by
      rw [← hqck]
      have hq0 := hq i
      have hc1 := (hc i).2
      linarith
    have hkgtint : -1 < k i := by
      exact_mod_cast hkgt
    omega
  let n : Fin d → ℕ := fun i => Int.toNat (k i)
  have hnk : ∀ i, ((n i : ℤ) = k i) := by
    intro i
    exact Int.toNat_of_nonneg (hknonneg i)
  have hsumk : (∑ i, k i • affineSemigroupNatToInt d (a i)) =
      affineSemigroupNatToInt d (∑ i, n i • a i) := by
    funext j
    simp [n, affineSemigroupNatToInt, hnk]
  have hzeq : z =
      affineSemigroupNatToInt d (w + ∑ i, n i • a i) := by
    have hz1 : z = affineSemigroupNatToInt d w +
        ∑ i, k i • affineSemigroupNatToInt d (a i) := by
      calc
        z = (z - affineSemigroupNatToInt d w) +
            affineSemigroupNatToInt d w := by abel
        _ = (∑ i, k i • affineSemigroupNatToInt d (a i)) +
            affineSemigroupNatToInt d w := by rw [hzwk]
        _ = affineSemigroupNatToInt d w +
            ∑ i, k i • affineSemigroupNatToInt d (a i) := by abel
    rw [hz1, hsumk]
    funext j
    simp [affineSemigroupNatToInt]
  have hsumS : (∑ i, n i • a i) ∈ S := by
    exact S.sum_mem (fun i hi => S.nsmul_mem (haS i) (n i))
  have htS : w + ∑ i, n i • a i ∈ S :=
    S.add_mem hwAp.1 hsumS
  exact ⟨w + ∑ i, n i • a i, htS, hzeq.symm⟩

/- accepted add_to_file helper 16 -/
lemma affineSemigroup_eq_add_sum_a_of_int_sub
    {d : ℕ} {a : Fin d → Fin d → ℕ}
    {w₁ w₂ : Fin d → ℕ} {k : Fin d → ℤ}
    (hk : ∀ i, 0 ≤ k i)
    (h : affineSemigroupNatToInt d w₂ - affineSemigroupNatToInt d w₁ =
      ∑ i, k i • affineSemigroupNatToInt d (a i)) :
    w₂ = w₁ + ∑ i, Int.toNat (k i) • a i := by
  let n : Fin d → ℕ := fun i => Int.toNat (k i)
  have hnk : ∀ i, ((n i : ℤ) = k i) := by
    intro i
    exact Int.toNat_of_nonneg (hk i)
  have hsumk : (∑ i, k i • affineSemigroupNatToInt d (a i)) =
      affineSemigroupNatToInt d (∑ i, n i • a i) := by
    funext j
    simp [n, affineSemigroupNatToInt, hnk]
  have hzeq : affineSemigroupNatToInt d w₂ =
      affineSemigroupNatToInt d (w₁ + ∑ i, n i • a i) := by
    have hz1 : affineSemigroupNatToInt d w₂ =
        affineSemigroupNatToInt d w₁ +
          ∑ i, k i • affineSemigroupNatToInt d (a i) := by
      calc
        affineSemigroupNatToInt d w₂ =
            (affineSemigroupNatToInt d w₂ -
              affineSemigroupNatToInt d w₁) +
              affineSemigroupNatToInt d w₁ := by abel
        _ = (∑ i, k i • affineSemigroupNatToInt d (a i)) +
              affineSemigroupNatToInt d w₁ := by rw [h]
        _ = affineSemigroupNatToInt d w₁ +
              ∑ i, k i • affineSemigroupNatToInt d (a i) := by abel
    rw [hz1, hsumk]
    funext j
    simp [affineSemigroupNatToInt]
  funext j
  apply Nat.cast_injective (R := ℤ)
  change (w₂ j : ℤ) = ((w₁ + ∑ i, n i • a i) j : ℤ)
  simpa [affineSemigroupNatToInt] using congrFun hzeq j

/- accepted add_to_file helper 17 -/
lemma affineSemigroup_sum_nat_smul_eq_add_a
    {d : ℕ} {S : AddSubmonoid (Fin d → ℕ)}
    {a : Fin d → Fin d → ℕ}
    (haS : ∀ i, a i ∈ S) {n : Fin d → ℕ}
    {i : Fin d} (hi : 0 < n i) :
    ∃ t : Fin d → ℕ, t ∈ S ∧
      ∑ k, n k • a k = t + a i := by
  let m : Fin d → ℕ := fun k => if k = i then n k - 1 else n k
  refine ⟨∑ k, m k • a k, ?_, ?_⟩
  · exact S.sum_mem (fun k hk => S.nsmul_mem (haS k) (m k))
  · have hn : n = fun k => m k + (if k = i then 1 else 0) := by
      funext k
      by_cases hk : k = i
      · simp [m, hk, Nat.sub_add_cancel hi]
      · simp [m, hk]
    calc
      ∑ k, n k • a k
          = ∑ k, (m k + (if k = i then 1 else 0)) • a k := by rw [hn]
      _ = ∑ k, m k • a k + ∑ k, (if k = i then (1 : ℕ) else 0) • a k := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k hk
          simp [add_smul]
      _ = ∑ k, m k • a k + a i := by simp

/- accepted add_to_file helper 18 -/
lemma affineSemigroup_apery_fiber_finite
    {d : ℕ} (hd : 1 ≤ d)
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haS : ∀ i, a i ∈ S)
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ)))
    (Q : (Fin d → ℤ) ⧸ affineSemigroupIntegerLattice d a) :
    {w : Fin d → ℕ | w ∈ affineSemigroupApery d S a ∧
      Submodule.Quotient.mk (p := affineSemigroupIntegerLattice d a)
        (affineSemigroupNatToInt d w) = Q}.Finite := by
  let F : Set (Fin d → ℕ) :=
    {w | w ∈ affineSemigroupApery d S a ∧
      Submodule.Quotient.mk (p := affineSemigroupIntegerLattice d a)
        (affineSemigroupNatToInt d w) = Q}
  change F.Finite
  obtain ⟨z₀, hz₀⟩ := Submodule.Quotient.mk_surjective
    (p := affineSemigroupIntegerLattice d a) Q
  have hkexists : ∀ w : F, ∃ k : Fin d → ℤ,
      affineSemigroupNatToInt d w - z₀ =
        ∑ i, k i • affineSemigroupNatToInt d (a i) := by
    intro w
    have hmk :
        Submodule.Quotient.mk (p := affineSemigroupIntegerLattice d a)
          (affineSemigroupNatToInt d w) =
        Submodule.Quotient.mk (p := affineSemigroupIntegerLattice d a) z₀ := by
      rw [w.2.2, hz₀]
    have hmem : affineSemigroupNatToInt d w - z₀ ∈
        affineSemigroupIntegerLattice d a :=
      (Submodule.Quotient.eq (affineSemigroupIntegerLattice d a)).mp hmk
    rw [affineSemigroupIntegerLattice,
      Submodule.mem_span_range_iff_exists_fun] at hmem
    rcases hmem with ⟨k, hk⟩
    exact ⟨k, hk.symm⟩
  let kfun : F → (Fin d → ℤ) := fun w => Classical.choose (hkexists w)
  have hkfun : ∀ w : F,
      affineSemigroupNatToInt d w - z₀ =
        ∑ i, kfun w i • affineSemigroupNatToInt d (a i) :=
    fun w => Classical.choose_spec (hkexists w)
  let b := affineSemigroupBasis d hd a haLI
  let q₀ : Fin d → ℝ := fun i =>
    b.repr (affineSemigroupIntToReal d z₀) i
  have hcoord : ∀ (w : F) (i : Fin d),
      b.repr (affineSemigroupIntToReal d (affineSemigroupNatToInt d w)) i =
        q₀ i + (kfun w i : ℝ) := by
    intro w i
    have hHreal : affineSemigroupIntToReal d
          (affineSemigroupNatToInt d w - z₀) =
        ∑ j, (kfun w j : ℝ) • (fun l : Fin d => (a j l : ℝ)) := by
      rw [hkfun w]
      funext j
      simp [affineSemigroupIntToReal, affineSemigroupNatToInt]
    have hkcoord := affineSemigroup_sum_coords
      (d := d) (hd := hd) (a := a) (haLI := haLI) hHreal i
    have hdiffcast : affineSemigroupIntToReal d
          (affineSemigroupNatToInt d w - z₀) =
        affineSemigroupIntToReal d (affineSemigroupNatToInt d w) -
          affineSemigroupIntToReal d z₀ := by
      funext j
      simp [affineSemigroupIntToReal, affineSemigroupNatToInt, Int.cast_sub]
    calc
      b.repr (affineSemigroupIntToReal d (affineSemigroupNatToInt d w)) i
          = (b.repr (affineSemigroupIntToReal d
              (affineSemigroupNatToInt d w - z₀)) i) +
            b.repr (affineSemigroupIntToReal d z₀) i := by
              rw [hdiffcast]
              simp
      _ = q₀ i + (kfun w i : ℝ) := by
              rw [hkcoord]
              simp [q₀, add_comm]
  have hlower : ∀ (w : F) (i : Fin d),
      Int.ceil (-(q₀ i)) ≤ kfun w i := by
    intro w i
    have hqnonneg := affineSemigroup_S_coord_nonneg
      (d := d) (hd := hd) (S := S) (a := a) (haLI := haLI) hcone
      w.2.1.1 i
    have hcast :
        affineSemigroupIntToReal d (affineSemigroupNatToInt d w) =
          affineSemigroupNatToReal d w := by
      funext j
      simp [affineSemigroupIntToReal, affineSemigroupNatToInt,
        affineSemigroupNatToReal]
    have hq : q₀ i + (kfun w i : ℝ) ≥ 0 := by
      rw [← hcoord w i, hcast]
      exact hqnonneg
    apply (Int.ceil_le).mpr
    linarith
  let mK : Fin d → ℤ := fun i => Int.ceil (-(q₀ i))
  let nfun : F → (Fin d → ℕ) := fun w i =>
    Int.toNat (kfun w i - mK i)
  have hnge : ∀ (w : F) (i : Fin d), 0 ≤ kfun w i - mK i := by
    intro w i
    exact sub_nonneg.mpr (hlower w i)
  have hnfun_cast : ∀ (w : F) (i : Fin d),
      ((nfun w i : ℤ) = kfun w i - mK i) := by
    intro w i
    exact Int.toNat_of_nonneg (hnge w i)
  have hninj : Function.Injective nfun := by
    intro x y hxy
    have hksame : kfun x = kfun y := by
      funext i
      have hi := congrFun hxy i
      have hx := hnfun_cast x i
      have hy := hnfun_cast y i
      have : ((nfun x i : ℤ) = (nfun y i : ℤ)) := by rw [hi]
      omega
    apply Subtype.ext
    have hint : affineSemigroupNatToInt d x = affineSemigroupNatToInt d y := by
      have hx := hkfun x
      have hy := hkfun y
      rw [hksame] at hx
      calc
        affineSemigroupNatToInt d x =
            (affineSemigroupNatToInt d x - z₀) + z₀ := by abel
        _ = (affineSemigroupNatToInt d y - z₀) + z₀ := by rw [hx, hy]
        _ = affineSemigroupNatToInt d y := by abel
    funext j
    have hj := congrFun hint j
    change ((x : Fin d → ℕ) j : ℤ) = ((y : Fin d → ℕ) j : ℤ) at hj
    exact Nat.cast_injective (R := ℤ) hj
  have hanti : IsAntichain (· ≤ ·) (Set.range nfun) := by
    intro x hx y hy hne hxy
    rcases hx with ⟨X, rfl⟩
    rcases hy with ⟨Y, rfl⟩
    have hkle : ∀ i, kfun X i ≤ kfun Y i := by
      intro i
      have hi := hxy i
      have hX := hnfun_cast X i
      have hY := hnfun_cast Y i
      have hcast : ((nfun X i : ℤ) ≤ (nfun Y i : ℤ)) := by exact_mod_cast hi
      omega
    by_cases hksame : kfun X = kfun Y
    · apply hne
      funext i
      have hX := hnfun_cast X i
      have hY := hnfun_cast Y i
      have hk : kfun X i - mK i = kfun Y i - mK i := by rw [hksame]
      have hcast :
          ((nfun X i : ℤ) = (nfun Y i : ℤ)) := by omega
      exact Nat.cast_injective (R := ℤ) hcast
    · have hex : ∃ i, kfun X i ≠ kfun Y i := by
        by_contra h
        push Not at h
        apply hksame
        funext i
        exact h i
      rcases hex with ⟨i, hi⟩
      have hlt : kfun X i < kfun Y i := lt_of_le_of_ne (hkle i) hi
      let kd : Fin d → ℤ := fun j => kfun Y j - kfun X j
      have hkd : ∀ j, 0 ≤ kd j := by
        intro j
        exact sub_nonneg.mpr (hkle j)
      have hdiff :
          affineSemigroupNatToInt d Y - affineSemigroupNatToInt d X =
            ∑ j, kd j • affineSemigroupNatToInt d (a j) := by
        have hXH := hkfun X
        have hYH := hkfun Y
        calc
          affineSemigroupNatToInt d Y - affineSemigroupNatToInt d X
              = (affineSemigroupNatToInt d Y - z₀) -
                (affineSemigroupNatToInt d X - z₀) := by abel
          _ = (∑ j, kfun Y j • affineSemigroupNatToInt d (a j)) -
              (∑ j, kfun X j • affineSemigroupNatToInt d (a j)) := by
                rw [hYH, hXH]
          _ = ∑ j, kd j • affineSemigroupNatToInt d (a j) := by
                simp [kd, Finset.sum_sub_distrib, sub_smul]
      have hnat := affineSemigroup_eq_add_sum_a_of_int_sub hkd hdiff
      let nd : Fin d → ℕ := fun j => Int.toNat (kd j)
      have hndi : 0 < nd i := by
        have hpos : 0 < kd i := sub_pos.mpr hlt
        change 0 < Int.toNat (kd i)
        have hcast := Int.toNat_of_nonneg (le_of_lt hpos)
        omega
      rcases affineSemigroup_sum_nat_smul_eq_add_a haS hndi with ⟨t, htS, hsumt⟩
      have hpre : (Y : Fin d → ℕ) = ((X : Fin d → ℕ) + t) + a i := by
        calc
          (Y : Fin d → ℕ) = (X : Fin d → ℕ) + ∑ j, nd j • a j := hnat
          _ = (X : Fin d → ℕ) + (t + a i) := by rw [hsumt]
          _ = ((X : Fin d → ℕ) + t) + a i := by abel
      exact Y.property.1.2 i ⟨X + t, S.add_mem X.property.1.1 htS, hpre⟩
  have hPWO : (Set.range nfun).PartiallyWellOrderedOn (· ≤ ·) :=
    Set.partiallyWellOrderedOn_of_wellQuasiOrdered wellQuasiOrdered_le
      (Set.range nfun)
  have hrange : (Set.range nfun).Finite :=
    hanti.finite_of_partiallyWellOrderedOn hPWO
  have hfinite : Finite F := (Set.finite_range_iff hninj).mp hrange
  exact Set.finite_coe_iff.mp hfinite

/- accepted add_to_file helper 19 -/
lemma affineSemigroup_apery_finite
    {d : ℕ} (hd : 1 ≤ d)
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haS : ∀ i, a i ∈ S)
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))) :
    (affineSemigroupApery d S a).Finite := by
  haveI : Finite ((Fin d → ℤ) ⧸ affineSemigroupIntegerLattice d a) :=
    affineSemigroup_finite_quotient_integerLattice haLI
  let F : ((Fin d → ℤ) ⧸ affineSemigroupIntegerLattice d a) →
      Set (Fin d → ℕ) :=
    fun Q => {w | w ∈ affineSemigroupApery d S a ∧
      Submodule.Quotient.mk (p := affineSemigroupIntegerLattice d a)
        (affineSemigroupNatToInt d w) = Q}
  have hAp : affineSemigroupApery d S a = ⋃ Q, F Q := by
    ext w
    constructor
    · intro hw
      refine Set.mem_iUnion.mpr ?_
      exact ⟨_, hw, rfl⟩
    · intro hw
      rcases Set.mem_iUnion.mp hw with ⟨Q, hwQ⟩
      exact hwQ.1
  rw [hAp]
  exact Set.finite_iUnion (fun Q =>
    affineSemigroup_apery_fiber_finite hd haS haLI hcone Q)

/- accepted add_to_file helper 20 -/
lemma affineSemigroup_exists_maximal_apery_above
    {d : ℕ} (hd : 1 ≤ d)
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haS : ∀ i, a i ∈ S)
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ)))
    {w : Fin d → ℕ} (hw : w ∈ affineSemigroupApery d S a) :
    ∃ m : Fin d → ℕ,
      affineSemigroupLeS d S w m ∧
        affineSemigroupMaximalApery d S a m := by
  letI : Preorder (Fin d → ℕ) :=
    { le := affineSemigroupLeS d S
      lt := fun u v => affineSemigroupLeS d S u v ∧
        ¬affineSemigroupLeS d S v u
      le_refl := by
        intro u
        exact ⟨0, S.zero_mem, by simp⟩
      le_trans := by
        intro u v t huv hvt
        rcases huv with ⟨s, hsS, hv⟩
        rcases hvt with ⟨r, hrS, ht⟩
        refine ⟨s + r, S.add_mem hsS hrS, ?_⟩
        rw [ht, hv]
        abel
      lt_iff_le_not_ge := by
        intro u v
        rfl }
  have hfinite := affineSemigroup_apery_finite hd haS haLI hcone
  rcases hfinite.exists_le_maximal hw with ⟨m, hwm, hm⟩
  refine ⟨m, hwm, hm.1, ?_⟩
  intro x hx hmx
  exact hm.2 hx hmx

/- accepted add_to_file helper 21 -/
lemma affineSemigroup_condition3_implies_condition4
    {d : ℕ} (hd : 1 ≤ d)
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haS : ∀ i, a i ∈ S)
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ)))
    (hcond3 : affineSemigroupCondition3 d S a) :
    affineSemigroupCondition4 d S a := by
  intro w hw
  rcases affineSemigroup_exists_maximal_apery_above
    (d := d) (hd := hd) (S := S) (a := a) (haLI := haLI)
    haS hcone hw with ⟨m, hwm, hmax⟩
  let f : Fin d → ℤ := affineSemigroupNatToInt d m -
    ∑ i, affineSemigroupNatToInt d (a i)
  have hfQF : f ∈ affineSemigroupQF d S a := by
    exact ⟨m, hmax, rfl⟩
  rcases hcond3 f hfQF with ⟨r, hr, hxr⟩
  let b := affineSemigroupBasis d hd a haLI
  have hm_lt_one : ∀ i,
      b.repr (affineSemigroupNatToReal d m) i < 1 := by
    intro i
    have hnegreal : affineSemigroupIntToReal d (-f) =
        (∑ k, (1 : ℝ) • (fun j : Fin d => (a k j : ℝ))) -
          affineSemigroupNatToReal d m := by
      funext j
      simp [f, affineSemigroupIntToReal, affineSemigroupNatToInt,
        affineSemigroupNatToReal]
    have hsumrepr :
        (∑ c, (b.repr (fun j : Fin d => (a c j : ℝ))) i) = 1 := by
      calc
        (∑ c, (b.repr (fun j : Fin d => (a c j : ℝ))) i)
            = ∑ c, (b.repr (b c)) i := by
              apply Finset.sum_congr rfl
              intro c hc
              rw [affineSemigroupBasis_apply d hd a haLI]
        _ = 1 := by simp
    have hcoordneg :
        b.repr (affineSemigroupIntToReal d (-f)) i =
          1 - b.repr (affineSemigroupNatToReal d m) i := by
      rw [hnegreal]
      simp [hsumrepr]
    have hrcoord := affineSemigroup_sum_coords
      (d := d) (hd := hd) (a := a) (haLI := haLI) hxr i
    rw [hcoordneg] at hrcoord
    have hri := hr i
    linarith
  have hw_nonneg : ∀ i,
      0 ≤ b.repr (affineSemigroupNatToReal d w) i := by
    intro i
    exact affineSemigroup_S_coord_nonneg
      (d := d) (hd := hd) (S := S) (a := a) (haLI := haLI) hcone hw.1 i
  have hw_le_m : ∀ i,
      b.repr (affineSemigroupNatToReal d w) i ≤
        b.repr (affineSemigroupNatToReal d m) i := by
    intro i
    rcases hwm with ⟨s, hsS, hm⟩
    have hs_nonneg := affineSemigroup_S_coord_nonneg
      (d := d) (hd := hd) (S := S) (a := a) (haLI := haLI) hcone hsS i
    have hmreal : affineSemigroupNatToReal d m =
        affineSemigroupNatToReal d w + affineSemigroupNatToReal d s := by
      rw [hm]
      funext j
      simp [affineSemigroupNatToReal]
    have hcoord := congrArg (fun x : Fin d → ℝ =>
        b.repr x i) hmreal
    simp at hcoord
    rw [hcoord]
    linarith
  let q : Fin d → ℝ := fun i =>
    b.repr (affineSemigroupNatToReal d w) i
  refine ⟨q, ?_, ?_⟩
  · intro i
    exact ⟨hw_nonneg i, lt_of_le_of_lt (hw_le_m i) (hm_lt_one i)⟩
  · calc
      affineSemigroupNatToReal d w =
          ∑ i, q i • b i := by
            symm
            exact b.sum_repr (affineSemigroupNatToReal d w)
      _ = ∑ i, q i • (fun j : Fin d => (a i j : ℝ)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [affineSemigroupBasis_apply d hd a haLI]

/- verified submission -/
theorem affineSemigroup_normal_equiv
    (d : ℕ) (hd : 1 ≤ d)
    (S : AddSubmonoid (Fin d → ℕ)) (hSfg : S.FG)
    (a : Fin d → Fin d → ℕ)
    (haS : ∀ i, a i ∈ S)
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ)))
    (hminray : ∀ (i : Fin d) (u : Fin d → ℕ),
      u ∈ S → u ≠ 0 →
      (∃ r : ℝ, 0 ≤ r ∧
        (fun j : Fin d => (u j : ℝ)) =
          r • (fun j : Fin d => (a i j : ℝ))) →
      ∀ j, a i j ≤ u j) :
    let natToInt : (Fin d → ℕ) → (Fin d → ℤ) :=
      fun u j => (u j : ℤ)
    let natToReal : (Fin d → ℕ) → (Fin d → ℝ) :=
      fun u j => (u j : ℝ)
    let intToReal : (Fin d → ℤ) → (Fin d → ℝ) :=
      fun u j => (u j : ℝ)
    let C : Set (Fin d → ℝ) :=
      {x | ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
        x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))}
    let relintC : Set (Fin d → ℝ) :=
      {x | ∃ c : Fin d → ℝ, (∀ i, 0 < c i) ∧
        x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))}
    let fundamentalParallelepiped : Set (Fin d → ℝ) :=
      {x | ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i ∧ c i < 1) ∧
        x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))}
    let apery : Set (Fin d → ℕ) :=
      {w | w ∈ S ∧ ∀ i, ¬∃ s : Fin d → ℕ, s ∈ S ∧ w = s + a i}
    let leS : (Fin d → ℕ) → (Fin d → ℕ) → Prop :=
      fun u v => ∃ s : Fin d → ℕ, s ∈ S ∧ v = u + s
    let maximalApery : (Fin d → ℕ) → Prop :=
      fun m => m ∈ apery ∧
        ∀ w, w ∈ apery → leS m w → leS w m
    let QF : Set (Fin d → ℤ) :=
      {f | ∃ m, maximalApery m ∧
        f = natToInt m - ∑ i, natToInt (a i)}
    let G : Set (Fin d → ℤ) :=
      {z | ∃ u : Fin d → ℕ, u ∈ S ∧
        ∃ v : Fin d → ℕ, v ∈ S ∧ z = natToInt u - natToInt v}
    let normal : Prop :=
      natToInt '' (S : Set (Fin d → ℕ)) =
        G ∩ {z | intToReal z ∈ C}
    let condition2 : Prop :=
      ∀ f, f ∈ QF →
        -f ∈ natToInt '' (S : Set (Fin d → ℕ)) ∧
          intToReal (-f) ∈ relintC
    let condition3 : Prop :=
      ∀ f, f ∈ QF → intToReal (-f) ∈ relintC
    let condition4 : Prop :=
      ∀ w, w ∈ apery → natToReal w ∈ fundamentalParallelepiped
    (normal ↔ condition2) ∧ (normal ↔ condition3) ∧ (normal ↔ condition4) := by
  change (affineSemigroupNormal d S a ↔ affineSemigroupCondition2 d S a) ∧
    (affineSemigroupNormal d S a ↔ affineSemigroupCondition3 d S a) ∧
    (affineSemigroupNormal d S a ↔ affineSemigroupCondition4 d S a)
  have h34 : affineSemigroupCondition3 d S a →
      affineSemigroupCondition4 d S a := by
    intro h3
    exact affineSemigroup_condition3_implies_condition4
      (d := d) (hd := hd) (S := S) (a := a) (haLI := haLI)
      haS hcone h3
  have h4N : affineSemigroupCondition4 d S a →
      affineSemigroupNormal d S a := by
    intro h4
    exact affineSemigroup_condition4_implies_normal
      (d := d) (hd := hd) (S := S) (a := a)
      haS haLI hcone h4
  have hN2 : affineSemigroupNormal d S a →
      affineSemigroupCondition2 d S a := by
    intro hN
    exact affineSemigroup_normal_implies_condition2
      (d := d) (hd := hd) (S := S) (a := a) (haLI := haLI)
      haS hcone hN
  constructor
  · constructor
    · exact hN2
    · intro h2
      exact h4N (h34 (fun f hf => (h2 f hf).2))
  · constructor
    · constructor
      · intro hN f hf
        exact (hN2 hN f hf).2
      · intro h3
        exact h4N (h34 h3)
    · constructor
      · intro hN w hw
        exact affineSemigroup_normal_implies_condition4
          (d := d) (hd := hd) (S := S) (a := a) (haLI := haLI)
          haS hcone hN hw
      · exact h4N

end Rollout_p0130_affinesemigroup_normal_equiv
