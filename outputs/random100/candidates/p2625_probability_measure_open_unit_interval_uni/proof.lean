import Mathlib

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
