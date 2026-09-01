import Mathlib

/- accepted add_to_file helper 1 -/
import Mathlib.MeasureTheory.Integral.Bochner.Basic

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
