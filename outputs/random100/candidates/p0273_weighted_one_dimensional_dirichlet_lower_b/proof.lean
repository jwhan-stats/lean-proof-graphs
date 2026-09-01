import Mathlib

/- accepted add_to_file helper 1 -/
open MeasureTheory
open scoped Interval

lemma l2_cauchy_schwarz_integral {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    {u v : X → ℝ} (hu : MeasureTheory.MemLp u 2 μ) (hv : MeasureTheory.MemLp v 2 μ) :
    (∫ x, u x * v x ∂μ) ^ 2 ≤
      (∫ x, u x ^ 2 ∂μ) * (∫ x, v x ^ 2 ∂μ) := by
  let A : ℝ := ∫ x, u x ^ 2 ∂μ
  let B : ℝ := ∫ x, v x ^ 2 ∂μ
  let I : ℝ := ∫ x, u x * v x ∂μ
  have hu2 : MeasureTheory.Integrable (fun x => u x ^ 2) μ := hu.integrable_sq
  have hv2 : MeasureTheory.Integrable (fun x => v x ^ 2) μ := hv.integrable_sq
  have huv : MeasureTheory.Integrable (fun x => u x * v x) μ := hu.integrable_mul hv
  have hquad (t : ℝ) : 0 ≤ t ^ 2 * A - 2 * t * I + B := by
    have hnon : 0 ≤ ∫ x, (t * u x - v x) ^ 2 ∂μ := by
      exact MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
    have hexp : (∫ x, (t * u x - v x) ^ 2 ∂μ) = t ^ 2 * A - 2 * t * I + B := by
      calc
        (∫ x, (t * u x - v x) ^ 2 ∂μ)
            = ∫ x, (t ^ 2 * (u x ^ 2) + (-(2 * t)) * (u x * v x)) + v x ^ 2 ∂μ := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards with x
              ring
        _ = (∫ x, t ^ 2 * (u x ^ 2) + (-(2 * t)) * (u x * v x) ∂μ) + ∫ x, v x ^ 2 ∂μ := by
          exact MeasureTheory.integral_add ((hu2.const_mul (t ^ 2)).add (huv.const_mul (-(2 * t)))) hv2
        _ = ((∫ x, t ^ 2 * (u x ^ 2) ∂μ) + ∫ x, (-(2 * t)) * (u x * v x) ∂μ) + ∫ x, v x ^ 2 ∂μ := by
          rw [MeasureTheory.integral_add (hu2.const_mul (t ^ 2)) (huv.const_mul (-(2 * t)))]
        _ = t ^ 2 * A - 2 * t * I + B := by
          rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
          dsimp [A, B, I]
          ring
    rwa [hexp] at hnon
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  change I ^ 2 ≤ A * B
  by_cases hAeq : A = 0
  · have hIeq : I = 0 := by
      by_contra hI0
      have ht := hquad ((B + 1) / (2 * I))
      rw [hAeq] at ht
      have hcalc : ((B + 1) / (2 * I)) ^ 2 * 0 - 2 * ((B + 1) / (2 * I)) * I + B = -1 := by
        field_simp [hI0]
        ring_nf
      linarith
    rw [hAeq, hIeq]
    simp
  · have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hAeq)
    have ht := hquad (I / A)
    have hcalc : (I / A) ^ 2 * A - 2 * (I / A) * I + B = B - I ^ 2 / A := by
      field_simp [hAeq]
      ring_nf
    rw [hcalc] at ht
    have hmul := mul_nonneg ht hApos.le
    have hcalc2 : (B - I ^ 2 / A) * A = B * A - I ^ 2 := by
      field_simp [hAeq]
    rw [hcalc2] at hmul
    nlinarith

/- accepted add_to_file helper 2 -/
lemma integral_inv_eq_of_two_valued_on_interval
    (b θ₀ : ℝ) (α : ℝ → ℝ)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hθ0 : 0 < θ₀) (hθ1 : θ₀ < 2 * Real.pi)
    (hαmeas : AEMeasurable α
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))))
    (hαvalues : ∀ᵐ θ ∂(MeasureTheory.volume.restrict
      (Set.Icc (0 : ℝ) (2 * Real.pi))), α θ ∈ ({b ^ 2, 1} : Set ℝ))
    (hαmeasure : (MeasureTheory.volume.restrict
      (Set.Icc (0 : ℝ) (2 * Real.pi))) {θ | α θ = b ^ 2} = ENNReal.ofReal θ₀) :
    ∫ θ, (α θ)⁻¹ ∂(MeasureTheory.volume.restrict
      (Set.Icc (0 : ℝ) (2 * Real.pi))) =
      2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1) := by
  classical
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict
    (Set.Icc (0 : ℝ) (2 * Real.pi))
  let β : ℝ → ℝ := AEMeasurable.mk α hαmeas
  let A : Set ℝ := {θ | β θ = b ^ 2}
  let q : ℝ → ℝ := A.piecewise (fun _ => (b ^ 2)⁻¹) (fun _ => 1)
  have hβmeas : Measurable β := hαmeas.measurable_mk
  have hA : MeasurableSet A := hβmeas (measurableSet_singleton _)
  have hβae : α =ᵐ[μ] β := hαmeas.ae_eq_mk
  have hβvalues : ∀ᵐ θ ∂μ, β θ ∈ ({b ^ 2, 1} : Set ℝ) := by
    filter_upwards [hαvalues, hβae] with θ hθ h_eq
    simpa [h_eq] using hθ
  have hsets : ({θ | α θ = b ^ 2} : Set ℝ) =ᵐ[μ] A := by
    filter_upwards [hβae] with θ h_eq
    apply propext
    constructor
    · intro h
      change β θ = b ^ 2
      rw [← h_eq]
      exact h
    · intro h
      change α θ = b ^ 2
      rw [h_eq]
      exact h
  have hAmeasure : μ A = ENNReal.ofReal θ₀ := by
    rw [← MeasureTheory.measure_congr hsets]
    exact hαmeasure
  have hμuniv : μ Set.univ = ENNReal.ofReal (2 * Real.pi) := by
    dsimp [μ]
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Icc]
    congr 1
    ring
  have hAfin : μ A ≠ ⊤ := by
    rw [hAmeasure]
    simp
  have hAcomp : μ Aᶜ = ENNReal.ofReal (2 * Real.pi - θ₀) := by
    rw [MeasureTheory.measure_compl hA hAfin, hμuniv, hAmeasure,
      ← ENNReal.ofReal_sub _ hθ0.le]
  have hAreal : μ.real A = θ₀ := by
    rw [MeasureTheory.measureReal_def, hAmeasure, ENNReal.toReal_ofReal hθ0.le]
  have hAcompreal : μ.real Aᶜ = 2 * Real.pi - θ₀ := by
    rw [MeasureTheory.measureReal_def, hAcomp,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hθ1.le)]
  have hαβinv : (fun θ => (α θ)⁻¹) =ᵐ[μ] (fun θ => (β θ)⁻¹) := by
    filter_upwards [hβae] with θ h_eq
    rw [h_eq]
  have hb2lt1 : b ^ 2 < 1 := by nlinarith
  have hb2ne1 : b ^ 2 ≠ 1 := ne_of_lt hb2lt1
  have hβq : (fun θ => (β θ)⁻¹) =ᵐ[μ] q := by
    filter_upwards [hβvalues] with θ hθ
    rcases hθ with hθ | hθ
    · have hmem : θ ∈ A := hθ
      simpa [q, hθ] using
        (Set.piecewise_eq_of_mem A (fun _ : ℝ => (b ^ 2)⁻¹) (fun _ : ℝ => 1) hmem).symm
    · have hθeq : β θ = 1 := by simpa using hθ
      have hnot : θ ∉ A := by
        intro hmem
        dsimp [A] at hmem
        rw [hθeq] at hmem
        exact hb2ne1 hmem.symm
      simpa [q, hθeq] using
        (Set.piecewise_eq_of_notMem A (fun _ : ℝ => (b ^ 2)⁻¹) (fun _ : ℝ => 1) hnot).symm
  have hic : MeasureTheory.IntegrableOn (fun _ : ℝ => (b ^ 2)⁻¹) A μ :=
    (integrable_const _).integrableOn
  have hid : MeasureTheory.IntegrableOn (fun _ : ℝ => (1 : ℝ)) Aᶜ μ :=
    (integrable_const _).integrableOn
  calc
    ∫ θ, (α θ)⁻¹ ∂μ = ∫ θ, (β θ)⁻¹ ∂μ :=
      MeasureTheory.integral_congr_ae hαβinv
    _ = ∫ θ, q θ ∂μ := MeasureTheory.integral_congr_ae hβq
    _ = (∫ θ in A, (b ^ 2)⁻¹ ∂μ) + ∫ θ in Aᶜ, (1 : ℝ) ∂μ := by
      dsimp [q]
      exact MeasureTheory.integral_piecewise hA hic hid
    _ = μ.real A * (b ^ 2)⁻¹ + μ.real Aᶜ := by
      rw [MeasureTheory.setIntegral_const, MeasureTheory.setIntegral_const]
      simp [smul_eq_mul]
    _ = 2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1) := by
      rw [hAreal, hAcompreal]
      ring

/- accepted add_to_file helper 3 -/
lemma weighted_l1_sq_le_weighted_l2_mul_inv
    {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    [MeasureTheory.IsFiniteMeasure μ]
    (b : ℝ) (α g : X → ℝ)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hαmeas : AEMeasurable α μ)
    (hαvalues : ∀ᵐ x ∂μ, α x ∈ ({b ^ 2, 1} : Set ℝ))
    (hg : MeasureTheory.MemLp g 2 μ) :
    (∫ x, |g x| ∂μ) ^ 2 ≤
      (∫ x, α x * |g x| ^ 2 ∂μ) * ∫ x, (α x)⁻¹ ∂μ := by
  let u : X → ℝ := fun x => √(α x) * |g x|
  let v : X → ℝ := fun x => √((α x)⁻¹)
  have hαpos_of_val : ∀ {x : X}, α x ∈ ({b ^ 2, 1} : Set ℝ) → 0 < α x := by
    intro x hx
    rcases hx with hx | hx
    · rw [hx]
      exact sq_pos_of_pos hb0
    · have hx1 : α x = 1 := by simpa using hx
      rw [hx1]
      norm_num
  have hu : MeasureTheory.MemLp u 2 μ := by
    apply MeasureTheory.MemLp.mono hg.abs
    · exact (hαmeas.sqrt.mul hg.aemeasurable.abs).aestronglyMeasurable
    · filter_upwards [hαvalues] with x hx
      have hsqrt_nonneg : 0 ≤ √(α x) := Real.sqrt_nonneg _
      have hsqrt_le_one : √(α x) ≤ 1 := by
        rcases hx with hx | hx
        · rw [hx, Real.sqrt_sq hb0.le]
          exact hb1.le
        · have hx1 : α x = 1 := by simpa using hx
          rw [hx1]
          simp
      dsimp [u]
      rw [abs_mul, abs_of_nonneg hsqrt_nonneg, abs_abs]
      nlinarith [abs_nonneg (g x)]
  have hv : MeasureTheory.MemLp v 2 μ := by
    apply MeasureTheory.MemLp.mono
      (MeasureTheory.memLp_const (b⁻¹) (μ := μ) (p := 2))
    · exact hαmeas.inv.sqrt.aestronglyMeasurable
    · filter_upwards [hαvalues] with x hx
      have hsqrt_le : √((α x)⁻¹) ≤ b⁻¹ := by
        rcases hx with hx | hx
        · rw [hx, Real.sqrt_inv, Real.sqrt_sq hb0.le]
        · have hx1 : α x = 1 := by simpa using hx
          rw [hx1]
          simp
          exact (one_le_inv₀ hb0).2 hb1.le
      dsimp [v]
      rw [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (inv_nonneg.mpr hb0.le)]
      exact hsqrt_le
  have hprod_ae : (fun x => u x * v x) =ᵐ[μ] fun x => |g x| := by
    filter_upwards [hαvalues] with x hx
    have hpos : 0 < α x := hαpos_of_val hx
    have hsqrt : √(α x) * √((α x)⁻¹) = 1 := by
      rw [Real.sqrt_inv]
      exact mul_inv_cancel₀ ((Real.sqrt_ne_zero').2 hpos)
    dsimp [u, v]
    calc
      √(α x) * |g x| * √((α x)⁻¹)
          = (√(α x) * √((α x)⁻¹)) * |g x| := by ring
      _ = |g x| := by rw [hsqrt, one_mul]
  have hCsquare_ae : (fun x => u x ^ 2) =ᵐ[μ] fun x => α x * |g x| ^ 2 := by
    filter_upwards [hαvalues] with x hx
    have hpos : 0 < α x := hαpos_of_val hx
    dsimp [u]
    rw [mul_pow, Real.sq_sqrt hpos.le]
  have hDsquare_ae : (fun x => v x ^ 2) =ᵐ[μ] fun x => (α x)⁻¹ := by
    filter_upwards [hαvalues] with x hx
    have hpos : 0 < α x := hαpos_of_val hx
    dsimp [v]
    rw [Real.sq_sqrt (inv_nonneg.mpr hpos.le)]
  have hcs := l2_cauchy_schwarz_integral hu hv
  rw [MeasureTheory.integral_congr_ae hprod_ae,
    MeasureTheory.integral_congr_ae hCsquare_ae,
    MeasureTheory.integral_congr_ae hDsquare_ae] at hcs
  exact hcs

/- verified submission -/
theorem weighted_one_dimensional_Dirichlet_lower_bound
    (b θ₀ : ℝ) (α φ : ℝ → ℝ)
    (hb0 : 0 < b) (hb1 : b < 1)
    (hθ0 : 0 < θ₀) (hθ1 : θ₀ < 2 * Real.pi)
    (hαmeas : AEMeasurable α
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))))
    (hαbounded : MeasureTheory.MemLp α ⊤
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))))
    (hαvalues : ∀ᵐ θ ∂(MeasureTheory.volume.restrict
      (Set.Icc (0 : ℝ) (2 * Real.pi))), α θ ∈ ({b ^ 2, 1} : Set ℝ))
    (hαmeasure : (MeasureTheory.volume.restrict
      (Set.Icc (0 : ℝ) (2 * Real.pi))) {θ | α θ = b ^ 2} = ENNReal.ofReal θ₀)
    (hφac : AbsolutelyContinuousOnInterval φ 0 (2 * Real.pi))
    (hφL2 : MeasureTheory.MemLp φ 2
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))))
    (hφderivL2 : MeasureTheory.MemLp (deriv φ) 2
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))))
    (hφend : φ (2 * Real.pi) - φ 0 = 2 * Real.pi) :
    (1 / 2 : ℝ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), α θ * |deriv φ θ| ^ 2 ≥
      2 * Real.pi ^ 2 / (2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1)) := by
  let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict
    (Set.Icc (0 : ℝ) (2 * Real.pi))
  let L : ℝ := ∫ θ, |deriv φ θ| ∂μ
  let C : ℝ := ∫ θ, α θ * |deriv φ θ| ^ 2 ∂μ
  let D : ℝ := ∫ θ, (α θ)⁻¹ ∂μ
  have h0le : 0 ≤ 2 * Real.pi := mul_nonneg zero_le_two Real.pi_pos.le
  have hinterval_to_restrict (f : ℝ → ℝ) :
      ∫ θ in (0 : ℝ)..(2 * Real.pi), f θ = ∫ θ, f θ ∂μ := by
    rw [intervalIntegral.integral_of_le h0le]
    exact (MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioc_ae_eq_Icc' (by simp : MeasureTheory.volume ({0} : Set ℝ) = 0))).trans rfl
  have hcs : L ^ 2 ≤ C * D := by
    dsimp [L, C, D]
    exact weighted_l1_sq_le_weighted_l2_mul_inv b α (deriv φ) hb0 hb1 hαmeas hαvalues
      hφderivL2
  have hD : D = 2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1) := by
    dsimp [D, μ]
    exact integral_inv_eq_of_two_valued_on_interval b θ₀ α hb0 hb1 hθ0 hθ1
      hαmeas hαvalues hαmeasure
  have hIntg : ∫ θ, deriv φ θ ∂μ = 2 * Real.pi := by
    rw [← hinterval_to_restrict (deriv φ),
      AbsolutelyContinuousOnInterval.integral_deriv_eq_sub hφac, hφend]
  have hLlower : 2 * Real.pi ≤ L := by
    have htriangle := MeasureTheory.abs_integral_le_integral_abs (μ := μ) (f := deriv φ)
    rw [hIntg, abs_of_nonneg h0le] at htriangle
    exact htriangle
  have hLnonneg : 0 ≤ L := by
    dsimp [L]
    exact MeasureTheory.integral_nonneg fun θ => abs_nonneg (deriv φ θ)
  have hTsq_le_Lsq : (2 * Real.pi) ^ 2 ≤ L ^ 2 := by
    apply sq_le_sq.2
    rw [abs_of_nonneg h0le, abs_of_nonneg hLnonneg]
    exact hLlower
  have hCD : (2 * Real.pi) ^ 2 ≤ C * D := hTsq_le_Lsq.trans hcs
  have hb2lt1 : b ^ 2 < 1 := by nlinarith
  have hinv_gt_one : 1 < (b ^ 2)⁻¹ :=
    (one_lt_inv₀ (sq_pos_of_pos hb0)).2 hb2lt1
  have hdenpos : 0 < 2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1) := by
    nlinarith [Real.pi_pos, hθ0, hinv_gt_one]
  have hmain : 2 * Real.pi ^ 2 / (2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1)) ≤
      (1 / 2 : ℝ) * C := by
    rw [div_le_iff₀ hdenpos]
    nlinarith [hCD, hD]
  have hCeq : ∫ θ in (0 : ℝ)..(2 * Real.pi), α θ * |deriv φ θ| ^ 2 = C :=
    hinterval_to_restrict (fun θ => α θ * |deriv φ θ| ^ 2)
  rw [hCeq]
  exact hmain
