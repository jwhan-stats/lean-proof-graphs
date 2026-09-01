import Mathlib

/- accepted add_to_file helper 1 -/
import Mathlib

open MeasureTheory intervalIntegral

lemma integral_id_mul_exp_complex {a b : ℝ} {q : ℂ} (hq : q ≠ 0) :
    ∫ x in a..b, (x : ℂ) * Complex.exp (q * (x : ℂ)) =
      (((b : ℂ) / q - 1 / q ^ 2) * Complex.exp (q * (b : ℂ))) -
      (((a : ℂ) / q - 1 / q ^ 2) * Complex.exp (q * (a : ℂ))) := by
  let G : ℝ → ℂ := fun x => ((x : ℂ) / q - 1 / q ^ 2) * Complex.exp (q * (x : ℂ))
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt G ((x : ℂ) * Complex.exp (q * (x : ℂ))) x := by
    intro x hx
    dsimp [G]
    have hxid : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) x := by
      simpa using (hasDerivAt_id x).ofReal_comp
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) / q - 1 / q ^ 2) (1 / q) x := by
      simpa using (hxid.div_const q).sub_const (1 / q ^ 2)
    have hxq : HasDerivAt (fun x : ℝ => q * (x : ℂ)) q x := by
      simpa using hxid.const_mul q
    have h2 : HasDerivAt (fun x : ℝ => Complex.exp (q * (x : ℂ))) (q * Complex.exp (q * (x : ℂ))) x := by
      simpa [mul_comm] using (Complex.hasDerivAt_exp (q * (x : ℂ))).comp x hxq
    convert h1.mul h2 using 1
    field_simp [hq]
    ring
  have hint : IntervalIntegrable (fun x : ℝ => (x : ℂ) * Complex.exp (q * (x : ℂ))) volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  simpa [G] using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

lemma weighted_exp_interval_integral {u x : ℝ} (hx : x ≠ 0) :
    ∫ s in (0 : ℝ)..u, ((u : ℂ) - (s : ℂ)) *
        Complex.exp (Complex.I * (s : ℂ) * (x : ℂ)) =
      (Complex.exp (Complex.I * (u : ℂ) * (x : ℂ)) - 1 -
        Complex.I * (u : ℂ) * (x : ℂ)) /
        (Complex.I * (x : ℂ)) ^ 2 := by
  let q : ℂ := Complex.I * (x : ℂ)
  have hq : q ≠ 0 := by
    dsimp [q]
    simp [Complex.I_ne_zero, hx]
  have hexp_point : ∀ s : ℝ,
      Complex.exp (Complex.I * (s : ℂ) * (x : ℂ)) =
        Complex.exp (q * (s : ℂ)) := by
    intro s
    congr 1
    dsimp [q]
    ring
  have hA0 : ∫ s in (0 : ℝ)..u,
      Complex.exp (Complex.I * (s : ℂ) * (x : ℂ)) =
      ∫ s in (0 : ℝ)..u, Complex.exp (q * (s : ℂ)) := by
    congr 1
    funext s
    exact hexp_point s
  have hB0 : ∫ s in (0 : ℝ)..u, (s : ℂ) *
      Complex.exp (Complex.I * (s : ℂ) * (x : ℂ)) =
      ∫ s in (0 : ℝ)..u, (s : ℂ) * Complex.exp (q * (s : ℂ)) := by
    congr 1
    funext s
    rw [hexp_point s]
  have hA : ∫ s in (0 : ℝ)..u, Complex.exp (Complex.I * (s : ℂ) * (x : ℂ)) =
      (Complex.exp (Complex.I * (u : ℂ) * (x : ℂ)) - 1) / q := by
    rw [hA0, integral_exp_mul_complex hq]
    dsimp [q]
    simp
    ring_nf
  have hB : ∫ s in (0 : ℝ)..u, (s : ℂ) *
      Complex.exp (Complex.I * (s : ℂ) * (x : ℂ)) =
      (((u : ℂ) / q - 1 / q ^ 2) *
        Complex.exp (Complex.I * (u : ℂ) * (x : ℂ))) + 1 / q ^ 2 := by
    have h := integral_id_mul_exp_complex (a := 0) (b := u) hq
    rw [hB0, h]
    have hexpu : Complex.exp (q * (u : ℂ)) =
        Complex.exp (Complex.I * (u : ℂ) * (x : ℂ)) := by
      congr 1
      dsimp [q]
      ring
    rw [hexpu]
    dsimp [q]
    simp
  have hsub : ∫ s in (0 : ℝ)..u, ((u : ℂ) - (s : ℂ)) *
      Complex.exp (Complex.I * (s : ℂ) * (x : ℂ)) =
      (u : ℂ) * (∫ s in (0 : ℝ)..u,
          Complex.exp (Complex.I * (s : ℂ) * (x : ℂ))) -
        ∫ s in (0 : ℝ)..u, (s : ℂ) *
          Complex.exp (Complex.I * (s : ℂ) * (x : ℂ)) := by
    have h1 : IntervalIntegrable (fun s : ℝ => (u : ℂ) *
        Complex.exp (Complex.I * (s : ℂ) * (x : ℂ))) volume 0 u := by
      apply Continuous.intervalIntegrable
      fun_prop
    have h2 : IntervalIntegrable (fun s : ℝ => (s : ℂ) *
        Complex.exp (Complex.I * (s : ℂ) * (x : ℂ))) volume 0 u := by
      apply Continuous.intervalIntegrable
      fun_prop
    have hfun : (fun s : ℝ => ((u : ℂ) - (s : ℂ)) *
          Complex.exp (Complex.I * (s : ℂ) * (x : ℂ))) =
        (fun s : ℝ => (u : ℂ) *
            Complex.exp (Complex.I * (s : ℂ) * (x : ℂ)) -
          (s : ℂ) * Complex.exp (Complex.I * (s : ℂ) * (x : ℂ))) := by
      funext s
      ring
    have hconst : ∫ s in (0 : ℝ)..u, (u : ℂ) *
        Complex.exp (Complex.I * (s : ℂ) * (x : ℂ)) =
        (u : ℂ) * ∫ s in (0 : ℝ)..u,
          Complex.exp (Complex.I * (s : ℂ) * (x : ℂ)) :=
      intervalIntegral.integral_const_mul _ _
    rw [hfun, intervalIntegral.integral_sub h1 h2, hconst]
  rw [hsub, hA, hB]
  field_simp [hq, Complex.I_sq, hx]
  ring

lemma complex_exp_sub_one_sub_linear_eq (u x : ℝ) :
    Complex.exp (Complex.I * (u : ℂ) * (x : ℂ)) - 1 -
        Complex.I * (u : ℂ) * (x : ℂ) =
      -(x : ℂ) ^ 2 *
        ∫ s in (0 : ℝ)..u, ((u : ℂ) - (s : ℂ)) *
          Complex.exp (Complex.I * (s : ℂ) * (x : ℂ)) := by
  by_cases hx : x = 0
  · subst x
    simp
  · rw [weighted_exp_interval_integral (u := u) (x := x) hx]
    field_simp [hx]
    simp [Complex.I_sq]

lemma integrable_exp_I_mul_mul {h : ℝ → ℂ} (hh : MeasureTheory.Integrable h) (s : ℝ) :
    MeasureTheory.Integrable (fun x : ℝ => Complex.exp (Complex.I * (s : ℂ) * (x : ℂ)) * h x) := by
  apply hh.bdd_mul (c := 1)
  · fun_prop
  · filter_upwards with x
    rw [Complex.norm_exp]
    simp

/- accepted add_to_file helper 2 -/
lemma integrable_interval_weight_exp_mul (u : ℝ) {h : ℝ → ℂ}
    (hh : MeasureTheory.Integrable h) :
    MeasureTheory.Integrable
      (Function.uncurry fun s x : ℝ =>
        ((u : ℂ) - (s : ℂ)) * Complex.exp (Complex.I * (s : ℂ) * (x : ℂ)) * h x)
      ((MeasureTheory.volume.restrict (Set.uIoc 0 u)).prod MeasureTheory.volume) := by
  let base : ℝ × ℝ → ℂ := fun p => ((u : ℂ) - (p.1 : ℂ)) * h p.2
  let phase : ℝ × ℝ → ℂ := fun p => Complex.exp (Complex.I * (p.1 : ℂ) * (p.2 : ℂ))
  have hg : MeasureTheory.Integrable (fun s : ℝ => (u : ℂ) - (s : ℂ))
      (MeasureTheory.volume.restrict (Set.uIoc 0 u)) := by
    have hi : IntervalIntegrable (fun s : ℝ => (u : ℂ) - (s : ℂ)) MeasureTheory.volume 0 u := by
      apply Continuous.intervalIntegrable
      fun_prop
    by_cases h0u : 0 ≤ u
    · have hu : Set.uIoc 0 u = Set.Ioc 0 u := Set.uIoc_of_le h0u
      rw [hu]
      exact hi.1
    · have hu0 : u ≤ 0 := le_of_not_ge h0u
      have hu : Set.uIoc 0 u = Set.Ioc u 0 := Set.uIoc_of_ge hu0
      rw [hu]
      exact hi.2
  have hbase : MeasureTheory.Integrable base
      ((MeasureTheory.volume.restrict (Set.uIoc 0 u)).prod MeasureTheory.volume) := by
    dsimp [base]
    exact hg.mul_prod hh
  have hmain : MeasureTheory.Integrable (fun p : ℝ × ℝ => phase p * base p)
      ((MeasureTheory.volume.restrict (Set.uIoc 0 u)).prod MeasureTheory.volume) := by
    apply hbase.bdd_mul (c := 1)
    · dsimp [phase]
      fun_prop
    · filter_upwards with p
      dsimp [phase]
      rw [Complex.norm_exp]
      simp
  convert hmain using 1
  ext p
  dsimp [base, phase, Function.uncurry]
  ring

/- accepted add_to_file helper 3 -/
lemma jump_integral_eq_interval_hstar
    (n : ℝ → NNReal)
    (hn2 : MeasureTheory.Integrable (fun x : ℝ => x ^ 2 * (n x : ℝ))) (u : ℝ) :
    let h : ℝ → ℂ := fun x => ((x ^ 2 * (n x : ℝ) : ℝ) : ℂ)
    let hstar : ℝ → ℂ := fun v =>
      ∫ x : ℝ, Complex.exp (Complex.I * (v : ℂ) * (x : ℂ)) * h x
    (∫ x : ℝ,
        (Complex.exp (Complex.I * (u : ℂ) * (x : ℂ)) - 1 -
          Complex.I * (u : ℂ) * (x : ℂ)) * (n x : ℂ)) =
      -∫ s in (0 : ℝ)..u, ((u : ℂ) - (s : ℂ)) * hstar s := by
  let h : ℝ → ℂ := fun x => ((x ^ 2 * (n x : ℝ) : ℝ) : ℂ)
  let hstar : ℝ → ℂ := fun v =>
    ∫ x : ℝ, Complex.exp (Complex.I * (v : ℂ) * (x : ℂ)) * h x
  let slice : ℝ → ℝ → ℂ := fun s x => ((u : ℂ) - (s : ℂ)) *
    Complex.exp (Complex.I * (s : ℂ) * (x : ℂ))
  have hh : MeasureTheory.Integrable h := by
    dsimp [h]
    exact hn2.ofReal
  have hpoint (x : ℝ) :
      (Complex.exp (Complex.I * (u : ℂ) * (x : ℂ)) - 1 -
          Complex.I * (u : ℂ) * (x : ℂ)) * (n x : ℂ) =
        -∫ s in (0 : ℝ)..u, slice s x * h x := by
    let J : ℂ := ∫ s in (0 : ℝ)..u, slice s x
    have hk : Complex.exp (Complex.I * (u : ℂ) * (x : ℂ)) - 1 -
        Complex.I * (u : ℂ) * (x : ℂ) = -(x : ℂ) ^ 2 * J := by
      dsimp [J, slice]
      exact complex_exp_sub_one_sub_linear_eq u x
    have hcast : h x = (x : ℂ) ^ 2 * (n x : ℂ) := by
      dsimp [h]
      simp [Complex.ofReal_pow, Complex.ofReal_mul]
    have hJ : J * h x = ∫ s in (0 : ℝ)..u, slice s x * h x := by
      calc
        J * h x = h x * J := by ring
        _ = ∫ s in (0 : ℝ)..u, h x * slice s x := by
          exact (intervalIntegral.integral_const_mul (h x) (fun s => slice s x)).symm
        _ = ∫ s in (0 : ℝ)..u, slice s x * h x := by
          apply intervalIntegral.integral_congr
          intro s hs
          ring
    calc
      (Complex.exp (Complex.I * (u : ℂ) * (x : ℂ)) - 1 -
            Complex.I * (u : ℂ) * (x : ℂ)) * (n x : ℂ)
          = (-(x : ℂ) ^ 2 * J) * (n x : ℂ) := by rw [hk]
      _ = -(J * h x) := by rw [hcast]; ring
      _ = -∫ s in (0 : ℝ)..u, slice s x * h x := by rw [hJ]
  have hprod : MeasureTheory.Integrable (Function.uncurry fun s x => slice s x * h x)
      ((MeasureTheory.volume.restrict (Set.uIoc 0 u)).prod MeasureTheory.volume) := by
    dsimp [slice]
    simpa [mul_assoc] using integrable_interval_weight_exp_mul u hh
  have hswap : ∫ s in (0 : ℝ)..u, ∫ x : ℝ, slice s x * h x =
      ∫ x : ℝ, ∫ s in (0 : ℝ)..u, slice s x * h x :=
    MeasureTheory.intervalIntegral_integral_swap hprod
  have hinner (s : ℝ) :
      (∫ x : ℝ, slice s x * h x) = ((u : ℂ) - (s : ℂ)) * hstar s := by
    dsimp [slice, hstar]
    simpa [mul_assoc] using
      (MeasureTheory.integral_const_mul ((u : ℂ) - (s : ℂ))
        (fun x : ℝ => Complex.exp (Complex.I * (s : ℂ) * (x : ℂ)) * h x))
  have hinterval : ∫ s in (0 : ℝ)..u, ∫ x : ℝ, slice s x * h x =
      ∫ s in (0 : ℝ)..u, ((u : ℂ) - (s : ℂ)) * hstar s := by
    apply intervalIntegral.integral_congr
    intro s hs
    exact hinner s
  calc
    (∫ x : ℝ,
          (Complex.exp (Complex.I * (u : ℂ) * (x : ℂ)) - 1 -
            Complex.I * (u : ℂ) * (x : ℂ)) * (n x : ℂ))
        = ∫ x : ℝ, -∫ s in (0 : ℝ)..u, slice s x * h x := by
          congr 1
          funext x
          exact hpoint x
    _ = -∫ x : ℝ, ∫ s in (0 : ℝ)..u, slice s x * h x := by
          rw [MeasureTheory.integral_neg]
    _ = -∫ s in (0 : ℝ)..u, ∫ x : ℝ, slice s x * h x := by
          rw [hswap]
    _ = -∫ s in (0 : ℝ)..u, ((u : ℂ) - (s : ℂ)) * hstar s := by
          rw [hinterval]

/- accepted add_to_file helper 4 -/
lemma continuous_hstar {h : ℝ → ℂ} (hh : MeasureTheory.Integrable h) :
    Continuous fun v : ℝ =>
      ∫ x : ℝ, Complex.exp (Complex.I * (v : ℂ) * (x : ℂ)) * h x := by
  apply MeasureTheory.continuous_of_dominated (bound := fun x : ℝ => ‖h x‖)
  · intro v
    exact (integrable_exp_I_mul_mul hh v).aestronglyMeasurable
  · intro v
    filter_upwards with x
    rw [norm_mul, Complex.norm_exp]
    simp
  · exact hh.norm
  · filter_upwards with x
    fun_prop

/- accepted add_to_file helper 5 -/
lemma norm_interval_weight_mul_le_abs_mul_integral_norm {f : ℝ → ℂ}
    (hf : Continuous f) (u : ℝ) :
    ‖∫ s in (0 : ℝ)..u, ((u : ℂ) - (s : ℂ)) * f s‖ ≤
      |u| * ∫ s in Set.Icc (min 0 u) (max 0 u), ‖f s‖ := by
  let F : ℝ → ℂ := fun s => ((u : ℂ) - (s : ℂ)) * f s
  let G : ℝ → ℝ := fun s => |u| * ‖f s‖
  have hG_int (a b : ℝ) : IntervalIntegrable G MeasureTheory.volume a b := by
    apply Continuous.intervalIntegrable
    dsimp [G]
    fun_prop
  have hnorm_sub (s : ℝ) : ‖((u : ℂ) - (s : ℂ))‖ = |u - s| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  by_cases h0u : 0 ≤ u
  · have hbound : ∀ᵐ t : ℝ, t ∈ Set.Ioc 0 u → ‖F t‖ ≤ G t := by
      filter_upwards with t ht
      dsimp [F, G]
      rw [norm_mul, hnorm_sub]
      have hnonneg : 0 ≤ u - t := sub_nonneg.mpr ht.2
      rw [abs_of_nonneg hnonneg, abs_of_nonneg h0u]
      nlinarith [norm_nonneg (f t), ht.1]
    have hmain := intervalIntegral.norm_integral_le_of_norm_le h0u hbound (hG_int 0 u)
    have hG_eq : ∫ s in (0 : ℝ)..u, G s =
        |u| * ∫ s in (0 : ℝ)..u, ‖f s‖ := by
      dsimp [G]
      exact intervalIntegral.integral_const_mul _ _
    have hnorm_eq : ∫ s in (0 : ℝ)..u, ‖f s‖ =
        ∫ s in Set.Icc (min 0 u) (max 0 u), ‖f s‖ := by
      rw [intervalIntegral.integral_of_le h0u]
      have hs : Set.Icc (min 0 u) (max 0 u) = Set.Icc 0 u := by
        simp [h0u]
      rw [hs]
      exact (MeasureTheory.integral_Icc_eq_integral_Ioc (μ := MeasureTheory.volume) (f := fun s => ‖f s‖)).symm
    calc
      ‖∫ s in (0 : ℝ)..u, ((u : ℂ) - (s : ℂ)) * f s‖
          = ‖∫ s in (0 : ℝ)..u, F s‖ := by rfl
      _ ≤ ∫ s in (0 : ℝ)..u, G s := hmain
      _ = |u| * ∫ s in (0 : ℝ)..u, ‖f s‖ := hG_eq
      _ = |u| * ∫ s in Set.Icc (min 0 u) (max 0 u), ‖f s‖ := by rw [hnorm_eq]
  · have hu0 : u ≤ 0 := le_of_not_ge h0u
    have hbound : ∀ᵐ t : ℝ, t ∈ Set.Ioc u 0 → ‖F t‖ ≤ G t := by
      filter_upwards with t ht
      dsimp [F, G]
      rw [norm_mul, hnorm_sub]
      have hnonpos : u - t ≤ 0 := sub_nonpos.mpr (le_of_lt ht.1)
      rw [abs_of_nonpos hnonpos, abs_of_nonpos hu0]
      nlinarith [norm_nonneg (f t), ht.2]
    have hmain := intervalIntegral.norm_integral_le_of_norm_le hu0 hbound (hG_int u 0)
    have hsymm : ∫ s in (0 : ℝ)..u, F s = -∫ s in u..(0 : ℝ), F s :=
      intervalIntegral.integral_symm (μ := MeasureTheory.volume) (f := F) (a := u) (b := 0)
    have hG_eq : ∫ s in u..(0 : ℝ), G s =
        |u| * ∫ s in u..(0 : ℝ), ‖f s‖ := by
      dsimp [G]
      exact intervalIntegral.integral_const_mul _ _
    have hnorm_eq : ∫ s in u..(0 : ℝ), ‖f s‖ =
        ∫ s in Set.Icc (min 0 u) (max 0 u), ‖f s‖ := by
      rw [intervalIntegral.integral_of_le hu0]
      have hs : Set.Icc (min 0 u) (max 0 u) = Set.Icc u 0 := by
        simp [hu0]
      rw [hs]
      exact (MeasureTheory.integral_Icc_eq_integral_Ioc (μ := MeasureTheory.volume) (f := fun s => ‖f s‖)).symm
    calc
      ‖∫ s in (0 : ℝ)..u, ((u : ℂ) - (s : ℂ)) * f s‖
          = ‖∫ s in (0 : ℝ)..u, F s‖ := by rfl
      _ = ‖∫ s in u..(0 : ℝ), F s‖ := by rw [hsymm, norm_neg]
      _ ≤ ∫ s in u..(0 : ℝ), G s := hmain
      _ = |u| * ∫ s in u..(0 : ℝ), ‖f s‖ := hG_eq
      _ = |u| * ∫ s in Set.Icc (min 0 u) (max 0 u), ‖f s‖ := by rw [hnorm_eq]

/- accepted add_to_file helper 6 -/
lemma integrable_jump_integrand
    (n : ℝ → NNReal)
    (hn2 : MeasureTheory.Integrable (fun x : ℝ => x ^ 2 * (n x : ℝ))) (u : ℝ) :
    MeasureTheory.Integrable (fun x : ℝ =>
      (Complex.exp (Complex.I * (u : ℂ) * (x : ℂ)) - 1 -
        Complex.I * (u : ℂ) * (x : ℂ)) * (n x : ℂ)) := by
  let h : ℝ → ℂ := fun x => ((x ^ 2 * (n x : ℝ) : ℝ) : ℂ)
  let slice : ℝ → ℝ → ℂ := fun s x => ((u : ℂ) - (s : ℂ)) *
    Complex.exp (Complex.I * (s : ℂ) * (x : ℂ))
  have hh : MeasureTheory.Integrable h := by
    dsimp [h]
    exact hn2.ofReal
  have hprod : MeasureTheory.Integrable (Function.uncurry fun s x => slice s x * h x)
      ((MeasureTheory.volume.restrict (Set.uIoc 0 u)).prod MeasureTheory.volume) := by
    dsimp [slice]
    simpa [mul_assoc] using integrable_interval_weight_exp_mul u hh
  have houter : MeasureTheory.Integrable
      (fun x : ℝ => ∫ s : ℝ, slice s x * h x ∂(MeasureTheory.volume.restrict (Set.uIoc 0 u))) :=
    hprod.integral_prod_right
  have hinterval_outer : MeasureTheory.Integrable
      (fun x : ℝ => ∫ s in (0 : ℝ)..u, slice s x * h x) := by
    by_cases h0u : 0 ≤ u
    · have hu : Set.uIoc 0 u = Set.Ioc 0 u := Set.uIoc_of_le h0u
      convert houter using 1
      ext x
      rw [hu]
      exact intervalIntegral.integral_of_le h0u
    · have hu0 : u ≤ 0 := le_of_not_ge h0u
      have hu : Set.uIoc 0 u = Set.Ioc u 0 := Set.uIoc_of_ge hu0
      have hneg : MeasureTheory.Integrable
          (fun x : ℝ => -∫ s : ℝ, slice s x * h x ∂(MeasureTheory.volume.restrict (Set.uIoc 0 u))) :=
        houter.neg
      convert hneg using 1
      ext x
      rw [hu]
      calc
        ∫ s in (0 : ℝ)..u, slice s x * h x
            = -∫ s in u..(0 : ℝ), slice s x * h x :=
          intervalIntegral.integral_symm (μ := MeasureTheory.volume) (f := fun s => slice s x * h x)
            (a := u) (b := 0)
        _ = -∫ s in Set.Ioc u 0, slice s x * h x := by
          rw [intervalIntegral.integral_of_le hu0]
  have htarget_eq : (fun x : ℝ =>
      (Complex.exp (Complex.I * (u : ℂ) * (x : ℂ)) - 1 -
        Complex.I * (u : ℂ) * (x : ℂ)) * (n x : ℂ)) =
      fun x : ℝ => -∫ s in (0 : ℝ)..u, slice s x * h x := by
    funext x
    let J : ℂ := ∫ s in (0 : ℝ)..u, slice s x
    have hk : Complex.exp (Complex.I * (u : ℂ) * (x : ℂ)) - 1 -
        Complex.I * (u : ℂ) * (x : ℂ) = -(x : ℂ) ^ 2 * J := by
      dsimp [J, slice]
      exact complex_exp_sub_one_sub_linear_eq u x
    have hcast : h x = (x : ℂ) ^ 2 * (n x : ℂ) := by
      dsimp [h]
      simp [Complex.ofReal_pow, Complex.ofReal_mul]
    have hJ : J * h x = ∫ s in (0 : ℝ)..u, slice s x * h x := by
      calc
        J * h x = h x * J := by ring
        _ = ∫ s in (0 : ℝ)..u, h x * slice s x := by
          exact (intervalIntegral.integral_const_mul (h x) (fun s => slice s x)).symm
        _ = ∫ s in (0 : ℝ)..u, slice s x * h x := by
          apply intervalIntegral.integral_congr
          intro s hs
          ring
    calc
      (Complex.exp (Complex.I * (u : ℂ) * (x : ℂ)) - 1 -
            Complex.I * (u : ℂ) * (x : ℂ)) * (n x : ℂ)
          = (-(x : ℂ) ^ 2 * J) * (n x : ℂ) := by rw [hk]
      _ = -(J * h x) := by rw [hcast]; ring
      _ = -∫ s in (0 : ℝ)..u, slice s x * h x := by rw [hJ]
  simpa [htarget_eq] using hinterval_outer

lemma re_jump_integrand (u x : ℝ) (r : NNReal) :
    ((Complex.exp (Complex.I * (u : ℂ) * (x : ℂ)) - 1 -
        Complex.I * (u : ℂ) * (x : ℂ)) * (r : ℂ)).re =
      (Real.cos (u * x) - 1) * (r : ℝ) := by
  let E : ℂ := Complex.exp (Complex.I * (u : ℂ) * (x : ℂ))
  let Z : ℂ := Complex.I * (u : ℂ) * (x : ℂ)
  have harg : Complex.I * (u : ℂ) * (x : ℂ) = ↑(u * x) * Complex.I := by
    norm_num [Complex.ofReal_mul]
    ring
  have hEre : E.re = Real.cos (u * x) := by
    dsimp [E]
    rw [harg]
    exact Complex.exp_ofReal_mul_I_re (u * x)
  have hEim : E.im = Real.sin (u * x) := by
    dsimp [E]
    rw [harg]
    exact Complex.exp_ofReal_mul_I_im (u * x)
  have hZre : Z.re = 0 := by
    dsimp [Z]
    simp
  have hZim : Z.im = u * x := by
    dsimp [Z]
    norm_num [Complex.ofReal_mul]
  change ((E - 1 - Z) * (r : ℂ)).re = (Real.cos (u * x) - 1) * (r : ℝ)
  rw [Complex.mul_re]
  simp [Complex.sub_re, Complex.sub_im, hEre, hEim, hZre, hZim]

/- accepted add_to_file helper 7 -/
lemma levy_exponent_re_nonpos
    (b σ2 : ℝ) (n : ℝ → NNReal) (hσ2 : 0 ≤ σ2)
    (hn2 : MeasureTheory.Integrable (fun x : ℝ => x ^ 2 * (n x : ℝ))) (u : ℝ) :
    (Complex.I * (u : ℂ) * (b : ℂ) -
          (σ2 : ℂ) * (u : ℂ) ^ 2 / 2 +
          ∫ x : ℝ,
            (Complex.exp (Complex.I * (u : ℂ) * (x : ℂ)) - 1 -
              Complex.I * (u : ℂ) * (x : ℂ)) * (n x : ℂ)).re ≤ 0 := by
  let R : ℂ := ∫ x : ℝ,
    (Complex.exp (Complex.I * (u : ℂ) * (x : ℂ)) - 1 -
      Complex.I * (u : ℂ) * (x : ℂ)) * (n x : ℂ)
  have hRint : MeasureTheory.Integrable (fun x : ℝ =>
      (Complex.exp (Complex.I * (u : ℂ) * (x : ℂ)) - 1 -
        Complex.I * (u : ℂ) * (x : ℂ)) * (n x : ℂ)) :=
    integrable_jump_integrand n hn2 u
  have hR_eq : R.re = ∫ x : ℝ,
      ((Complex.exp (Complex.I * (u : ℂ) * (x : ℂ)) - 1 -
        Complex.I * (u : ℂ) * (x : ℂ)) * (n x : ℂ)).re := by
    dsimp [R]
    exact (integral_re hRint).symm
  have hR_nonpos : R.re ≤ 0 := by
    rw [hR_eq]
    apply MeasureTheory.integral_nonpos
    intro x
    change ((Complex.exp (Complex.I * (u : ℂ) * (x : ℂ)) - 1 -
        Complex.I * (u : ℂ) * (x : ℂ)) * (n x : ℂ)).re ≤ (0 : ℝ)
    rw [re_jump_integrand]
    have hcos : Real.cos (u * x) ≤ 1 := Real.cos_le_one _
    have hn_nonneg : 0 ≤ (n x : ℝ) := NNReal.coe_nonneg _
    nlinarith
  have hA : (Complex.I * (u : ℂ) * (b : ℂ) -
          (σ2 : ℂ) * (u : ℂ) ^ 2 / 2 + R).re =
        -σ2 * u^2 / 2 + R.re := by
    simp [Complex.add_re, Complex.sub_re, Complex.mul_re, pow_two]
    ring
  have hg : -σ2 * u^2 / 2 ≤ 0 := by
    have hu : 0 ≤ u^2 := sq_nonneg u
    nlinarith
  change (Complex.I * (u : ℂ) * (b : ℂ) -
          (σ2 : ℂ) * (u : ℂ) ^ 2 / 2 + R).re ≤ 0
  rw [hA]
  linarith

/- accepted add_to_file helper 8 -/
lemma norm_exp_sub_one_le_of_re_nonpos {z : ℂ} (hz : z.re ≤ 0) :
    ‖Complex.exp z - 1‖ ≤ ‖z‖ := by
  let f : ℝ → ℂ := fun t => Complex.exp ((t : ℂ) * z)
  let f' : ℝ → ℂ := fun t => z * Complex.exp ((t : ℂ) * z)
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt f (f' t) (Set.Icc 0 1) t := by
    intro t ht
    have htcast : HasDerivAt (fun t : ℝ => (t : ℂ)) (1 : ℂ) t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    have hg : HasDerivAt (fun t : ℝ => (t : ℂ) * z) z t := by
      simpa using htcast.mul_const z
    have hexp : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * z))
        (Complex.exp ((t : ℂ) * z) * z) t := by
      exact (Complex.hasDerivAt_exp ((t : ℂ) * z)).comp t hg
    have hexp' : HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * z))
        (z * Complex.exp ((t : ℂ) * z)) t := by
      convert hexp using 1
      ring
    exact hexp'.hasDerivWithinAt
  have hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖f' t‖ ≤ ‖z‖ := by
    intro t ht
    dsimp [f']
    rw [norm_mul, Complex.norm_exp]
    have hre : ((t : ℂ) * z).re = t * z.re := by
      simp [Complex.mul_re]
    rw [hre]
    have hnonpos : t * z.re ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.1 hz
    have hexp_le : Real.exp (t * z.re) ≤ 1 := (Real.exp_le_one_iff).2 hnonpos
    nlinarith [norm_nonneg z]
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := f') (s := Set.Icc (0 : ℝ) 1) (x := 0) (y := 1) (C := ‖z‖)
    hderiv hbound (convex_Icc 0 1) (Set.left_mem_Icc.2 zero_le_one)
    (Set.right_mem_Icc.2 zero_le_one)
  simpa [f] using hmvt

/- accepted add_to_file helper 9 -/
lemma levy_exponent_norm_le
    (b σ2 : ℝ) (n : ℝ → NNReal) (hσ2 : 0 ≤ σ2)
    (hn2 : MeasureTheory.Integrable (fun x : ℝ => x ^ 2 * (n x : ℝ))) (u : ℝ) :
    let h : ℝ → ℂ := fun x => ((x ^ 2 * (n x : ℝ) : ℝ) : ℂ)
    let hstar : ℝ → ℂ := fun v =>
      ∫ x : ℝ, Complex.exp (Complex.I * (v : ℂ) * (x : ℂ)) * h x
    ‖Complex.I * (u : ℂ) * (b : ℂ) -
          (σ2 : ℂ) * (u : ℂ) ^ 2 / 2 +
          ∫ x : ℝ,
            (Complex.exp (Complex.I * (u : ℂ) * (x : ℂ)) - 1 -
              Complex.I * (u : ℂ) * (x : ℂ)) * (n x : ℂ)‖ ≤
      |u| * (|b| + (∫ v in Set.Icc (min 0 u) (max 0 u), ‖hstar v‖) + σ2 * |u|) := by
  let h : ℝ → ℂ := fun x => ((x ^ 2 * (n x : ℝ) : ℝ) : ℂ)
  let hstar : ℝ → ℂ := fun v =>
    ∫ x : ℝ, Complex.exp (Complex.I * (v : ℂ) * (x : ℂ)) * h x
  let J : ℝ := ∫ v in Set.Icc (min 0 u) (max 0 u), ‖hstar v‖
  let R : ℂ := ∫ x : ℝ,
    (Complex.exp (Complex.I * (u : ℂ) * (x : ℂ)) - 1 -
      Complex.I * (u : ℂ) * (x : ℂ)) * (n x : ℂ)
  have hh : MeasureTheory.Integrable h := by
    dsimp [h]
    exact hn2.ofReal
  have hstar_cont : Continuous hstar := by
    dsimp [hstar]
    exact continuous_hstar hh
  have hjump : R = -∫ s in (0 : ℝ)..u, ((u : ℂ) - (s : ℂ)) * hstar s := by
    dsimp [R, h, hstar]
    exact jump_integral_eq_interval_hstar n hn2 u
  have hR : ‖R‖ ≤ |u| * J := by
    rw [hjump, norm_neg]
    dsimp [J]
    exact norm_interval_weight_mul_le_abs_mul_integral_norm hstar_cont u
  have hd : ‖Complex.I * (u : ℂ) * (b : ℂ)‖ = |u| * |b| := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs]
  have hg : ‖(σ2 : ℂ) * (u : ℂ) ^ 2 / (2 : ℂ)‖ = σ2 * u^2 / 2 := by
    rw [norm_div, norm_mul, Complex.norm_real]
    simp [Real.norm_eq_abs, abs_of_nonneg hσ2, norm_pow, Complex.norm_real]
  have hg_le : ‖(σ2 : ℂ) * (u : ℂ) ^ 2 / (2 : ℂ)‖ ≤ σ2 * u^2 := by
    rw [hg]
    have hu : 0 ≤ u^2 := sq_nonneg u
    nlinarith
  have htri : ‖Complex.I * (u : ℂ) * (b : ℂ) -
          (σ2 : ℂ) * (u : ℂ) ^ 2 / 2 + R‖ ≤
        ‖Complex.I * (u : ℂ) * (b : ℂ)‖ +
          ‖(σ2 : ℂ) * (u : ℂ) ^ 2 / 2‖ + ‖R‖ := by
    calc
      ‖Complex.I * (u : ℂ) * (b : ℂ) -
            (σ2 : ℂ) * (u : ℂ) ^ 2 / 2 + R‖
          ≤ ‖Complex.I * (u : ℂ) * (b : ℂ) -
              (σ2 : ℂ) * (u : ℂ) ^ 2 / 2‖ + ‖R‖ := norm_add_le _ _
      _ ≤ (‖Complex.I * (u : ℂ) * (b : ℂ)‖ +
              ‖(σ2 : ℂ) * (u : ℂ) ^ 2 / 2‖) + ‖R‖ := by
            gcongr
            exact norm_sub_le _ _
  have hmain : ‖Complex.I * (u : ℂ) * (b : ℂ) -
          (σ2 : ℂ) * (u : ℂ) ^ 2 / 2 + R‖ ≤
        |u| * |b| + σ2 * u^2 + |u| * J := by
    refine htri.trans ?_
    rw [hd]
    have hJnonneg : 0 ≤ J := by
      dsimp [J]
      apply MeasureTheory.integral_nonneg
      intro v
      exact norm_nonneg _
    nlinarith [hg_le, hR]
  have hfinal : |u| * |b| + σ2 * u^2 + |u| * J =
      |u| * (|b| + J + σ2 * |u|) := by
    rw [← sq_abs]
    ring
  change ‖Complex.I * (u : ℂ) * (b : ℂ) -
        (σ2 : ℂ) * (u : ℂ) ^ 2 / 2 + R‖ ≤
      |u| * (|b| + (∫ v in Set.Icc (min 0 u) (max 0 u), ‖hstar v‖) + σ2 * |u|)
  dsimp [J] at hmain hfinal
  rw [← hfinal]
  exact hmain

/- accepted add_to_file helper 10 -/
lemma levy_psi_bound_first
    (b σ2 Δ : ℝ) (n : ℝ → NNReal)
    (hσ2 : 0 ≤ σ2) (hΔ : 0 ≤ Δ)
    (hn2 : MeasureTheory.Integrable (fun x : ℝ => x ^ 2 * (n x : ℝ))) :
    let h : ℝ → ℂ := fun x => ((x ^ 2 * (n x : ℝ) : ℝ) : ℂ)
    let hstar : ℝ → ℂ := fun v =>
      ∫ x : ℝ, Complex.exp (Complex.I * (v : ℂ) * (x : ℂ)) * h x
    let ψΔ : ℝ → ℂ := fun u =>
      Complex.exp ((Δ : ℂ) *
        (Complex.I * (u : ℂ) * (b : ℂ) -
          (σ2 : ℂ) * (u : ℂ) ^ 2 / 2 +
          ∫ x : ℝ,
            (Complex.exp (Complex.I * (u : ℂ) * (x : ℂ)) - 1 -
              Complex.I * (u : ℂ) * (x : ℂ)) * (n x : ℂ)))
    let c : ℝ → ℝ := fun u =>
      |b| + ∫ v in Set.Icc (min 0 u) (max 0 u), ‖hstar v‖
    ∀ u : ℝ, ‖ψΔ u - 1‖ ≤ Δ * |u| * (c u + σ2 * |u|) := by
  dsimp only
  intro u
  let A : ℂ := Complex.I * (u : ℂ) * (b : ℂ) -
    (σ2 : ℂ) * (u : ℂ) ^ 2 / 2 +
    ∫ x : ℝ,
      (Complex.exp (Complex.I * (u : ℂ) * (x : ℂ)) - 1 -
        Complex.I * (u : ℂ) * (x : ℂ)) * (n x : ℂ)
  have hAre : A.re ≤ 0 := by
    dsimp [A]
    exact levy_exponent_re_nonpos b σ2 n hσ2 hn2 u
  have hΔre : ((Δ : ℂ) * A).re ≤ 0 := by
    rw [Complex.mul_re]
    simp
    exact mul_nonpos_of_nonneg_of_nonpos hΔ hAre
  have hexp : ‖Complex.exp ((Δ : ℂ) * A) - 1‖ ≤ ‖(Δ : ℂ) * A‖ :=
    norm_exp_sub_one_le_of_re_nonpos hΔre
  have hA : ‖A‖ ≤ |u| *
      (|b| + (∫ v in Set.Icc (min 0 u) (max 0 u),
          ‖∫ x : ℝ, Complex.exp (Complex.I * (v : ℂ) * (x : ℂ)) *
            ((x ^ 2 * (n x : ℝ) : ℝ) : ℂ)‖) + σ2 * |u|) := by
    dsimp [A]
    exact levy_exponent_norm_le b σ2 n hσ2 hn2 u
  have hscaled : ‖(Δ : ℂ) * A‖ ≤
      Δ * (|u| *
        (|b| + (∫ v in Set.Icc (min 0 u) (max 0 u),
          ‖∫ x : ℝ, Complex.exp (Complex.I * (v : ℂ) * (x : ℂ)) *
            ((x ^ 2 * (n x : ℝ) : ℝ) : ℂ)‖) + σ2 * |u|)) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΔ]
    exact mul_le_mul_of_nonneg_left hA hΔ
  change ‖Complex.exp ((Δ : ℂ) * A) - 1‖ ≤
    Δ * |u| * (|b| + (∫ v in Set.Icc (min 0 u) (max 0 u),
        ‖∫ x : ℝ, Complex.exp (Complex.I * (v : ℂ) * (x : ℂ)) *
          ((x ^ 2 * (n x : ℝ) : ℝ) : ℂ)‖) + σ2 * |u|)
  calc
    ‖Complex.exp ((Δ : ℂ) * A) - 1‖ ≤ ‖(Δ : ℂ) * A‖ := hexp
    _ ≤ Δ * (|u| *
        (|b| + (∫ v in Set.Icc (min 0 u) (max 0 u),
          ‖∫ x : ℝ, Complex.exp (Complex.I * (v : ℂ) * (x : ℂ)) *
            ((x ^ 2 * (n x : ℝ) : ℝ) : ℂ)‖) + σ2 * |u|)) := hscaled
    _ = Δ * |u| * (|b| + (∫ v in Set.Icc (min 0 u) (max 0 u),
          ‖∫ x : ℝ, Complex.exp (Complex.I * (v : ℂ) * (x : ℂ)) *
            ((x ^ 2 * (n x : ℝ) : ℝ) : ℂ)‖) + σ2 * |u|) := by ring

/- verified submission -/
theorem levyKhintchine_increment_bound
    (b σ2 Δ : ℝ) (n : ℝ → NNReal)
    (hσ2 : 0 ≤ σ2) (hΔ : 0 ≤ Δ)
    (hn : Measurable n)
    (hn2 : MeasureTheory.Integrable (fun x : ℝ => x ^ 2 * (n x : ℝ))) :
    let h : ℝ → ℂ := fun x => ((x ^ 2 * (n x : ℝ) : ℝ) : ℂ)
    let hstar : ℝ → ℂ := fun v =>
      ∫ x : ℝ, Complex.exp (Complex.I * (v : ℂ) * (x : ℂ)) * h x
    let ψΔ : ℝ → ℂ := fun u =>
      Complex.exp ((Δ : ℂ) *
        (Complex.I * (u : ℂ) * (b : ℂ) -
          (σ2 : ℂ) * (u : ℂ) ^ 2 / 2 +
          ∫ x : ℝ,
            (Complex.exp (Complex.I * (u : ℂ) * (x : ℂ)) - 1 -
              Complex.I * (u : ℂ) * (x : ℂ)) * (n x : ℂ)))
    let c : ℝ → ℝ := fun u =>
      |b| + ∫ v in Set.Icc (min 0 u) (max 0 u), ‖hstar v‖
    (∀ u : ℝ, ‖ψΔ u - 1‖ ≤ Δ * |u| * (c u + σ2 * |u|)) ∧
      (MeasureTheory.Integrable hstar →
        ∀ u : ℝ,
          ‖ψΔ u - 1‖ ≤
            Δ * |u| * (|b| + (∫ v : ℝ, ‖hstar v‖) + σ2 * |u|)) := by
  refine ⟨levy_psi_bound_first b σ2 Δ n hσ2 hΔ hn2, ?_⟩
  dsimp only
  intro hhstar u
  have hfirst := levy_psi_bound_first b σ2 Δ n hσ2 hΔ hn2 u
  have hseg : (∫ v in Set.Icc (min 0 u) (max 0 u),
        ‖∫ x : ℝ, Complex.exp (Complex.I * (v : ℂ) * (x : ℂ)) *
          ((x ^ 2 * (n x : ℝ) : ℝ) : ℂ)‖) ≤
      ∫ v : ℝ,
        ‖∫ x : ℝ, Complex.exp (Complex.I * (v : ℂ) * (x : ℂ)) *
          ((x ^ 2 * (n x : ℝ) : ℝ) : ℂ)‖ := by
    apply MeasureTheory.setIntegral_le_integral
    · simpa using hhstar.norm
    · filter_upwards with v
      exact norm_nonneg _
  have hinner : |b| + (∫ v in Set.Icc (min 0 u) (max 0 u),
        ‖∫ x : ℝ, Complex.exp (Complex.I * (v : ℂ) * (x : ℂ)) *
          ((x ^ 2 * (n x : ℝ) : ℝ) : ℂ)‖) + σ2 * |u| ≤
      |b| + (∫ v : ℝ,
        ‖∫ x : ℝ, Complex.exp (Complex.I * (v : ℂ) * (x : ℂ)) *
          ((x ^ 2 * (n x : ℝ) : ℝ) : ℂ)‖) + σ2 * |u| := by
    nlinarith
  have houter_nonneg : 0 ≤ Δ * |u| := mul_nonneg hΔ (abs_nonneg u)
  exact hfirst.trans (mul_le_mul_of_nonneg_left hinner houter_nonneg)
