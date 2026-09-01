import Mathlib

/- accepted add_to_file helper 1 -/
lemma deriv_hump_factor (k : ℕ) (hk : 0 < k) (lam x : ℝ) :
    deriv (fun x : ℝ => x ^ k - lam * x ^ (k + 2)) x =
      x ^ (k - 1) * ((k : ℝ) - lam * (k + 2 : ℝ) * x ^ 2) := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ k) ((k : ℝ) * x ^ (k - 1)) x := by
    simpa using hasDerivAt_pow k x
  have h2 : HasDerivAt (fun x : ℝ => x ^ (k+2)) ((k+2 : ℝ) * x ^ (k+1)) x := by
    simpa using hasDerivAt_pow (k+2) x
  have hd := h1.sub (h2.const_mul lam)
  change deriv ((fun x : ℝ => x ^ k) - (fun x : ℝ => lam * x ^ (k + 2))) x = _
  rw [hd.deriv]
  have hk' : k + 1 = k - 1 + 2 := by omega
  rw [hk']
  rw [pow_add]
  ring

/- accepted add_to_file helper 2 -/
lemma hump_strictMono_on_left (k : ℕ) (hk : 0 < k) {lam : ℝ} (hlam : 0 < lam) :
    StrictMonoOn (fun x : ℝ => x ^ k - lam * x ^ (k + 2))
      (Set.Icc 0 (Real.sqrt ((k : ℝ) / (lam * (k + 2 : ℝ))))) := by
  let c := Real.sqrt ((k : ℝ) / (lam * (k + 2 : ℝ)))
  have hdiff : Differentiable ℝ (fun x : ℝ => x ^ k - lam * x ^ (k + 2)) := by
    exact (differentiable_pow k).sub ((differentiable_pow (k+2)).const_mul lam)
  apply strictMonoOn_of_deriv_pos (D := Set.Icc 0 c) (convex_Icc 0 c)
  · exact hdiff.continuous.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hcsq : c ^ 2 = (k : ℝ) / (lam * (k + 2 : ℝ)) := by
      dsimp [c]
      exact Real.sq_sqrt (by positivity)
    have hxsq : x ^ 2 < c ^ 2 := by
      rw [sq_lt_sq, abs_of_pos hx.1, abs_of_pos]
      · exact hx.2
      · dsimp [c]
        positivity
    have hcoef : 0 < lam * (k + 2 : ℝ) := by positivity
    have hfactor : 0 < (k : ℝ) - lam * (k + 2 : ℝ) * x ^ 2 := by
      have hmul := mul_lt_mul_of_pos_left hxsq hcoef
      rw [hcsq] at hmul
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      field_simp at hmul
      nlinarith
    rw [deriv_hump_factor k hk]
    exact mul_pos (pow_pos hx.1 _) hfactor

lemma hump_strictAnti_on_right (k : ℕ) (hk : 0 < k) {lam : ℝ} (hlam : 0 < lam) :
    StrictAntiOn (fun x : ℝ => x ^ k - lam * x ^ (k + 2))
      (Set.Icc (Real.sqrt ((k : ℝ) / (lam * (k + 2 : ℝ)))) (1 / Real.sqrt lam)) := by
  let c := Real.sqrt ((k : ℝ) / (lam * (k + 2 : ℝ)))
  let z := 1 / Real.sqrt lam
  have hdiff : Differentiable ℝ (fun x : ℝ => x ^ k - lam * x ^ (k + 2)) := by
    exact (differentiable_pow k).sub ((differentiable_pow (k+2)).const_mul lam)
  apply strictAntiOn_of_deriv_neg (D := Set.Icc c z) (convex_Icc c z)
  · exact hdiff.continuous.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hcpos : 0 < c := by dsimp [c]; positivity
    have hxpos : 0 < x := lt_trans hcpos hx.1
    have hcsq : c ^ 2 = (k : ℝ) / (lam * (k + 2 : ℝ)) := by
      dsimp [c]
      exact Real.sq_sqrt (by positivity)
    have hxsq : c ^ 2 < x ^ 2 := by
      rw [sq_lt_sq, abs_of_pos hcpos, abs_of_pos hxpos]
      exact hx.1
    have hcoef : 0 < lam * (k + 2 : ℝ) := by positivity
    have hfactor : (k : ℝ) - lam * (k + 2 : ℝ) * x ^ 2 < 0 := by
      have hmul := mul_lt_mul_of_pos_left hxsq hcoef
      rw [hcsq] at hmul
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      field_simp at hmul
      nlinarith
    rw [deriv_hump_factor k hk]
    exact mul_neg_of_pos_of_neg (pow_pos hxpos _) hfactor

/- accepted add_to_file helper 3 -/
lemma two_roots_hump (k : ℕ) (hk : 0 < k) {M lam : ℝ} (hM : 0 < M) (hlam : 0 < lam)
    (hcond : M ^ 2 * lam ^ k < (k : ℝ) ^ k / ((k : ℝ) + 2) ^ (k + 2)) :
    ∃ r_minus r_plus : ℝ,
      0 < r_minus ∧ r_minus < r_plus ∧
      (r_minus ^ k - lam * r_minus ^ (k + 2)) = 2 * M ∧
      (r_plus ^ k - lam * r_plus ^ (k + 2)) = 2 * M ∧
      ∀ r : ℝ, 0 < r →
        (r ^ k - lam * r ^ (k + 2)) = 2 * M →
        r = r_minus ∨ r = r_plus := by
  let h : ℝ → ℝ := fun x => x ^ k - lam * x ^ (k + 2)
  let c := Real.sqrt ((k : ℝ) / (lam * (k + 2 : ℝ)))
  let z := 1 / Real.sqrt lam
  have hdiff : Differentiable ℝ h := by
    dsimp [h]
    exact (differentiable_pow k).sub ((differentiable_pow (k+2)).const_mul lam)
  have hcont : Continuous h := hdiff.continuous
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hzpos : 0 < z := by dsimp [z]; positivity
  have hcsq : c ^ 2 = (k : ℝ) / (lam * (k + 2 : ℝ)) := by
    dsimp [c]
    exact Real.sq_sqrt (by positivity)
  have hzsq : z ^ 2 = 1 / lam := by
    dsimp [z]
    rw [div_pow, Real.sq_sqrt (le_of_lt hlam)]
    norm_num
  have hcltz : c < z := by
    have hsq : c ^ 2 < z ^ 2 := by
      rw [hcsq, hzsq]
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      rw [div_lt_div_iff₀]
      · nlinarith
      · positivity
      · exact hlam
    have := sq_lt_sq.mp hsq
    rwa [abs_of_pos hcpos, abs_of_pos hzpos] at this
  have hcval : h c = c ^ k * (2 / ((k : ℝ) + 2)) := by
    dsimp [h]
    rw [pow_add]
    rw [hcsq]
    have hcoef : 0 < lam * (k + 2 : ℝ) := by positivity
    field_simp
    ring
  have hcsqid : (h c) ^ 2 * lam ^ k =
      4 * (k : ℝ) ^ k / ((k : ℝ) + 2) ^ (k + 2) := by
    have hprod : c ^ 2 * lam = (k : ℝ) / ((k : ℝ) + 2) := by
      rw [hcsq]
      have hcoef : 0 < lam * (k + 2 : ℝ) := by positivity
      field_simp
    have hpow : (c ^ k) ^ 2 * lam ^ k = ((k : ℝ) / ((k : ℝ) + 2)) ^ k := by
      calc
        (c ^ k) ^ 2 * lam ^ k = (c ^ 2) ^ k * lam ^ k := by
          rw [← pow_mul]
          rw [← pow_mul]
          rw [Nat.mul_comm k 2]
        _ = (c ^ 2 * lam) ^ k := by rw [mul_pow]
        _ = ((k : ℝ) / ((k : ℝ) + 2)) ^ k := by rw [hprod]
    calc
      (h c) ^ 2 * lam ^ k = (c ^ k * (2 / ((k : ℝ) + 2))) ^ 2 * lam ^ k := by rw [hcval]
      _ = (2 / ((k : ℝ) + 2)) ^ 2 * ((c ^ k) ^ 2 * lam ^ k) := by ring
      _ = (2 / ((k : ℝ) + 2)) ^ 2 * ((k : ℝ) / ((k : ℝ) + 2)) ^ k := by rw [hpow]
      _ = 4 * (k : ℝ) ^ k / ((k : ℝ) + 2) ^ (k + 2) := by
        rw [div_pow, div_pow]
        field_simp
        rw [pow_add]
        ring
  have hcvalue_pos : 0 < h c := by
    rw [hcval]
    positivity
  have hcmax : 2 * M < h c := by
    have h4 : (2 * M) ^ 2 * lam ^ k < 4 * (k : ℝ) ^ k / ((k : ℝ) + 2) ^ (k + 2) := by
      have hmul := mul_lt_mul_of_pos_left hcond (show (0 : ℝ) < 4 by norm_num)
      convert hmul using 1
      · ring
      · ring
    have hsquares_mul : (2 * M) ^ 2 * lam ^ k < (h c) ^ 2 * lam ^ k := by
      calc
        (2 * M) ^ 2 * lam ^ k < 4 * (k : ℝ) ^ k / ((k : ℝ) + 2) ^ (k + 2) := h4
        _ = (h c) ^ 2 * lam ^ k := hcsqid.symm
    have hsquares : (2 * M) ^ 2 < (h c) ^ 2 := by
      nlinarith [hsquares_mul, pow_pos hlam k]
    have htarget : 0 < 2 * M := by positivity
    have := sq_lt_sq.mp hsquares
    rwa [abs_of_pos htarget, abs_of_pos hcvalue_pos] at this
  have hz : h z = 0 := by
    have hzlam : lam * z ^ 2 = 1 := by
      rw [hzsq]
      field_simp
    dsimp [h]
    rw [pow_add]
    nlinarith [pow_pos hzpos k]
  obtain ⟨r_minus, hrminusI, hrminus_eq⟩ := by
    have hmem : 2 * M ∈ Set.Ioo (h 0) (h c) := by
      have h0 : h 0 = 0 := by
        dsimp [h]
        simp [Nat.ne_zero_of_lt hk]
      rw [h0]
      exact ⟨by positivity, hcmax⟩
    have himg := intermediate_value_Ioo (show 0 ≤ c from le_of_lt hcpos) hcont.continuousOn hmem
    simpa [Set.mem_image] using himg
  obtain ⟨r_plus, hrplusI, hrplus_eq⟩ := by
    have hmem : 2 * M ∈ Set.Ioo (h z) (h c) := by
      rw [hz]
      exact ⟨by positivity, hcmax⟩
    have himg := intermediate_value_Ioo' (show c ≤ z from le_of_lt hcltz) hcont.continuousOn hmem
    simpa [Set.mem_image] using himg
  refine ⟨r_minus, r_plus, hrminusI.1, lt_trans hrminusI.2 hrplusI.1, ?_, ?_, ?_⟩
  · simpa [h] using hrminus_eq
  · simpa [h] using hrplus_eq
  · intro r hrpos hr_eq
    have hr_eq_h : h r = 2 * M := by simpa [h] using hr_eq
    have hleft : StrictMonoOn h (Set.Icc 0 c) := by
      simpa [h, c] using hump_strictMono_on_left k hk hlam
    have hright : StrictAntiOn h (Set.Icc c z) := by
      simpa [h, c, z] using hump_strictAnti_on_right k hk hlam
    have hform : h r = r ^ k * (1 - lam * r ^ 2) := by
      dsimp [h]
      rw [pow_add]
      ring
    have hprodpos : 0 < r ^ k * (1 - lam * r ^ 2) := by
      rw [← hform, hr_eq_h]
      positivity
    have hfactorpos : 0 < 1 - lam * r ^ 2 := by
      nlinarith [hprodpos, pow_pos hrpos k]
    have hrsq : r ^ 2 < z ^ 2 := by
      rw [hzsq]
      rw [lt_div_iff₀ hlam]
      nlinarith
    have hrltz : r < z := by
      have := sq_lt_sq.mp hrsq
      rwa [abs_of_pos hrpos, abs_of_pos hzpos] at this
    rcases lt_trichotomy r c with hrc | rfl | hrc
    · left
      apply hleft.injOn
      · exact ⟨le_of_lt hrpos, le_of_lt hrc⟩
      · exact ⟨le_of_lt hrminusI.1, le_of_lt hrminusI.2⟩
      · rw [hr_eq_h, hrminus_eq]
    · exfalso
      linarith
    · right
      apply hright.injOn
      · exact ⟨le_of_lt hrc, le_of_lt hrltz⟩
      · exact ⟨le_of_lt hrplusI.1, le_of_lt hrplusI.2⟩
      · rw [hr_eq_h, hrplus_eq]

/- accepted add_to_file helper 4 -/
lemma hump_to_mu_nat (k : ℕ) {M lam r : ℝ} (hr : 0 < r)
    (hh : r ^ k - lam * r ^ (k + 2) = 2 * M) :
    1 - 2 * M / r ^ k - lam * r ^ 2 = 0 := by
  have hrpow : r ^ k ≠ 0 := pow_ne_zero _ hr.ne'
  have hdiv := congrArg (fun x : ℝ => x / r ^ k) hh
  rw [pow_add] at hdiv
  field_simp [hrpow] at hdiv ⊢
  linarith

lemma mu_to_hump_nat (k : ℕ) {M lam r : ℝ} (hr : 0 < r)
    (hmu : 1 - 2 * M / r ^ k - lam * r ^ 2 = 0) :
    r ^ k - lam * r ^ (k + 2) = 2 * M := by
  have hrpow : r ^ k ≠ 0 := pow_ne_zero _ hr.ne'
  have hmul := congrArg (fun x : ℝ => x * r ^ k) hmu
  field_simp [hrpow] at hmul
  rw [pow_add]
  linarith

/- verified submission -/
theorem two_positive_roots_of_mu
    (n : ℤ) (hn : 4 ≤ n)
    (M Λ : ℝ) (hM : 0 < M) (hΛ : 0 < Λ) :
    let lam : ℝ := 2 * Λ / (((n : ℝ) - 2) * ((n : ℝ) - 1))
    let mu : ℝ → ℝ := fun r ↦ 1 - 2 * M / r ^ (n - 3) - lam * r ^ 2
    M ^ 2 * lam ^ (n - 3) <
        ((n : ℝ) - 3) ^ (n - 3) / ((n : ℝ) - 1) ^ (n - 1) →
      ∃ r_minus r_plus : ℝ,
        0 < r_minus ∧ r_minus < r_plus ∧
        mu r_minus = 0 ∧ mu r_plus = 0 ∧
        ∀ r : ℝ, 0 < r → mu r = 0 → r = r_minus ∨ r = r_plus := by
  dsimp
  set lam : ℝ := 2 * Λ / (((n : ℝ) - 2) * ((n : ℝ) - 1))
  set mu : ℝ → ℝ := fun r ↦ 1 - 2 * M / r ^ (n - 3) - lam * r ^ 2
  intro hcond
  let k : ℕ := (n - 3).toNat
  have hk_nonneg : (0 : ℤ) ≤ n - 3 := by omega
  have hk_int : (k : ℤ) = n - 3 := by
    dsimp [k]
    exact Int.toNat_of_nonneg hk_nonneg
  have hk : 0 < k := by omega
  have hkR : (k : ℝ) = (n : ℝ) - 3 := by exact_mod_cast hk_int
  have hk2_int : ((k + 2 : ℕ) : ℤ) = n - 1 := by omega
  have hk2R : ((k : ℝ) + 2) = (n : ℝ) - 1 := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hk2_int
    norm_num at this
    linarith
  have hlam : 0 < lam := by
    dsimp [lam]
    have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
    have hn2 : 0 < (n : ℝ) - 2 := by linarith
    have hn1 : 0 < (n : ℝ) - 1 := by linarith
    have hden : 0 < ((n : ℝ) - 2) * ((n : ℝ) - 1) := mul_pos hn2 hn1
    positivity
  have hcond_nat : M ^ 2 * lam ^ k <
      (k : ℝ) ^ k / ((k : ℝ) + 2) ^ (k + 2) := by
    convert hcond using 2
    · rw [← hk_int, zpow_natCast]
    · rw [← hkR, ← hk_int, zpow_natCast]
    · rw [← hk2R, ← hk2_int, zpow_natCast]
  obtain ⟨r_minus, r_plus, hrminus_pos, hr_lt, hminus_hump, hplus_hump, huniq⟩ :=
    two_roots_hump k hk hM hlam hcond_nat
  have hpowcast : ∀ r : ℝ, r ^ (n - 3) = r ^ k := by
    intro r
    rw [← hk_int, zpow_natCast]
  refine ⟨r_minus, r_plus, hrminus_pos, hr_lt, ?_, ?_, ?_⟩
  · rw [hpowcast]
    exact hump_to_mu_nat k hrminus_pos hminus_hump
  · rw [hpowcast]
    exact hump_to_mu_nat k (lt_trans hrminus_pos hr_lt) hplus_hump
  · intro r hr hmu
    rw [hpowcast] at hmu
    exact huniq r hr (mu_to_hump_nat k hr hmu)
