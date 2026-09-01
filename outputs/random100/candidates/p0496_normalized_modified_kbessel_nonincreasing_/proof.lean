import Mathlib

/- accepted add_to_file helper 1 -/
noncomputable def risingProd (y : ℝ) (r : ℕ) : ℝ :=
  ∏ j ∈ Finset.range r, (y + (j : ℝ))

lemma risingProd_pos {y : ℝ} (hy : 0 < y) (r : ℕ) : 0 < risingProd y r := by
  unfold risingProd
  exact Finset.prod_pos fun j hj => by positivity

lemma risingProd_nonneg {y : ℝ} (hy : 0 ≤ y) (r : ℕ) : 0 ≤ risingProd y r := by
  unfold risingProd
  exact Finset.prod_nonneg fun j hj => by positivity

lemma Gamma_add_nat_cast_eq_mul_risingProd {y : ℝ} (hy : 0 < y) (r : ℕ) :
    Real.Gamma (y + (r : ℝ)) = Real.Gamma y * risingProd y r := by
  induction r with
  | zero =>
      simp [risingProd]
  | succ r ih =>
      have hpos : 0 < y + (r : ℝ) := by positivity
      calc
        Real.Gamma (y + ((r + 1 : ℕ) : ℝ))
            = Real.Gamma ((y + (r : ℝ)) + 1) := by
                congr 1
                norm_num [Nat.cast_add, Nat.cast_one]
                ring
        _ = (y + (r : ℝ)) * Real.Gamma (y + (r : ℝ)) := by
                exact Real.Gamma_add_one hpos.ne'
        _ = (y + (r : ℝ)) * (Real.Gamma y * risingProd y r) := by
                rw [ih]
        _ = Real.Gamma y * risingProd y (r + 1) := by
                simp [risingProd, Finset.prod_range_succ, mul_comm, mul_left_comm]

/- accepted add_to_file helper 2 -/
lemma kGamma_ratio_eq_inv_mul_risingProd {k ν : ℝ} (hk : 0 < k) (hν : -k < ν)
    (r : ℕ) :
    (k ^ ((ν + k) / k - 1) * Real.Gamma ((ν + k) / k)) /
        (k ^ (((r : ℝ) * k + ν + k) / k - 1) *
          Real.Gamma (((r : ℝ) * k + ν + k) / k))
      = 1 / (k ^ r * risingProd (ν / k + 1) r) := by
  let y : ℝ := ν / k + 1
  have hy : 0 < y := by
    have hmul : (-1 : ℝ) * k < ν := by
      simpa using hν
    have hνk : -1 < ν / k := (lt_div_iff₀ hk).mpr hmul
    dsimp [y]
    linarith
  have harg1 : (ν + k) / k = y := by
    dsimp [y]
    field_simp [hk.ne']
  have harg2 : ((r : ℝ) * k + ν + k) / k = y + (r : ℝ) := by
    dsimp [y]
    field_simp [hk.ne']
    ring
  have hexp2 : y + (r : ℝ) - 1 = (y - 1) + (r : ℝ) := by ring
  have hΓ : Real.Gamma (y + (r : ℝ)) = Real.Gamma y * risingProd y r :=
    Gamma_add_nat_cast_eq_mul_risingProd hy r
  calc
    (k ^ ((ν + k) / k - 1) * Real.Gamma ((ν + k) / k)) /
        (k ^ (((r : ℝ) * k + ν + k) / k - 1) *
          Real.Gamma (((r : ℝ) * k + ν + k) / k))
        = (k ^ (y - 1) * Real.Gamma y) /
          (k ^ ((y + (r : ℝ)) - 1) * Real.Gamma (y + (r : ℝ))) := by
            rw [harg1, harg2]
    _ = (k ^ (y - 1) * Real.Gamma y) /
          ((k ^ (y - 1) * k ^ (r : ℝ)) *
            (Real.Gamma y * risingProd y r)) := by
            rw [hexp2, Real.rpow_add hk, hΓ]
    _ = 1 / (k ^ r * risingProd y r) := by
            rw [Real.rpow_natCast]
            have hkp : k ^ (y - 1) ≠ 0 := (Real.rpow_pos_of_pos hk _).ne'
            have hΓp : Real.Gamma y ≠ 0 := (Real.Gamma_pos_of_pos hy).ne'
            have hPp : risingProd y r ≠ 0 := (risingProd_pos hy r).ne'
            have hkn : k ^ r ≠ 0 := pow_ne_zero r hk.ne'
            field_simp [hkp, hΓp, hPp, hkn]
    _ = 1 / (k ^ r * risingProd (ν / k + 1) r) := by rfl

/- accepted add_to_file helper 3 -/
lemma kBessel_term_eq {k x ν : ℝ} (hk : 0 < k) (hν : -k < ν) (r : ℕ) :
    (k ^ ((ν + k) / k - 1) * Real.Gamma ((ν + k) / k)) /
        ((k ^ (((r : ℝ) * k + ν + k) / k - 1) *
          Real.Gamma (((r : ℝ) * k + ν + k) / k)) *
          (4 : ℝ) ^ r * (r.factorial : ℝ)) * x ^ (2 * r)
      = x ^ (2 * r) /
        ((4 * k) ^ r * (r.factorial : ℝ) * risingProd (ν / k + 1) r) := by
  have hratio := kGamma_ratio_eq_inv_mul_risingProd hk hν r
  rw [div_mul_eq_div_div, div_mul_eq_div_div, hratio]
  have hP : risingProd (ν / k + 1) r ≠ 0 := by
    have hmul : (-1 : ℝ) * k < ν := by simpa using hν
    have hνk : -1 < ν / k := (lt_div_iff₀ hk).mpr hmul
    have hy : 0 < ν / k + 1 := by linarith
    exact (risingProd_pos hy r).ne'
  have hkpow : k ^ r ≠ 0 := pow_ne_zero r hk.ne'
  have hfour : (4 : ℝ) ^ r ≠ 0 := pow_ne_zero r (by norm_num)
  have hfact : (r.factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_ne_zero r)
  have h4k : (4 * k) ^ r ≠ 0 := pow_ne_zero r (mul_pos (by norm_num) hk).ne'
  field_simp [hP, hkpow, hfour, hfact, h4k]
  rw [mul_pow]
  ring

/- accepted add_to_file helper 4 -/
lemma risingProd_mono {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z) (r : ℕ) :
    risingProd y r ≤ risingProd z r := by
  unfold risingProd
  exact Finset.prod_le_prod
    (fun j hj => by positivity)
    (fun j hj => by linarith)

lemma kBessel_term_nonneg {k x ν : ℝ} (hk : 0 < k) (hx : 0 ≤ x) (hν : -k < ν) (r : ℕ) :
    0 ≤ (k ^ ((ν + k) / k - 1) * Real.Gamma ((ν + k) / k)) /
        ((k ^ (((r : ℝ) * k + ν + k) / k - 1) *
          Real.Gamma (((r : ℝ) * k + ν + k) / k)) *
          (4 : ℝ) ^ r * (r.factorial : ℝ)) * x ^ (2 * r) := by
  rw [kBessel_term_eq hk hν r]
  have hmul : (-1 : ℝ) * k < ν := by simpa using hν
  have hνk : -1 < ν / k := (lt_div_iff₀ hk).mpr hmul
  have hy : 0 < ν / k + 1 := by linarith
  have hden : 0 < (4 * k) ^ r * (r.factorial : ℝ) * risingProd (ν / k + 1) r :=
    mul_pos (mul_pos (pow_pos (mul_pos (by norm_num) hk) _)
      (by exact_mod_cast Nat.factorial_pos r)) (risingProd_pos hy r)
  exact div_nonneg (pow_nonneg hx _) hden.le

lemma kBessel_term_antitone {k x ν μ : ℝ} (hk : 0 < k) (hx : 0 ≤ x)
    (hν : -k < ν) (hνμ : ν ≤ μ) (r : ℕ) :
    (k ^ ((μ + k) / k - 1) * Real.Gamma ((μ + k) / k)) /
        ((k ^ (((r : ℝ) * k + μ + k) / k - 1) *
          Real.Gamma (((r : ℝ) * k + μ + k) / k)) *
          (4 : ℝ) ^ r * (r.factorial : ℝ)) * x ^ (2 * r)
    ≤ (k ^ ((ν + k) / k - 1) * Real.Gamma ((ν + k) / k)) /
        ((k ^ (((r : ℝ) * k + ν + k) / k - 1) *
          Real.Gamma (((r : ℝ) * k + ν + k) / k)) *
          (4 : ℝ) ^ r * (r.factorial : ℝ)) * x ^ (2 * r) := by
  have hμ : -k < μ := lt_of_lt_of_le hν hνμ
  rw [kBessel_term_eq hk hμ r, kBessel_term_eq hk hν r]
  have hmulν : (-1 : ℝ) * k < ν := by simpa using hν
  have hνk : -1 < ν / k := (lt_div_iff₀ hk).mpr hmulν
  have hyn : 0 < ν / k + 1 := by linarith
  have hmulμ : (-1 : ℝ) * k < μ := by simpa using hμ
  have hμk : -1 < μ / k := (lt_div_iff₀ hk).mpr hmulμ
  have hym : 0 < μ / k + 1 := by linarith
  have hyνμ : ν / k + 1 ≤ μ / k + 1 := by
    have : ν / k ≤ μ / k := div_le_div_of_nonneg_right hνμ hk.le
    linarith
  have hP : risingProd (ν / k + 1) r ≤ risingProd (μ / k + 1) r :=
    risingProd_mono hyn.le hyνμ r
  have hbase : 0 < (4 * k) ^ r * (r.factorial : ℝ) :=
    mul_pos (pow_pos (mul_pos (by norm_num) hk) _)
      (by exact_mod_cast Nat.factorial_pos r)
  have hDν : 0 < (4 * k) ^ r * (r.factorial : ℝ) * risingProd (ν / k + 1) r :=
    mul_pos hbase (risingProd_pos hyn r)
  have hD : (4 * k) ^ r * (r.factorial : ℝ) * risingProd (ν / k + 1) r ≤
      (4 * k) ^ r * (r.factorial : ℝ) * risingProd (μ / k + 1) r :=
    mul_le_mul_of_nonneg_left hP hbase.le
  exact div_le_div_of_nonneg_left (pow_nonneg hx _) hDν hD

/- accepted add_to_file helper 5 -/
lemma factorial_mul_min_pow_le_risingProd {y : ℝ} (hy : 0 < y) (r : ℕ) :
    (r.factorial : ℝ) * (min y 1) ^ r ≤ risingProd y r := by
  let m : ℝ := min y 1
  have hm0 : 0 ≤ m := le_min hy.le zero_le_one
  have hmy : m ≤ y := min_le_left _ _
  have hm1 : m ≤ 1 := min_le_right _ _
  have hfacprod : (∏ j ∈ Finset.range r, ((j : ℝ) + 1)) = (r.factorial : ℝ) := by
    exact_mod_cast Finset.prod_range_add_one_eq_factorial r
  calc
    (r.factorial : ℝ) * m ^ r
        = (∏ j ∈ Finset.range r, m) *
            (∏ j ∈ Finset.range r, ((j : ℝ) + 1)) := by
          rw [hfacprod, Finset.prod_const, Finset.card_range, mul_comm]
    _ = ∏ j ∈ Finset.range r, (m * ((j : ℝ) + 1)) := by
          rw [Finset.prod_mul_distrib]
    _ ≤ risingProd y r := by
          unfold risingProd
          refine Finset.prod_le_prod ?_ ?_
          · intro j hj
            exact mul_nonneg hm0 (by positivity)
          · intro j hj
            have hj0 : 0 ≤ (j : ℝ) := by positivity
            nlinarith

/- accepted add_to_file helper 6 -/
lemma kBessel_term_le_exp_term {k x ν : ℝ} (hk : 0 < k) (hx : 0 ≤ x)
    (hν : -k < ν) (r : ℕ) :
    (k ^ ((ν + k) / k - 1) * Real.Gamma ((ν + k) / k)) /
        ((k ^ (((r : ℝ) * k + ν + k) / k - 1) *
          Real.Gamma (((r : ℝ) * k + ν + k) / k)) *
          (4 : ℝ) ^ r * (r.factorial : ℝ)) * x ^ (2 * r)
      ≤ (x ^ 2 / (4 * k * min (ν / k + 1) 1)) ^ r / (r.factorial : ℝ) := by
  rw [kBessel_term_eq hk hν r]
  have hmul : (-1 : ℝ) * k < ν := by simpa using hν
  have hνk : -1 < ν / k := (lt_div_iff₀ hk).mpr hmul
  have hy : 0 < ν / k + 1 := by linarith
  let m : ℝ := min (ν / k + 1) 1
  have hm : 0 < m := lt_min hy zero_lt_one
  have hlow : (r.factorial : ℝ) * m ^ r ≤ risingProd (ν / k + 1) r :=
    factorial_mul_min_pow_le_risingProd hy r
  have hmP : m ^ r ≤ risingProd (ν / k + 1) r := by
    have hfac1 : (1 : ℝ) ≤ (r.factorial : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos r)
    calc
      m ^ r = 1 * m ^ r := by ring
      _ ≤ (r.factorial : ℝ) * m ^ r :=
          mul_le_mul_of_nonneg_right hfac1 (pow_nonneg hm.le r)
      _ ≤ risingProd (ν / k + 1) r := hlow
  have hA : 0 < (4 * k) ^ r := pow_pos (mul_pos (by norm_num) hk) r
  have hF : 0 < (r.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos r
  have hD0 : 0 < (4 * k) ^ r * (r.factorial : ℝ) * risingProd (ν / k + 1) r :=
    mul_pos (mul_pos hA hF) (risingProd_pos hy r)
  have hB0 : 0 < (4 * k) ^ r * m ^ r * (r.factorial : ℝ) :=
    mul_pos (mul_pos hA (pow_pos hm r)) hF
  have hBD : (4 * k) ^ r * m ^ r * (r.factorial : ℝ) ≤
      (4 * k) ^ r * (r.factorial : ℝ) * risingProd (ν / k + 1) r := by
    have h := mul_le_mul_of_nonneg_left hmP (mul_nonneg hA.le hF.le)
    nlinarith
  have hnum : 0 ≤ (x ^ 2) ^ r := pow_nonneg (sq_nonneg x) r
  calc
    x ^ (2 * r) /
        ((4 * k) ^ r * (r.factorial : ℝ) * risingProd (ν / k + 1) r)
        = (x ^ 2) ^ r /
          ((4 * k) ^ r * (r.factorial : ℝ) * risingProd (ν / k + 1) r) := by
          rw [pow_mul]
    _ ≤ (x ^ 2) ^ r / ((4 * k) ^ r * m ^ r * (r.factorial : ℝ)) :=
          div_le_div_of_nonneg_left hnum hB0 hBD
    _ = (x ^ 2 / (4 * k * m)) ^ r / (r.factorial : ℝ) := by
          rw [div_pow, mul_pow, mul_pow]
          ring
    _ = (x ^ 2 / (4 * k * min (ν / k + 1) 1)) ^ r / (r.factorial : ℝ) := by rfl

lemma summable_kBessel_term {k x ν : ℝ} (hk : 0 < k) (hx : 0 ≤ x) (hν : -k < ν) :
    Summable fun r : ℕ =>
      (k ^ ((ν + k) / k - 1) * Real.Gamma ((ν + k) / k)) /
        ((k ^ (((r : ℝ) * k + ν + k) / k - 1) *
          Real.Gamma (((r : ℝ) * k + ν + k) / k)) *
          (4 : ℝ) ^ r * (r.factorial : ℝ)) * x ^ (2 * r) := by
  exact Summable.of_nonneg_of_le
    (fun r => kBessel_term_nonneg hk hx hν r)
    (fun r => kBessel_term_le_exp_term hk hx hν r)
    (Real.summable_pow_div_factorial _)

/- accepted add_to_file helper 7 -/
lemma Real.rpow_finset_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) (a : ℝ) :
    (∏ i ∈ s, f i) ^ a = ∏ i ∈ s, f i ^ a := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        Real.mul_rpow (hf i (Finset.mem_insert_self i s))
          (Finset.prod_nonneg fun j hj => hf j (Finset.mem_insert_of_mem hj)),
        ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

lemma weighted_geomean_div {N B P Q α : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hP : 0 < P) (hQ : 0 < Q)
    (hsum : α + (1 - α) = 1) :
    (N / (B * P)) ^ α * (N / (B * Q)) ^ (1 - α) =
      N / (B * (P ^ α * Q ^ (1 - α))) := by
  rw [Real.div_rpow hN.le (mul_pos hB hP).le α,
    Real.div_rpow hN.le (mul_pos hB hQ).le (1 - α),
    Real.mul_rpow hB.le hP.le, Real.mul_rpow hB.le hQ.le]
  have hNpow : N ^ α * N ^ (1 - α) = N := by
    rw [← Real.rpow_add hN, hsum, Real.rpow_one]
  have hBpow : B ^ α * B ^ (1 - α) = B := by
    rw [← Real.rpow_add hB, hsum, Real.rpow_one]
  have hNα : N ^ α ≠ 0 := (Real.rpow_pos_of_pos hN α).ne'
  have hNβ : N ^ (1 - α) ≠ 0 := (Real.rpow_pos_of_pos hN (1-α)).ne'
  have hBα : B ^ α ≠ 0 := (Real.rpow_pos_of_pos hB α).ne'
  have hBβ : B ^ (1 - α) ≠ 0 := (Real.rpow_pos_of_pos hB (1-α)).ne'
  have hPα : P ^ α ≠ 0 := (Real.rpow_pos_of_pos hP α).ne'
  have hQβ : Q ^ (1 - α) ≠ 0 := (Real.rpow_pos_of_pos hQ (1-α)).ne'
  field_simp [hNα, hNβ, hBα, hBβ, hPα, hQβ]
  rw [hNpow, hBpow]
  ring

/- accepted add_to_file helper 8 -/
lemma weighted_risingProd_le_risingProd {y z α : ℝ} (hy : 0 < y) (hz : 0 < z)
    (hα : 0 ≤ α) (hβ : 0 ≤ 1 - α) (r : ℕ) :
    risingProd y r ^ α * risingProd z r ^ (1 - α) ≤
      risingProd (α * y + (1 - α) * z) r := by
  have hsum : α + (1 - α) = 1 := by ring
  unfold risingProd
  rw [Real.rpow_finset_prod _ _ (fun j hj => by positivity) α,
    Real.rpow_finset_prod _ _ (fun j hj => by positivity) (1 - α),
    ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod ?_ ?_
  · intro j hj
    exact mul_nonneg (Real.rpow_nonneg (by positivity) α)
      (Real.rpow_nonneg (by positivity) (1 - α))
  · intro j hj
    have hfactor : α * (y + (j : ℝ)) + (1 - α) * (z + (j : ℝ)) =
        α * y + (1 - α) * z + (j : ℝ) := by
      nlinarith
    rw [← hfactor]
    exact Real.geom_mean_le_arith_mean2_weighted hα hβ (by positivity) (by positivity) hsum

/- accepted add_to_file helper 9 -/
lemma kBessel_term_logConvex {k x ν₁ ν₂ α : ℝ} (hk : 0 < k) (hx : 0 < x)
    (hν₁ : -k < ν₁) (hν₂ : -k < ν₂) (hα : 0 ≤ α) (hα₁ : α ≤ 1) (r : ℕ) :
    (k ^ (((α * ν₁ + (1 - α) * ν₂) + k) / k - 1) *
          Real.Gamma (((α * ν₁ + (1 - α) * ν₂) + k) / k)) /
        ((k ^ (((r : ℝ) * k + (α * ν₁ + (1 - α) * ν₂) + k) / k - 1) *
          Real.Gamma (((r : ℝ) * k + (α * ν₁ + (1 - α) * ν₂) + k) / k)) *
          (4 : ℝ) ^ r * (r.factorial : ℝ)) * x ^ (2 * r)
      ≤
      ((k ^ ((ν₁ + k) / k - 1) * Real.Gamma ((ν₁ + k) / k)) /
        ((k ^ (((r : ℝ) * k + ν₁ + k) / k - 1) *
          Real.Gamma (((r : ℝ) * k + ν₁ + k) / k)) *
          (4 : ℝ) ^ r * (r.factorial : ℝ)) * x ^ (2 * r)) ^ α *
      ((k ^ ((ν₂ + k) / k - 1) * Real.Gamma ((ν₂ + k) / k)) /
        ((k ^ (((r : ℝ) * k + ν₂ + k) / k - 1) *
          Real.Gamma (((r : ℝ) * k + ν₂ + k) / k)) *
          (4 : ℝ) ^ r * (r.factorial : ℝ)) * x ^ (2 * r)) ^ (1 - α) := by
  have hβ : 0 ≤ 1 - α := by linarith
  have hmul₁ : (-1 : ℝ) * k < ν₁ := by simpa using hν₁
  have hν₁k : -1 < ν₁ / k := (lt_div_iff₀ hk).mpr hmul₁
  have hy₁ : 0 < ν₁ / k + 1 := by linarith
  have hmul₂ : (-1 : ℝ) * k < ν₂ := by simpa using hν₂
  have hν₂k : -1 < ν₂ / k := (lt_div_iff₀ hk).mpr hmul₂
  have hy₂ : 0 < ν₂ / k + 1 := by linarith
  have hmid : -k < α * ν₁ + (1 - α) * ν₂ := by
    by_cases hα0 : α = 0
    · simp [hα0, hν₂]
    · by_cases hα1 : α = 1
      · simp [hα1, hν₁]
      · have hpα : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
        have hltα : α < 1 := lt_of_le_of_ne hα₁ hα1
        have hpβ : 0 < 1 - α := by linarith
        have h1 : α * (-k) < α * ν₁ := mul_lt_mul_of_pos_left hν₁ hpα
        have h2 : (1 - α) * (-k) < (1 - α) * ν₂ :=
          mul_lt_mul_of_pos_left hν₂ hpβ
        have h := add_lt_add h1 h2
        have hleft : α * (-k) + (1 - α) * (-k) = -k := by ring
        rwa [hleft] at h
  have hymid_eq : (α * ν₁ + (1 - α) * ν₂) / k + 1 =
      α * (ν₁ / k + 1) + (1 - α) * (ν₂ / k + 1) := by
    field_simp [hk.ne']
    ring
  rw [kBessel_term_eq hk hmid r, kBessel_term_eq hk hν₁ r, kBessel_term_eq hk hν₂ r]
  rw [hymid_eq]
  let N : ℝ := x ^ (2 * r)
  let B : ℝ := (4 * k) ^ r * (r.factorial : ℝ)
  let P : ℝ := risingProd (ν₁ / k + 1) r
  let Q : ℝ := risingProd (ν₂ / k + 1) r
  have hN : 0 < N := by
    dsimp [N]
    exact pow_pos hx _
  have hB : 0 < B := by
    dsimp [B]
    exact mul_pos (pow_pos (mul_pos (by norm_num) hk) r)
      (by exact_mod_cast Nat.factorial_pos r)
  have hP : 0 < P := by
    dsimp [P]
    exact risingProd_pos hy₁ r
  have hQ : 0 < Q := by
    dsimp [Q]
    exact risingProd_pos hy₂ r
  have hsum : α + (1 - α) = 1 := by ring
  rw [weighted_geomean_div hN hB hP hQ hsum]
  have hG : 0 < P ^ α * Q ^ (1 - α) :=
    mul_pos (Real.rpow_pos_of_pos hP α) (Real.rpow_pos_of_pos hQ (1 - α))
  have hGle : P ^ α * Q ^ (1 - α) ≤
      risingProd (α * (ν₁ / k + 1) + (1 - α) * (ν₂ / k + 1)) r := by
    dsimp [P, Q]
    exact weighted_risingProd_le_risingProd hy₁ hy₂ hα hβ r
  have hDG : 0 < B * (P ^ α * Q ^ (1 - α)) := mul_pos hB hG
  have hD : B * (P ^ α * Q ^ (1 - α)) ≤
      B * risingProd (α * (ν₁ / k + 1) + (1 - α) * (ν₂ / k + 1)) r :=
    mul_le_mul_of_nonneg_left hGle hB.le
  exact div_le_div_of_nonneg_left hN.le hDG hD

/- accepted add_to_file helper 10 -/
lemma tsum_logConvex_of_pointwise {t : ℝ → ℕ → ℝ} {ν₁ ν₂ α : ℝ}
    (hα : 0 < α) (hα₁ : α < 1)
    (hmid : Summable (t (α * ν₁ + (1 - α) * ν₂)))
    (h₁ : Summable (t ν₁)) (h₂ : Summable (t ν₂))
    (hmid_nonneg : ∀ r, 0 ≤ t (α * ν₁ + (1 - α) * ν₂) r)
    (h₁_nonneg : ∀ r, 0 ≤ t ν₁ r) (h₂_nonneg : ∀ r, 0 ≤ t ν₂ r)
    (hpoint : ∀ r, t (α * ν₁ + (1 - α) * ν₂) r ≤
      t ν₁ r ^ α * t ν₂ r ^ (1 - α)) :
    (∑' r : ℕ, t (α * ν₁ + (1 - α) * ν₂) r) ≤
      (∑' r : ℕ, t ν₁ r) ^ α * (∑' r : ℕ, t ν₂ r) ^ (1 - α) := by
  let β : ℝ := 1 - α
  let p : ℝ := 1 / α
  let q : ℝ := 1 / β
  let A : ℝ := (∑' r : ℕ, t ν₁ r) ^ α
  let B : ℝ := (∑' r : ℕ, t ν₂ r) ^ β
  have hβ : 0 < β := by dsimp [β]; linarith
  have hpq : p.HolderConjugate q := by
    dsimp [p, q, β]
    exact Real.holderConjugate_one_div hα (by linarith) (by ring)
  have hT1_nonneg : 0 ≤ ∑' r : ℕ, t ν₁ r := tsum_nonneg h₁_nonneg
  have hT2_nonneg : 0 ≤ ∑' r : ℕ, t ν₂ r := tsum_nonneg h₂_nonneg
  have hαne : α ≠ 0 := hα.ne'
  have hβne : β ≠ 0 := hβ.ne'
  have hpeq : p = α⁻¹ := by dsimp [p]; rw [one_div]
  have hqeq : q = β⁻¹ := by dsimp [q]; rw [one_div]
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Real.rpow_nonneg hT1_nonneg α
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Real.rpow_nonneg hT2_nonneg β
  have hAp : A ^ p = ∑' r : ℕ, t ν₁ r := by
    dsimp [A]
    rw [hpeq, Real.rpow_rpow_inv hT1_nonneg hαne]
  have hBq : B ^ q = ∑' r : ℕ, t ν₂ r := by
    dsimp [B]
    rw [hqeq, Real.rpow_rpow_inv hT2_nonneg hβne]
  have hf_sum : HasSum (fun r : ℕ => (t ν₁ r ^ α) ^ p) (A ^ p) := by
    rw [hAp]
    exact h₁.hasSum.congr_fun fun r => by
      rw [hpeq, Real.rpow_rpow_inv (h₁_nonneg r) hαne]
  have hg_sum : HasSum (fun r : ℕ => (t ν₂ r ^ β) ^ q) (B ^ q) := by
    rw [hBq]
    exact h₂.hasSum.congr_fun fun r => by
      rw [hqeq, Real.rpow_rpow_inv (h₂_nonneg r) hβne]
  obtain ⟨C, hC_nonneg, hC_le, hC_sum⟩ :=
    Real.inner_le_Lp_mul_Lq_hasSum_of_nonneg hpq hA hB
      (fun r => Real.rpow_nonneg (h₁_nonneg r) α)
      (fun r => Real.rpow_nonneg (h₂_nonneg r) β)
      hf_sum hg_sum
  have hC_eq : C = ∑' r : ℕ, t ν₁ r ^ α * t ν₂ r ^ β := hC_sum.tsum_eq.symm
  have hmid_le_C : (∑' r : ℕ, t (α * ν₁ + (1 - α) * ν₂) r) ≤ C := by
    rw [hC_eq]
    exact Summable.tsum_le_tsum hpoint hmid hC_sum.summable
  exact le_trans hmid_le_C hC_le

/- accepted add_to_file helper 11 -/
lemma kBessel_convexCombo_gt {k ν₁ ν₂ α : ℝ} (hk : 0 < k)
    (hν₁ : -k < ν₁) (hν₂ : -k < ν₂) (hα : 0 ≤ α) (hα₁ : α ≤ 1) :
    -k < α * ν₁ + (1 - α) * ν₂ := by
  by_cases hα0 : α = 0
  · simp [hα0, hν₂]
  · by_cases hα1 : α = 1
    · simp [hα1, hν₁]
    · have hpα : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
      have hltα : α < 1 := lt_of_le_of_ne hα₁ hα1
      have hpβ : 0 < 1 - α := by linarith
      have h1 : α * (-k) < α * ν₁ := mul_lt_mul_of_pos_left hν₁ hpα
      have h2 : (1 - α) * (-k) < (1 - α) * ν₂ :=
        mul_lt_mul_of_pos_left hν₂ hpβ
      have h := add_lt_add h1 h2
      have hleft : α * (-k) + (1 - α) * (-k) = -k := by ring
      rwa [hleft] at h

/- verified submission -/
theorem normalized_modified_kBessel_nonincreasing_logConvex
    (k x : ℝ) (hk : 0 < k) (hx : 0 < x) :
    let Γk : ℝ → ℝ := fun z => k ^ (z / k - 1) * Real.Gamma (z / k)
    let 𝓘 : ℝ → ℝ := fun ν => ∑' r : ℕ,
      Γk (ν + k) /
        (Γk ((r : ℝ) * k + ν + k) * (4 : ℝ) ^ r * (r.factorial : ℝ)) * x ^ (2 * r)
    (∀ ⦃ν μ : ℝ⦄, -k < ν → ν ≤ μ → 𝓘 μ ≤ 𝓘 ν) ∧
      (∀ ⦃ν₁ ν₂ α : ℝ⦄, -k < ν₁ → -k < ν₂ → 0 ≤ α → α ≤ 1 →
        𝓘 (α * ν₁ + (1 - α) * ν₂) ≤ 𝓘 ν₁ ^ α * 𝓘 ν₂ ^ (1 - α)) := by
  dsimp only
  constructor
  · intro ν μ hν hνμ
    have hμ : -k < μ := lt_of_lt_of_le hν hνμ
    exact Summable.tsum_le_tsum
      (fun r => kBessel_term_antitone hk hx.le hν hνμ r)
      (summable_kBessel_term hk hx.le hμ)
      (summable_kBessel_term hk hx.le hν)
  · intro ν₁ ν₂ α hν₁ hν₂ hα hα₁
    let t : ℝ → ℕ → ℝ := fun ν r =>
      (k ^ ((ν + k) / k - 1) * Real.Gamma ((ν + k) / k)) /
        ((k ^ (((r : ℝ) * k + ν + k) / k - 1) *
          Real.Gamma (((r : ℝ) * k + ν + k) / k)) *
          (4 : ℝ) ^ r * (r.factorial : ℝ)) * x ^ (2 * r)
    change (∑' r : ℕ, t (α * ν₁ + (1 - α) * ν₂) r) ≤
      (∑' r : ℕ, t ν₁ r) ^ α * (∑' r : ℕ, t ν₂ r) ^ (1 - α)
    by_cases hα0 : α = 0
    · subst α
      simp [t]
    · by_cases hα1 : α = 1
      · subst α
        simp [t]
      · have hαpos : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
        have hαlt : α < 1 := lt_of_le_of_ne hα₁ hα1
        have hmid : -k < α * ν₁ + (1 - α) * ν₂ :=
          kBessel_convexCombo_gt hk hν₁ hν₂ hα hα₁
        exact tsum_logConvex_of_pointwise (t := t) hαpos hαlt
          (summable_kBessel_term hk hx.le hmid)
          (summable_kBessel_term hk hx.le hν₁)
          (summable_kBessel_term hk hx.le hν₂)
          (fun r => kBessel_term_nonneg hk hx.le hmid r)
          (fun r => kBessel_term_nonneg hk hx.le hν₁ r)
          (fun r => kBessel_term_nonneg hk hx.le hν₂ r)
          (fun r => kBessel_term_logConvex hk hx hν₁ hν₂ hα hα₁ r)
