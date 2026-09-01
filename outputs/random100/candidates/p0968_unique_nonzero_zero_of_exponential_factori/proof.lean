import Mathlib

/- accepted add_to_file helper 1 -/
noncomputable def Ftrunc (n : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    (-1 : ℝ) ^ (n - j) * ((n.factorial : ℝ) / (j.factorial : ℝ)) * t ^ j

lemma Ftrunc_shift_term_eq_neg (n i : ℕ) (hi : i < n) (t : ℝ) :
    (-1 : ℝ) ^ (n - (i + 1)) * ((n.factorial : ℝ) / ((i + 1).factorial : ℝ)) *
        ((i + 1 : ℝ) * t ^ i)
      =
    - ((-1 : ℝ) ^ (n - i) * ((n.factorial : ℝ) / (i.factorial : ℝ)) * t ^ i) := by
  have hfact : ((i + 1).factorial : ℝ) = (i + 1 : ℝ) * (i.factorial : ℝ) := by
    norm_num [Nat.factorial_succ]
  have hsub : n - (i + 1) + 1 = n - i := by omega
  have hpow : (-1 : ℝ) ^ (n - i) = - (-1 : ℝ) ^ (n - (i + 1)) := by
    rw [← hsub]
    rw [pow_succ]
    ring
  rw [hfact, hpow]
  field_simp

lemma Ftrunc_deriv_eq_neg_sum (n : ℕ) (t : ℝ) :
    deriv (Ftrunc n) t =
      - ∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ (n - i) * ((n.factorial : ℝ) / (i.factorial : ℝ)) * t ^ i := by
  unfold Ftrunc
  rw [deriv_fun_sum]
  · rw [Finset.sum_range_succ']
    simp
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    exact Ftrunc_shift_term_eq_neg n i hi' t
  · intro i hi
    fun_prop

lemma Ftrunc_add_deriv (n : ℕ) (t : ℝ) :
    Ftrunc n t + deriv (Ftrunc n) t = t ^ n := by
  rw [Ftrunc_deriv_eq_neg_sum]
  unfold Ftrunc
  rw [Finset.sum_range_succ]
  simp
  field_simp

/- accepted add_to_file helper 2 -/
lemma Ftrunc_differentiableAt (n : ℕ) (t : ℝ) : DifferentiableAt ℝ (Ftrunc n) t := by
  unfold Ftrunc
  fun_prop

lemma hasDerivAt_exp_mul_Ftrunc (n : ℕ) (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Real.exp t * Ftrunc n t) (Real.exp t * t ^ n) t := by
  have hF := (Ftrunc_differentiableAt n t).hasDerivAt
  have h := (Real.hasDerivAt_exp t).mul hF
  convert h using 1
  rw [← Ftrunc_add_deriv]
  ring

lemma Ftrunc_integral (n : ℕ) (a b : ℝ) :
    ∫ t in a..b, Real.exp t * t ^ n =
      Real.exp b * Ftrunc n b - Real.exp a * Ftrunc n a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    exact hasDerivAt_exp_mul_Ftrunc n x
  · exact (Real.continuous_exp.mul (continuous_pow n)).intervalIntegrable a b

/- accepted add_to_file helper 3 -/
noncomputable def Porig (n : ℕ) (a x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    (-1 : ℝ) ^ (n - j) * ((n.factorial : ℝ) / (j.factorial : ℝ)) *
      a ^ ((j : ℤ) - 1) * (a - (j : ℝ)) * x ^ j

lemma Porig_succ_term (n i : ℕ) (a x : ℝ) :
    (-1 : ℝ) ^ (n - (i + 1)) * ((n.factorial : ℝ) / ((i + 1).factorial : ℝ)) *
        a ^ (((i + 1 : ℕ) : ℤ) - 1) * (a - ((i + 1 : ℕ) : ℝ)) * x ^ (i + 1)
      =
    (-1 : ℝ) ^ (n - (i + 1)) * ((n.factorial : ℝ) / ((i + 1).factorial : ℝ)) *
        (a * x) ^ (i + 1)
      -
      x * ((-1 : ℝ) ^ (n - (i + 1)) * ((n.factorial : ℝ) / (i.factorial : ℝ)) *
        (a * x) ^ i) := by
  have hz : a ^ (((i + 1 : ℕ) : ℤ) - 1) = a ^ i := by
    norm_num
  rw [hz]
  have hfact : ((i + 1).factorial : ℝ) = (i + 1 : ℝ) * (i.factorial : ℝ) := by
    norm_num [Nat.factorial_succ]
  rw [hfact]
  field_simp
  norm_num
  ring

lemma Porig_D_eq_neg_Fterm (n i : ℕ) (hi : i < n) (a x : ℝ) :
    (-1 : ℝ) ^ (n - (i + 1)) * ((n.factorial : ℝ) / (i.factorial : ℝ)) *
        (a * x) ^ i
      =
    - ((-1 : ℝ) ^ (n - i) * ((n.factorial : ℝ) / (i.factorial : ℝ)) * (a * x) ^ i) := by
  have hsub : n - (i + 1) + 1 = n - i := by omega
  have hpow : (-1 : ℝ) ^ (n - i) = - (-1 : ℝ) ^ (n - (i + 1)) := by
    rw [← hsub]
    rw [pow_succ]
    ring
  rw [hpow]
  ring

/- accepted add_to_file helper 4 -/
lemma Porig_eq (n : ℕ) {a x : ℝ} (ha : a ≠ 0) :
    Porig n a x = (1 + x) * Ftrunc n (a * x) - x * (a * x) ^ n := by
  classical
  let D : ℕ → ℝ := fun i ↦
    (-1 : ℝ) ^ (n - (i + 1)) * ((n.factorial : ℝ) / (i.factorial : ℝ)) * (a * x) ^ i
  have hdecomp : Porig n a x = Ftrunc n (a * x) - x * ∑ i ∈ Finset.range n, D i := by
    unfold Porig Ftrunc
    rw [Finset.sum_range_succ']
    rw [Finset.sum_range_succ']
    have hzero :
        (-1 : ℝ) ^ (n - 0) * ((n.factorial : ℝ) / (((0 : ℕ).factorial : ℝ))) *
          a ^ (((0 : ℕ) : ℤ) - 1) * (a - ((0 : ℕ) : ℝ)) * x ^ 0
        = (-1 : ℝ) ^ n * (n.factorial : ℝ) := by
      norm_num [zpow_neg_one, ha]
    rw [hzero]
    have hsum := Finset.sum_congr (rfl : Finset.range n = Finset.range n)
      (fun i hi ↦ Porig_succ_term n i a x)
    rw [hsum]
    rw [Finset.sum_sub_distrib]
    rw [← Finset.mul_sum]
    dsimp [D]
    norm_num
    ring
  rw [hdecomp]
  have hD :
      ∑ i ∈ Finset.range n, D i =
        - ∑ i ∈ Finset.range n,
          (-1 : ℝ) ^ (n - i) * ((n.factorial : ℝ) / (i.factorial : ℝ)) * (a * x) ^ i := by
    dsimp [D]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact Porig_D_eq_neg_Fterm n i (Finset.mem_range.mp hi) a x
  rw [hD]
  unfold Ftrunc
  rw [Finset.sum_range_succ]
  field_simp
  simp
  ring_nf

/- accepted add_to_file helper 5 -/
lemma exp_pow_endpoint_integral (n : ℕ) (x a b : ℝ) :
    ∫ u in b..a, Real.exp (x * u) * (x * u ^ n + (n : ℝ) * u ^ (n - 1)) =
      Real.exp (x * a) * a ^ n - Real.exp (x * b) * b ^ n := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    have hexp : HasDerivAt (fun u : ℝ ↦ Real.exp (x * u)) (x * Real.exp (x * u)) u := by
      have h := (Real.hasDerivAt_exp (x * u)).comp u ((hasDerivAt_id u).const_mul x)
      simpa [mul_assoc, mul_comm, mul_left_comm] using h
    have hpow : HasDerivAt (fun u : ℝ ↦ u ^ n) ((n : ℝ) * u ^ (n - 1)) u := by
      simpa using hasDerivAt_pow n u
    have h := hexp.mul hpow
    convert h using 1
    ring
  · have hc : Continuous fun u : ℝ ↦ Real.exp (x * u) * (x * u ^ n + (n : ℝ) * u ^ (n - 1)) := by
      continuity
    exact hc.intervalIntegrable b a

/- accepted add_to_file helper 6 -/
lemma exp_Ftrunc_diff (n : ℕ) (x a b : ℝ) :
    Real.exp ((a - b) * x) * Ftrunc n (a * x) - Ftrunc n (b * x)
      =
    Real.exp (-(b * x)) *
      ∫ s in b * x..a * x, Real.exp s * s ^ n := by
  have hmul : Real.exp (-(b * x)) * Real.exp (a * x) = Real.exp ((a - b) * x) := by
    rw [← Real.exp_add]
    ring_nf
  have hone : Real.exp (-(b * x)) * Real.exp (b * x) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    Real.exp ((a - b) * x) * Ftrunc n (a * x) - Ftrunc n (b * x)
        = Real.exp (-(b * x)) *
            (Real.exp (a * x) * Ftrunc n (a * x) - Real.exp (b * x) * Ftrunc n (b * x)) := by
          rw [mul_sub]
          congr 1
          · calc
              Real.exp ((a - b) * x) * Ftrunc n (a * x)
                  = (Real.exp (-(b * x)) * Real.exp (a * x)) * Ftrunc n (a * x) := by
                    rw [hmul]
              _ = Real.exp (-(b * x)) * (Real.exp (a * x) * Ftrunc n (a * x)) := by
                    ring
          · calc
              Ftrunc n (b * x)
                  = (Real.exp (-(b * x)) * Real.exp (b * x)) * Ftrunc n (b * x) := by
                    rw [hone]
                    simp
              _ = Real.exp (-(b * x)) * (Real.exp (b * x) * Ftrunc n (b * x)) := by
                    ring
    _ = Real.exp (-(b * x)) *
          ∫ s in b * x..a * x, Real.exp s * s ^ n := by
          rw [Ftrunc_integral]

/- accepted add_to_file helper 7 -/
lemma scaled_exp_pow_integral (n : ℕ) {x a b : ℝ} (hx : x ≠ 0) :
    ∫ s in b * x..a * x, Real.exp s * s ^ n =
      x ^ (n + 1) * ∫ u in b..a, Real.exp (x * u) * u ^ n := by
  have hcomp :
      ∫ u in b..a, Real.exp (x * u) * (x * u) ^ n =
        x⁻¹ * ∫ s in x * b..x * a, Real.exp s * s ^ n := by
    simpa using intervalIntegral.integral_comp_mul_left
      (fun s : ℝ ↦ Real.exp s * s ^ n) hx (a := b) (b := a)
  have hI :
      ∫ s in x * b..x * a, Real.exp s * s ^ n =
        x * ∫ u in b..a, Real.exp (x * u) * (x * u) ^ n := by
    rw [hcomp]
    field_simp [hx]
  have hcongr :
      ∫ u in b..a, Real.exp (x * u) * (x * u) ^ n =
        x ^ n * ∫ u in b..a, Real.exp (x * u) * u ^ n := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    ring
  rw [show b * x = x * b by ring, show a * x = x * a by ring]
  rw [hI, hcongr]
  ring

/- accepted add_to_file helper 8 -/
lemma exp_sub_factor (x a b A B : ℝ) :
    Real.exp ((a - b) * x) * A - B =
      Real.exp (-(b * x)) * (Real.exp (x * a) * A - Real.exp (x * b) * B) := by
  have hmul : Real.exp (-(b * x)) * Real.exp (x * a) = Real.exp ((a - b) * x) := by
    rw [← Real.exp_add]
    ring_nf
  have hone : Real.exp (-(b * x)) * Real.exp (x * b) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  rw [mul_sub]
  congr 1
  · calc
      Real.exp ((a - b) * x) * A
          = (Real.exp (-(b * x)) * Real.exp (x * a)) * A := by rw [hmul]
      _ = Real.exp (-(b * x)) * (Real.exp (x * a) * A) := by ring
  · calc
      B = (Real.exp (-(b * x)) * Real.exp (x * b)) * B := by
        rw [hone]
        simp
      _ = Real.exp (-(b * x)) * (Real.exp (x * b) * B) := by ring

lemma exp_pow_endpoint_diff (n : ℕ) (x a b : ℝ) :
    Real.exp ((a - b) * x) * a ^ n - b ^ n =
      Real.exp (-(b * x)) *
        ∫ u in b..a, Real.exp (x * u) * (x * u ^ n + (n : ℝ) * u ^ (n - 1)) := by
  rw [exp_sub_factor, exp_pow_endpoint_integral]

/- accepted add_to_file helper 9 -/
lemma combine_exp_integrals (n : ℕ) (hn : 1 ≤ n) (x a b : ℝ) :
    (1 + x) * (∫ u in b..a, Real.exp (x * u) * u ^ n)
      - (∫ u in b..a, Real.exp (x * u) * (x * u ^ n + (n : ℝ) * u ^ (n - 1)))
    =
    ∫ u in b..a, Real.exp (x * u) * u ^ (n - 1) * (u - (n : ℝ)) := by
  have hA : IntervalIntegrable (fun u : ℝ ↦ Real.exp (x * u) * u ^ n)
      MeasureTheory.volume b a := by
    have hc : Continuous fun u : ℝ ↦ Real.exp (x * u) * u ^ n := by continuity
    exact hc.intervalIntegrable b a
  have hB : IntervalIntegrable
      (fun u : ℝ ↦ Real.exp (x * u) * (x * u ^ n + (n : ℝ) * u ^ (n - 1)))
      MeasureTheory.volume b a := by
    have hc : Continuous fun u : ℝ ↦ Real.exp (x * u) * (x * u ^ n + (n : ℝ) * u ^ (n - 1)) := by
      continuity
    exact hc.intervalIntegrable b a
  rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_sub (hA.const_mul (1 + x)) hB]
  apply intervalIntegral.integral_congr
  intro u hu
  cases n with
  | zero => omega
  | succ m =>
      have hm : m + 1 - 1 = m := by omega
      rw [hm]
      ring

/- accepted add_to_file helper 10 -/
noncomputable def Hdiff (n : ℕ) (x a b : ℝ) : ℝ :=
  Real.exp ((a - b) * x) * Porig n a x - Porig n b x

noncomputable def Kbase (n : ℕ) (a b x : ℝ) : ℝ :=
  ∫ u in b..a, Real.exp (x * u) * u ^ (n - 1) * (u - (n : ℝ))

lemma Hdiff_eq_of_ne (n : ℕ) (hn : 1 ≤ n) {x a b : ℝ} (hx : x ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Hdiff n x a b = Real.exp (-(b * x)) * x ^ (n + 1) * Kbase n a b x := by
  unfold Hdiff Kbase
  rw [Porig_eq n ha, Porig_eq n hb]
  have hcalc :
      Real.exp ((a - b) * x) * ((1 + x) * Ftrunc n (a * x) - x * (a * x) ^ n) -
          ((1 + x) * Ftrunc n (b * x) - x * (b * x) ^ n)
      =
      (1 + x) * (Real.exp ((a - b) * x) * Ftrunc n (a * x) - Ftrunc n (b * x))
        - x ^ (n + 1) * (Real.exp ((a - b) * x) * a ^ n - b ^ n) := by
    ring
  rw [hcalc]
  rw [exp_Ftrunc_diff]
  rw [scaled_exp_pow_integral n hx]
  rw [exp_pow_endpoint_diff]
  have hcombine := combine_exp_integrals n hn x a b
  rw [← hcombine]
  ring

lemma Hdiff_zero (n : ℕ) {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Hdiff n 0 a b = 0 := by
  unfold Hdiff
  rw [Porig_eq n ha, Porig_eq n hb]
  simp

lemma Hdiff_eq (n : ℕ) (hn : 1 ≤ n) (x a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Hdiff n x a b = Real.exp (-(b * x)) * x ^ (n + 1) * Kbase n a b x := by
  by_cases hx : x = 0
  · subst x
    rw [Hdiff_zero n ha hb]
    have hnp : n + 1 ≠ 0 := by omega
    simp [hnp]
  · exact Hdiff_eq_of_ne n hn hx ha hb

/- accepted add_to_file helper 11 -/
noncomputable def Kcenter (n k : ℕ) (x : ℝ) : ℝ :=
  ∫ v in -(k : ℝ)..(k : ℝ),
    Real.exp (x * v) * ((n : ℝ) + v) ^ (n - 1) * v

lemma Kbase_eq_exp_mul_Kcenter (n k : ℕ) (x : ℝ) :
    Kbase n ((n : ℝ) + (k : ℝ)) ((n : ℝ) - (k : ℝ)) x =
      Real.exp ((n : ℝ) * x) * Kcenter n k x := by
  unfold Kbase Kcenter
  have hshift :
      ∫ v in -(k : ℝ)..(k : ℝ),
          Real.exp (x * v) * ((n : ℝ) + v) ^ (n - 1) * v
        =
      ∫ u in (n : ℝ) - (k : ℝ)..(n : ℝ) + (k : ℝ),
        Real.exp (x * (u - (n : ℝ))) * u ^ (n - 1) * (u - (n : ℝ)) := by
    have h := intervalIntegral.integral_comp_add_left
      (fun u : ℝ ↦ Real.exp (x * (u - (n : ℝ))) * u ^ (n - 1) * (u - (n : ℝ)))
      (n : ℝ) (a := -(k : ℝ)) (b := (k : ℝ))
    simpa [sub_eq_add_neg] using h
  rw [hshift]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u hu
  dsimp
  have hexp : Real.exp (x * u) = Real.exp ((n : ℝ) * x) * Real.exp (x * (u - (n : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/- accepted add_to_file helper 12 -/
lemma Hdiff_eq_center (n k : ℕ) (hn : 2 ≤ n) (hk₂ : k ≤ n - 1) (x : ℝ) :
    Hdiff n x ((n : ℝ) + (k : ℝ)) ((n : ℝ) - (k : ℝ)) =
      Real.exp ((k : ℝ) * x) * x ^ (n + 1) * Kcenter n k x := by
  have hn1 : 1 ≤ n := by omega
  have hkn : k < n := by omega
  have ha : ((n : ℝ) + (k : ℝ)) ≠ 0 := by
    have : 0 < (n : ℝ) + (k : ℝ) := by positivity
    exact ne_of_gt this
  have hb : ((n : ℝ) - (k : ℝ)) ≠ 0 := by
    have hcastlt : (k : ℝ) < (n : ℝ) := by exact_mod_cast hkn
    have : 0 < (n : ℝ) - (k : ℝ) := sub_pos.mpr hcastlt
    exact ne_of_gt this
  rw [Hdiff_eq n hn1 x _ _ ha hb]
  rw [Kbase_eq_exp_mul_Kcenter]
  have hexp : Real.exp (-(((n : ℝ) - (k : ℝ)) * x)) * Real.exp ((n : ℝ) * x)
      = Real.exp ((k : ℝ) * x) := by
    rw [← Real.exp_add]
    congr 1
    have hknle : k ≤ n := by omega
    have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
      exact Nat.cast_sub hknle
    have hknr : ((k : ℝ) + ((n : ℝ) - (k : ℝ))) = (n : ℝ) := by
      rw [← hcast]
      have : k + (n - k) = n := by omega
      exact_mod_cast this
    nlinarith
  rw [show Real.exp (-(((n : ℝ) - (k : ℝ)) * x)) * x ^ (n + 1) *
        (Real.exp ((n : ℝ) * x) * Kcenter n k x)
      =
      (Real.exp (-(((n : ℝ) - (k : ℝ)) * x)) * Real.exp ((n : ℝ) * x)) *
        x ^ (n + 1) * Kcenter n k x by ring]
  rw [hexp]

/- accepted add_to_file helper 13 -/
lemma Kcenter_strictMono {n k : ℕ} (hn : 2 ≤ n) (hk₁ : 1 ≤ k)
    (hk₂ : k ≤ n - 1) :
    StrictMono (Kcenter n k) := by
  intro x y hxy
  let g : ℝ → ℝ := fun v ↦
    (Real.exp (y * v) - Real.exp (x * v)) * ((n : ℝ) + v) ^ (n - 1) * v
  have hdiff :
      Kcenter n k y - Kcenter n k x =
        ∫ v in -(k : ℝ)..(k : ℝ), g v := by
    unfold Kcenter
    dsimp [g]
    have hf : IntervalIntegrable
        (fun v : ℝ ↦ Real.exp (y * v) * ((n : ℝ) + v) ^ (n - 1) * v)
        MeasureTheory.volume (-(k : ℝ)) (k : ℝ) := by
      have hc : Continuous fun v : ℝ ↦ Real.exp (y * v) * ((n : ℝ) + v) ^ (n - 1) * v := by
        continuity
      exact hc.intervalIntegrable _ _
    have hg : IntervalIntegrable
        (fun v : ℝ ↦ Real.exp (x * v) * ((n : ℝ) + v) ^ (n - 1) * v)
        MeasureTheory.volume (-(k : ℝ)) (k : ℝ) := by
      have hc : Continuous fun v : ℝ ↦ Real.exp (x * v) * ((n : ℝ) + v) ^ (n - 1) * v := by
        continuity
      exact hc.intervalIntegrable _ _
    rw [← intervalIntegral.integral_sub hf hg]
    apply intervalIntegral.integral_congr
    intro v hv
    ring
  have hpos : 0 < ∫ v in -(k : ℝ)..(k : ℝ), g v := by
    apply intervalIntegral.integral_pos
    · have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk₁
      linarith
    · have hc : Continuous g := by
        dsimp [g]
        continuity
      exact hc.continuousOn
    · intro v hv
      dsimp [g]
      have hvge : -(k : ℝ) ≤ v := hv.1.le
      have hvle : v ≤ (k : ℝ) := hv.2
      have hnv : 0 ≤ ((n : ℝ) + v) ^ (n - 1) := by
        have hklt : (k : ℝ) < (n : ℝ) := by
          have hkn : k < n := by omega
          exact_mod_cast hkn
        have hbase : 0 < (n : ℝ) + v := by nlinarith
        exact pow_nonneg hbase.le _
      by_cases hv0 : 0 ≤ v
      · have hexp : 0 ≤ Real.exp (y * v) - Real.exp (x * v) := by
          have : x * v ≤ y * v := mul_le_mul_of_nonneg_right hxy.le hv0
          exact sub_nonneg.mpr (Real.exp_le_exp.mpr this)
        exact mul_nonneg (mul_nonneg hexp hnv) hv0
      · have hv0' : v ≤ 0 := le_of_not_ge hv0
        have hexp : Real.exp (y * v) - Real.exp (x * v) ≤ 0 := by
          have : y * v ≤ x * v := mul_le_mul_of_nonpos_right hxy.le hv0'
          exact sub_nonpos.mpr (Real.exp_le_exp.mpr this)
        have hprod : (Real.exp (y * v) - Real.exp (x * v)) * ((n : ℝ) + v) ^ (n - 1) ≤ 0 := by
          exact mul_nonpos_of_nonpos_of_nonneg hexp hnv
        exact mul_nonneg_of_nonpos_of_nonpos hprod hv0'
    · use 1
      constructor
      · constructor
        · have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk₁
          linarith
        · exact_mod_cast hk₁
      · dsimp [g]
        have hexp : 0 < Real.exp y - Real.exp x := by
          exact sub_pos.mpr (Real.exp_lt_exp.mpr hxy)
        have hpow : 0 < ((n : ℝ) + (1 : ℝ)) ^ (n - 1) := by
          have hb : 0 < (n : ℝ) + 1 := by positivity
          exact pow_pos hb _
        have hprod := mul_pos (mul_pos hexp hpow) (by norm_num : (0 : ℝ) < 1)
        simpa [mul_assoc] using hprod
  rw [← hdiff] at hpos
  linarith

/- accepted add_to_file helper 14 -/
lemma Kcenter_pair (n k : ℕ) (x : ℝ) :
    Kcenter n k x =
      ∫ v in (0 : ℝ)..(k : ℝ),
        v * (((n : ℝ) + v) ^ (n - 1) * Real.exp (x * v)
          - ((n : ℝ) - v) ^ (n - 1) * Real.exp (-(x * v))) := by
  let f : ℝ → ℝ := fun v ↦ Real.exp (x * v) * ((n : ℝ) + v) ^ (n - 1) * v
  have hcont : Continuous f := by
    dsimp [f]
    continuity
  have hneg :
      ∫ v in (0 : ℝ)..(k : ℝ), f (-v) =
        ∫ v in -(k : ℝ)..(0 : ℝ), f v := by
    simpa using intervalIntegral.integral_comp_neg f (a := (0 : ℝ)) (b := (k : ℝ))
  have hsplit :
      (∫ v in -(k : ℝ)..(0 : ℝ), f v) + (∫ v in (0 : ℝ)..(k : ℝ), f v) =
        ∫ v in -(k : ℝ)..(k : ℝ), f v := by
    simpa using
      (intervalIntegral.integral_add_adjacent_intervals
        (a := -(k : ℝ)) (b := (0 : ℝ)) (c := (k : ℝ)) (μ := MeasureTheory.volume)
        (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _))
  unfold Kcenter
  change ∫ v in -(k : ℝ)..(k : ℝ), f v = _
  calc
    ∫ v in -(k : ℝ)..(k : ℝ), f v
        = (∫ v in -(k : ℝ)..(0 : ℝ), f v) + (∫ v in (0 : ℝ)..(k : ℝ), f v) := hsplit.symm
    _ = (∫ v in (0 : ℝ)..(k : ℝ), f (-v)) + (∫ v in (0 : ℝ)..(k : ℝ), f v) := by
          exact congrArg (fun z ↦ z + (∫ v in (0 : ℝ)..(k : ℝ), f v)) hneg.symm
    _ = ∫ v in (0 : ℝ)..(k : ℝ),
          v * (((n : ℝ) + v) ^ (n - 1) * Real.exp (x * v)
            - ((n : ℝ) - v) ^ (n - 1) * Real.exp (-(x * v))) := by
          have hi : IntervalIntegrable (fun v : ℝ ↦ f (-v)) MeasureTheory.volume 0 (k : ℝ) := by
            exact (hcont.comp continuous_neg).intervalIntegrable _ _
          have hp : IntervalIntegrable f MeasureTheory.volume 0 (k : ℝ) := by
            exact hcont.intervalIntegrable _ _
          have hcongr :
              ∫ v in (0 : ℝ)..(k : ℝ),
                  v * (((n : ℝ) + v) ^ (n - 1) * Real.exp (x * v)
                    - ((n : ℝ) - v) ^ (n - 1) * Real.exp (-(x * v)))
                =
              ∫ v in (0 : ℝ)..(k : ℝ), f (-v) + f v := by
            apply intervalIntegral.integral_congr
            intro v hv
            dsimp [f]
            have hnegexp : x * -v = -(x * v) := by ring
            rw [hnegexp]
            ring
          rw [hcongr]
          exact (intervalIntegral.integral_add hi hp).symm

/- accepted add_to_file helper 15 -/
lemma Kcenter_zero_pos {n k : ℕ} (hn : 2 ≤ n) (hk₁ : 1 ≤ k)
    (hk₂ : k ≤ n - 1) : 0 < Kcenter n k 0 := by
  rw [Kcenter_pair]
  simp
  apply intervalIntegral.integral_pos
  · have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk₁
    exact this
  · have hc : Continuous fun v : ℝ ↦
        v * (((n : ℝ) + v) ^ (n - 1) - ((n : ℝ) - v) ^ (n - 1)) := by
      continuity
    exact hc.continuousOn
  · intro v hv
    have hv0 : 0 ≤ v := hv.1.le
    have hvle : v ≤ (k : ℝ) := hv.2
    have hkn : (k : ℝ) < (n : ℝ) := by
      have : k < n := by omega
      exact_mod_cast this
    have hb1 : 0 ≤ (n : ℝ) - v := by nlinarith
    have hb2 : (n : ℝ) - v ≤ (n : ℝ) + v := by nlinarith
    have hpow := pow_le_pow_left₀ hb1 hb2 (n - 1)
    exact mul_nonneg hv0 (sub_nonneg.mpr hpow)
  · use 1
    constructor
    · constructor
      · norm_num
      · exact_mod_cast hk₁
    · have hkn : (k : ℝ) < (n : ℝ) := by
        have : k < n := by omega
        exact_mod_cast this
      have hb : 0 ≤ (n : ℝ) - 1 := by
        have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk₁
        nlinarith
      have hbase : (n : ℝ) - 1 < (n : ℝ) + 1 := by nlinarith
      have hexp : n - 1 ≠ 0 := by omega
      have hpow : ((n : ℝ) - 1) ^ (n - 1) < ((n : ℝ) + 1) ^ (n - 1) :=
        pow_lt_pow_left₀ hbase hb hexp
      have hbr : 0 < ((n : ℝ) + 1) ^ (n - 1) - ((n : ℝ) - 1) ^ (n - 1) :=
        sub_pos.mpr hpow
      exact mul_pos (by norm_num : (0 : ℝ) < 1) hbr

/- accepted add_to_file helper 16 -/
lemma neg_exp_weight_integral (n : ℕ) (hn : 1 ≤ n) (a b : ℝ) :
    ∫ u in b..a, Real.exp (-u) * u ^ (n - 1) * (u - (n : ℝ)) =
      Real.exp (-b) * b ^ n - Real.exp (-a) * a ^ n := by
  have hderiv :
      ∀ u ∈ Set.uIcc b a,
        HasDerivAt (fun u : ℝ ↦ Real.exp (-u) * u ^ n)
          (-(Real.exp (-u) * u ^ (n - 1) * (u - (n : ℝ)))) u := by
    intro u hu
    have hexp : HasDerivAt (fun u : ℝ ↦ Real.exp (-u)) (-Real.exp (-u)) u := by
      have h := (Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_id u).neg
      simpa using h
    have hpow : HasDerivAt (fun u : ℝ ↦ u ^ n) ((n : ℝ) * u ^ (n - 1)) u := by
      simpa using hasDerivAt_pow n u
    have h := hexp.mul hpow
    convert h using 1
    cases n with
    | zero => omega
    | succ m =>
        have hm : m + 1 - 1 = m := by omega
        rw [hm]
        ring
  have hint : IntervalIntegrable
      (fun u : ℝ ↦ -(Real.exp (-u) * u ^ (n - 1) * (u - (n : ℝ))))
      MeasureTheory.volume b a := by
    have hc : Continuous fun u : ℝ ↦ -(Real.exp (-u) * u ^ (n - 1) * (u - (n : ℝ))) := by
      continuity
    exact hc.intervalIntegrable b a
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have htarget :
      ∫ u in b..a, Real.exp (-u) * u ^ (n - 1) * (u - (n : ℝ))
        =
      -(∫ u in b..a, -(Real.exp (-u) * u ^ (n - 1) * (u - (n : ℝ)))) := by
    rw [← intervalIntegral.integral_neg]
    simp
  rw [htarget, hI]
  ring

/- accepted add_to_file helper 17 -/
lemma endpoint_log_ratio {n k : ℕ} (hk₁ : 1 ≤ k) (hk₂ : k ≤ n - 1) :
    2 * (k : ℝ) / (n : ℝ) <
      Real.log (((n : ℝ) + (k : ℝ)) / ((n : ℝ) - (k : ℝ))) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hbpos : (0 : ℝ) < (n : ℝ) - (k : ℝ) := by
    have hkn : k < n := by omega
    have : (k : ℝ) < (n : ℝ) := by exact_mod_cast hkn
    exact sub_pos.mpr this
  let t : ℝ := 2 * (k : ℝ) / ((n : ℝ) - (k : ℝ))
  have htpos : 0 < t := by
    dsimp [t]
    positivity
  have hbound := Real.lt_log_one_add_of_pos htpos
  have harg : 1 + t = ((n : ℝ) + (k : ℝ)) / ((n : ℝ) - (k : ℝ)) := by
    dsimp [t]
    field_simp [ne_of_gt hbpos]
    ring
  have hleft : 2 * t / (t + 2) = 2 * (k : ℝ) / (n : ℝ) := by
    dsimp [t]
    field_simp [ne_of_gt hbpos, ne_of_gt hnpos]
    ring
  rw [harg, hleft] at hbound
  exact hbound

/- accepted add_to_file helper 18 -/
lemma endpoint_exp_pow_lt {n k : ℕ} (hk₁ : 1 ≤ k) (hk₂ : k ≤ n - 1) :
    Real.exp (-((n : ℝ) - (k : ℝ))) * ((n : ℝ) - (k : ℝ)) ^ n <
      Real.exp (-((n : ℝ) + (k : ℝ))) * ((n : ℝ) + (k : ℝ)) ^ n := by
  let N : ℝ := n
  let K : ℝ := k
  let B : ℝ := N - K
  let A : ℝ := N + K
  have hN : 0 < N := by
    dsimp [N]
    have : 0 < n := by omega
    exact_mod_cast this
  have hB : 0 < B := by
    dsimp [B, N, K]
    have hkn : k < n := by omega
    have : (k : ℝ) < (n : ℝ) := by exact_mod_cast hkn
    exact sub_pos.mpr this
  have hA : 0 < A := by positivity
  have hleftpos : 0 < Real.exp (-B) * B ^ n := by positivity
  have hrightpos : 0 < Real.exp (-A) * A ^ n := by positivity
  have hlog : Real.log (Real.exp (-B) * B ^ n) <
      Real.log (Real.exp (-A) * A ^ n) := by
    have hleftlog : Real.log (Real.exp (-B) * B ^ n) = -B + N * Real.log B := by
      rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt (pow_pos hB n))]
      rw [Real.log_exp, Real.log_pow]
    have hrightlog : Real.log (Real.exp (-A) * A ^ n) = -A + N * Real.log A := by
      rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt (pow_pos hA n))]
      rw [Real.log_exp, Real.log_pow]
    rw [hleftlog, hrightlog]
    have hratio : 2 * K / N < Real.log (A / B) := by
      dsimp [A, B, N, K]
      exact endpoint_log_ratio hk₁ hk₂
    have hmul := mul_lt_mul_of_pos_left hratio hN
    have htwo : N * (2 * K / N) = 2 * K := by
      field_simp [ne_of_gt hN]
    have hlogdiv : Real.log (A / B) = Real.log A - Real.log B := by
      exact Real.log_div (ne_of_gt hA) (ne_of_gt hB)
    have hdiff : A - B = 2 * K := by
      dsimp [A, B]
      ring
    rw [htwo] at hmul
    rw [hlogdiv] at hmul
    nlinarith
  exact (Real.log_lt_log_iff hleftpos hrightpos).mp hlog

/- accepted add_to_file helper 19 -/
lemma Kcenter_neg_one_neg {n k : ℕ} (hn : 2 ≤ n) (hk₁ : 1 ≤ k)
    (hk₂ : k ≤ n - 1) : Kcenter n k (-1) < 0 := by
  have hn1 : 1 ≤ n := by omega
  let A : ℝ := (n : ℝ) + (k : ℝ)
  let B : ℝ := (n : ℝ) - (k : ℝ)
  have hbaseeq : Kbase n A B (-1) =
      Real.exp (-B) * B ^ n - Real.exp (-A) * A ^ n := by
    unfold Kbase
    dsimp [A, B]
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (neg_exp_weight_integral n hn1 ((n : ℝ) + (k : ℝ)) ((n : ℝ) - (k : ℝ)))
  have hbaseneg : Kbase n A B (-1) < 0 := by
    rw [hbaseeq]
    have h := endpoint_exp_pow_lt hk₁ hk₂
    dsimp [A, B]
    exact sub_neg.mpr h
  have hrel := Kbase_eq_exp_mul_Kcenter n k (-1)
  dsimp [A, B] at hbaseeq hbaseneg
  have hrel' : Kbase n ((n : ℝ) + (k : ℝ)) ((n : ℝ) - (k : ℝ)) (-1) =
      Real.exp (-(n : ℝ)) * Kcenter n k (-1) := by
    simpa using hrel
  have hK : Kcenter n k (-1) =
      Real.exp (n : ℝ) * Kbase n ((n : ℝ) + (k : ℝ)) ((n : ℝ) - (k : ℝ)) (-1) := by
    calc
      Kcenter n k (-1)
          = Real.exp (n : ℝ) * (Real.exp (-(n : ℝ)) * Kcenter n k (-1)) := by
            have hone : Real.exp (n : ℝ) * Real.exp (-(n : ℝ)) = 1 := by
              rw [← Real.exp_add]
              simp
            rw [show Real.exp (n : ℝ) * (Real.exp (-(n : ℝ)) * Kcenter n k (-1))
                = (Real.exp (n : ℝ) * Real.exp (-(n : ℝ))) * Kcenter n k (-1) by ring]
            rw [hone]
            simp
      _ = Real.exp (n : ℝ) * Kbase n ((n : ℝ) + (k : ℝ)) ((n : ℝ) - (k : ℝ)) (-1) := by
            rw [← hrel']
  rw [hK]
  exact mul_neg_of_pos_of_neg (Real.exp_pos _) hbaseneg

/- accepted add_to_file helper 20 -/
lemma Kcenter_continuous (n k : ℕ) : Continuous (Kcenter n k) := by
  unfold Kcenter
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have hf : Continuous fun p : ℝ × ℝ ↦
      Real.exp (p.1 * p.2) * ((n : ℝ) + p.2) ^ (n - 1) * p.2 := by
    continuity
  exact hf

lemma exists_Kcenter_root {n k : ℕ} (hn : 2 ≤ n) (hk₁ : 1 ≤ k)
    (hk₂ : k ≤ n - 1) :
    ∃ c : ℝ, -1 < c ∧ c < 0 ∧ Kcenter n k c = 0 := by
  have hcont : ContinuousOn (Kcenter n k) (Set.Icc (-1 : ℝ) 0) :=
    (Kcenter_continuous n k).continuousOn
  have hivt := intermediate_value_Ioo (by norm_num : (-1 : ℝ) ≤ 0) hcont
  have hzero_mem : (0 : ℝ) ∈ Set.Ioo (Kcenter n k (-1)) (Kcenter n k 0) := by
    exact ⟨Kcenter_neg_one_neg hn hk₁ hk₂, Kcenter_zero_pos hn hk₁ hk₂⟩
  have himage := hivt hzero_mem
  rcases himage with ⟨c, hc, hfc⟩
  exact ⟨c, hc.1, hc.2, hfc⟩

/- accepted add_to_file helper 21 -/
noncomputable def Hformal (n k : ℕ) (x : ℝ) : ℝ :=
  Real.exp (2 * (k : ℝ) * x) *
      Porig n ((n : ℝ) + (k : ℝ)) x
    - Porig n ((n : ℝ) - (k : ℝ)) x

lemma Hformal_eq_Hdiff (n k : ℕ) (x : ℝ) :
    Hformal n k x =
      Hdiff n x ((n : ℝ) + (k : ℝ)) ((n : ℝ) - (k : ℝ)) := by
  unfold Hformal Hdiff
  congr 1
  congr 1
  ring

lemma Hformal_eq_factor (n k : ℕ) (hn : 2 ≤ n) (hk₂ : k ≤ n - 1) (x : ℝ) :
    Hformal n k x =
      Real.exp ((k : ℝ) * x) * x ^ (n + 1) * Kcenter n k x := by
  rw [Hformal_eq_Hdiff]
  exact Hdiff_eq_center n k hn hk₂ x

/- verified submission -/
theorem unique_nonzero_zero_of_exponential_factorial_sum
    (n k : ℕ) (hn : 2 ≤ n) (hk₁ : 1 ≤ k) (hk₂ : k ≤ n - 1) :
    let h : ℝ → ℝ := fun x ↦
      Real.exp (2 * (k : ℝ) * x) *
          (∑ j ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ (n - j) *
              ((n.factorial : ℝ) / (j.factorial : ℝ)) *
              ((n : ℝ) + (k : ℝ)) ^ ((j : ℤ) - 1) *
              ((n : ℝ) + (k : ℝ) - (j : ℝ)) * x ^ j)
        - (∑ j ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ (n - j) *
              ((n.factorial : ℝ) / (j.factorial : ℝ)) *
              ((n : ℝ) - (k : ℝ)) ^ ((j : ℤ) - 1) *
              ((n : ℝ) - (k : ℝ) - (j : ℝ)) * x ^ j)
    ∃ c : ℝ, -1 < c ∧ c < 0 ∧ h c = 0 ∧
      ∀ x : ℝ, h x = 0 ↔ x = 0 ∨ x = c := by
  dsimp
  rcases exists_Kcenter_root hn hk₁ hk₂ with ⟨c, hcneg, hcneg0, hcK⟩
  refine ⟨c, hcneg, hcneg0, ?_, ?_⟩
  · show Hformal n k c = 0
    rw [Hformal_eq_factor n k hn hk₂ c, hcK]
    simp
  · intro x
    show Hformal n k x = 0 ↔ x = 0 ∨ x = c
    rw [Hformal_eq_factor n k hn hk₂ x]
    constructor
    · intro hz
      have hz' := (mul_eq_zero.mp hz)
      rcases hz' with hz' | hz'
      · have hxp := (mul_eq_zero.mp hz')
        rcases hxp with hexp | hxp
        · exact False.elim ((ne_of_gt (Real.exp_pos _)) hexp)
        · left
          exact eq_zero_of_pow_eq_zero hxp
      · right
        have hEq : Kcenter n k x = Kcenter n k c := by
          rw [hz', hcK]
        exact (Kcenter_strictMono hn hk₁ hk₂).injective hEq
    · intro hxc
      rcases hxc with rfl | rfl
      · simp
      · rw [hcK]
        simp
