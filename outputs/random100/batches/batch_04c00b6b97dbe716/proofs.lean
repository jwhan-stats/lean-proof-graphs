import Mathlib

/- Generated only to amortize Mathlib loading during graph export. -/

namespace Rollout_p2674_graded_dual_rational_map_mem_completion

/- accepted add_to_file helper 1 -/
lemma finite_family_support_of_dual_pointwise_finite
    {ι : Type*} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (v : ι → V)
    (h : ∀ l : Module.Dual ℂ V, Set.Finite {i | l (v i) ≠ 0}) :
    Set.Finite {i | v i ≠ 0} := by
  by_contra hs
  obtain ⟨b, hb_subset, hb_span, hb_li⟩ := exists_linearIndependent ℂ (Set.range v)
  let p : Submodule ℂ V := Submodule.span ℂ b
  have hrange : Set.range (Subtype.val : b → V) = b := Subtype.range_val
  have hp_eq : Submodule.span ℂ (Set.range (Subtype.val : b → V)) = p := by
    simp [p, hrange]
  have hv_mem : ∀ i, v i ∈ p := by
    intro i
    have : v i ∈ Submodule.span ℂ (Set.range v) :=
      Submodule.subset_span (Set.mem_range_self i)
    simpa [p, hb_span] using this
  let B : Module.Basis b ℂ p :=
    (Module.Basis.span hb_li).map (LinearEquiv.ofEq _ _ hp_eq)
  by_cases hbfin : b.Finite
  · haveI : Fintype b := hbfin.fintype
    have hcoordfin : ∀ j : b,
        Set.Finite {i | (B.repr ⟨v i, hv_mem i⟩) j ≠ 0} := by
      intro j
      obtain ⟨l, hl⟩ := LinearMap.exists_extend (p := p) (B.coord j)
      have hval : ∀ i, l (v i) = (B.repr ⟨v i, hv_mem i⟩) j := by
        intro i
        have happ := LinearMap.congr_fun hl ⟨v i, hv_mem i⟩
        change l (v i) = (B.coord j) ⟨v i, hv_mem i⟩ at happ
        simpa [Module.Basis.coord] using happ
      simpa [hval] using h l
    have hUnionfin : Set.Finite (⋃ j : b, {i | (B.repr ⟨v i, hv_mem i⟩) j ≠ 0}) := by
      exact Set.Finite.iUnion Set.finite_univ (fun j _ => hcoordfin j)
        (fun j hj => by simp at hj)
    have hsubset : {i | v i ≠ 0} ⊆ ⋃ j : b, {i | (B.repr ⟨v i, hv_mem i⟩) j ≠ 0} := by
      intro i hi
      have hrepr_ne : B.repr ⟨v i, hv_mem i⟩ ≠ 0 := by
        intro hr
        apply hi
        have hz : (⟨v i, hv_mem i⟩ : p) = 0 := by
          apply B.repr.injective
          simpa using hr
        exact congrArg Subtype.val hz
      rw [← Finsupp.support_nonempty_iff] at hrepr_ne
      rcases hrepr_ne with ⟨j, hj⟩
      exact Set.mem_iUnion.mpr ⟨j, Finsupp.mem_support_iff.mp hj⟩
    have hsinf : Set.Infinite {i | v i ≠ 0} := Set.not_finite.mp hs
    exact (hsinf.mono hsubset) hUnionfin
  · have hbinf : b.Infinite := Set.not_finite.mp hbfin
    haveI : Infinite b := hbinf.to_subtype
    let φ : p →ₗ[ℂ] ℂ := B.constr ℂ (fun _ : b => (1 : ℂ))
    obtain ⟨l, hl⟩ := LinearMap.exists_extend (p := p) φ
    let e : b → ι := fun j => Classical.choose (hb_subset j.property)
    have he : ∀ j : b, v (e j) = j.1 := fun j => Classical.choose_spec (hb_subset j.property)
    have he_inj : Function.Injective e := by
      intro j k hjk
      apply Subtype.ext
      have hvj := he j
      have hvk := he k
      rw [← hvj, hjk, hvk]
    have hB_coe : ∀ j : b, ((B j : p) : V) = j.1 := by
      intro j
      simp [B]
    have hl_e : ∀ j : b, l (v (e j)) = 1 := by
      intro j
      have happ := LinearMap.congr_fun hl ⟨v (e j), hv_mem (e j)⟩
      change l (v (e j)) = φ ⟨v (e j), hv_mem (e j)⟩ at happ
      rw [happ]
      change ((B.constr ℂ) fun _ : b => (1 : ℂ)) ⟨v (e j), hv_mem (e j)⟩ = 1
      have hsub : (⟨v (e j), hv_mem (e j)⟩ : p) = B j := by
        ext
        simp [he j, hB_coe j]
      rw [hsub, Module.Basis.constr_basis]
    have hsub : Set.range e ⊆ {i | l (v i) ≠ 0} := by
      rintro i ⟨j, rfl⟩
      change l (v (e j)) ≠ 0
      rw [hl_e j]
      exact one_ne_zero
    exact ((Set.infinite_range_of_injective he_inj).mono hsub) (h l)

/- verified submission -/
theorem graded_dual_rational_map_mem_completion
    {n : ℕ} (hn : 0 < n)
    (W : ℂ → Type*) [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)]
    (f : {z : Fin n → ℂ // Function.Injective z} →
      Module.Dual ℂ (DirectSum ℂ (fun a => Module.Dual ℂ (W a))))
    (p : Fin n → Fin n → ℤ)
    (g : (Fin n →₀ ℕ) → (∀ a, W a))
    (C : ℂ) :
    letI := Classical.decEq ℂ
    (∀ w' : DirectSum ℂ (fun a => Module.Dual ℂ (W a)),
      ∃ (q : Fin n → Fin n → ℕ) (P : MvPolynomial (Fin n) ℂ),
        ∀ z : {z : Fin n → ℂ // Function.Injective z},
          f z w' = MvPolynomial.eval z.1 P /
            (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (z.1 i - z.1 j) ^ q i j)) →
    (∀ w' : DirectSum ℂ (fun a => Module.Dual ℂ (W a)),
      ∃ P : MvPolynomial (Fin n) ℂ,
        (∀ α : Fin n →₀ ℕ,
          MvPolynomial.coeff α P =
            (DirectSum.toModule ℂ ℂ ℂ
              (fun a => (Module.Dual.eval ℂ (W a)) (g α a))) w') ∧
        ∀ z : {z : Fin n → ℂ // Function.Injective z},
          (∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
              (z.1 i - z.1 j) ^ p i j) * f z w' = MvPolynomial.eval z.1 P) →
    (∀ (α : Fin n →₀ ℕ) (a : ℂ),
      a ≠ C + (α.sum fun _ e => e : ℂ) → g α a = 0) →
    ∀ z : {z : Fin n → ℂ // Function.Injective z},
      ∃ b : ∀ a, W a,
        f z = DirectSum.toModule ℂ ℂ ℂ
          (fun a => (Module.Dual.eval ℂ (W a)) (b a)) := by
  intro hrational hcleared hhom z
  have hfinite_g : ∀ a : ℂ, Set.Finite {α : Fin n →₀ ℕ | g α a ≠ 0} := by
    intro a
    apply finite_family_support_of_dual_pointwise_finite (fun α : Fin n →₀ ℕ => g α a)
    intro l
    obtain ⟨P, hcoeff, hid⟩ := hcleared (DirectSum.lof ℂ ℂ (fun b => Module.Dual ℂ (W b)) a l)
    apply Set.Finite.subset (Finset.finite_toSet P.support)
    intro α hα
    exact Finsupp.mem_support_iff.mpr (by
      have hc := hcoeff α
      rw [DirectSum.toModule_lof, Module.Dual.eval_apply] at hc
      change MvPolynomial.coeff α P ≠ 0
      rwa [hc])
  let S : ℂ → Finset (Fin n →₀ ℕ) := fun a => (hfinite_g a).toFinset
  let mval : (Fin n →₀ ℕ) → ℂ := fun α => α.prod fun i e => z.1 i ^ e
  let D : ℂ := ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (z.1 i - z.1 j) ^ p i j
  have hD : D ≠ 0 := by
    dsimp [D]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    apply zpow_ne_zero
    rw [sub_ne_zero]
    apply z.2.ne
    rw [Finset.mem_Ioi] at hj
    exact ne_of_lt hj
  let b : ∀ a, W a := fun a =>
    D⁻¹ • ∑ α ∈ S a, mval α • g α a
  have hcomponent : ∀ (a : ℂ) (l : Module.Dual ℂ (W a)),
      f z (DirectSum.lof ℂ ℂ (fun c => Module.Dual ℂ (W c)) a l) = l (b a) := by
    intro a l
    obtain ⟨P, hcoeff, hid⟩ :=
      hcleared (DirectSum.lof ℂ ℂ (fun c => Module.Dual ℂ (W c)) a l)
    have hPsub : P.support ⊆ S a := by
      intro α hα
      rw [MvPolynomial.mem_support_iff] at hα
      have hc := hcoeff α
      rw [DirectSum.toModule_lof, Module.Dual.eval_apply] at hc
      change α ∈ (hfinite_g a).toFinset
      rw [Set.Finite.mem_toFinset]
      change g α a ≠ 0
      intro hg
      rw [hg, map_zero] at hc
      exact hα hc
    have h_eval : MvPolynomial.eval z.1 P = ∑ α ∈ S a, mval α * l (g α a) := by
      have h_eval_support :
          MvPolynomial.eval z.1 P = ∑ α ∈ P.support, mval α * l (g α a) := by
        conv_lhs => rw [MvPolynomial.as_sum P]
        rw [MvPolynomial.eval_sum]
        apply Finset.sum_congr rfl
        intro α hα
        rw [MvPolynomial.eval_monomial, hcoeff α, DirectSum.toModule_lof,
          Module.Dual.eval_apply]
        change l (g α a) * mval α = mval α * l (g α a)
        ring
      rw [h_eval_support]
      apply Finset.sum_subset hPsub
      intro α hαS hαP
      have hc : MvPolynomial.coeff α P = l (g α a) := by
        simpa [DirectSum.toModule_lof, Module.Dual.eval_apply] using hcoeff α
      have hc0 : MvPolynomial.coeff α P = 0 := by
        by_contra hne
        exact hαP ((MvPolynomial.mem_support_iff).mpr hne)
      have hl0 : l (g α a) = 0 := by
        rw [← hc, hc0]
      rw [hl0, mul_zero]
    have hf : f z (DirectSum.lof ℂ ℂ (fun c => Module.Dual ℂ (W c)) a l) =
        D⁻¹ * MvPolynomial.eval z.1 P := by
      apply (eq_inv_mul_iff_mul_eq₀ hD).mpr
      change D * f z (DirectSum.lof ℂ ℂ (fun c => Module.Dual ℂ (W c)) a l) = _
      exact hid z
    rw [hf, h_eval]
    dsimp [b]
    rw [map_smul, map_sum]
    apply congrArg (fun t : ℂ => D⁻¹ * t)
    apply Finset.sum_congr rfl
    intro α hα
    rw [map_smul]
    rfl
  refine ⟨b, ?_⟩
  apply DirectSum.linearMap_ext ℂ
  intro a
  apply LinearMap.ext
  intro l
  change f z (DirectSum.lof ℂ ℂ (fun c => Module.Dual ℂ (W c)) a l) =
    (DirectSum.toModule ℂ ℂ ℂ fun c => (Module.Dual.eval ℂ (W c)) (b c))
      (DirectSum.lof ℂ ℂ (fun c => Module.Dual ℂ (W c)) a l)
  rw [hcomponent a l, DirectSum.toModule_lof, Module.Dual.eval_apply]

end Rollout_p2674_graded_dual_rational_map_mem_completion

namespace Rollout_p0292_two_positive_roots_of_mu

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

end Rollout_p0292_two_positive_roots_of_mu

namespace Rollout_p2753_planeposet_union_islinearorder

/- verified submission -/
theorem planePoset_union_isLinearOrder
    {P : Type*} [Finite P]
    (leH leR : P → P → Prop)
    (hH : IsPartialOrder P leH)
    (hR : IsPartialOrder P leR)
    (hcompat : ∀ {x y : P}, x ≠ y →
      ((leH x y ∨ leH y x) ↔ ¬ (leR x y ∨ leR y x))) :
    IsLinearOrder P (fun x y => leH x y ∨ leR x y) := by
  let U : P → P → Prop := fun x y => leH x y ∨ leR x y
  change IsLinearOrder P U
  have hreflU : ∀ x : P, U x x := by
    intro x
    exact Or.inl (hH.refl x)
  have htotalU : ∀ x y : P, U x y ∨ U y x := by
    intro x y
    by_cases hxy : x = y
    · subst y
      exact Or.inl (hreflU x)
    · by_cases hr : leR x y ∨ leR y x
      · rcases hr with hrxy | hryx
        · exact Or.inl (Or.inr hrxy)
        · exact Or.inr (Or.inr hryx)
      · have hh : leH x y ∨ leH y x := (hcompat hxy).mpr hr
        rcases hh with hhxy | hhyx
        · exact Or.inl (Or.inl hhxy)
        · exact Or.inr (Or.inl hhyx)
  have hantisymmU : ∀ x y : P, U x y → U y x → x = y := by
    intro x y hxy hyx
    by_cases heq : x = y
    · exact heq
    · rcases hxy with hxyH | hxyR
      · rcases hyx with hyxH | hyxR
        · exact hH.antisymm x y hxyH hyxH
        · have hnoR : ¬ (leR x y ∨ leR y x) :=
            (hcompat heq).mp (Or.inl hxyH)
          exact False.elim (hnoR (Or.inr hyxR))
      · rcases hyx with hyxH | hyxR
        · have hnoR : ¬ (leR x y ∨ leR y x) :=
            (hcompat heq).mp (Or.inr hyxH)
          exact False.elim (hnoR (Or.inl hxyR))
        · exact hR.antisymm x y hxyR hyxR
  have htransU : ∀ x y z : P, U x y → U y z → U x z := by
    intro x y z hxy hyz
    rcases hxy with hxyH | hxyR
    · rcases hyz with hyzH | hyzR
      · exact Or.inl (hH.trans x y z hxyH hyzH)
      · by_cases hxyeq : x = y
        · subst y
          exact Or.inr hyzR
        · by_cases hyzeq : y = z
          · subst z
            exact Or.inl hxyH
          · rcases htotalU x z with hxzU | hzxU
            · exact hxzU
            · rcases hzxU with hzxH | hzxR
              · have hzyH : leH z y := hH.trans z x y hzxH hxyH
                have hnoR : ¬ (leR y z ∨ leR z y) :=
                  (hcompat hyzeq).mp (Or.inr hzyH)
                exact False.elim (hnoR (Or.inl hyzR))
              · have hyxR : leR y x := hR.trans y z x hyzR hzxR
                have hnoR : ¬ (leR x y ∨ leR y x) :=
                  (hcompat hxyeq).mp (Or.inl hxyH)
                exact False.elim (hnoR (Or.inr hyxR))
    · rcases hyz with hyzH | hyzR
      · by_cases hxyeq : x = y
        · subst y
          exact Or.inl hyzH
        · by_cases hyzeq : y = z
          · subst z
            exact Or.inr hxyR
          · rcases htotalU x z with hxzU | hzxU
            · exact hxzU
            · rcases hzxU with hzxH | hzxR
              · have hyxH : leH y x := hH.trans y z x hyzH hzxH
                have hnoR : ¬ (leR x y ∨ leR y x) :=
                  (hcompat hxyeq).mp (Or.inr hyxH)
                exact False.elim (hnoR (Or.inl hxyR))
              · have hzyR : leR z y := hR.trans z x y hzxR hxyR
                have hnoR : ¬ (leR y z ∨ leR z y) :=
                  (hcompat hyzeq).mp (Or.inl hyzH)
                exact False.elim (hnoR (Or.inr hzyR))
      · exact Or.inr (hR.trans x y z hxyR hyzR)
  exact {
    refl := hreflU
    trans := htransU
    antisymm := hantisymmU
    total := htotalU
  }

end Rollout_p2753_planeposet_union_islinearorder

namespace Rollout_p1232_diagonal_homogeneous_polynomial_norm_bound

/- accepted add_to_file helper 1 -/
lemma one_le_diagonal_lp_norm {𝕂 : Type*} [RCLike 𝕂] {k : ℕ} (p : ENNReal)
    (hp : 1 < p) (α : Fin k → 𝕂) {j : Fin k} (hj : α j = 1) :
    1 ≤ (if p = ⊤ then ‖α‖ else
      Real.rpow (∑ i : Fin k, Real.rpow ‖α i‖ p.toReal) (1 / p.toReal)) := by
  by_cases hpt : p = ⊤
  · simp [hpt]
    calc
      (1:ℝ) = ‖α j‖ := by simp [hj]
      _ ≤ ‖α‖ := norm_le_pi_norm α j
  · have hpreal : 0 < p.toReal := by
      exact ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hp.le)) hpt
    simp [hpt]
    have hterm : (1:ℝ) ≤ ∑ i : Fin k, ‖α i‖ ^ p.toReal := by
      calc
        (1:ℝ) = ‖α j‖ ^ p.toReal := by simp [hj]
        _ ≤ ∑ i : Fin k, ‖α i‖ ^ p.toReal := by
          exact Finset.single_le_sum (fun i _ => Real.rpow_nonneg (norm_nonneg _) _) (Finset.mem_univ j)
    have h := Real.rpow_le_rpow zero_le_one hterm (by positivity : 0 ≤ 1 / p.toReal)
    simpa [Real.one_rpow] using h

/- accepted add_to_file helper 2 -/
noncomputable section

instance instNormSubmoduleDualCLM
    {𝕂 E : Type*} [RCLike 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
    (K : Submodule 𝕂 E) : Norm (K →L[𝕂] 𝕂) :=
  ContinuousLinearMap.hasOpNorm

lemma diagonal_functional_restriction_norm_ge
    {𝕂 E : Type*} [RCLike 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
    {k : ℕ} (φ : Fin k → E →L[𝕂] 𝕂)
    {A B : ℝ} (hA : 0 < A) (p : ENNReal) (hp : 1 < p)
    (hφ : ∀ α : Fin k → 𝕂,
      A * (if p = ⊤ then ‖α‖ else
        Real.rpow (∑ j : Fin k, Real.rpow ‖α j‖ p.toReal) (1 / p.toReal)) ≤
          ‖∑ j : Fin k, α j • φ j‖ ∧
      ‖∑ j : Fin k, α j • φ j‖ ≤
        B * (if p = ⊤ then ‖α‖ else
          Real.rpow (∑ j : Fin k, Real.rpow ‖α j‖ p.toReal) (1 / p.toReal)))
    (j : Fin k) :
    A ≤ ‖(φ j).comp
      ((⨅ i : {i // i ∈ Finset.univ \ {j}}, ((φ i.1).toLinearMap).ker).subtypeL)‖ := by
  let I := {i : Fin k // i ∈ Finset.univ \ {j}}
  let K : Submodule 𝕂 E := ⨅ i : I, ((φ i.1).toLinearMap).ker
  let f : K →L[𝕂] 𝕂 := (φ j).comp K.subtypeL
  rcases exists_extension_norm_eq K f with ⟨g, hgext, hgnorm⟩
  have hker : ⨅ i : I, ((φ i.1).toLinearMap).ker ≤ (g - φ j).toLinearMap.ker := by
    intro x hx
    rw [LinearMap.mem_ker]
    have hgx : g x = φ j x := by
      simpa [f, K] using hgext ⟨x, hx⟩
    simp [hgx]
  rcases (Submodule.mem_span_range_iff_exists_fun 𝕂).mp
      (mem_span_of_iInf_ker_le_ker hker) with ⟨c, hc⟩
  let β : Fin k → 𝕂 := fun l =>
    if h : l ∈ Finset.univ \ {j} then c ⟨l, h⟩ else 1
  have hgsum : g = ∑ l : Fin k, β l • φ l := by
    apply ContinuousLinearMap.ext
    intro x
    have hsum_split :
        (∑ l : Fin k, β l • φ l) x =
          φ j x + ∑ i : I, c i * (φ i.1) x := by
      rw [ContinuousLinearMap.sum_apply]
      simp_rw [ContinuousLinearMap.smul_apply]
      calc
        ∑ l : Fin k, β l * φ l x =
            β j * φ j x + ∑ l ∈ Finset.univ \ {j}, β l * φ l x := by
          exact Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ) j
            (fun l => β l * φ l x) (fun h => False.elim (by simpa using h))
        _ = φ j x + ∑ i : I, c i * (φ i.1) x := by
          congr 1
          · simp [β]
          · rw [Finset.sum_subtype (Finset.univ \ {j}) (fun l => Iff.rfl)
              (fun l => β l * φ l x)]
            apply Finset.sum_congr rfl
            intro i hi
            have hne : i.1 ≠ j := by
              have hnotmem : i.1 ∉ ({j} : Finset (Fin k)) :=
                (Finset.mem_sdiff.mp i.2).2
              intro hij
              exact hnotmem (by simpa [hij])
            simp [β, hne]
    have hcx : (∑ i : I, c i • (φ i.1).toLinearMap) x = (g - φ j).toLinearMap x := by
      simpa using congrFun (congrArg DFunLike.coe hc) x
    simp at hcx
    rw [hsum_split]
    calc
      g x = (g x - φ j x) + φ j x := by abel
      _ = (∑ i : I, c i * (φ i.1) x) + φ j x := by rw [← hcx]
      _ = φ j x + ∑ i : I, c i * (φ i.1) x := by rw [add_comm]
  have hone : β j = 1 := by simp [β]
  have hnormβ := one_le_diagonal_lp_norm p hp β hone
  calc
    A = A * 1 := by rw [mul_one]
    _ ≤ A * (if p = ⊤ then ‖β‖ else
        Real.rpow (∑ i : Fin k, Real.rpow ‖β i‖ p.toReal) (1 / p.toReal)) := by
          exact mul_le_mul_of_nonneg_left hnormβ hA.le
    _ ≤ ‖∑ l : Fin k, β l • φ l‖ := (hφ β).1
    _ = ‖g‖ := by rw [← hgsum]
    _ = ‖f‖ := hgnorm

end

/- accepted add_to_file helper 3 -/
noncomputable section

lemma diagonal_pairing_le_of_lp_le_one
    {𝕂 E : Type*} [RCLike 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
    {k : ℕ} (φ : Fin k → E →L[𝕂] 𝕂)
    {B : ℝ} (hB : 0 < B) (p : ENNReal) (hp : 1 < p) (hpt : p ≠ ⊤)
    (hφ : ∀ α : Fin k → 𝕂,
      ‖∑ j : Fin k, α j • φ j‖ ≤
        B * Real.rpow (∑ j : Fin k, Real.rpow ‖α j‖ p.toReal) (1 / p.toReal))
    (x : E) (hx : ‖x‖ ≤ 1) (g : Fin k → NNReal)
    (hg : Real.rpow (∑ i : Fin k, ((g i : ℝ) ^ p.toReal)) (1 / p.toReal) ≤ 1) :
    ∑ i : Fin k, (g i : ℝ) * ‖φ i x‖ ≤ B := by
  let y : Fin k → 𝕂 := fun i => φ i x
  let phase : 𝕂 → 𝕂 := fun z => if z = 0 then 0 else (‖z‖ : 𝕂) / z
  let β : Fin k → 𝕂 := fun i => ((g i : ℝ) : 𝕂) * phase (y i)
  have hphase_norm : ∀ z : 𝕂, ‖phase z‖ ≤ 1 := by
    intro z
    by_cases hz : z = 0
    · simp [phase, hz]
    · simp only [phase, if_neg hz]
      rw [norm_div, RCLike.norm_ofReal]
      rw [abs_of_nonneg (norm_nonneg z)]
      rw [div_self (norm_ne_zero_iff.mpr hz)]
  have hphase_apply : ∀ z : 𝕂, phase z * z = (‖z‖ : 𝕂) := by
    intro z
    by_cases hz : z = 0
    · simp [phase, hz]
    · simp only [phase, if_neg hz]
      field_simp [hz]
  have hβnorm : ∀ i, ‖β i‖ ≤ (g i : ℝ) := by
    intro i
    have hg0 : 0 ≤ (g i : ℝ) := NNReal.coe_nonneg _
    calc
      ‖β i‖ = |(g i : ℝ)| * ‖phase (y i)‖ := by
        simp [β, norm_mul]
      _ ≤ |(g i : ℝ)| * 1 := by
        exact mul_le_mul_of_nonneg_left (hphase_norm (y i)) (abs_nonneg _)
      _ = (g i : ℝ) := by simp [abs_of_nonneg hg0]
  have hpreal : 0 < p.toReal := by
    exact ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hp.le)) hpt
  have hβlp : Real.rpow (∑ i : Fin k, ‖β i‖ ^ p.toReal) (1 / p.toReal) ≤ 1 := by
    have hsum : (∑ i : Fin k, ‖β i‖ ^ p.toReal) ≤
        ∑ i : Fin k, ((g i : ℝ) ^ p.toReal) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Real.rpow_le_rpow (norm_nonneg _) (hβnorm i) hpreal.le
    calc
      Real.rpow (∑ i : Fin k, ‖β i‖ ^ p.toReal) (1 / p.toReal)
          ≤ Real.rpow (∑ i : Fin k, ((g i : ℝ) ^ p.toReal)) (1 / p.toReal) := by
            exact Real.rpow_le_rpow (by positivity) hsum (by positivity)
      _ ≤ 1 := hg
  let F : E →L[𝕂] 𝕂 := ∑ i : Fin k, β i • φ i
  have hF : ‖F‖ ≤ B := by
    calc
      ‖F‖ ≤ B * Real.rpow (∑ i : Fin k, ‖β i‖ ^ p.toReal) (1 / p.toReal) := hφ β
      _ ≤ B * 1 := mul_le_mul_of_nonneg_left hβlp hB.le
      _ = B := by ring
  have hFx : ‖F x‖ ≤ B := by
    calc
      ‖F x‖ ≤ ‖F‖ * ‖x‖ := ContinuousLinearMap.le_opNorm F x
      _ ≤ ‖F‖ * 1 := mul_le_mul_of_nonneg_left hx (norm_nonneg F)
      _ = ‖F‖ := by ring
      _ ≤ B := hF
  have hvalue : F x = ((∑ i : Fin k, (g i : ℝ) * ‖y i‖ : ℝ) : 𝕂) := by
    calc
      F x = ∑ i : Fin k, β i * y i := by
        simp [F, y, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
      _ = ∑ i : Fin k, (((g i : ℝ) * ‖y i‖ : ℝ) : 𝕂) := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          β i * y i = ((g i : ℝ) : 𝕂) * (phase (y i) * y i) := by
            simp [β, mul_assoc]
          _ = ((g i : ℝ) : 𝕂) * (‖y i‖ : 𝕂) := by rw [hphase_apply]
          _ = (((g i : ℝ) * ‖y i‖ : ℝ) : 𝕂) := by norm_num [RCLike.ofReal_mul]
      _ = ((∑ i : Fin k, (g i : ℝ) * ‖y i‖ : ℝ) : 𝕂) := by
        norm_num [map_sum]
  have hsum_nonneg : 0 ≤ ∑ i : Fin k, (g i : ℝ) * ‖y i‖ := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _)
  have hnormcast : ‖(((∑ i : Fin k, (g i : ℝ) * ‖y i‖) : ℝ) : 𝕂)‖ =
      ∑ i : Fin k, (g i : ℝ) * ‖y i‖ := by
    rw [RCLike.norm_ofReal, abs_of_nonneg hsum_nonneg]
  calc
    ∑ i : Fin k, (g i : ℝ) * ‖φ i x‖ = ∑ i : Fin k, (g i : ℝ) * ‖y i‖ := by
      simp [y]
    _ = ‖(((∑ i : Fin k, (g i : ℝ) * ‖y i‖) : ℝ) : 𝕂)‖ := hnormcast.symm
    _ = ‖F x‖ := by rw [← hvalue]
    _ ≤ B := hFx

end

/- accepted add_to_file helper 4 -/
noncomputable section

lemma diagonal_coordinate_lq_norm_le
    {𝕂 E : Type*} [RCLike 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
    {k : ℕ} (φ : Fin k → E →L[𝕂] 𝕂)
    {B : ℝ} (hB : 0 < B) (p : ENNReal) (hp : 1 < p) (hpt : p ≠ ⊤)
    (hφ : ∀ α : Fin k → 𝕂,
      ‖∑ j : Fin k, α j • φ j‖ ≤
        B * Real.rpow (∑ j : Fin k, Real.rpow ‖α j‖ p.toReal) (1 / p.toReal))
    (x : E) (hx : ‖x‖ ≤ 1) :
    Real.rpow (∑ i : Fin k, ‖φ i x‖ ^ (ENNReal.conjExponent p).toReal)
        (1 / (ENNReal.conjExponent p).toReal) ≤ B := by
  let q : ENNReal := ENNReal.conjExponent p
  haveI hpq : p.HolderConjugate q := ENNReal.HolderConjugate.conjExponent hp.le
  have hpreal : 1 < p.toReal := by
    have h := (ENNReal.toReal_lt_toReal (by norm_num : (1 : ENNReal) ≠ ⊤) hpt).2 hp
    simpa using h
  have hqp_real : q.toReal.HolderConjugate p.toReal :=
    (ENNReal.HolderConjugate.toReal hpreal).symm
  let f : Fin k → NNReal := fun i => ⟨‖φ i x‖, norm_nonneg _⟩
  let qnorm : NNReal := (∑ i : Fin k, f i ^ q.toReal) ^ (1 / q.toReal)
  have hgreat := NNReal.isGreatest_Lp Finset.univ f hqp_real
  rcases hgreat.1 with ⟨g, hgset, hgpair⟩
  have hgreal : (∑ i : Fin k, ((g i : ℝ) ^ p.toReal)) ≤ 1 := by
    exact_mod_cast hgset
  have hp_pos : 0 < p.toReal := by positivity
  have hgroot : (∑ i : Fin k, ((g i : ℝ) ^ p.toReal)) ^ (1 / p.toReal) ≤ 1 := by
    calc
      (∑ i : Fin k, ((g i : ℝ) ^ p.toReal)) ^ (1 / p.toReal)
          ≤ (1 : ℝ) ^ (1 / p.toReal) := by
            exact Real.rpow_le_rpow (by positivity) hgreal (by positivity)
      _ = 1 := by simp
  have hpair : ∑ i : Fin k, (g i : ℝ) * ‖φ i x‖ ≤ B :=
    diagonal_pairing_le_of_lp_le_one φ hB p hp hpt hφ x hx g hgroot
  have hpair' : ((∑ i : Fin k, f i * g i : NNReal) : ℝ) =
      ∑ i : Fin k, (g i : ℝ) * ‖φ i x‖ := by
    simp [f, mul_comm]
  have hqnorm_eq : (qnorm : ℝ) =
      Real.rpow (∑ i : Fin k, ‖φ i x‖ ^ q.toReal) (1 / q.toReal) := by
    simp [qnorm, f]
  calc
    Real.rpow (∑ i : Fin k, ‖φ i x‖ ^ (ENNReal.conjExponent p).toReal)
        (1 / (ENNReal.conjExponent p).toReal)
        = (qnorm : ℝ) := by simp [q, hqnorm_eq]
    _ = (∑ i : Fin k, (g i : ℝ) * ‖φ i x‖) := by
      calc
        (qnorm : ℝ) = ((∑ i : Fin k, f i * g i : NNReal) : ℝ) := by
          exact congrArg (fun r : NNReal => (r : ℝ)) hgpair.symm
        _ = ∑ i : Fin k, (g i : ℝ) * ‖φ i x‖ := hpair'
    _ ≤ B := hpair

end

/- accepted add_to_file helper 5 -/
lemma sum_nat_pow_le_of_lq_norm_le
    {k : ℕ} (hk : 1 ≤ k) {q B : ℝ} (hq : 0 < q) (hB : 0 < B)
    {n : ℕ} (hqn : q ≤ n) (f : Fin k → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hC : (∑ i : Fin k, f i ^ q) ^ (1 / q) ≤ B) :
    ∑ i : Fin k, f i ^ n ≤ B ^ n := by
  haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  rcases Finset.exists_max_image Finset.univ f Finset.univ_nonempty with ⟨j, hjmem, hjmax⟩
  let M : ℝ := f j
  have hM0 : 0 ≤ M := hf j
  have hsum_nonneg : 0 ≤ ∑ i : Fin k, f i ^ q := by
    exact Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hf i) _)
  have hMq_sum : M ^ q ≤ ∑ i : Fin k, f i ^ q := by
    calc
      M ^ q = f j ^ q := rfl
      _ ≤ ∑ i : Fin k, f i ^ q := by
        exact Finset.single_le_sum (fun i _ => Real.rpow_nonneg (hf i) _) hjmem
  have hM : M ≤ B := by
    calc
      M = (M ^ q) ^ (1 / q) := by
        symm
        simpa [one_div] using Real.rpow_rpow_inv hM0 hq.ne'
      _ ≤ (∑ i : Fin k, f i ^ q) ^ (1 / q) := by
        exact Real.rpow_le_rpow (Real.rpow_nonneg hM0 _) hMq_sum (by positivity)
      _ ≤ B := hC
  have hCq : ((∑ i : Fin k, f i ^ q) ^ (1 / q)) ^ q = ∑ i : Fin k, f i ^ q := by
    simpa [one_div] using Real.rpow_inv_rpow hsum_nonneg hq.ne'
  have hterm : ∀ i : Fin k, f i ^ n ≤ M ^ ((n : ℝ) - q) * f i ^ q := by
    intro i
    by_cases hi : f i = 0
    · have hnpos : 0 < n := by
        by_contra hnot
        have hn0 : n = 0 := by omega
        rw [hn0] at hqn
        norm_num at hqn
        linarith
      simp [hi, hnpos.ne', hq.ne']
    · have hi0 : 0 < f i := lt_of_le_of_ne (hf i) (Ne.symm hi)
      have hsplit : f i ^ (n : ℝ) = f i ^ ((n : ℝ) - q) * f i ^ q := by
        rw [← Real.rpow_add hi0]
        congr 1
        ring
      have hpow : f i ^ ((n : ℝ) - q) ≤ M ^ ((n : ℝ) - q) := by
        exact Real.rpow_le_rpow (hf i) (hjmax i (Finset.mem_univ i)) (by linarith)
      calc
        f i ^ n = f i ^ (n : ℝ) := by rw [Real.rpow_natCast]
        _ = f i ^ ((n : ℝ) - q) * f i ^ q := hsplit
        _ ≤ M ^ ((n : ℝ) - q) * f i ^ q := by
          exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (hf i) _)
  have hC_nonneg : 0 ≤ (∑ i : Fin k, f i ^ q) ^ (1 / q) := Real.rpow_nonneg hsum_nonneg _
  calc
    ∑ i : Fin k, f i ^ n ≤ ∑ i : Fin k, M ^ ((n : ℝ) - q) * f i ^ q := by
      exact Finset.sum_le_sum (fun i _ => hterm i)
    _ = M ^ ((n : ℝ) - q) * ∑ i : Fin k, f i ^ q := by
      rw [Finset.mul_sum]
    _ = M ^ ((n : ℝ) - q) * (((∑ i : Fin k, f i ^ q) ^ (1 / q)) ^ q) := by
      rw [hCq]
    _ ≤ B ^ ((n : ℝ) - q) * B ^ q := by
      have h1 : M ^ ((n : ℝ) - q) ≤ B ^ ((n : ℝ) - q) := by
        exact Real.rpow_le_rpow hM0 hM (by linarith)
      have h2 : ((∑ i : Fin k, f i ^ q) ^ (1 / q)) ^ q ≤ B ^ q := by
        exact Real.rpow_le_rpow hC_nonneg hC hq.le
      exact mul_le_mul h1 h2 (Real.rpow_nonneg hC_nonneg _)
        (Real.rpow_nonneg hB.le _)
    _ = B ^ (n : ℝ) := by
      rw [← Real.rpow_add_of_nonneg hB.le (by linarith : 0 ≤ (n : ℝ) - q) hq.le]
      congr 1
      ring
    _ = B ^ n := by rw [Real.rpow_natCast]

/- accepted add_to_file helper 6 -/
noncomputable section

lemma diagonal_sum_norms_le_top
    {𝕂 E : Type*} [RCLike 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
    {k : ℕ} (φ : Fin k → E →L[𝕂] 𝕂)
    {B : ℝ} (hB : 0 < B) (p : ENNReal) (hpt : p = ⊤)
    (hφ : ∀ α : Fin k → 𝕂,
      ‖∑ j : Fin k, α j • φ j‖ ≤ B * ‖α‖)
    (x : E) (hx : ‖x‖ ≤ 1) :
    ∑ i : Fin k, ‖φ i x‖ ≤ B := by
  let y : Fin k → 𝕂 := fun i => φ i x
  let phase : 𝕂 → 𝕂 := fun z => if z = 0 then 0 else (‖z‖ : 𝕂) / z
  let β : Fin k → 𝕂 := fun i => phase (y i)
  have hphase_norm : ∀ z : 𝕂, ‖phase z‖ ≤ 1 := by
    intro z
    by_cases hz : z = 0
    · simp [phase, hz]
    · simp only [phase, if_neg hz]
      rw [norm_div, RCLike.norm_ofReal]
      rw [abs_of_nonneg (norm_nonneg z)]
      rw [div_self (norm_ne_zero_iff.mpr hz)]
  have hphase_apply : ∀ z : 𝕂, phase z * z = (‖z‖ : 𝕂) := by
    intro z
    by_cases hz : z = 0
    · simp [phase, hz]
    · simp only [phase, if_neg hz]
      field_simp [hz]
  have hβnorm : ‖β‖ ≤ 1 := by
    rw [Pi.norm_def]
    norm_cast
    rw [Finset.sup_le_iff]
    intro i hi
    exact_mod_cast hphase_norm (y i)
  let F : E →L[𝕂] 𝕂 := ∑ i : Fin k, β i • φ i
  have hF : ‖F‖ ≤ B := by
    calc
      ‖F‖ ≤ B * ‖β‖ := hφ β
      _ ≤ B * 1 := mul_le_mul_of_nonneg_left hβnorm hB.le
      _ = B := by ring
  have hFx : ‖F x‖ ≤ B := by
    calc
      ‖F x‖ ≤ ‖F‖ * ‖x‖ := ContinuousLinearMap.le_opNorm F x
      _ ≤ ‖F‖ * 1 := mul_le_mul_of_nonneg_left hx (norm_nonneg F)
      _ = ‖F‖ := by ring
      _ ≤ B := hF
  have hvalue : F x = ((∑ i : Fin k, ‖y i‖ : ℝ) : 𝕂) := by
    calc
      F x = ∑ i : Fin k, β i * y i := by
        simp [F, y, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
      _ = ∑ i : Fin k, ((‖y i‖ : ℝ) : 𝕂) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [β, hphase_apply]
      _ = ((∑ i : Fin k, ‖y i‖ : ℝ) : 𝕂) := by norm_num [map_sum]
  have hsum_nonneg : 0 ≤ ∑ i : Fin k, ‖y i‖ := by
    exact Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hnormcast : ‖(((∑ i : Fin k, ‖y i‖) : ℝ) : 𝕂)‖ = ∑ i : Fin k, ‖y i‖ := by
    rw [RCLike.norm_ofReal, abs_of_nonneg hsum_nonneg]
  calc
    ∑ i : Fin k, ‖φ i x‖ = ∑ i : Fin k, ‖y i‖ := by simp [y]
    _ = ‖(((∑ i : Fin k, ‖y i‖) : ℝ) : 𝕂)‖ := hnormcast.symm
    _ = ‖F x‖ := by rw [← hvalue]
    _ ≤ B := hFx

end

/- accepted add_to_file helper 7 -/
noncomputable section

lemma diagonal_polynomial_pointwise_upper
    {𝕂 E : Type*} [RCLike 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
    {k : ℕ} (hk : 1 ≤ k) (φ : Fin k → E →L[𝕂] 𝕂)
    {A B : ℝ} (hB : 0 < B) (p : ENNReal) (hp : 1 < p)
    (hφ : ∀ α : Fin k → 𝕂,
      A * (if p = ⊤ then ‖α‖ else
        Real.rpow (∑ j : Fin k, Real.rpow ‖α j‖ p.toReal) (1 / p.toReal)) ≤
          ‖∑ j : Fin k, α j • φ j‖ ∧
      ‖∑ j : Fin k, α j • φ j‖ ≤
        B * (if p = ⊤ then ‖α‖ else
          Real.rpow (∑ j : Fin k, Real.rpow ‖α j‖ p.toReal) (1 / p.toReal)))
    (n : ℕ) (hn : 1 ≤ n) (hnq : ENNReal.conjExponent p ≤ n)
    (α : Fin k → 𝕂) (x : E) (hx : ‖x‖ ≤ 1) :
    ‖∑ j : Fin k, α j * (φ j x) ^ n‖ ≤ B ^ n * ‖α‖ := by
  have hsumy : ∑ i : Fin k, ‖φ i x‖ ^ n ≤ B ^ n := by
    by_cases hpt : p = ⊤
    · have hupper : ∀ β : Fin k → 𝕂, ‖∑ j : Fin k, β j • φ j‖ ≤ B * ‖β‖ := by
        intro β
        simpa [hpt] using (hφ β).2
      have hs := diagonal_sum_norms_le_top φ hB p hpt hupper x hx
      have hC : (∑ i : Fin k, ‖φ i x‖ ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) ≤ B := by
        simpa using hs
      have hq1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      simpa using sum_nat_pow_le_of_lq_norm_le hk zero_lt_one hB hq1
        (fun i => ‖φ i x‖) (fun i => norm_nonneg _) hC
    · have hupper : ∀ β : Fin k → 𝕂,
          ‖∑ j : Fin k, β j • φ j‖ ≤
            B * Real.rpow (∑ j : Fin k, Real.rpow ‖β j‖ p.toReal) (1 / p.toReal) := by
        intro β
        simpa [hpt] using (hφ β).2
      have hC := diagonal_coordinate_lq_norm_le φ hB p hp hpt hupper x hx
      let q : ENNReal := ENNReal.conjExponent p
      haveI hpq : p.HolderConjugate q := ENNReal.HolderConjugate.conjExponent hp.le
      haveI hqp : q.HolderConjugate p := ENNReal.HolderConjugate.symm
      have hqposEN : 0 < q := ENNReal.HolderConjugate.pos q p
      have hqtop : q ≠ ⊤ := by
        intro hqt
        have hpone : p = 1 :=
          (ENNReal.HolderConjugate.eq_top_iff_eq_one q p).1 hqt
        exact ne_of_gt hp hpone
      have hqpos : 0 < q.toReal := ENNReal.toReal_pos hqposEN.ne' hqtop
      have hqn : q.toReal ≤ (n : ℝ) := by
        have h := (ENNReal.toReal_le_toReal hqtop (by simp : ((n : ENNReal) ≠ ⊤))).2 hnq
        simpa using h
      have hC' : (∑ i : Fin k, ‖φ i x‖ ^ q.toReal) ^ (1 / q.toReal) ≤ B := by
        simpa [q] using hC
      simpa [q] using sum_nat_pow_le_of_lq_norm_le hk hqpos hB hqn
        (fun i => ‖φ i x‖) (fun i => norm_nonneg _) hC'
  calc
    ‖∑ j : Fin k, α j * (φ j x) ^ n‖
        ≤ ∑ j : Fin k, ‖α j * (φ j x) ^ n‖ := norm_sum_le _ _
    _ = ∑ j : Fin k, ‖α j‖ * ‖φ j x‖ ^ n := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [norm_mul, norm_pow]
    _ ≤ ∑ j : Fin k, ‖α‖ * ‖φ j x‖ ^ n := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (norm_le_pi_norm α j)
        (pow_nonneg (norm_nonneg _) _)
    _ = ‖α‖ * ∑ j : Fin k, ‖φ j x‖ ^ n := by rw [Finset.mul_sum]
    _ ≤ ‖α‖ * B ^ n := by
      exact mul_le_mul_of_nonneg_left hsumy (norm_nonneg α)
    _ = B ^ n * ‖α‖ := by rw [mul_comm]

end

/- accepted add_to_file helper 8 -/
noncomputable section

lemma diagonal_polynomial_coordinate_lower
    {𝕂 E : Type*} [RCLike 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
    {k : ℕ} (φ : Fin k → E →L[𝕂] 𝕂)
    {A B : ℝ} (hA : 0 < A) (p : ENNReal) (hp : 1 < p)
    (hφ : ∀ α : Fin k → 𝕂,
      A * (if p = ⊤ then ‖α‖ else
        Real.rpow (∑ j : Fin k, Real.rpow ‖α j‖ p.toReal) (1 / p.toReal)) ≤
          ‖∑ j : Fin k, α j • φ j‖ ∧
      ‖∑ j : Fin k, α j • φ j‖ ≤
        B * (if p = ⊤ then ‖α‖ else
          Real.rpow (∑ j : Fin k, Real.rpow ‖α j‖ p.toReal) (1 / p.toReal)))
    (n : ℕ) (hn : 1 ≤ n) (α : Fin k → 𝕂) (j : Fin k)
    (hBdd : BddAbove (Set.range (fun x : {x : E // ‖x‖ ≤ 1} =>
      ‖∑ l : Fin k, α l * (φ l x) ^ n‖))) :
    A ^ n * ‖α j‖ ≤ sSup (Set.range (fun x : {x : E // ‖x‖ ≤ 1} =>
      ‖∑ l : Fin k, α l * (φ l x) ^ n‖)) := by
  let I := {i : Fin k // i ∈ Finset.univ \ {j}}
  let K : Submodule 𝕂 E := ⨅ i : I, ((φ i.1).toLinearMap).ker
  let f : K →L[𝕂] 𝕂 := (φ j).comp K.subtypeL
  let S : Set ℝ := Set.range (fun x : {x : E // ‖x‖ ≤ 1} =>
    ‖∑ l : Fin k, α l * (φ l x) ^ n‖)
  have hrest : A ≤ ‖f‖ := by
    simpa [f, K, I] using diagonal_functional_restriction_norm_ge φ hA p hp hφ j
  change A ^ n * ‖α j‖ ≤ sSup S
  have hnp : 0 < n := by omega
  by_cases hα : ‖α j‖ = 0
  · have hzero_mem : (0 : ℝ) ∈ S := by
      refine ⟨⟨0, by simp⟩, ?_⟩
      simp [hnp.ne']
    have hzero_le : (0 : ℝ) ≤ sSup S := le_csSup hBdd hzero_mem
    simpa [hα] using hzero_le
  · apply le_of_forall_lt
    intro c hc
    have hαpos : 0 < ‖α j‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hα)
    let C : ℝ := c / ‖α j‖
    have hC : C < A ^ n := by
      exact (div_lt_iff₀ hαpos).2 hc
    have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hnp.ne'
    by_cases hCpos : 0 < C
    · let s : ℝ := C ^ (1 / (n : ℝ))
      have hsA : s < A := by
        calc
          s < (A ^ (n : ℝ)) ^ (1 / (n : ℝ)) := by
            apply Real.rpow_lt_rpow hCpos.le
            · simpa [Real.rpow_natCast] using hC
            · positivity
          _ = A := by
            simpa [one_div] using Real.rpow_rpow_inv hA.le hnreal
      rcases exists_between hsA with ⟨r, hsr, hrA⟩
      have hr : r < ‖f‖ := lt_of_lt_of_le hrA hrest
      rcases ContinuousLinearMap.exists_lt_apply_of_lt_opNorm f hr with ⟨z, hznorm, hzval⟩
      have hzero : ∀ i : Fin k, i ≠ j → φ i z.1 = 0 := by
        intro i hij
        have hmem : z.1 ∈ K := z.2
        have hker : z.1 ∈ ((φ i).toLinearMap).ker := by
          exact ((Submodule.mem_iInf _).1 hmem) ⟨i, by simp [hij]⟩
        simpa [LinearMap.mem_ker] using hker
      have hsum : (∑ l : Fin k, α l * (φ l z.1) ^ n) = α j * (φ j z.1) ^ n := by
        apply Finset.sum_eq_single j
        · intro i hi hij
          simp [hzero i hij, hnp.ne']
        · intro hj
          simp at hj
      let v : ℝ := ‖α j‖ * ‖f z‖ ^ n
      have hv_eq : v = ‖∑ l : Fin k, α l * (φ l z.1) ^ n‖ := by
        rw [hsum]
        simp [v, f, norm_mul, norm_pow]
      have hvmem : v ∈ S := by
        refine ⟨⟨z.1, hznorm.le⟩, ?_⟩
        simpa [S] using hv_eq.symm
      have hs_nonneg : 0 ≤ s := Real.rpow_nonneg hCpos.le _
      have hr_nonneg : 0 ≤ r := le_trans hs_nonneg hsr.le
      have hCs : C = s ^ n := by
        calc
          C = s ^ (n : ℝ) := by
            symm
            simpa [s, one_div] using Real.rpow_inv_rpow hCpos.le hnreal
          _ = s ^ n := by rw [Real.rpow_natCast]
      have hCr : C < r ^ n := by
        rw [hCs]
        exact pow_lt_pow_left₀ hsr hs_nonneg hnp.ne'
      have hrv : r ^ n < ‖f z‖ ^ n := by
        exact pow_lt_pow_left₀ hzval hr_nonneg hnp.ne'
      have hCv : C < ‖f z‖ ^ n := lt_trans hCr hrv
      have hcv : c < v := by
        have h := mul_lt_mul_of_pos_left hCv hαpos
        have hmul : ‖α j‖ * C = c := by
          simpa [C] using mul_div_cancel₀ c hα
        rwa [hmul] at h
      exact lt_of_lt_of_le hcv (le_csSup hBdd hvmem)
    · have hCnonpos : C ≤ 0 := le_of_not_gt hCpos
      have hfpos : 0 < ‖f‖ := lt_of_lt_of_le hA hrest
      rcases ContinuousLinearMap.exists_lt_apply_of_lt_opNorm f hfpos with ⟨z, hznorm, hzval⟩
      have hzero : ∀ i : Fin k, i ≠ j → φ i z.1 = 0 := by
        intro i hij
        have hmem : z.1 ∈ K := z.2
        have hker : z.1 ∈ ((φ i).toLinearMap).ker := by
          exact ((Submodule.mem_iInf _).1 hmem) ⟨i, by simp [hij]⟩
        simpa [LinearMap.mem_ker] using hker
      have hsum : (∑ l : Fin k, α l * (φ l z.1) ^ n) = α j * (φ j z.1) ^ n := by
        apply Finset.sum_eq_single j
        · intro i hi hij
          simp [hzero i hij, hnp.ne']
        · intro hj
          simp at hj
      let v : ℝ := ‖α j‖ * ‖f z‖ ^ n
      have hv_eq : v = ‖∑ l : Fin k, α l * (φ l z.1) ^ n‖ := by
        rw [hsum]
        simp [v, f, norm_mul, norm_pow]
      have hvmem : v ∈ S := by
        refine ⟨⟨z.1, hznorm.le⟩, ?_⟩
        simpa [S] using hv_eq.symm
      have hvpos : 0 < v := by
        exact mul_pos hαpos (pow_pos hzval _)
      have hc0 : c ≤ 0 := by
        have h := (div_le_iff₀ hαpos).1 hCnonpos
        simpa using h
      have hcv : c < v := lt_of_le_of_lt hc0 hvpos
      exact lt_of_lt_of_le hcv (le_csSup hBdd hvmem)

end

/- accepted add_to_file helper 9 -/
lemma exists_norm_eq_pi_norm {G : Type*} [SeminormedAddCommGroup G]
    {k : ℕ} (hk : 1 ≤ k) (α : Fin k → G) : ∃ j : Fin k, ‖α‖ = ‖α j‖ := by
  haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  rcases Finset.exists_max_image Finset.univ (fun j => ‖α j‖) Finset.univ_nonempty with
    ⟨j, hjmem, hjmax⟩
  refine ⟨j, ?_⟩
  have hsup : Finset.univ.sup (fun i => ‖α i‖₊) = ‖α j‖₊ := by
    apply le_antisymm
    · rw [Finset.sup_le_iff]
      intro i hi
      exact_mod_cast hjmax i hi
    · exact Finset.le_sup (s := Finset.univ) (f := fun i => ‖α i‖₊) hjmem
  rw [Pi.norm_def, hsup, coe_nnnorm]

/- verified submission -/
theorem diagonal_homogeneous_polynomial_norm_bounds
    {𝕂 E : Type*} [RCLike 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
    [CompleteSpace E] {k : ℕ} (hk : 1 ≤ k) (φ : Fin k → E →L[𝕂] 𝕂)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (p : ENNReal) (hp : 1 < p)
    (hφ : ∀ α : Fin k → 𝕂,
      A * (if p = ⊤ then ‖α‖ else
        Real.rpow (∑ j : Fin k, Real.rpow ‖α j‖ p.toReal) (1 / p.toReal)) ≤
          ‖∑ j : Fin k, α j • φ j‖ ∧
      ‖∑ j : Fin k, α j • φ j‖ ≤
        B * (if p = ⊤ then ‖α‖ else
          Real.rpow (∑ j : Fin k, Real.rpow ‖α j‖ p.toReal) (1 / p.toReal)))
    (n : ℕ) (hn : 1 ≤ n) (hnq : ENNReal.conjExponent p ≤ n) :
    ∀ α : Fin k → 𝕂,
      A ^ n * ‖α‖ ≤
          sSup (Set.range (fun x : {x : E // ‖x‖ ≤ 1} =>
            ‖∑ j : Fin k, α j * (φ j x) ^ n‖)) ∧
      sSup (Set.range (fun x : {x : E // ‖x‖ ≤ 1} =>
            ‖∑ j : Fin k, α j * (φ j x) ^ n‖)) ≤
        B ^ n * ‖α‖ := by
  intro α
  let S : Set ℝ := Set.range (fun x : {x : E // ‖x‖ ≤ 1} =>
    ‖∑ j : Fin k, α j * (φ j x) ^ n‖)
  have hpoint : ∀ y ∈ S, y ≤ B ^ n * ‖α‖ := by
    rintro y ⟨x, rfl⟩
    exact diagonal_polynomial_pointwise_upper hk φ hB p hp hφ n hn hnq α x x.2
  have hBdd : BddAbove S := ⟨B ^ n * ‖α‖, hpoint⟩
  have hnonempty : S.Nonempty := by
    refine ⟨0, ⟨⟨0, by simp⟩, ?_⟩⟩
    simp [show n ≠ 0 by omega]
  have hupper : sSup S ≤ B ^ n * ‖α‖ := (csSup_le_iff hBdd hnonempty).2 hpoint
  rcases exists_norm_eq_pi_norm hk α with ⟨j, hj⟩
  have hcoord : A ^ n * ‖α j‖ ≤ sSup S := by
    exact diagonal_polynomial_coordinate_lower φ hA p hp hφ n hn α j hBdd
  constructor
  · calc
      A ^ n * ‖α‖ = A ^ n * ‖α j‖ := by rw [hj]
      _ ≤ sSup S := hcoord
  · exact hupper

end Rollout_p1232_diagonal_homogeneous_polynomial_norm_bound

namespace Rollout_p1918_correspondence_of_induced_probability_assi

/- accepted add_to_file helper 1 -/
lemma toReal_measure_sdiff_add_inter
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ]
    (s t : Set α) (ht : MeasurableSet t) :
    (μ (s \ t)).toReal + (μ (s ∩ t)).toReal = (μ s).toReal := by
  have h := MeasureTheory.measure_diff_add_inter (μ := μ) s ht
  have h' := congrArg ENNReal.toReal h
  rwa [ENNReal.toReal_add (MeasureTheory.measure_ne_top μ _)
    (MeasureTheory.measure_ne_top μ _)] at h'

lemma toReal_measure_univ_diff_union
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
    (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (μ (Set.univ \ (s ∪ t))).toReal =
      1 - (μ s).toReal - (μ t).toReal + (μ (s ∩ t)).toReal := by
  let u : Set α := s ∪ t
  have hd : Disjoint (Set.univ \ u) u := disjoint_sdiff_self_left
  have hcompENN : μ (Set.univ \ u) + μ u = 1 := by
    have h := MeasureTheory.measure_union (μ := μ) hd (hs.union ht)
    have huniv : Set.univ \ u ∪ u = Set.univ := by
      simp [Set.diff_union_self]
    rw [huniv] at h
    simpa using h.symm
  have hcomp := congrArg ENNReal.toReal hcompENN
  rw [ENNReal.toReal_add (MeasureTheory.measure_ne_top μ _)
    (MeasureTheory.measure_ne_top μ _)] at hcomp
  have hunionENN : μ (s ∪ t) + μ (s ∩ t) = μ s + μ t :=
    MeasureTheory.measure_union_add_inter (μ := μ) s ht
  have hunion := congrArg ENNReal.toReal hunionENN
  rw [ENNReal.toReal_add (MeasureTheory.measure_ne_top μ _)
    (MeasureTheory.measure_ne_top μ _),
    ENNReal.toReal_add (MeasureTheory.measure_ne_top μ _)
    (MeasureTheory.measure_ne_top μ _)] at hunion
  dsimp [u] at hcomp
  nlinarith

lemma four_valued_tuple_eq
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
    (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ((μ s).toReal - (μ (s ∩ t)).toReal,
      (μ t).toReal - (μ (s ∩ t)).toReal,
      1 - (μ s).toReal - (μ t).toReal + (μ (s ∩ t)).toReal,
      (μ (s ∩ t)).toReal) =
    ((μ (s \ t)).toReal,
      (μ (t \ s)).toReal,
      (μ (Set.univ \ (s ∪ t))).toReal,
      (μ (s ∩ t)).toReal) := by
  have hs_partition : (μ (s \ t)).toReal + (μ (s ∩ t)).toReal = (μ s).toReal :=
    toReal_measure_sdiff_add_inter (μ := μ) s t ht
  have ht_partition : (μ (t \ s)).toReal + (μ (s ∩ t)).toReal = (μ t).toReal := by
    have h := toReal_measure_sdiff_add_inter (μ := μ) t s hs
    rwa [Set.inter_comm] at h
  have hcompl := toReal_measure_univ_diff_union (μ := μ) s t hs ht
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · nlinarith
  · nlinarith
  · rw [hcompl]
  · rfl

/- verified submission -/
theorem correspondence_of_induced_probability_assignments
    {Atom : Type*} [Fintype Atom]
    {State : Type*} [Countable State]
    (vPos vNeg : Atom → Set State)
    (μ : @MeasureTheory.Measure State ⊤)
    [MeasureTheory.IsProbabilityMeasure μ] :
    let formulas : Set Mathlib.Tactic.ITauto.IProp :=
      {φ | ∀ S : Set Mathlib.Tactic.ITauto.IProp,
        (∀ a : Atom,
          Mathlib.Tactic.ITauto.IProp.var (Fintype.equivFin Atom a) ∈ S) →
        (∀ ψ ∈ S, Mathlib.Tactic.ITauto.IProp.not ψ ∈ S) →
        (∀ ψ χ, ψ ∈ S → χ ∈ S → Mathlib.Tactic.ITauto.IProp.and ψ χ ∈ S) →
        φ ∈ S}
    let Formula := ↥formulas
    let atom : Atom → Formula :=
      fun a => ⟨Mathlib.Tactic.ITauto.IProp.var (Fintype.equivFin Atom a),
        fun S hAtom _ _ => hAtom a⟩
    let neg : Formula → Formula :=
      fun φ => ⟨Mathlib.Tactic.ITauto.IProp.not φ.1,
        fun S hAtom hNeg hConj => hNeg φ.1 (φ.2 S hAtom hNeg hConj)⟩
    let conj : Formula → Formula → Formula :=
      fun φ ψ => ⟨Mathlib.Tactic.ITauto.IProp.and φ.1 ψ.1,
        fun S hAtom hNeg hConj =>
          hConj φ.1 ψ.1 (φ.2 S hAtom hNeg hConj) (ψ.2 S hAtom hNeg hConj)⟩
    ∀ (P N : Formula → Set State),
      (∀ a, P (atom a) = vPos a) →
      (∀ a, N (atom a) = vNeg a) →
      (∀ φ, P (neg φ) = N φ) →
      (∀ φ, N (neg φ) = P φ) →
      (∀ φ ψ, P (conj φ ψ) = P φ ∩ P ψ) →
      (∀ φ ψ, N (conj φ ψ) = N φ ∪ N ψ) →
      let p : Formula → ℝ := fun φ => (μ (P φ)).toReal
      let q : Formula → ℝ × (ℝ × (ℝ × ℝ)) :=
        fun φ =>
          ((μ (P φ \ N φ)).toReal,
            (μ (N φ \ P φ)).toReal,
            (μ (Set.univ \ (P φ ∪ N φ))).toReal,
            (μ (P φ ∩ N φ)).toReal)
      let T₄₁ : (Formula → ℝ × (ℝ × (ℝ × ℝ))) → Formula → ℝ :=
        fun r φ => (r φ).1 + (r φ).2.2.2
      let T₁₄ : (Formula → ℝ) → Formula → ℝ × (ℝ × (ℝ × ℝ)) :=
        fun r φ =>
          (r φ - r (conj φ (neg φ)),
            r (neg φ) - r (conj φ (neg φ)),
            1 - r φ - r (neg φ) + r (conj φ (neg φ)),
            r (conj φ (neg φ)))
      T₄₁ q = p ∧ T₁₄ p = q := by
  intro formulas Formula atom neg conj
  intro P N hPatom hNatom hPneg hNneg hPconj hNconj
  intro p q T41 T14
  constructor
  · funext φ
    have hpartition := @toReal_measure_sdiff_add_inter State ⊤ μ _ (P φ) (N φ)
      MeasurableSpace.measurableSet_top
    simp [T41, q, p]
    nlinarith
  · funext φ
    have hmeasP : @MeasurableSet State ⊤ (P φ) := MeasurableSpace.measurableSet_top
    have hmeasN : @MeasurableSet State ⊤ (N φ) := MeasurableSpace.measurableSet_top
    have hneg : P (neg φ) = N φ := hPneg φ
    have hconf : P (conj φ (neg φ)) = P φ ∩ N φ := by
      rw [hPconj, hneg]
    dsimp [T14, p, q]
    rw [hneg, hconf]
    exact @four_valued_tuple_eq State ⊤ μ _ (P φ) (N φ) hmeasP hmeasN

end Rollout_p1918_correspondence_of_induced_probability_assi

namespace Rollout_p1499_countablytight_iff_prod_firstcountable

/- accepted add_to_file helper 1 -/
lemma countablyTight_prod_firstCountable
    {X : Type u} [TopologicalSpace X]
    (hX : ∀ (A : Set X) (x : X), x ∈ closure A →
      ∃ B : Set X, B ⊆ A ∧ B.Countable ∧ x ∈ closure B)
    {Y : Type v} [TopologicalSpace Y] [FirstCountableTopology Y] :
    ∀ (A : Set (X × Y)) (p : X × Y), p ∈ closure A →
      ∃ B : Set (X × Y), B ⊆ A ∧ B.Countable ∧ p ∈ closure B := by
  intro A p hp
  obtain ⟨V, hV⟩ := (Filter.isCountablyGenerated_iff_exists_antitone_basis.mp
    (FirstCountableTopology.nhds_generated_countable p.2))
  let C : ℕ → Set X := fun n => Prod.fst '' (A ∩ (Set.univ ×ˢ V n))
  have hVn : ∀ n, V n ∈ nhds p.2 := by
    intro n
    exact hV.mem_iff.mpr ⟨n, subset_rfl⟩
  have hpC : ∀ n, p.1 ∈ closure (C n) := by
    intro n
    rw [mem_closure_iff_nhds]
    intro U hU
    have hprod : U ×ˢ V n ∈ nhds p := by
      rw [mem_nhds_prod_iff]
      exact ⟨U, hU, V n, hVn n, subset_rfl⟩
    obtain ⟨q, hqprod, hqA⟩ := (mem_closure_iff_nhds.mp hp) (U ×ˢ V n) hprod
    rcases hqprod with ⟨hqU, hqV⟩
    refine ⟨q.1, hqU, ?_⟩
    exact ⟨q, ⟨hqA, ⟨trivial, hqV⟩⟩, rfl⟩
  choose BX hBXsub hBXcount hpBX using fun n => hX (C n) p.1 (hpC n)
  have hchoose : ∀ n, ∀ x : BX n, ∃ q : X × Y, q ∈ A ∧ q.2 ∈ V n ∧ q.1 = x.1 := by
    intro n x
    have hxC : (x : X) ∈ C n := hBXsub n x.2
    rcases hxC with ⟨q, hq, hq1⟩
    rcases hq with ⟨hqA, hqprod⟩
    rcases hqprod with ⟨-, hqV⟩
    exact ⟨q, hqA, hqV, hq1⟩
  choose f hfA hfV hf1 using hchoose
  let D : ℕ → Set (X × Y) := fun n => Set.range (f n)
  let Bset : Set (X × Y) := ⋃ n, D n
  refine ⟨Bset, ?_, ?_, ?_⟩
  · intro q hq
    rw [Set.mem_iUnion] at hq
    rcases hq with ⟨n, hn⟩
    rcases hn with ⟨x, rfl⟩
    exact hfA n x
  · have hDcount : ∀ n, (D n).Countable := by
      intro n
      haveI : Countable (BX n) := (hBXcount n).to_subtype
      exact Set.countable_range (f n)
    exact Set.countable_iUnion hDcount
  · rw [mem_closure_iff_nhds]
    intro W hW
    obtain ⟨U, hU, T, hT, hUT⟩ := mem_nhds_prod_iff.mp hW
    obtain ⟨n, hnVT⟩ := hV.mem_iff.mp hT
    obtain ⟨z, hzU, hzB⟩ := (mem_closure_iff_nhds.mp (hpBX n)) U hU
    refine ⟨f n ⟨z, hzB⟩, hUT ?_, ?_⟩
    · constructor
      · rw [hf1 n ⟨z, hzB⟩]
        exact hzU
      · exact hnVT (hfV n ⟨z, hzB⟩)
    · rw [Set.mem_iUnion]
      exact ⟨n, ⟨⟨z, hzB⟩, rfl⟩⟩

/- verified submission -/
theorem countablyTight_iff_prod_firstCountable {X : Type u} [TopologicalSpace X] :
    (∀ (A : Set X) (x : X), x ∈ closure A →
      ∃ B : Set X, B ⊆ A ∧ B.Countable ∧ x ∈ closure B) ↔
      ∀ (Y : Type v) [TopologicalSpace Y] [FirstCountableTopology Y],
        ∀ (A : Set (X × Y)) (p : X × Y), p ∈ closure A →
          ∃ B : Set (X × Y), B ⊆ A ∧ B.Countable ∧ p ∈ closure B := by
  constructor
  · intro hX Y _ _
    exact countablyTight_prod_firstCountable hX
  · intro hprod A x hx
    let Z : Type v := ULift.{v} PUnit
    let h : X × Z ≃ₜ X := Homeomorph.prodUnique X Z
    have hp : h.symm x ∈ closure (⇑h ⁻¹' A) := by
      have hmem : h.symm x ∈ ⇑h ⁻¹' closure A := by
        simpa using hx
      rwa [h.preimage_closure A] at hmem
    obtain ⟨B0, hB0A, hB0count, hB0cl⟩ := hprod Z (⇑h ⁻¹' A) (h.symm x) hp
    refine ⟨⇑h '' B0, ?_, hB0count.image ⇑h, ?_⟩
    · intro z hz
      rcases hz with ⟨q, hqB0, rfl⟩
      exact hB0A hqB0
    · have hxcl : h (h.symm x) ∈ closure (⇑h '' B0) := by
        rw [← h.image_closure B0]
        exact ⟨h.symm x, hB0cl, rfl⟩
      simpa using hxcl

end Rollout_p1499_countablytight_iff_prod_firstcountable

namespace Rollout_p0043_independentdominationnumber_eq_dominationn

/- accepted add_to_file helper 1 -/
def IsDominatingFinset {V : Type*} (G : SimpleGraph V) (D : Finset V) : Prop :=
  ∀ v : V, v ∉ D → ∃ w : V, w ∈ D ∧ G.Adj v w

def dominationCardinalities {V : Type*} [Fintype V] (G : SimpleGraph V) : Set ℕ :=
  {n : ℕ | ∃ D : Finset V, D.card = n ∧ IsDominatingFinset G D}

noncomputable def internalAdjPairs {V : Type*} (G : SimpleGraph V) (D : Finset V) : Finset (V × V) := by
  classical
  exact (D ×ˢ D).filter fun p : V × V => G.Adj p.1 p.2

noncomputable def internalAdjPairCount {V : Type*} (G : SimpleGraph V) (D : Finset V) : ℕ :=
  (internalAdjPairs G D).card

lemma exists_private_neighbor_of_min_dominating
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    {n : ℕ} (hmin : ∀ E : Finset V, IsDominatingFinset G E → n ≤ E.card)
    {D : Finset V} (hDcard : D.card = n) (hDdom : IsDominatingFinset G D)
    {u v : V} (huD : u ∈ D) (hvD : v ∈ D) (huv : G.Adj u v) :
    ∃ p : V, p ∉ D ∧ G.Adj u p ∧ ∀ z : V, z ∈ D.erase u → ¬ G.Adj p z := by
  classical
  have hcard_erase_lt : (D.erase u).card < n := by
    rw [Finset.card_erase_of_mem huD, hDcard]
    have hpos : 0 < n := by
      rw [← hDcard]
      exact Finset.card_pos.mpr ⟨u, huD⟩
    omega
  have hnotdom : ¬ IsDominatingFinset G (D.erase u) := by
    intro hdom
    have hle := hmin (D.erase u) hdom
    omega
  unfold IsDominatingFinset at hnotdom
  push Not at hnotdom
  obtain ⟨x, hx_erase, hno⟩ := hnotdom
  by_cases hxD : x ∈ D
  · have hx_eq_u : x = u := by
      by_contra hxne
      exact hx_erase (Finset.mem_erase.mpr ⟨hxne, hxD⟩)
    subst x
    have hv_erase : v ∈ D.erase u := by
      exact Finset.mem_erase.mpr ⟨huv.ne.symm, hvD⟩
    exact False.elim (hno v hv_erase huv)
  · obtain ⟨z, hzD, hxz⟩ := hDdom x hxD
    have hz_eq_u : z = u := by
      by_contra hzne
      have hz_erase : z ∈ D.erase u := Finset.mem_erase.mpr ⟨hzne, hzD⟩
      exact hno z hz_erase hxz
    subst z
    exact ⟨x, hxD, (G.adj_comm x u).mp hxz, hno⟩

lemma internalAdjPairs_insert_private
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) {D : Finset V} {a p : V}
    (hpriv : ∀ z : V, z ∈ D.erase a → ¬ G.Adj p z) :
    internalAdjPairs G (insert p (D.erase a)) = internalAdjPairs G (D.erase a) := by
  classical
  ext q
  constructor
  · intro hq
    rw [internalAdjPairs, Finset.mem_filter] at hq ⊢
    obtain ⟨hqmem, hqadj⟩ := hq
    rw [Finset.mem_product] at hqmem ⊢
    have hq1' : q.1 = p ∨ q.1 ∈ D.erase a := by
      simpa [Finset.mem_insert] using hqmem.1
    have hq2' : q.2 = p ∨ q.2 ∈ D.erase a := by
      simpa [Finset.mem_insert] using hqmem.2
    rcases hq1' with hq1eq | hq1mem
    · rcases hq2' with hq2eq | hq2mem
      · have hdiag : q.1 = q.2 := hq1eq.trans hq2eq.symm
        rw [hdiag] at hqadj
        exact False.elim (G.irrefl hqadj)
      · rw [hq1eq] at hqadj
        exact False.elim (hpriv q.2 hq2mem hqadj)
    · rcases hq2' with hq2eq | hq2mem
      · have hqp : G.Adj p q.1 := by
          rw [hq2eq] at hqadj
          exact (G.adj_comm q.1 p).mp hqadj
        exact False.elim (hpriv q.1 hq1mem hqp)
      · exact ⟨⟨hq1mem, hq2mem⟩, hqadj⟩
  · intro hq
    rw [internalAdjPairs, Finset.mem_filter] at hq ⊢
    obtain ⟨hqmem, hqadj⟩ := hq
    rw [Finset.mem_product] at hqmem ⊢
    exact ⟨⟨Finset.mem_insert_of_mem hqmem.1, Finset.mem_insert_of_mem hqmem.2⟩, hqadj⟩

lemma internalAdjPairCount_erase_lt
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    {D : Finset V} {a b : V} (ha : a ∈ D) (hb : b ∈ D.erase a)
    (hab : G.Adj a b) :
    internalAdjPairCount G (D.erase a) < internalAdjPairCount G D := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro q hq
    rw [internalAdjPairs, Finset.mem_filter, Finset.mem_product] at hq ⊢
    obtain ⟨⟨hq1, hq2⟩, hqadj⟩ := hq
    exact ⟨⟨(Finset.erase_subset a D) hq1, (Finset.erase_subset a D) hq2⟩, hqadj⟩
  · intro heq
    have hmem_full : (a,b) ∈ internalAdjPairs G D := by
      rw [internalAdjPairs, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨ha, (Finset.erase_subset a D) hb⟩, hab⟩
    have hmem_erase : (a,b) ∈ internalAdjPairs G (D.erase a) := by
      rw [heq]
      exact hmem_full
    rw [internalAdjPairs, Finset.mem_filter, Finset.mem_product] at hmem_erase
    exact (Finset.notMem_erase a D) hmem_erase.1.1

lemma min_dominating_independent
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hhigh : G.IsIndepSet {v : V | 2 < (G.neighborSet v).ncard}) :
    ∃ D : Finset V, D.card = sInf (dominationCardinalities G) ∧
      G.IsIndepSet (↑D : Set V) ∧ IsDominatingFinset G D := by
  classical
  let γ := sInf (dominationCardinalities G)
  have hnonempty : (dominationCardinalities G).Nonempty := by
    refine ⟨Fintype.card V, Finset.univ, ?_, ?_⟩
    · simp
    · intro v hv
      simp at hv
  have hγ_mem : γ ∈ dominationCardinalities G := Nat.sInf_mem hnonempty
  obtain ⟨D0, hD0card, hD0dom⟩ := hγ_mem
  let candidates : Finset (Finset V) :=
    Finset.univ.filter fun D : Finset V => D.card = γ ∧ IsDominatingFinset G D
  have hcandidates_nonempty : candidates.Nonempty := by
    refine ⟨D0, ?_⟩
    simp [candidates, hD0card, hD0dom]
  let cost : Finset V → ℕ := fun D => internalAdjPairCount G D
  obtain ⟨D, hDcandidate, hDmincost⟩ := Finset.exists_min_image candidates cost hcandidates_nonempty
  have hDprops : D.card = γ ∧ IsDominatingFinset G D := by
    simpa [candidates] using hDcandidate
  obtain ⟨hDcard, hDdom⟩ := hDprops
  have hγle : ∀ E : Finset V, IsDominatingFinset G E → γ ≤ E.card := by
    intro E hE
    exact Nat.sInf_le ⟨E, rfl, hE⟩
  refine ⟨D, hDcard, ?_, hDdom⟩
  by_contra hnotind
  rw [SimpleGraph.isIndepSet_iff] at hnotind
  unfold Set.Pairwise at hnotind
  push Not at hnotind
  obtain ⟨u, huD, v, hvD, huvne, huv⟩ := hnotind
  have hlow : ∃ a b : V, a ∈ D ∧ b ∈ D ∧ a ≠ b ∧ G.Adj a b ∧
      (G.neighborSet a).ncard ≤ 2 := by
    by_cases hu_high : 2 < (G.neighborSet u).ncard
    · have hv_not_high : ¬ 2 < (G.neighborSet v).ncard := by
        intro hv_high
        exact (hhigh hu_high hv_high huvne) huv
      exact ⟨v, u, hvD, huD, huvne.symm, (G.adj_comm u v).mp huv, not_lt.mp hv_not_high⟩
    · exact ⟨u, v, huD, hvD, huvne, huv, not_lt.mp hu_high⟩
  obtain ⟨a, b, haD, hbD, habne, hab, ha_low⟩ := hlow
  obtain ⟨p, hpD, hap, hprivate⟩ :=
    exists_private_neighbor_of_min_dominating G hγle hDcard hDdom haD hbD hab
  have hb_ne_p : b ≠ p := by
    intro h
    exact hpD (h ▸ hbD)
  have hneighbors_subset : ({b, p} : Set V) ⊆ G.neighborSet a := by
    intro z hz
    simp at hz
    rcases hz with hzb | hzp
    · rw [hzb]
      exact (G.mem_neighborSet a b).mpr hab
    · rw [hzp]
      exact (G.mem_neighborSet a p).mpr hap
  have hfiniteN : (G.neighborSet a).Finite := by
    exact Set.finite_univ.subset (by intro x hx; trivial)
  have hpair_card : ({b, p} : Set V).ncard = 2 := Set.ncard_pair hb_ne_p
  have hN_ge : 2 ≤ (G.neighborSet a).ncard := by
    rw [← hpair_card]
    exact Set.ncard_le_ncard hneighbors_subset hfiniteN
  have hN_card : (G.neighborSet a).ncard = 2 := le_antisymm ha_low hN_ge
  have hN_eq_pair : ({b, p} : Set V) = G.neighborSet a := by
    apply Set.eq_of_subset_of_ncard_le hneighbors_subset
    rw [hpair_card, hN_card]
  let D' : Finset V := insert p (D.erase a)
  have hp_not_erase : p ∉ D.erase a := by
    intro hp
    exact hpD ((Finset.erase_subset a D) hp)
  have hD'_card_D : D'.card = D.card := by
    dsimp [D']
    rw [Finset.card_insert_of_notMem hp_not_erase,
      Finset.card_erase_of_mem haD]
    have hDpos : 0 < D.card := Finset.card_pos.mpr ⟨a, haD⟩
    omega
  have hD'_card : D'.card = γ := by
    rw [hD'_card_D, hDcard]
  have hD'_dom : IsDominatingFinset G D' := by
    intro x hxD'
    by_cases hxD : x ∈ D
    · by_cases hxa : x = a
      · subst x
        exact ⟨p, by simp [D'], hap⟩
      · have hx_erase : x ∈ D.erase a := Finset.mem_erase.mpr ⟨hxa, hxD⟩
        exact False.elim (hxD' (Finset.mem_insert_of_mem hx_erase))
    · obtain ⟨z, hzD, hxz⟩ := hDdom x hxD
      by_cases hza : z = a
      · subst z
        have hxN : x ∈ G.neighborSet a :=
          (G.mem_neighborSet a x).mpr ((G.adj_comm x a).mp hxz)
        rw [← hN_eq_pair] at hxN
        simp at hxN
        rcases hxN with hxb | hxp
        · exact False.elim (hxD (hxb ▸ hbD))
        · exact False.elim (hxD' (hxp ▸ by simp [D']))
      · have hz_erase : z ∈ D.erase a := Finset.mem_erase.mpr ⟨hza, hzD⟩
        exact ⟨z, Finset.mem_insert_of_mem hz_erase, hxz⟩
  have hD'_candidate : D' ∈ candidates := by
    simp [candidates, hD'_card, hD'_dom]
  have hcost_eq : cost D' = cost (D.erase a) := by
    dsimp [cost, internalAdjPairCount]
    exact congrArg Finset.card (internalAdjPairs_insert_private G hprivate)
  have hb_erase : b ∈ D.erase a := Finset.mem_erase.mpr ⟨habne.symm, hbD⟩
  have hcost_lt : cost D' < cost D := by
    rw [hcost_eq]
    exact internalAdjPairCount_erase_lt G haD hb_erase hab
  have hcost_le := hDmincost D' hD'_candidate
  omega

/- verified submission -/
theorem independentDominationNumber_eq_dominationNumber
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hhigh : G.IsIndepSet {v : V | 2 < (G.neighborSet v).ncard}) :
    sInf {n : ℕ | ∃ D : Finset V,
      D.card = n ∧ G.IsIndepSet (↑D : Set V) ∧
        ∀ v : V, v ∉ D → ∃ w : V, w ∈ D ∧ G.Adj v w} =
    sInf {n : ℕ | ∃ D : Finset V,
      D.card = n ∧ ∀ v : V, v ∉ D → ∃ w : V, w ∈ D ∧ G.Adj v w} := by
  classical
  let independentCardinalities : Set ℕ :=
    {n : ℕ | ∃ D : Finset V,
      D.card = n ∧ G.IsIndepSet (↑D : Set V) ∧
        ∀ v : V, v ∉ D → ∃ w : V, w ∈ D ∧ G.Adj v w}
  let dominatingCardinalities : Set ℕ :=
    {n : ℕ | ∃ D : Finset V,
      D.card = n ∧ ∀ v : V, v ∉ D → ∃ w : V, w ∈ D ∧ G.Adj v w}
  change sInf independentCardinalities = sInf dominatingCardinalities
  obtain ⟨D, hDcard, hDind, hDdom⟩ := min_dominating_independent G hhigh
  have hdom_sets_eq : dominationCardinalities G = dominatingCardinalities := rfl
  have hDcard' : D.card = sInf dominatingCardinalities := by
    simpa [hdom_sets_eq] using hDcard
  have hI_nonempty : independentCardinalities.Nonempty := by
    exact ⟨sInf dominatingCardinalities, D, hDcard', hDind, hDdom⟩
  have hsubset : independentCardinalities ⊆ dominatingCardinalities := by
    intro n hn
    obtain ⟨E, hEcard, hEind, hEdom⟩ := hn
    exact ⟨E, hEcard, hEdom⟩
  have h_le_dom : sInf dominatingCardinalities ≤ sInf independentCardinalities := by
    exact Nat.sInf_le (hsubset (Nat.sInf_mem hI_nonempty))
  have h_le_ind : sInf independentCardinalities ≤ sInf dominatingCardinalities := by
    exact Nat.sInf_le ⟨D, hDcard', hDind, hDdom⟩
  exact le_antisymm h_le_ind h_le_dom

end Rollout_p0043_independentdominationnumber_eq_dominationn

namespace Rollout_p2272_proposition_4_2

/- accepted add_to_file helper 1 -/
lemma gsp_inv_aux {l : Type*} [DecidableEq l] [Fintype l] {R : Type*} [CommRing R]
    (g : Matrix.GeneralLinearGroup (l ⊕ l) R) {μ : Rˣ}
    (h : (g : Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
        (g : Matrix (l ⊕ l) (l ⊕ l) R) = (μ : R) • Matrix.J l R) :
    ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
        Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
        ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
          Matrix (l ⊕ l) (l ⊕ l) R) =
      ((μ⁻¹ : Rˣ) : R) • Matrix.J l R := by
  have hmul :
      (μ : R) •
        ((((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
            Matrix (l ⊕ l) (l ⊕ l) R).transpose) * Matrix.J l R *
          ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
            Matrix (l ⊕ l) (l ⊕ l) R)) = Matrix.J l R := by
    calc
      (μ : R) •
          ((((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R).transpose) * Matrix.J l R *
            ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R))
          =
          (((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R).transpose) *
            ((μ : R) • Matrix.J l R) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R) := by
            simp [Matrix.mul_smul, mul_assoc]
      _ =
          (((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R).transpose) *
            ((g : Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
              (g : Matrix (l ⊕ l) (l ⊕ l) R)) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R) := by rw [h]
      _ =
          ((((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R).transpose) *
            ((g : Matrix (l ⊕ l) (l ⊕ l) R).transpose)) *
            Matrix.J l R *
            ((g : Matrix (l ⊕ l) (l ⊕ l) R) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R)) := by
            simp [mul_assoc]
      _ = Matrix.J l R := by
            rw [← Matrix.transpose_mul]
            simp
  calc
    (((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
          Matrix (l ⊕ l) (l ⊕ l) R).transpose) * Matrix.J l R *
        ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
          Matrix (l ⊕ l) (l ⊕ l) R)
        = ((μ⁻¹ : Rˣ) : R) •
          ((μ : R) •
            ((((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
                Matrix (l ⊕ l) (l ⊕ l) R).transpose) * Matrix.J l R *
              ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
                Matrix (l ⊕ l) (l ⊕ l) R))) := by
          simp [smul_smul]
    _ = ((μ⁻¹ : Rˣ) : R) • Matrix.J l R := by rw [hmul]

/- accepted add_to_file helper 2 -/
lemma gsp_conj_aux {l : Type*} [DecidableEq l] [Fintype l] {R : Type*} [CommRing R]
    (g x : Matrix.GeneralLinearGroup (l ⊕ l) R)
    {μg μx : Rˣ}
    (hg : (g : Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
        (g : Matrix (l ⊕ l) (l ⊕ l) R) = (μg : R) • Matrix.J l R)
    (hx : (x : Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
        (x : Matrix (l ⊕ l) (l ⊕ l) R) = (μx : R) • Matrix.J l R) :
    ((g⁻¹ * x * g : Matrix.GeneralLinearGroup (l ⊕ l) R) :
        Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
        ((g⁻¹ * x * g : Matrix.GeneralLinearGroup (l ⊕ l) R) :
          Matrix (l ⊕ l) (l ⊕ l) R) =
      (μx : R) • Matrix.J l R := by
  have hgi := gsp_inv_aux g hg
  have hc : ((μg⁻¹ : Rˣ) : R) * ((μx : R) * (μg : R)) = μx := by
    simp [mul_assoc, mul_left_comm]
  calc
    ((g⁻¹ * x * g : Matrix.GeneralLinearGroup (l ⊕ l) R) :
        Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
        ((g⁻¹ * x * g : Matrix.GeneralLinearGroup (l ⊕ l) R) :
          Matrix (l ⊕ l) (l ⊕ l) R)
        =
        (g : Matrix (l ⊕ l) (l ⊕ l) R).transpose *
        ((x : Matrix (l ⊕ l) (l ⊕ l) R).transpose *
          ((((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R).transpose) * Matrix.J l R *
            ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R))) *
        (x : Matrix (l ⊕ l) (l ⊕ l) R) *
        (g : Matrix (l ⊕ l) (l ⊕ l) R) := by
          simp [Matrix.transpose_mul, mul_assoc]
    _ =
        (g : Matrix (l ⊕ l) (l ⊕ l) R).transpose *
        ((x : Matrix (l ⊕ l) (l ⊕ l) R).transpose *
          (((μg⁻¹ : Rˣ) : R) • Matrix.J l R)) *
        (x : Matrix (l ⊕ l) (l ⊕ l) R) *
        (g : Matrix (l ⊕ l) (l ⊕ l) R) := by rw [hgi]
    _ =
        ((μg⁻¹ : Rˣ) : R) •
          ((g : Matrix (l ⊕ l) (l ⊕ l) R).transpose *
          ((x : Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
            (x : Matrix (l ⊕ l) (l ⊕ l) R)) *
          (g : Matrix (l ⊕ l) (l ⊕ l) R)) := by
          simp [Matrix.smul_mul, Matrix.mul_smul, mul_assoc]
    _ =
        ((μg⁻¹ : Rˣ) : R) •
          ((g : Matrix (l ⊕ l) (l ⊕ l) R).transpose *
          ((μx : R) • Matrix.J l R) *
          (g : Matrix (l ⊕ l) (l ⊕ l) R)) := by rw [hx]
    _ =
        (((μg⁻¹ : Rˣ) : R) * (μx : R)) •
          ((g : Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
            (g : Matrix (l ⊕ l) (l ⊕ l) R)) := by
          simp [Matrix.smul_mul, Matrix.mul_smul, mul_assoc, smul_smul]
    _ =
        (((μg⁻¹ : Rˣ) : R) * (μx : R)) •
          ((μg : R) • Matrix.J l R) := by rw [hg]
    _ = (μx : R) • Matrix.J l R := by
          simp only [smul_eq_mul, smul_smul]
          rw [show ((μg⁻¹ : Rˣ) : R) * (μx : R) * (μg : R) = μx by
            simpa [mul_assoc] using hc]

/- accepted add_to_file helper 3 -/
def Hmat {R : Type*} [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
  Matrix.fromBlocks
    (Matrix.diagonal ![A 0 0, B 0 0])
    (Matrix.diagonal ![A 0 1, B 0 1])
    (Matrix.diagonal ![A 1 0, B 1 0])
    (Matrix.diagonal ![A 1 1, B 1 1])

lemma Hmat_det {R : Type*} [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R) :
    (Hmat A B).det = A.det * B.det := by
  have hsub :
      (Hmat A B).submatrix
        (Equiv.swap (Sum.inl (1 : Fin 2)) (Sum.inr (0 : Fin 2)))
        (Equiv.swap (Sum.inl (1 : Fin 2)) (Sum.inr (0 : Fin 2))) =
      Matrix.fromBlocks A 0 0 B := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Hmat, Equiv.swap_apply_of_ne_of_ne]
  have hdet := Matrix.det_submatrix_equiv_self
    (Equiv.swap (Sum.inl (1 : Fin 2)) (Sum.inr (0 : Fin 2))) (Hmat A B)
  rw [hsub] at hdet
  rw [← hdet]
  exact Matrix.det_fromBlocks_zero₁₂ A 0 B

lemma Hmat_gsp {R : Type*} [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R)
    (hd : A.det = B.det) :
    (Hmat A B).transpose * Matrix.J (Fin 2) R * Hmat A B =
      A.det • Matrix.J (Fin 2) R := by
  rw [Matrix.det_fin_two A, Matrix.det_fin_two B] at hd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, Hmat, Matrix.J, Matrix.det_fin_two] <;>
    ring_nf <;> first | linear_combination hd | linear_combination -hd

/- accepted add_to_file helper 4 -/
lemma padic_algebraMap_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (algebraMap ℤ_[p] ℚ_[p]) :=
  IsFractionRing.injective ℤ_[p] ℚ_[p]

/- accepted add_to_file helper 5 -/
lemma conjugate_line_decomp {R : Type*} [CommRing R]
    (γ k : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) {N : R}
    (hγcol :
      Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
        ((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) =
      ((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) +
        ((Pi.single (Sum.inl (1 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)))
    (hk : ∀ i : Fin 2 ⊕ Fin 2, i ≠ Sum.inl (0 : Fin 2) →
      N ∣ (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) i (Sum.inl (0 : Fin 2))) :
    ∃ a : R, ∃ w : (Fin 2 ⊕ Fin 2) → R,
      Matrix.mulVec
        (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
        (((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) +
          ((Pi.single (Sum.inl (1 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R))) =
      a • (((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) +
          ((Pi.single (Sum.inl (1 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R))) +
        N • w := by
  let e : (Fin 2 ⊕ Fin 2) → R :=
    Pi.single (Sum.inl (0 : Fin 2)) (1 : R)
  let x : (Fin 2 ⊕ Fin 2) → R :=
    e + Pi.single (Sum.inl (1 : Fin 2)) (1 : R)
  have hγcol' : Matrix.mulVec
      (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e = x := by
    dsimp [e, x]
    exact hγcol
  let a : R := (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
    (Sum.inl (0 : Fin 2)) (Sum.inl (0 : Fin 2))
  let c : (Fin 2 ⊕ Fin 2) → R := fun i =>
    if hi : i = Sum.inl (0 : Fin 2) then 0 else Classical.choose (hk i hi)
  have hc : ∀ i : Fin 2 ⊕ Fin 2, i ≠ Sum.inl (0 : Fin 2) →
      (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) i (Sum.inl (0 : Fin 2)) =
        N * c i := by
    intro i hi
    simpa [c, hi] using Classical.choose_spec (hk i hi)
  have hkc : Matrix.mulVec (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e =
      a • e + N • c := by
    ext i
    by_cases hi : i = Sum.inl (0 : Fin 2)
    · subst i
      simp [e, a, c, Matrix.mulVec]
    · simp [e, Matrix.mulVec, hi, hc i hi]
  have hginvx :
      Matrix.mulVec
        ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x = e := by
    rw [← hγcol']
    calc
      Matrix.mulVec
          ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
          (Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e)
          =
          Matrix.mulVec
            (((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) *
              (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) e := by
            exact Matrix.mulVec_mulVec e _ _
      _ = e := by simp
  refine ⟨a, Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) c, ?_⟩
  calc
    Matrix.mulVec
        (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x
        =
        Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
          (Matrix.mulVec (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e) := by
          have h1 :
              Matrix.mulVec
                (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                  Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x =
              Matrix.mulVec
                (((γ * k : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                  Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                (Matrix.mulVec
                  ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
                    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x) := by
            calc
              Matrix.mulVec
                  (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x
                  =
                  Matrix.mulVec
                    ((((γ * k : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) *
                    ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
                      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) x := by
                    simp [mul_assoc]
              _ =
                  Matrix.mulVec
                    (((γ * k : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                    (Matrix.mulVec
                      ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
                        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x) := by
                    exact (Matrix.mulVec_mulVec x _ _).symm
          rw [hginvx] at h1
          rw [h1]
          calc
            Matrix.mulVec
                (((γ * k : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                  Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e
                =
                Matrix.mulVec
                  (((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) *
                    (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) e := by simp
            _ =
                Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                  (Matrix.mulVec (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e) := by
                  exact (Matrix.mulVec_mulVec e _ _).symm
    _ =
        Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
          (a • e + N • c) := by rw [hkc]
    _ = a • x + N • Matrix.mulVec
        (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) c := by
          rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hγcol']

/- accepted add_to_file helper 6 -/
def extractA {R : Type*} [CommRing R]
    (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) :
    Matrix (Fin 2) (Fin 2) R :=
  !![G (Sum.inl 0) (Sum.inl 0), G (Sum.inl 0) (Sum.inr 0);
     G (Sum.inr 0) (Sum.inl 0), G (Sum.inr 0) (Sum.inr 0)]

def extractB {R : Type*} [CommRing R]
    (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) :
    Matrix (Fin 2) (Fin 2) R :=
  !![G (Sum.inl 1) (Sum.inl 1), G (Sum.inl 1) (Sum.inr 1);
     G (Sum.inr 1) (Sum.inl 1), G (Sum.inr 1) (Sum.inr 1)]

/- accepted add_to_file helper 7 -/
lemma extractA_map_of_eq {R K : Type*} [CommRing R] [CommRing K] [Algebra R K]
    {h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    {A B : Matrix (Fin 2) (Fin 2) K}
    {G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (hh : h = Hmat A B) (hg : h = G.map (algebraMap R K)) :
    A = (extractA G).map (algebraMap R K) := by
  ext i j
  have heq : Hmat A B = G.map (algebraMap R K) := hh.symm.trans hg
  fin_cases i <;> fin_cases j
  · have eq := congr_fun (congr_fun heq (Sum.inl (0:Fin 2))) (Sum.inl (0:Fin 2))
    simpa [Hmat, extractA] using eq
  · have eq := congr_fun (congr_fun heq (Sum.inl (0:Fin 2))) (Sum.inr (0:Fin 2))
    simpa [Hmat, extractA] using eq
  · have eq := congr_fun (congr_fun heq (Sum.inr (0:Fin 2))) (Sum.inl (0:Fin 2))
    simpa [Hmat, extractA] using eq
  · have eq := congr_fun (congr_fun heq (Sum.inr (0:Fin 2))) (Sum.inr (0:Fin 2))
    simpa [Hmat, extractA] using eq

lemma extractB_map_of_eq {R K : Type*} [CommRing R] [CommRing K] [Algebra R K]
    {h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    {A B : Matrix (Fin 2) (Fin 2) K}
    {G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (hh : h = Hmat A B) (hg : h = G.map (algebraMap R K)) :
    B = (extractB G).map (algebraMap R K) := by
  ext i j
  have heq : Hmat A B = G.map (algebraMap R K) := hh.symm.trans hg
  fin_cases i <;> fin_cases j
  · have eq := congr_fun (congr_fun heq (Sum.inl (1:Fin 2))) (Sum.inl (1:Fin 2))
    simpa [Hmat, extractB] using eq
  · have eq := congr_fun (congr_fun heq (Sum.inl (1:Fin 2))) (Sum.inr (1:Fin 2))
    simpa [Hmat, extractB] using eq
  · have eq := congr_fun (congr_fun heq (Sum.inr (1:Fin 2))) (Sum.inl (1:Fin 2))
    simpa [Hmat, extractB] using eq
  · have eq := congr_fun (congr_fun heq (Sum.inr (1:Fin 2))) (Sum.inr (1:Fin 2))
    simpa [Hmat, extractB] using eq

/- accepted add_to_file helper 8 -/
lemma extract_det_data (p : ℕ) [Fact p.Prime]
    {h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ_[p]}
    {A B : Matrix (Fin 2) (Fin 2) ℚ_[p]}
    {G : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]}
    (hh : h = Hmat A B)
    (hg : h = ((G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
      (algebraMap ℤ_[p] ℚ_[p])))
    (hdetAB : A.det = B.det) :
    IsUnit (extractA (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])).det ∧
      IsUnit (extractB (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])).det ∧
      (extractA (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])).det =
        (extractB (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])).det := by
  let AZ := extractA (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
  let BZ := extractB (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
  have hAmap : A = AZ.map (algebraMap ℤ_[p] ℚ_[p]) := by
    dsimp [AZ]
    exact extractA_map_of_eq hh hg
  have hBmap : B = BZ.map (algebraMap ℤ_[p] ℚ_[p]) := by
    dsimp [BZ]
    exact extractB_map_of_eq hh hg
  have hdetZ : AZ.det = BZ.det := by
    apply padic_algebraMap_injective p
    calc
      algebraMap ℤ_[p] ℚ_[p] AZ.det = (AZ.map (algebraMap ℤ_[p] ℚ_[p])).det := by
        exact RingHom.map_det (algebraMap ℤ_[p] ℚ_[p]) AZ
      _ = A.det := by rw [← hAmap]
      _ = B.det := hdetAB
      _ = (BZ.map (algebraMap ℤ_[p] ℚ_[p])).det := by rw [← hBmap]
      _ = algebraMap ℤ_[p] ℚ_[p] BZ.det := by
        exact (RingHom.map_det (algebraMap ℤ_[p] ℚ_[p]) BZ).symm
  have hGunit : IsUnit ((G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).det) := by
    simpa using (Matrix.GeneralLinearGroup.det G).isUnit
  have hGdet : (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).det =
      AZ.det * BZ.det := by
    apply padic_algebraMap_injective p
    calc
      algebraMap ℤ_[p] ℚ_[p]
          (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).det
          =
          (((G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
            (algebraMap ℤ_[p] ℚ_[p])).det) := by
            exact RingHom.map_det (algebraMap ℤ_[p] ℚ_[p])
              (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
      _ = (Hmat A B).det := by
            have heqmat :
                ((G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
                  (algebraMap ℤ_[p] ℚ_[p])) = Hmat A B := hg.symm.trans hh
            rw [heqmat]
      _ = A.det * B.det := Hmat_det A B
      _ = (AZ.map (algebraMap ℤ_[p] ℚ_[p])).det *
          (BZ.map (algebraMap ℤ_[p] ℚ_[p])).det := by rw [← hAmap, ← hBmap]
      _ = algebraMap ℤ_[p] ℚ_[p] (AZ.det * BZ.det) := by
        rw [RingHom.map_mul,
          RingHom.map_det (algebraMap ℤ_[p] ℚ_[p]) AZ,
          RingHom.map_det (algebraMap ℤ_[p] ℚ_[p]) BZ,
          RingHom.mapMatrix_apply, RingHom.mapMatrix_apply]
  have hprod : IsUnit (AZ.det * BZ.det) := by
    simpa [hGdet] using hGunit
  exact ⟨isUnit_of_mul_isUnit_left hprod, isUnit_of_mul_isUnit_right hprod, hdetZ⟩

/- accepted add_to_file helper 9 -/
lemma extract_congr_data (p m : ℕ) [Fact p.Prime]
    {h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ_[p]}
    {A B : Matrix (Fin 2) (Fin 2) ℚ_[p]}
    (γ k : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p])
    (hγe₁e₁ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inl 0) (Sum.inl 0) = 1)
    (hγe₁e₂ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inl 1) (Sum.inl 0) = 1)
    (hγe₁f₁ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inr 0) (Sum.inl 0) = 0)
    (hγe₁f₂ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inr 1) (Sum.inl 0) = 0)
    (hk : ∀ i : Fin 2 ⊕ Fin 2, i ≠ Sum.inl 0 →
      (p : ℤ_[p]) ^ m ∣
        (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) i (Sum.inl 0))
    (hh : h = Hmat A B)
    (hg : h = (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
      (algebraMap ℤ_[p] ℚ_[p]))) :
    (p : ℤ_[p]) ^ m ∣
      (extractA (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]))) 1 0 ∧
    (p : ℤ_[p]) ^ m ∣
      (extractB (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]))) 1 0 ∧
    (p : ℤ_[p]) ^ m ∣
      ((extractA (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]))) 0 0 -
        (extractB (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]))) 0 0) := by
  let e : (Fin 2 ⊕ Fin 2) → ℤ_[p] := Pi.single (Sum.inl (0 : Fin 2)) 1
  let x : (Fin 2 ⊕ Fin 2) → ℤ_[p] :=
    e + Pi.single (Sum.inl (1 : Fin 2)) 1
  have hγcol : Matrix.mulVec
      (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) e = x := by
    ext i
    fin_cases i <;> simp [e, x, Matrix.mulVec, hγe₁e₁, hγe₁e₂, hγe₁f₁, hγe₁f₂]
  obtain ⟨a, w, hdecomp⟩ := conjugate_line_decomp γ k hγcol hk
  have zero_entry : ∀ r c : Fin 2 ⊕ Fin 2, Hmat A B r c = 0 →
      (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) r c = 0 := by
    intro r c hr
    apply padic_algebraMap_injective p
    calc
      algebraMap ℤ_[p] ℚ_[p]
          ((((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) r c) = h r c := by
        exact (congr_fun (congr_fun hg r) c).symm
      _ = Hmat A B r c := congr_fun (congr_fun hh r) c
      _ = 0 := hr
  have z₁ : ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) *
      (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) *
      ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]))⁻¹)
      (Sum.inl (0:Fin 2)) (Sum.inl (1:Fin 2)) = 0 := by
    simpa using zero_entry _ _ (by simp [Hmat])
  have z₂ : ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) *
      (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) *
      ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]))⁻¹)
      (Sum.inl (1:Fin 2)) (Sum.inl (0:Fin 2)) = 0 := by
    simpa using zero_entry _ _ (by simp [Hmat])
  have z₃ : ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) *
      (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) *
      ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]))⁻¹)
      (Sum.inr (0:Fin 2)) (Sum.inl (1:Fin 2)) = 0 := by
    simpa using zero_entry _ _ (by simp [Hmat])
  have z₄ : ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) *
      (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) *
      ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]))⁻¹)
      (Sum.inr (1:Fin 2)) (Sum.inl (0:Fin 2)) = 0 := by
    simpa using zero_entry _ _ (by simp [Hmat])
  have hA00 : extractA (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) 0 0 =
      a + (p : ℤ_[p]) ^ m * w (Sum.inl (0:Fin 2)) := by
    have e0 := congr_fun hdecomp (Sum.inl (0:Fin 2))
    calc
      extractA (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) 0 0
        =
        Matrix.mulVec (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) x (Sum.inl (0:Fin 2)) := by
        symm
        simp [extractA, e, x, Matrix.mulVec, z₁]
      _ = a • x (Sum.inl (0:Fin 2)) + (p : ℤ_[p]) ^ m • w (Sum.inl (0:Fin 2)) := e0
      _ = a + (p : ℤ_[p]) ^ m * w (Sum.inl (0:Fin 2)) := by simp [e, x]
  have hB00 : extractB (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) 0 0 =
      a + (p : ℤ_[p]) ^ m * w (Sum.inl (1:Fin 2)) := by
    have e1 := congr_fun hdecomp (Sum.inl (1:Fin 2))
    calc
      extractB (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) 0 0
        =
        Matrix.mulVec (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) x (Sum.inl (1:Fin 2)) := by
        symm
        simp [extractB, e, x, Matrix.mulVec, z₂]
      _ = a • x (Sum.inl (1:Fin 2)) + (p : ℤ_[p]) ^ m • w (Sum.inl (1:Fin 2)) := e1
      _ = a + (p : ℤ_[p]) ^ m * w (Sum.inl (1:Fin 2)) := by simp [e, x]
  have hA10 : extractA (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) 1 0 =
      (p : ℤ_[p]) ^ m * w (Sum.inr (0:Fin 2)) := by
    have ef0 := congr_fun hdecomp (Sum.inr (0:Fin 2))
    calc
      extractA (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) 1 0
        =
        Matrix.mulVec (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) x (Sum.inr (0:Fin 2)) := by
        symm
        simp [extractA, e, x, Matrix.mulVec, z₃]
      _ = a • x (Sum.inr (0:Fin 2)) + (p : ℤ_[p]) ^ m • w (Sum.inr (0:Fin 2)) := ef0
      _ = (p : ℤ_[p]) ^ m * w (Sum.inr (0:Fin 2)) := by simp [e, x]
  have hB10 : extractB (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) 1 0 =
      (p : ℤ_[p]) ^ m * w (Sum.inr (1:Fin 2)) := by
    have ef1 := congr_fun hdecomp (Sum.inr (1:Fin 2))
    calc
      extractB (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) 1 0
        =
        Matrix.mulVec (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) x (Sum.inr (1:Fin 2)) := by
        symm
        simp [extractB, e, x, Matrix.mulVec, z₄]
      _ = a • x (Sum.inr (1:Fin 2)) + (p : ℤ_[p]) ^ m • w (Sum.inr (1:Fin 2)) := ef1
      _ = (p : ℤ_[p]) ^ m * w (Sum.inr (1:Fin 2)) := by simp [e, x]
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨w (Sum.inr (0:Fin 2)), hA10⟩
  · exact ⟨w (Sum.inr (1:Fin 2)), hB10⟩
  · refine ⟨w (Sum.inl (0:Fin 2)) - w (Sum.inl (1:Fin 2)), ?_⟩
    rw [hA00, hB00]
    ring

/- accepted add_to_file helper 10 -/
lemma Hmat_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A B : Matrix (Fin 2) (Fin 2) R) :
    Hmat (A.map f) (B.map f) = (Hmat A B).map f := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Hmat]

/- accepted add_to_file helper 11 -/
lemma Hmat_line_decomp {R : Type*} [CommRing R]
    (A B : Matrix (Fin 2) (Fin 2) R) {N : R}
    (hA10 : N ∣ A 1 0) (hB10 : N ∣ B 1 0)
    (hdiff : N ∣ (A 0 0 - B 0 0)) :
    ∃ w : (Fin 2 ⊕ Fin 2) → R,
      Matrix.mulVec (Hmat A B)
        (((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) +
          ((Pi.single (Sum.inl (1 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R))) =
      A 0 0 • (((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) +
          ((Pi.single (Sum.inl (1 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R))) +
        N • w := by
  obtain ⟨ca, hca⟩ := hA10
  obtain ⟨cb, hcb⟩ := hB10
  obtain ⟨cd, hcd⟩ := hdiff
  let w : (Fin 2 ⊕ Fin 2) → R := fun i =>
    if i = Sum.inl (0:Fin 2) then 0 else
    if i = Sum.inl (1:Fin 2) then -cd else
    if i = Sum.inr (0:Fin 2) then ca else cb
  refine ⟨w, ?_⟩
  ext i
  fin_cases i <;> simp [Hmat, Matrix.mulVec, w, hca, hcb, hcd] <;> ring <;>
    try linear_combination -hcd

/- accepted add_to_file helper 12 -/
lemma line_condition_of_decomp {R : Type*} [CommRing R]
    (γ H : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) {N a : R}
    (w : (Fin 2 ⊕ Fin 2) → R)
    (hγcol :
      Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
        ((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) =
      ((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) +
        ((Pi.single (Sum.inl (1 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)))
    (hHx :
      Matrix.mulVec (H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
        (((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) +
          ((Pi.single (Sum.inl (1 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R))) =
      a • (((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) +
          ((Pi.single (Sum.inl (1 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R))) +
        N • w) :
    ∀ i : Fin 2 ⊕ Fin 2, i ≠ Sum.inl (0 : Fin 2) →
      N ∣ (((γ⁻¹ * H * γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) i (Sum.inl (0 : Fin 2)) := by
  let e : (Fin 2 ⊕ Fin 2) → R := Pi.single (Sum.inl (0 : Fin 2)) 1
  let x : (Fin 2 ⊕ Fin 2) → R :=
    e + Pi.single (Sum.inl (1 : Fin 2)) 1
  have hγcol' : Matrix.mulVec
      (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e = x := by
    dsimp [e, x]
    exact hγcol
  have hHx' : Matrix.mulVec
      (H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x = a • x + N • w := by
    dsimp [e, x]
    exact hHx
  have hginvx :
      Matrix.mulVec
        ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x = e := by
    rw [← hγcol']
    calc
      Matrix.mulVec
          ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
          (Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e)
          =
          Matrix.mulVec
            (((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) *
              (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) e := by
            exact Matrix.mulVec_mulVec e _ _
      _ = e := by simp
  have hcol :
      Matrix.mulVec
        (((γ⁻¹ * H * γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) e =
      Matrix.mulVec
        ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
        (a • x + N • w) := by
    calc
      Matrix.mulVec
          (((γ⁻¹ * H * γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) e
          =
          Matrix.mulVec
            ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
            (Matrix.mulVec (H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
              (Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e)) := by
          calc
            Matrix.mulVec
                (((γ⁻¹ * H * γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
                  Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) e
                =
                Matrix.mulVec
                  ((((γ⁻¹ * H : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) *
                  (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) e := by
                  simp [mul_assoc]
            _ =
                Matrix.mulVec
                  (((γ⁻¹ * H : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                  (Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e) := by
                  exact (Matrix.mulVec_mulVec e _ _).symm
            _ =
                Matrix.mulVec
                  ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
                    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                  (Matrix.mulVec (H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                    (Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e)) := by
                  calc
                    Matrix.mulVec
                        (((γ⁻¹ * H : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                        (Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e)
                        =
                        Matrix.mulVec
                          ((((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) *
                          (H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R))
                          (Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e) := by
                          simp
                    _ =
                        Matrix.mulVec
                          ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
                            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                          (Matrix.mulVec (H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                            (Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e)) := by
                          exact (Matrix.mulVec_mulVec _ _ _).symm
      _ =
          Matrix.mulVec
            ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
            (Matrix.mulVec (H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x) := by
            rw [hγcol']
      _ =
          Matrix.mulVec
            ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
            (a • x + N • w) := by rw [hHx']
  intro i hi
  refine ⟨Matrix.mulVec
    ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) w i, ?_⟩
  calc
    (((γ⁻¹ * H * γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) i (Sum.inl (0 : Fin 2))
        =
        Matrix.mulVec
          (((γ⁻¹ * H * γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) e i := by
          simp [e, Matrix.mulVec]
    _ =
        Matrix.mulVec
          ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
          (a • x + N • w) i := by rw [hcol]
    _ = N * Matrix.mulVec
          ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) w i := by
          rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hginvx]
          simp [e, hi]

/- accepted add_to_file helper 13 -/
lemma Hmat_GL_map_eq {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A B : Matrix.GeneralLinearGroup (Fin 2) R) :
    (Hmat (A : Matrix (Fin 2) (Fin 2) R)
      (B : Matrix (Fin 2) (Fin 2) R)).map f =
    Hmat ((Matrix.GeneralLinearGroup.map f A :
      Matrix.GeneralLinearGroup (Fin 2) S) : Matrix (Fin 2) (Fin 2) S)
      ((Matrix.GeneralLinearGroup.map f B :
        Matrix.GeneralLinearGroup (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Hmat, Matrix.GeneralLinearGroup.map_apply]

/- verified submission -/
theorem proposition_4_2
    (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m)
    (γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p])
    (hγGSp : ∃ μ : ℤ_[p]ˣ,
      (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).transpose *
          Matrix.J (Fin 2) ℤ_[p] *
          (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) =
        (μ : ℤ_[p]) • Matrix.J (Fin 2) ℤ_[p])
    (hγe₁e₁ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inl 0) (Sum.inl 0) = 1)
    (hγe₁e₂ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inl 1) (Sum.inl 0) = 1)
    (hγe₁f₁ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inr 0) (Sum.inl 0) = 0)
    (hγe₁f₂ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inr 1) (Sum.inl 0) = 0) :
    {h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ_[p] |
      (∃ A B : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p],
        Matrix.det (A : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
            Matrix.det (B : Matrix (Fin 2) (Fin 2) ℚ_[p]) ∧
        h = Matrix.fromBlocks
          (Matrix.diagonal ![A 0 0, B 0 0])
          (Matrix.diagonal ![A 0 1, B 0 1])
          (Matrix.diagonal ![A 1 0, B 1 0])
          (Matrix.diagonal ![A 1 1, B 1 1])) ∧
      ∃ k : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p],
        (∃ μ : ℤ_[p]ˣ,
          (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).transpose *
              Matrix.J (Fin 2) ℤ_[p] *
              (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) =
            (μ : ℤ_[p]) • Matrix.J (Fin 2) ℤ_[p]) ∧
        (∀ i : Fin 2 ⊕ Fin 2, i ≠ Sum.inl 0 →
          (p : ℤ_[p]) ^ m ∣
            (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) i (Sum.inl 0)) ∧
        h = ((↑(γ * k * γ⁻¹) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
            (algebraMap ℤ_[p] ℚ_[p]))} =
    {h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ_[p] |
      ∃ A B : Matrix.GeneralLinearGroup (Fin 2) ℤ_[p],
        Matrix.det (A : Matrix (Fin 2) (Fin 2) ℤ_[p]) =
            Matrix.det (B : Matrix (Fin 2) (Fin 2) ℤ_[p]) ∧
        (p : ℤ_[p]) ^ m ∣ (A : Matrix (Fin 2) (Fin 2) ℤ_[p]) 1 0 ∧
        (p : ℤ_[p]) ^ m ∣ (B : Matrix (Fin 2) (Fin 2) ℤ_[p]) 1 0 ∧
        (p : ℤ_[p]) ^ m ∣
          ((A : Matrix (Fin 2) (Fin 2) ℤ_[p]) 0 0 -
            (B : Matrix (Fin 2) (Fin 2) ℤ_[p]) 0 0) ∧
        h = (Matrix.fromBlocks
          (Matrix.diagonal ![A 0 0, B 0 0])
          (Matrix.diagonal ![A 0 1, B 0 1])
          (Matrix.diagonal ![A 1 0, B 1 0])
          (Matrix.diagonal ![A 1 1, B 1 1])).map
            (algebraMap ℤ_[p] ℚ_[p])} := by
  ext h
  constructor
  · rintro ⟨⟨A, B, hdet, hH⟩, k, _hkGSp, hk, hconj⟩
    change h = Hmat (A : Matrix (Fin 2) (Fin 2) ℚ_[p])
      (B : Matrix (Fin 2) (Fin 2) ℚ_[p]) at hH
    let G : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p] := γ * k * γ⁻¹
    have hconj' : h = ((G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
      (algebraMap ℤ_[p] ℚ_[p])) := by
      simpa [G] using hconj
    obtain ⟨huA, huB, hdetZ⟩ := extract_det_data p hH hconj' hdet
    let AZ : Matrix (Fin 2) (Fin 2) ℤ_[p] :=
      extractA (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
    let BZ : Matrix (Fin 2) (Fin 2) ℤ_[p] :=
      extractB (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
    let AGL : Matrix.GeneralLinearGroup (Fin 2) ℤ_[p] :=
      Matrix.GeneralLinearGroup.mk'' AZ huA
    let BGL : Matrix.GeneralLinearGroup (Fin 2) ℤ_[p] :=
      Matrix.GeneralLinearGroup.mk'' BZ huB
    obtain ⟨hcA, hcB, hdiff⟩ :=
      extract_congr_data p m γ k hγe₁e₁ hγe₁e₂ hγe₁f₁ hγe₁f₂ hk hH hconj'
    refine ⟨AGL, BGL, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [AGL, BGL, AZ, BZ, Matrix.GeneralLinearGroup.val_mk''] using hdetZ
    · simpa [AGL, AZ, G, Matrix.GeneralLinearGroup.val_mk''] using hcA
    · simpa [BGL, BZ, G, Matrix.GeneralLinearGroup.val_mk''] using hcB
    · simpa [AGL, BGL, AZ, BZ, G, Matrix.GeneralLinearGroup.val_mk''] using hdiff
    · have hAmap : (A : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
          AZ.map (algebraMap ℤ_[p] ℚ_[p]) := by
        dsimp [AZ]
        exact extractA_map_of_eq hH hconj'
      have hBmap : (B : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
          BZ.map (algebraMap ℤ_[p] ℚ_[p]) := by
        dsimp [BZ]
        exact extractB_map_of_eq hH hconj'
      calc
        h = Hmat (A : Matrix (Fin 2) (Fin 2) ℚ_[p])
            (B : Matrix (Fin 2) (Fin 2) ℚ_[p]) := hH
        _ = Hmat (AZ.map (algebraMap ℤ_[p] ℚ_[p]))
            (BZ.map (algebraMap ℤ_[p] ℚ_[p])) := by rw [hAmap, hBmap]
        _ = (Hmat AZ BZ).map (algebraMap ℤ_[p] ℚ_[p]) := Hmat_map _ _ _
        _ = (Hmat (AGL : Matrix (Fin 2) (Fin 2) ℤ_[p])
            (BGL : Matrix (Fin 2) (Fin 2) ℤ_[p])).map
            (algebraMap ℤ_[p] ℚ_[p]) := by
          simp [AGL, BGL, Matrix.GeneralLinearGroup.val_mk'']
  · rintro ⟨A, B, hdet, hcA, hcB, hdiff, hH⟩
    change h = (Hmat (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
      (B : Matrix (Fin 2) (Fin 2) ℤ_[p])).map (algebraMap ℤ_[p] ℚ_[p]) at hH
    let Aq : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p] :=
      Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) A
    let Bq : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p] :=
      Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) B
    have hdetq :
        Matrix.det (Aq : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
          Matrix.det (Bq : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
      rw [Matrix.GeneralLinearGroup.val_map_apply,
        Matrix.GeneralLinearGroup.val_map_apply]
      rw [← RingHom.mapMatrix_apply (algebraMap ℤ_[p] ℚ_[p])
        (A : Matrix (Fin 2) (Fin 2) ℤ_[p]),
        ← RingHom.mapMatrix_apply (algebraMap ℤ_[p] ℚ_[p])
        (B : Matrix (Fin 2) (Fin 2) ℤ_[p])]
      rw [← RingHom.map_det (algebraMap ℤ_[p] ℚ_[p])
        (A : Matrix (Fin 2) (Fin 2) ℤ_[p]),
        ← RingHom.map_det (algebraMap ℤ_[p] ℚ_[p])
        (B : Matrix (Fin 2) (Fin 2) ℤ_[p])]
      rw [hdet]
    have hHq : h = Hmat (Aq : Matrix (Fin 2) (Fin 2) ℚ_[p])
        (Bq : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
      calc
        h = (Hmat (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
            (B : Matrix (Fin 2) (Fin 2) ℤ_[p])).map
            (algebraMap ℤ_[p] ℚ_[p]) := hH
        _ = Hmat (Aq : Matrix (Fin 2) (Fin 2) ℚ_[p])
            (Bq : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
          dsimp [Aq, Bq]
          exact Hmat_GL_map_eq (algebraMap ℤ_[p] ℚ_[p]) A B
    have hUA : IsUnit (A : Matrix (Fin 2) (Fin 2) ℤ_[p]).det := by
      simpa using (Matrix.GeneralLinearGroup.det A).isUnit
    have hUB : IsUnit (B : Matrix (Fin 2) (Fin 2) ℤ_[p]).det := by
      simpa using (Matrix.GeneralLinearGroup.det B).isUnit
    have hunitH : IsUnit (Hmat (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
        (B : Matrix (Fin 2) (Fin 2) ℤ_[p])).det := by
      rw [Hmat_det]
      exact hUA.mul hUB
    let HGL : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p] :=
      Matrix.GeneralLinearGroup.mk''
        (Hmat (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
          (B : Matrix (Fin 2) (Fin 2) ℤ_[p])) hunitH
    let k : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p] := γ⁻¹ * HGL * γ
    have hHGSp :
        (HGL : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).transpose *
            Matrix.J (Fin 2) ℤ_[p] *
          (HGL : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) =
        ((Matrix.GeneralLinearGroup.det A : ℤ_[p]ˣ) : ℤ_[p]) •
          Matrix.J (Fin 2) ℤ_[p] := by
      have base := Hmat_gsp (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
        (B : Matrix (Fin 2) (Fin 2) ℤ_[p]) hdet
      simpa [HGL, Matrix.GeneralLinearGroup.val_mk''] using base
    obtain ⟨μγ, hγeq⟩ := hγGSp
    have hkGSp :
        (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).transpose *
            Matrix.J (Fin 2) ℤ_[p] *
          (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) =
        ((Matrix.GeneralLinearGroup.det A : ℤ_[p]ˣ) : ℤ_[p]) •
          Matrix.J (Fin 2) ℤ_[p] := by
      have conj := gsp_conj_aux γ HGL hγeq hHGSp
      simpa [k] using conj
    let e : (Fin 2 ⊕ Fin 2) → ℤ_[p] := Pi.single (Sum.inl (0 : Fin 2)) 1
    let x : (Fin 2 ⊕ Fin 2) → ℤ_[p] :=
      e + Pi.single (Sum.inl (1 : Fin 2)) 1
    have hγcol : Matrix.mulVec
        (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) e = x := by
      ext i
      fin_cases i <;> simp [e, x, Matrix.mulVec, hγe₁e₁, hγe₁e₂, hγe₁f₁, hγe₁f₂]
    obtain ⟨w, hHx⟩ := Hmat_line_decomp
      (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
      (B : Matrix (Fin 2) (Fin 2) ℤ_[p]) hcA hcB hdiff
    have hHxH :
        Matrix.mulVec (HGL : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
          (((Pi.single (Sum.inl (0 : Fin 2)) (1 : ℤ_[p]) : (Fin 2 ⊕ Fin 2) → ℤ_[p])) +
            ((Pi.single (Sum.inl (1 : Fin 2)) (1 : ℤ_[p]) : (Fin 2 ⊕ Fin 2) → ℤ_[p]))) =
        (A : Matrix (Fin 2) (Fin 2) ℤ_[p]) 0 0 •
          (((Pi.single (Sum.inl (0 : Fin 2)) (1 : ℤ_[p]) : (Fin 2 ⊕ Fin 2) → ℤ_[p])) +
            ((Pi.single (Sum.inl (1 : Fin 2)) (1 : ℤ_[p]) : (Fin 2 ⊕ Fin 2) → ℤ_[p]))) +
          (p : ℤ_[p]) ^ m • w := by
      simpa [HGL, Matrix.GeneralLinearGroup.val_mk''] using hHx
    have hkl : ∀ i : Fin 2 ⊕ Fin 2, i ≠ Sum.inl 0 →
        (p : ℤ_[p]) ^ m ∣
          (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) i (Sum.inl 0) := by
      have line := line_condition_of_decomp γ HGL w hγcol hHxH
      simpa [k] using line
    have hconj : h = ((↑(γ * k * γ⁻¹) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
        (algebraMap ℤ_[p] ℚ_[p])) := by
      have hgroup : γ * k * γ⁻¹ = HGL := by
        dsimp [k]
        group
      calc
        h = (Hmat (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
            (B : Matrix (Fin 2) (Fin 2) ℤ_[p])).map
            (algebraMap ℤ_[p] ℚ_[p]) := hH
        _ = ((HGL : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
            (algebraMap ℤ_[p] ℚ_[p])) := by
          simp [HGL, Matrix.GeneralLinearGroup.val_mk'']
        _ = ((↑(γ * k * γ⁻¹) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
            (algebraMap ℤ_[p] ℚ_[p])) := by rw [hgroup]
    exact ⟨⟨Aq, Bq, hdetq, hHq⟩, k,
      ⟨Matrix.GeneralLinearGroup.det A, hkGSp⟩, hkl, hconj⟩

end Rollout_p2272_proposition_4_2

namespace Rollout_p2823_two_local_inner_derivation_matrix_is_inner

/- accepted add_to_file helper 1 -/
namespace TwoLocalInnerDerivation

variable {R : Type*} [CommRing R]

noncomputable def E {n : ℕ} (i j : Fin n) : Matrix (Fin n) (Fin n) R :=
  Matrix.single i j (1 : R)

lemma E_apply {n : ℕ} (i j a b : Fin n) :
    E (R := R) i j a b = (if i = a ∧ j = b then (1 : R) else 0) := by
  rfl

lemma mul_E_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (i j a b : Fin n) :
    (M * E (R := R) i j) a b = (if j = b then M a i else 0) := by
  rw [Matrix.mul_apply]
  by_cases hb : j = b
  · subst b
    rw [Finset.sum_eq_single i]
    · simp [E, Matrix.single_apply]
    · intro x _ hx
      by_cases hix : i = x
      · exact False.elim (hx hix.symm)
      · simp [E, Matrix.single_apply, hix]
    · simp
  · simp [E, Matrix.single_apply, hb]

lemma E_mul_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (i j a b : Fin n) :
    (E (R := R) i j * M) a b = (if i = a then M j b else 0) := by
  rw [Matrix.mul_apply]
  by_cases ha : i = a
  · subst a
    rw [Finset.sum_eq_single j]
    · simp [E, Matrix.single_apply]
    · intro x _ hx
      by_cases hjx : j = x
      · exact False.elim (hx hjx.symm)
      · simp [E, Matrix.single_apply, hjx]
    · simp
  · simp [E, Matrix.single_apply, ha]

end TwoLocalInnerDerivation

/- accepted add_to_file helper 2 -/
namespace TwoLocalInnerDerivation

variable {R : Type*} [CommRing R]

def Up (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  fun i j => if j.1 = i.1 + 1 then (1 : R) else 0

def Down (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  fun i j => if i.1 = j.1 + 1 then (1 : R) else 0

end TwoLocalInnerDerivation

/- accepted add_to_file helper 3 -/
namespace TwoLocalInnerDerivation

variable {R : Type*} [CommRing R]

lemma mul_Up_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (M * Up (R := R) n) i j =
      if h : 0 < j.1 then M i ⟨j.1 - 1, by omega⟩ else 0 := by
  rw [Matrix.mul_apply]
  by_cases hj : 0 < j.1
  · rw [dif_pos hj]
    rw [Finset.sum_eq_single ⟨j.1 - 1, by omega⟩]
    · have hUp : Up (R := R) n ⟨j.1 - 1, by omega⟩ j = 1 := by
        simp [Up]
        omega
      rw [hUp, mul_one]
    · intro x _ hx
      by_cases hxj : j.1 = x.1 + 1
      · apply False.elim
        apply hx
        have hxval : x.1 = (⟨j.1 - 1, by omega⟩ : Fin n).1 := by
          simp
          omega
        exact Fin.eq_of_val_eq hxval
      · have hzero : Up (R := R) n x j = 0 := by simp [Up, hxj]
        rw [hzero, mul_zero]
    · simp
  · rw [dif_neg hj]
    have hzero : j.1 = 0 := by omega
    apply Finset.sum_eq_zero
    intro x _
    have hUp : Up (R := R) n x j = 0 := by simp [Up, hzero]
    rw [hUp, mul_zero]

lemma Up_mul_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (Up (R := R) n * M) i j =
      if h : i.1 + 1 < n then M ⟨i.1 + 1, h⟩ j else 0 := by
  rw [Matrix.mul_apply]
  by_cases hi : i.1 + 1 < n
  · rw [dif_pos hi]
    rw [Finset.sum_eq_single ⟨i.1 + 1, hi⟩]
    · have hUp : Up (R := R) n i ⟨i.1 + 1, hi⟩ = 1 := by
        simp [Up]
      rw [hUp, one_mul]
    · intro x _ hx
      by_cases hxi : x.1 = i.1 + 1
      · apply False.elim
        apply hx
        have hxval : x.1 = (⟨i.1 + 1, hi⟩ : Fin n).1 := by
          simp [hxi]
        exact Fin.eq_of_val_eq hxval
      · have hzero : Up (R := R) n i x = 0 := by simp [Up, hxi]
        rw [hzero, zero_mul]
    · simp
  · rw [dif_neg hi]
    apply Finset.sum_eq_zero
    intro x _
    have hx : x.1 ≠ i.1 + 1 := by
      intro h
      omega
    have hUp : Up (R := R) n i x = 0 := by simp [Up, hx]
    rw [hUp, zero_mul]

lemma Down_transpose {n : ℕ} :
    Down (R := R) n = (Up (R := R) n).transpose := by
  ext i j
  simp [Down, Up]

end TwoLocalInnerDerivation

/- accepted add_to_file helper 4 -/
namespace TwoLocalInnerDerivation

variable {R : Type*} [CommRing R]

lemma commute_Up_succ_zero {n a : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (hcomm : M * Up (R := R) n = Up (R := R) n * M) (ha : a + 1 < n) :
    M ⟨a + 1, ha⟩ ⟨0, by omega⟩ = 0 := by
  have h := congr_fun (congr_fun hcomm ⟨a, by omega⟩) ⟨0, by omega⟩
  rw [mul_Up_apply, Up_mul_apply] at h
  simpa [ha] using h.symm

lemma commute_Up_succ_succ {n a b : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (hcomm : M * Up (R := R) n = Up (R := R) n * M)
    (ha : a + 1 < n) (hb : b + 1 < n) :
    M ⟨a + 1, ha⟩ ⟨b + 1, hb⟩ = M ⟨a, by omega⟩ ⟨b, by omega⟩ := by
  have h := congr_fun (congr_fun hcomm ⟨a, by omega⟩) ⟨b + 1, hb⟩
  rw [mul_Up_apply, Up_mul_apply] at h
  simpa [ha] using h.symm

lemma commute_Up_below_aux {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (hcomm : M * Up (R := R) n = Up (R := R) n * M) :
    ∀ d : ℕ, ∀ i j : Fin n, j.1 = d → j.1 < i.1 → M i j = 0 := by
  intro d
  induction d with
  | zero =>
      intro i j hj hlt
      have hi : i.1 - 1 + 1 < n := by omega
      have hrow : i = ⟨i.1 - 1 + 1, hi⟩ := by
        apply Fin.eq_of_val_eq
        simp
        omega
      have hcol : j = ⟨0, by omega⟩ := by
        apply Fin.eq_of_val_eq
        simp [hj]
      rw [hrow, hcol]
      exact commute_Up_succ_zero (R := R) (n := n) (a := i.1 - 1) M hcomm hi
  | succ d ih =>
      intro i j hj hlt
      have hip : i.1 - 1 < n := by omega
      have hjp : d < n := by omega
      let ip : Fin n := ⟨i.1 - 1, hip⟩
      let jp : Fin n := ⟨d, hjp⟩
      have hi : ip.1 + 1 < n := by
        have : ip.1 = i.1 - 1 := rfl
        omega
      have hb : jp.1 + 1 < n := by
        have : jp.1 = d := rfl
        omega
      have hrow : i = ⟨ip.1 + 1, hi⟩ := by
        apply Fin.eq_of_val_eq
        have : (⟨ip.1 + 1, hi⟩ : Fin n).1 = ip.1 + 1 := rfl
        rw [this]
        have : ip.1 = i.1 - 1 := rfl
        omega
      have hcol : j = ⟨jp.1 + 1, hb⟩ := by
        apply Fin.eq_of_val_eq
        have : (⟨jp.1 + 1, hb⟩ : Fin n).1 = jp.1 + 1 := rfl
        rw [this]
        have : jp.1 = d := rfl
        omega
      rw [hrow, hcol]
      rw [commute_Up_succ_succ (R := R) (n := n) M hcomm hi hb]
      apply ih ip jp rfl
      have hipval : ip.1 = i.1 - 1 := rfl
      have hjpval : jp.1 = d := rfl
      rw [hipval, hjpval]
      omega

lemma commute_Up_eq_zero_of_lt {n : ℕ} {M : Matrix (Fin n) (Fin n) R}
    (hcomm : M * Up (R := R) n = Up (R := R) n * M) {i j : Fin n} (h : j.1 < i.1) :
    M i j = 0 :=
  commute_Up_below_aux (R := R) M hcomm j.1 i j rfl h

end TwoLocalInnerDerivation

/- accepted add_to_file helper 5 -/
namespace TwoLocalInnerDerivation

variable {R : Type*} [CommRing R]

lemma commute_Up_diag_aux {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (hcomm : M * Up (R := R) n = Up (R := R) n * M) :
    ∀ k : ℕ, ∀ hk : k < n,
      M ⟨k, hk⟩ ⟨k, hk⟩ = M ⟨0, by omega⟩ ⟨0, by omega⟩ := by
  intro k
  induction k with
  | zero =>
      intro hk
      rfl
  | succ k ih =>
      intro hk
      have hk0 : k < n := by omega
      have hsucc : k + 1 < n := hk
      rw [commute_Up_succ_succ (R := R) (n := n) M hcomm hsucc hsucc]
      exact ih hk0

lemma commute_Up_diag_eq {n : ℕ} {M : Matrix (Fin n) (Fin n) R}
    (hcomm : M * Up (R := R) n = Up (R := R) n * M) (i j : Fin n) :
    M i i = M j j := by
  have hi := commute_Up_diag_aux (R := R) M hcomm i.1 i.2
  have hj := commute_Up_diag_aux (R := R) M hcomm j.1 j.2
  rw [hi, hj]

lemma commute_Down_eq_zero_of_lt {n : ℕ} {M : Matrix (Fin n) (Fin n) R}
    (hcomm : M * Down (R := R) n = Down (R := R) n * M) {i j : Fin n}
    (h : i.1 < j.1) : M i j = 0 := by
  have ht : M.transpose * Up (R := R) n = Up (R := R) n * M.transpose := by
    have htr := congrArg Matrix.transpose hcomm
    have hs := htr.symm
    simpa [Matrix.transpose_mul, Down_transpose] using hs
  have hz := commute_Up_eq_zero_of_lt (R := R) (M := M.transpose) ht (i := j) (j := i) h
  simpa [Matrix.transpose_apply] using hz

lemma commute_Down_diag_eq {n : ℕ} {M : Matrix (Fin n) (Fin n) R}
    (hcomm : M * Down (R := R) n = Down (R := R) n * M) (i j : Fin n) :
    M i i = M j j := by
  have ht : M.transpose * Up (R := R) n = Up (R := R) n * M.transpose := by
    have htr := congrArg Matrix.transpose hcomm
    have hs := htr.symm
    simpa [Matrix.transpose_mul, Down_transpose] using hs
  have hd := commute_Up_diag_eq (R := R) (M := M.transpose) ht j i
  exact hd.symm

end TwoLocalInnerDerivation

/- accepted add_to_file helper 6 -/
namespace TwoLocalInnerDerivation

variable {R : Type*} [CommRing R]

lemma commute_E_row_eq_zero {n : ℕ} {M : Matrix (Fin n) (Fin n) R} {r s q : Fin n}
    (hcomm : M * E (R := R) r s = E (R := R) r s * M) (hq : q ≠ s) :
    M s q = 0 := by
  have h := congr_fun (congr_fun hcomm r) q
  rw [mul_E_apply, E_mul_apply] at h
  have hsq : s ≠ q := fun hqs => hq hqs.symm
  simp [hsq] at h
  exact h.symm

lemma commute_E_col_eq_zero {n : ℕ} {M : Matrix (Fin n) (Fin n) R} {r s q : Fin n}
    (hcomm : M * E (R := R) r s = E (R := R) r s * M) (hq : q ≠ r) :
    M q r = 0 := by
  have h := congr_fun (congr_fun hcomm q) s
  rw [mul_E_apply, E_mul_apply] at h
  have hrq : r ≠ q := fun hqr => hq hqr.symm
  simp [hrq] at h
  exact h

lemma commute_E_diag_diag_eq {n : ℕ} {M : Matrix (Fin n) (Fin n) R} {r s : Fin n}
    (hcomm : M * E (R := R) r s = E (R := R) r s * M) :
    M r r = M s s := by
  have h := congr_fun (congr_fun hcomm r) s
  rw [mul_E_apply, E_mul_apply] at h
  simpa using h

end TwoLocalInnerDerivation

/- accepted add_to_file helper 7 -/
namespace TwoLocalInnerDerivation

variable {R : Type*} [CommRing R]

lemma projector_extension {n : ℕ} {W U V : Matrix (Fin n) (Fin n) R} {p : Fin n}
    (hWU : W = U * E (R := R) p p - E (R := R) p p * U)
    (hWV : W = V * E (R := R) p p - E (R := R) p p * V)
    (hU : U * Up (R := R) n = Up (R := R) n * U)
    (hV : V * Down (R := R) n = Down (R := R) n * V) :
    W = 0 := by
  ext i j
  by_cases hi : i = p
  · by_cases hj : j = p
    · subst i
      subst j
      have h := congr_fun (congr_fun hWU p) p
      rw [Matrix.sub_apply, mul_E_apply, E_mul_apply] at h
      simpa [sub_self] using h
    · subst i
      have hpj : p ≠ j := fun h => hj h.symm
      have hUeq := congr_fun (congr_fun hWU p) j
      have hVeq := congr_fun (congr_fun hWV p) j
      rw [Matrix.sub_apply, mul_E_apply, E_mul_apply] at hUeq hVeq
      by_cases hlt : j.1 < p.1
      · have hz := commute_Up_eq_zero_of_lt (R := R) (M := U) hU hlt
        simp [hpj, hz] at hUeq
        exact hUeq
      · have hgt : p.1 < j.1 := by
          have hne : p.1 ≠ j.1 := by
            intro hv
            apply hj
            exact Fin.eq_of_val_eq hv.symm
          omega
        have hz := commute_Down_eq_zero_of_lt (R := R) (M := V) hV hgt
        simp [hpj, hz] at hVeq
        exact hVeq
  · have hpi : p ≠ i := fun h => hi h.symm
    by_cases hj : j = p
    · subst j
      have hUeq := congr_fun (congr_fun hWU i) p
      have hVeq := congr_fun (congr_fun hWV i) p
      rw [Matrix.sub_apply, mul_E_apply, E_mul_apply] at hUeq hVeq
      by_cases hlt : i.1 < p.1
      · have hz := commute_Down_eq_zero_of_lt (R := R) (M := V) hV hlt
        simp [hpi, hz] at hVeq
        exact hVeq
      · have hgt : p.1 < i.1 := by
          have hne : p.1 ≠ i.1 := by
            intro hv
            apply hi
            exact Fin.eq_of_val_eq hv.symm
          omega
        have hz := commute_Up_eq_zero_of_lt (R := R) (M := U) hU hgt
        simp [hpi, hz] at hUeq
        exact hUeq
    · have hpj : p ≠ j := fun h => hj h.symm
      have h := congr_fun (congr_fun hWU i) j
      rw [Matrix.sub_apply, mul_E_apply, E_mul_apply] at h
      simp [hpi, hpj] at h
      simpa using h

end TwoLocalInnerDerivation

/- accepted add_to_file helper 8 -/
namespace TwoLocalInnerDerivation

variable {R : Type*} [CommRing R]

lemma offdiag_extension {n : ℕ} {W U V T : Matrix (Fin n) (Fin n) R}
    {p q : Fin n}
    (hWU : W = U * E (R := R) p q - E (R := R) p q * U)
    (hWV : W = V * E (R := R) p q - E (R := R) p q * V)
    (hWT : W = T * E (R := R) p q - E (R := R) p q * T)
    (hU : U * E (R := R) p p = E (R := R) p p * U)
    (hV : V * E (R := R) q q = E (R := R) q q * V)
    (hT : T * Up (R := R) n = Up (R := R) n * T) :
    W = 0 := by
  ext a b
  by_cases ha : a = p
  · by_cases hb : b = q
    · subst a
      subst b
      have hTeq := congr_fun (congr_fun hWT p) q
      rw [Matrix.sub_apply, mul_E_apply, E_mul_apply] at hTeq
      have hdiag := commute_Up_diag_eq (R := R) (M := T) hT p q
      simp [hdiag] at hTeq
      exact hTeq
    · subst a
      have hqb : q ≠ b := fun h => hb h.symm
      have hVeq := congr_fun (congr_fun hWV p) b
      rw [Matrix.sub_apply, mul_E_apply, E_mul_apply] at hVeq
      have hz := commute_E_row_eq_zero (R := R) (M := V) (r := q) (s := q) (q := b) hV hb
      simp [hqb, hz] at hVeq
      exact hVeq
  · by_cases hb : b = q
    · subst b
      have hpa : p ≠ a := fun h => ha h.symm
      have hUeq := congr_fun (congr_fun hWU a) q
      rw [Matrix.sub_apply, mul_E_apply, E_mul_apply] at hUeq
      have hz := commute_E_col_eq_zero (R := R) (M := U) (r := p) (s := p) (q := a) hU ha
      simp [hpa, hz] at hUeq
      exact hUeq
    · have hpa : p ≠ a := fun h => ha h.symm
      have hqb : q ≠ b := fun h => hb h.symm
      have h := congr_fun (congr_fun hWU a) b
      rw [Matrix.sub_apply, mul_E_apply, E_mul_apply] at h
      simp [hpa, hqb] at h
      simpa using h

end TwoLocalInnerDerivation

/- accepted add_to_file helper 9 -/
namespace TwoLocalInnerDerivation

variable {R : Type*} [CommRing R]

lemma final_diag_entry {n : ℕ} {W U X : Matrix (Fin n) (Fin n) R} {a : Fin n}
    (hW : W = U * X - X * U)
    (hU : U * E (R := R) a a = E (R := R) a a * U) :
    W a a = 0 := by
  have hprod1 : (U * X) a a = U a a * X a a := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single a]
    · intro k _ hk
      have hz := commute_E_row_eq_zero (R := R) (M := U) (r := a) (s := a) (q := k) hU hk
      rw [hz, zero_mul]
    · simp
  have hprod2 : (X * U) a a = X a a * U a a := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single a]
    · intro k _ hk
      have hz := commute_E_col_eq_zero (R := R) (M := U) (r := a) (s := a) (q := k) hU hk
      rw [hz, mul_zero]
    · simp
  have h := congr_fun (congr_fun hW a) a
  rw [Matrix.sub_apply, hprod1, hprod2, mul_comm (U a a) (X a a), sub_self] at h
  exact h

lemma final_offdiag_entry {n : ℕ} {W U X : Matrix (Fin n) (Fin n) R} {a b : Fin n}
    (hW : W = U * X - X * U)
    (hU : U * E (R := R) b a = E (R := R) b a * U) :
    W a b = 0 := by
  have hprod1 : (U * X) a b = U a a * X a b := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single a]
    · intro k _ hk
      have hz := commute_E_row_eq_zero (R := R) (M := U) (r := b) (s := a) (q := k) hU hk
      rw [hz, zero_mul]
    · simp
  have hprod2 : (X * U) a b = X a b * U b b := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single b]
    · intro k _ hk
      have hz := commute_E_col_eq_zero (R := R) (M := U) (r := b) (s := a) (q := k) hU hk
      rw [hz, mul_zero]
    · simp
  have hdiag : U a a = U b b :=
    (commute_E_diag_diag_eq (R := R) (M := U) (r := b) (s := a) hU).symm
  have h := congr_fun (congr_fun hW a) b
  rw [Matrix.sub_apply, hprod1, hprod2, hdiag, mul_comm (U b b) (X a b), sub_self] at h
  exact h

end TwoLocalInnerDerivation

/- accepted add_to_file helper 10 -/
namespace TwoLocalInnerDerivation

variable {R : Type*} [CommRing R]

lemma comm_sub_of_comm_eq {n : ℕ} {A B Y : Matrix (Fin n) (Fin n) R}
    (hAB : A * Y - Y * A = B * Y - Y * B) :
    (A - B) * Y = Y * (A - B) := by
  rw [sub_mul, mul_sub]
  calc
    A * Y - B * Y = (A * Y - Y * A) + (Y * A - B * Y) := by abel
    _ = (B * Y - Y * B) + (Y * A - B * Y) := by rw [hAB]
    _ = Y * A - Y * B := by abel

end TwoLocalInnerDerivation

/- verified submission -/
open TwoLocalInnerDerivation

theorem two_local_inner_derivation_matrix_is_inner
    (R : Type*) [CommRing R] (n : ℕ) (hn : 1 < n)
    (h2 : IsUnit (2 : R))
    (Δ : Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R)
    (hΔ : ∀ X Y, ∃ A, Δ X = A * X - X * A ∧ Δ Y = A * Y - Y * A) :
    ∃ B, ∀ X, Δ X = B * X - X * B := by
  obtain ⟨B, hBU, hBD⟩ := hΔ (Up (R := R) n) (Down (R := R) n)
  have hBdiag : ∀ p : Fin n,
      Δ (E (R := R) p p) = B * E (R := R) p p - E (R := R) p p * B := by
    intro p
    obtain ⟨AU, hAUP, hAUU⟩ := hΔ (E (R := R) p p) (Up (R := R) n)
    obtain ⟨AD, hADP, hADD⟩ := hΔ (E (R := R) p p) (Down (R := R) n)
    let U : Matrix (Fin n) (Fin n) R := AU - B
    let V : Matrix (Fin n) (Fin n) R := AD - B
    have hU : U * Up (R := R) n = Up (R := R) n * U := by
      dsimp [U]
      apply comm_sub_of_comm_eq
      rw [← hAUU, ← hBU]
    have hV : V * Down (R := R) n = Down (R := R) n * V := by
      dsimp [V]
      apply comm_sub_of_comm_eq
      rw [← hADD, ← hBD]
    let W : Matrix (Fin n) (Fin n) R :=
      Δ (E (R := R) p p) - (B * E (R := R) p p - E (R := R) p p * B)
    have hWU : W = U * E (R := R) p p - E (R := R) p p * U := by
      dsimp [W, U]
      rw [hAUP, sub_mul, mul_sub]
      abel
    have hWV : W = V * E (R := R) p p - E (R := R) p p * V := by
      dsimp [W, V]
      rw [hADP, sub_mul, mul_sub]
      abel
    have hzero : W = 0 := projector_extension (R := R) hWU hWV hU hV
    have hsub : Δ (E (R := R) p p) - (B * E (R := R) p p - E (R := R) p p * B) = 0 := by
      dsimp [W] at hzero
      exact hzero
    exact sub_eq_zero.mp hsub
  have hBunit : ∀ p q : Fin n,
      Δ (E (R := R) p q) = B * E (R := R) p q - E (R := R) p q * B := by
    intro p q
    by_cases hpq : p = q
    · subst q
      exact hBdiag p
    · obtain ⟨AP, hAPQ, hAPP⟩ := hΔ (E (R := R) p q) (E (R := R) p p)
      obtain ⟨AQ, hAQQ, hAQP⟩ := hΔ (E (R := R) p q) (E (R := R) q q)
      obtain ⟨AT, hATQ, hATU⟩ := hΔ (E (R := R) p q) (Up (R := R) n)
      let U : Matrix (Fin n) (Fin n) R := AP - B
      let V : Matrix (Fin n) (Fin n) R := AQ - B
      let T : Matrix (Fin n) (Fin n) R := AT - B
      have hU : U * E (R := R) p p = E (R := R) p p * U := by
        dsimp [U]
        apply comm_sub_of_comm_eq
        rw [← hAPP, ← hBdiag p]
      have hV : V * E (R := R) q q = E (R := R) q q * V := by
        dsimp [V]
        apply comm_sub_of_comm_eq
        rw [← hAQP, ← hBdiag q]
      have hT : T * Up (R := R) n = Up (R := R) n * T := by
        dsimp [T]
        apply comm_sub_of_comm_eq
        rw [← hATU, ← hBU]
      let W : Matrix (Fin n) (Fin n) R :=
        Δ (E (R := R) p q) - (B * E (R := R) p q - E (R := R) p q * B)
      have hWU : W = U * E (R := R) p q - E (R := R) p q * U := by
        dsimp [W, U]
        rw [hAPQ, sub_mul, mul_sub]
        abel
      have hWV : W = V * E (R := R) p q - E (R := R) p q * V := by
        dsimp [W, V]
        rw [hAQQ, sub_mul, mul_sub]
        abel
      have hWT : W = T * E (R := R) p q - E (R := R) p q * T := by
        dsimp [W, T]
        rw [hATQ, sub_mul, mul_sub]
        abel
      have hzero : W = 0 := offdiag_extension (R := R) hWU hWV hWT hU hV hT
      have hsub : Δ (E (R := R) p q) - (B * E (R := R) p q - E (R := R) p q * B) = 0 := by
        dsimp [W] at hzero
        exact hzero
      exact sub_eq_zero.mp hsub
  refine ⟨B, ?_⟩
  intro X
  let W : Matrix (Fin n) (Fin n) R := Δ X - (B * X - X * B)
  have hWzero : W = 0 := by
    ext a b
    by_cases hab : a = b
    · subst b
      obtain ⟨A, hAX, hAE⟩ := hΔ X (E (R := R) a a)
      let U : Matrix (Fin n) (Fin n) R := A - B
      have hU : U * E (R := R) a a = E (R := R) a a * U := by
        dsimp [U]
        apply comm_sub_of_comm_eq
        rw [← hAE, ← hBunit a a]
      have hW : W = U * X - X * U := by
        dsimp [W, U]
        rw [hAX, sub_mul, mul_sub]
        abel
      exact final_diag_entry (R := R) hW hU
    · obtain ⟨A, hAX, hAE⟩ := hΔ X (E (R := R) b a)
      let U : Matrix (Fin n) (Fin n) R := A - B
      have hU : U * E (R := R) b a = E (R := R) b a * U := by
        dsimp [U]
        apply comm_sub_of_comm_eq
        rw [← hAE, ← hBunit b a]
      have hW : W = U * X - X * U := by
        dsimp [W, U]
        rw [hAX, sub_mul, mul_sub]
        abel
      exact final_offdiag_entry (R := R) hW hU
  have hsub : Δ X - (B * X - X * B) = 0 := by
    dsimp [W] at hWzero
    exact hWzero
  exact sub_eq_zero.mp hsub

end Rollout_p2823_two_local_inner_derivation_matrix_is_inner

namespace Rollout_p1722_hirzebruch_jung_large_entries_at_most_two

/- accepted add_to_file helper 1 -/

def hjCont : List ℤ → ℤ × ℤ
  | [] => (1, 0)
  | x :: xs =>
      let y := hjCont xs
      (x * y.1 - y.2, y.1)

lemma hjCont_bounds (xs : List ℤ) (h : ∀ x ∈ xs, 2 ≤ x) :
    0 < (hjCont xs).1 ∧
    0 ≤ (hjCont xs).2 ∧
    (hjCont xs).2 ≤ (hjCont xs).1 ∧
    (xs.map fun x => x - 1).prod ≤ (hjCont xs).1 := by
  induction xs with
  | nil => simp [hjCont]
  | cons x xs ih =>
      have hx : 2 ≤ x := h x (by simp)
      have hxs : ∀ y ∈ xs, 2 ≤ y := fun y hy => h y (by simp [hy])
      rcases ih hxs with ⟨hu_pos, hv_nonneg, hvu, hprod⟩
      set u := (hjCont xs).1
      set v := (hjCont xs).2
      have hu_nonneg : 0 ≤ u := le_of_lt hu_pos
      have hxu : 2 * u ≤ x * u := mul_le_mul_of_nonneg_right hx hu_nonneg
      have hxm1_nonneg : 0 ≤ x - 1 := by linarith
      have hmul : (x - 1) * (xs.map fun y => y - 1).prod ≤ (x - 1) * u :=
        mul_le_mul_of_nonneg_left hprod hxm1_nonneg
      have hstep : (x - 1) * u ≤ x * u - v := by nlinarith
      simp [hjCont]
      constructor
      · nlinarith
      constructor
      · exact hu_nonneg
      constructor
      · nlinarith
      · exact le_trans hmul hstep

lemma hjCont_snd_pos_of_ne_nil (xs : List ℤ) (h : ∀ x ∈ xs, 2 ≤ x) (hne : xs ≠ []) :
    0 < (hjCont xs).2 := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
      simp [hjCont]
      exact (hjCont_bounds xs (fun y hy => h y (by simp [hy]))).1

lemma hjCont_gcd (xs : List ℤ) :
    (hjCont xs).1.gcd (hjCont xs).2 = 1 := by
  induction xs with
  | nil => simp [hjCont]
  | cons x xs ih =>
      simp [hjCont]
      rw [Int.gcd_comm]
      exact ih

lemma hj_fold_eq_div (xs : List ℤ) (h : ∀ x ∈ xs, 2 ≤ x) :
    (xs.map fun x : ℤ => (x : ℚ)).foldr (fun x r => x - 1 / r) 0 =
      ((hjCont xs).1 : ℚ) / ((hjCont xs).2 : ℚ) := by
  induction xs with
  | nil => simp [hjCont]
  | cons x xs ih =>
      have hxs : ∀ y ∈ xs, 2 ≤ y := fun y hy => h y (by simp [hy])
      have hb := hjCont_bounds xs hxs
      have hN : ((hjCont xs).1 : ℚ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hb.1)
      rw [List.map_cons, List.foldr_cons, ih hxs]
      simp [hjCont]
      field_simp [hN]

lemma triple_tail_sum_le_prod_add_two (x y z : ℤ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (t : List ℤ) (ht : ∀ w ∈ t, 1 ≤ w) :
    5 * (x + y + z + t.sum) ≤
      (x + 2) * (y + 2) * (z + 2) * (t.map fun u => u + 2).prod := by
  induction t with
  | nil =>
      simp
      nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy),
        mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hz),
        mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr hz)]
  | cons w t ih =>
      have hw : 1 ≤ w := ht w (by simp)
      have ht' : ∀ u ∈ t, 1 ≤ u := by
        intro u hu
        exact ht u (by simp [hu])
      have hS : 3 ≤ x + y + z + t.sum := by
        have hnon : 0 ≤ t.sum := List.sum_nonneg (by
          intro u hu
          exact le_trans (by norm_num : (0:ℤ) ≤ 1) (ht' u hu))
        nlinarith
      have hP := ih ht'
      simp [List.sum_cons, List.map_cons, List.prod_cons]
      nlinarith

lemma list_sum_le_prod_add_two (xs : List ℤ)
    (hpos : ∀ x ∈ xs, 1 ≤ x) (hlen : 3 ≤ xs.length) :
    5 * xs.sum ≤ (xs.map fun x => x + 2).prod := by
  have hne : xs ≠ [] := by
    intro h
    rw [h] at hlen
    norm_num at hlen
  rcases List.exists_cons_of_ne_nil hne with ⟨x, xs₁, rfl⟩
  have hlen₁ : 2 ≤ xs₁.length := by
    simpa using hlen
  have hne₁ : xs₁ ≠ [] := by
    intro h
    rw [h] at hlen₁
    norm_num at hlen₁
  rcases List.exists_cons_of_ne_nil hne₁ with ⟨y, xs₂, rfl⟩
  have hlen₂ : 1 ≤ xs₂.length := by
    simpa using hlen₁
  have hne₂ : xs₂ ≠ [] := by
    intro h
    rw [h] at hlen₂
    norm_num at hlen₂
  rcases List.exists_cons_of_ne_nil hne₂ with ⟨z, t, rfl⟩
  have hx : 1 ≤ x := hpos x (by simp)
  have hy : 1 ≤ y := hpos y (by simp)
  have hz : 1 ≤ z := hpos z (by simp)
  have ht : ∀ w ∈ t, 1 ≤ w := by
    intro w hw
    exact hpos w (by simp [hw])
  have h := triple_tail_sum_le_prod_add_two x y z hx hy hz t ht
  simpa [List.sum_cons, List.map_cons, List.prod_cons, add_assoc, add_comm, add_left_comm,
    mul_assoc] using h

lemma finset_five_sum_excess_le_prod_sub_one {n : ℕ} (a : Fin n → ℤ)
    (ha : ∀ i, 2 ≤ a i)
    (F : Finset (Fin n)) (hF : F ⊆ Finset.univ.filter (fun i => 3 < a i))
    (hcard : 3 ≤ F.card) :
    5 * ∑ i ∈ F, (a i - 3) ≤ ∏ i ∈ Finset.univ, (a i - 1) := by
  let xs := F.toList.map (fun i => a i - 3)
  have hpos : ∀ x ∈ xs, 1 ≤ x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
    have hiF : i ∈ F := by
      simpa using hi
    have hbig : 3 < a i := by
      have hiu : i ∈ Finset.univ.filter (fun j => 3 < a j) := hF hiF
      simpa using hiu
    linarith
  have hlen : 3 ≤ xs.length := by
    simp [xs, hcard]
  have hlist := list_sum_le_prod_add_two xs hpos hlen
  have hsum : xs.sum = ∑ i ∈ F, (a i - 3) := by
    simp [xs]
  have hprodF : (xs.map fun x => x + 2).prod = ∏ i ∈ F, (a i - 1) := by
    simp [xs]
    apply Finset.prod_congr rfl
    intro i hi
    ring
  have hFprod : 5 * ∑ i ∈ F, (a i - 3) ≤ ∏ i ∈ F, (a i - 1) := by
    simpa [hsum, hprodF] using hlist
  have hsubset : (∏ i ∈ F, (a i - 1)) ≤ ∏ i ∈ Finset.univ, (a i - 1) := by
    apply Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ F)
    · intro i hi
      have := ha i
      linarith
    · intro i hi hnot
      have := ha i
      linarith
  exact le_trans hFprod hsubset

/- verified submission -/
theorem hirzebruch_jung_large_entries_at_most_two
    (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℤ)
    (ha : ∀ i, 2 ≤ a i)
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q)
    (hfrac : (List.ofFn fun i => (a i : ℚ)).foldr
      (fun x r => x - 1 / r) 0 = (p : ℚ) / (q : ℚ))
    (hS : (2 * (p : ℚ)) / 9 <
      ∑ i ∈ Finset.univ.filter (fun i => 3 < a i), ((a i - 3 : ℤ) : ℚ)) :
    (Finset.univ.filter (fun i => 3 < a i)).card ≤ 2 := by
  by_contra hcardle
  have hcard3 : 3 ≤ (Finset.univ.filter (fun i => 3 < a i)).card := by
    omega
  let L : List ℤ := List.ofFn a
  have hL : ∀ x ∈ L, 2 ≤ x := by
    intro x hx
    rw [List.mem_ofFn] at hx
    rcases hx with ⟨i, rfl⟩
    exact ha i
  have hcomb := finset_five_sum_excess_le_prod_sub_one a ha
    (Finset.univ.filter (fun i => 3 < a i)) (fun i hi => hi) hcard3
  have hb := hjCont_bounds L hL
  have hprod_eq : (L.map fun x : ℤ => x - 1).prod = ∏ i ∈ Finset.univ, (a i - 1) := by
    simp [L, List.map_ofFn]
    rw [List.prod_ofFn]
    rfl
  have hSN : 5 * ∑ i ∈ Finset.univ.filter (fun i => 3 < a i), (a i - 3) ≤ (hjCont L).1 := by
    exact le_trans (by simpa [hprod_eq] using hcomb) hb.2.2.2
  have hcf : (List.ofFn fun i => (a i : ℚ)).foldr (fun x r => x - 1 / r) 0 =
      ((hjCont L).1 : ℚ) / ((hjCont L).2 : ℚ) := by
    simpa [L] using hj_fold_eq_div L hL
  have hLne : L ≠ [] := by
    intro hnil
    have hlen : L.length = n := by simp [L]
    have hzero : L.length = 0 := by simp [hnil]
    omega
  have hDpos : 0 < (hjCont L).2 := hjCont_snd_pos_of_ne_nil L hL hLne
  have hgcd : (hjCont L).1.gcd (hjCont L).2 = 1 := hjCont_gcd L
  have hco : (hjCont L).1.natAbs.Coprime (hjCont L).2.natAbs := by
    rw [Nat.coprime_iff_gcd_eq_one]
    simpa [Int.gcd] using hgcd
  have hNnum : (((hjCont L).1 : ℚ) / ((hjCont L).2 : ℚ)).num = (hjCont L).1 :=
    Rat.num_div_eq_of_coprime hDpos hco
  have hpqInt : ((p : ℤ).natAbs).Coprime ((q : ℤ).natAbs) := by
    simpa using hpq
  have hpnum : ((p : ℚ) / (q : ℚ)).num = (p : ℤ) := by
    have h := Rat.num_div_eq_of_coprime (show (0 : ℤ) < (q : ℤ) by exact_mod_cast hq) hpqInt
    simpa using h
  have hNp : (hjCont L).1 = (p : ℤ) := by
    calc
      (hjCont L).1 = (((hjCont L).1 : ℚ) / ((hjCont L).2 : ℚ)).num := hNnum.symm
      _ = ((p : ℚ) / (q : ℚ)).num := by
        congr 1
        exact hcf.symm.trans hfrac
      _ = (p : ℤ) := hpnum
  rw [hNp] at hSN
  let S : ℤ := ∑ i ∈ Finset.univ.filter (fun i => 3 < a i), (a i - 3)
  have hSNp : (5 : ℤ) * S ≤ (p : ℤ) := by
    simpa [S] using hSN
  have hSNq : (5 : ℚ) * (S : ℚ) ≤ (p : ℚ) := by
    exact_mod_cast hSNp
  have hsumq : (∑ i ∈ Finset.univ.filter (fun i => 3 < a i), ((a i - 3 : ℤ) : ℚ)) = (S : ℚ) := by
    simp [S]
  have hSq : (2 * (p : ℚ)) / 9 < (S : ℚ) := by
    rw [← hsumq]
    exact hS
  have hpqpos : 0 < (p : ℚ) := by
    exact_mod_cast hp
  nlinarith

end Rollout_p1722_hirzebruch_jung_large_entries_at_most_two

namespace Rollout_p3184_levykhintchine_increment_bound

/- accepted add_to_file helper 1 -/

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

end Rollout_p3184_levykhintchine_increment_bound

namespace Rollout_p0496_normalized_modified_kbessel_nonincreasing_

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

end Rollout_p0496_normalized_modified_kbessel_nonincreasing_

namespace Rollout_p2331_reverse_cauchy_schwarz_with_three_term_min

/- accepted add_to_file helper 1 -/
lemma weighted_variance_bound {n : ℕ} (p z : Fin n → ℝ) (r R : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hzl : ∀ i, r ≤ z i) (hzu : ∀ i, z i ≤ R) :
    (∑ i, p i) * (∑ i, p i * z i ^ 2) - (∑ i, p i * z i) ^ 2 ≤
      (R - r) ^ 2 / 4 * (∑ i, p i) ^ 2 := by
  let U := ∑ i, p i
  let V := ∑ i, p i * z i ^ 2
  let W := ∑ i, p i * z i
  have hU : 0 ≤ U := by
    exact Finset.sum_nonneg fun i _ => hp i
  have hV : V ≤ (r + R) * W - r * R * U := by
    have hpoint : ∀ i ∈ Finset.univ,
        p i * z i ^ 2 ≤ p i * ((r + R) * z i - r * R) := by
      intro i _
      have hzi : z i ^ 2 ≤ (r + R) * z i - r * R := by
        have hnonneg : 0 ≤ (z i - r) * (R - z i) :=
          mul_nonneg (sub_nonneg.mpr (hzl i)) (sub_nonneg.mpr (hzu i))
        nlinarith
      exact mul_le_mul_of_nonneg_left hzi (hp i)
    calc
      V ≤ ∑ i, p i * ((r + R) * z i - r * R) := Finset.sum_le_sum hpoint
      _ = ∑ i, ((p i * z i) * (r + R) - p i * (r * R)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, (p i * z i) * (r + R)) - ∑ i, p i * (r * R) := by
        rw [Finset.sum_sub_distrib]
      _ = W * (r + R) - U * (r * R) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
      _ = (r + R) * W - r * R * U := by ring
  have hmul : U * V ≤ U * ((r + R) * W - r * R * U) :=
    mul_le_mul_of_nonneg_left hV hU
  have hsq : 0 ≤ (W - (r + R) * U / 2) ^ 2 := sq_nonneg _
  change U * V - W ^ 2 ≤ (R - r) ^ 2 / 4 * U ^ 2
  nlinarith

/- accepted add_to_file helper 2 -/
lemma interval_variance_bound {n : ℕ}
    (a A b B : ℝ)
    (ha : 0 < a) (haA : a ≤ A) (hb : 0 < b) (hbB : b ≤ B)
    (x y : Fin n → ℝ)
    (hx : ∀ i, a ≤ x i ∧ x i ≤ A)
    (hy : ∀ i, b ≤ y i ∧ y i ≤ B) :
    (∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 ≤
      ((A * B - a * b) ^ 2 / 4) *
        ((∑ i, x i ^ 2) ^ 2 / (A ^ 2 * a ^ 2)) := by
  have hA : 0 < A := lt_of_lt_of_le ha haA
  have hB : 0 < B := lt_of_lt_of_le hb hbB
  have hxpos : ∀ i, 0 < x i := fun i => lt_of_lt_of_le ha (hx i).1
  have hypos : ∀ i, 0 < y i := fun i => lt_of_lt_of_le hb (hy i).1
  have hvarx :
      (∑ i, x i ^ 2) * (∑ i, x i ^ 2 * (y i / x i) ^ 2) -
          (∑ i, x i ^ 2 * (y i / x i)) ^ 2 ≤
        (B / a - b / A) ^ 2 / 4 * (∑ i, x i ^ 2) ^ 2 := by
    apply weighted_variance_bound
    · intro i
      exact sq_nonneg (x i)
    · intro i
      apply (div_le_div_iff₀ hA (hxpos i)).mpr
      calc
        b * x i ≤ y i * x i := mul_le_mul_of_nonneg_right (hy i).1 (hxpos i).le
        _ ≤ y i * A := mul_le_mul_of_nonneg_left (hx i).2 (hypos i).le
    · intro i
      apply (div_le_div_iff₀ (hxpos i) ha).mpr
      calc
        y i * a ≤ B * a := mul_le_mul_of_nonneg_right (hy i).2 ha.le
        _ ≤ B * x i := mul_le_mul_of_nonneg_left (hx i).1 hB.le
  have hVeq : (∑ i, x i ^ 2 * (y i / x i) ^ 2) = ∑ i, y i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    have hxi : x i ≠ 0 := ne_of_gt (hxpos i)
    field_simp [hxi]
  have hWeq : (∑ i, x i ^ 2 * (y i / x i)) = ∑ i, x i * y i := by
    apply Finset.sum_congr rfl
    intro i _
    have hxi : x i ≠ 0 := ne_of_gt (hxpos i)
    field_simp [hxi]
  have hxterm :
      (∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 ≤
        (B / a - b / A) ^ 2 / 4 * (∑ i, x i ^ 2) ^ 2 := by
    simpa [hVeq, hWeq] using hvarx
  calc
    (∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 ≤
        (B / a - b / A) ^ 2 / 4 * (∑ i, x i ^ 2) ^ 2 := hxterm
    _ = ((A * B - a * b) ^ 2 / 4) *
          ((∑ i, x i ^ 2) ^ 2 / (A ^ 2 * a ^ 2)) := by
      field_simp [ha.ne', hA.ne']

/- accepted add_to_file helper 3 -/
lemma interval_cross_bound {n : ℕ}
    (a A b B : ℝ)
    (ha : 0 < a) (haA : a ≤ A) (hb : 0 < b) (hbB : b ≤ B)
    (x y : Fin n → ℝ)
    (hx : ∀ i, a ≤ x i ∧ x i ≤ A)
    (hy : ∀ i, b ≤ y i ∧ y i ≤ B) :
    (∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 ≤
      ((A * B - a * b) ^ 2 / 4) *
        ((∑ i, x i * y i) ^ 2 / (a * b * A * B)) := by
  let U := ∑ i, x i ^ 2
  let V := ∑ i, y i ^ 2
  let W := ∑ i, x i * y i
  have hU : 0 ≤ U := Finset.sum_nonneg fun i _ => sq_nonneg (x i)
  have hV : 0 ≤ V := Finset.sum_nonneg fun i _ => sq_nonneg (y i)
  have hlin :
      b * B * U + a * A * V ≤ (A * B + a * b) * W := by
    have hpoint : ∀ i ∈ Finset.univ,
        b * B * x i ^ 2 + a * A * y i ^ 2 ≤
          (A * B + a * b) * (x i * y i) := by
      intro i _
      have hfactor1 : 0 ≤ A * y i - b * x i := by
        apply sub_nonneg.mpr
        calc
          b * x i ≤ y i * x i := by
            exact mul_le_mul_of_nonneg_right (hy i).1
              (lt_of_lt_of_le ha (hx i).1).le
          _ ≤ y i * A := by
            exact mul_le_mul_of_nonneg_left (hx i).2
              (lt_of_lt_of_le hb (hy i).1).le
          _ = A * y i := by ring
      have hfactor2 : 0 ≤ B * x i - a * y i := by
        apply sub_nonneg.mpr
        calc
          a * y i ≤ a * B := by
            exact mul_le_mul_of_nonneg_left (hy i).2 ha.le
          _ = B * a := by ring
          _ ≤ B * x i := by
            exact mul_le_mul_of_nonneg_left (hx i).1 (lt_of_lt_of_le hb hbB).le
      have hprod : 0 ≤ (A * y i - b * x i) * (B * x i - a * y i) :=
        mul_nonneg hfactor1 hfactor2
      nlinarith
    have hsum := Finset.sum_le_sum hpoint
    have hleft :
        (∑ i, (b * B * x i ^ 2 + a * A * y i ^ 2)) =
          b * B * U + a * A * V := by
      calc
        (∑ i, (b * B * x i ^ 2 + a * A * y i ^ 2)) =
            (∑ i, b * B * x i ^ 2) + ∑ i, a * A * y i ^ 2 :=
          Finset.sum_add_distrib
        _ = b * B * (∑ i, x i ^ 2) + a * A * (∑ i, y i ^ 2) := by
          congr 1
          · rw [← Finset.mul_sum]
          · rw [← Finset.mul_sum]
    have hright :
        (∑ i, (A * B + a * b) * (x i * y i)) =
          (A * B + a * b) * W := by
      rw [← Finset.mul_sum]
    rw [hleft, hright] at hsum
    exact hsum
  have hLnonneg : 0 ≤ b * B * U + a * A * V := by
    exact add_nonneg
      (mul_nonneg (mul_pos hb (lt_of_lt_of_le hb hbB)).le hU)
      (mul_nonneg (mul_pos ha (lt_of_lt_of_le ha haA)).le hV)
  have hsq : (b * B * U + a * A * V) ^ 2 ≤ ((A * B + a * b) * W) ^ 2 :=
    pow_le_pow_left₀ hLnonneg hlin 2
  have h4 : 4 * (b * B) * (a * A) * (U * V) ≤
      (b * B * U + a * A * V) ^ 2 := by
    nlinarith [sq_nonneg (b * B * U - a * A * V)]
  have hmain : 4 * (b * B) * (a * A) * (U * V) ≤
      ((A * B + a * b) * W) ^ 2 := le_trans h4 hsq
  have hnum : 4 * (b * B) * (a * A) * (U * V - W ^ 2) ≤
      (A * B - a * b) ^ 2 * W ^ 2 := by
    nlinarith
  have hden : 0 < 4 * (b * B) * (a * A) := by
    have hA : 0 < A := lt_of_lt_of_le ha haA
    have hB : 0 < B := lt_of_lt_of_le hb hbB
    positivity
  have htarget : U * V - W ^ 2 ≤
      ((A * B - a * b) ^ 2 * W ^ 2) / (4 * (b * B) * (a * A)) := by
    exact (le_div_iff₀ hden).mpr (by nlinarith)
  have hA : 0 < A := lt_of_lt_of_le ha haA
  have hB : 0 < B := lt_of_lt_of_le hb hbB
  calc
    (∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 =
        U * V - W ^ 2 := rfl
    _ ≤ ((A * B - a * b) ^ 2 * W ^ 2) / (4 * (b * B) * (a * A)) := htarget
    _ = ((A * B - a * b) ^ 2 / 4) *
          (W ^ 2 / (a * b * A * B)) := by
      field_simp [ha.ne', hA.ne', hb.ne', hB.ne']

/- accepted add_to_file helper 4 -/
lemma three_term_strict_examples :
    ∀ k : Fin 3,
      ∃ (m : ℕ) (a' A' b' B' : ℝ) (x' y' : Fin m → ℝ),
        1 ≤ m ∧
        0 < a' ∧ a' ≤ A' ∧ 0 < b' ∧ b' ≤ B' ∧
        (∀ i, a' ≤ x' i ∧ x' i ≤ A') ∧
        (∀ i, b' ≤ y' i ∧ y' i ≤ B') ∧
        (let t : Fin 3 → ℝ :=
          ![((∑ i, x' i ^ 2) ^ 2 / (A' ^ 2 * a' ^ 2)),
            ((∑ i, y' i ^ 2) ^ 2 / (B' ^ 2 * b' ^ 2)),
            ((∑ i, x' i * y' i) ^ 2 / (a' * b' * A' * B'))]
         ∀ j : Fin 3, j ≠ k → t k < t j) := by
  intro k
  fin_cases k
  · refine ⟨1, 1, 2, 1, 2, fun _ => 1, fun _ => 2, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · intro i
      norm_num
    · intro i
      norm_num
    · dsimp
      intro j hj
      fin_cases j
      · simp at hj
      · norm_num [Fin.sum_univ_one]
      · norm_num [Fin.sum_univ_one]
  · refine ⟨1, 1, 2, 1, 2, fun _ => 2, fun _ => 1, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · intro i
      norm_num
    · intro i
      norm_num
    · dsimp
      intro j hj
      fin_cases j
      · norm_num [Fin.sum_univ_one]
      · simp at hj
      · norm_num [Fin.sum_univ_one]
  · refine ⟨2, 1, 2, 1, 2, ![2, 1], ![1, 2], by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> norm_num
    · intro i
      fin_cases i <;> norm_num
    · dsimp
      intro j hj
      fin_cases j
      · norm_num [Fin.sum_univ_two]
      · norm_num [Fin.sum_univ_two]
      · simp at hj

/- verified submission -/
theorem reverse_cauchy_schwarz_with_three_term_min
    (n : ℕ) (hn : 1 ≤ n)
    (a A b B : ℝ)
    (ha : 0 < a) (haA : a ≤ A) (hb : 0 < b) (hbB : b ≤ B)
    (x y : Fin n → ℝ)
    (hx : ∀ i, a ≤ x i ∧ x i ≤ A)
    (hy : ∀ i, b ≤ y i ∧ y i ≤ B) :
    ((∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 ≤
      ((A * B - a * b) ^ 2 / 4) *
        min ((∑ i, x i ^ 2) ^ 2 / (A ^ 2 * a ^ 2))
          (min ((∑ i, y i ^ 2) ^ 2 / (B ^ 2 * b ^ 2))
            ((∑ i, x i * y i) ^ 2 / (a * b * A * B)))) ∧
    (∀ k : Fin 3,
      ∃ (m : ℕ) (a' A' b' B' : ℝ) (x' y' : Fin m → ℝ),
        1 ≤ m ∧
        0 < a' ∧ a' ≤ A' ∧ 0 < b' ∧ b' ≤ B' ∧
        (∀ i, a' ≤ x' i ∧ x' i ≤ A') ∧
        (∀ i, b' ≤ y' i ∧ y' i ≤ B') ∧
        (let t : Fin 3 → ℝ :=
          ![((∑ i, x' i ^ 2) ^ 2 / (A' ^ 2 * a' ^ 2)),
            ((∑ i, y' i ^ 2) ^ 2 / (B' ^ 2 * b' ^ 2)),
            ((∑ i, x' i * y' i) ^ 2 / (a' * b' * A' * B'))]
         ∀ j : Fin 3, j ≠ k → t k < t j)) := by
  constructor
  · have hxbound :
        (∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 ≤
          ((A * B - a * b) ^ 2 / 4) *
            ((∑ i, x i ^ 2) ^ 2 / (A ^ 2 * a ^ 2)) :=
      interval_variance_bound a A b B ha haA hb hbB x y hx hy
    have hyraw := interval_variance_bound b B a A hb hbB ha haA y x hy hx
    have hybound :
        (∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 ≤
          ((A * B - a * b) ^ 2 / 4) *
            ((∑ i, y i ^ 2) ^ 2 / (B ^ 2 * b ^ 2)) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hyraw
    have hcrossbound :
        (∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 ≤
          ((A * B - a * b) ^ 2 / 4) *
            ((∑ i, x i * y i) ^ 2 / (a * b * A * B)) :=
      interval_cross_bound a A b B ha haA hb hbB x y hx hy
    have hc : 0 ≤ ((A * B - a * b) ^ 2 / 4) := by positivity
    rw [mul_min_of_nonneg _ _ hc, mul_min_of_nonneg _ _ hc]
    exact le_min hxbound (le_min hybound hcrossbound)
  · exact three_term_strict_examples

end Rollout_p2331_reverse_cauchy_schwarz_with_three_term_min

namespace Rollout_p1355_locallycontinuousmeasurableonecocycle_iff_

/- verified submission -/
theorem locallyContinuousMeasurableOneCocycle_iff_continuousCrossedHomomorphism
    {G A : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [DistribMulAction G A] [ContinuousSMul G A]
    [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace A] [BorelSpace A]
    (c : G → A) :
    (Measurable c ∧
        (∀ s t : G, c (s * t) = c s + s • c t) ∧
        ∃ U : Set G, IsOpen U ∧ (1 : G) ∈ U ∧ ContinuousOn c U) ↔
      (Continuous c ∧ ∀ s t : G, c (s * t) = c s + s • c t) := by
  constructor
  · rintro ⟨hmeas, hcoc, U, hUopen, h1U, hcU⟩
    have hc1 : ContinuousAt c 1 := hcU.continuousAt (hUopen.mem_nhds h1U)
    have hcont : Continuous c := by
      rw [continuous_iff_continuousAt]
      intro g
      have hceq : c = fun x => c g + g • c (g⁻¹ * x) := by
        funext x
        calc
          c x = c (g * (g⁻¹ * x)) := by
            congr 1
            rw [← mul_assoc, mul_inv_cancel, one_mul]
          _ = c g + g • c (g⁻¹ * x) := hcoc g (g⁻¹ * x)
      rw [hceq]
      have hgx : ContinuousAt (fun x : G => g⁻¹ * x) g :=
        continuousAt_const.mul continuousAt_id
      have hc1g : ContinuousAt c (g⁻¹ * g) := by
        rw [inv_mul_cancel]
        exact hc1
      have hinner : ContinuousAt (fun x : G => c (g⁻¹ * x)) g :=
        ContinuousAt.comp hc1g hgx
      exact continuousAt_const.add (hinner.const_smul g)
    exact ⟨hcont, hcoc⟩
  · rintro ⟨hcont, hcoc⟩
    exact ⟨hcont.measurable, hcoc, Set.univ, isOpen_univ, Set.mem_univ 1, hcont.continuousOn⟩

end Rollout_p1355_locallycontinuousmeasurableonecocycle_iff_

namespace Rollout_p1362_common_coincidence_point_of_ordered_metric

/- accepted add_to_file helper 1 -/
lemma not_cauchySeq_far_pair
    {X : Type*} [MetricSpace X] {u : ℕ → X}
    {ε : ℝ} (hε : 0 < ε)
    (hbad : ∀ N : ℕ, ∃ m ≥ N, ∃ n ≥ N, ε ≤ dist (u m) (u n)) :
    ∀ N : ℕ, ∃ m n : ℕ, N ≤ m ∧ m < n ∧ ε ≤ dist (u m) (u n) ∧
      ∀ j : ℕ, m < j → j < n → dist (u m) (u j) < ε := by
  classical
  intro N
  let P : ℕ → Prop := fun m => N ≤ m ∧ ∃ n, m < n ∧ ε ≤ dist (u m) (u n)
  have hP : ∃ m, P m := by
    obtain ⟨m, hmN, n, hnN, hmn⟩ := hbad N
    rcases lt_trichotomy m n with hlt | heq | hgt
    · exact ⟨m, hmN, n, hlt, hmn⟩
    · subst n
      have : ε ≤ 0 := by simpa [dist_self] using hmn
      linarith
    · refine ⟨n, hnN, m, hgt, ?_⟩
      rwa [dist_comm]
  let m := Nat.find hP
  have hm : P m := Nat.find_spec hP
  obtain ⟨hmN, n₀, hmn₀, hfar₀⟩ := hm
  let Q : ℕ → Prop := fun n => m < n ∧ ε ≤ dist (u m) (u n)
  have hQ : ∃ n, Q n := ⟨n₀, hmn₀, hfar₀⟩
  let n := Nat.find hQ
  have hn : Q n := Nat.find_spec hQ
  refine ⟨m, n, hmN, hn.1, hn.2, ?_⟩
  intro j hmj hjn
  have hnot : ¬ Q j := Nat.find_min hQ hjn
  have : ¬ ε ≤ dist (u m) (u j) := by
    intro hj
    exact hnot ⟨hmj, hj⟩
  exact lt_of_not_ge this

/- accepted add_to_file helper 2 -/
lemma not_cauchySeq_subseq
    {X : Type*} [MetricSpace X] {u : ℕ → X}
    (h : ¬ CauchySeq u) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m n : ℕ → ℕ,
      StrictMono m ∧ StrictMono n ∧
      ∀ k : ℕ,
        m k < n k ∧
        ε ≤ dist (u (m k)) (u (n k)) ∧
        dist (u (m k)) (u (n k)) <
          ε + dist (u (n k - 1)) (u (n k)) := by
  classical
  rw [Metric.cauchySeq_iff] at h
  push Not at h
  obtain ⟨ε, hε, hbad⟩ := h
  let PairProp : ℕ × ℕ → Prop := fun p =>
    p.1 < p.2 ∧ ε ≤ dist (u p.1) (u p.2) ∧
      ∀ j : ℕ, p.1 < j → j < p.2 → dist (u p.1) (u j) < ε
  let PairAt : ℕ → Type := fun N => {p : ℕ × ℕ // N ≤ p.1 ∧ PairProp p}
  have hpair_exists : ∀ N : ℕ, Nonempty (PairAt N) := by
    intro N
    obtain ⟨m, n, hmN, hmn, hfar, hmin⟩ :=
      not_cauchySeq_far_pair (u := u) hε hbad N
    exact ⟨⟨(m, n), hmN, hmn, hfar, hmin⟩⟩
  let choosePair : ∀ N : ℕ, PairAt N := fun N => Classical.choice (hpair_exists N)
  let state : ℕ → Σ N : ℕ, PairAt N := fun k =>
    Nat.rec ⟨0, choosePair 0⟩
      (fun k prev =>
        ⟨max (prev.2.1.2 + 1) (k + 1),
          choosePair (max (prev.2.1.2 + 1) (k + 1))⟩) k
  let m : ℕ → ℕ := fun k => (state k).2.1.1
  let n : ℕ → ℕ := fun k => (state k).2.1.2
  have hpair : ∀ k, PairProp (m k, n k) := fun k => (state k).2.2.2
  have hm_lt_n : ∀ k, m k < n k := fun k => (hpair k).1
  have hnext : ∀ k, n k < m (k + 1) := by
    intro k
    have hlow : max (n k + 1) (k + 1) ≤ m (k + 1) := by
      change max ((state k).2.1.2 + 1) (k + 1) ≤
        (state (k + 1)).2.1.1
      rw [show state (k + 1) =
        ⟨max ((state k).2.1.2 + 1) (k + 1),
          choosePair (max ((state k).2.1.2 + 1) (k + 1))⟩ from rfl]
      exact (choosePair (max ((state k).2.1.2 + 1) (k + 1))).2.1
    exact lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_left _ _).trans hlow)
  have hm_strict : StrictMono m :=
    strictMono_nat_of_lt_succ (fun k => (hm_lt_n k).trans (hnext k))
  have hn_strict : StrictMono n :=
    strictMono_nat_of_lt_succ (fun k => (hnext k).trans (hm_lt_n (k + 1)))
  refine ⟨ε, hε, m, n, hm_strict, hn_strict, ?_⟩
  intro k
  refine ⟨hm_lt_n k, (hpair k).2.1, ?_⟩
  have hprev : dist (u (m k)) (u (n k - 1)) < ε := by
    by_cases hlt : m k < n k - 1
    · exact (hpair k).2.2 (n k - 1) hlt (Nat.sub_one_lt_of_lt (hm_lt_n k))
    · have hle1 : n k - 1 ≤ m k := Nat.le_of_not_gt hlt
      have hle2 : m k ≤ n k - 1 := Nat.le_pred_of_lt (hm_lt_n k)
      have heq : n k - 1 = m k := le_antisymm hle1 hle2
      rw [heq, dist_self]
      exact hε
  calc
    dist (u (m k)) (u (n k)) ≤
        dist (u (m k)) (u (n k - 1)) + dist (u (n k - 1)) (u (n k)) :=
      dist_triangle _ _ _
    _ < ε + dist (u (n k - 1)) (u (n k)) := add_lt_add_left hprev _

/- accepted add_to_file helper 3 -/
lemma tendsto_zero_of_succ_le_beta_mul
    {β : NNReal → NNReal}
    (hβ_lt_one : ∀ t, β t < 1)
    (hβ_zero : ∀ t : ℕ → NNReal,
      Filter.Tendsto (fun n => β (t n)) Filter.atTop (nhds 1) →
        Filter.Tendsto t Filter.atTop (nhds 0))
    {r : ℕ → NNReal}
    (hstep : ∀ n, r (n + 1) ≤ β (r n) * r n) :
    Filter.Tendsto r Filter.atTop (nhds 0) := by
  have hdec : ∀ n, r (n + 1) ≤ r n := by
    intro n
    calc
      r (n + 1) ≤ β (r n) * r n := hstep n
      _ ≤ 1 * r n := mul_le_mul_right' (le_of_lt (hβ_lt_one _)) _
      _ = r n := one_mul _
  let L : NNReal := ⨅ i, r i
  have hbdd : BddBelow (Set.range r) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact zero_le _⟩
  have hanti : Antitone r := antitone_nat_of_succ_le hdec
  have hlim : Filter.Tendsto r Filter.atTop (nhds L) :=
    tendsto_atTop_ciInf hanti hbdd
  by_cases hL : L = 0
  · simpa [L, hL] using hlim
  · have hLpos : 0 < L := lt_of_le_of_ne' (zero_le L) hL
    have hlimR : Filter.Tendsto (fun n => (r n : ℝ)) Filter.atTop (nhds (L : ℝ)) :=
      (NNReal.tendsto_coe).2 hlim
    have hlimNext : Filter.Tendsto (fun n => r (n + 1)) Filter.atTop (nhds L) :=
      hlim.comp (Filter.tendsto_add_atTop_nat 1)
    have hlimNextR : Filter.Tendsto (fun n => (r (n + 1) : ℝ)) Filter.atTop
        (nhds (L : ℝ)) :=
      (NNReal.tendsto_coe).2 hlimNext
    have hLneR : (L : ℝ) ≠ 0 := by
      exact_mod_cast ne_of_gt hLpos
    have hq : Filter.Tendsto (fun n => (r (n + 1) : ℝ) / (r n : ℝ))
        Filter.atTop (nhds 1) := by
      have hdiv := hlimNextR.div hlimR hLneR
      simpa [div_self hLneR] using hdiv
    have hq_le : (fun n => (r (n + 1) : ℝ) / (r n : ℝ)) ≤
        fun n => (β (r n) : ℝ) := by
      intro n
      have hLrn : L ≤ r n := ciInf_le hbdd n
      have hrpos : (0 : ℝ) < (r n : ℝ) := by
        exact_mod_cast hLpos.trans_le hLrn
      have hsR : (r (n + 1) : ℝ) ≤ (β (r n) : ℝ) * (r n : ℝ) := by
        exact_mod_cast hstep n
      exact (div_le_iff₀ hrpos).2 hsR
    have hβ_le_one : (fun n => (β (r n) : ℝ)) ≤ fun _ => (1 : ℝ) := by
      intro n
      exact_mod_cast le_of_lt (hβ_lt_one (r n))
    have hβ_tendstoR : Filter.Tendsto (fun n => (β (r n) : ℝ))
        Filter.atTop (nhds (1 : ℝ)) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le hq tendsto_const_nhds hq_le hβ_le_one
    have hβ_tendsto : Filter.Tendsto (fun n => β (r n)) Filter.atTop (nhds 1) :=
      (NNReal.tendsto_coe).1 hβ_tendstoR
    have hzero := hβ_zero r hβ_tendsto
    have hLeq : L = 0 := tendsto_nhds_unique hlim hzero
    exact False.elim (hL hLeq)

/- accepted add_to_file helper 4 -/
lemma cauchySeq_of_ordered_beta_contraction
    {X : Type*} [PartialOrder X] [MetricSpace X]
    {y : ℕ → X} {β : NNReal → NNReal}
    (hβ_lt_one : ∀ t, β t < 1)
    (hβ_zero : ∀ t : ℕ → NNReal,
      Filter.Tendsto (fun n => β (t n)) Filter.atTop (nhds 1) →
        Filter.Tendsto t Filter.atTop (nhds 0))
    (hmono : Monotone y)
    (hcross : ∀ m n : ℕ, m < n →
      nndist (y (m + 1)) (y (n + 1)) ≤
        β (nndist (y m) (y n)) * nndist (y m) (y n)) :
    CauchySeq y := by
  let r : ℕ → NNReal := fun k => nndist (y k) (y (k + 1))
  have hr_step : ∀ k, r (k + 1) ≤ β (r k) * r k := by
    intro k
    exact hcross k (k + 1) (Nat.lt_succ_self k)
  have hr0 : Filter.Tendsto r Filter.atTop (nhds 0) :=
    tendsto_zero_of_succ_le_beta_mul hβ_lt_one hβ_zero hr_step
  have hr0_real : Filter.Tendsto (fun k => dist (y k) (y (k + 1)))
      Filter.atTop (nhds 0) := by
    have hcoe : Filter.Tendsto (fun k => (r k : ℝ)) Filter.atTop (nhds 0) :=
      (NNReal.tendsto_coe).2 hr0
    have heq : (fun k => (r k : ℝ)) =ᶠ[Filter.atTop]
        fun k => dist (y k) (y (k + 1)) := by
      refine Filter.Eventually.of_forall ?_
      intro k
      change (nndist (y k) (y (k + 1)) : ℝ) = dist (y k) (y (k + 1))
      rw [dist_nndist]
    exact Filter.Tendsto.congr' heq hcoe
  by_contra hc
  obtain ⟨ε, hε, m, n, hmstrict, hnstrict, hpair⟩ := not_cauchySeq_subseq hc
  have hmn : ∀ k, m k < n k := fun k => (hpair k).1
  have hlower : ∀ k, ε ≤ dist (y (m k)) (y (n k)) := fun k => (hpair k).2.1
  have hupper : ∀ k, dist (y (m k)) (y (n k)) <
      ε + dist (y (n k - 1)) (y (n k)) := fun k => (hpair k).2.2
  have hnpos : ∀ k, 0 < n k := fun k => Nat.zero_lt_of_lt (hmn k)
  have hn_pred_tendsto : Filter.Tendsto (fun k => n k - 1) Filter.atTop Filter.atTop :=
    (Filter.tendsto_sub_atTop_nat 1).comp hnstrict.tendsto_atTop
  have hsmall_nn : Filter.Tendsto (fun k => r (n k - 1)) Filter.atTop (nhds 0) :=
    hr0.comp hn_pred_tendsto
  have hsmall : Filter.Tendsto (fun k => dist (y (n k - 1)) (y (n k)))
      Filter.atTop (nhds 0) := by
    have hcoe : Filter.Tendsto (fun k => (r (n k - 1) : ℝ)) Filter.atTop (nhds 0) :=
      (NNReal.tendsto_coe).2 hsmall_nn
    have heq : (fun k => (r (n k - 1) : ℝ)) =ᶠ[Filter.atTop]
        fun k => dist (y (n k - 1)) (y (n k)) := by
      refine Filter.Eventually.of_forall ?_
      intro k
      change (nndist (y (n k - 1)) (y (n k - 1 + 1)) : ℝ) =
        dist (y (n k - 1)) (y (n k))
      rw [Nat.sub_one_add_one (ne_of_gt (hnpos k)), dist_nndist]
    exact Filter.Tendsto.congr' heq hcoe
  have hε_small : Filter.Tendsto (fun k => ε + dist (y (n k - 1)) (y (n k)))
      Filter.atTop (nhds ε) := by
    have hcst : Filter.Tendsto (fun _ : ℕ => ε) Filter.atTop (nhds ε) :=
      tendsto_const_nhds
    have h := hcst.add hsmall
    simpa only [add_zero] using h
  have hD : Filter.Tendsto (fun k => dist (y (m k)) (y (n k)))
      Filter.atTop (nhds ε) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hε_small
      (fun k => hlower k) (fun k => le_of_lt (hupper k))
  have hm_step : Filter.Tendsto (fun k => dist (y (m k + 1)) (y (m k)))
      Filter.atTop (nhds 0) := by
    have h := hr0_real.comp hmstrict.tendsto_atTop
    change Filter.Tendsto (fun k => dist (y (m k)) (y (m k + 1)))
      Filter.atTop (nhds 0) at h
    have heq : (fun k => dist (y (m k)) (y (m k + 1))) =
        fun k => dist (y (m k + 1)) (y (m k)) := by
      funext k
      exact dist_comm _ _
    rw [heq] at h
    exact h
  have hn_step : Filter.Tendsto (fun k => dist (y (n k)) (y (n k + 1)))
      Filter.atTop (nhds 0) := by
    have h := hr0_real.comp hnstrict.tendsto_atTop
    change Filter.Tendsto (fun k => dist (y (n k)) (y (n k + 1)))
      Filter.atTop (nhds 0) at h
    exact h
  have hS : Filter.Tendsto
      (fun k => dist (y (m k + 1)) (y (m k)) +
        dist (y (n k + 1)) (y (n k)))
      Filter.atTop (nhds 0) := by
    have hn_step' : Filter.Tendsto (fun k => dist (y (n k + 1)) (y (n k)))
        Filter.atTop (nhds 0) := by
      have heq : (fun k => dist (y (n k)) (y (n k + 1))) =
          fun k => dist (y (n k + 1)) (y (n k)) := by
        funext k
        exact dist_comm _ _
      rw [heq] at hn_step
      exact hn_step
    have h := hm_step.add hn_step'
    simpa only [add_zero] using h
  have hDshift : Filter.Tendsto (fun k => dist (y (m k + 1)) (y (n k + 1)))
      Filter.atTop (nhds ε) := by
    have hlowT : Filter.Tendsto
        (fun k => dist (y (m k)) (y (n k)) -
          (dist (y (m k + 1)) (y (m k)) + dist (y (n k + 1)) (y (n k))))
        Filter.atTop (nhds ε) := by
      have h := hD.sub hS
      simpa only [sub_zero] using h
    have hhighT : Filter.Tendsto
        (fun k => dist (y (m k)) (y (n k)) +
          (dist (y (m k + 1)) (y (m k)) + dist (y (n k + 1)) (y (n k))))
        Filter.atTop (nhds ε) := by
      have h := hD.add hS
      simpa only [add_zero] using h
    have hlow : (fun k => dist (y (m k)) (y (n k)) -
          (dist (y (m k + 1)) (y (m k)) + dist (y (n k + 1)) (y (n k)))) ≤
        fun k => dist (y (m k + 1)) (y (n k + 1)) := by
      intro k
      have hdiff := dist_dist_dist_le (y (m k + 1)) (y (n k + 1)) (y (m k)) (y (n k))
      rw [Real.dist_eq] at hdiff
      have hparts := (abs_sub_le_iff.mp hdiff).2
      linarith
    have hhigh : (fun k => dist (y (m k + 1)) (y (n k + 1))) ≤
        fun k => dist (y (m k)) (y (n k)) +
          (dist (y (m k + 1)) (y (m k)) + dist (y (n k + 1)) (y (n k))) := by
      intro k
      have hdiff := dist_dist_dist_le (y (m k + 1)) (y (n k + 1)) (y (m k)) (y (n k))
      rw [Real.dist_eq] at hdiff
      have hparts := (abs_sub_le_iff.mp hdiff).1
      linarith
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlowT hhighT hlow hhigh
  let t : ℕ → NNReal := fun k => nndist (y (m k)) (y (n k))
  have hq : Filter.Tendsto
      (fun k => dist (y (m k + 1)) (y (n k + 1)) /
        dist (y (m k)) (y (n k)))
      Filter.atTop (nhds 1) := by
    have hεne : ε ≠ 0 := ne_of_gt hε
    have hdiv := hDshift.div hD hεne
    simpa [div_self hεne] using hdiv
  have hq_le : (fun k => dist (y (m k + 1)) (y (n k + 1)) /
        dist (y (m k)) (y (n k))) ≤ fun k => (β (t k) : ℝ) := by
    intro k
    have hDpos : 0 < dist (y (m k)) (y (n k)) := hε.trans_le (hlower k)
    have hcrossR : dist (y (m k + 1)) (y (n k + 1)) ≤
        (β (t k) : ℝ) * dist (y (m k)) (y (n k)) := by
      have hc := hcross (m k) (n k) (hmn k)
      change nndist (y (m k + 1)) (y (n k + 1)) ≤ β (t k) * t k at hc
      calc
        dist (y (m k + 1)) (y (n k + 1)) =
            (nndist (y (m k + 1)) (y (n k + 1)) : ℝ) := dist_nndist _ _
        _ ≤ (β (t k) * t k : NNReal) := by exact_mod_cast hc
        _ = (β (t k) : ℝ) * dist (y (m k)) (y (n k)) := by
          rw [NNReal.coe_mul, dist_nndist]
    exact (div_le_iff₀ hDpos).2 hcrossR
  have hβ_le_one : (fun k => (β (t k) : ℝ)) ≤ fun _ => (1 : ℝ) := by
    intro k
    exact_mod_cast le_of_lt (hβ_lt_one (t k))
  have hβ_tendstoR : Filter.Tendsto (fun k => (β (t k) : ℝ))
      Filter.atTop (nhds (1 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hq tendsto_const_nhds hq_le hβ_le_one
  have hβ_tendsto : Filter.Tendsto (fun k => β (t k)) Filter.atTop (nhds 1) :=
    (NNReal.tendsto_coe).1 hβ_tendstoR
  have ht0 : Filter.Tendsto t Filter.atTop (nhds 0) := hβ_zero t hβ_tendsto
  have hD0 : Filter.Tendsto (fun k => dist (y (m k)) (y (n k)))
      Filter.atTop (nhds 0) := by
    have hcoe : Filter.Tendsto (fun k => (t k : ℝ)) Filter.atTop (nhds 0) :=
      (NNReal.tendsto_coe).2 ht0
    have heq : (fun k => (t k : ℝ)) =ᶠ[Filter.atTop]
        fun k => dist (y (m k)) (y (n k)) := by
      refine Filter.Eventually.of_forall ?_
      intro k
      change (nndist (y (m k)) (y (n k)) : ℝ) = dist (y (m k)) (y (n k))
      rw [dist_nndist]
    exact Filter.Tendsto.congr' heq hcoe
  have hε0 : ε = 0 := tendsto_nhds_unique hD hD0
  exact (ne_of_gt hε) hε0

/- verified submission -/
theorem common_coincidence_point_of_ordered_metric_contraction
    {X : Type*} [Nonempty X] [PartialOrder X] [MetricSpace X] [CompleteSpace X]
    (f g H : X → X) (β : NNReal → NNReal)
    (hregular : ∀ (z : ℕ → X) (a : X), Monotone z →
      Filter.Tendsto z Filter.atTop (nhds a) → ∀ n, z n ≤ a)
    (hf_range : Set.range f ⊆ Set.range H)
    (hg_range : Set.range g ⊆ Set.range H)
    (hH_closed : IsClosed (Set.range H))
    (hfg_inc : ∀ x y, H y = f x → f x ≤ g y)
    (hgf_inc : ∀ x y, H y = g x → g x ≤ f y)
    (hβ_lt_one : ∀ t, β t < 1)
    (hβ_zero : ∀ t : ℕ → NNReal,
      Filter.Tendsto (fun n => β (t n)) Filter.atTop (nhds 1) →
        Filter.Tendsto t Filter.atTop (nhds 0))
    (hcontract : ∀ x y, (H x ≤ H y ∨ H y ≤ H x) →
      nndist (f x) (g y) ≤ β (nndist (H x) (H y)) * nndist (H x) (H y)) :
    ∃ u, f u = g u ∧ g u = H u := by
  classical
  have hf_eq_g : ∀ x, f x = g x := by
    intro x
    have hle := hcontract x x (Or.inl le_rfl)
    rw [nndist_self, mul_zero] at hle
    have hzero : nndist (f x) (g x) = 0 := le_antisymm hle (zero_le _)
    exact nndist_eq_zero.mp hzero
  obtain ⟨a₀⟩ := (inferInstance : Nonempty X)
  let next : ∀ x : X, {y : X // H y = f x} := fun x =>
    ⟨Classical.choose (hf_range ⟨x, rfl⟩), Classical.choose_spec (hf_range ⟨x, rfl⟩)⟩
  let a : ℕ → X := fun n => Nat.rec a₀ (fun _ x => (next x).1) n
  have ha : ∀ n, H (a (n + 1)) = f (a n) := by
    intro n
    exact (next (a n)).2
  let y : ℕ → X := fun n => H (a (n + 1))
  have hy_succ : ∀ n, y n ≤ y (n + 1) := by
    intro n
    have h := hfg_inc (a n) (a (n + 1)) (ha n)
    change f (a n) ≤ g (a (n + 1)) at h
    rw [← hf_eq_g (a (n + 1))] at h
    change H (a (n + 1)) ≤ H (a (n + 2))
    rw [ha n, ha (n + 1)]
    exact h
  have hmono : Monotone y := monotone_nat_of_le_succ hy_succ
  have hcross : ∀ m n : ℕ, m < n →
      nndist (y (m + 1)) (y (n + 1)) ≤
        β (nndist (y m) (y n)) * nndist (y m) (y n) := by
    intro m n hmn
    have hcomp : H (a (m + 1)) ≤ H (a (n + 1)) := hmono hmn.le
    have hc := hcontract (a (m + 1)) (a (n + 1)) (Or.inl hcomp)
    change nndist (f (a (m + 1))) (g (a (n + 1))) ≤
      β (nndist (y m) (y n)) * nndist (y m) (y n) at hc
    rw [← ha (m + 1), ← hf_eq_g (a (n + 1)), ← ha (n + 1)] at hc
    exact hc
  have hycauchy : CauchySeq y :=
    cauchySeq_of_ordered_beta_contraction hβ_lt_one hβ_zero hmono hcross
  let L : X := Filter.atTop.limUnder y
  have hyL : Filter.Tendsto y Filter.atTop (nhds L) :=
    hycauchy.tendsto_limUnder
  have hy_le_L : ∀ n, y n ≤ L := hregular y L hmono hyL
  have hy_mem : ∀ n, y n ∈ Set.range H := fun n => ⟨a (n + 1), rfl⟩
  have hL_mem : L ∈ Set.range H :=
    hH_closed.mem_of_tendsto hyL (Filter.Eventually.of_forall hy_mem)
  obtain ⟨u, huH⟩ := hL_mem
  have hbound : ∀ n, nndist (y (n + 1)) (f u) ≤ nndist (y n) L := by
    intro n
    have hcomp : H (a (n + 1)) ≤ H u := by
      change y n ≤ H u
      rw [huH]
      exact hy_le_L n
    have hc := hcontract (a (n + 1)) u (Or.inl hcomp)
    change nndist (f (a (n + 1))) (g u) ≤
      β (nndist (y n) (H u)) * nndist (y n) (H u) at hc
    rw [← ha (n + 1), ← hf_eq_g u, huH] at hc
    calc
      nndist (y (n + 1)) (f u) ≤ β (nndist (y n) L) * nndist (y n) L := hc
      _ ≤ 1 * nndist (y n) L := mul_le_mul_right' (le_of_lt (hβ_lt_one _)) _
      _ = nndist (y n) L := one_mul _
  have hdL : Filter.Tendsto (fun n => nndist (y n) L) Filter.atTop (nhds 0) := by
    have hconst : Filter.Tendsto (fun _ : ℕ => L) Filter.atTop (nhds L) :=
      tendsto_const_nhds
    have h := hyL.nndist hconst
    simpa using h
  have htarget_nn : Filter.Tendsto (fun n => nndist (y (n + 1)) (f u))
      Filter.atTop (nhds 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdL
      (fun n => zero_le _) hbound
  have htarget_dist : Filter.Tendsto (fun n => dist (y (n + 1)) (f u))
      Filter.atTop (nhds 0) := by
    have hcoe : Filter.Tendsto (fun n => (nndist (y (n + 1)) (f u) : ℝ))
        Filter.atTop (nhds 0) := (NNReal.tendsto_coe).2 htarget_nn
    have heq : (fun n => (nndist (y (n + 1)) (f u) : ℝ)) =ᶠ[Filter.atTop]
        fun n => dist (y (n + 1)) (f u) := by
      refine Filter.Eventually.of_forall ?_
      intro n
      exact (dist_nndist _ _).symm
    exact Filter.Tendsto.congr' heq hcoe
  have hyshift_fu : Filter.Tendsto (fun n => y (n + 1)) Filter.atTop (nhds (f u)) :=
    tendsto_iff_dist_tendsto_zero.2 htarget_dist
  have hyshift_L : Filter.Tendsto (fun n => y (n + 1)) Filter.atTop (nhds L) :=
    hyL.comp (Filter.tendsto_add_atTop_nat 1)
  have hL_eq_fu : L = f u := tendsto_nhds_unique hyshift_L hyshift_fu
  have hfu_eq_Hu : f u = H u := by
    rw [← hL_eq_fu, huH]
  exact ⟨u, hf_eq_g u, by
    rw [← hf_eq_g u]
    exact hfu_eq_Hu⟩

end Rollout_p1362_common_coincidence_point_of_ordered_metric

namespace Rollout_p1371_decktransformation_eq_id_of_fixed_point

/- verified submission -/
theorem deckTransformation_eq_id_of_fixed_point
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace E]
    (p : E → B) (hp : Continuous p)
    (arc_lifting : ∀ (f : C(Set.Icc (0 : ℝ) 1, B))
      (t₀ : Set.Icc (0 : ℝ) 1) (e₀ : E), p e₀ = f t₀ →
        ∃! g : C(Set.Icc (0 : ℝ) 1, E),
          (∀ t, p (g t) = f t) ∧ g t₀ = e₀)
    (h : E ≃ₜ E) (hdeck : p ∘ h = p)
    {e : E} (he : h e = e) :
    h = Homeomorph.refl E := by
  apply Homeomorph.ext
  intro x
  let γ : Path e x := PathConnectedSpace.somePath e x
  let f : C(Set.Icc (0 : ℝ) 1, B) := ⟨fun t => p (γ t), hp.comp γ.continuous⟩
  let g₁ : C(Set.Icc (0 : ℝ) 1, E) := ⟨fun t => γ t, γ.continuous⟩
  let g₂ : C(Set.Icc (0 : ℝ) 1, E) := ⟨fun t => h (γ t), h.continuous.comp γ.continuous⟩
  have hbase : p e = f 0 := by
    exact (congrArg p γ.source).symm
  have huniq := arc_lifting f 0 e hbase
  have hg₁ : (∀ t, p (g₁ t) = f t) ∧ g₁ 0 = e := by
    constructor
    · intro t
      rfl
    · exact γ.source
  have hg₂ : (∀ t, p (g₂ t) = f t) ∧ g₂ 0 = e := by
    constructor
    · intro t
      exact congrFun hdeck (γ t)
    · calc
        g₂ 0 = h (γ 0) := rfl
        _ = h e := congrArg h γ.source
        _ = e := he
  have hg : g₁ = g₂ := huniq.unique hg₁ hg₂
  have hx : γ 1 = h (γ 1) := congrArg (fun g : C(Set.Icc (0 : ℝ) 1, E) => g 1) hg
  calc
    h x = h (γ 1) := by rw [γ.target]
    _ = γ 1 := hx.symm
    _ = x := γ.target

end Rollout_p1371_decktransformation_eq_id_of_fixed_point

namespace Rollout_p0256_marking_equivalence

/- accepted add_to_file helper 1 -/

lemma exists_perm_comp_eq_of_injective {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f g : α → β) (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ σ : Equiv.Perm β, σ ∘ f = g := by
  classical
  let p : β → Prop := fun x => ∃ a, f a = x
  let q : β → Prop := fun x => ∃ a, g a = x
  let ef : α ≃ {x // p x} := Function.Embedding.toEquivRange ⟨f, hf⟩
  let eg : α ≃ {x // q x} := Function.Embedding.toEquivRange ⟨g, hg⟩
  let es : {x // p x} ≃ {x // q x} := ef.symm.trans eg
  have hfcard : Fintype.card {x : β // p x} = Fintype.card α :=
    Fintype.card_congr ef.symm
  have hgcard : Fintype.card {x : β // q x} = Fintype.card α :=
    Fintype.card_congr eg.symm
  have hcard : Fintype.card {x // ¬p x} = Fintype.card {x // ¬q x} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hfcard, hgcard]
  let ec : {x // ¬p x} ≃ {x // ¬q x} := Fintype.equivOfCardEq hcard
  let esum : {x // p x} ⊕ {x // ¬p x} ≃ {x // q x} ⊕ {x // ¬q x} := es.sumCongr ec
  let σ : Equiv.Perm β :=
    (Equiv.sumCompl p).symm.trans (esum.trans (Equiv.sumCompl q))
  use σ
  funext a
  have hfa : (⟨f a, ⟨a, rfl⟩⟩ : {x // p x}) = ef a := by
    apply Subtype.ext
    rfl
  change (Equiv.sumCompl q) (esum ((Equiv.sumCompl p).symm (f a))) = g a
  rw [Equiv.sumCompl_symm_apply_of_pos (p := p) (⟨a, rfl⟩ : p (f a))]
  rw [hfa]
  simp [esum, es]
  rfl

/- accepted add_to_file helper 2 -/
namespace MarkingEquivalence

abbrev MVertex (d k : ℕ) := Fin d ⊕ Fin k
abbrev MEdge (n d k : ℕ) :=
  ({p : Fin d × Fin d // p.1 < p.2} × Fin n) ⊕ (Fin d × Fin k)

def mends {n d k : ℕ} : MEdge n d k → Sym2 (MVertex d k)
  | Sum.inl x => Sym2.mk (Sum.inl x.1.val.1) (Sum.inl x.1.val.2)
  | Sum.inr x => Sym2.mk (Sum.inl x.1) (Sum.inr x.2)

abbrev MMarking (n d k r : ℕ) := {μ : Fin r → MEdge n d k // Function.Injective μ}

def unmarkedRel {n d k r : ℕ} (μ : Fin r → MEdge n d k) : MVertex d k → MVertex d k → Prop :=
  fun u v => ∃ e : MEdge n d k, e ∉ Set.range μ ∧ mends e = Sym2.mk u v

def unmarkedGraph {n d k r : ℕ} (μ : Fin r → MEdge n d k) : SimpleGraph (MVertex d k) :=
  SimpleGraph.fromRel (unmarkedRel μ)

def mirreducible {n d k r : ℕ} (μ : MMarking n d k r) : Prop :=
  (unmarkedGraph μ.1).Connected

def applyPermMarking {n d k r : ℕ} (σ : Equiv.Perm (MEdge n d k)) (μ : MMarking n d k r) :
    MMarking n d k r :=
  ⟨fun i => σ (μ.1 i), σ.injective.comp μ.2⟩

def applySwapMarking {n d k r : ℕ} (a b : MEdge n d k) (μ : MMarking n d k r) :
    MMarking n d k r :=
  applyPermMarking (Equiv.swap a b) μ

end MarkingEquivalence

/- accepted add_to_file helper 3 -/
namespace MarkingEquivalence

def MDMove {n d k r : ℕ} : MMarking n d k r → MMarking n d k r → Prop := fun μ ν =>
  ∃ a b : MEdge n d k, a ≠ b ∧ mends a = mends b ∧
    ν.1 = fun i => Equiv.swap a b (μ.1 i)

def MTMove {n d k r : ℕ} : MMarking n d k r → MMarking n d k r → Prop := fun μ ν =>
  ∃ D D' D'' : MVertex d k,
    D ≠ D' ∧ D ≠ D'' ∧ D' ≠ D'' ∧
    ∃ q q' q'' : MEdge n d k,
      mends q = Sym2.mk D' D'' ∧
      mends q' = Sym2.mk D D'' ∧
      mends q'' = Sym2.mk D D' ∧
      ν.1 = if q' ∈ Set.range μ.1 then μ.1
        else fun i => Equiv.swap q q'' (μ.1 i)

def MMove {n d k r : ℕ} (μ ν : MMarking n d k r) : Prop :=
  MDMove μ ν ∨ MTMove μ ν

lemma MDMove.move {n d k r : ℕ} {μ ν : MMarking n d k r} (h : MDMove μ ν) : MMove μ ν :=
  Or.inl h

lemma MTMove.move {n d k r : ℕ} {μ ν : MMarking n d k r} (h : MTMove μ ν) : MMove μ ν :=
  Or.inr h

end MarkingEquivalence

/- accepted add_to_file helper 4 -/
namespace MarkingEquivalence

lemma dmove_swap {n d k r : ℕ} {a b : MEdge n d k} (hab : a ≠ b)
    (hends : mends a = mends b) (μ : MMarking n d k r) :
    MDMove μ (applySwapMarking a b μ) := by
  exact ⟨a, b, hab, hends, rfl⟩

lemma tmove_swap {n d k r : ℕ} (μ : MMarking n d k r) {D D' D'' : MVertex d k}
    (h12 : D ≠ D') (h13 : D ≠ D'') (h23 : D' ≠ D'')
    {q q' q'' : MEdge n d k}
    (hq : mends q = Sym2.mk D' D'')
    (hq' : mends q' = Sym2.mk D D'')
    (hq'' : mends q'' = Sym2.mk D D')
    (hun : q' ∉ Set.range μ.1) :
    MTMove μ (applySwapMarking q q'' μ) := by
  refine ⟨D, D', D'', h12, h13, h23, q, q', q'', hq, hq', hq'', ?_⟩
  simp [applySwapMarking, applyPermMarking, hun]

end MarkingEquivalence

/- accepted add_to_file helper 5 -/
namespace MarkingEquivalence

lemma mem_range_perm_comp {β ι : Type*} [DecidableEq β] (σ : Equiv.Perm β)
    (f : ι → β) (b : β) :
    b ∈ Set.range (fun i => σ (f i)) ↔ σ.symm b ∈ Set.range f := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    apply σ.injective
    simpa using hi
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    change σ (f i) = b
    rw [hi]
    simp

lemma mends_swap_parallel_apply {n d k : ℕ} {a b : MEdge n d k}
    (hends : mends a = mends b) (e : MEdge n d k) :
    mends (Equiv.swap a b e) = mends e := by
  classical
  by_cases ha : e = a
  · subst ha
    simp [hends]
  · by_cases hb : e = b
    · subst hb
      simp [hends]
    · simp [Equiv.swap_apply_of_ne_of_ne ha hb]

lemma unmarkedRel_swap_parallel {n d k r : ℕ} (μ : Fin r → MEdge n d k)
    {a b : MEdge n d k} (hends : mends a = mends b) (u v : MVertex d k) :
    unmarkedRel (fun i => Equiv.swap a b (μ i)) u v ↔ unmarkedRel μ u v := by
  classical
  constructor
  · rintro ⟨e, he, hend⟩
    have he' : Equiv.swap a b e ∉ Set.range μ := by
      have hiff := mem_range_perm_comp (σ := Equiv.swap a b) (f := μ) (b := e)
      exact (not_congr hiff).mp he
    refine ⟨Equiv.swap a b e, he', ?_⟩
    rw [mends_swap_parallel_apply hends]
    exact hend
  · rintro ⟨e, he, hend⟩
    have he' : Equiv.swap a b e ∉ Set.range (fun i => Equiv.swap a b (μ i)) := by
      have hiff := mem_range_perm_comp (σ := Equiv.swap a b) (f := μ) (b := Equiv.swap a b e)
      have hbase : (Equiv.swap a b).symm (Equiv.swap a b e) ∉ Set.range μ := by simpa using he
      exact (not_congr hiff).mpr hbase
    refine ⟨Equiv.swap a b e, he', ?_⟩
    rw [mends_swap_parallel_apply hends]
    exact hend

lemma dmove_preserves_irreducible {n d k r : ℕ} {μ : MMarking n d k r}
    {a b : MEdge n d k} (hends : mends a = mends b)
    (hμ : mirreducible μ) : mirreducible (applySwapMarking a b μ) := by
  unfold mirreducible unmarkedGraph applySwapMarking applyPermMarking
  have hrel : unmarkedRel (fun i => (Equiv.swap a b) (μ.1 i)) = unmarkedRel μ.1 := by
    funext u v
    exact propext (unmarkedRel_swap_parallel μ.1 hends u v)
  rw [hrel]
  exact hμ

end MarkingEquivalence

/- accepted add_to_file helper 6 -/
namespace MarkingEquivalence

lemma old_adj_reachable_swap_triangle {n d k r : ℕ} (μ : MMarking n d k r)
    {D D' D'' : MVertex d k}
    (h12 : D ≠ D') (h13 : D ≠ D'') (h23 : D' ≠ D'')
    {q q' q'' : MEdge n d k}
    (hq : mends q = Sym2.mk D' D'')
    (hq' : mends q' = Sym2.mk D D'')
    (hq'' : mends q'' = Sym2.mk D D')
    (hq'un : q' ∉ Set.range μ.1)
    {u v : MVertex d k}
    (hadj : (unmarkedGraph μ.1).Adj u v) :
    (unmarkedGraph (applySwapMarking q q'' μ).1).Reachable u v := by
  classical
  let σ : Equiv.Perm (MEdge n d k) := Equiv.swap q q''
  have hqq' : q ≠ q' := by
    intro h
    rw [h, hq'] at hq
    rw [Sym2.eq_iff] at hq
    rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h12 h1
    · exact h13 h1
  have hqq'' : q ≠ q'' := by
    intro h
    rw [h, hq''] at hq
    rw [Sym2.eq_iff] at hq
    rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h12 h1
    · exact h13 h1
  have hq'q'' : q' ≠ q'' := by
    intro h
    rw [h, hq''] at hq'
    rw [Sym2.eq_iff] at hq'
    rcases hq' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h23 h2
    · exact h13 h1
  have adj_of {x y : MVertex d k} {e : MEdge n d k}
      (hxy : x ≠ y) (hunm : e ∉ Set.range (fun i => σ (μ.1 i)))
      (hends : mends e = Sym2.mk x y) :
      (unmarkedGraph (applySwapMarking q q'' μ).1).Adj x y := by
    unfold unmarkedGraph applySwapMarking applyPermMarking
    rw [SimpleGraph.fromRel_adj]
    exact ⟨hxy, Or.inl ⟨e, hunm, by simpa [σ] using hends⟩⟩
  have hq'new : q' ∉ Set.range (fun i => σ (μ.1 i)) := by
    have hiff := mem_range_perm_comp (σ := σ) (f := μ.1) (b := q')
    have hfix : σ.symm q' = q' := by
      simp [σ, Equiv.swap_apply_of_ne_of_ne hqq'.symm hq'q'']
    intro hmem
    exact hq'un (by simpa [hfix] using hiff.mp hmem)
  rw [unmarkedGraph, SimpleGraph.fromRel_adj] at hadj
  rcases hadj with ⟨huv, hor⟩
  rcases hor with hrel | hrel
  · rcases hrel with ⟨e, he, hend⟩
    by_cases heq : e = q
    · subst e
      by_cases hq''old : q'' ∈ Set.range μ.1
      · have hq''new : q'' ∉ Set.range (fun i => σ (μ.1 i)) := by
          have hiff := mem_range_perm_comp (σ := σ) (f := μ.1) (b := q'')
          have hsymm : σ.symm q'' = q := by simp [σ]
          intro hmem
          exact he (by simpa [hsymm] using hiff.mp hmem)
        have hreach : (unmarkedGraph (applySwapMarking q q'' μ).1).Reachable D' D'' :=
          ((adj_of h12 hq''new hq'').symm.reachable).trans
            (adj_of h13 hq'new hq').reachable
        have hpair : Sym2.mk u v = Sym2.mk D' D'' := by rw [← hend, hq]
        rcases Sym2.eq_iff.mp hpair with ⟨hu, hv⟩ | ⟨hu, hv⟩
        · subst u; subst v; exact hreach
        · subst u; subst v; exact hreach.symm
      · have hqnew : q ∉ Set.range (fun i => σ (μ.1 i)) := by
          have hiff := mem_range_perm_comp (σ := σ) (f := μ.1) (b := q)
          have hsymm : σ.symm q = q'' := by simp [σ]
          intro hmem
          exact hq''old (by simpa [hsymm] using hiff.mp hmem)
        exact (adj_of huv hqnew (by simpa [σ] using hend)).reachable
    · by_cases heq'' : e = q''
      · subst e
        by_cases hqold : q ∈ Set.range μ.1
        · have hqnew : q ∉ Set.range (fun i => σ (μ.1 i)) := by
            have hiff := mem_range_perm_comp (σ := σ) (f := μ.1) (b := q)
            have hsymm : σ.symm q = q'' := by simp [σ]
            intro hmem
            exact he (by simpa [hsymm] using hiff.mp hmem)
          have hreach : (unmarkedGraph (applySwapMarking q q'' μ).1).Reachable D D' :=
            (adj_of h13 hq'new hq').reachable.trans
              ((adj_of h23 hqnew hq).symm.reachable)
          have hpair : Sym2.mk u v = Sym2.mk D D' := by rw [← hend, hq'']
          rcases Sym2.eq_iff.mp hpair with ⟨hu, hv⟩ | ⟨hu, hv⟩
          · subst u; subst v; exact hreach
          · subst u; subst v; exact hreach.symm
        · have hq''new : q'' ∉ Set.range (fun i => σ (μ.1 i)) := by
            have hiff := mem_range_perm_comp (σ := σ) (f := μ.1) (b := q'')
            have hsymm : σ.symm q'' = q := by simp [σ]
            intro hmem
            exact hqold (by simpa [hsymm] using hiff.mp hmem)
          exact (adj_of huv hq''new (by simpa [σ] using hend)).reachable
      · have henew : e ∉ Set.range (fun i => σ (μ.1 i)) := by
          have hiff := mem_range_perm_comp (σ := σ) (f := μ.1) (b := e)
          have hfix : σ.symm e = e := by
            simp [σ, Equiv.swap_apply_of_ne_of_ne heq heq'']
          intro hmem
          exact he (by simpa [hfix] using hiff.mp hmem)
        exact (adj_of huv henew (by simpa [σ] using hend)).reachable
  · rcases hrel with ⟨e, he, hend⟩
    have hend' : mends e = Sym2.mk u v := by
      calc
        mends e = Sym2.mk v u := hend
        _ = Sym2.mk u v := Sym2.eq_swap
    by_cases heq : e = q
    · subst e
      by_cases hq''old : q'' ∈ Set.range μ.1
      · have hq''new : q'' ∉ Set.range (fun i => σ (μ.1 i)) := by
          have hiff := mem_range_perm_comp (σ := σ) (f := μ.1) (b := q'')
          have hsymm : σ.symm q'' = q := by simp [σ]
          intro hmem
          exact he (by simpa [hsymm] using hiff.mp hmem)
        have hreach : (unmarkedGraph (applySwapMarking q q'' μ).1).Reachable D' D'' :=
          ((adj_of h12 hq''new hq'').symm.reachable).trans
            (adj_of h13 hq'new hq').reachable
        have hpair : Sym2.mk u v = Sym2.mk D' D'' := by rw [← hend', hq]
        rcases Sym2.eq_iff.mp hpair with ⟨hu, hv⟩ | ⟨hu, hv⟩
        · subst u; subst v; exact hreach
        · subst u; subst v; exact hreach.symm
      · have hqnew : q ∉ Set.range (fun i => σ (μ.1 i)) := by
          have hiff := mem_range_perm_comp (σ := σ) (f := μ.1) (b := q)
          have hsymm : σ.symm q = q'' := by simp [σ]
          intro hmem
          exact hq''old (by simpa [hsymm] using hiff.mp hmem)
        exact (adj_of huv hqnew (by simpa [σ] using hend')).reachable
    · by_cases heq'' : e = q''
      · subst e
        by_cases hqold : q ∈ Set.range μ.1
        · have hqnew : q ∉ Set.range (fun i => σ (μ.1 i)) := by
            have hiff := mem_range_perm_comp (σ := σ) (f := μ.1) (b := q)
            have hsymm : σ.symm q = q'' := by simp [σ]
            intro hmem
            exact he (by simpa [hsymm] using hiff.mp hmem)
          have hreach : (unmarkedGraph (applySwapMarking q q'' μ).1).Reachable D D' :=
            (adj_of h13 hq'new hq').reachable.trans
              ((adj_of h23 hqnew hq).symm.reachable)
          have hpair : Sym2.mk u v = Sym2.mk D D' := by rw [← hend', hq'']
          rcases Sym2.eq_iff.mp hpair with ⟨hu, hv⟩ | ⟨hu, hv⟩
          · subst u; subst v; exact hreach
          · subst u; subst v; exact hreach.symm
        · have hq''new : q'' ∉ Set.range (fun i => σ (μ.1 i)) := by
            have hiff := mem_range_perm_comp (σ := σ) (f := μ.1) (b := q'')
            have hsymm : σ.symm q'' = q := by simp [σ]
            intro hmem
            exact hqold (by simpa [hsymm] using hiff.mp hmem)
          exact (adj_of huv hq''new (by simpa [σ] using hend')).reachable
      · have henew : e ∉ Set.range (fun i => σ (μ.1 i)) := by
          have hiff := mem_range_perm_comp (σ := σ) (f := μ.1) (b := e)
          have hfix : σ.symm e = e := by
            simp [σ, Equiv.swap_apply_of_ne_of_ne heq heq'']
          intro hmem
          exact he (by simpa [hfix] using hiff.mp hmem)
        exact (adj_of huv henew (by simpa [σ] using hend')).reachable

end MarkingEquivalence

/- accepted add_to_file helper 7 -/
namespace MarkingEquivalence

lemma tmove_preserves_irreducible {n d k r : ℕ} (μ : MMarking n d k r)
    {D D' D'' : MVertex d k}
    (h12 : D ≠ D') (h13 : D ≠ D'') (h23 : D' ≠ D'')
    {q q' q'' : MEdge n d k}
    (hq : mends q = Sym2.mk D' D'')
    (hq' : mends q' = Sym2.mk D D'')
    (hq'' : mends q'' = Sym2.mk D D')
    (hq'un : q' ∉ Set.range μ.1)
    (hμ : mirreducible μ) :
    mirreducible (applySwapMarking q q'' μ) := by
  unfold mirreducible
  haveI : Nonempty (MVertex d k) := hμ.nonempty
  refine SimpleGraph.Connected.mk ?_
  intro u v
  have hold : (unmarkedGraph μ.1).Reachable u v := hμ.preconnected u v
  rw [SimpleGraph.reachable_eq_reflTransGen] at hold
  induction hold with
  | refl => exact SimpleGraph.Reachable.refl u
  | tail hrt hadj ih =>
      exact ih.trans (old_adj_reachable_swap_triangle μ h12 h13 h23 hq hq' hq'' hq'un hadj)

end MarkingEquivalence

/- accepted add_to_file helper 8 -/
namespace MarkingEquivalence

def root {d k : ℕ} (hd : 0 < d) : MVertex d k :=
  Sum.inl (⟨0, hd⟩ : Fin d)

def starEdge {n d k : ℕ} (hn : 0 < n) (hd : 0 < d)
    (x : MVertex d k) (hx : x ≠ root hd) : MEdge n d k :=
  match x with
  | Sum.inl i =>
      haveI : NeZero d := ⟨Nat.ne_of_gt hd⟩
      have hine : (⟨0, hd⟩ : Fin d) ≠ i := by
        intro h
        apply hx
        cases h
        rfl
      let p : {p : Fin d × Fin d // p.1 < p.2} :=
        ⟨Prod.mk (⟨0, hd⟩ : Fin d) i, lt_of_le_of_ne (Fin.zero_le i) hine⟩
      Sum.inl (p, ⟨0, hn⟩)
  | Sum.inr j => Sum.inr (⟨0, hd⟩, j)

lemma mends_starEdge {n d k : ℕ} (hn : 0 < n) (hd : 0 < d)
    (x : MVertex d k) (hx : x ≠ root hd) :
    mends (starEdge hn hd x hx) = Sym2.mk (root hd) x := by
  cases x with
  | inl i =>
      unfold starEdge mends root
      simp
  | inr j =>
      unfold starEdge mends root
      simp

lemma starEdge_eq_of_mends_eq {n d k : ℕ} (hn : 0 < n) (hd : 0 < d)
    {x y : MVertex d k} (hx : x ≠ root hd) (hy : y ≠ root hd)
    (h : starEdge hn hd x hx = starEdge hn hd y hy) : x = y := by
  have he := congrArg mends h
  rw [mends_starEdge hn hd x hx, mends_starEdge hn hd y hy] at he
  rw [Sym2.eq_iff] at he
  rcases he with ⟨hr, hxy⟩ | ⟨hry, hxr⟩
  · exact hxy
  · exact False.elim (hy hry.symm)

def IsCanonicalStarEdge {n d k : ℕ} (hn : 0 < n) (hd : 0 < d) : MEdge n d k → Prop :=
  fun e => ∃ (x : MVertex d k) (hx : x ≠ root hd), e = starEdge hn hd x hx

abbrev PosEdge {n d k : ℕ} (hn : 0 < n) (hd : 0 < d) :=
  {e : MEdge n d k // ¬ IsCanonicalStarEdge hn hd e}

end MarkingEquivalence

/- accepted add_to_file helper 9 -/
namespace MarkingEquivalence

lemma exists_cross_of_reachable {V : Type*} [DecidableEq V]
    {r : V → V → Prop} {S : Finset V} {a b : V}
    (h : Relation.ReflTransGen r a b) (ha : a ∉ S) (hb : b ∈ S) :
    ∃ x ∉ S, ∃ y ∈ S, r x y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      exact False.elim (ha hb)
  | head hac hcb ih =>
      rename_i a c
      by_cases hc : c ∈ S
      · exact ⟨a, ha, c, hc, hac⟩
      · exact ih hc

end MarkingEquivalence

/- accepted add_to_file helper 10 -/
namespace MarkingEquivalence

lemma notMem_range_applySwap_preimage {n d k r : ℕ} (μ : MMarking n d k r)
    {a b target source : MEdge n d k}
    (hpre : Equiv.swap a b target = source)
    (hs : source ∉ Set.range μ.1) :
    target ∉ Set.range (applySwapMarking a b μ).1 := by
  classical
  intro hmem
  have hiff := mem_range_perm_comp (σ := Equiv.swap a b) (f := μ.1) (b := target)
  have hsrc : (Equiv.swap a b).symm target ∈ Set.range μ.1 := hiff.mp hmem
  exact hs (by simpa [hpre] using hsrc)

lemma notMem_range_applySwap_fixed {n d k r : ℕ} (μ : MMarking n d k r)
    {a b e : MEdge n d k}
    (hfix : Equiv.swap a b e = e)
    (he : e ∉ Set.range μ.1) :
    e ∉ Set.range (applySwapMarking a b μ).1 := by
  classical
  intro hmem
  have hiff := mem_range_perm_comp (σ := Equiv.swap a b) (f := μ.1) (b := e)
  have hsrc : (Equiv.swap a b).symm e ∈ Set.range μ.1 := hiff.mp hmem
  exact he (by simpa [hfix] using hsrc)

end MarkingEquivalence

/- accepted add_to_file helper 11 -/
namespace MarkingEquivalence

lemma exists_unmarked_edge_of_adj {n d k r : ℕ} {μ : Fin r → MEdge n d k}
    {a b : MVertex d k} (hadj : (unmarkedGraph μ).Adj a b) :
    ∃ e : MEdge n d k, e ∉ Set.range μ ∧ mends e = Sym2.mk a b := by
  rw [unmarkedGraph, SimpleGraph.fromRel_adj] at hadj
  rcases hadj with ⟨hab, hor⟩
  rcases hor with hrel | hrel
  · exact hrel
  · rcases hrel with ⟨e, he, hend⟩
    exact ⟨e, he, hend.trans Sym2.eq_swap⟩

end MarkingEquivalence

/- accepted add_to_file helper 12 -/
namespace MarkingEquivalence

lemma starify_one_step {n d k r : ℕ} (hn : 0 < n) (hd : 0 < d)
    (μ : MMarking n d k r) (hμ : mirreducible μ)
    (S : Finset (MVertex d k)) (hroot : root hd ∈ S)
    (hstar : ∀ x ∈ S, ∀ hx : x ≠ root hd,
      starEdge hn hd x hx ∉ Set.range μ.1)
    {a b : MVertex d k} (ha : a ∉ S) (hb : b ∈ S)
    (hadj : (unmarkedGraph μ.1).Adj a b) :
    ∃ μ' : MMarking n d k r,
      Relation.ReflTransGen MMove μ μ' ∧ mirreducible μ' ∧
      ∀ x ∈ insert a S, ∀ hx : x ≠ root hd,
        starEdge hn hd x hx ∉ Set.range μ'.1 := by
  classical
  obtain ⟨e, he, hend⟩ := exists_unmarked_edge_of_adj hadj
  have haR : a ≠ root hd := by
    intro har
    exact ha (har ▸ hroot)
  by_cases hsa : starEdge hn hd a haR ∈ Set.range μ.1
  · by_cases hbR : b = root hd
    · subst b
      let sa := starEdge hn hd a haR
      have hendsym : mends e = Sym2.mk (root hd) a := hend.trans Sym2.eq_swap
      have hends : mends sa = mends e := by
        rw [mends_starEdge hn hd a haR, hendsym]
      have hsane : sa ≠ e := by
        intro h
        exact he (h ▸ hsa)
      refine ⟨applySwapMarking sa e μ, Relation.ReflTransGen.single ?_, ?_, ?_⟩
      · exact MDMove.move (dmove_swap hsane hends μ)
      · exact dmove_preserves_irreducible hends hμ
      · intro x hxS hxR
        rw [Finset.mem_insert] at hxS
        rcases hxS with rfl | hxS
        · apply notMem_range_applySwap_preimage μ
            (a := sa) (b := e) (target := sa) (source := e)
          · simp
          · exact he
        · have hxa : x ≠ a := by
            intro hxa
            exact ha (hxa ▸ hxS)
          have hfix : Equiv.swap sa e (starEdge hn hd x hxR) = starEdge hn hd x hxR := by
            apply Equiv.swap_apply_of_ne_of_ne
            · intro hsx
              exact hxa (starEdge_eq_of_mends_eq hn hd hxR haR hsx)
            · intro hxe
              have heq := congrArg mends hxe
              rw [mends_starEdge hn hd x hxR, hendsym] at heq
              rw [Sym2.eq_iff] at heq
              rcases heq with ⟨hroot, hxa'⟩ | ⟨hroota, hxroot⟩
              · exact hxa hxa'
              · exact haR hroota.symm
          apply notMem_range_applySwap_fixed μ hfix
          exact hstar x hxS hxR
    · let sa := starEdge hn hd a haR
      let sb := starEdge hn hd b hbR
      have hsb : sb ∉ Set.range μ.1 := hstar b hb hbR
      have hRb : root hd ≠ b := fun h => hbR h.symm
      have hRa : root hd ≠ a := fun h => haR h.symm
      have hab' : a ≠ b := by
        have h := hadj
        rw [unmarkedGraph, SimpleGraph.fromRel_adj] at h
        exact h.1
      have hT : MTMove μ (applySwapMarking e sa μ) :=
        tmove_swap μ hRa hRb hab'
          (q := e) (q' := sb) (q'' := sa) hend
          (mends_starEdge hn hd b hbR) (mends_starEdge hn hd a haR) hsb
      refine ⟨applySwapMarking e sa μ, Relation.ReflTransGen.single ?_, ?_, ?_⟩
      · exact MTMove.move hT
      · exact tmove_preserves_irreducible μ hRa hRb hab' hend
          (mends_starEdge hn hd b hbR) (mends_starEdge hn hd a haR) hsb hμ
      · intro x hxS hxR
        rw [Finset.mem_insert] at hxS
        rcases hxS with rfl | hxS
        · apply notMem_range_applySwap_preimage μ
            (a := e) (b := sa) (target := sa) (source := e)
          · simp
          · exact he
        · have hxa : x ≠ a := by
            intro hxa
            exact ha (hxa ▸ hxS)
          have hfix : Equiv.swap e sa (starEdge hn hd x hxR) = starEdge hn hd x hxR := by
            apply Equiv.swap_apply_of_ne_of_ne
            · intro hxe
              have heq := congrArg mends hxe
              rw [mends_starEdge hn hd x hxR, hend] at heq
              rw [Sym2.eq_iff] at heq
              rcases heq with ⟨hroota, hxb⟩ | ⟨hrootb, hxa'⟩
              · exact hRa hroota
              · exact hRb hrootb
            · intro hxsa
              exact hxa (starEdge_eq_of_mends_eq hn hd hxR haR hxsa)
          apply notMem_range_applySwap_fixed μ hfix
          exact hstar x hxS hxR
  · refine ⟨μ, Relation.ReflTransGen.refl, hμ, ?_⟩
    intro x hxS hxR
    rw [Finset.mem_insert] at hxS
    rcases hxS with rfl | hxS
    · exact hsa
    · exact hstar x hxS hxR

end MarkingEquivalence

/- accepted add_to_file helper 13 -/
namespace MarkingEquivalence

lemma exists_unmarked_edge_from_root {n d k r : ℕ} (hd : 0 < d)
    (μ : MMarking n d k r) (hμ : mirreducible μ)
    {v : MVertex d k} (hv : v ≠ root hd) :
    ∃ z : MVertex d k, z ≠ root hd ∧
      ∃ e : MEdge n d k, e ∉ Set.range μ.1 ∧ mends e = Sym2.mk (root hd) z := by
  have hreach : (unmarkedGraph μ.1).Reachable (root hd) v := hμ.preconnected _ _
  rw [SimpleGraph.reachable_eq_reflTransGen] at hreach
  rcases Relation.ReflTransGen.cases_head hreach with hEq | ⟨z, hAdj, hrest⟩
  · exact False.elim (hv hEq.symm)
  · refine ⟨z, ?_, ?_⟩
    · intro hz
      subst z
      rw [unmarkedGraph, SimpleGraph.fromRel_adj] at hAdj
      exact hAdj.1 rfl
    · exact exists_unmarked_edge_of_adj hAdj

end MarkingEquivalence

/- accepted add_to_file helper 14 -/
namespace MarkingEquivalence

lemma starify_aux_measure {n d k r : ℕ} (hn : 0 < n) (hd : 0 < d) :
    ∀ m : ℕ, ∀ (S : Finset (MVertex d k)) (μ : MMarking n d k r),
      Fintype.card (MVertex d k) - S.card = m →
      root hd ∈ S →
      (∀ x ∈ S, ∀ hx : x ≠ root hd,
        starEdge hn hd x hx ∉ Set.range μ.1) →
      mirreducible μ →
      ∃ μ' : MMarking n d k r,
        Relation.ReflTransGen MMove μ μ' ∧ mirreducible μ' ∧
        ∀ x : MVertex d k, ∀ hx : x ≠ root hd,
          starEdge hn hd x hx ∉ Set.range μ'.1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro S μ hmeasure hroot hstar hμ
      by_cases hS : S = Finset.univ
      · refine ⟨μ, Relation.ReflTransGen.refl, hμ, ?_⟩
        intro x hx
        exact hstar x (by rw [hS]; simp) hx
      · have hnotall : ∃ a : MVertex d k, a ∉ S := by
          by_contra hnone
          apply hS
          ext a
          simp only [Finset.mem_univ, iff_true]
          show a ∈ S
          by_contra ha
          exact hnone ⟨a, ha⟩
        rcases hnotall with ⟨a, ha⟩
        have hreach : (unmarkedGraph μ.1).Reachable a (root hd) := hμ.preconnected _ _
        rw [SimpleGraph.reachable_eq_reflTransGen] at hreach
        obtain ⟨x, hx, y, hy, hxy⟩ := exists_cross_of_reachable hreach ha hroot
        obtain ⟨μ₁, hpath₁, hμ₁, hstar₁⟩ :=
          starify_one_step hn hd μ hμ S hroot hstar hx hy hxy
        have hltcard : S.card < Fintype.card (MVertex d k) := by
          have hss : S ⊂ Finset.univ := Finset.ssubset_univ_iff.mpr hS
          have := Finset.card_lt_card hss
          simpa using this
        have hlt : Fintype.card (MVertex d k) - (insert x S).card < m := by
          rw [← hmeasure, Finset.card_insert_of_notMem hx]
          omega
        obtain ⟨μ₂, hpath₂, hμ₂, hstar₂⟩ :=
          ih (Fintype.card (MVertex d k) - (insert x S).card) hlt
            (insert x S) μ₁ rfl (Finset.mem_insert_of_mem hroot) hstar₁ hμ₁
        exact ⟨μ₂, hpath₁.trans hpath₂, hμ₂, hstar₂⟩

lemma starify_with_seed {n d k r : ℕ} (hn : 0 < n) (hd : 0 < d)
    (μ : MMarking n d k r) (hμ : mirreducible μ)
    {z : MVertex d k} (hz : z ≠ root hd)
    (hseed : starEdge hn hd z hz ∉ Set.range μ.1) :
    ∃ μ' : MMarking n d k r,
      Relation.ReflTransGen MMove μ μ' ∧ mirreducible μ' ∧
      ∀ x : MVertex d k, ∀ hx : x ≠ root hd,
        starEdge hn hd x hx ∉ Set.range μ'.1 := by
  classical
  let S : Finset (MVertex d k) := {root hd, z}
  have hroot : root hd ∈ S := by simp [S]
  have hstar : ∀ x ∈ S, ∀ hx : x ≠ root hd,
      starEdge hn hd x hx ∉ Set.range μ.1 := by
    intro x hxS hx
    simp [S] at hxS
    rcases hxS with rfl | rfl
    · exact False.elim (hx rfl)
    · exact hseed
  exact starify_aux_measure hn hd (Fintype.card (MVertex d k) - S.card)
    S μ rfl hroot hstar hμ

end MarkingEquivalence

/- accepted add_to_file helper 15 -/
namespace MarkingEquivalence

lemma starify {n d k r : ℕ} (hn : 0 < n) (hd : 0 < d)
    (μ : MMarking n d k r) (hμ : mirreducible μ) :
    ∃ μ' : MMarking n d k r,
      Relation.ReflTransGen MMove μ μ' ∧ mirreducible μ' ∧
      ∀ x : MVertex d k, ∀ hx : x ≠ root hd,
        starEdge hn hd x hx ∉ Set.range μ'.1 := by
  classical
  by_cases hsingle : ∀ v : MVertex d k, v = root hd
  · exact ⟨μ, Relation.ReflTransGen.refl, hμ, fun x hx => False.elim (hx (hsingle x))⟩
  · push_neg at hsingle
    rcases hsingle with ⟨v, hv⟩
    obtain ⟨z, hz, e, he, hend⟩ := exists_unmarked_edge_from_root hd μ hμ hv
    let sz := starEdge hn hd z hz
    by_cases hsz : sz ∈ Set.range μ.1
    · have hendsym : mends e = Sym2.mk z (root hd) := hend.trans Sym2.eq_swap
      have hends : mends sz = mends e := by
        rw [mends_starEdge hn hd z hz, hendsym, Sym2.eq_swap]
      have hsne : sz ≠ e := by
        intro h
        exact he (h ▸ hsz)
      let μ₁ := applySwapMarking sz e μ
      have hpath₁ : Relation.ReflTransGen MMove μ μ₁ :=
        Relation.ReflTransGen.single (MDMove.move (dmove_swap hsne hends μ))
      have hμ₁ : mirreducible μ₁ := dmove_preserves_irreducible hends hμ
      have hseed₁ : sz ∉ Set.range μ₁.1 := by
        apply notMem_range_applySwap_preimage μ
          (a := sz) (b := e) (target := sz) (source := e)
        · simp
        · exact he
      obtain ⟨μ₂, hpath₂, hμ₂, hstar₂⟩ := starify_with_seed hn hd μ₁ hμ₁ hz hseed₁
      exact ⟨μ₂, hpath₁.trans hpath₂, hμ₂, hstar₂⟩
    · exact starify_with_seed hn hd μ hμ hz hsz

end MarkingEquivalence

/- accepted add_to_file helper 16 -/
namespace MarkingEquivalence

noncomputable def liftPosPerm {n d k : ℕ} (hn : 0 < n) (hd : 0 < d) :
    Equiv.Perm (PosEdge (k := k) hn hd) →* Equiv.Perm (MEdge n d k) := by
  classical
  exact Equiv.Perm.extendDomainHom (Equiv.refl (PosEdge (k := k) hn hd))

end MarkingEquivalence

/- accepted add_to_file helper 17 -/
namespace MarkingEquivalence

lemma liftPosPerm_swap {n d k : ℕ} (hn : 0 < n) (hd : 0 < d)
    (x y : PosEdge (k := k) hn hd) :
    liftPosPerm hn hd (Equiv.swap x y) = Equiv.swap x.1 y.1 := by
  classical
  apply Equiv.ext
  intro e
  by_cases heP : ¬ IsCanonicalStarEdge hn hd e
  · rw [liftPosPerm]
    rw [Equiv.Perm.extendDomainHom_apply]
    rw [Equiv.Perm.extendDomain_apply_subtype (Equiv.swap x y)
      (p := fun e => ¬ IsCanonicalStarEdge hn hd e)
      (Equiv.refl (PosEdge (k:=k) hn hd)) heP]
    by_cases hx : e = x.1
    · subst e
      simp
    · by_cases hy : e = y.1
      · subst e
        simp
      · have hrhs : Equiv.swap x.1 y.1 e = e := Equiv.swap_apply_of_ne_of_ne hx hy
        rw [hrhs]
        change ((Equiv.swap x y) ⟨e, heP⟩).1 = e
        rw [Equiv.swap_apply_of_ne_of_ne]
        · intro hsub
          exact hx (congrArg Subtype.val hsub)
        · intro hsub
          exact hy (congrArg Subtype.val hsub)
  · have heC : IsCanonicalStarEdge hn hd e := by
      by_contra h
      exact heP h
    have hnotP : ¬ ¬ IsCanonicalStarEdge hn hd e := by
      intro h
      exact h heC
    have hfixx : e ≠ x.1 := by
      intro h
      exact x.2 (h ▸ heC)
    have hfixy : e ≠ y.1 := by
      intro h
      exact y.2 (h ▸ heC)
    rw [Equiv.swap_apply_of_ne_of_ne hfixx hfixy]
    rw [liftPosPerm]
    rw [Equiv.Perm.extendDomainHom_apply]
    rw [Equiv.Perm.extendDomain_apply_not_subtype (Equiv.swap x y)
      (p := fun e => ¬ IsCanonicalStarEdge hn hd e)
      (Equiv.refl (PosEdge (k:=k) hn hd)) hnotP]

end MarkingEquivalence

/- accepted add_to_file helper 18 -/
namespace MarkingEquivalence

lemma mends_eq_mk_of_mem {n d k : ℕ} {e : MEdge n d k} {z : MVertex d k}
    (h : Sym2.Mem z (mends e)) :
    ∃ w : MVertex d k, mends e = Sym2.mk z w := by
  revert h
  exact Sym2.inductionOn (mends e) (fun a b hmem => by
    rw [Sym2.mem_iff'] at hmem
    rcases hmem with rfl | rfl
    · exact ⟨b, rfl⟩
    · exact ⟨a, Sym2.eq_swap⟩)

def PosAdj {n d k : ℕ} (hn : 0 < n) (hd : 0 < d) :
    PosEdge (k := k) hn hd → PosEdge (k := k) hn hd → Prop :=
  fun x y => x ≠ y ∧ ∃ z : MVertex d k, z ≠ root hd ∧
    Sym2.Mem z (mends x.1) ∧ Sym2.Mem z (mends y.1)

end MarkingEquivalence

/- accepted add_to_file helper 19 -/
namespace MarkingEquivalence

lemma mends_ne_of_eq {n d k : ℕ} {e : MEdge n d k} {u v : MVertex d k}
    (h : mends e = Sym2.mk u v) : u ≠ v := by
  intro huv
  subst v
  cases e with
  | inl e =>
      simp only [mends] at h
      have hs := Sym2.eq_iff.mp h
      rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hv : e.1.val.1 = e.1.val.2 := Sum.inl.inj (h1.trans h2.symm)
        exact (ne_of_lt e.1.property) hv
      · have hv : e.1.val.1 = e.1.val.2 := Sum.inl.inj (h1.trans h2.symm)
        exact (ne_of_lt e.1.property) hv
  | inr e =>
      simp only [mends] at h
      have hs := Sym2.eq_iff.mp h
      rcases hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        exact Sum.inr_ne_inl (h2.trans h1.symm)

lemma starEdge_ne_of_other_ne {n d k : ℕ} (hn : 0 < n) (hd : 0 < d)
    {y : MVertex d k} (hy : y ≠ root hd) {u v : MVertex d k}
    (h : mends (starEdge hn hd y hy) = Sym2.mk u v)
    (hu : u ≠ root hd) (hv : v ≠ root hd) : False := by
  rw [mends_starEdge hn hd y hy] at h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨hur, hyv⟩ | ⟨hvr, hyu⟩
  · exact hu hur.symm
  · exact hv hvr.symm

end MarkingEquivalence

/- accepted add_to_file helper 20 -/
namespace MarkingEquivalence

lemma star_unmarked_applySwap_pos {n d k r : ℕ} (hn : 0 < n) (hd : 0 < d)
    (μ : MMarking n d k r)
    (hstar : ∀ x : MVertex d k, ∀ hx : x ≠ root hd,
      starEdge hn hd x hx ∉ Set.range μ.1)
    (x y : PosEdge (k := k) hn hd)
    (w : MVertex d k) (hw : w ≠ root hd) :
    starEdge hn hd w hw ∉ Set.range (applySwapMarking x.1 y.1 μ).1 := by
  classical
  let sw := starEdge hn hd w hw
  have hwx : sw ≠ x.1 := by
    intro h
    exact x.2 ⟨w, hw, h.symm⟩
  have hwy : sw ≠ y.1 := by
    intro h
    exact y.2 ⟨w, hw, h.symm⟩
  have hfix : Equiv.swap x.1 y.1 sw = sw :=
    Equiv.swap_apply_of_ne_of_ne hwx hwy
  exact notMem_range_applySwap_fixed μ hfix (hstar w hw)

end MarkingEquivalence

/- accepted add_to_file helper 21 -/
namespace MarkingEquivalence

lemma rtc_posadj_swap {n d k r : ℕ} (hn : 0 < n) (hd : 0 < d)
    (μ : MMarking n d k r)
    (hstar : ∀ x : MVertex d k, ∀ hx : x ≠ root hd,
      starEdge hn hd x hx ∉ Set.range μ.1)
    {x y : PosEdge (k := k) hn hd} (hxy : PosAdj hn hd x y) :
    Relation.ReflTransGen MMove μ (applySwapMarking x.1 y.1 μ) := by
  classical
  rcases hxy with ⟨hne, A, hA, hxmem, hymem⟩
  obtain ⟨B, hxends⟩ := mends_eq_mk_of_mem hxmem
  obtain ⟨C, hyends⟩ := mends_eq_mk_of_mem hymem
  have hAB : A ≠ B := mends_ne_of_eq hxends
  have hAC : A ≠ C := mends_ne_of_eq hyends
  by_cases hends : mends x.1 = mends y.1
  · have hneE : x.1 ≠ y.1 := by
      intro h
      exact hne (Subtype.ext h)
    exact Relation.ReflTransGen.single
      (MDMove.move (dmove_swap hneE hends μ))
  · have hBC : B ≠ C := by
      intro h
      apply hends
      rw [hxends, hyends, h]
    have hRA : root hd ≠ A := fun h => hA h.symm
    by_cases hB : B = root hd
    · have hC : C ≠ root hd := by
        intro h
        apply hends
        rw [hxends, hyends, hB, h]
      let sC := starEdge hn hd C hC
      have hsC : sC ∉ Set.range μ.1 := hstar C hC
      have hxends' : mends x.1 = Sym2.mk (root hd) A := hxends.trans (by rw [hB]; exact Sym2.eq_swap)
      have hRC : root hd ≠ C := fun h => hC h.symm
      have hT : MTMove μ (applySwapMarking y.1 x.1 μ) :=
        tmove_swap μ hRA hRC hAC
          (q := y.1) (q' := sC) (q'' := x.1) hyends
          (mends_starEdge hn hd C hC) hxends' hsC
      have hswap : applySwapMarking y.1 x.1 μ = applySwapMarking x.1 y.1 μ := by
        apply Subtype.ext
        funext i
        simp [applySwapMarking, applyPermMarking, Equiv.swap_comm]
      rw [← hswap]
      exact Relation.ReflTransGen.single (MTMove.move hT)
    · by_cases hC : C = root hd
      · let sB := starEdge hn hd B hB
        have hsB : sB ∉ Set.range μ.1 := hstar B hB
        have hyends' : mends y.1 = Sym2.mk (root hd) A := hyends.trans (by rw [hC]; exact Sym2.eq_swap)
        have hRB : root hd ≠ B := fun h => hB h.symm
        have hT : MTMove μ (applySwapMarking x.1 y.1 μ) :=
          tmove_swap μ hRA hRB hAB
            (q := x.1) (q' := sB) (q'' := y.1) hxends
            (mends_starEdge hn hd B hB) hyends' hsB
        exact Relation.ReflTransGen.single (MTMove.move hT)
      · let sA := starEdge hn hd A hA
        let sB := starEdge hn hd B hB
        let sC := starEdge hn hd C hC
        have hsB : sB ∉ Set.range μ.1 := hstar B hB
        have hsC : sC ∉ Set.range μ.1 := hstar C hC
        have hRB : root hd ≠ B := fun h => hB h.symm
        have hRC : root hd ≠ C := fun h => hC h.symm
        have hsA_ne_x : sA ≠ x.1 := by
          intro h
          have hm : mends sA = Sym2.mk A B := by
            have hm0 := congrArg mends h
            rwa [hxends] at hm0
          exact starEdge_ne_of_other_ne hn hd hA hm hA hB
        have hsA_ne_y : sA ≠ y.1 := by
          intro h
          have hm : mends sA = Sym2.mk A C := by
            have hm0 := congrArg mends h
            rwa [hyends] at hm0
          exact starEdge_ne_of_other_ne hn hd hA hm hA hC
        have hsB_ne_sA : sB ≠ sA := by
          intro h
          exact hAB (starEdge_eq_of_mends_eq hn hd hB hA h).symm
        have hsC_ne_sA : sC ≠ sA := by
          intro h
          exact hAC (starEdge_eq_of_mends_eq hn hd hC hA h).symm
        let μ₁ := applySwapMarking x.1 sA μ
        have hT₁ : MTMove μ μ₁ :=
          tmove_swap μ hRA hRB hAB
            (q := x.1) (q' := sB) (q'' := sA) hxends
            (mends_starEdge hn hd B hB) (mends_starEdge hn hd A hA) hsB
        have hsC₁ : sC ∉ Set.range μ₁.1 := by
          have hfix : Equiv.swap x.1 sA sC = sC := by
            apply Equiv.swap_apply_of_ne_of_ne
            · intro h
              have hm : mends sC = Sym2.mk A B := by
                have hm0 := congrArg mends h
                rwa [hxends] at hm0
              exact starEdge_ne_of_other_ne hn hd hC hm hA hB
            · exact hsC_ne_sA
          exact notMem_range_applySwap_fixed μ hfix hsC
        have hsB₁ : sB ∉ Set.range μ₁.1 := by
          have hfix : Equiv.swap x.1 sA sB = sB := by
            apply Equiv.swap_apply_of_ne_of_ne
            · intro h
              have hm : mends sB = Sym2.mk A B := by
                have hm0 := congrArg mends h
                rwa [hxends] at hm0
              exact starEdge_ne_of_other_ne hn hd hB hm hA hB
            · exact hsB_ne_sA
          exact notMem_range_applySwap_fixed μ hfix hsB
        let μ₂ := applySwapMarking y.1 sA μ₁
        have hT₂ : MTMove μ₁ μ₂ :=
          tmove_swap μ₁ hRA hRC hAC
            (q := y.1) (q' := sC) (q'' := sA) hyends
            (mends_starEdge hn hd C hC) (mends_starEdge hn hd A hA) hsC₁
        have hsB₂ : sB ∉ Set.range μ₂.1 := by
          have hfix : Equiv.swap y.1 sA sB = sB := by
            apply Equiv.swap_apply_of_ne_of_ne
            · intro h
              have hm : mends sB = Sym2.mk A C := by
                have hm0 := congrArg mends h
                rwa [hyends] at hm0
              exact starEdge_ne_of_other_ne hn hd hB hm hA hC
            · exact hsB_ne_sA
          exact notMem_range_applySwap_fixed μ₁ hfix hsB₁
        let μ₃ := applySwapMarking x.1 sA μ₂
        have hT₃ : MTMove μ₂ μ₃ :=
          tmove_swap μ₂ hRA hRB hAB
            (q := x.1) (q' := sB) (q'' := sA) hxends
            (mends_starEdge hn hd B hB) (mends_starEdge hn hd A hA) hsB₂
        have hpath : Relation.ReflTransGen MMove μ μ₃ :=
          (Relation.ReflTransGen.single (MTMove.move hT₁)).trans
            ((Relation.ReflTransGen.single (MTMove.move hT₂)).trans
              (Relation.ReflTransGen.single (MTMove.move hT₃)))
        have hμ₃ : μ₃ = applySwapMarking x.1 y.1 μ := by
          apply Subtype.ext
          funext i
          have hperm :
              Equiv.swap x.1 sA * Equiv.swap y.1 sA * Equiv.swap x.1 sA =
                Equiv.swap x.1 y.1 := by
            have h := Equiv.swap_mul_swap_mul_swap
              (x := y.1) (y := sA) (z := x.1)
              (by
                intro h
                exact hsA_ne_y h.symm)
              (by
                intro h
                exact hne (Subtype.ext h.symm))
            simpa [Equiv.swap_comm] using h
          have happ := congrArg (fun σ : Equiv.Perm (MEdge n d k) => σ (μ.1 i)) hperm
          simpa [μ₁, μ₂, μ₃, applySwapMarking, applyPermMarking, Equiv.Perm.mul_apply] using happ
        rw [hμ₃] at hpath
        exact hpath

end MarkingEquivalence

/- accepted add_to_file helper 22 -/
namespace MarkingEquivalence

lemma rtc_swap_of_posadj_path {n d k r : ℕ} (hn : 0 < n) (hd : 0 < d)
    {x y : PosEdge (k := k) hn hd} (hne : x ≠ y)
    (h : Relation.ReflTransGen (PosAdj hn hd) x y) :
    ∀ (μ : MMarking n d k r),
      (∀ v : MVertex d k, ∀ hv : v ≠ root hd,
        starEdge hn hd v hv ∉ Set.range μ.1) →
      Relation.ReflTransGen MMove μ (applySwapMarking x.1 y.1 μ) := by
  induction h with
  | refl =>
      intro μ hstar
      exact False.elim (hne rfl)
  | tail hxy hyz ih =>
      rename_i y z
      intro μ hstar
      by_cases hxyeq : x = y
      · subst y
        exact rtc_posadj_swap hn hd μ hstar hyz
      · let μ₁ := applySwapMarking x.1 y.1 μ
        have hstar₁ : ∀ v : MVertex d k, ∀ hv : v ≠ root hd,
            starEdge hn hd v hv ∉ Set.range μ₁.1 :=
          fun v hv => star_unmarked_applySwap_pos hn hd μ hstar x y v hv
        have hpath₁ : Relation.ReflTransGen MMove μ μ₁ := ih hxyeq μ hstar
        let μ₂ := applySwapMarking y.1 z.1 μ₁
        have hstar₂ : ∀ v : MVertex d k, ∀ hv : v ≠ root hd,
            starEdge hn hd v hv ∉ Set.range μ₂.1 :=
          fun v hv => star_unmarked_applySwap_pos hn hd μ₁ hstar₁ y z v hv
        have hpath₂ : Relation.ReflTransGen MMove μ₁ μ₂ :=
          rtc_posadj_swap hn hd μ₁ hstar₁ hyz
        let μ₃ := applySwapMarking x.1 y.1 μ₂
        have hstar₃ : ∀ v : MVertex d k, ∀ hv : v ≠ root hd,
            starEdge hn hd v hv ∉ Set.range μ₃.1 :=
          fun v hv => star_unmarked_applySwap_pos hn hd μ₂ hstar₂ x y v hv
        have hpath₃ : Relation.ReflTransGen MMove μ₂ μ₃ := ih hxyeq μ₂ hstar₂
        have hpath : Relation.ReflTransGen MMove μ μ₃ :=
          hpath₁.trans (hpath₂.trans hpath₃)
        have hμ₃ : μ₃ = applySwapMarking x.1 z.1 μ := by
          apply Subtype.ext
          funext i
          have hperm :
              Equiv.swap x.1 y.1 * Equiv.swap y.1 z.1 * Equiv.swap x.1 y.1 =
                Equiv.swap x.1 z.1 := by
            have hyz' : z.1 ≠ y.1 := by
              intro hE
              exact hyz.1 (Subtype.ext hE.symm)
            have hzx : z.1 ≠ x.1 := by
              intro hE
              exact hne (Subtype.ext hE.symm)
            have hswap := Equiv.swap_mul_swap_mul_swap
              (x := z.1) (y := y.1) (z := x.1) hyz' hzx
            simpa [Equiv.swap_comm] using hswap
          have happ := congrArg (fun σ : Equiv.Perm (MEdge n d k) => σ (μ.1 i)) hperm
          simpa [μ₁, μ₂, μ₃, applySwapMarking, applyPermMarking, Equiv.Perm.mul_apply] using happ
        rw [hμ₃] at hpath
        exact hpath

end MarkingEquivalence

/- accepted add_to_file helper 23 -/
namespace MarkingEquivalence

def hubVertex {d k : ℕ} (hd2 : 1 < d) : MVertex d k :=
  Sum.inl (⟨1, hd2⟩ : Fin d)

def llEdge {n d k : ℕ} (hn : 0 < n) (i j : Fin d) (hij : i ≠ j) : MEdge n d k :=
  if hlt : i < j then
    Sum.inl (⟨(i, j), hlt⟩, ⟨0, hn⟩)
  else
    Sum.inl (⟨(j, i), lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hij)⟩, ⟨0, hn⟩)

lemma mends_llEdge {n d k : ℕ} (hn : 0 < n) (i j : Fin d) (hij : i ≠ j) :
    mends (llEdge hn i j hij) = Sym2.mk (Sum.inl i : MVertex d k) (Sum.inl j) := by
  unfold llEdge
  split <;> simp [mends, Sym2.eq_swap]

end MarkingEquivalence

/- accepted add_to_file helper 24 -/
namespace MarkingEquivalence

lemma llEdge_notCanonical {n d k : ℕ} (hn : 0 < n) {hd : 0 < d}
    {i j : Fin d} (hij : i ≠ j)
    (hi : (Sum.inl i : MVertex d k) ≠ root hd)
    (hj : (Sum.inl j : MVertex d k) ≠ root hd) :
    ¬ IsCanonicalStarEdge (k := k) hn hd (llEdge (k := k) hn i j hij) := by
  rintro ⟨x, hx, hEq⟩
  have hm := congrArg mends hEq
  rw [mends_llEdge (k := k) hn i j hij, mends_starEdge hn hd x hx] at hm
  have hmstar : mends (starEdge hn hd x hx) =
      Sym2.mk (Sum.inl i : MVertex d k) (Sum.inl j) := by
    rw [mends_starEdge hn hd x hx]
    exact hm.symm
  exact starEdge_ne_of_other_ne hn hd hx hmstar hi hj

lemma inl_ne_root_of_ne {d k : ℕ} {hd : 0 < d} {i : Fin d}
    (hi : i ≠ ⟨0, hd⟩) : (Sum.inl i : MVertex d k) ≠ root hd := by
  intro h
  apply hi
  cases h
  rfl

lemma fin_ne_of_inl_ne_root {d k : ℕ} {hd : 0 < d} {i : Fin d}
    (hi : (Sum.inl i : MVertex d k) ≠ root hd) : i ≠ ⟨0, hd⟩ := by
  intro h
  apply hi
  rw [h]
  rfl

lemma inr_ne_root {d k : ℕ} (hd : 0 < d) (j : Fin k) :
    (Sum.inr j : MVertex d k) ≠ root hd := by
  intro h
  cases h

end MarkingEquivalence

/- accepted add_to_file helper 25 -/
namespace MarkingEquivalence

lemma mem_mends_of_eq_left {n d k : ℕ} {e : MEdge n d k} {u v : MVertex d k}
    (h : mends e = Sym2.mk u v) : Sym2.Mem u (mends e) := by
  rw [h, Sym2.mem_iff']
  exact Or.inl rfl

lemma mem_mends_of_eq_right {n d k : ℕ} {e : MEdge n d k} {u v : MVertex d k}
    (h : mends e = Sym2.mk u v) : Sym2.Mem v (mends e) := by
  rw [h, Sym2.mem_iff']
  exact Or.inr rfl

lemma hub_mem_llEdge_left {n d k : ℕ} (hn : 0 < n) {hd2 : 1 < d}
    (i : Fin d) (h : ⟨1, hd2⟩ ≠ i) :
    Sym2.Mem (hubVertex (k := k) hd2)
      (mends (llEdge (k := k) hn (⟨1, hd2⟩ : Fin d) i h)) := by
  apply mem_mends_of_eq_left (mends_llEdge (k := k) hn (⟨1, hd2⟩ : Fin d) i h)

lemma hub_mem_llEdge_right {n d k : ℕ} (hn : 0 < n) {hd2 : 1 < d}
    (i : Fin d) (h : i ≠ ⟨1, hd2⟩) :
    Sym2.Mem (hubVertex (k := k) hd2)
      (mends (llEdge (k := k) hn i (⟨1, hd2⟩ : Fin d) h)) := by
  apply mem_mends_of_eq_right (mends_llEdge (k := k) hn i (⟨1, hd2⟩ : Fin d) h)

end MarkingEquivalence

/- accepted add_to_file helper 26 -/
namespace MarkingEquivalence

lemma exists_hub_neighbor {n d k : ℕ} (hn : 0 < n) {hd2 : 1 < d}
    (p : PosEdge (k := k) hn (Nat.lt_trans Nat.zero_lt_one hd2)) :
    ∃ q : PosEdge (k := k) hn (Nat.lt_trans Nat.zero_lt_one hd2),
      Sym2.Mem (hubVertex (k := k) hd2) (mends q.1) ∧
      Relation.ReflTransGen (PosAdj hn (Nat.lt_trans Nat.zero_lt_one hd2)) p q := by
  classical
  let hd : 0 < d := Nat.lt_trans Nat.zero_lt_one hd2
  let hubF : Fin d := ⟨1, hd2⟩
  let rootF : Fin d := ⟨0, hd⟩
  have hhubR : hubVertex (k := k) hd2 ≠ root hd :=
    inl_ne_root_of_ne (by
      intro h
      have : (1 : ℕ) = 0 := congrArg Fin.val h
      omega)
  cases hp : p.1 with
  | inr x =>
      rcases x with ⟨i, j⟩
      by_cases hiH : i = hubF
      · refine ⟨p, ?_, Relation.ReflTransGen.refl⟩
        have hend : mends p.1 = Sym2.mk (Sum.inl i : MVertex d k) (Sum.inr j) := by
          simp [hp, mends]
        rw [hiH] at hend
        exact mem_mends_of_eq_left hend
      · have hiRfin : i ≠ rootF := by
          intro hi0
          have hcan : IsCanonicalStarEdge (k := k) hn hd p.1 :=
            ⟨Sum.inr j, inr_ne_root hd j, by
              simp [hp, starEdge, hi0, rootF]⟩
          exact p.2 hcan
        have hiR : (Sum.inl i : MVertex d k) ≠ root hd := inl_ne_root_of_ne hiRfin
        have hhubi : hubF ≠ i := fun h => hiH h.symm
        let qe : MEdge n d k := llEdge (k := k) hn hubF i hhubi
        have hqP : ¬ IsCanonicalStarEdge (k := k) hn hd qe :=
          llEdge_notCanonical hn hhubi hhubR hiR
        let q : PosEdge (k := k) hn hd := ⟨qe, hqP⟩
        refine ⟨q, ?_, Relation.ReflTransGen.single ?_⟩
        · exact hub_mem_llEdge_left (k := k) hn i hhubi
        · refine ⟨?_, Sum.inl i, hiR, ?_, ?_⟩
          · intro hqp
            have hmem := hub_mem_llEdge_left (k := k) hn i hhubi
            have hqeq : q.1 = p.1 := congrArg Subtype.val hqp.symm
            have hmem' : Sym2.Mem (hubVertex (k := k) hd2) (mends p.1) := by
              rw [← hqeq]
              exact hmem
            have hendp : mends p.1 = Sym2.mk (Sum.inl i : MVertex d k) (Sum.inr j) := by
              simp [hp, mends]
            rw [hendp, Sym2.mem_iff'] at hmem'
            rcases hmem' with h | h
            · exact hiH (Sum.inl.inj h).symm
            · cases h
          · have hendp : mends p.1 = Sym2.mk (Sum.inl i : MVertex d k) (Sum.inr j) := by
              simp [hp, mends]
            exact mem_mends_of_eq_left hendp
          · exact mem_mends_of_eq_right (mends_llEdge (k := k) hn hubF i hhubi)
  | inl x =>
      rcases x with ⟨⟨⟨i, j⟩, hij⟩, c⟩
      have hendp : mends p.1 = Sym2.mk (Sum.inl i : MVertex d k) (Sum.inl j) := by
        simp [hp, mends]
      by_cases hiH : i = hubF
      · refine ⟨p, ?_, Relation.ReflTransGen.refl⟩
        rw [hiH] at hendp
        exact mem_mends_of_eq_left hendp
      · by_cases hjH : j = hubF
        · refine ⟨p, ?_, Relation.ReflTransGen.refl⟩
          rw [hjH] at hendp
          exact mem_mends_of_eq_right hendp
        · by_cases hi0 : i = rootF
          · have hjRfin : j ≠ rootF := by
              intro hj0
              have hval : i.val < j.val := hij
              rw [hi0, hj0] at hval
              simp [rootF] at hval
            have hjR : (Sum.inl j : MVertex d k) ≠ root hd := inl_ne_root_of_ne hjRfin
            have hhubj : hubF ≠ j := fun h => hjH h.symm
            let qe : MEdge n d k := llEdge (k := k) hn hubF j hhubj
            have hqP : ¬ IsCanonicalStarEdge (k := k) hn hd qe :=
              llEdge_notCanonical hn hhubj hhubR hjR
            let q : PosEdge (k := k) hn hd := ⟨qe, hqP⟩
            refine ⟨q, ?_, Relation.ReflTransGen.single ?_⟩
            · exact hub_mem_llEdge_left (k := k) hn j hhubj
            · refine ⟨?_, Sum.inl j, hjR, ?_, ?_⟩
              · intro hqp
                have hmem := hub_mem_llEdge_left (k := k) hn j hhubj
                have hqeq : q.1 = p.1 := congrArg Subtype.val hqp.symm
                have hmem' : Sym2.Mem (hubVertex (k := k) hd2) (mends p.1) := by
                  rw [← hqeq]
                  exact hmem
                rw [hendp, Sym2.mem_iff'] at hmem'
                rcases hmem' with h | h
                · exact hiH (Sum.inl.inj h).symm
                · exact hjH (Sum.inl.inj h).symm
              · exact mem_mends_of_eq_right hendp
              · exact mem_mends_of_eq_right (mends_llEdge (k := k) hn hubF j hhubj)
          · have hiR : (Sum.inl i : MVertex d k) ≠ root hd := inl_ne_root_of_ne hi0
            have hhubi : hubF ≠ i := fun h => hiH h.symm
            let qe : MEdge n d k := llEdge (k := k) hn hubF i hhubi
            have hqP : ¬ IsCanonicalStarEdge (k := k) hn hd qe :=
              llEdge_notCanonical hn hhubi hhubR hiR
            let q : PosEdge (k := k) hn hd := ⟨qe, hqP⟩
            refine ⟨q, ?_, Relation.ReflTransGen.single ?_⟩
            · exact hub_mem_llEdge_left (k := k) hn i hhubi
            · refine ⟨?_, Sum.inl i, hiR, ?_, ?_⟩
              · intro hqp
                have hmem := hub_mem_llEdge_left (k := k) hn i hhubi
                have hqeq : q.1 = p.1 := congrArg Subtype.val hqp.symm
                have hmem' : Sym2.Mem (hubVertex (k := k) hd2) (mends p.1) := by
                  rw [← hqeq]
                  exact hmem
                rw [hendp, Sym2.mem_iff'] at hmem'
                rcases hmem' with h | h
                · exact hiH (Sum.inl.inj h).symm
                · exact hjH (Sum.inl.inj h).symm
              · exact mem_mends_of_eq_left hendp
              · exact mem_mends_of_eq_right (mends_llEdge (k := k) hn hubF i hhubi)

end MarkingEquivalence

/- accepted add_to_file helper 27 -/
namespace MarkingEquivalence

lemma PosAdj.symm {n d k : ℕ} (hn : 0 < n) (hd : 0 < d)
    {x y : PosEdge (k := k) hn hd} (h : PosAdj hn hd x y) :
    PosAdj hn hd y x := by
  rcases h with ⟨hne, z, hz, hxz, hyz⟩
  exact ⟨hne.symm, z, hz, hyz, hxz⟩

lemma rtc_posadj_symm {n d k : ℕ} (hn : 0 < n) (hd : 0 < d)
    {x y : PosEdge (k := k) hn hd}
    (h : Relation.ReflTransGen (PosAdj hn hd) x y) :
    Relation.ReflTransGen (PosAdj hn hd) y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact (Relation.ReflTransGen.single (PosAdj.symm hn hd hyz)).trans ih

lemma posadj_reachable_all {n d k : ℕ} (hn : 0 < n) {hd2 : 1 < d}
    (x y : PosEdge (k := k) hn (Nat.lt_trans Nat.zero_lt_one hd2)) :
    Relation.ReflTransGen (PosAdj hn (Nat.lt_trans Nat.zero_lt_one hd2)) x y := by
  classical
  let hd : 0 < d := Nat.lt_trans Nat.zero_lt_one hd2
  obtain ⟨a, ha, hxa⟩ := exists_hub_neighbor (k := k) hn (hd2 := hd2) x
  obtain ⟨b, hb, hyb⟩ := exists_hub_neighbor (k := k) hn (hd2 := hd2) y
  have hhubR : hubVertex (k := k) hd2 ≠ root hd :=
    inl_ne_root_of_ne (by
      intro h
      have : (1 : ℕ) = 0 := congrArg Fin.val h
      omega)
  have hab : Relation.ReflTransGen (PosAdj hn hd) a b := by
    by_cases hEq : a = b
    · subst b
      exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single
        ⟨hEq, hubVertex (k := k) hd2, hhubR, ha, hb⟩
  exact hxa.trans (hab.trans (rtc_posadj_symm hn hd hyb))

end MarkingEquivalence

/- accepted add_to_file helper 28 -/
namespace MarkingEquivalence

lemma liftPosPerm_apply_canonical {n d k : ℕ} (hn : 0 < n) (hd : 0 < d)
    (σ : Equiv.Perm (PosEdge (k := k) hn hd))
    {e : MEdge n d k} (he : IsCanonicalStarEdge hn hd e) :
    (liftPosPerm hn hd σ) e = e := by
  classical
  rw [liftPosPerm, Equiv.Perm.extendDomainHom_apply]
  rw [Equiv.Perm.extendDomain_apply_not_subtype σ
    (p := fun e => ¬ IsCanonicalStarEdge hn hd e)
    (Equiv.refl (PosEdge (k := k) hn hd))]
  intro h
  exact h he

lemma star_unmarked_applyPerm_pos {n d k r : ℕ} (hn : 0 < n) (hd : 0 < d)
    (σ : Equiv.Perm (PosEdge (k := k) hn hd))
    (μ : MMarking n d k r)
    (hstar : ∀ x : MVertex d k, ∀ hx : x ≠ root hd,
      starEdge hn hd x hx ∉ Set.range μ.1)
    (x : MVertex d k) (hx : x ≠ root hd) :
    starEdge hn hd x hx ∉ Set.range (applyPermMarking (liftPosPerm hn hd σ) μ).1 := by
  classical
  intro hmem
  have hiff := mem_range_perm_comp (σ := liftPosPerm hn hd σ) (f := μ.1)
    (b := starEdge hn hd x hx)
  have hold := hiff.mp hmem
  have hfixsymm : (liftPosPerm hn hd σ).symm (starEdge hn hd x hx) =
      starEdge hn hd x hx := by
    have hfix := liftPosPerm_apply_canonical hn hd σ.symm
      (e := starEdge hn hd x hx) ⟨x, hx, rfl⟩
    simpa using hfix
  exact hstar x hx (by simpa [hfixsymm] using hold)

end MarkingEquivalence

/- accepted add_to_file helper 29 -/
namespace MarkingEquivalence

lemma rtc_applyPerm_pos {n d k r : ℕ} (hn : 0 < n) {hd2 : 1 < d}
    (μ : MMarking n d k r)
    (hstar : ∀ x : MVertex d k, ∀ hx : x ≠ root (Nat.lt_trans Nat.zero_lt_one hd2),
      starEdge hn (Nat.lt_trans Nat.zero_lt_one hd2) x hx ∉ Set.range μ.1)
    (σ : Equiv.Perm (PosEdge (k := k) hn (Nat.lt_trans Nat.zero_lt_one hd2))) :
    Relation.ReflTransGen MMove μ
      (applyPermMarking (liftPosPerm hn (Nat.lt_trans Nat.zero_lt_one hd2) σ) μ) := by
  classical
  let hd : 0 < d := Nat.lt_trans Nat.zero_lt_one hd2
  let P := PosEdge (k := k) hn hd
  let motive : Equiv.Perm P → Prop := fun σ =>
    Relation.ReflTransGen MMove μ (applyPermMarking (liftPosPerm hn hd σ) μ)
  have hone : motive 1 := by
    change Relation.ReflTransGen MMove μ (applyPermMarking (liftPosPerm hn hd (1 : Equiv.Perm P)) μ)
    have hid : applyPermMarking (liftPosPerm hn hd (1 : Equiv.Perm P)) μ = μ := by
      apply Subtype.ext
      funext i
      simp [applyPermMarking]
    simpa [hid] using (Relation.ReflTransGen.refl : Relation.ReflTransGen MMove μ μ)
  have hstep : ∀ (τ : Equiv.Perm P) (x y : P), x ≠ y → motive τ →
      motive (Equiv.swap x y * τ) := by
    intro τ x y hxy hτ
    change Relation.ReflTransGen MMove μ
      (applyPermMarking (liftPosPerm hn hd (Equiv.swap x y * τ)) μ)
    let μτ := applyPermMarking (liftPosPerm hn hd τ) μ
    have hstarτ : ∀ v : MVertex d k, ∀ hv : v ≠ root hd,
        starEdge hn hd v hv ∉ Set.range μτ.1 :=
      fun v hv => star_unmarked_applyPerm_pos hn hd τ μ hstar v hv
    have hpath : Relation.ReflTransGen MMove μτ (applySwapMarking x.1 y.1 μτ) :=
      rtc_swap_of_posadj_path hn hd hxy (posadj_reachable_all (k := k) hn (hd2 := hd2) x y)
        μτ hstarτ
    have hnext : applySwapMarking x.1 y.1 μτ =
        applyPermMarking (liftPosPerm hn hd (Equiv.swap x y * τ)) μ := by
      apply Subtype.ext
      funext i
      simp [μτ, applySwapMarking, applyPermMarking, map_mul,
        liftPosPerm_swap hn hd x y, Equiv.Perm.mul_apply]
    simpa [hnext] using hτ.trans hpath
  exact Equiv.Perm.swap_induction_on σ hone hstep

end MarkingEquivalence

/- accepted add_to_file helper 30 -/
namespace MarkingEquivalence

lemma liftPosPerm_apply_pos {n d k : ℕ} (hn : 0 < n) (hd : 0 < d)
    (σ : Equiv.Perm (PosEdge (k := k) hn hd))
    (p : PosEdge (k := k) hn hd) :
    (liftPosPerm hn hd σ) p.1 = (σ p).1 := by
  classical
  rw [liftPosPerm, Equiv.Perm.extendDomainHom_apply]
  rw [Equiv.Perm.extendDomain_apply_subtype σ
    (p := fun e => ¬ IsCanonicalStarEdge hn hd e)
    (Equiv.refl (PosEdge (k := k) hn hd)) p.2]
  simp

end MarkingEquivalence

/- accepted add_to_file helper 31 -/
namespace MarkingEquivalence

lemma star_unmarked_equiv {n d k r : ℕ} (hn : 0 < n) {hd2 : 1 < d}
    (μ ν : MMarking n d k r)
    (hμstar : ∀ x : MVertex d k, ∀ hx : x ≠ root (Nat.lt_trans Nat.zero_lt_one hd2),
      starEdge hn (Nat.lt_trans Nat.zero_lt_one hd2) x hx ∉ Set.range μ.1)
    (hνstar : ∀ x : MVertex d k, ∀ hx : x ≠ root (Nat.lt_trans Nat.zero_lt_one hd2),
      starEdge hn (Nat.lt_trans Nat.zero_lt_one hd2) x hx ∉ Set.range ν.1) :
    Relation.ReflTransGen MMove μ ν := by
  classical
  let hd : 0 < d := Nat.lt_trans Nat.zero_lt_one hd2
  let P := PosEdge (k := k) hn hd
  let f : Fin r → P := fun i =>
    ⟨μ.1 i, by
      intro hcan
      rcases hcan with ⟨x, hx, hEq⟩
      exact hμstar x hx ⟨i, hEq⟩⟩
  let g : Fin r → P := fun i =>
    ⟨ν.1 i, by
      intro hcan
      rcases hcan with ⟨x, hx, hEq⟩
      exact hνstar x hx ⟨i, hEq⟩⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply μ.2
    exact congrArg Subtype.val hij
  have hg : Function.Injective g := by
    intro i j hij
    apply ν.2
    exact congrArg Subtype.val hij
  obtain ⟨σ, hσ⟩ := exists_perm_comp_eq_of_injective f g hf hg
  have hpath := rtc_applyPerm_pos (k := k) hn (hd2 := hd2) μ hμstar σ
  have htarget : applyPermMarking (liftPosPerm hn hd σ) μ = ν := by
    apply Subtype.ext
    funext i
    calc
      (liftPosPerm hn hd σ) (μ.1 i) = (σ (f i)).1 := by
        rw [liftPosPerm_apply_pos hn hd σ (f i)]
      _ = (g i).1 := by
        have hi := congrFun hσ i
        exact congrArg Subtype.val hi
      _ = ν.1 i := rfl
  rw [htarget] at hpath
  exact hpath

end MarkingEquivalence

/- accepted add_to_file helper 32 -/
namespace MarkingEquivalence

lemma edge_d1_eq {n k : ℕ} (e : MEdge n 1 k) :
    ∃ j : Fin k, e = Sum.inr (⟨0, Nat.zero_lt_one⟩, j) := by
  cases e with
  | inl x =>
      rcases x with ⟨⟨⟨i, j⟩, hij⟩, c⟩
      have hi : i.val < 1 := i.isLt
      have hj : j.val < 1 := j.isLt
      have hlt : i.val < j.val := hij
      omega
  | inr x =>
      rcases x with ⟨i, j⟩
      refine ⟨j, ?_⟩
      congr 1
      congr 1
      apply Fin.ext
      have hi : i.val < 1 := i.isLt
      omega

lemma d1_star_unmarked {n k r : ℕ} (μ : MMarking n 1 k r)
    (hμ : mirreducible μ) (j : Fin k) :
    Sum.inr (⟨0, Nat.zero_lt_one⟩, j) ∉ Set.range μ.1 := by
  classical
  let R : MVertex 1 k := Sum.inl (⟨0, Nat.zero_lt_one⟩ : Fin 1)
  let F : MVertex 1 k := Sum.inr j
  have hRF : R ≠ F := by simp [R, F]
  have hreach : (unmarkedGraph μ.1).Reachable R F := hμ.preconnected _ _
  rw [SimpleGraph.reachable_eq_reflTransGen] at hreach
  rcases Relation.ReflTransGen.cases_tail hreach with hEq | ⟨c, hrtc, hAdj⟩
  · exact False.elim (hRF hEq.symm)
  · obtain ⟨e, he, hend⟩ := exists_unmarked_edge_of_adj hAdj
    obtain ⟨j₀, hj₀⟩ := edge_d1_eq e
    have hend₀ : mends e = Sym2.mk R (Sum.inr j₀ : MVertex 1 k) := by
      simp [hj₀, mends, R]
    have hpair : Sym2.mk c F = Sym2.mk R (Sum.inr j₀ : MVertex 1 k) := by
      rw [← hend, hend₀]
    rw [Sym2.eq_iff] at hpair
    rcases hpair with ⟨hcR, hjF⟩ | ⟨hcF, hFR⟩
    · have hj₀j : j₀ = j := (Sum.inr.inj hjF).symm
      subst c
      subst j₀
      simpa [hj₀] using he
    · exact False.elim (hRF hFR.symm)

end MarkingEquivalence

/- accepted add_to_file helper 33 -/
namespace MarkingEquivalence

lemma d1_markings_eq {n k r : ℕ} (μ ν : MMarking n 1 k r)
    (hμ : mirreducible μ) (hν : mirreducible ν) : μ = ν := by
  have hr : r = 0 := by
    by_contra hr
    let i : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
    obtain ⟨j, hj⟩ := edge_d1_eq (μ.1 i)
    exact d1_star_unmarked μ hμ j ⟨i, hj⟩
  subst r
  apply Subtype.ext
  funext i
  exact Fin.elim0 i

end MarkingEquivalence

/- accepted add_to_file helper 34 -/
namespace MarkingEquivalence

lemma d0_markings_eq {n k r : ℕ} (μ ν : MMarking n 0 k r) : μ = ν := by
  have hr : r = 0 := by
    by_contra hr
    let i : Fin r := ⟨0, Nat.pos_of_ne_zero hr⟩
    cases h : μ.1 i with
    | inl e =>
        exact e.1.val.1.elim0
    | inr e =>
        exact e.1.elim0
  subst r
  apply Subtype.ext
  funext i
  exact Fin.elim0 i

end MarkingEquivalence

/- accepted add_to_file helper 35 -/
namespace MarkingEquivalence

lemma MDMove.symm {n d k r : ℕ} {μ ν : MMarking n d k r}
    (h : MDMove μ ν) : MDMove ν μ := by
  rcases h with ⟨a, b, hab, hends, hfun⟩
  refine ⟨a, b, hab, hends, ?_⟩
  funext i
  rw [hfun]
  simp

lemma MTMove.symm {n d k r : ℕ} {μ ν : MMarking n d k r}
    (h : MTMove μ ν) : MTMove ν μ := by
  classical
  rcases h with ⟨D, D', D'', h12, h13, h23, q, q', q'', hq, hq', hq'', hfun⟩
  have hqq' : q ≠ q' := by
    intro h
    rw [h, hq'] at hq
    rw [Sym2.eq_iff] at hq
    rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h12 h1
    · exact h13 h1
  have hqq'' : q ≠ q'' := by
    intro h
    rw [h, hq''] at hq
    rw [Sym2.eq_iff] at hq
    rcases hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h12 h1
    · exact h13 h1
  have hq'q'' : q' ≠ q'' := by
    intro h
    rw [h, hq''] at hq'
    rw [Sym2.eq_iff] at hq'
    rcases hq' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact h23 h2
    · exact h13 h1
  by_cases hmarked : q' ∈ Set.range μ.1
  · have hνq' : q' ∈ Set.range ν.1 := by
      rw [hfun, if_pos hmarked]
      exact hmarked
    refine ⟨D, D', D'', h12, h13, h23, q, q', q'', hq, hq', hq'', ?_⟩
    rw [if_pos hνq']
    rw [hfun, if_pos hmarked]
  · have hνq' : q' ∉ Set.range ν.1 := by
      rw [hfun, if_neg hmarked]
      have hfix : Equiv.swap q q'' q' = q' :=
        Equiv.swap_apply_of_ne_of_ne hqq'.symm hq'q''
      exact notMem_range_applySwap_fixed μ hfix hmarked
    refine ⟨D, D', D'', h12, h13, h23, q, q', q'', hq, hq', hq'', ?_⟩
    rw [if_neg hνq']
    funext i
    rw [hfun, if_neg hmarked]
    simp

lemma MMove.symmetric {n d k r : ℕ} : Symmetric (MMove (n := n) (d := d) (k := k) (r := r)) := by
  intro μ ν h
  rcases h with h | h
  · exact Or.inl (MDMove.symm h)
  · exact Or.inr (MTMove.symm h)

end MarkingEquivalence

/- accepted add_to_file helper 36 -/
namespace MarkingEquivalence

lemma marking_equiv_hd2 {n d k r : ℕ} (hn : 0 < n) (hd2 : 1 < d)
    (μ ν : MMarking n d k r) (hμ : mirreducible μ) (hν : mirreducible ν) :
    Relation.ReflTransGen MMove μ ν := by
  let hd : 0 < d := Nat.lt_trans Nat.zero_lt_one hd2
  obtain ⟨μ₁, hμpath, hμ₁, hμstar⟩ := starify hn hd μ hμ
  obtain ⟨ν₁, hνpath, hν₁, hνstar⟩ := starify hn hd ν hν
  have hmid : Relation.ReflTransGen MMove μ₁ ν₁ :=
    star_unmarked_equiv (k := k) hn (hd2 := hd2) μ₁ ν₁ hμstar hνstar
  have hνback : Relation.ReflTransGen MMove ν₁ ν :=
    Relation.ReflTransGen.symmetric MMove.symmetric hνpath
  exact hμpath.trans (hmid.trans hνback)

end MarkingEquivalence

/- verified submission -/
theorem marking_equivalence
    (n d k r : ℕ) (hn : 0 < n) :
    let V := Fin d ⊕ Fin k
    let E := ({p : Fin d × Fin d // p.1 < p.2} × Fin n) ⊕ (Fin d × Fin k)
    let ends : E → Sym2 V := fun e =>
      match e with
      | Sum.inl x => Sym2.mk (Sum.inl x.1.val.1 : V) (Sum.inl x.1.val.2 : V)
      | Sum.inr x => Sym2.mk (Sum.inl x.1 : V) (Sum.inr x.2 : V)
    let Marking := {μ : Fin r → E // Function.Injective μ}
    let irreducible : Marking → Prop := fun μ =>
      (SimpleGraph.fromRel (fun u v : V =>
        ∃ e : E, e ∉ Set.range μ.1 ∧ ends e = Sym2.mk u v)).Connected
    let DMove : Marking → Marking → Prop := fun μ ν =>
      ∃ a b : E, a ≠ b ∧ ends a = ends b ∧
        ν.1 = fun i => Equiv.swap a b (μ.1 i)
    let TMove : Marking → Marking → Prop := fun μ ν =>
      ∃ D D' D'' : V,
        D ≠ D' ∧ D ≠ D'' ∧ D' ≠ D'' ∧
        ∃ q q' q'' : E,
          ends q = Sym2.mk D' D'' ∧
          ends q' = Sym2.mk D D'' ∧
          ends q'' = Sym2.mk D D' ∧
          ν.1 = if q' ∈ Set.range μ.1 then μ.1
            else fun i => Equiv.swap q q'' (μ.1 i)
    let Move : Marking → Marking → Prop := fun μ ν => DMove μ ν ∨ TMove μ ν
    ∀ μ ν : Marking, irreducible μ → irreducible ν →
      Relation.ReflTransGen Move μ ν := by
  intro V E ends Marking irreducible DMove TMove Move μ ν hμ hν
  change MarkingEquivalence.mirreducible μ at hμ
  change MarkingEquivalence.mirreducible ν at hν
  change Relation.ReflTransGen (MarkingEquivalence.MMove (n:=n) (d:=d) (k:=k) (r:=r)) μ ν
  by_cases hd0 : d = 0
  · subst d
    have hEq := MarkingEquivalence.d0_markings_eq (n:=n) (k:=k) (r:=r) μ ν
    rw [hEq]
  · by_cases hd1 : d = 1
    · subst d
      have hEq := MarkingEquivalence.d1_markings_eq (n:=n) (k:=k) (r:=r) μ ν hμ hν
      rw [hEq]
    · have hd2 : 1 < d := by omega
      exact MarkingEquivalence.marking_equiv_hd2 (n:=n) (d:=d) (k:=k) (r:=r) hn hd2 μ ν hμ hν

end Rollout_p0256_marking_equivalence

namespace Rollout_p1268_flower_graph_equitable_coloring_moments

/- accepted add_to_file helper 1 -/

abbrev FlowerVertex (n : ℕ) := Unit ⊕ (Fin n ⊕ Fin n)

def flowerRel (n : ℕ) : FlowerVertex n → FlowerVertex n → Prop := fun a b =>
  (∃ i : Fin n, a = Sum.inl () ∧ b = Sum.inr (Sum.inl i)) ∨
  (∃ i : Fin n,
    a = Sum.inr (Sum.inl i) ∧
      b = Sum.inr (Sum.inl ((finRotate n) i))) ∨
  (∃ i : Fin n, a = Sum.inr (Sum.inl i) ∧ b = Sum.inr (Sum.inr i)) ∨
  (∃ i : Fin n, a = Sum.inl () ∧ b = Sum.inr (Sum.inr i))

def flowerGraph (n : ℕ) : SimpleGraph (FlowerVertex n) :=
  SimpleGraph.fromRel (flowerRel n)

def flowerPairColor (n : ℕ) : FlowerVertex n → Fin (n + 1)
  | Sum.inl _ => Fin.last n
  | Sum.inr (Sum.inl i) => i.castSucc
  | Sum.inr (Sum.inr i) => ((finRotate n) i).castSucc

lemma finRotate_ne_self_of_two_le {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    (finRotate n) i ≠ i := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
      intro h
      have hv := congrArg Fin.val h
      rw [coe_finRotate] at hv
      by_cases hi : i = Fin.last m
      · simp [hi] at hv
        omega
      · simp [hi] at hv

lemma flowerPairColor_rel_ne {n : ℕ} (hn : 2 ≤ n) {a b : FlowerVertex n}
    (h : flowerRel n a b) : flowerPairColor n a ≠ flowerPairColor n b := by
  rcases h with ⟨i, ha, hb⟩ | ⟨i, ha, hb⟩ | ⟨i, ha, hb⟩ | ⟨i, ha, hb⟩
  · subst a
    subst b
    exact (Fin.castSucc_ne_last i).symm
  · subst a
    subst b
    exact fun heq => finRotate_ne_self_of_two_le hn i
      (Fin.castSucc_injective n heq).symm
  · subst a
    subst b
    exact fun heq => finRotate_ne_self_of_two_le hn i
      (Fin.castSucc_injective n heq).symm
  · subst a
    subst b
    exact (Fin.castSucc_ne_last ((finRotate n) i)).symm

def flowerPairColoring {n : ℕ} (hn : 2 ≤ n) :
    (flowerGraph n).Coloring (Fin (n + 1)) where
  toFun := flowerPairColor n
  map_rel' := by
    intro a b hab
    rw [flowerGraph, SimpleGraph.fromRel_adj] at hab
    rcases hab with ⟨_, h | h⟩
    · exact flowerPairColor_rel_ne hn h
    · exact (flowerPairColor_rel_ne hn h).symm

lemma flowerPairColoring_surjective {n : ℕ} (hn : 2 ≤ n) :
    Function.Surjective (flowerPairColoring hn) := by
  intro j
  by_cases hj : j = Fin.last n
  · refine ⟨Sum.inl (), ?_⟩
    simp [flowerPairColoring, flowerPairColor, hj]
  · obtain ⟨i, hi⟩ := Fin.eq_castSucc_of_ne_last hj
    refine ⟨Sum.inr (Sum.inl i), ?_⟩
    simp [flowerPairColoring, flowerPairColor, hi]

lemma flowerPairColor_colorClass_last (n : ℕ) :
    Set.ncard {x : FlowerVertex n | flowerPairColor n x = Fin.last n} = 1 := by
  have hset : {x : FlowerVertex n | flowerPairColor n x = Fin.last n} = {Sum.inl ()} := by
    ext x
    cases x with
    | inl u =>
        cases u
        simp [flowerPairColor]
    | inr x =>
        cases x with
        | inl i => simp [flowerPairColor, (Fin.castSucc_ne_last i).symm]
        | inr i => simp [flowerPairColor, (Fin.castSucc_ne_last ((finRotate n) i)).symm]
  rw [hset, Set.ncard_singleton]

lemma flowerPairColor_colorClass_castSucc (n : ℕ) (i : Fin n) :
    Set.ncard {x : FlowerVertex n | flowerPairColor n x = i.castSucc} = 2 := by
  let y : Fin n := (finRotate n).symm i
  have hset : {x : FlowerVertex n | flowerPairColor n x = i.castSucc} =
      {Sum.inr (Sum.inl i), Sum.inr (Sum.inr y)} := by
    ext x
    cases x with
    | inl u =>
        cases u
        simp [flowerPairColor, (Fin.castSucc_ne_last i).symm]
    | inr x =>
        cases x with
        | inl j =>
            simp [flowerPairColor, Fin.castSucc_injective n |>.eq_iff]
        | inr j =>
            simp [flowerPairColor, Fin.castSucc_injective n |>.eq_iff,
              Equiv.apply_eq_iff_eq_symm_apply, y]
  rw [hset]
  exact Set.ncard_pair (by simp)

lemma flowerPairColoring_equitable {n : ℕ} (hn : 2 ≤ n) :
    ∀ i j : Fin (n + 1),
      Nat.dist ((flowerPairColoring hn).colorClass i).ncard
        ((flowerPairColoring hn).colorClass j).ncard ≤ 1 := by
  intro i j
  have hi : ((flowerPairColoring hn).colorClass i).ncard = 1 ∨
      ((flowerPairColoring hn).colorClass i).ncard = 2 := by
    by_cases h : i = Fin.last n
    · left
      simp [SimpleGraph.Coloring.colorClass, flowerPairColoring, h,
        flowerPairColor_colorClass_last]
    · obtain ⟨a, ha⟩ := Fin.eq_castSucc_of_ne_last h
      right
      simp [SimpleGraph.Coloring.colorClass, flowerPairColoring, ← ha,
        flowerPairColor_colorClass_castSucc]
  have hj : ((flowerPairColoring hn).colorClass j).ncard = 1 ∨
      ((flowerPairColoring hn).colorClass j).ncard = 2 := by
    by_cases h : j = Fin.last n
    · left
      simp [SimpleGraph.Coloring.colorClass, flowerPairColoring, h,
        flowerPairColor_colorClass_last]
    · obtain ⟨a, ha⟩ := Fin.eq_castSucc_of_ne_last h
      right
      simp [SimpleGraph.Coloring.colorClass, flowerPairColoring, ← ha,
        flowerPairColor_colorClass_castSucc]
  rcases hi with hi | hi <;> rcases hj with hj | hj <;> rw [hi, hj] <;> decide

/- accepted add_to_file helper 2 -/
lemma flowerGraph_adj_center_rim (n : ℕ) (i : Fin n) :
    (flowerGraph n).Adj (Sum.inl () : FlowerVertex n) (Sum.inr (Sum.inl i)) := by
  rw [flowerGraph, SimpleGraph.fromRel_adj]
  constructor
  · simp
  · left
    left
    exact ⟨i, rfl, rfl⟩

lemma flowerGraph_adj_center_outer (n : ℕ) (i : Fin n) :
    (flowerGraph n).Adj (Sum.inl () : FlowerVertex n) (Sum.inr (Sum.inr i)) := by
  rw [flowerGraph, SimpleGraph.fromRel_adj]
  constructor
  · simp
  · left
    right
    right
    right
    exact ⟨i, rfl, rfl⟩

lemma flowerGraph_center_colorClass_singleton {n : ℕ} {β : Type}
    (f : (flowerGraph n).Coloring β) :
    f.colorClass (f (Sum.inl () : FlowerVertex n)) = {Sum.inl ()} := by
  ext x
  constructor
  · intro hx
    cases x with
    | inl u =>
        cases u
        rfl
    | inr x =>
        cases x with
        | inl i =>
            exfalso
            exact f.valid (flowerGraph_adj_center_rim n i) hx.symm
        | inr i =>
            exfalso
            exact f.valid (flowerGraph_adj_center_outer n i) hx.symm
  · intro hx
    simp at hx
    simp [SimpleGraph.Coloring.colorClass, hx]

lemma FlowerVertex_card (n : ℕ) :
    Fintype.card (FlowerVertex n) = 2 * n + 1 := by
  simp [FlowerVertex]
  omega

lemma Set.ncard_eq_filter_card {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (f : α → β) (b : β) :
    Set.ncard {a : α | f a = b} = (Finset.univ.filter fun a => f a = b).card := by
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext a
  simp

lemma sum_ncard_colorClass {V β : Type} [Fintype V] [DecidableEq V]
    [Fintype β] [DecidableEq β] {G : SimpleGraph V} (f : G.Coloring β) :
    ∑ i : β, (f.colorClass i).ncard = Fintype.card V := by
  have hpoint : ∀ i : β, (f.colorClass i).ncard =
      (Finset.univ.filter fun x : V => f x = i).card := by
    intro i
    exact Set.ncard_eq_filter_card f i
  calc
    ∑ i : β, (f.colorClass i).ncard
        = ∑ i : β, (Finset.univ.filter fun x : V => f x = i).card := by
            exact Finset.sum_congr rfl fun i _ => hpoint i
    _ = ∑ i : β, ∑ x ∈ Finset.univ.filter (fun x : V => f x = i), 1 := by
            simp
    _ = ∑ x : V, 1 := Finset.sum_fiberwise Finset.univ f (fun _ : V => (1 : ℕ))
    _ = Fintype.card V := (Fintype.card_eq_sum_ones (α := V)).symm

lemma flowerGraph_color_lower {n ℓ : ℕ} (f : (flowerGraph n).Coloring (Fin ℓ))
    (hsurj : Function.Surjective f)
    (heq : ∀ i j : Fin ℓ,
      Nat.dist (f.colorClass i).ncard (f.colorClass j).ncard ≤ 1) :
    n + 1 ≤ ℓ := by
  classical
  let s : Fin ℓ → ℕ := fun i => (f.colorClass i).ncard
  have hcenter_set := flowerGraph_center_colorClass_singleton f
  have hcenter : s (f (Sum.inl () : FlowerVertex n)) = 1 := by
    simp [s, hcenter_set]
  have hpos : ∀ i : Fin ℓ, 0 < s i := by
    intro i
    obtain ⟨x, hx⟩ := hsurj i
    apply (Set.ncard_pos).mpr
    exact ⟨x, by simpa [SimpleGraph.Coloring.colorClass, s] using hx⟩
  have hsle : ∀ i : Fin ℓ, s i ≤ 2 := by
    intro i
    have hd := heq (f (Sum.inl () : FlowerVertex n)) i
    change Nat.dist (s (f (Sum.inl () : FlowerVertex n))) (s i) ≤ 1 at hd
    rw [hcenter, Nat.dist] at hd
    have hp := hpos i
    omega
  have hsum := sum_ncard_colorClass f
  have hbound : ∑ i : Fin ℓ, s i ≤ ∑ i : Fin ℓ, 2 := by
    exact Finset.sum_le_sum fun i _ => hsle i
  rw [FlowerVertex_card] at hsum
  change ∑ i : Fin ℓ, s i = 2 * n + 1 at hsum
  have hbound' : ∑ i : Fin ℓ, s i ≤ ℓ * 2 := by
    simpa using hbound
  omega

/- accepted add_to_file helper 3 -/
lemma flowerGraph_min_color_class_sizes {n : ℕ}
    (f : (flowerGraph n).Coloring (Fin (n + 1)))
    (hsurj : Function.Surjective f)
    (heq : ∀ i j : Fin (n + 1),
      Nat.dist (f.colorClass i).ncard (f.colorClass j).ncard ≤ 1)
    (hsort : ∀ i j : Fin (n + 1), i ≤ j →
      (f.colorClass j).ncard ≤ (f.colorClass i).ncard) :
    (∀ i : Fin n, (f.colorClass i.castSucc).ncard = 2) ∧
      (f.colorClass (Fin.last n)).ncard = 1 := by
  classical
  let s : Fin (n + 1) → ℕ := fun i => (f.colorClass i).ncard
  have hcenter_set := flowerGraph_center_colorClass_singleton f
  have hcenter : s (f (Sum.inl () : FlowerVertex n)) = 1 := by
    simp [s, hcenter_set]
  have hpos : ∀ i : Fin (n + 1), 0 < s i := by
    intro i
    obtain ⟨x, hx⟩ := hsurj i
    apply (Set.ncard_pos).mpr
    exact ⟨x, by simpa [SimpleGraph.Coloring.colorClass, s] using hx⟩
  have hs12 : ∀ i : Fin (n + 1), s i = 1 ∨ s i = 2 := by
    intro i
    have hd := heq (f (Sum.inl () : FlowerVertex n)) i
    change Nat.dist (s (f (Sum.inl () : FlowerVertex n))) (s i) ≤ 1 at hd
    rw [hcenter, Nat.dist] at hd
    have hp := hpos i
    omega
  have hsum := sum_ncard_colorClass f
  rw [FlowerVertex_card] at hsum
  change ∑ i : Fin (n + 1), s i = 2 * n + 1 at hsum
  have hdecomp : ∑ i : Fin (n + 1), s i =
      (n + 1) + (Finset.univ.filter fun i => s i = 2).card := by
    calc
      ∑ i : Fin (n + 1), s i
          = ∑ i : Fin (n + 1), (1 + if s i = 2 then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro i _
              rcases hs12 i with hi | hi <;> simp [hi]
      _ = (∑ i : Fin (n + 1), (1 : ℕ)) +
            ∑ i : Fin (n + 1), (if s i = 2 then 1 else 0) := by
              rw [Finset.sum_add_distrib]
      _ = (n + 1) + (Finset.univ.filter fun i => s i = 2).card := by
              simp
  have hfilter : (Finset.univ.filter fun i => s i = 2).card = n := by
    omega
  have hnotcard : (Finset.univ.filter fun i => ¬ s i = 2).card = 1 := by
    have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (p := fun i : Fin (n + 1) => s i = 2)
    have huniv : (Finset.univ : Finset (Fin (n + 1))).card = n + 1 := by simp
    omega
  obtain ⟨i, hi_mem⟩ := Finset.card_pos.mp (by
    rw [hnotcard]
    norm_num : 0 < (Finset.univ.filter fun i => ¬ s i = 2).card)
  have hi_not2 : ¬ s i = 2 := by
    simpa using hi_mem
  have hi1 : s i = 1 := by
    rcases hs12 i with h | h
    · exact h
    · exact False.elim (hi_not2 h)
  have hlast : s (Fin.last n) = 1 := by
    have hle := hsort i (Fin.last n) (Fin.le_last i)
    change s (Fin.last n) ≤ s i at hle
    rw [hi1] at hle
    have hp := hpos (Fin.last n)
    omega
  have hunique : ∀ a b : Fin (n + 1), ¬ s a = 2 → ¬ s b = 2 → a = b := by
    have hle1 : (Finset.univ.filter fun i => ¬ s i = 2).card ≤ 1 := by omega
    have hu := Finset.card_le_one.mp hle1
    intro a b ha hb
    exact hu a (by simpa using ha) b (by simpa using hb)
  have hcast : ∀ a : Fin n, s a.castSucc = 2 := by
    intro a
    by_contra hnot
    have heqind := hunique a.castSucc (Fin.last n) hnot (by omega)
    exact Fin.castSucc_ne_last a heqind
  constructor
  · intro a
    exact hcast a
  · exact hlast

/- accepted add_to_file helper 4 -/
lemma sum_comp_colorClass {V β : Type} [Fintype V] [DecidableEq V]
    [Fintype β] [DecidableEq β] {G : SimpleGraph V}
    (f : G.Coloring β) (Y : β → ℝ) :
    ∑ x : V, Y (f x) = ∑ i : β, ((f.colorClass i).ncard : ℝ) * Y i := by
  have hfib := Finset.sum_fiberwise (s := Finset.univ) (g := f)
    (f := fun x : V => Y (f x))
  calc
    ∑ x : V, Y (f x) = ∑ i : β,
        ∑ x ∈ Finset.univ.filter (fun x : V => f x = i), Y (f x) := hfib.symm
    _ = ∑ i : β, ((Finset.univ.filter fun x : V => f x = i).card : ℝ) * Y i := by
          apply Finset.sum_congr rfl
          intro i _
          have hconst :
              (∑ x ∈ Finset.univ.filter (fun x : V => f x = i), Y (f x)) =
              ∑ x ∈ Finset.univ.filter (fun x : V => f x = i), Y i := by
            apply Finset.sum_congr rfl
            intro x hx
            simp at hx
            simp [hx]
          rw [hconst]
          simp [mul_comm]
    _ = ∑ i : β, ((f.colorClass i).ncard : ℝ) * Y i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← Set.ncard_eq_filter_card f i]
          rfl

lemma uniformPMF_integral_color_comp {V β : Type} [Fintype V] [Nonempty V]
    [DecidableEq V] [Fintype β] [DecidableEq β] {G : SimpleGraph V}
    (f : G.Coloring β) (Y : β → ℝ) :
    @MeasureTheory.integral V ℝ _ _ ⊤
      (@PMF.toMeasure V ⊤ (PMF.uniformOfFintype V)) (fun x => Y (f x)) =
    (∑ i : β, ((f.colorClass i).ncard : ℝ) * Y i) / (Fintype.card V : ℝ) := by
  letI : MeasurableSpace V := ⊤
  rw [PMF.integral_eq_sum]
  have hpoint : ∀ x : V, ((PMF.uniformOfFintype V) x).toReal • Y (f x) =
      ((Fintype.card V : ℝ)⁻¹) * Y (f x) := by
    intro x
    simp [PMF.uniformOfFintype_apply]
  calc
    ∑ a : V, ((PMF.uniformOfFintype V) a).toReal • Y (f a)
        = ∑ a : V, ((Fintype.card V : ℝ)⁻¹) * Y (f a) := by
            exact Finset.sum_congr rfl fun x _ => hpoint x
    _ = ((Fintype.card V : ℝ)⁻¹) * ∑ x : V, Y (f x) := by
            rw [Finset.mul_sum]
    _ = ((Fintype.card V : ℝ)⁻¹) *
          ∑ i : β, ((f.colorClass i).ncard : ℝ) * Y i := by
            rw [sum_comp_colorClass f Y]
    _ = (∑ i : β, ((f.colorClass i).ncard : ℝ) * Y i) / (Fintype.card V : ℝ) := by
            ring

/- accepted add_to_file helper 5 -/
lemma two_mul_sum_range_add_one (n : ℕ) :
    2 * (∑ i ∈ Finset.range n, ((i : ℝ) + 1)) = (n : ℝ) * ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      rw [mul_add, ih]
      push_cast
      ring

lemma six_mul_sum_range_add_one_sq (n : ℕ) :
    6 * (∑ i ∈ Finset.range n, (((i : ℝ) + 1) ^ 2)) =
      (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      rw [mul_add, ih]
      push_cast
      ring_nf

lemma flower_weighted_sum_first {n : ℕ}
    {f : (flowerGraph n).Coloring (Fin (n + 1))}
    (hcast : ∀ i : Fin n, (f.colorClass i.castSucc).ncard = 2)
    (hlast : (f.colorClass (Fin.last n)).ncard = 1) :
    ∑ i : Fin (n + 1), ((f.colorClass i).ncard : ℝ) * ((i.val : ℝ) + 1) =
      ((n : ℝ) + 1) ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  have hfirst :
      (∑ i : Fin n, ((f.colorClass i.castSucc).ncard : ℝ) *
        ((i.castSucc.val : ℝ) + 1)) =
      2 * ∑ i : Fin n, ((i.val : ℝ) + 1) := by
    calc
      ∑ i : Fin n, ((f.colorClass i.castSucc).ncard : ℝ) *
          ((i.castSucc.val : ℝ) + 1)
          = ∑ i : Fin n, 2 * ((i.val : ℝ) + 1) := by
              apply Finset.sum_congr rfl
              intro i _
              simp [hcast i]
      _ = 2 * ∑ i : Fin n, ((i.val : ℝ) + 1) := by
              rw [Finset.mul_sum]
  rw [hfirst]
  have hlastval :
      ((f.colorClass (Fin.last n)).ncard : ℝ) * (((Fin.last n).val : ℝ) + 1) =
      (n : ℝ) + 1 := by
    simp [hlast]
  rw [hlastval]
  rw [Fin.sum_univ_eq_sum_range (fun i => ((i : ℝ) + 1)) n]
  have h2 := two_mul_sum_range_add_one n
  nlinarith

lemma flower_weighted_sum_second {n : ℕ}
    {f : (flowerGraph n).Coloring (Fin (n + 1))}
    (hcast : ∀ i : Fin n, (f.colorClass i.castSucc).ncard = 2)
    (hlast : (f.colorClass (Fin.last n)).ncard = 1) :
    ∑ i : Fin (n + 1), ((f.colorClass i).ncard : ℝ) * (((i.val : ℝ) + 1) ^ 2) =
      ((n : ℝ) ^ 4 + 2 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 + (n : ℝ)) /
        (3 * (2 * (n : ℝ) + 1)) + ((n : ℝ) + 1) ^ 4 / (2 * (n : ℝ) + 1) := by
  rw [Fin.sum_univ_castSucc]
  have hfirst :
      (∑ i : Fin n, ((f.colorClass i.castSucc).ncard : ℝ) *
        (((i.castSucc.val : ℝ) + 1) ^ 2)) =
      2 * ∑ i : Fin n, (((i.val : ℝ) + 1) ^ 2) := by
    calc
      ∑ i : Fin n, ((f.colorClass i.castSucc).ncard : ℝ) *
          (((i.castSucc.val : ℝ) + 1) ^ 2)
          = ∑ i : Fin n, 2 * (((i.val : ℝ) + 1) ^ 2) := by
              apply Finset.sum_congr rfl
              intro i _
              simp [hcast i]
      _ = 2 * ∑ i : Fin n, (((i.val : ℝ) + 1) ^ 2) := by
              rw [Finset.mul_sum]
  rw [hfirst]
  have hlastval :
      ((f.colorClass (Fin.last n)).ncard : ℝ) * ((((Fin.last n).val : ℝ) + 1) ^ 2) =
      ((n : ℝ) + 1) ^ 2 := by
    simp [hlast]
  rw [hlastval]
  rw [Fin.sum_univ_eq_sum_range (fun i => (((i : ℝ) + 1) ^ 2)) n]
  have h6 := six_mul_sum_range_add_one_sq n
  have h2S : 2 * (∑ i ∈ Finset.range n, (((i : ℝ) + 1) ^ 2)) =
      (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / 3 := by
    nlinarith
  rw [h2S]
  have hden : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hden]
  ring

/- accepted add_to_file helper 6 -/
lemma flower_graph_moments_of_min {n : ℕ}
    (f : (flowerGraph n).Coloring (Fin (n + 1)))
    (hsurj : Function.Surjective f)
    (heq : ∀ i j : Fin (n + 1),
      Nat.dist (f.colorClass i).ncard (f.colorClass j).ncard ≤ 1)
    (hsort : ∀ i j : Fin (n + 1), i ≤ j →
      (f.colorClass j).ncard ≤ (f.colorClass i).ncard) :
    let X : FlowerVertex n → ℝ := fun x => (↑((f x).val + 1) : ℝ)
    let μ := @PMF.toMeasure (FlowerVertex n) ⊤ (PMF.uniformOfFintype (FlowerVertex n))
    @MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ X =
        ((n : ℝ) + 1) ^ 2 / (2 * (n : ℝ) + 1) ∧
      @ProbabilityTheory.variance (FlowerVertex n) ⊤ X μ =
        ((n : ℝ) ^ 4 + 2 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 + (n : ℝ)) /
          (3 * (2 * (n : ℝ) + 1) ^ 2) := by
  classical
  let X : FlowerVertex n → ℝ := fun x => (↑((f x).val + 1) : ℝ)
  let μ := @PMF.toMeasure (FlowerVertex n) ⊤ (PMF.uniformOfFintype (FlowerVertex n))
  obtain ⟨hcast, hlast⟩ := flowerGraph_min_color_class_sizes f hsurj heq hsort
  have hweighted1 := flower_weighted_sum_first (f := f) hcast hlast
  have hweighted2 := flower_weighted_sum_second (f := f) hcast hlast
  have hN : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have hmean : @MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ X =
      ((n : ℝ) + 1) ^ 2 / (2 * (n : ℝ) + 1) := by
    have h := uniformPMF_integral_color_comp (V := FlowerVertex n)
      (β := Fin (n + 1)) (G := flowerGraph n) f
      (fun i => ((i.val : ℝ) + 1))
    calc
      @MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ X
          = (∑ i : Fin (n + 1), ((f.colorClass i).ncard : ℝ) *
              ((i.val : ℝ) + 1)) / (Fintype.card (FlowerVertex n) : ℝ) := by
                simpa [X, μ] using h
      _ = ((n : ℝ) + 1) ^ 2 / (2 * (n : ℝ) + 1) := by
              rw [hweighted1, FlowerVertex_card]
              norm_num
  have hsecond : @MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ (fun x => X x ^ 2) =
      ((n : ℝ) ^ 4 + 2 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 + (n : ℝ)) /
          (3 * (2 * (n : ℝ) + 1) ^ 2) +
        ((n : ℝ) + 1) ^ 4 / ((2 * (n : ℝ) + 1) ^ 2) := by
    have h := uniformPMF_integral_color_comp (V := FlowerVertex n)
      (β := Fin (n + 1)) (G := flowerGraph n) f
      (fun i => (((i.val : ℝ) + 1) ^ 2))
    calc
      @MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ (fun x => X x ^ 2)
          = (∑ i : Fin (n + 1), ((f.colorClass i).ncard : ℝ) *
              (((i.val : ℝ) + 1) ^ 2)) / (Fintype.card (FlowerVertex n) : ℝ) := by
                simpa [X, μ] using h
      _ = ((n : ℝ) ^ 4 + 2 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 + (n : ℝ)) /
            (3 * (2 * (n : ℝ) + 1) ^ 2) +
          ((n : ℝ) + 1) ^ 4 / ((2 * (n : ℝ) + 1) ^ 2) := by
            rw [hweighted2, FlowerVertex_card]
            field_simp [hN]
            ring_nf
            norm_num
  have hmem : MeasureTheory.MemLp X 2 μ := by
    exact MeasureTheory.MemLp.of_discrete
  have hvar : @ProbabilityTheory.variance (FlowerVertex n) ⊤ X μ =
      @MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ (fun x => X x ^ 2) -
        (@MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ X) ^ 2 := by
    have hv := ProbabilityTheory.variance_eq_sub (μ := μ) (X := X) hmem
    simpa [pow_two] using hv
  constructor
  · exact hmean
  · calc
      @ProbabilityTheory.variance (FlowerVertex n) ⊤ X μ
          = @MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ (fun x => X x ^ 2) -
              (@MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ X) ^ 2 := hvar
      _ = (((n : ℝ) ^ 4 + 2 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 + (n : ℝ)) /
              (3 * (2 * (n : ℝ) + 1) ^ 2) +
            ((n : ℝ) + 1) ^ 4 / ((2 * (n : ℝ) + 1) ^ 2)) -
            (((n : ℝ) + 1) ^ 2 / (2 * (n : ℝ) + 1)) ^ 2 := by
              rw [hsecond, hmean]
      _ = ((n : ℝ) ^ 4 + 2 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 + (n : ℝ)) /
            (3 * (2 * (n : ℝ) + 1) ^ 2) := by
              field_simp [hN]
              ring

/- verified submission -/
theorem flower_graph_equitable_coloring_moments
    (n k : ℕ) (hn : 3 ≤ n) :
    let V := Unit ⊕ (Fin n ⊕ Fin n)
    let F : SimpleGraph V := SimpleGraph.fromRel fun a b =>
      (∃ i : Fin n, a = Sum.inl () ∧ b = Sum.inr (Sum.inl i)) ∨
      (∃ i : Fin n,
        a = Sum.inr (Sum.inl i) ∧
          b = Sum.inr (Sum.inl ((finRotate n) i))) ∨
      (∃ i : Fin n, a = Sum.inr (Sum.inl i) ∧ b = Sum.inr (Sum.inr i)) ∨
      (∃ i : Fin n, a = Sum.inl () ∧ b = Sum.inr (Sum.inr i))
    ∀ f : F.Coloring (Fin k),
      Function.Surjective f →
      (∀ i j : Fin k,
        Nat.dist (f.colorClass i).ncard (f.colorClass j).ncard ≤ 1) →
      (∀ ℓ : ℕ, ℓ < k →
        ¬ ∃ g : F.Coloring (Fin ℓ),
          Function.Surjective g ∧
          (∀ i j : Fin ℓ,
            Nat.dist (g.colorClass i).ncard (g.colorClass j).ncard ≤ 1)) →
      (∀ i j : Fin k, i ≤ j →
        (f.colorClass j).ncard ≤ (f.colorClass i).ncard) →
      let X : V → ℝ := fun x => (↑((f x).val + 1) : ℝ)
      let μ := @PMF.toMeasure V ⊤ (PMF.uniformOfFintype V)
      @MeasureTheory.integral V ℝ _ _ ⊤ μ X =
          ((n : ℝ) + 1) ^ 2 / (2 * (n : ℝ) + 1) ∧
        @ProbabilityTheory.variance V ⊤ X μ =
          ((n : ℝ) ^ 4 + 2 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 + (n : ℝ)) /
            (3 * (2 * (n : ℝ) + 1) ^ 2) := by
  classical
  intro V F f hsurj heq hmin hsort
  have h2n : 2 ≤ n := by omega
  have hk_lower : n + 1 ≤ k :=
    flowerGraph_color_lower f hsurj heq
  have hk_upper : k ≤ n + 1 := by
    by_contra h
    have hlt : n + 1 < k := Nat.lt_of_not_ge h
    exact hmin (n + 1) hlt
      ⟨flowerPairColoring h2n, flowerPairColoring_surjective h2n,
        flowerPairColoring_equitable h2n⟩
  have hk : k = n + 1 := le_antisymm hk_upper hk_lower
  subst k
  exact flower_graph_moments_of_min f hsurj heq hsort

end Rollout_p1268_flower_graph_equitable_coloring_moments

namespace Rollout_p2468_average_projection_positive_definite

/- verified submission -/
theorem average_projection_positive_definite
    {n : ℕ} (hn : 1 ≤ n)
    {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (C : ι → Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hC : ⨆ i, C i = ⊤)
    (J : Ω → Finset ι)
    (hproj : Measurable (fun ω =>
      (∑ i ∈ J ω, C i).starProjection))
    (hadm : ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 →
      μ {ω | x ∈ (∑ i ∈ J ω, C i)ᗮ} < 1) :
    ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 →
      0 < inner ℝ x
        ((∫ ω, (∑ i ∈ J ω, C i).starProjection ∂μ) x) := by
  intro x hx
  let K : Ω → Submodule ℝ (EuclideanSpace ℝ (Fin n)) := fun ω => ∑ i ∈ J ω, C i
  have hPint : MeasureTheory.Integrable (fun ω => (K ω).starProjection) μ := by
    refine MeasureTheory.Integrable.of_bound hproj.aestronglyMeasurable 1 ?_
    filter_upwards with ω
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
    intro v
    simpa using Submodule.norm_starProjection_apply_le (K ω) v
  have hφint : MeasureTheory.Integrable (fun ω => (K ω).starProjection x) μ :=
    hPint.apply_continuousLinearMap x
  have hfint : MeasureTheory.Integrable (fun ω => inner ℝ x ((K ω).starProjection x)) μ :=
    MeasureTheory.Integrable.const_inner x hφint
  have hfmeas : Measurable (fun ω => inner ℝ x ((K ω).starProjection x)) :=
    Measurable.const_inner (hproj.apply_continuousLinearMap x)
  have hnonneg : 0 ≤ fun ω => inner ℝ x ((K ω).starProjection x) := by
    intro ω
    have h := Submodule.re_inner_starProjection_nonneg (K ω) x
    convert h using 1
    rw [real_inner_comm]
    rfl
  have hnormsq (ω : Ω) :
      inner ℝ x ((K ω).starProjection x) = ‖(K ω).orthogonalProjection x‖ ^ 2 := by
    have h := Submodule.re_inner_starProjection_eq_normSq (K ω) x
    convert h using 1
    · rw [real_inner_comm]
      rfl
  have hsupp : Function.support (fun ω => inner ℝ x ((K ω).starProjection x)) =
      {ω | x ∈ (K ω)ᗮ}ᶜ := by
    ext ω
    constructor
    · intro hsupport horth
      have hsne : inner ℝ x ((K ω).starProjection x) ≠ 0 := Function.mem_support.mp hsupport
      have hpzero : (K ω).starProjection x = 0 :=
        (Submodule.starProjection_apply_eq_zero_iff (K ω)).2 horth
      exact hsne (by simp [hpzero])
    · intro hnotorth
      rw [Function.mem_support]
      by_contra hinner
      have hsquarezero : ‖(K ω).orthogonalProjection x‖ ^ 2 = 0 := by
        rw [← hnormsq ω, hinner]
      have hprojzero : (K ω).orthogonalProjection x = 0 := by
        have hnormzero : ‖(K ω).orthogonalProjection x‖ = 0 :=
          eq_zero_of_pow_eq_zero hsquarezero
        exact norm_eq_zero.mp hnormzero
      exact hnotorth ((Submodule.orthogonalProjection_eq_zero_iff).1 hprojzero)
  have hbad_meas : MeasurableSet {ω | x ∈ (K ω)ᗮ} := by
    have h := (measurableSet_support hfmeas).compl
    rwa [hsupp, compl_compl] at h
  have hsupp_pos :
      0 < μ (Function.support (fun ω => inner ℝ x ((K ω).starProjection x))) := by
    have hcomp : 0 < μ {ω | x ∈ (K ω)ᗮ}ᶜ := by
      rw [MeasureTheory.prob_compl_eq_one_sub hbad_meas]
      exact tsub_pos_iff_lt.2 (hadm x hx)
    rwa [hsupp]
  have hintpos : 0 < ∫ ω, inner ℝ x ((K ω).starProjection x) ∂μ :=
    (MeasureTheory.integral_pos_iff_support_of_nonneg hnonneg hfint).2 hsupp_pos
  calc
    0 < ∫ ω, inner ℝ x ((K ω).starProjection x) ∂μ := hintpos
    _ = inner ℝ x (∫ ω, (K ω).starProjection x ∂μ) := integral_inner hφint x
    _ = inner ℝ x ((∫ ω, (K ω).starProjection ∂μ) x) := by
      rw [ContinuousLinearMap.integral_apply hPint x]

end Rollout_p2468_average_projection_positive_definite

namespace Rollout_p0968_unique_nonzero_zero_of_exponential_factori

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

end Rollout_p0968_unique_nonzero_zero_of_exponential_factori

namespace Rollout_p0617_sqrt_two_weighted_sum_lt

/- accepted add_to_file helper 1 -/

open Finset Real

noncomputable section

def wsum (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), ((n - j : ℕ) : ℝ) * (Real.sqrt 2) ^ j

lemma wsum_succ (n : ℕ) :
    wsum (n + 1) = wsum n + ∑ j ∈ Finset.range (n + 1), (Real.sqrt 2) ^ j := by
  unfold wsum
  rw [Finset.sum_range_succ]
  have hlast : ((n + 1 - (n + 1) : ℕ) : ℝ) * (Real.sqrt 2) ^ (n + 1) = 0 := by simp
  rw [hlast, add_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hnat : n + 1 - j = n - j + 1 := by omega
  rw [hnat]
  norm_num [pow_succ, add_mul, one_mul]

lemma wsum_eq (n : ℕ) :
    wsum n =
      ((Real.sqrt 2) ^ (n + 1) + (n : ℝ) - ((n + 1 : ℕ) : ℝ) * Real.sqrt 2) *
        (Real.sqrt 2 + 1) ^ 2 := by
  induction n with
  | zero =>
      simp [wsum]
  | succ n ih =>
      rw [wsum_succ n, geom_sum_eq, ih]
      · rw [div_eq_mul_inv, Real.inv_sqrt_two_sub_one]
        have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        have h3 : (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 := by
          rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, h2]
        have h4 : (Real.sqrt 2) ^ 4 = 4 := by
          rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, h2]
          norm_num
        ring_nf
        simp only [h2, h3, h4]
        push_cast
        ring
      · exact Real.one_lt_sqrt_two.ne'

/- verified submission -/
theorem sqrt_two_weighted_sum_lt (i : ℕ) :
    (∑ j ∈ Finset.range (i + 1), ((i - j : ℕ) : ℝ) * (Real.sqrt 2) ^ j) <
      (4 + 3 * Real.sqrt 2) * (Real.sqrt 2) ^ i := by
  change wsum i < (4 + 3 * Real.sqrt 2) * (Real.sqrt 2) ^ i
  let r : ℝ := Real.sqrt 2
  let q : ℝ := (r + 1) ^ 2
  let b : ℝ := ((i + 1 : ℕ) : ℝ) * r - (i : ℝ)
  have hr_gt_one : 1 < r := by
    dsimp [r]
    exact Real.one_lt_sqrt_two
  have hr_pos : 0 < r := lt_trans zero_lt_one hr_gt_one
  have hsq : r ^ 2 = 2 := by
    dsimp [r]
    exact Real.sq_sqrt (by norm_num)
  have hcube : r ^ 3 = 2 * r := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, hsq]
  have htarget : (4 + 3 * r) * r ^ i = r ^ (i + 1) * q := by
    have hrq : r * q = 4 + 3 * r := by
      dsimp [q]
      ring_nf
      rw [hcube, hsq]
      ring
    calc
      (4 + 3 * r) * r ^ i = (r * q) * r ^ i := by rw [hrq]
      _ = r ^ (i + 1) * q := by
        rw [pow_succ]
        ring
  have hdiff : (4 + 3 * r) * r ^ i - wsum i = b * q := by
    rw [wsum_eq i]
    dsimp [r, q, b]
    rw [htarget]
    dsimp [r, q]
    push_cast
    ring
  have hb : 0 < b := by
    have hnonneg : 0 ≤ (i : ℝ) * (r - 1) := by
      exact mul_nonneg (Nat.cast_nonneg i) (sub_nonneg.mpr hr_gt_one.le)
    have hsumpos : 0 < (i : ℝ) * (r - 1) + r :=
      add_pos_of_nonneg_of_pos hnonneg hr_pos
    have hb_eq : b = (i : ℝ) * (r - 1) + r := by
      dsimp [b]
      push_cast
      ring
    rw [hb_eq]
    exact hsumpos
  have hq : 0 < q := by
    dsimp [q]
    exact sq_pos_of_pos (add_pos hr_pos zero_lt_one)
  have hdiff_pos : 0 < (4 + 3 * r) * r ^ i - wsum i := by
    rw [hdiff]
    exact mul_pos hb hq
  dsimp [r] at hdiff_pos
  linarith

/- Scopes closed implicitly by EOF in the original file. -/
end

end Rollout_p0617_sqrt_two_weighted_sum_lt

namespace Rollout_p1662_binary_quadratic_form_volume_identity

/- accepted add_to_file helper 1 -/
lemma quadratic_root_gt_one {A B C q : ℝ}
    (hA : 0 < A) (hC : C < 0) (h1 : A + B + C < 0)
    (hqpos : 0 < q) (hqroot : A * q ^ 2 + B * q + C = 0) :
    1 < q := by
  have hAne : A ≠ 0 := ne_of_gt hA
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hfactor : A + B + C = A * (1 - q) * (1 - C / (A * q)) := by
    field_simp [hAne, hqne]
    nlinarith [hqroot]
  have hAq : 0 < A * q := mul_pos hA hqpos
  have hfrac : C / (A * q) < 0 := div_neg_of_neg_of_pos hC hAq
  have hy : 0 < 1 - C / (A * q) := by linarith
  have hprod : A * (1 - q) * (1 - C / (A * q)) < 0 := by
    rw [← hfactor]
    exact h1
  have hAX : A * (1 - q) < 0 := by
    exact neg_of_mul_neg_left hprod hy.le
  have hx : 1 - q < 0 := by
    exact neg_of_mul_neg_right hAX hA.le
  linarith

lemma transformed_root_relation {A B C lam mu : ℝ}
    (hA : 0 < A) (hC : C < 0)
    (hlampos : 0 < lam)
    (hlamroot : A * lam ^ 2 + B * lam + C = 0)
    (hmuunique : ∀ x : ℝ, 0 < x →
      A * x ^ 2 + (-2 * A - B) * x + (A + B + C) = 0 → x = mu) :
    1 - C / (A * lam) = mu := by
  have hAne : A ≠ 0 := ne_of_gt hA
  have hlamne : lam ≠ 0 := ne_of_gt hlampos
  let r : ℝ := C / (A * lam)
  have hrneg : r < 0 := by
    dsimp [r]
    exact div_neg_of_neg_of_pos hC (mul_pos hA hlampos)
  have hother : A * r ^ 2 + B * r + C = 0 := by
    dsimp [r]
    field_simp [hAne, hlamne]
    nlinarith [hlamroot]
  have hxpos : 0 < 1 - r := by linarith
  have hxroot : A * (1 - r) ^ 2 + (-2 * A - B) * (1 - r) + (A + B + C) = 0 := by
    nlinarith [hother]
  have hx : 1 - r = mu := hmuunique (1-r) hxpos hxroot
  dsimp [r] at hx
  exact hx

/- accepted add_to_file helper 2 -/
lemma quadratic_volume_eq {A B C x : ℝ}
    (hA : 0 < A) (hC : C < 0) (h1 : A + B + C < 0)
    (hxpos : 0 < x) (hxgt : 1 < x)
    (hxroot : A * x ^ 2 + B * x + C = 0) :
    A * x * (x - 1) * (1 + 1 / x ^ 2 + 1 / (x - 1) ^ 2) =
      A * (x ^ 2 - x) + 2 * A + A * (A * x + B) / C -
        A * (A * x + A + B) / (A + B + C) := by
  have hAne : A ≠ 0 := ne_of_gt hA
  have hCne : C ≠ 0 := ne_of_lt hC
  have h1ne : A+B+C ≠0 := ne_of_lt h1
  have hxne : x≠0 := ne_of_gt hxpos
  have hx1ne : x-1≠0 := by nlinarith
  have hinvx : 1 / x = -(A * x + B) / C := by
    field_simp [hCne,hxne]
    nlinarith [hxroot]
  have hinvx1 : 1 / (x-1) = -(A * x + A + B) / (A+B+C) := by
    field_simp [h1ne,hx1ne]
    nlinarith [hxroot]
  have hdecomp :
      A * x * (x - 1) * (1 + 1 / x ^ 2 + 1 / (x - 1) ^ 2) =
        A * (x ^ 2 - x) + A * (1 - 1 / x) + A * (1 + 1 / (x - 1)) := by
    field_simp [hxne,hx1ne]
    ring
  rw [hdecomp, hinvx, hinvx1]
  field_simp [hCne,h1ne]
  ring

/- accepted add_to_file helper 3 -/
lemma quadratic_sum_from_relation {A B C lam mu : ℝ}
    (hA : A ≠ 0)
    (hroot : A * lam ^ 2 + B * lam + C = 0)
    (hrel : mu = lam + 1 + B / A) :
    A * (lam ^ 2 - lam) + A * (mu ^ 2 - mu) =
      B + B ^ 2 / A - 2 * C := by
  have hrootA : A ^ 2 * lam ^ 2 + A * B * lam + A * C = 0 := by
    have h := congrArg (fun t : ℝ => A * t) hroot
    ring_nf at h ⊢
    exact h
  rw [hrel]
  field_simp [hA]
  ring_nf
  nlinarith [hrootA]

lemma rational_c_sum_from_relation {A B C lam mu : ℝ}
    (hA : A ≠ 0) (hC : C ≠ 0)
    (hrel : mu = lam + 1 + B / A) :
    A * (A * lam + B) / C -
        A * (A * mu - A - B) / C = A * B / C := by
  rw [hrel]
  field_simp [hA,hC]
  ring

lemma rational_d_sum_from_relation {A B C lam mu : ℝ}
    (hA : A ≠ 0) (hd : A+B+C ≠ 0)
    (hrel : mu = lam + 1 + B / A) :
    - A * (A * lam + A + B) / (A+B+C) +
        A * (A * mu - 2*A - B) / (A+B+C) =
      - A * (2*A+B)/(A+B+C) := by
  rw [hrel]
  field_simp [hA,hd]
  ring

/- verified submission -/
theorem binary_quadratic_form_volume_identity
    (D a b c : ℤ) (lam mu : ℝ)
    (hDpos : 0 < D)
    (hDnsq : ¬ IsSquare D)
    (hDmod : D % 4 = 0 ∨ D % 4 = 1)
    (hdisc : b ^ 2 - 4 * a * c = D)
    (ha : 0 < a)
    (hc : c < 0)
    (hsum : a + b + c < 0)
    (hlamroot : (a : ℝ) * lam ^ 2 + (b : ℝ) * lam + (c : ℝ) = 0)
    (hlampos : 0 < lam)
    (hlamunique : ∀ x : ℝ,
      0 < x → (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0 → x = lam)
    (hmuroot :
      (a : ℝ) * mu ^ 2 + ((-2 * a - b : ℤ) : ℝ) * mu +
        ((a + b + c : ℤ) : ℝ) = 0)
    (hmupos : 0 < mu)
    (hmuunique : ∀ x : ℝ,
      0 < x →
        (a : ℝ) * x ^ 2 + ((-2 * a - b : ℤ) : ℝ) * x +
          ((a + b + c : ℤ) : ℝ) = 0 →
        x = mu) :
    (a : ℝ) * lam * (lam - 1) *
          (1 + 1 / lam ^ 2 + 1 / (lam - 1) ^ 2) +
        (a : ℝ) * mu * (mu - 1) *
          (1 + 1 / mu ^ 2 + 1 / (mu - 1) ^ 2) =
      4 * (a : ℝ) + (b : ℝ) + (b : ℝ) ^ 2 / (a : ℝ) +
        (a : ℝ) * (b : ℝ) / (c : ℝ) - 2 * (c : ℝ) -
        (a : ℝ) * (2 * (a : ℝ) + (b : ℝ)) /
          ((a : ℝ) + (b : ℝ) + (c : ℝ)) := by
  have hA : 0 < (a : ℝ) := by exact_mod_cast ha
  have hC : (c : ℝ) < 0 := by exact_mod_cast hc
  have hsumR : (a : ℝ) + (b : ℝ) + (c : ℝ) < 0 := by exact_mod_cast hsum
  have hlamgt : 1 < lam :=
    quadratic_root_gt_one hA hC hsumR hlampos hlamroot
  have hmurootR :
      (a : ℝ) * mu ^ 2 + (-2 * (a : ℝ) - (b : ℝ)) * mu +
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) = 0 := by
    push_cast at hmuroot
    convert hmuroot using 1 <;> ring_nf
  have hmu_at_one :
      (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) +
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) < 0 := by
    have : (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) +
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) = (c : ℝ) := by ring
    rw [this]
    exact hC
  have hmu_gt : 1 < mu :=
    quadratic_root_gt_one hA hsumR hmu_at_one hmupos hmurootR
  have hmuunique' : ∀ x : ℝ, 0 < x →
      (a : ℝ) * x ^ 2 + (-2 * (a : ℝ) - (b : ℝ)) * x +
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) = 0 → x = mu := by
    intro x hx hxroot
    apply hmuunique x hx
    push_cast
    convert hxroot using 1 <;> ring_nf
  have hrel : 1 - (c : ℝ) / ((a : ℝ) * lam) = mu :=
    transformed_root_relation hA hC hlampos hlamroot hmuunique'
  have hAne : (a : ℝ) ≠ 0 := ne_of_gt hA
  have hlamne : lam ≠ 0 := ne_of_gt hlampos
  have hCne : (c : ℝ) ≠ 0 := ne_of_lt hC
  have hsumne : (a : ℝ) + (b : ℝ) + (c : ℝ) ≠ 0 := ne_of_lt hsumR
  have hcdiv : (c : ℝ) / ((a : ℝ) * lam) = -((b : ℝ) / (a : ℝ)) - lam := by
    field_simp [hAne,hlamne]
    nlinarith [hlamroot]
  have hmlin : mu = lam + 1 + (b : ℝ) / (a : ℝ) := by
    linarith [hrel,hcdiv]
  have hVlam := quadratic_volume_eq hA hC hsumR hlampos hlamgt hlamroot
  have hVmu := quadratic_volume_eq hA hsumR hmu_at_one hmupos hmu_gt hmurootR
  have hfmu : (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) +
      ((a : ℝ) + (b : ℝ) + (c : ℝ)) = (c : ℝ) := by ring
  rw [hfmu] at hVmu
  have hquad := quadratic_sum_from_relation hAne hlamroot hmlin
  have hrC := rational_c_sum_from_relation hAne hCne hmlin
  have hrD := rational_d_sum_from_relation hAne hsumne hmlin
  rw [hVlam, hVmu]
  have harrange :
      ((a : ℝ) * (lam ^ 2 - lam) + 2 * (a : ℝ) +
          (a : ℝ) * ((a : ℝ) * lam + (b : ℝ)) / (c : ℝ) -
          (a : ℝ) * ((a : ℝ) * lam + (a : ℝ) + (b : ℝ)) /
            ((a : ℝ) + (b : ℝ) + (c : ℝ))) +
        ((a : ℝ) * (mu ^ 2 - mu) + 2 * (a : ℝ) +
          (a : ℝ) * ((a : ℝ) * mu + (-2 * (a : ℝ) - (b : ℝ))) /
            ((a : ℝ) + (b : ℝ) + (c : ℝ)) -
          (a : ℝ) * ((a : ℝ) * mu + (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ))) /
            (c : ℝ)) =
      ((a : ℝ) * (lam ^ 2 - lam) + (a : ℝ) * (mu ^ 2 - mu)) +
        4 * (a : ℝ) +
        ((a : ℝ) * ((a : ℝ) * lam + (b : ℝ)) / (c : ℝ) -
          (a : ℝ) * ((a : ℝ) * mu - (a : ℝ) - (b : ℝ)) / (c : ℝ)) +
        (- (a : ℝ) * ((a : ℝ) * lam + (a : ℝ) + (b : ℝ)) /
            ((a : ℝ) + (b : ℝ) + (c : ℝ)) +
          (a : ℝ) * ((a : ℝ) * mu - 2 * (a : ℝ) - (b : ℝ)) /
            ((a : ℝ) + (b : ℝ) + (c : ℝ))) := by
    ring
  rw [harrange, hquad, hrC, hrD]
  ring

end Rollout_p1662_binary_quadratic_form_volume_identity

namespace Rollout_p1552_index_two_infinite_cyclic_classification

/- accepted add_to_file helper 1 -/

open Subgroup

/-- Two-sided normal forms for a group generated by an involution and a conjugated generator. -/
def twoSidedNF {G : Type*} [Group G] (a b : G) : Set G :=
  {x | ∃ c : Bool, ∃ k : ℤ, x = if c then a * b ^ k else b ^ k}

lemma one_mem_twoSidedNF {G : Type*} [Group G] (a b : G) :
    (1 : G) ∈ twoSidedNF a b := by
  refine ⟨false, 0, ?_⟩
  simp

lemma generator_left_mem_twoSidedNF {G : Type*} [Group G] (a b : G) :
    a ∈ twoSidedNF a b := by
  refine ⟨true, 0, ?_⟩
  simp

lemma generator_right_mem_twoSidedNF {G : Type*} [Group G] (a b : G) :
    b ∈ twoSidedNF a b := by
  refine ⟨false, 1, ?_⟩
  simp

lemma zpow_conjugate_eq_neg {G : Type*} [Group G] {a b : G}
    (hconj : a * b * a⁻¹ = b⁻¹) (k : ℤ) :
    a * b ^ k = b ^ (-k) * a := by
  have h : (a * b * a⁻¹) ^ k = (b⁻¹) ^ k := congrArg (fun x => x ^ k) hconj
  rw [conj_zpow] at h
  calc
    a * b ^ k = (a * b ^ k * a⁻¹) * a := by group
    _ = (b⁻¹) ^ k * a := by rw [h]
    _ = b ^ (-k) * a := by rw [inv_zpow']

lemma zpow_mul_eq_left {G : Type*} [Group G] {a b : G}
    (hconj : a * b * a⁻¹ = b⁻¹) (k : ℤ) :
    b ^ k * a = a * b ^ (-k) := by
  simpa using (zpow_conjugate_eq_neg hconj (-k)).symm

/- accepted add_to_file helper 2 -/
lemma twoSidedNF_mul_of_inversion {G : Type*} [Group G] {a b : G}
    (hconj : a * b * a⁻¹ = b⁻¹) (hsq : a * a = 1)
    {x y : G} (hx : x ∈ twoSidedNF a b) (hy : y ∈ twoSidedNF a b) :
    x * y ∈ twoSidedNF a b := by
  rcases hx with ⟨cx, k, rfl⟩
  rcases hy with ⟨cy, l, rfl⟩
  cases cx <;> cases cy
  · refine ⟨false, k + l, ?_⟩
    simp [zpow_add]
  · refine ⟨true, l - k, ?_⟩
    simp
    calc
      b ^ k * (a * b ^ l) = (b ^ k * a) * b ^ l := by group
      _ = (a * b ^ (-k)) * b ^ l := by rw [zpow_mul_eq_left hconj]
      _ = a * b ^ (l - k) := by
        rw [mul_assoc, ← zpow_add]
        ring_nf
  · refine ⟨true, k + l, ?_⟩
    simp
    rw [mul_assoc, ← zpow_add]
  · refine ⟨false, l - k, ?_⟩
    simp
    calc
      (a * b ^ k) * (a * b ^ l) = ((a * b ^ k) * a) * b ^ l := by group
      _ = ((b ^ (-k) * a) * a) * b ^ l := by rw [zpow_conjugate_eq_neg hconj]
      _ = (b ^ (-k) * (a * a)) * b ^ l := by group
      _ = b ^ (l - k) := by
        rw [hsq, mul_one, ← zpow_add]
        ring_nf

lemma twoSidedNF_inv_of_inversion {G : Type*} [Group G] {a b : G}
    (hconj : a * b * a⁻¹ = b⁻¹) (hsq : a * a = 1)
    {x : G} (hx : x ∈ twoSidedNF a b) :
    x⁻¹ ∈ twoSidedNF a b := by
  rcases hx with ⟨c, k, rfl⟩
  cases c
  · refine ⟨false, -k, ?_⟩
    simp [zpow_neg]
  · have hainv : a⁻¹ = a := by
      apply inv_eq_of_mul_eq_one_left hsq
    refine ⟨true, k, ?_⟩
    simp only [↓reduceIte]
    calc
      (a * b ^ k)⁻¹ = b ^ (-k) * a := by
        rw [mul_inv_rev, hainv, zpow_neg]
      _ = a * b ^ k := by
        rw [zpow_mul_eq_left hconj (-k), neg_neg]

/- accepted add_to_file helper 3 -/
lemma twoSidedNF_eq_univ_of_inversion {G : Type*} [Group G] (a b : G)
    (hconj : a * b * a⁻¹ = b⁻¹) (hsq : a * a = 1)
    (hgen : Subgroup.closure {a, b} = ⊤) :
    twoSidedNF a b = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  have hx : x ∈ Subgroup.closure {a, b} := by simp [hgen]
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      simp at hy
      rcases hy with rfl | rfl
      · exact generator_left_mem_twoSidedNF y b
      · exact generator_right_mem_twoSidedNF a y
  | one => exact one_mem_twoSidedNF a b
  | mul y z hy hz ihy ihz =>
      exact twoSidedNF_mul_of_inversion hconj hsq ihy ihz
  | inv y hy ihy =>
      exact twoSidedNF_inv_of_inversion hconj hsq ihy

/- accepted add_to_file helper 4 -/
lemma zpow_commute_left {G : Type*} [Group G] {a b : G}
    (hcomm : a * b = b * a) (k : ℤ) :
    b ^ k * a = a * b ^ k :=
  (Commute.zpow_right hcomm k).symm.eq

/- accepted add_to_file helper 5 -/
lemma twoSidedNF_mul_of_commute_square {G : Type*} [Group G] {a b : G}
    (hcomm : a * b = b * a) {n : ℤ} (hsq : a * a = b ^ (2 * n))
    {x y : G} (hx : x ∈ twoSidedNF a b) (hy : y ∈ twoSidedNF a b) :
    x * y ∈ twoSidedNF a b := by
  rcases hx with ⟨cx, k, rfl⟩
  rcases hy with ⟨cy, l, rfl⟩
  cases cx <;> cases cy
  · refine ⟨false, k + l, ?_⟩
    simp [zpow_add]
  · refine ⟨true, k + l, ?_⟩
    simp
    calc
      b ^ k * (a * b ^ l) = (b ^ k * a) * b ^ l := by group
      _ = (a * b ^ k) * b ^ l := by rw [zpow_commute_left hcomm]
      _ = a * b ^ (k + l) := by
        rw [mul_assoc, ← zpow_add]
  · refine ⟨true, k + l, ?_⟩
    simp
    rw [mul_assoc, ← zpow_add]
  · refine ⟨false, 2 * n + k + l, ?_⟩
    simp
    calc
      (a * b ^ k) * (a * b ^ l) = (a * (b ^ k * a)) * b ^ l := by group
      _ = (a * (a * b ^ k)) * b ^ l := by rw [zpow_commute_left hcomm]
      _ = ((a * a) * b ^ k) * b ^ l := by group
      _ = b ^ (2 * n + k + l) := by
        rw [hsq, ← zpow_add, ← zpow_add]

/- accepted add_to_file helper 6 -/
lemma twoSidedNF_inv_of_commute_square {G : Type*} [Group G] {a b : G}
    (hcomm : a * b = b * a) {n : ℤ} (hsq : a * a = b ^ (2 * n))
    {x : G} (hx : x ∈ twoSidedNF a b) :
    x⁻¹ ∈ twoSidedNF a b := by
  rcases hx with ⟨c, k, rfl⟩
  cases c
  · refine ⟨false, -k, ?_⟩
    simp [zpow_neg]
  · refine ⟨true, -k - 2 * n, ?_⟩
    simp only [↓reduceIte]
    apply inv_eq_of_mul_eq_one_left
    calc
      (a * b ^ (-k - 2 * n)) * (a * b ^ k)
          = (a * (b ^ (-k - 2 * n) * a)) * b ^ k := by group
      _ = (a * (a * b ^ (-k - 2 * n))) * b ^ k := by
        rw [zpow_commute_left hcomm]
      _ = ((a * a) * b ^ (-k - 2 * n)) * b ^ k := by group
      _ = 1 := by
        rw [hsq, ← zpow_add, ← zpow_add]
        have hzero : 2 * n + (-k - 2 * n) + k = 0 := by ring
        rw [hzero]
        simp

lemma twoSidedNF_eq_univ_of_commute_square {G : Type*} [Group G] (a b : G)
    (hcomm : a * b = b * a) {n : ℤ} (hsq : a * a = b ^ (2 * n))
    (hgen : Subgroup.closure {a, b} = ⊤) :
    twoSidedNF a b = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  have hx : x ∈ Subgroup.closure {a, b} := by simp [hgen]
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      simp at hy
      rcases hy with rfl | rfl
      · exact generator_left_mem_twoSidedNF y b
      · exact generator_right_mem_twoSidedNF a y
  | one => exact one_mem_twoSidedNF a b
  | mul y z hy hz ihy ihz =>
      exact twoSidedNF_mul_of_commute_square hcomm hsq ihy ihz
  | inv y hy ihy =>
      exact twoSidedNF_inv_of_commute_square hcomm hsq ihy

/- accepted add_to_file helper 7 -/
noncomputable def mulEquivOfTwoSidedNF {P K : Type*} [Group P] [Group K]
    (f : P →* K) (a b : P) (v t : K)
    (fa : f a = v) (fb : f b = t)
    (hnf : twoSidedNF a b = Set.univ)
    (hgenK : Subgroup.closure {v, t} = ⊤)
    (hvH : v ∉ Subgroup.zpowers t)
    (htinj : Function.Injective fun k : ℤ => t ^ k) :
    P ≃* K := by
  have hsubset : ({v, t} : Set K) ⊆ f.range := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl
    · exact ⟨a, fa⟩
    · exact ⟨b, fb⟩
  have hle : Subgroup.closure {v, t} ≤ f.range := (Subgroup.closure_le _).mpr hsubset
  have hrange : f.range = ⊤ := by
    apply top_unique
    rwa [hgenK] at hle
  have hsurj : Function.Surjective f := MonoidHom.range_eq_top.mp hrange
  have hker : f.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro p hp
    rw [MonoidHom.mem_ker] at hp
    have hpnf : p ∈ twoSidedNF a b := by
      rw [hnf]
      trivial
    rcases hpnf with ⟨c, k, rfl⟩
    cases c
    · have ht : t ^ k = 1 := by
        simpa [fb] using hp
      have hk : k = 0 := by
        apply htinj
        simpa using ht
      simp [hk]
    · have hvt : v * t ^ k = 1 := by
        simpa [fa, fb] using hp
      have hv_eq : v = t ^ (-k) := by
        calc
          v = (v * t ^ k) * (t ^ k)⁻¹ := by group
          _ = (t ^ k)⁻¹ := by rw [hvt, one_mul]
          _ = t ^ (-k) := by rw [zpow_neg]
      have hvmem : v ∈ Subgroup.zpowers t := by
        rw [Subgroup.mem_zpowers_iff]
        exact ⟨-k, hv_eq.symm⟩
      exact False.elim (hvH hvmem)
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
  exact MulEquiv.ofBijective f ⟨hinj, hsurj⟩

/- accepted add_to_file helper 8 -/
def classificationCommRels (n : ℤ) : Set (FreeGroup (Fin 2)) :=
  {FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) *
      (FreeGroup.of (0 : Fin 2))⁻¹ * (FreeGroup.of (1 : Fin 2))⁻¹,
    (FreeGroup.of (0 : Fin 2)) ^ (2 : ℕ) *
      ((FreeGroup.of (1 : Fin 2)) ^ (2 * n))⁻¹}

def classificationInvRels : Set (FreeGroup (Fin 2)) :=
  {FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) *
      (FreeGroup.of (0 : Fin 2))⁻¹ * FreeGroup.of (1 : Fin 2),
    (FreeGroup.of (0 : Fin 2)) ^ (2 : ℕ)}

/- accepted add_to_file helper 9 -/
lemma mem_zpowers_coe_generator {G : Type*} [Group G] (u : G)
    (y : Subgroup.zpowers u) :
    y ∈ Subgroup.zpowers (⟨u, Subgroup.mem_zpowers u⟩ : Subgroup.zpowers u) := by
  rcases y with ⟨x, hx⟩
  rw [Subgroup.mem_zpowers_iff] at hx ⊢
  rcases hx with ⟨q, rfl⟩
  refine ⟨q, ?_⟩
  ext
  simp

noncomputable def zmodTwoEquivZpowers {G : Type*} [Group G] (u : G)
    (hu : orderOf u = 2) :
    Multiplicative (ZMod 2) ≃* Subgroup.zpowers u := by
  refine zmodMulEquivOfGenerator (g := ⟨u, Subgroup.mem_zpowers u⟩) ?_ ?_
  · intro y
    exact mem_zpowers_coe_generator u y
  · rw [Nat.card_zpowers]
    change orderOf u = 2
    exact hu

/- accepted add_to_file helper 10 -/
noncomputable def zmodTwoHomOfOrderTwo {G : Type*} [Group G] (u : G)
    (hu : orderOf u = 2) : Multiplicative (ZMod 2) →* G :=
  (Subgroup.zpowers u).subtype.comp (zmodTwoEquivZpowers u hu).toMonoidHom

lemma zmodTwoHomOfOrderTwo_apply_one {G : Type*} [Group G] (u : G)
    (hu : orderOf u = 2) :
    zmodTwoHomOfOrderTwo u hu (Multiplicative.ofAdd (1 : ZMod 2)) = u := by
  simp [zmodTwoHomOfOrderTwo, zmodTwoEquivZpowers]

/- accepted add_to_file helper 11 -/
lemma mem_zpowers_multiplicative_int_one (z : Multiplicative ℤ) :
    z ∈ Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ)) := by
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨Multiplicative.toAdd z, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [Int.toAdd_zpow]
  simp

lemma mem_zpowers_multiplicative_zmod_two_one (c : Multiplicative (ZMod 2)) :
    c ∈ Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod 2)) := by
  rw [Subgroup.mem_zpowers_iff]
  fin_cases c
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

lemma closure_pair_product_int_zmod_two :
    Subgroup.closure
      ({(1, Multiplicative.ofAdd (1 : ZMod 2)),
        (Multiplicative.ofAdd (1 : ℤ), 1)} :
        Set (Multiplicative ℤ × Multiplicative (ZMod 2))) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro x
  rcases x with ⟨z, c⟩
  have hz := mem_zpowers_multiplicative_int_one z
  have hc := mem_zpowers_multiplicative_zmod_two_one c
  rw [Subgroup.mem_zpowers_iff] at hz hc
  rcases hz with ⟨q, hq⟩
  rcases hc with ⟨w, hw⟩
  rw [← hq, ← hw]
  let a : Multiplicative ℤ × Multiplicative (ZMod 2) :=
    (1, Multiplicative.ofAdd (1 : ZMod 2))
  let b : Multiplicative ℤ × Multiplicative (ZMod 2) :=
    (Multiplicative.ofAdd (1 : ℤ), 1)
  have hprod : ((Multiplicative.ofAdd (1 : ℤ)) ^ q,
      (Multiplicative.ofAdd (1 : ZMod 2)) ^ w) = b ^ q * a ^ w := by
    ext <;> simp [a, b]
  rw [hprod]
  exact mul_mem
    (zpow_mem (Subgroup.subset_closure (by simp [a, b])) q)
    (zpow_mem (Subgroup.subset_closure (by simp [a, b])) w)

/- accepted add_to_file helper 12 -/
lemma not_isOfFinOrder_of_infinite_zpowers {G : Type*} [Group G] {t : G}
    (htinf : Infinite (Subgroup.zpowers t)) : ¬IsOfFinOrder t := by
  intro ht
  haveI : Infinite (Subgroup.zpowers t) := htinf
  haveI : Finite (Subgroup.zpowers t) := ht.finite_zpowers.to_subtype
  exact not_finite (Subgroup.zpowers t)

lemma zpow_injective_of_infinite_zpowers {G : Type*} [Group G] {t : G}
    (htinf : Infinite (Subgroup.zpowers t)) :
    Function.Injective fun k : ℤ => t ^ k :=
  injective_zpow_iff_not_isOfFinOrder.mpr
    (not_isOfFinOrder_of_infinite_zpowers htinf)

lemma not_mem_zpowers_of_closure_eq_top_index_two {G : Type*} [Group G] {v t : G}
    (hgen : Subgroup.closure {v, t} = ⊤)
    (hindex : (Subgroup.zpowers t).index = 2) :
    v ∉ Subgroup.zpowers t := by
  intro hv
  have hsubset : ({v, t} : Set G) ⊆ Subgroup.zpowers t := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl
    · exact hv
    · exact Subgroup.mem_zpowers x
  have hle : Subgroup.closure {v, t} ≤ Subgroup.zpowers t :=
    (Subgroup.closure_le _).mpr hsubset
  have htop : (⊤ : Subgroup G) ≤ Subgroup.zpowers t := by
    rwa [hgen] at hle
  have h_eq : Subgroup.zpowers t = ⊤ := top_unique htop
  have hindex1 : (Subgroup.zpowers t).index = 1 :=
    Subgroup.index_eq_one.mpr h_eq
  omega

/- accepted add_to_file helper 13 -/
lemma sq_mem_zpowers_of_index_two {G : Type*} [Group G] {v t : G}
    (hindex : (Subgroup.zpowers t).index = 2) :
    v * v ∈ Subgroup.zpowers t := by
  haveI : (Subgroup.zpowers t).Normal :=
    Subgroup.normal_of_index_eq_two hindex
  let H := Subgroup.zpowers t
  have hcard : Nat.card (G ⧸ H) = 2 := by
    rw [← Subgroup.index_eq_card, hindex]
  have hq : ((QuotientGroup.mk' H) v) ^ 2 = 1 := by
    have h := pow_card_eq_one' (x := (QuotientGroup.mk' H) v)
    rwa [hcard] at h
  have hq2 : (QuotientGroup.mk' H) (v ^ (2 : ℕ)) = 1 := by
    simpa using hq
  have hmem : v ^ (2 : ℕ) ∈ H := (QuotientGroup.eq_one_iff _).mp hq2
  simpa [sq] using hmem

/- accepted add_to_file helper 14 -/
lemma conjugation_cases_of_index_two {G : Type*} [Group G] {v t : G}
    (hindex : (Subgroup.zpowers t).index = 2)
    (htinj : Function.Injective fun k : ℤ => t ^ k) :
    v * t = t * v ∨ v * t * v⁻¹ = t⁻¹ := by
  haveI hnormal : (Subgroup.zpowers t).Normal :=
    Subgroup.normal_of_index_eq_two hindex
  have hmem1 : v * t * v⁻¹ ∈ Subgroup.zpowers t :=
    hnormal.conj_mem t (Subgroup.mem_zpowers t) v
  rw [Subgroup.mem_zpowers_iff] at hmem1
  rcases hmem1 with ⟨m, hm⟩
  have hconj : v * t * v⁻¹ = t ^ m := hm.symm
  have hmem2 : v⁻¹ * t * v ∈ Subgroup.zpowers t :=
    hnormal.conj_mem' t (Subgroup.mem_zpowers t) v
  rw [Subgroup.mem_zpowers_iff] at hmem2
  rcases hmem2 with ⟨l, hl⟩
  have hconji : v⁻¹ * t * v = t ^ l := hl.symm
  have hcycle : t = t ^ (l * m) := by
    calc
      t = v⁻¹ * (v * t * v⁻¹) * v := by group
      _ = v⁻¹ * t ^ m * v := by rw [hconj]
      _ = (v⁻¹ * t * v) ^ m := by
        have hz := (conj_zpow (a := v⁻¹) (b := t) (i := m)).symm
        simpa using hz
      _ = (t ^ l) ^ m := by rw [hconji]
      _ = t ^ (l * m) := (zpow_mul t l m).symm
  have hlm : l * m = 1 := by
    apply htinj
    calc
      t ^ (l * m) = t := hcycle.symm
      _ = t ^ (1 : ℤ) := by simp
  have hm_cases : m = 1 ∨ m = -1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hlm with hl1 | hlneg1
    · left
      simpa [hl1] using hlm
    · right
      have hnegm : -m = 1 := by
        simpa [hlneg1] using hlm
      omega
  rcases hm_cases with hm1 | hmneg1
  · left
    have hconj1 : v * t * v⁻¹ = t := by simpa [hm1] using hconj
    calc
      v * t = (v * t * v⁻¹) * v := by group
      _ = t * v := by rw [hconj1]
  · right
    simpa [hmneg1] using hconj

/- accepted add_to_file helper 15 -/
lemma no_torsion_of_commute_square_odd {K : Type*} [Group K] {v t : K} {s : ℤ}
    (hgen : Subgroup.closure {v, t} = ⊤)
    (hcomm : v * t = t * v)
    (hv2 : v * v = t ^ (2 * s + 1))
    (htinj : Function.Injective fun k : ℤ => t ^ k)
    (htors : ∃ x : K, x ≠ 1 ∧ IsOfFinOrder x) : False := by
  let w : K := v * t ^ (-s)
  have hw2 : w * w = t := by
    dsimp [w]
    calc
      (v * t ^ (-s)) * (v * t ^ (-s))
          = (v * (t ^ (-s) * v)) * t ^ (-s) := by group
      _ = (v * (v * t ^ (-s))) * t ^ (-s) := by
        rw [zpow_commute_left hcomm]
      _ = ((v * v) * t ^ (-s)) * t ^ (-s) := by group
      _ = t := by
        rw [hv2, ← zpow_add, ← zpow_add]
        have hone : 2 * s + 1 + -s + -s = 1 := by ring
        rw [hone]
        simp
  have ht_mem : t ∈ Subgroup.zpowers w := by
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨2, ?_⟩
    rw [← hw2, zpow_ofNat, pow_two]
  have hv_mem : v ∈ Subgroup.zpowers w := by
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨1 + 2 * s, ?_⟩
    calc
      w ^ (1 + 2 * s) = w * w ^ (2 * s) := by rw [zpow_add]; simp
      _ = w * (w * w) ^ s := by
        rw [zpow_mul w 2 s, zpow_ofNat, pow_two]
      _ = w * t ^ s := by rw [hw2]
      _ = v := by
        dsimp [w]
        calc
          (v * t ^ (-s)) * t ^ s = v * (t ^ (-s) * t ^ s) := by group
          _ = v := by rw [← zpow_add]; simp
  have hsubset : ({v, t} : Set K) ⊆ Subgroup.zpowers w := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl
    · exact hv_mem
    · exact ht_mem
  have hle : Subgroup.closure {v, t} ≤ Subgroup.zpowers w :=
    (Subgroup.closure_le _).mpr hsubset
  have hall : ∀ x : K, x ∈ Subgroup.zpowers w := by
    intro x
    have htop : (⊤ : Subgroup K) ≤ Subgroup.zpowers w := by
      rwa [hgen] at hle
    exact htop trivial
  rcases htors with ⟨x, hxne, hxfin⟩
  have hxmem := hall x
  rw [Subgroup.mem_zpowers_iff] at hxmem
  rcases hxmem with ⟨q, hq⟩
  have hx2 : x * x = t ^ q := by
    calc
      x * x = w ^ q * w ^ q := by rw [hq]
      _ = w ^ (q + q) := by rw [← zpow_add]
      _ = w ^ (2 * q) := by ring_nf
      _ = (w * w) ^ q := by
        rw [zpow_mul w 2 q, zpow_ofNat, pow_two]
      _ = t ^ q := by rw [hw2]
  have htqfin : IsOfFinOrder (t ^ q) := by
    rw [← hx2, ← pow_two x]
    exact hxfin.pow
  rcases isOfFinOrder_iff_pow_eq_one.mp htqfin with ⟨N, hNpos, hN⟩
  have hpow : t ^ (q * (N : ℤ)) = 1 := by
    calc
      t ^ (q * (N : ℤ)) = (t ^ q) ^ (N : ℤ) := zpow_mul t q N
      _ = 1 := by simpa using hN
  have hqN : q * (N : ℤ) = 0 := by
    apply htinj
    simpa using hpow
  have hNne : (N : ℤ) ≠ 0 := by omega
  have hq0 : q = 0 := by
    rcases mul_eq_zero.mp hqN with hq0 | hN0
    · exact hq0
    · exact False.elim (hNne hN0)
  apply hxne
  rw [← hq, hq0]
  simp

/- accepted add_to_file helper 16 -/
lemma square_exponent_even_of_torsion {K : Type*} [Group K] {v t : K} {r : ℤ}
    (hgen : Subgroup.closure {v, t} = ⊤)
    (hcomm : v * t = t * v)
    (hv2 : v * v = t ^ r)
    (htinj : Function.Injective fun k : ℤ => t ^ k)
    (htors : ∃ x : K, x ≠ 1 ∧ IsOfFinOrder x) :
    Even r := by
  by_contra hnot
  have hodd : Odd r := Int.not_even_iff_odd.mp hnot
  rcases hodd.exists_bit1 with ⟨s, hs⟩
  rw [hs] at hv2
  exact no_torsion_of_commute_square_odd hgen hcomm hv2 htinj htors

/- accepted add_to_file helper 17 -/
lemma presentedGroup_fin_two_closure_pair (rels : Set (FreeGroup (Fin 2))) :
    Subgroup.closure
      ({PresentedGroup.of (rels := rels) (0 : Fin 2),
        PresentedGroup.of (rels := rels) (1 : Fin 2)} :
        Set (PresentedGroup rels)) = ⊤ := by
  have hset :
      ({PresentedGroup.of (rels := rels) (0 : Fin 2),
        PresentedGroup.of (rels := rels) (1 : Fin 2)} :
        Set (PresentedGroup rels)) = Set.range (PresentedGroup.of (rels := rels)) := by
    ext x
    constructor
    · intro hx
      simp at hx
      rcases hx with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  rw [hset]
  exact PresentedGroup.closure_range_of rels

/- accepted add_to_file helper 18 -/
noncomputable def presentedCommEquiv {K : Type*} [Group K] (v t : K) (n : ℤ)
    (hcomm : v * t = t * v)
    (hsq : v * v = t ^ (2 * n))
    (hgen : Subgroup.closure {v, t} = ⊤)
    (hvH : v ∉ Subgroup.zpowers t)
    (htinj : Function.Injective fun k : ℤ => t ^ k) :
    PresentedGroup (classificationCommRels n) ≃* K := by
  let a : PresentedGroup (classificationCommRels n) := PresentedGroup.of 0
  let b : PresentedGroup (classificationCommRels n) := PresentedGroup.of 1
  have hrel1 : a * b * a⁻¹ * b⁻¹ = 1 := by
    have h := PresentedGroup.one_of_mem
      (rels := classificationCommRels n)
      (x := FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) *
        (FreeGroup.of (0 : Fin 2))⁻¹ * (FreeGroup.of (1 : Fin 2))⁻¹)
      (by simp [classificationCommRels])
    change a * b * a⁻¹ * b⁻¹ = 1 at h
    exact h
  have hcommP : a * b = b * a := by
    calc
      a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [hrel1, one_mul]
  have hrel2 : a ^ (2 : ℕ) * (b ^ (2 * n))⁻¹ = 1 := by
    have h := PresentedGroup.one_of_mem
      (rels := classificationCommRels n)
      (x := (FreeGroup.of (0 : Fin 2)) ^ (2 : ℕ) *
        ((FreeGroup.of (1 : Fin 2)) ^ (2 * n))⁻¹)
      (by simp [classificationCommRels])
    change a ^ (2 : ℕ) * (b ^ (2 * n))⁻¹ = 1 at h
    exact h
  have hsqP : a * a = b ^ (2 * n) := by
    have h := mul_inv_eq_one.mp hrel2
    simpa [sq] using h
  have hnf := twoSidedNF_eq_univ_of_commute_square a b hcommP hsqP
    (presentedGroup_fin_two_closure_pair (classificationCommRels n))
  let φ : Fin 2 → K := fun i => if i = 0 then v else t
  have hrels : ∀ r ∈ classificationCommRels n, (FreeGroup.lift φ) r = 1 := by
    intro r hr
    simp [classificationCommRels] at hr
    rcases hr with rfl | rfl
    · simp [φ]
      calc
        v * t * v⁻¹ * t⁻¹ = (v * t) * (v⁻¹ * t⁻¹) := by group
        _ = (t * v) * (v⁻¹ * t⁻¹) := by rw [hcomm]
        _ = 1 := by group
    · simp [φ]
      calc
        v ^ 2 * (t ^ (2 * n))⁻¹ = (v * v) * (t ^ (2 * n))⁻¹ := by rw [sq]
        _ = 1 := by rw [hsq, mul_inv_cancel]
  let f : PresentedGroup (classificationCommRels n) →* K := PresentedGroup.toGroup hrels
  have fa : f a = v := by
    simp [f, a, φ, PresentedGroup.toGroup.of]
  have fb : f b = t := by
    simp [f, b, φ, PresentedGroup.toGroup.of]
  exact mulEquivOfTwoSidedNF f a b v t fa fb hnf hgen hvH htinj

/- accepted add_to_file helper 19 -/
lemma presentedCommEquiv_apply_of_zero {K : Type*} [Group K] (v t : K) (n : ℤ)
    (hcomm : v * t = t * v) (hsq : v * v = t ^ (2 * n))
    (hgen : Subgroup.closure {v, t} = ⊤)
    (hvH : v ∉ Subgroup.zpowers t)
    (htinj : Function.Injective fun k : ℤ => t ^ k) :
    presentedCommEquiv v t n hcomm hsq hgen hvH htinj
      (PresentedGroup.of (0 : Fin 2)) = v := by
  simp [presentedCommEquiv, mulEquivOfTwoSidedNF, PresentedGroup.toGroup.of]

lemma presentedCommEquiv_apply_of_one {K : Type*} [Group K] (v t : K) (n : ℤ)
    (hcomm : v * t = t * v) (hsq : v * v = t ^ (2 * n))
    (hgen : Subgroup.closure {v, t} = ⊤)
    (hvH : v ∉ Subgroup.zpowers t)
    (htinj : Function.Injective fun k : ℤ => t ^ k) :
    presentedCommEquiv v t n hcomm hsq hgen hvH htinj
      (PresentedGroup.of (1 : Fin 2)) = t := by
  simp [presentedCommEquiv, mulEquivOfTwoSidedNF, PresentedGroup.toGroup.of]

/- accepted add_to_file helper 20 -/
noncomputable def presentedInvEquiv {K : Type*} [Group K] (v t : K)
    (hconj : v * t * v⁻¹ = t⁻¹)
    (hsq : v * v = 1)
    (hgen : Subgroup.closure {v, t} = ⊤)
    (hvH : v ∉ Subgroup.zpowers t)
    (htinj : Function.Injective fun k : ℤ => t ^ k) :
    PresentedGroup classificationInvRels ≃* K := by
  let a : PresentedGroup classificationInvRels := PresentedGroup.of 0
  let b : PresentedGroup classificationInvRels := PresentedGroup.of 1
  have hrel1 : a * b * a⁻¹ * b = 1 := by
    have h := PresentedGroup.one_of_mem
      (rels := classificationInvRels)
      (x := FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) *
        (FreeGroup.of (0 : Fin 2))⁻¹ * FreeGroup.of (1 : Fin 2))
      (by simp [classificationInvRels])
    change a * b * a⁻¹ * b = 1 at h
    exact h
  have hconjP : a * b * a⁻¹ = b⁻¹ := by
    calc
      a * b * a⁻¹ = (a * b * a⁻¹ * b) * b⁻¹ := by group
      _ = b⁻¹ := by rw [hrel1, one_mul]
  have hrel2 : a ^ (2 : ℕ) = 1 := by
    have h := PresentedGroup.one_of_mem
      (rels := classificationInvRels)
      (x := (FreeGroup.of (0 : Fin 2)) ^ (2 : ℕ))
      (by simp [classificationInvRels])
    change a ^ (2 : ℕ) = 1 at h
    exact h
  have hsqP : a * a = 1 := by
    simpa [sq] using hrel2
  have hnf := twoSidedNF_eq_univ_of_inversion a b hconjP hsqP
    (presentedGroup_fin_two_closure_pair classificationInvRels)
  let φ : Fin 2 → K := fun i => if i = 0 then v else t
  have hrels : ∀ r ∈ classificationInvRels, (FreeGroup.lift φ) r = 1 := by
    intro r hr
    simp [classificationInvRels] at hr
    rcases hr with rfl | rfl
    · simp [φ]
      rw [hconj, inv_mul_cancel]
    · simp [φ]
      rw [sq, hsq]
  let f : PresentedGroup classificationInvRels →* K := PresentedGroup.toGroup hrels
  have fa : f a = v := by
    simp [f, a, φ, PresentedGroup.toGroup.of]
  have fb : f b = t := by
    simp [f, b, φ, PresentedGroup.toGroup.of]
  exact mulEquivOfTwoSidedNF f a b v t fa fb hnf hgen hvH htinj

lemma presentedInvEquiv_apply_of_zero {K : Type*} [Group K] (v t : K)
    (hconj : v * t * v⁻¹ = t⁻¹) (hsq : v * v = 1)
    (hgen : Subgroup.closure {v, t} = ⊤)
    (hvH : v ∉ Subgroup.zpowers t)
    (htinj : Function.Injective fun k : ℤ => t ^ k) :
    presentedInvEquiv v t hconj hsq hgen hvH htinj
      (PresentedGroup.of (0 : Fin 2)) = v := by
  simp [presentedInvEquiv, mulEquivOfTwoSidedNF, PresentedGroup.toGroup.of]

lemma presentedInvEquiv_apply_of_one {K : Type*} [Group K] (v t : K)
    (hconj : v * t * v⁻¹ = t⁻¹) (hsq : v * v = 1)
    (hgen : Subgroup.closure {v, t} = ⊤)
    (hvH : v ∉ Subgroup.zpowers t)
    (htinj : Function.Injective fun k : ℤ => t ^ k) :
    presentedInvEquiv v t hconj hsq hgen hvH htinj
      (PresentedGroup.of (1 : Fin 2)) = t := by
  simp [presentedInvEquiv, mulEquivOfTwoSidedNF, PresentedGroup.toGroup.of]

/- accepted add_to_file helper 21 -/
noncomputable def directProductEquivOfCommute {K : Type*} [Group K] (v t : K) (n : ℤ)
    (hcomm : v * t = t * v)
    (hv2 : v * v = t ^ (2 * n))
    (hgen : Subgroup.closure {v, t} = ⊤)
    (hvH : v ∉ Subgroup.zpowers t)
    (htinj : Function.Injective fun k : ℤ => t ^ k) :
    Multiplicative ℤ × Multiplicative (ZMod 2) ≃* K := by
  let u : K := v * t ^ (-n)
  have hu2 : u * u = 1 := by
    dsimp [u]
    calc
      (v * t ^ (-n)) * (v * t ^ (-n))
          = (v * (t ^ (-n) * v)) * t ^ (-n) := by group
      _ = (v * (v * t ^ (-n))) * t ^ (-n) := by
        rw [zpow_commute_left hcomm]
      _ = ((v * v) * t ^ (-n)) * t ^ (-n) := by group
      _ = 1 := by
        rw [hv2, ← zpow_add, ← zpow_add]
        have hzero : 2 * n + -n + -n = 0 := by ring
        rw [hzero]
        simp
  have hu_ne : u ≠ 1 := by
    intro hu1
    have hv_eq : v = t ^ n := by
      calc
        v = (v * t ^ (-n)) * t ^ n := by group
        _ = u * t ^ n := rfl
        _ = t ^ n := by rw [hu1, one_mul]
    have hvmem : v ∈ Subgroup.zpowers t := by
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨n, hv_eq.symm⟩
    exact hvH hvmem
  have hu2pow : u ^ (2 : ℕ) = 1 := by
    rw [sq]
    exact hu2
  have hu_order : orderOf u = 2 := orderOf_eq_prime hu2pow hu_ne
  let fT : Multiplicative ℤ →* K := zpowersHom K t
  let fC : Multiplicative (ZMod 2) →* K := zmodTwoHomOfOrderTwo u hu_order
  have htu : Commute u t := by
    have hvt : Commute v t := hcomm
    have htn : Commute (t ^ (-n)) t :=
      (Commute.refl t).zpow_left (-n)
    exact hvt.mul_left htn
  have hcomm_fg : ∀ (z : Multiplicative ℤ) (c : Multiplicative (ZMod 2)),
      Commute (fT z) (fC c) := by
    intro z c
    have hz : fT z = t ^ Multiplicative.toAdd z := by
      simp [fT, zpowersHom_apply]
    have hc_mem : fC c ∈ Subgroup.zpowers u := by
      change ((zmodTwoEquivZpowers u hu_order) c : K) ∈ Subgroup.zpowers u
      exact ((zmodTwoEquivZpowers u hu_order) c).property
    rw [Subgroup.mem_zpowers_iff] at hc_mem
    rcases hc_mem with ⟨q, hq⟩
    rw [hz, ← hq]
    exact (Commute.zpow_zpow htu q (Multiplicative.toAdd z)).symm
  let F : Multiplicative ℤ × Multiplicative (ZMod 2) →* K :=
    MonoidHom.noncommCoprod fT fC hcomm_fg
  let a : Multiplicative ℤ × Multiplicative (ZMod 2) :=
    (1, Multiplicative.ofAdd (1 : ZMod 2))
  let b : Multiplicative ℤ × Multiplicative (ZMod 2) :=
    (Multiplicative.ofAdd (1 : ℤ), 1)
  have hcomm_ab : a * b = b * a := by
    ext <;> simp [a, b]
  have hsq_ab : a * a = b ^ (2 * (0 : ℤ)) := by
    ext <;> simp [a, b] <;> decide
  have hnf := twoSidedNF_eq_univ_of_commute_square a b hcomm_ab hsq_ab
    closure_pair_product_int_zmod_two
  have fa : F a = u := by
    simp [F, a, MonoidHom.noncommCoprod_apply, fT, fC,
      zmodTwoHomOfOrderTwo_apply_one, zpowersHom_apply]
  have fb : F b = t := by
    simp [F, b, MonoidHom.noncommCoprod_apply, fT, fC, zpowersHom_apply]
  have huH : u ∉ Subgroup.zpowers t := by
    intro humem
    rw [Subgroup.mem_zpowers_iff] at humem
    rcases humem with ⟨q, hq⟩
    have hv_mem : v ∈ Subgroup.zpowers t := by
      have hv_eq : v = u * t ^ n := by
        dsimp [u]
        group
      rw [hv_eq]
      exact mul_mem ⟨q, hq⟩ (zpow_mem (Subgroup.mem_zpowers t) n)
    exact hvH hv_mem
  have hgen_ut : Subgroup.closure {u, t} = ⊤ := by
    have hu_base : u ∈ Subgroup.closure {u, t} :=
      Subgroup.subset_closure (by simp)
    have ht_base : t ∈ Subgroup.closure {u, t} :=
      Subgroup.subset_closure (by simp)
    have hv_mem : v ∈ Subgroup.closure {u, t} := by
      have hv_eq : v = u * t ^ n := by
        dsimp [u]
        group
      rw [hv_eq]
      exact mul_mem hu_base (zpow_mem ht_base n)
    have hsubset : ({v, t} : Set K) ⊆ Subgroup.closure {u, t} := by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl
      · exact hv_mem
      · exact ht_base
    have hle : Subgroup.closure {v, t} ≤ Subgroup.closure {u, t} :=
      (Subgroup.closure_le _).mpr hsubset
    apply top_unique
    rwa [hgen] at hle
  exact mulEquivOfTwoSidedNF F a b u t fa fb hnf hgen_ut huH htinj

/- accepted add_to_file helper 22 -/
lemma multiplicative_zmod_two_one_mul_self :
    Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2) = 1 := by
  apply Multiplicative.toAdd.injective
  simp
  decide

/- accepted add_to_file helper 23 -/
abbrev ZModTwoMult : Type := Multiplicative (ZMod 2)
abbrev InfiniteDihedralModel : Type := Monoid.Coprod ZModTwoMult ZModTwoMult

/- accepted add_to_file helper 24 -/
lemma closure_infinite_dihedral_pair :
    Subgroup.closure
      ({Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ZMod 2)),
        Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ZMod 2)) *
          Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ZMod 2))} :
        Set InfiniteDihedralModel) = ⊤ := by
  let x : InfiniteDihedralModel := Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ZMod 2))
  let y : InfiniteDihedralModel := Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ZMod 2))
  let b : InfiniteDihedralModel := x * y
  have hx2 : x * x = 1 := by
    calc
      x * x = Monoid.Coprod.inl
        (Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2)) := by
        simp [x]
      _ = 1 := by simp [multiplicative_zmod_two_one_mul_self]
  have hy_eq : y = x * b := by
    dsimp [b]
    calc
      y = (x * x) * y := by rw [hx2, one_mul]
      _ = x * (x * y) := by group
  let S : Subgroup InfiniteDihedralModel := Subgroup.closure {x, b}
  have hxS : x ∈ S := Subgroup.subset_closure (by simp [S, x, b])
  have hbS : b ∈ S := Subgroup.subset_closure (by simp [S, x, b])
  have hyS : y ∈ S := by
    rw [hy_eq]
    exact mul_mem hxS hbS
  have hinl_le : Monoid.Coprod.inl.range ≤ S := by
    intro z hz
    rcases hz with ⟨c, rfl⟩
    have hc := mem_zpowers_multiplicative_zmod_two_one c
    rw [Subgroup.mem_zpowers_iff] at hc
    rcases hc with ⟨q, hq⟩
    rw [← hq]
    have hxpow : Monoid.Coprod.inl ((Multiplicative.ofAdd (1 : ZMod 2)) ^ q) = x ^ q := by
      simp [x]
    have hmem : x ^ q ∈ S := zpow_mem hxS q
    simpa [← hxpow] using hmem
  have hinr_le : Monoid.Coprod.inr.range ≤ S := by
    intro z hz
    rcases hz with ⟨c, rfl⟩
    have hc := mem_zpowers_multiplicative_zmod_two_one c
    rw [Subgroup.mem_zpowers_iff] at hc
    rcases hc with ⟨q, hq⟩
    rw [← hq]
    have hypow : Monoid.Coprod.inr ((Multiplicative.ofAdd (1 : ZMod 2)) ^ q) = y ^ q := by
      simp [y]
    have hmem : y ^ q ∈ S := zpow_mem hyS q
    simpa [← hypow] using hmem
  have hjoin : Monoid.Coprod.inl.range ⊔ Monoid.Coprod.inr.range ≤ S :=
    sup_le hinl_le hinr_le
  have htop_le : (⊤ : Subgroup InfiniteDihedralModel) ≤ S := by
    rw [← (Monoid.Coprod.codisjoint_range_inl_range_inr.eq_top)]
    exact hjoin
  have hS : S = ⊤ := top_unique htop_le
  simpa [S, x, b] using hS

/- accepted add_to_file helper 25 -/
noncomputable def infiniteDihedralEquivOfInversion {K : Type*} [Group K] (v t : K)
    (hconj : v * t * v⁻¹ = t⁻¹)
    (hsq : v * v = 1)
    (hgen : Subgroup.closure {v, t} = ⊤)
    (hvH : v ∉ Subgroup.zpowers t)
    (htinj : Function.Injective fun k : ℤ => t ^ k) :
    InfiniteDihedralModel ≃* K := by
  have hv_ne : v ≠ 1 := by
    intro hv1
    rw [hv1] at hvH
    exact hvH (Subgroup.one_mem _)
  have hv2pow : v ^ (2 : ℕ) = 1 := by
    rw [sq]
    exact hsq
  have hv_order : orderOf v = 2 := orderOf_eq_prime hv2pow hv_ne
  let w : K := v * t
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_left hsq
  have hvtv : v * t * v = t⁻¹ := by
    simpa [hvinv] using hconj
  have hw2 : w * w = 1 := by
    dsimp [w]
    calc
      (v * t) * (v * t) = ((v * t) * v) * t := by group
      _ = 1 := by rw [hvtv, inv_mul_cancel]
  have hw_ne : w ≠ 1 := by
    intro hw1
    have ht_eq : t = v := by
      calc
        t = v⁻¹ * (v * t) := by group
        _ = v⁻¹ * w := by dsimp [w]
        _ = v⁻¹ := by rw [hw1, mul_one]
        _ = v := hvinv
    have hvmem : v ∈ Subgroup.zpowers t := by
      rw [← ht_eq]
      exact Subgroup.mem_zpowers t
    exact hvH hvmem
  have hw2pow : w ^ (2 : ℕ) = 1 := by
    rw [sq]
    exact hw2
  have hw_order : orderOf w = 2 := orderOf_eq_prime hw2pow hw_ne
  let fV : ZModTwoMult →* K := zmodTwoHomOfOrderTwo v hv_order
  let fW : ZModTwoMult →* K := zmodTwoHomOfOrderTwo w hw_order
  let F : InfiniteDihedralModel →* K := Monoid.Coprod.lift fV fW
  let a : InfiniteDihedralModel := Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ZMod 2))
  let y : InfiniteDihedralModel := Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ZMod 2))
  let b : InfiniteDihedralModel := a * y
  have hx2 : a * a = 1 := by
    calc
      a * a = Monoid.Coprod.inl
        (Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2)) := by
        simp [a]
      _ = 1 := by simp [multiplicative_zmod_two_one_mul_self]
  have hy2 : y * y = 1 := by
    calc
      y * y = Monoid.Coprod.inr
        (Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2)) := by
        simp [y]
      _ = 1 := by simp [multiplicative_zmod_two_one_mul_self]
  have hxinv : a⁻¹ = a := inv_eq_of_mul_eq_one_left hx2
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_left hy2
  have hconj_ab : a * b * a⁻¹ = b⁻¹ := by
    calc
      a * b * a⁻¹ = ((a * a) * y) * a := by
        dsimp [b]
        rw [hxinv]
        group
      _ = y * a := by rw [hx2, one_mul]
      _ = b⁻¹ := by
        dsimp [b]
        rw [mul_inv_rev, hxinv, hyinv]
  have hnf := twoSidedNF_eq_univ_of_inversion a b hconj_ab hx2
    closure_infinite_dihedral_pair
  have fa : F a = v := by
    simp [F, a, fV, Monoid.Coprod.lift_comp_inl, zmodTwoHomOfOrderTwo_apply_one]
  have fy : F y = w := by
    simp [F, y, fW, Monoid.Coprod.lift_comp_inr, zmodTwoHomOfOrderTwo_apply_one]
  have fb : F b = t := by
    calc
      F b = F a * F y := by simp [b]
      _ = v * (v * t) := by rw [fa, fy]
      _ = t := by
        calc
          v * (v * t) = (v * v) * t := by group
          _ = t := by rw [hsq, one_mul]
  exact mulEquivOfTwoSidedNF F a b v t fa fb hnf hgen hvH htinj

/- verified submission -/
theorem index_two_infinite_cyclic_classification
    {K : Type*} [Group K] (v t : K)
    (hgen : Subgroup.closure {v, t} = ⊤)
    (htinf : Infinite (Subgroup.zpowers t))
    (hindex : (Subgroup.zpowers t).index = 2)
    (htors : ∃ x : K, x ≠ 1 ∧ IsOfFinOrder x) :
    (∃ n : ℤ,
      ∃ e : PresentedGroup
          ({FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) *
              (FreeGroup.of (0 : Fin 2))⁻¹ * (FreeGroup.of (1 : Fin 2))⁻¹,
            (FreeGroup.of (0 : Fin 2)) ^ (2 : ℕ) *
              ((FreeGroup.of (1 : Fin 2)) ^ (2 * n))⁻¹} :
            Set (FreeGroup (Fin 2))) ≃* K,
        e (PresentedGroup.of (0 : Fin 2)) = v ∧
        e (PresentedGroup.of (1 : Fin 2)) = t ∧
        Nonempty (K ≃* Multiplicative ℤ × Multiplicative (ZMod 2))) ∨
    (∃ e : PresentedGroup
          ({FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) *
              (FreeGroup.of (0 : Fin 2))⁻¹ * FreeGroup.of (1 : Fin 2),
            (FreeGroup.of (0 : Fin 2)) ^ (2 : ℕ)} :
            Set (FreeGroup (Fin 2))) ≃* K,
        e (PresentedGroup.of (0 : Fin 2)) = v ∧
        e (PresentedGroup.of (1 : Fin 2)) = t ∧
        Nonempty
          (K ≃* Monoid.Coprod (Multiplicative (ZMod 2))
            (Multiplicative (ZMod 2)))) := by
  have htinj : Function.Injective fun k : ℤ => t ^ k :=
    zpow_injective_of_infinite_zpowers htinf
  have hvH : v ∉ Subgroup.zpowers t :=
    not_mem_zpowers_of_closure_eq_top_index_two hgen hindex
  have hv2mem : v * v ∈ Subgroup.zpowers t :=
    sq_mem_zpowers_of_index_two (v := v) (t := t) hindex
  rw [Subgroup.mem_zpowers_iff] at hv2mem
  rcases hv2mem with ⟨r, hr⟩
  have hv2 : v * v = t ^ r := hr.symm
  have hcases := conjugation_cases_of_index_two (v := v) (t := t) hindex htinj
  rcases hcases with hcomm | hconj
  · have heven : Even r :=
      square_exponent_even_of_torsion hgen hcomm hv2 htinj htors
    rcases even_iff_exists_two_mul.mp heven with ⟨n, hn⟩
    have hv2n : v * v = t ^ (2 * n) := by
      simpa [hn] using hv2
    let e := presentedCommEquiv v t n hcomm hv2n hgen hvH htinj
    refine Or.inl ?_
    refine ⟨n, e, ?_, ?_, ?_⟩
    · exact presentedCommEquiv_apply_of_zero v t n hcomm hv2n hgen hvH htinj
    · exact presentedCommEquiv_apply_of_one v t n hcomm hv2n hgen hvH htinj
    · exact ⟨(directProductEquivOfCommute v t n hcomm hv2n hgen hvH htinj).symm⟩
  · have hvr : v * v = t ^ (-r) := by
      calc
        v * v = v * (v * v) * v⁻¹ := by group
        _ = v * t ^ r * v⁻¹ := by rw [hv2]
        _ = (v * t * v⁻¹) ^ r := by
          simpa using (conj_zpow (a := v) (b := t) (i := r)).symm
        _ = (t⁻¹) ^ r := by rw [hconj]
        _ = t ^ (-r) := by rw [inv_zpow']
    have hrneg : r = -r := by
      have htr : t ^ r = t ^ (-r) := by
        rw [← hv2, hvr]
      exact htinj htr
    have hr0 : r = 0 := by omega
    have hsq : v * v = 1 := by
      rw [hv2, hr0]
      simp
    let e := presentedInvEquiv v t hconj hsq hgen hvH htinj
    refine Or.inr ?_
    refine ⟨e, ?_, ?_, ?_⟩
    · exact presentedInvEquiv_apply_of_zero v t hconj hsq hgen hvH htinj
    · exact presentedInvEquiv_apply_of_one v t hconj hsq hgen hvH htinj
    · exact ⟨(infiniteDihedralEquivOfInversion v t hconj hsq hgen hvH htinj).symm⟩

end Rollout_p1552_index_two_infinite_cyclic_classification

namespace Rollout_p0194_seifert_chi_div_e_lt_one

/- verified submission -/
lemma seifert_nat_div_lt_one_rat {a b : ℕ} (h : a < b) :
    (a : ℚ) / (b : ℚ) < 1 := by
  have hb : 0 < (b : ℚ) := by
    exact_mod_cast Nat.zero_lt_of_lt h
  exact (div_lt_one hb).mpr (by exact_mod_cast h)

lemma seifert_nat_inv_pos_rat {b : ℕ} (hb : 2 ≤ b) :
    0 < (b : ℚ)⁻¹ := by
  have hb0 : 0 < (b : ℚ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hb)
  exact inv_pos.mpr hb0

theorem seifert_chi_div_e_lt_one
    (t d : ℕ) (n q : ℕ → ℕ)
    (hn : ∀ i, 1 ≤ i → i ≤ t → 2 ≤ n i)
    (hq_pos : ∀ i, 1 ≤ i → i ≤ t → 1 ≤ q i)
    (hq_lt : ∀ i, 1 ≤ i → i ≤ t → q i < n i)
    (hcoprime : ∀ i, 1 ≤ i → i ≤ t → Nat.Coprime (n i) (q i))
    (he : 0 < (d : ℚ) - ∑ i ∈ Finset.Icc 1 t, (q i : ℚ) / (n i : ℚ))
    (hcases :
      (t = 3 ∧
        (4 ≤ d ∨
          (d = 3 ∧ q 1 = 1) ∨
          (d = 2 ∧ q 1 = 1 ∧ q 2 = 1))) ∨
      (t = 4 ∧ 3 ≤ d ∧ q 1 = 1 ∧ q 2 = 1 ∧ q 3 = 1)) :
    let e : ℚ := (d : ℚ) - ∑ i ∈ Finset.Icc 1 t, (q i : ℚ) / (n i : ℚ)
    let χ : ℚ := -2 + ∑ i ∈ Finset.Icc 1 t, (1 - 1 / (n i : ℚ))
    χ / e < 1 := by
  rw [div_lt_one he]
  rcases hcases with h3 | h4
  · rcases h3 with ⟨ht, hc⟩
    subst t
    rcases hc with hd | hd | hd
    · have hdQ : (4 : ℚ) ≤ d := by exact_mod_cast hd
      have hq1 : (q 1 : ℚ) / (n 1 : ℚ) < 1 :=
        seifert_nat_div_lt_one_rat (hq_lt 1 (by norm_num) (by norm_num))
      have hq2 : (q 2 : ℚ) / (n 2 : ℚ) < 1 :=
        seifert_nat_div_lt_one_rat (hq_lt 2 (by norm_num) (by norm_num))
      have hq3 : (q 3 : ℚ) / (n 3 : ℚ) < 1 :=
        seifert_nat_div_lt_one_rat (hq_lt 3 (by norm_num) (by norm_num))
      have hn1 : 0 < (n 1 : ℚ)⁻¹ :=
        seifert_nat_inv_pos_rat (hn 1 (by norm_num) (by norm_num))
      have hn2 : 0 < (n 2 : ℚ)⁻¹ :=
        seifert_nat_inv_pos_rat (hn 2 (by norm_num) (by norm_num))
      have hn3 : 0 < (n 3 : ℚ)⁻¹ :=
        seifert_nat_inv_pos_rat (hn 3 (by norm_num) (by norm_num))
      have hsumq : ∑ i ∈ Finset.Icc 1 3, (q i : ℚ) / (n i : ℚ) < 3 := by
        norm_num [Finset.sum_Icc_succ_top]
        nlinarith
      have hsuminv_exp :
          0 < (n 1 : ℚ)⁻¹ + (n 2 : ℚ)⁻¹ + (n 3 : ℚ)⁻¹ :=
        add_pos (add_pos hn1 hn2) hn3
      have hchi : -2 + ∑ i ∈ Finset.Icc 1 3, (1 - 1 / (n i : ℚ)) < 1 := by
        norm_num [Finset.sum_Icc_succ_top]
        linarith
      have he1 : 1 < (d : ℚ) - ∑ i ∈ Finset.Icc 1 3, (q i : ℚ) / (n i : ℚ) := by
        nlinarith
      exact lt_trans hchi he1
    · rcases hd with ⟨hd, hq1nat⟩
      subst d
      have hq2 : (q 2 : ℚ) / (n 2 : ℚ) < 1 :=
        seifert_nat_div_lt_one_rat (hq_lt 2 (by norm_num) (by norm_num))
      have hq3 : (q 3 : ℚ) / (n 3 : ℚ) < 1 :=
        seifert_nat_div_lt_one_rat (hq_lt 3 (by norm_num) (by norm_num))
      have hn2 : 0 < (n 2 : ℚ)⁻¹ :=
        seifert_nat_inv_pos_rat (hn 2 (by norm_num) (by norm_num))
      have hn3 : 0 < (n 3 : ℚ)⁻¹ :=
        seifert_nat_inv_pos_rat (hn 3 (by norm_num) (by norm_num))
      norm_num [Finset.sum_Icc_succ_top, hq1nat]
      nlinarith
    · rcases hd with ⟨hd, hq1nat, hq2nat⟩
      subst d
      have hq3 : (q 3 : ℚ) / (n 3 : ℚ) < 1 :=
        seifert_nat_div_lt_one_rat (hq_lt 3 (by norm_num) (by norm_num))
      have hn3 : 0 < (n 3 : ℚ)⁻¹ :=
        seifert_nat_inv_pos_rat (hn 3 (by norm_num) (by norm_num))
      norm_num [Finset.sum_Icc_succ_top, hq1nat, hq2nat]
      nlinarith
  · rcases h4 with ⟨ht, hd, hq1nat, hq2nat, hq3nat⟩
    subst t
    have hdQ : (3 : ℚ) ≤ d := by exact_mod_cast hd
    have hq4 : (q 4 : ℚ) / (n 4 : ℚ) < 1 :=
      seifert_nat_div_lt_one_rat (hq_lt 4 (by norm_num) (by norm_num))
    have hn4 : 0 < (n 4 : ℚ)⁻¹ :=
      seifert_nat_inv_pos_rat (hn 4 (by norm_num) (by norm_num))
    norm_num [Finset.sum_Icc_succ_top, hq1nat, hq2nat, hq3nat]
    nlinarith

end Rollout_p0194_seifert_chi_div_e_lt_one

namespace Rollout_p0912_catlin_vertical_curve_is_geodesic

/- accepted add_to_file helper 1 -/

open scoped ComplexConjugate

noncomputable section

def evalDiag : ℂ → MvPolynomial (Fin 2) ℂ → ℂ :=
  fun z q => MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z else star z) q

@[simp] lemma evalDiag_zero (z : ℂ) : evalDiag z (0 : MvPolynomial (Fin 2) ℂ) = 0 := by
  change MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z else star z) 0 = 0
  exact map_zero _

@[simp] lemma evalDiag_one (z : ℂ) : evalDiag z (1 : MvPolynomial (Fin 2) ℂ) = 1 := by
  change MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z else star z) 1 = 1
  exact map_one _

@[simp] lemma evalDiag_C (z : ℂ) (a : ℂ) : evalDiag z (MvPolynomial.C a) = a := by
  change MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z else star z) (MvPolynomial.C a) = a
  exact MvPolynomial.eval_C a

@[simp] lemma evalDiag_add (z : ℂ) (q r : MvPolynomial (Fin 2) ℂ) :
    evalDiag z (q + r) = evalDiag z q + evalDiag z r := by
  change MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z else star z) (q + r) = _
  exact map_add _ _ _

@[simp] lemma evalDiag_mul (z : ℂ) (q r : MvPolynomial (Fin 2) ℂ) :
    evalDiag z (q * r) = evalDiag z q * evalDiag z r := by
  change MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z else star z) (q * r) = _
  exact map_mul _ _ _

@[simp] lemma evalDiag_X (z : ℂ) (i : Fin 2) :
    evalDiag z (MvPolynomial.X i) = if i = 0 then z else star z := by
  change MvPolynomial.eval (fun j : Fin 2 => if j = 0 then z else star z) (MvPolynomial.X i) = _
  exact MvPolynomial.eval_X i

lemma hasDerivAt_evalDiag
    (q : MvPolynomial (Fin 2) ℂ) {z : ℝ → ℂ} {z' : ℂ} {x : ℝ}
    (hz : HasDerivAt z z' x) :
    HasDerivAt (fun u => evalDiag (z u) q)
      (z' * evalDiag (z x) ((MvPolynomial.pderiv (0 : Fin 2)) q) +
        star z' * evalDiag (z x) ((MvPolynomial.pderiv (1 : Fin 2)) q)) x := by
  induction q using MvPolynomial.induction_on with
  | C a =>
      have hfun : (fun u => evalDiag (z u) (MvPolynomial.C a)) = fun _ : ℝ => a := by
        ext u; simp
      have hder : z' * evalDiag (z x) ((MvPolynomial.pderiv (0 : Fin 2)) (MvPolynomial.C a)) +
        star z' * evalDiag (z x) ((MvPolynomial.pderiv (1 : Fin 2)) (MvPolynomial.C a)) = 0 := by
        rw [MvPolynomial.pderiv_C, MvPolynomial.pderiv_C]
        simp
      rw [hfun, hder]
      exact hasDerivAt_const x a
  | add q r hq hr =>
      have h := hq.add hr
      convert h using 1
      · ext u; simp
      · rw [map_add, map_add]
        simp
        ring
  | mul_X q i hq =>
      let f : Fin 2 → ℝ → ℂ := fun j u => if j = 0 then z u else star (z u)
      let f' : Fin 2 → ℂ := fun j => if j = 0 then z' else star z'
      have hf : HasDerivAt (fun u => f i u) (f' i) x := by
        by_cases hi : i = 0
        · simp [f, f', hi, hz]
        · have hi1 : i = 1 := by omega
          simpa [f, f', hi, hi1] using hz.star
      have hmul := hq.mul hf
      convert hmul using 1
      · ext u
        simp [f]
      · simp [f, f']
        by_cases hi : i = 0
        · simp [hi, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, Pi.single_apply]
          ring
        · have hi1 : i = 1 := by omega
          simp [hi, hi1, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, Pi.single_apply]
          ring

/- accepted add_to_file helper 2 -/
lemma evalDiag_pderiv_one_eq_conj_pderiv_zero
    (p : MvPolynomial (Fin 2) ℂ)
    (hreal : ∀ z : ℂ, (evalDiag z p).im = 0) (z : ℂ) :
    evalDiag z ((MvPolynomial.pderiv (1 : Fin 2)) p) =
      star (evalDiag z ((MvPolynomial.pderiv (0 : Fin 2)) p)) := by
  let A : ℂ := evalDiag z ((MvPolynomial.pderiv (0 : Fin 2)) p)
  let B : ℂ := evalDiag z ((MvPolynomial.pderiv (1 : Fin 2)) p)
  have hxpath : HasDerivAt (fun t : ℝ => z + (t : ℂ)) 1 0 := by
    have h := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_id (0 : ℝ)))
    simpa [Function.comp_def] using h.const_add z
  have hx := hasDerivAt_evalDiag p hxpath
  have hxim : HasDerivAt (fun t : ℝ => (evalDiag (z + (t : ℂ)) p).im)
      (1 * A + star (1 : ℂ) * B).im 0 := by
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hx
    simpa [A, B, Function.comp_def] using h
  have hxfun : (fun t : ℝ => (evalDiag (z + (t : ℂ)) p).im) = fun _ : ℝ => 0 := by
    ext t
    exact hreal _
  rw [hxfun] at hxim
  have h1 : (A + B).im = 0 := by
    have hu := hxim.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    simpa [A, B] using hu
  have hipath : HasDerivAt (fun t : ℝ => z + Complex.I * (t : ℂ)) Complex.I 0 := by
    have h := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_id (0 : ℝ)))
    have hmul := h.const_mul Complex.I
    simpa [Function.comp_def] using hmul.const_add z
  have hi := hasDerivAt_evalDiag p hipath
  have hiim : HasDerivAt (fun t : ℝ => (evalDiag (z + Complex.I * (t : ℂ)) p).im)
      (Complex.I * A + star Complex.I * B).im 0 := by
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hi
    simpa [A, B, Function.comp_def] using h
  have hifun : (fun t : ℝ => (evalDiag (z + Complex.I * (t : ℂ)) p).im) = fun _ : ℝ => 0 := by
    ext t
    exact hreal _
  rw [hifun] at hiim
  have h2 : (Complex.I * A - Complex.I * B).im = 0 := by
    have hu := hiim.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    simpa [A, B, sub_eq_add_neg] using hu
  apply Complex.ext
  · have h : A.re - B.re = 0 := by
      simpa [A, B, Complex.mul_im] using h2
    have hb : A.re = B.re := by linarith
    simpa [A, B, star] using hb.symm
  · have h : A.im + B.im = 0 := by simpa [A, B] using h1
    have hb : B.im = -A.im := by linarith
    simpa [A, B, star] using hb

/- accepted add_to_file helper 3 -/
lemma continuous_evalDiag (q : MvPolynomial (Fin 2) ℂ) : Continuous fun z => evalDiag z q := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using continuous_const
  | add q r hq hr => simpa using hq.add hr
  | mul_X q i hq =>
      have hi : Continuous fun z : ℂ => (if i = 0 then z else star z) := by
        by_cases h : i = 0
        · simpa [h] using continuous_id
        · have h1 : i = 1 := by omega
          simpa [h, h1] using continuous_star
      have h := hq.mul hi
      convert h using 1
      ext z
      by_cases hiz : i = 0 <;> simp [hiz]

/- accepted add_to_file helper 4 -/
def diagDer (p : MvPolynomial (Fin 2) ℂ) (j k : ℕ) (z : ℂ) : ℂ :=
  evalDiag z ((MvPolynomial.pderiv (1 : Fin 2))^[k]
    ((MvPolynomial.pderiv (0 : Fin 2))^[j] p))

def ASet (p : MvPolynomial (Fin 2) ℂ) (l : ℕ) (z : ℂ) : Set ℝ :=
  {u : ℝ | ∃ j k : ℕ, 0 < j ∧ 0 < k ∧ j + k = l ∧ u = ‖diagDer p j k z‖}

def AIndex (l : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (l + 1)).product (Finset.range (l + 1))

def AValue (p : MvPolynomial (Fin 2) ℂ) (l : ℕ) (z : ℂ) (jk : ℕ × ℕ) : ℝ :=
  if 0 < jk.1 ∧ 0 < jk.2 ∧ jk.1 + jk.2 = l then ‖diagDer p jk.1 jk.2 z‖ else 0

lemma AIndex_nonempty (l : ℕ) : (AIndex l).Nonempty := by
  refine ⟨(0,0), ?_⟩
  simp [AIndex]

lemma ASet_eq_finset_sup' {p : MvPolynomial (Fin 2) ℂ} {l : ℕ} (hl : 2 ≤ l) (z : ℂ) :
    sSup (ASet p l z) = (AIndex l).sup' (AIndex_nonempty l) (AValue p l z) := by
  have hne : (ASet p l z).Nonempty := by
    refine ⟨‖diagDer p 1 (l-1) z‖, 1, l-1, by omega, by omega, by omega, rfl⟩
  refine IsLUB.csSup_eq ?_ hne
  constructor
  · rintro u ⟨j,k,hj,hk,hjk,rfl⟩
    have hmem : (j,k) ∈ AIndex l := by
      simp [AIndex]
      omega
    have hv : AValue p l z (j,k) = ‖diagDer p j k z‖ := by
      simp [AValue,hj,hk,hjk]
    rw [← hv]
    exact Finset.le_sup' (AValue p l z) hmem
  · intro b hb
    apply Finset.sup'_le
    rintro ⟨j,k⟩ hmem
    by_cases hvalid : 0 < j ∧ 0 < k ∧ j + k = l
    · have hbv := hb ⟨j,k,hvalid.1,hvalid.2.1,hvalid.2.2,rfl⟩
      simpa [AValue,hvalid] using hbv
    · have hv : AValue p l z (j,k) = 0 := by simp [AValue,hvalid]
      have hnonneg : 0 ≤ ‖diagDer p 1 (l-1) z‖ := norm_nonneg _
      have hb0 : 0 ≤ b := by
        exact hnonneg.trans (hb ⟨1,l-1,by omega,by omega,by omega,rfl⟩)
      simpa [hv] using hb0

lemma continuous_ASet_sSup {p : MvPolynomial (Fin 2) ℂ} {l : ℕ} (hl : 2 ≤ l) :
    Continuous fun z : ℂ => sSup (ASet p l z) := by
  have hfun : (fun z : ℂ => sSup (ASet p l z)) =
      fun z => (AIndex l).sup' (AIndex_nonempty l) (AValue p l z) := by
    funext z
    exact ASet_eq_finset_sup' hl z
  rw [hfun]
  apply Continuous.finset_sup'_apply
  rintro ⟨j,k⟩ hmem
  by_cases hvalid : 0 < j ∧ 0 < k ∧ j + k = l
  · simpa [AValue, hvalid, diagDer] using (continuous_evalDiag _).norm
  · simpa [AValue, hvalid] using continuous_const

/- accepted add_to_file helper 5 -/
lemma re_evalDiag_chain {p : MvPolynomial (Fin 2) ℂ}
    (hreal : ∀ z : ℂ, (evalDiag z p).im = 0) {z v : ℂ} :
    (v * evalDiag z ((MvPolynomial.pderiv (0 : Fin 2)) p) +
      star v * evalDiag z ((MvPolynomial.pderiv (1 : Fin 2)) p)).re =
      (2 * v * evalDiag z ((MvPolynomial.pderiv (0 : Fin 2)) p)).re := by
  rw [evalDiag_pderiv_one_eq_conj_pderiv_zero p hreal z]
  let X : ℂ := v * evalDiag z ((MvPolynomial.pderiv (0 : Fin 2)) p)
  have hs : star v * star (evalDiag z ((MvPolynomial.pderiv (0 : Fin 2)) p)) = star X := by
    simp [X]
  rw [hs]
  simp [X]
  ring

/- accepted add_to_file helper 6 -/
lemma frontier_sublevel_eq_zero {X : Type*} [TopologicalSpace X] {r : X → ℝ}
    (hr : Continuous r) {Ω : Set X} (hΩ : Ω = {q | r q < 0}) {q : X}
    (hfront : q ∈ frontier Ω) : r q = 0 := by
  have hopen : IsOpen Ω := by
    rw [hΩ]
    exact isOpen_Iio.preimage hr
  have hnot : q ∉ Ω := by
    have hi := hfront.2
    rwa [hopen.interior_eq] at hi
  have hle : r q ≤ 0 := by
    have hsub : Ω ⊆ {x | r x ≤ 0} := by
      intro x hx
      exact le_of_lt (show r x < 0 from by rwa [hΩ] at hx)
    have hclosed : IsClosed {x | r x ≤ 0} := isClosed_le hr continuous_const
    exact closure_minimal hsub hclosed hfront.1
  have hge : 0 ≤ r q := by
    by_contra h
    have : r q < 0 := lt_of_not_ge h
    exact hnot (by rwa [hΩ])
  linarith

/- accepted add_to_file helper 7 -/
def PiecewiseC1Curve : (ℝ → ℂ × ℂ) → Prop := fun γ =>
  ∃ n : ℕ, ∃ u : Fin (n + 1) → ℝ,
    u 0 = 0 ∧ u ⟨n, Nat.lt_add_one n⟩ = 1 ∧ StrictMono u ∧
      ∀ i : Fin n,
        ContDiffOn ℝ 1 γ (Set.Icc (u i.castSucc) (u i.succ))

lemma PiecewiseC1Curve_single {γ : ℝ → ℂ × ℂ} (hγ : ContDiff ℝ 1 γ) :
    PiecewiseC1Curve γ := by
  refine ⟨1, fun i : Fin 2 => (i : ℝ), ?_, ?_, ?_, ?_⟩
  · simp
  · norm_num
  · intro i j hij
    exact Nat.cast_lt.mpr hij
  · intro i
    fin_cases i
    simpa using hγ.contDiffOn

/- accepted add_to_file helper 8 -/
lemma contDiff_evalDiag (q : MvPolynomial (Fin 2) ℂ) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun z => evalDiag z q := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add q r hq hr => simpa using hq.add hr
  | mul_X q i hq =>
      have hi : ContDiff ℝ n fun z : ℂ => (if i = 0 then z else star z) := by
        by_cases h : i = 0
        · simpa [h] using contDiff_id
        · have h1 : i = 1 := by omega
          have hc : ContDiff ℝ n fun z : ℂ => Complex.conjCLE z := Complex.conjCLE.contDiff
          simpa [h, h1, Complex.conjCLE_apply] using hc
      have h := hq.mul hi
      convert h using 1
      ext z
      by_cases hiz : i = 0 <;> simp [hiz]

/- accepted add_to_file helper 9 -/
def catlinP (p : MvPolynomial (Fin 2) ℂ) (z : ℂ) : ℝ := (evalDiag z p).re

def catlinPz (p : MvPolynomial (Fin 2) ℂ) (z : ℂ) : ℂ := diagDer p 1 0 z

def catlinA (p : MvPolynomial (Fin 2) ℂ) (l : ℕ) (z : ℂ) : ℝ := sSup (ASet p l z)

def catlinR (p : MvPolynomial (Fin 2) ℂ) (q : ℂ × ℂ) : ℝ := q.2.re + catlinP p q.1

def catlinM (m : ℕ) (p : MvPolynomial (Fin 2) ℂ) (q v : ℂ × ℂ) : ℝ :=
  ‖v.2 + 2 * v.1 * catlinPz p q.1‖ / |catlinR p q| +
    ‖v.1‖ * ∑ l ∈ Finset.Icc 2 m,
      Real.rpow (catlinA p l q.1 / |catlinR p q|) (1 / (l : ℝ))

/- accepted add_to_file helper 10 -/
lemma continuous_catlinP (p : MvPolynomial (Fin 2) ℂ) : Continuous (catlinP p) := by
  exact Complex.continuous_re.comp (continuous_evalDiag p)

lemma continuous_catlinPz (p : MvPolynomial (Fin 2) ℂ) : Continuous (catlinPz p) := by
  exact continuous_evalDiag _

lemma continuous_catlinR (p : MvPolynomial (Fin 2) ℂ) : Continuous (catlinR p) := by
  exact (Complex.continuous_re.comp continuous_snd).add ((continuous_catlinP p).comp continuous_fst)

lemma continuous_catlinA (p : MvPolynomial (Fin 2) ℂ) {l : ℕ} (hl : 2 ≤ l) :
    Continuous (catlinA p l) := by
  exact continuous_ASet_sSup hl

lemma catlinA_nonneg (p : MvPolynomial (Fin 2) ℂ) (l : ℕ) (z : ℂ) :
    0 ≤ catlinA p l z := by
  apply Real.sSup_nonneg
  rintro u ⟨j,k,hj,hk,hjk,rfl⟩
  exact norm_nonneg _

lemma catlinM_nonneg (m : ℕ) (p : MvPolynomial (Fin 2) ℂ) (q v : ℂ × ℂ) :
    0 ≤ catlinM m p q v := by
  unfold catlinM
  apply add_nonneg
  · exact div_nonneg (norm_nonneg _) (abs_nonneg _)
  · apply mul_nonneg (norm_nonneg _)
    apply Finset.sum_nonneg
    intro l hl
    apply Real.rpow_nonneg
    exact div_nonneg (catlinA_nonneg p l q.1) (abs_nonneg _)

/- accepted add_to_file helper 11 -/
lemma continuousOn_catlinM_comp {m : ℕ} {p : MvPolynomial (Fin 2) ℂ}
    {q v : ℝ → ℂ × ℂ} {s : Set ℝ}
    (hq : ContinuousOn q s) (hv : ContinuousOn v s)
    (hr : ∀ u ∈ s, catlinR p (q u) < 0) :
    ContinuousOn (fun u => catlinM m p (q u) (v u)) s := by
  have hq1 : ContinuousOn (fun u => (q u).1) s := continuous_fst.comp_continuousOn hq
  have hq2 : ContinuousOn (fun u => (q u).2) s := continuous_snd.comp_continuousOn hq
  have hv1 : ContinuousOn (fun u => (v u).1) s := continuous_fst.comp_continuousOn hv
  have hv2 : ContinuousOn (fun u => (v u).2) s := continuous_snd.comp_continuousOn hv
  have hR : ContinuousOn (fun u => catlinR p (q u)) s :=
    (continuous_catlinR p).comp_continuousOn hq
  have habs : ContinuousOn (fun u => |catlinR p (q u)|) s := hR.abs
  have hRne : ∀ u ∈ s, catlinR p (q u) ≠ 0 := fun u hu => ne_of_lt (hr u hu)
  have hfirst_num : ContinuousOn (fun u => ‖(v u).2 + 2 * (v u).1 * catlinPz p (q u).1‖) s := by
    have hpz : ContinuousOn (fun u => catlinPz p (q u).1) s :=
      (continuous_catlinPz p).comp_continuousOn hq1
    exact (hv2.add ((continuousOn_const.mul hv1).mul hpz)).norm
  have hfirst : ContinuousOn (fun u =>
      ‖(v u).2 + 2 * (v u).1 * catlinPz p (q u).1‖ / |catlinR p (q u)|) s := by
    exact hfirst_num.div habs (fun u hu => abs_ne_zero.mpr (hRne u hu))
  have hsum : ContinuousOn (fun u =>
      ∑ l ∈ Finset.Icc 2 m,
        Real.rpow (catlinA p l (q u).1 / |catlinR p (q u)|) (1 / (l : ℝ))) s := by
    apply continuousOn_finset_sum
    intro l hl
    have hl2 : 2 ≤ l := (Finset.mem_Icc.mp hl).1
    have hA : ContinuousOn (fun u => catlinA p l (q u).1) s :=
      (continuous_catlinA p hl2).comp_continuousOn hq1
    have hbase : ContinuousOn (fun u => catlinA p l (q u).1 / |catlinR p (q u)|) s :=
      hA.div habs (fun u hu => abs_ne_zero.mpr (hRne u hu))
    have hpow : ContinuousOn (fun u =>
        (catlinA p l (q u).1 / |catlinR p (q u)|) ^ (1 / (l : ℝ))) s := by
      apply ContinuousOn.rpow hbase continuousOn_const
      intro u hu
      right
      have : (0:ℝ) < l := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (2:ℕ)) hl2)
      positivity
    simpa using hpow
  have hsecond : ContinuousOn (fun u =>
      ‖(v u).1‖ * ∑ l ∈ Finset.Icc 2 m,
        Real.rpow (catlinA p l (q u).1 / |catlinR p (q u)|) (1 / (l : ℝ))) s :=
    hv1.norm.mul hsum
  simpa [catlinM] using hfirst.add hsecond

/- accepted add_to_file helper 12 -/
lemma hasDerivAt_catlinR_comp {p : MvPolynomial (Fin 2) ℂ}
    (hreal : ∀ z : ℂ, (evalDiag z p).im = 0)
    {γ : ℝ → ℂ × ℂ} {v : ℂ × ℂ} {u : ℝ}
    (hγ : HasDerivAt γ v u) :
    HasDerivAt (fun u => catlinR p (γ u))
      ((v.2 + 2 * v.1 * catlinPz p (γ u).1).re) u := by
  have hγ1 : HasDerivAt (fun u => (γ u).1) v.1 u := by
    have h := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt u hγ
    simpa [Function.comp_def] using h
  have hγ2 : HasDerivAt (fun u => (γ u).2) v.2 u := by
    have h := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt u hγ
    simpa [Function.comp_def] using h
  have hp := hasDerivAt_evalDiag p hγ1
  have hp' : HasDerivAt (fun u => (evalDiag (γ u).1 p).re)
      ((2 * v.1 * catlinPz p (γ u).1).re) u := by
    have h0 : HasDerivAt (fun u => (evalDiag (γ u).1 p).re)
        ((v.1 * evalDiag (γ u).1 ((MvPolynomial.pderiv (0 : Fin 2)) p) +
          star v.1 * evalDiag (γ u).1 ((MvPolynomial.pderiv (1 : Fin 2)) p)).re) u := by
      have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hp
      simpa [Function.comp_def, Complex.reCLM_apply] using h
    have hre := re_evalDiag_chain (p:=p) hreal (z:=(γ u).1) (v:=v.1)
    have hre' : (v.1 * evalDiag (γ u).1 ((MvPolynomial.pderiv (0 : Fin 2)) p) +
        star v.1 * evalDiag (γ u).1 ((MvPolynomial.pderiv (1 : Fin 2)) p)).re =
        (2 * v.1 * catlinPz p (γ u).1).re := by
      simpa [catlinPz, diagDer] using hre
    rw [hre'] at h0
    exact h0
  have hw : HasDerivAt (fun u => (γ u).2.re) v.2.re u := by
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hγ2
    simpa [Function.comp_def, Complex.reCLM_apply] using h
  have hsum := hw.add hp'
  have hder : v.2.re + (2 * v.1 * catlinPz p (γ u).1).re =
      (v.2 + 2 * v.1 * catlinPz p (γ u).1).re := by
    simp [Complex.add_re]
  rw [hder] at hsum
  simpa [catlinR, catlinP] using hsum

/- accepted add_to_file helper 13 -/
lemma catlinM_first_le (m : ℕ) (p : MvPolynomial (Fin 2) ℂ) (q v : ℂ × ℂ) :
    ‖v.2 + 2 * v.1 * catlinPz p q.1‖ / |catlinR p q| ≤ catlinM m p q v := by
  unfold catlinM
  apply le_add_of_nonneg_right
  apply mul_nonneg (norm_nonneg _)
  apply Finset.sum_nonneg
  intro l hl
  apply Real.rpow_nonneg
  exact div_nonneg (catlinA_nonneg p l q.1) (abs_nonneg _)

/- accepted add_to_file helper 14 -/
lemma abs_deriv_log_neg_catlinR_le {m : ℕ} {p : MvPolynomial (Fin 2) ℂ}
    (hreal : ∀ z : ℂ, (evalDiag z p).im = 0)
    {γ : ℝ → ℂ × ℂ} {v : ℂ × ℂ} {u : ℝ}
    (hγ : HasDerivAt γ v u) (hr : catlinR p (γ u) < 0) :
    |deriv (fun u => Real.log (-catlinR p (γ u))) u| ≤
      catlinM m p (γ u) v := by
  let R : ℝ := catlinR p (γ u)
  let X : ℂ := v.2 + 2 * v.1 * catlinPz p (γ u).1
  have hR := hasDerivAt_catlinR_comp (p:=p) hreal hγ
  have hnegR : HasDerivAt (fun u => -catlinR p (γ u)) (-X.re) u := by
    simpa [X] using hR.neg
  have hlog : HasDerivAt (fun u => Real.log (-catlinR p (γ u)))
      ((-X.re) / (-R)) u := by
    apply hnegR.log
    exact ne_of_gt (neg_pos.mpr hr)
  have hder : deriv (fun u => Real.log (-catlinR p (γ u))) u = (-X.re) / (-R) :=
    hlog.deriv
  have habs_eq : |deriv (fun u => Real.log (-catlinR p (γ u))) u| = |X.re| / |R| := by
    rw [hder]
    rw [abs_div]
    simp [R]
  rw [habs_eq]
  have hden : 0 < |R| := abs_pos.mpr (ne_of_lt hr)
  have hre : |X.re| ≤ ‖X‖ := Complex.abs_re_le_norm X
  have hdiv : |X.re| / |R| ≤ ‖X‖ / |R| := div_le_div_of_nonneg_right hre (le_of_lt hden)
  exact hdiv.trans (catlinM_first_le m p (γ u) v)

/- accepted add_to_file helper 15 -/
lemma ae_imp_of_eqOn_Ioo_Ioc {f g : ℝ → ℝ} {a b : ℝ}
    (hfg : Set.EqOn f g (Set.Ioo a b)) :
    ∀ᵐ x ∂MeasureTheory.volume, x ∈ Set.Ioc a b → f x = g x := by
  change MeasureTheory.volume {x | ¬(x ∈ Set.Ioc a b → f x = g x)} = 0
  refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.NoAtoms.measure_singleton b)
  intro x hx
  by_cases hxb : x = b
  · exact hxb
  · exfalso
    rw [Set.mem_setOf_eq, Classical.not_imp] at hx
    have hxlt : x < b := lt_of_le_of_ne hx.1.2 hxb
    exact hx.2 (hfg ⟨hx.1.1,hxlt⟩)

lemma intervalIntegral_congr_of_eqOn_Ioo_of_le {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfg : Set.EqOn f g (Set.Ioo a b)) :
    ∫ x in a..b, f x = ∫ x in a..b, g x := by
  apply intervalIntegral.integral_congr_ae
  have h := ae_imp_of_eqOn_Ioo_Ioc hfg
  filter_upwards [h] with x hx
  intro hxmem
  have hxmem' : x ∈ Set.Ioc a b := by simpa [Set.uIoc, hab] using hxmem
  exact hx hxmem'

/- accepted add_to_file helper 16 -/
lemma intervalIntegrable_of_continuousOn_eqOn_Ioo {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hfg : Set.EqOn f g (Set.Ioo a b)) :
    IntervalIntegrable g MeasureTheory.volume a b := by
  have hFIoo : MeasureTheory.IntegrableOn f (Set.Ioo a b) MeasureTheory.volume := by
    have h := hf.integrableOn_Icc (μ:=MeasureTheory.volume)
    exact h.mono_set Set.Ioo_subset_Icc_self
  have hGIoo : MeasureTheory.IntegrableOn g (Set.Ioo a b) MeasureTheory.volume := by
    exact hFIoo.congr (Set.EqOn.aeEq_restrict hfg measurableSet_Ioo)
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mpr hGIoo

/- accepted add_to_file helper 17 -/
lemma eqOn_deriv_derivWithin_Ioo_of_contDiffOn {γ : ℝ → ℂ × ℂ} {a b : ℝ}
    (hab : a < b) (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b)) :
    Set.EqOn (fun u => deriv γ u) (fun u => derivWithin γ (Set.Icc a b) u)
      (Set.Ioo a b) := by
  intro u huI
  have hIcc_nhds : Set.Icc a b ∈ nhds u := Icc_mem_nhds huI.1 huI.2
  have hdiff : DifferentiableWithinAt ℝ γ (Set.Icc a b) u :=
    hγ.differentiableOn (by norm_num) u (Set.Ioo_subset_Icc_self huI)
  have hwithin : HasDerivWithinAt γ (derivWithin γ (Set.Icc a b) u) (Set.Icc a b) u :=
    hdiff.hasDerivWithinAt
  have hat : HasDerivAt γ (derivWithin γ (Set.Icc a b) u) u := hwithin.hasDerivAt hIcc_nhds
  exact hat.deriv

lemma intervalIntegrable_catlinM_deriv_of_contDiffOn {m : ℕ} {p : MvPolynomial (Fin 2) ℂ}
    {γ : ℝ → ℂ × ℂ} {a b : ℝ} (hab : a < b)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b))
    (hr : ∀ u ∈ Set.Icc a b, catlinR p (γ u) < 0) :
    IntervalIntegrable (fun u => catlinM m p (γ u) (deriv γ u))
      MeasureTheory.volume a b := by
  let F : ℝ → ℝ := fun u => catlinM m p (γ u) (derivWithin γ (Set.Icc a b) u)
  have hderiv : ContinuousOn (fun u => derivWithin γ (Set.Icc a b) u) (Set.Icc a b) :=
    hγ.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)
  have hF : ContinuousOn F (Set.Icc a b) := by
    exact continuousOn_catlinM_comp hγ.continuousOn hderiv hr
  have heq : Set.EqOn F (fun u => catlinM m p (γ u) (deriv γ u)) (Set.Ioo a b) := by
    intro u hu
    have hd := eqOn_deriv_derivWithin_Ioo_of_contDiffOn hab hγ hu
    simp [F, hd]
  exact intervalIntegrable_of_continuousOn_eqOn_Ioo (le_of_lt hab) hF heq

/- accepted add_to_file helper 18 -/
lemma contDiff_catlinP (p : MvPolynomial (Fin 2) ℂ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (catlinP p) := by
  exact Complex.reCLM.contDiff.comp (contDiff_evalDiag p)

lemma contDiff_catlinR (p : MvPolynomial (Fin 2) ℂ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (catlinR p) := by
  have h2 : ContDiff ℝ n fun q : ℂ × ℂ => q.2.re :=
    Complex.reCLM.contDiff.comp (ContinuousLinearMap.snd ℝ ℂ ℂ).contDiff
  have h1 : ContDiff ℝ n fun q : ℂ × ℂ => catlinP p q.1 :=
    (contDiff_catlinP p).comp (ContinuousLinearMap.fst ℝ ℂ ℂ).contDiff
  exact h2.add h1

/- accepted add_to_file helper 19 -/
lemma eqOn_deriv_derivWithin_Ioo_of_contDiffOn_generic {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {γ : ℝ → E} {a b : ℝ}
    (hab : a < b) (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b)) :
    Set.EqOn (fun u => deriv γ u) (fun u => derivWithin γ (Set.Icc a b) u)
      (Set.Ioo a b) := by
  intro u huI
  have hIcc_nhds : Set.Icc a b ∈ nhds u := Icc_mem_nhds huI.1 huI.2
  have hdiff : DifferentiableWithinAt ℝ γ (Set.Icc a b) u :=
    hγ.differentiableOn (by norm_num) u (Set.Ioo_subset_Icc_self huI)
  have hwithin : HasDerivWithinAt γ (derivWithin γ (Set.Icc a b) u) (Set.Icc a b) u :=
    hdiff.hasDerivWithinAt
  have hat : HasDerivAt γ (derivWithin γ (Set.Icc a b) u) u := hwithin.hasDerivAt hIcc_nhds
  exact hat.deriv

/- accepted add_to_file helper 20 -/
lemma catlin_segment_log_bound {m : ℕ} {p : MvPolynomial (Fin 2) ℂ}
    (hreal : ∀ z : ℂ, (evalDiag z p).im = 0)
    {γ : ℝ → ℂ × ℂ} {a b : ℝ} (hab : a < b)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b))
    (hr : ∀ u ∈ Set.Icc a b, catlinR p (γ u) < 0) :
    |Real.log (-catlinR p (γ b)) - Real.log (-catlinR p (γ a))| ≤
      ∫ u in a..b, catlinM m p (γ u) (deriv γ u) := by
  let g : ℝ → ℝ := fun u => Real.log (-catlinR p (γ u))
  let Fg : ℝ → ℝ := fun u => |derivWithin g (Set.Icc a b) u|
  let Fm : ℝ → ℝ := fun u => catlinM m p (γ u) (derivWithin γ (Set.Icc a b) u)
  have hRγ : ContDiffOn ℝ 1 (fun u => catlinR p (γ u)) (Set.Icc a b) := by
    exact (contDiff_catlinR p).comp_contDiffOn hγ
  have hg : ContDiffOn ℝ 1 g (Set.Icc a b) := by
    apply ContDiffOn.log hRγ.neg
    intro u hu
    exact ne_of_gt (neg_pos.mpr (hr u hu))
  have hderivg : ContinuousOn (fun u => derivWithin g (Set.Icc a b) u) (Set.Icc a b) :=
    hg.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)
  have hFg : ContinuousOn Fg (Set.Icc a b) := hderivg.norm
  have hderivγ : ContinuousOn (fun u => derivWithin γ (Set.Icc a b) u) (Set.Icc a b) :=
    hγ.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)
  have hFm : ContinuousOn Fm (Set.Icc a b) := by
    exact continuousOn_catlinM_comp hγ.continuousOn hderivγ hr
  have hineq_Ioo : ∀ u ∈ Set.Ioo a b, Fg u ≤ Fm u := by
    intro u huI
    have hdg := eqOn_deriv_derivWithin_Ioo_of_contDiffOn_generic (E:=ℝ) hab hg huI
    have hdg' : deriv (fun u => Real.log (-catlinR p (γ u))) u =
        derivWithin (fun u => Real.log (-catlinR p (γ u))) (Set.Icc a b) u := by
      simpa [g] using hdg
    have hdiffγ : DifferentiableWithinAt ℝ γ (Set.Icc a b) u :=
      hγ.differentiableOn (by norm_num) u (Set.Ioo_subset_Icc_self huI)
    have hwithinγ : HasDerivWithinAt γ (derivWithin γ (Set.Icc a b) u) (Set.Icc a b) u :=
      hdiffγ.hasDerivWithinAt
    have hAtγ : HasDerivAt γ (derivWithin γ (Set.Icc a b) u) u :=
      hwithinγ.hasDerivAt (Icc_mem_nhds huI.1 huI.2)
    have hbound := abs_deriv_log_neg_catlinR_le (m:=m) hreal hAtγ
      (hr u (Set.Ioo_subset_Icc_self huI))
    change |derivWithin (fun u => Real.log (-catlinR p (γ u))) (Set.Icc a b) u| ≤
      catlinM m p (γ u) (derivWithin γ (Set.Icc a b) u)
    rw [← hdg']
    exact hbound
  have hineq : ∀ u ∈ Set.Icc a b, Fg u ≤ Fm u := by
    intro u hu
    have hcl : u ∈ closure (Set.Ioo a b) := by
      rw [closure_Ioo (ne_of_lt hab)]
      exact hu
    exact le_on_closure hineq_Ioo (by simpa [closure_Ioo (ne_of_lt hab)] using hFg)
      (by simpa [closure_Ioo (ne_of_lt hab)] using hFm) hcl
  have hFTC : ∫ u in a..b, derivWithin g (Set.Icc a b) u = g b - g a :=
    intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc hg (le_of_lt hab)
  have hnorm : ‖∫ u in a..b, derivWithin g (Set.Icc a b) u‖ ≤
      ∫ u in a..b, ‖derivWithin g (Set.Icc a b) u‖ :=
    intervalIntegral.norm_integral_le_integral_norm (le_of_lt hab)
  have hFgu : ContinuousOn Fg (Set.uIcc a b) := by
    simpa [Set.uIcc, le_of_lt hab] using hFg
  have hFmu : ContinuousOn Fm (Set.uIcc a b) := by
    simpa [Set.uIcc, le_of_lt hab] using hFm
  have hintFg : IntervalIntegrable Fg MeasureTheory.volume a b := hFgu.intervalIntegrable
  have hintFm : IntervalIntegrable Fm MeasureTheory.volume a b := hFmu.intervalIntegrable
  have hint : ∫ u in a..b, Fg u ≤ ∫ u in a..b, Fm u :=
    intervalIntegral.integral_mono_on (le_of_lt hab) hintFg hintFm hineq
  have heqFm : Set.EqOn Fm (fun u => catlinM m p (γ u) (deriv γ u)) (Set.Ioo a b) := by
    intro u hu
    have hdγ := eqOn_deriv_derivWithin_Ioo_of_contDiffOn_generic (E:=ℂ × ℂ) hab hγ hu
    simp [Fm, hdγ]
  have hint_eq : ∫ u in a..b, Fm u =
      ∫ u in a..b, catlinM m p (γ u) (deriv γ u) :=
    intervalIntegral_congr_of_eqOn_Ioo_of_le (le_of_lt hab) heqFm
  have hmain : |g b - g a| ≤ ∫ u in a..b, Fm u := by
    rw [← hFTC]
    have hnorm' : |∫ u in a..b, derivWithin g (Set.Icc a b) u| ≤ ∫ u in a..b, Fg u := by
      simpa [Fg, Real.norm_eq_abs] using hnorm
    exact hnorm'.trans hint
  exact hmain.trans_eq hint_eq

/- accepted add_to_file helper 21 -/
lemma catlin_piecewise_path_log_bound {m : ℕ} {p : MvPolynomial (Fin 2) ℂ}
    (hreal : ∀ z : ℂ, (evalDiag z p).im = 0)
    {γ : ℝ → ℂ × ℂ} (hpc : PiecewiseC1Curve γ)
    (hΩ : ∀ u ∈ Set.Icc (0 : ℝ) 1, catlinR p (γ u) < 0) :
    |Real.log (-catlinR p (γ 1)) - Real.log (-catlinR p (γ 0))| ≤
      ∫ u in (0 : ℝ)..1, catlinM m p (γ u) (deriv γ u) := by
  rcases hpc with ⟨n,u,hu0,hu1,hmono,hseg⟩
  let idx : ℕ → Fin (n + 1) := fun k =>
    ⟨min k n, Nat.lt_succ_of_le (min_le_right k n)⟩
  let a : ℕ → ℝ := fun k => u (idx k)
  let g : ℝ → ℝ := fun u => Real.log (-catlinR p (γ u))
  let F : ℕ → ℝ := fun k => g (a k)
  have ha0 : a 0 = 0 := by
    simp [a, idx, hu0]
  have han : a n = 1 := by
    have hid : idx n = ⟨n, Nat.lt_add_one n⟩ := by
      ext
      simp [idx]
    simp [a, hid, hu1]
  have hF0 : F 0 = g 0 := by
    simp [F, ha0]
  have hFn : F n = g 1 := by
    simp [F, han]
  have htele : |F n - F 0| ≤ ∑ k ∈ Finset.range n, |F (k+1) - F k| := by
    rw [← Finset.sum_range_sub F n]
    exact IsAbsoluteValue.abv_sum abs (fun k => F (k+1)-F k) (Finset.range n)
  have hsegbound : ∀ k ∈ Finset.range n,
      |F (k+1)-F k| ≤ ∫ x in a k..a (k+1), catlinM m p (γ x) (deriv γ x) := by
    intro k hk
    have hkn : k < n := Finset.mem_range.mp hk
    let i : Fin n := ⟨k,hkn⟩
    have ha : a k = u i.castSucc := by
      apply congrArg u
      ext
      simp [idx, i, hkn.le]
    have hb : a (k+1) = u i.succ := by
      apply congrArg u
      ext
      simp [idx, i, hkn]
    have hab : u i.castSucc < u i.succ := hmono Fin.castSucc_lt_succ
    have hrseg : ∀ x ∈ Set.Icc (u i.castSucc) (u i.succ), catlinR p (γ x) < 0 := by
      intro x hx
      have h0a : (0:ℝ) ≤ u i.castSucc := by
        have hm := hmono.monotone (Fin.zero_le i.castSucc)
        simpa [hu0] using hm
      have hb1 : u i.succ ≤ 1 := by
        have hm := hmono.monotone (Fin.le_last i.succ)
        have hid : (Fin.last n : Fin (n+1)) = ⟨n, Nat.lt_add_one n⟩ := by ext; rfl
        simpa [hid, hu1] using hm
      exact hΩ x ⟨h0a.trans hx.1, hx.2.trans hb1⟩
    have hbnd := catlin_segment_log_bound (m:=m) hreal hab (hseg i) hrseg
    have hFk : F k = g (u i.castSucc) := by
      simp [F, ha]
    have hFk1 : F (k+1) = g (u i.succ) := by
      simp [F, hb]
    rw [hFk, hFk1, ha, hb]
    simpa [g] using hbnd
  have hint : ∀ k < n,
      IntervalIntegrable (fun x => catlinM m p (γ x) (deriv γ x))
        MeasureTheory.volume (a k) (a (k+1)) := by
    intro k hkn
    let i : Fin n := ⟨k,hkn⟩
    have ha : a k = u i.castSucc := by
      apply congrArg u
      ext
      simp [idx, i, hkn.le]
    have hb : a (k+1) = u i.succ := by
      apply congrArg u
      ext
      simp [idx, i, hkn]
    have hab : u i.castSucc < u i.succ := hmono Fin.castSucc_lt_succ
    have hrseg : ∀ x ∈ Set.Icc (u i.castSucc) (u i.succ), catlinR p (γ x) < 0 := by
      intro x hx
      have h0a : (0:ℝ) ≤ u i.castSucc := by
        have hm := hmono.monotone (Fin.zero_le i.castSucc)
        simpa [hu0] using hm
      have hb1 : u i.succ ≤ 1 := by
        have hm := hmono.monotone (Fin.le_last i.succ)
        have hid : (Fin.last n : Fin (n+1)) = ⟨n, Nat.lt_add_one n⟩ := by ext; rfl
        simpa [hid, hu1] using hm
      exact hΩ x ⟨h0a.trans hx.1, hx.2.trans hb1⟩
    have hi := intervalIntegrable_catlinM_deriv_of_contDiffOn (m:=m) (p:=p) hab (hseg i) hrseg
    simpa [ha, hb] using hi
  have hsumint := intervalIntegral.sum_integral_adjacent_intervals
    (f:=fun x => catlinM m p (γ x) (deriv γ x)) (a:=a) (n:=n) hint
  have hsum_abs : |F n-F 0| ≤
      ∑ k ∈ Finset.range n, ∫ x in a k..a (k+1), catlinM m p (γ x) (deriv γ x) := by
    exact htele.trans (Finset.sum_le_sum hsegbound)
  rw [hsumint, ha0, han] at hsum_abs
  simpa [hF0, hFn, g] using hsum_abs

/- accepted add_to_file helper 22 -/
lemma setIntegral_Icc_zero_one_eq_intervalIntegral (f : ℝ → ℝ) :
    ∫ u in Set.Icc (0 : ℝ) 1, f u = ∫ u in (0 : ℝ)..1, f u := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact (intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)).symm

/- accepted add_to_file helper 23 -/
lemma deriv_vertical_second (w₀ : ℂ) (a s c u : ℝ) :
    deriv (fun x : ℝ => w₀ - ((a * Real.exp (-(s+c*x)) : ℝ) : ℂ)) u =
      (((a*c*Real.exp (-(s+c*u)) : ℝ) : ℂ)) := by
  have hlin : HasDerivAt (fun x : ℝ => s+c*x) c u := by
    simpa using ((hasDerivAt_id u).const_mul c).const_add s
  have harg : HasDerivAt (fun x : ℝ => -(s+c*x)) (-c) u := hlin.neg
  have he : HasDerivAt (fun x : ℝ => Real.exp (-(s+c*x)))
    (Real.exp (-(s+c*u)) * (-c)) u := by
    exact (Real.hasDerivAt_exp (-(s+c*u))).comp u harg
  have hm : HasDerivAt (fun x : ℝ => a * Real.exp (-(s+c*x)))
    (a * (Real.exp (-(s+c*u)) * (-c))) u := he.const_mul a
  have hc := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u hm)
  have hsub := (hasDerivAt_const u w₀).sub hc
  have hfun : ((fun _ : ℝ => w₀) - Complex.ofRealCLM ∘ fun x : ℝ => a * Real.exp (-(s+c*x))) =
      (fun x : ℝ => w₀ - ((a * Real.exp (-(s+c*x)) : ℝ) : ℂ)) := by
    ext x
    rfl
  rw [hfun] at hsub
  rw [hsub.deriv]
  simp
  ring

/- accepted add_to_file helper 24 -/
lemma contDiff_vertical_curve (z₀ w₀ : ℂ) (a s c : ℝ) :
    ContDiff ℝ 1 (fun u : ℝ =>
      (z₀, w₀ - ((a * Real.exp (-(s + c * u)) : ℝ) : ℂ))) := by
  have h1 : ContDiff ℝ 1 (fun u : ℝ => a * Real.exp (-(s+c*u))) := by
    fun_prop
  exact contDiff_const.prodMk (contDiff_const.sub (Complex.ofRealCLM.contDiff.comp h1))

/- accepted add_to_file helper 25 -/
lemma contDiff_vertical_second (w₀ : ℂ) (a s c : ℝ) :
    ContDiff ℝ 1 (fun u : ℝ => w₀ - ((a * Real.exp (-(s+c*u)) : ℝ) : ℂ)) := by
  have h1 : ContDiff ℝ 1 (fun u : ℝ => a * Real.exp (-(s+c*u))) := by
    fun_prop
  exact contDiff_const.sub (Complex.ofRealCLM.contDiff.comp h1)

lemma hasDerivAt_vertical_curve (z₀ w₀ : ℂ) (a s c u : ℝ) :
    HasDerivAt (fun x : ℝ =>
      (z₀, w₀ - ((a * Real.exp (-(s+c*x)) : ℝ) : ℂ)))
      (0, (((a*c*Real.exp (-(s+c*u)) : ℝ) : ℂ))) u := by
  have hdiff := ((contDiff_vertical_second w₀ a s c).differentiable (by norm_num)) u
  have hsecond := hdiff.hasDerivAt
  rw [deriv_vertical_second w₀ a s c u] at hsecond
  exact (hasDerivAt_const u z₀).prodMk hsecond

/- accepted add_to_file helper 26 -/
lemma catlinM_vertical {m : ℕ} {p : MvPolynomial (Fin 2) ℂ} {q : ℂ × ℂ}
    {a c e : ℝ} (ha : 0 < a) (he : 0 < e)
    (hr : catlinR p q = -a*e) :
    catlinM m p q (0, (((a*c*e:ℝ) : ℂ))) = |c| := by
  have hpos : 0 < a*e := mul_pos ha he
  unfold catlinM
  rw [hr]
  simp [hpos.ne', abs_of_pos hpos]
  field_simp [hpos.ne']
  rw [abs_of_pos ha, abs_of_pos he]
  ring

/- accepted add_to_file helper 27 -/
lemma catlinR_vertical {p : MvPolynomial (Fin 2) ℂ} {z₀ w₀ : ℂ} {a t : ℝ}
    (hb : catlinR p (z₀,w₀) = 0) :
    catlinR p (z₀, w₀ - ((a * Real.exp (-t) : ℝ) : ℂ)) =
      -a * Real.exp (-t) := by
  have hb' : w₀.re + catlinP p z₀ = 0 := by
    simpa [catlinR] using hb
  have h : (Complex.exp (-(t : ℂ))).re = Real.exp (-t) := by
    rw [show -(t : ℂ) = (↑(-t) : ℂ) by simp, Complex.exp_ofReal_re]
  simp [catlinR, h]
  nlinarith

/- accepted add_to_file helper 28 -/
lemma log_neg_catlinR_vertical {p : MvPolynomial (Fin 2) ℂ} {z₀ w₀ : ℂ} {a t : ℝ}
    (ha : 0 < a) (hb : catlinR p (z₀,w₀) = 0) :
    Real.log (-catlinR p (z₀, w₀ - ((a * Real.exp (-t) : ℝ) : ℂ))) =
      Real.log a - t := by
  rw [catlinR_vertical hb]
  have hae : a * Real.exp (-t) ≠ 0 := by
    exact mul_ne_zero (ne_of_gt ha) (ne_of_gt (Real.exp_pos _))
  rw [show -(-a * Real.exp (-t)) = a * Real.exp (-t) by ring]
  rw [Real.log_mul (ne_of_gt ha) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  ring

/- accepted add_to_file helper 29 -/
lemma vertical_catlin_length {m : ℕ} {p : MvPolynomial (Fin 2) ℂ} {z₀ w₀ : ℂ}
    {a s t : ℝ} (ha : 0 < a) (hb : catlinR p (z₀,w₀) = 0) :
    ∫ u in Set.Icc (0 : ℝ) 1,
      catlinM m p
        ((z₀, w₀ - ((a * Real.exp (-(s + (t-s)*u)) : ℝ) : ℂ)))
        (deriv (fun x : ℝ =>
          (z₀, w₀ - ((a * Real.exp (-(s + (t-s)*x)) : ℝ) : ℂ))) u) = |s-t| := by
  have hpoint : ∀ u : ℝ,
      catlinM m p
        ((z₀, w₀ - ((a * Real.exp (-(s + (t-s)*u)) : ℝ) : ℂ)))
        (deriv (fun x : ℝ =>
          (z₀, w₀ - ((a * Real.exp (-(s + (t-s)*x)) : ℝ) : ℂ))) u) = |t-s| := by
    intro u
    have hd := (hasDerivAt_vertical_curve z₀ w₀ a s (t-s) u).deriv
    have hr := catlinR_vertical (p:=p) (z₀:=z₀) (w₀:=w₀) (a:=a) (t:=s+(t-s)*u) hb
    have hm := catlinM_vertical (m:=m) (p:=p)
      (q:=(z₀, w₀ - ((a * Real.exp (-(s+(t-s)*u)) : ℝ) : ℂ)))
      (a:=a) (c:=t-s) (e:=Real.exp (-(s+(t-s)*u))) ha (Real.exp_pos _) hr
    rw [hd]
    exact hm
  rw [setIntegral_Icc_zero_one_eq_intervalIntegral]
  have hc : ∫ u in (0:ℝ)..1,
      catlinM m p
        ((z₀, w₀ - ((a * Real.exp (-(s + (t-s)*u)) : ℝ) : ℂ)))
        (deriv (fun x : ℝ =>
          (z₀, w₀ - ((a * Real.exp (-(s + (t-s)*x)) : ℝ) : ℂ))) u)
      = ∫ _ in (0:ℝ)..1, |t-s| :=
    intervalIntegral.integral_congr (fun u hu => hpoint u)
  rw [hc]
  rw [intervalIntegral.integral_const]
  simp [abs_sub_comm]

/- verified submission -/
theorem catlin_vertical_curve_is_geodesic
    (m : ℕ) (p : MvPolynomial (Fin 2) ℂ) :
    let evalAt : ℂ → MvPolynomial (Fin 2) ℂ → ℂ :=
      fun z q => MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z else star z) q
    let D : ℕ → ℕ → ℂ → ℂ := fun j k z =>
      evalAt z ((MvPolynomial.pderiv (1 : Fin 2))^[k]
        ((MvPolynomial.pderiv (0 : Fin 2))^[j] p))
    let P : ℂ → ℝ := fun z => (evalAt z p).re
    let Pz : ℂ → ℂ := fun z => D 1 0 z
    let A : ℕ → ℂ → ℝ := fun l z =>
      sSup {u : ℝ | ∃ j k : ℕ, 0 < j ∧ 0 < k ∧ j + k = l ∧ u = ‖D j k z‖}
    let r : ℂ × ℂ → ℝ := fun q => q.2.re + P q.1
    let Ω : Set (ℂ × ℂ) := {q | r q < 0}
    let M : (ℂ × ℂ) → (ℂ × ℂ) → ℝ := fun q v =>
      ‖v.2 + 2 * v.1 * Pz q.1‖ / |r q| +
        ‖v.1‖ * ∑ l ∈ Finset.Icc 2 m,
          Real.rpow (A l q.1 / |r q|) (1 / (l : ℝ))
    let PiecewiseC1 : (ℝ → ℂ × ℂ) → Prop := fun γ =>
      ∃ n : ℕ, ∃ u : Fin (n + 1) → ℝ,
        u 0 = 0 ∧ u ⟨n, Nat.lt_add_one n⟩ = 1 ∧ StrictMono u ∧
          ∀ i : Fin n,
            ContDiffOn ℝ 1 γ (Set.Icc (u i.castSucc) (u i.succ))
    let d : (ℂ × ℂ) → (ℂ × ℂ) → ℝ := fun q₁ q₂ =>
      sInf {L : ℝ | ∃ γ : ℝ → ℂ × ℂ,
        PiecewiseC1 γ ∧
        γ 0 = q₁ ∧ γ 1 = q₂ ∧
        (∀ u ∈ Set.Icc (0 : ℝ) 1, γ u ∈ Ω) ∧
        L = ∫ u in Set.Icc (0 : ℝ) 1, M (γ u) (deriv γ u)}
    2 ≤ m →
    p.totalDegree = m →
    (∀ z : ℂ, (evalAt z p).im = 0) →
    P 0 = 0 →
    (∀ z : ℂ, 0 ≤ (D 1 1 z).re) →
    (∀ j : ℕ, 0 < j → p.coeff (Finsupp.single (0 : Fin 2) j) = 0) →
    (∀ k : ℕ, 0 < k → p.coeff (Finsupp.single (1 : Fin 2) k) = 0) →
    ∀ (z₀ w₀ : ℂ) (a : ℝ),
      0 < a →
      (z₀, w₀) ∈ frontier Ω →
      let σ : ℝ → ℂ × ℂ := fun t =>
        (z₀, w₀ - ((a * Real.exp (-t) : ℝ) : ℂ))
      (∀ t : ℝ, σ t ∈ Ω) ∧
        ∀ s t : ℝ, d (σ s) (σ t) = |s - t| := by
  intro evalAt D P Pz A r Ω M PiecewiseC1 d hm hdeg hreal hP0 hsub hpurez hpurebar
  intro z₀ w₀ a ha hfront σ
  have heval : evalAt = evalDiag := rfl
  have hD : D = diagDer p := rfl
  have hP : P = catlinP p := rfl
  have hPz : Pz = catlinPz p := rfl
  have hA : A = catlinA p := rfl
  have hr : r = catlinR p := rfl
  have hM : M = catlinM m p := rfl
  have hPC : PiecewiseC1 = PiecewiseC1Curve := rfl
  have hrealG : ∀ z : ℂ, (evalDiag z p).im = 0 := by
    intro z
    rw [← heval]
    exact hreal z
  have hΩdef : Ω = {q | catlinR p q < 0} := by
    ext q
    change (r q < 0) ↔ (catlinR p q < 0)
    rw [hr]
  have hb : catlinR p (z₀,w₀) = 0 :=
    frontier_sublevel_eq_zero (continuous_catlinR p) hΩdef hfront
  constructor
  · intro t
    show catlinR p (σ t) < 0
    dsimp [σ]
    rw [catlinR_vertical hb]
    have hpos : 0 < a * Real.exp (-t) := mul_pos ha (Real.exp_pos _)
    linarith
  · intro s t
    let S : Set ℝ := {L : ℝ | ∃ γ : ℝ → ℂ × ℂ,
      PiecewiseC1 γ ∧
      γ 0 = σ s ∧ γ 1 = σ t ∧
      (∀ u ∈ Set.Icc (0 : ℝ) 1, γ u ∈ Ω) ∧
      L = ∫ u in Set.Icc (0 : ℝ) 1, M (γ u) (deriv γ u)}
    have hd : d (σ s) (σ t) = sInf S := rfl
    let γ : ℝ → ℂ × ℂ := fun u =>
      (z₀, w₀ - ((a * Real.exp (-(s + (t-s)*u)) : ℝ) : ℂ))
    have hγpc : PiecewiseC1Curve γ :=
      PiecewiseC1Curve_single (contDiff_vertical_curve z₀ w₀ a s (t-s))
    have hγ0 : γ 0 = σ s := by
      simp [γ, σ]
    have hγ1 : γ 1 = σ t := by
      dsimp [γ, σ]
      ext
      · rfl
      · congr 1
        congr 1
        congr 1
        ring
    have hγΩ : ∀ u ∈ Set.Icc (0 : ℝ) 1, γ u ∈ Ω := by
      intro u hu
      show catlinR p (γ u) < 0
      dsimp [γ]
      rw [catlinR_vertical hb]
      have hpos : 0 < a * Real.exp (-(s+(t-s)*u)) :=
        mul_pos ha (Real.exp_pos _)
      linarith
    have hγlen : |s-t| = ∫ u in Set.Icc (0 : ℝ) 1, M (γ u) (deriv γ u) := by
      rw [hM]
      exact (vertical_catlin_length (m:=m) (p:=p) (z₀:=z₀) (w₀:=w₀) (a:=a) (s:=s) (t:=t) ha hb).symm
    have hnonempty : S.Nonempty := by
      refine ⟨|s-t|, γ, ?_, hγ0, hγ1, hγΩ, hγlen⟩
      simpa [hPC] using hγpc
    have hbdd : BddBelow S := by
      refine ⟨0, ?_⟩
      rintro L ⟨δ,hδpc,hδ0,hδ1,hδΩ,hL⟩
      rw [hL, hM]
      apply MeasureTheory.integral_nonneg
      intro u
      exact catlinM_nonneg m p (δ u) (deriv δ u)
    have hlower : ∀ L ∈ S, |s-t| ≤ L := by
      rintro L ⟨δ,hδpc,hδ0,hδ1,hδΩ,hL⟩
      have hδpcG : PiecewiseC1Curve δ := by
        simpa [hPC] using hδpc
      have hδΩG : ∀ u ∈ Set.Icc (0 : ℝ) 1, catlinR p (δ u) < 0 := by
        intro u hu
        have huΩ := hδΩ u hu
        rwa [hΩdef] at huΩ
      have hbound := catlin_piecewise_path_log_bound (m:=m) (p:=p) hrealG hδpcG hδΩG
      rw [hδ0, hδ1] at hbound
      have hlogdiff :
          |Real.log (-catlinR p (σ t)) - Real.log (-catlinR p (σ s))| = |s-t| := by
        dsimp [σ]
        rw [log_neg_catlinR_vertical ha hb, log_neg_catlinR_vertical ha hb]
        have h : Real.log a - t - (Real.log a - s) = s-t := by ring
        rw [h]
      rw [hlogdiff] at hbound
      rw [hL, hM, setIntegral_Icc_zero_one_eq_intervalIntegral]
      exact hbound
    have hle : |s-t| ≤ sInf S := le_csInf hnonempty hlower
    have hge : sInf S ≤ |s-t| := csInf_le hbdd (by
      refine ⟨γ, ?_, hγ0, hγ1, hγΩ, hγlen⟩
      simpa [hPC] using hγpc)
    rw [hd]
    exact le_antisymm hge hle

/- Scopes closed implicitly by EOF in the original file. -/
end

end Rollout_p0912_catlin_vertical_curve_is_geodesic
