import Mathlib

/- Generated only to amortize Mathlib loading during graph export. -/

namespace Rollout_p2476_approximatepointspectrum_subset_closure_sc

/- accepted add_to_file helper 1 -/
lemma srg_sqrt_sq_add_sq_le_abs_add {u q : ℝ} (hq : 0 ≤ q) :
    Real.sqrt (u ^ 2 + q ^ 2) ≤ |u| + q := by
  apply le_of_sq_le_sq
  · rw [Real.sq_sqrt (by positivity)]
    nlinarith [sq_abs u, abs_nonneg u, hq]
  · positivity

lemma srg_abs_sub_sqrt_sq_add_sq_le {u q : ℝ} (hq : 0 ≤ q) :
    |(|u| - Real.sqrt (u ^ 2 + q ^ 2))| ≤ q := by
  have hupper : Real.sqrt (u ^ 2 + q ^ 2) ≤ |u| + q :=
    srg_sqrt_sq_add_sq_le_abs_add hq
  have hlower : |u| ≤ Real.sqrt (u ^ 2 + q ^ 2) := by
    apply Real.abs_le_sqrt
    nlinarith [sq_nonneg q]
  rw [abs_sub_le_iff]
  constructor
  · nlinarith [Real.sqrt_nonneg (u ^ 2 + q ^ 2)]
  · nlinarith

lemma scaledRelativeGraph_polar_approx
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) {x : H} (hx : ‖x‖ = 1) (w : ℂ) :
    ∃ z : ℂ,
      (let a : ℝ := (inner ℂ (T x) x).re
       let b : ℝ := Real.sqrt (‖T x‖ ^ 2 - a ^ 2)
       z = (a : ℂ) + Complex.I * (b : ℂ) ∨
         z = (a : ℂ) - Complex.I * (b : ℂ)) ∧
      dist w z ≤ 2 * ‖T x - w • x‖ := by
  let α : ℂ := inner ℂ (T x) x
  let c : ℂ := star α
  let y : H := T x - c • x
  let a : ℝ := α.re
  let b : ℝ := Real.sqrt (‖T x‖ ^ 2 - a ^ 2)
  have hyx : inner ℂ y x = 0 := by
    dsimp [y, c, α]
    rw [inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K, hx]
    simp
  have hxy : inner ℂ x y = 0 := (inner_eq_zero_symm).1 hyx
  have hortho : inner ℂ (c • x) y = 0 := by
    rw [inner_smul_left, hxy]
    simp
  have hpyth : ‖c • x + y‖ ^ 2 = ‖c • x‖ ^ 2 + ‖y‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (c • x) y hortho
    nlinarith
  have hTxeq : c • x + y = T x := by
    simp [y]
  rw [hTxeq] at hpyth
  have hc : ‖c • x‖ = ‖c‖ := by
    simp [norm_smul, hx]
  have hcn : ‖c • x‖ ^ 2 = ‖c‖ ^ 2 := by
    rw [hc]
  have hcre : c.re = a := by
    dsimp [c, a, α]
  have hc_sq : ‖c‖ ^ 2 = a ^ 2 + c.im ^ 2 := by
    calc
      ‖c‖ ^ 2 = Complex.normSq c := by
        rw [Complex.normSq_eq_norm_sq]
      _ = c.re * c.re + c.im * c.im := by
        rw [Complex.normSq_apply]
      _ = a ^ 2 + c.im ^ 2 := by
        rw [hcre]
        ring
  have hb_sq : ‖T x‖ ^ 2 - a ^ 2 = c.im ^ 2 + ‖y‖ ^ 2 := by
    nlinarith
  have hb : b = Real.sqrt (c.im ^ 2 + ‖y‖ ^ 2) := by
    dsimp [b]
    rw [hb_sq]
  have horthod : inner ℂ ((c - w) • x) y = 0 := by
    rw [inner_smul_left, hxy]
    simp
  have hdeq : T x - w • x = (c - w) • x + y := by
    rw [sub_smul]
    simp [y]
  have hpythd : ‖(c - w) • x + y‖ ^ 2 = ‖(c - w) • x‖ ^ 2 + ‖y‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ((c - w) • x) y horthod
    nlinarith
  rw [← hdeq] at hpythd
  have hcwn : ‖(c - w) • x‖ = ‖c - w‖ := by
    simp [norm_smul, hx]
  have hcwnsq : ‖(c - w) • x‖ ^ 2 = ‖c - w‖ ^ 2 := by
    rw [hcwn]
  have hcw_sq : ‖c - w‖ ^ 2 ≤ ‖T x - w • x‖ ^ 2 := by
    nlinarith [sq_nonneg ‖y‖]
  have hy_sq : ‖y‖ ^ 2 ≤ ‖T x - w • x‖ ^ 2 := by
    nlinarith [sq_nonneg ‖c - w‖]
  have hcw_le : ‖c - w‖ ≤ ‖T x - w • x‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hcw_sq
  have hy_le : ‖y‖ ≤ ‖T x - w • x‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hy_sq
  have hsqrt_abs : |(|c.im| - Real.sqrt (c.im ^ 2 + ‖y‖ ^ 2))| ≤ ‖y‖ :=
    srg_abs_sub_sqrt_sq_add_sq_le (norm_nonneg y)
  have hsqrt_abs' : |(|c.im| - b)| ≤ ‖y‖ := by
    simpa [hb] using hsqrt_abs
  by_cases hcim : 0 ≤ c.im
  · refine ⟨a + Complex.I * (b : ℂ), Or.inl rfl, ?_⟩
    have hcdiff :
        c - ((c.re : ℂ) + Complex.I * (b : ℂ)) =
          Complex.I * ((c.im - b : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simp
    have hz : (a : ℂ) + Complex.I * (b : ℂ) =
        (c.re : ℂ) + Complex.I * (b : ℂ) := by
      rw [hcre]
    have hnorm_cz : ‖c - ((a : ℂ) + Complex.I * (b : ℂ))‖ = |c.im - b| := by
      rw [hz, hcdiff]
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have him : |c.im - b| ≤ ‖y‖ := by
      have hcabs : |c.im| = c.im := abs_of_nonneg hcim
      have h := hsqrt_abs'
      rw [hcabs] at h
      exact h
    calc
      dist w ((a : ℂ) + Complex.I * (b : ℂ))
          ≤ dist w c + dist c ((a : ℂ) + Complex.I * (b : ℂ)) :=
        dist_triangle w c _
      _ = ‖w - c‖ + ‖c - ((a : ℂ) + Complex.I * (b : ℂ))‖ := by
        rw [dist_eq_norm, dist_eq_norm]
      _ ≤ ‖T x - w • x‖ + ‖y‖ := by
        gcongr
        · rw [norm_sub_rev]
          exact hcw_le
        · rw [hnorm_cz]
          exact him
      _ ≤ 2 * ‖T x - w • x‖ := by
        nlinarith
  · have hcimneg : c.im < 0 := lt_of_not_ge hcim
    refine ⟨a - Complex.I * (b : ℂ), Or.inr rfl, ?_⟩
    have hcdiff :
        c - ((c.re : ℂ) - Complex.I * (b : ℂ)) =
          Complex.I * ((c.im + b : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simp
    have hz : (a : ℂ) - Complex.I * (b : ℂ) =
        (c.re : ℂ) - Complex.I * (b : ℂ) := by
      rw [hcre]
    have hnorm_cz : ‖c - ((a : ℂ) - Complex.I * (b : ℂ))‖ = |c.im + b| := by
      rw [hz, hcdiff]
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have him : |c.im + b| ≤ ‖y‖ := by
      have hEq : |c.im + b| = |(|c.im| - b)| := by
        rw [abs_of_neg hcimneg]
        rw [show -c.im - b = -(c.im + b) by ring]
        rw [abs_neg]
      rw [hEq]
      exact hsqrt_abs'
    calc
      dist w ((a : ℂ) - Complex.I * (b : ℂ))
          ≤ dist w c + dist c ((a : ℂ) - Complex.I * (b : ℂ)) :=
        dist_triangle w c _
      _ = ‖w - c‖ + ‖c - ((a : ℂ) - Complex.I * (b : ℂ))‖ := by
        rw [dist_eq_norm, dist_eq_norm]
      _ ≤ ‖T x - w • x‖ + ‖y‖ := by
        gcongr
        · rw [norm_sub_rev]
          exact hcw_le
        · rw [hnorm_cz]
          exact him
      _ ≤ 2 * ‖T x - w • x‖ := by
        nlinarith

/- verified submission -/
theorem approximatePointSpectrum_subset_closure_scaledRelativeGraph_polar
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) :
    {w : ℂ |
        ∃ x : ℕ → H,
          (∀ n : ℕ, ‖x n‖ = 1) ∧
            Filter.Tendsto (fun n : ℕ => ‖T (x n) - w • x n‖)
              Filter.atTop (nhds 0)} ⊆
      closure
        {z : ℂ |
          ∃ x : H, ‖x‖ = 1 ∧
            let a : ℝ := (inner ℂ (T x) x).re
            let b : ℝ := Real.sqrt (‖T x‖ ^ 2 - a ^ 2)
            z = (a : ℂ) + Complex.I * (b : ℂ) ∨
              z = (a : ℂ) - Complex.I * (b : ℂ)} := by
  intro w hw
  rcases hw with ⟨x, hxnorm, hlim⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hδ : 0 < ε / 2 := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (ε / 2) hδ
  have hr : ‖T (x N) - w • x N‖ < ε / 2 := by
    have h := hN N le_rfl
    simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using h
  obtain ⟨z, hzgraph, hzdist⟩ :=
    scaledRelativeGraph_polar_approx T (hxnorm N) w
  refine ⟨z, ?_, ?_⟩
  · exact ⟨x N, hxnorm N, hzgraph⟩
  · calc
      dist w z ≤ 2 * ‖T (x N) - w • x N‖ := hzdist
      _ < ε := by nlinarith

end Rollout_p2476_approximatepointspectrum_subset_closure_sc

namespace Rollout_p2937_coinvariants_addmonoidalgebra_eq_range

/- accepted add_to_file helper 1 -/
lemma coinvariants_coaction_coeff
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [DecidableEq N]
    (ψ : M →+ N) (S : AddSubmonoid M)
    (c : AddMonoidAlgebra R S →ₐ[R]
      TensorProduct R (AddMonoidAlgebra R N) (AddMonoidAlgebra R S))
    (hc : ∀ m : S,
      c (AddMonoidAlgebra.single m 1) =
        TensorProduct.tmul R (AddMonoidAlgebra.single (ψ m) 1)
          (AddMonoidAlgebra.single m 1))
    (x : AddMonoidAlgebra R S) (m : S) :
    ((TensorProduct.equivFinsuppOfBasisLeft (AddMonoidAlgebra.basis N R))
      (c x) (ψ m)) m = x m := by
  refine AddMonoidAlgebra.induction_on
    (p := fun y =>
      ((TensorProduct.equivFinsuppOfBasisLeft (AddMonoidAlgebra.basis N R))
        (c y) (ψ m)) m = y m)
    x ?_ ?_ ?_
  · intro q
    rw [AddMonoidAlgebra.of_apply, hc,
      TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
    by_cases hqm : q = m
    · subst m
      simp [AddMonoidAlgebra.basis]
      change ((LinearEquiv.refl R (N →₀ R))
        ((AddMonoidAlgebra.single (ψ q) (1 : R)) : N →₀ R)) (ψ q) = 1
      rw [LinearEquiv.refl_apply]
      exact Finsupp.single_eq_same
    · simp [hqm]
  · intro x y hx hy
    simp [map_add, hx, hy]
  · intro r x hx
    simp [hx]

lemma coinvariants_includeRight_coeff_eq_zero
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [DecidableEq N]
    (ψ : M →+ N) (S : AddSubmonoid M)
    (x : AddMonoidAlgebra R S) (m : S) (hm : ψ m ≠ 0) :
    ((TensorProduct.equivFinsuppOfBasisLeft (AddMonoidAlgebra.basis N R))
      (Algebra.TensorProduct.includeRight x) (ψ m)) m = 0 := by
  rw [Algebra.TensorProduct.includeRight_apply,
    TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
  have hrepr : ((AddMonoidAlgebra.basis N R).repr (1 : AddMonoidAlgebra R N)) (ψ m) = 0 := by
    change ((LinearEquiv.refl R (N →₀ R))
      ((1 : AddMonoidAlgebra R N) : N →₀ R)) (ψ m) = 0
    rw [LinearEquiv.refl_apply]
    rw [AddMonoidAlgebra.one_def]
    exact Finsupp.single_eq_of_ne hm
  rw [hrepr]
  rw [zero_smul]
  rfl

/- verified submission -/
theorem coinvariants_addMonoidAlgebra_eq_range
    {R M₂ M N : Type*} [CommRing R]
    [AddCommGroup M₂] [AddCommGroup M] [AddCommGroup N]
    (φ : M₂ →+ M) (ψ : M →+ N)
    (hφ : Function.Injective φ) (hexact : Function.Exact φ ψ)
    (S : AddSubmonoid M)
    (c : AddMonoidAlgebra R S →ₐ[R]
      TensorProduct R (AddMonoidAlgebra R N) (AddMonoidAlgebra R S))
    (hc : ∀ m : S,
      c (AddMonoidAlgebra.single m 1) =
        TensorProduct.tmul R (AddMonoidAlgebra.single (ψ m) 1)
          (AddMonoidAlgebra.single m 1)) :
    AlgHom.equalizer c Algebra.TensorProduct.includeRight =
      (AddMonoidAlgebra.mapDomainAlgHom R R (φ.addSubmonoidComap S)).range := by
  classical
  let G := AddMonoidAlgebra.mapDomainAlgHom R R (φ.addSubmonoidComap S)
  apply Subalgebra.ext
  intro x
  constructor
  · intro hx
    have heq : c x = Algebra.TensorProduct.includeRight x :=
      (AlgHom.mem_equalizer c Algebra.TensorProduct.includeRight x).mp hx
    let E : TensorProduct R (AddMonoidAlgebra R N) (AddMonoidAlgebra R S) ≃ₗ[R]
        N →₀ AddMonoidAlgebra R S :=
      TensorProduct.equivFinsuppOfBasisLeft (AddMonoidAlgebra.basis N R)
    have hcoeff : ∀ m : S, ψ m ≠ 0 → x m = 0 := by
      intro m hm
      have h1 := congrArg (fun z : N →₀ AddMonoidAlgebra R S => z (ψ m))
        (congrArg E heq)
      have h := congrArg (fun z : AddMonoidAlgebra R S => z m) h1
      dsimp only at h
      rw [show E = TensorProduct.equivFinsuppOfBasisLeft (AddMonoidAlgebra.basis N R) from rfl] at h
      rw [coinvariants_coaction_coeff ψ S c hc x m,
        coinvariants_includeRight_coeff_eq_zero ψ S x m hm] at h
      exact h
    let ι : ↥(AddSubmonoid.comap φ S) →+ S := φ.addSubmonoidComap S
    have hιinj : Function.Injective ι := by
      intro a b hab
      apply Subtype.ext
      apply hφ
      have hval := congrArg Subtype.val hab
      simpa [ι, AddMonoidHom.addSubmonoidComap_apply_coe] using hval
    have hsupport : (x.support : Set S) ⊆ Set.range ι := by
      intro m hm
      have hxm_ne : x m ≠ 0 := Finsupp.mem_support_iff.mp hm
      have hψm : ψ m = 0 := by
        by_contra hne
        exact hxm_ne (hcoeff m hne)
      have hrange : (m : M) ∈ Set.range φ := (hexact m).mp hψm
      rcases hrange with ⟨a, ha⟩
      refine ⟨⟨a, ?_⟩, ?_⟩
      · change φ a ∈ S
        simpa [ha] using m.property
      · apply Subtype.ext
        simpa [ι, AddMonoidHom.addSubmonoidComap_apply_coe] using ha
    let y : AddMonoidAlgebra R ↥(AddSubmonoid.comap φ S) :=
      AddMonoidAlgebra.comapDomain ι hιinj x
    rw [AlgHom.mem_range]
    refine ⟨y, ?_⟩
    change G y = x
    rw [show G = AddMonoidAlgebra.mapDomainAlgHom R R (φ.addSubmonoidComap S) from rfl]
    rw [AddMonoidAlgebra.mapDomainAlgHom_apply]
    exact AddMonoidAlgebra.mapDomain_comapDomain hsupport hιinj
  · intro hx
    rw [AlgHom.mem_range] at hx
    rcases hx with ⟨y, rfl⟩
    have hcomp :
        c.comp (AddMonoidAlgebra.mapDomainAlgHom R R (φ.addSubmonoidComap S)) =
          Algebra.TensorProduct.includeRight.comp
            (AddMonoidAlgebra.mapDomainAlgHom R R (φ.addSubmonoidComap S)) := by
      apply AddMonoidAlgebra.algHom_ext
      intro z
      have hψz : ψ (φ z.1) = 0 := hexact.apply_apply_eq_zero z.1
      simp [AlgHom.comp_apply, AddMonoidAlgebra.mapDomainAlgHom_apply, hc,
        AddMonoidHom.addSubmonoidComap_apply_coe, hψz, AddMonoidAlgebra.one_def]
    rw [AlgHom.mem_equalizer]
    exact (AlgHom.ext_iff.mp hcomp) y

end Rollout_p2937_coinvariants_addmonoidalgebra_eq_range

namespace Rollout_p2732_exteriorsquare_surjective_commutatorquotie

/- accepted add_to_file helper 1 -/
lemma exteriorSquare_derivedSubgroup_le
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ H := by
  exact hH

lemma exteriorSquare_derived_commutator_le_comap
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    commutator DG ≤ C.comap DG.subtype := by
  intro DG C
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  change commutator DG ≤ C.comap DG.subtype
  rw [← Subgroup.map_le_iff_le_comap]
  rw [Subgroup.map_subtype_commutator]
  exact Subgroup.commutator_mono (exteriorSquare_derivedSubgroup_le H hH) le_top

def exteriorSquare_quotientCommGroup
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    CommGroup (DG ⧸ D) := by
  intro DG C D
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  exact
    { (inferInstance : Group (DG ⧸ D)) with
      mul_comm := fun a b =>
        ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := D)).mpr
          (exteriorSquare_derived_commutator_le_comap H hH)).comm a b }

lemma exteriorSquare_mk_conj
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    ∀ (a : G) (x : DG),
      QuotientGroup.mk' D
          ⟨a * (x : G) * a⁻¹,
            Subgroup.Normal.conj_mem inferInstance (x : G) x.2 a⟩ =
        QuotientGroup.mk' D x := by
  intro DG C D a x
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  let y : DG := ⟨a * (x : G) * a⁻¹,
    Subgroup.Normal.conj_mem inferInstance (x : G) x.2 a⟩
  rw [show QuotientGroup.mk' D y = QuotientGroup.mk' D x ↔ y⁻¹ * x ∈ D from QuotientGroup.eq]
  change ((y⁻¹ * x : DG) : G) ∈ C
  have hcalc : ((y⁻¹ * x : DG) : G) =
      (@commutatorElement G inferInstance).bracket a (x : G)⁻¹ := by
    change (a * (x : G) * a⁻¹)⁻¹ * (x : G) =
      a * (x : G)⁻¹ * a⁻¹ * ((x : G)⁻¹)⁻¹
    group
  rw [hcalc]
  change (@commutatorElement G inferInstance).bracket a (x : G)⁻¹ ∈
    ⁅H, (⊤ : Subgroup G)⁆
  rw [Subgroup.commutator_comm H (⊤ : Subgroup G)]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a)
    (H.inv_mem ((exteriorSquare_derivedSubgroup_le H hH) x.2))

lemma exteriorSquare_mk_comm_mul_left
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    ∀ a₁ a₂ b : G,
      QuotientGroup.mk' D
          ⟨(@commutatorElement G inferInstance).bracket (a₁ * a₂) b,
            Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ =
        QuotientGroup.mk' D
            ⟨(@commutatorElement G inferInstance).bracket a₁ b,
              Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ *
          QuotientGroup.mk' D
            ⟨(@commutatorElement G inferInstance).bracket a₂ b,
              Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ := by
  intro DG C D a₁ a₂ b
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroup H hH
  let c₁ : DG := ⟨(@commutatorElement G inferInstance).bracket a₁ b,
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩
  let c₂ : DG := ⟨(@commutatorElement G inferInstance).bracket a₂ b,
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩
  let c₂conj : DG := ⟨a₁ * (c₂ : G) * a₁⁻¹,
    Subgroup.Normal.conj_mem inferInstance (c₂ : G) c₂.2 a₁⟩
  have hid : (@commutatorElement G inferInstance).bracket (a₁ * a₂) b =
      ((c₂conj * c₁ : DG) : G) := by
    change a₁ * a₂ * b * (a₁ * a₂)⁻¹ * b⁻¹ =
      a₁ * (a₂ * b * a₂⁻¹ * b⁻¹) * a₁⁻¹ * (a₁ * b * a₁⁻¹ * b⁻¹)
    group
  have hsub : (⟨(@commutatorElement G inferInstance).bracket (a₁ * a₂) b,
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) =
      c₂conj * c₁ := Subtype.ext hid
  change QuotientGroup.mk' D (⟨(@commutatorElement G inferInstance).bracket (a₁ * a₂) b,
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) =
      QuotientGroup.mk' D c₁ * QuotientGroup.mk' D c₂
  rw [hsub]
  rw [map_mul]
  rw [exteriorSquare_mk_conj H hH a₁ c₂]
  exact mul_comm _ _

/- accepted add_to_file helper 2 -/
lemma exteriorSquare_mk_comm_mul_right
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    ∀ a b₁ b₂ : G,
      QuotientGroup.mk' D
          ⟨(@commutatorElement G inferInstance).bracket a (b₁ * b₂),
            Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ =
        QuotientGroup.mk' D
            ⟨(@commutatorElement G inferInstance).bracket a b₁,
              Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ *
          QuotientGroup.mk' D
            ⟨(@commutatorElement G inferInstance).bracket a b₂,
              Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ := by
  intro DG C D a b₁ b₂
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  let c₁ : DG := ⟨(@commutatorElement G inferInstance).bracket a b₁,
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩
  let c₂ : DG := ⟨(@commutatorElement G inferInstance).bracket a b₂,
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩
  let c₂conj : DG := ⟨b₁ * (c₂ : G) * b₁⁻¹,
    Subgroup.Normal.conj_mem inferInstance (c₂ : G) c₂.2 b₁⟩
  have hid : (@commutatorElement G inferInstance).bracket a (b₁ * b₂) =
      ((c₁ * c₂conj : DG) : G) := by
    change a * (b₁ * b₂) * a⁻¹ * (b₁ * b₂)⁻¹ =
      (a * b₁ * a⁻¹ * b₁⁻¹) * (b₁ * (a * b₂ * a⁻¹ * b₂⁻¹) * b₁⁻¹)
    group
  have hsub : (⟨(@commutatorElement G inferInstance).bracket a (b₁ * b₂),
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) =
      c₁ * c₂conj := Subtype.ext hid
  change QuotientGroup.mk' D (⟨(@commutatorElement G inferInstance).bracket a (b₁ * b₂),
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) =
      QuotientGroup.mk' D c₁ * QuotientGroup.mk' D c₂
  rw [hsub]
  rw [map_mul]
  rw [exteriorSquare_mk_conj H hH b₁ c₂]

/- accepted add_to_file helper 3 -/
def exteriorSquare_rawLeftHom
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    G → (G →* (DG ⧸ D)) := by
  intro DG C D b
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  exact
    { toFun := fun a =>
        QuotientGroup.mk' D
          ⟨(@commutatorElement G inferInstance).bracket a b,
            Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩
      map_one' := by
        have hsub : (⟨(@commutatorElement G inferInstance).bracket 1 b,
            Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) = 1 :=
          Subtype.ext (commutatorElement_one_left b)
        change QuotientGroup.mk' D
            (⟨(@commutatorElement G inferInstance).bracket 1 b,
              Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) = 1
        rw [hsub]
        rfl
      map_mul' := by
        intro a₁ a₂
        exact exteriorSquare_mk_comm_mul_left H hH a₁ a₂ b }

/- accepted add_to_file helper 4 -/
lemma exteriorSquare_sup_le_rawLeftHom_ker
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    ∀ b : G,
      H ⊔ Subgroup.center G ≤ (exteriorSquare_rawLeftHom H hH b).ker := by
  intro DG C D b
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  rw [sup_le_iff]
  constructor
  · intro x hx
    rw [MonoidHom.mem_ker]
    let xb : DG := ⟨(@commutatorElement G inferInstance).bracket x b,
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩
    change QuotientGroup.mk' D xb = 1
    apply (QuotientGroup.eq_one_iff xb).mpr
    change (@commutatorElement G inferInstance).bracket x b ∈ C
    change (@commutatorElement G inferInstance).bracket x b ∈ ⁅H, (⊤ : Subgroup G)⁆
    exact Subgroup.commutator_mem_commutator hx (Subgroup.mem_top b)
  · intro z hz
    rw [MonoidHom.mem_ker]
    have hcomm : Commute z b := ((Subgroup.mem_center_iff.mp hz b).symm)
    have hsub : (⟨(@commutatorElement G inferInstance).bracket z b,
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) = 1 :=
      Subtype.ext (Commute.commutator_eq hcomm)
    change QuotientGroup.mk' D
        (⟨(@commutatorElement G inferInstance).bracket z b,
          Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) = 1
    rw [hsub]
    rfl

/- accepted add_to_file helper 5 -/
def exteriorSquare_leftHomB
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let K : Subgroup G := H ⊔ Subgroup.center G
    letI : K.Normal := inferInstance
    let B := G ⧸ K
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    G → (B →* (DG ⧸ D)) := by
  intro K B DG C D b
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : K.Normal := by
    change (H ⊔ Subgroup.center G).Normal
    infer_instance
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  exact QuotientGroup.lift K (exteriorSquare_rawLeftHom H hH b)
    (exteriorSquare_sup_le_rawLeftHom_ker H hH b)

/- accepted add_to_file helper 6 -/
@[reducible]
def exteriorSquare_quotientCommGroupRed
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    CommGroup (DG ⧸ D) := by
  intro DG C D
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  exact
    { (inferInstance : Group (DG ⧸ D)) with
      mul_comm := fun a b =>
        ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := D)).mpr
          (exteriorSquare_derived_commutator_le_comap H hH)).comm a b }

/- accepted add_to_file helper 7 -/
lemma exteriorSquare_leftHomB_mk
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let K : Subgroup G := H ⊔ Subgroup.center G
    letI : K.Normal := inferInstance
    let B := G ⧸ K
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    ∀ a b : G,
      exteriorSquare_leftHomB H hH b (QuotientGroup.mk' K a) =
        exteriorSquare_rawLeftHom H hH b a := by
  intro K B DG C D a b
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : K.Normal := by
    change (H ⊔ Subgroup.center G).Normal
    infer_instance
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  exact QuotientGroup.lift_mk' K (exteriorSquare_sup_le_rawLeftHom_ker H hH b) a

/- accepted add_to_file helper 8 -/
def exteriorSquare_rawRightAddHom
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let K : Subgroup G := H ⊔ Subgroup.center G
    letI : K.Normal := inferInstance
    let B := G ⧸ K
    letI : CommGroup B :=
      { (inferInstance : Group B) with
        mul_comm := fun a b =>
          ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).mpr
            (hH.trans le_sup_left)).comm a b }
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
    G →* Multiplicative (Additive B →+ Additive (DG ⧸ D)) := by
  intro K B DG C D
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : K.Normal := by
    change (H ⊔ Subgroup.center G).Normal
    infer_instance
  letI : CommGroup B :=
    { (inferInstance : Group B) with
      mul_comm := fun a b =>
        ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).mpr
          (hH.trans le_sup_left)).comm a b }
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
  exact
    { toFun := fun b =>
        Multiplicative.ofAdd
          { toFun := fun x =>
              Additive.ofMul ((exteriorSquare_leftHomB H hH b) (Additive.toMul x))
            map_zero' := by
              change Additive.ofMul ((exteriorSquare_leftHomB H hH b) 1) = 0
              rw [map_one]
              rfl
            map_add' := by
              intro x y
              change Additive.ofMul
                  ((exteriorSquare_leftHomB H hH b)
                    (Additive.toMul x * Additive.toMul y)) =
                Additive.ofMul ((exteriorSquare_leftHomB H hH b) (Additive.toMul x)) +
                  Additive.ofMul ((exteriorSquare_leftHomB H hH b) (Additive.toMul y))
              rw [map_mul]
              rfl }
      map_one' := by
        ext a
        change Additive.ofMul ((exteriorSquare_leftHomB H hH 1) (QuotientGroup.mk' K a)) =
          Additive.ofMul 1
        congr 1
        rw [exteriorSquare_leftHomB_mk]
        change QuotientGroup.mk' D
            ⟨(@commutatorElement G inferInstance).bracket a 1,
              Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ = 1
        have hsub : (⟨(@commutatorElement G inferInstance).bracket a 1,
            Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) = 1 :=
          Subtype.ext (commutatorElement_one_right a)
        change QuotientGroup.mk' D
            (⟨(@commutatorElement G inferInstance).bracket a 1,
              Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) = 1
        rw [hsub]
        rfl
      map_mul' := by
        intro b₁ b₂
        ext a
        change Additive.ofMul
            ((exteriorSquare_leftHomB H hH (b₁ * b₂)) (QuotientGroup.mk' K a)) =
          Additive.ofMul ((exteriorSquare_leftHomB H hH b₁) (QuotientGroup.mk' K a)) +
            Additive.ofMul ((exteriorSquare_leftHomB H hH b₂) (QuotientGroup.mk' K a))
        congr 1
        change (exteriorSquare_leftHomB H hH (b₁ * b₂)) (QuotientGroup.mk' K a) =
          (exteriorSquare_leftHomB H hH b₁) (QuotientGroup.mk' K a) *
            (exteriorSquare_leftHomB H hH b₂) (QuotientGroup.mk' K a)
        rw [exteriorSquare_leftHomB_mk, exteriorSquare_leftHomB_mk, exteriorSquare_leftHomB_mk]
        exact exteriorSquare_mk_comm_mul_right H hH a b₁ b₂ }

/- accepted add_to_file helper 9 -/
lemma exteriorSquare_sup_le_rawRightAddHom_ker
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let K : Subgroup G := H ⊔ Subgroup.center G
    letI : K.Normal := inferInstance
    let B := G ⧸ K
    letI : CommGroup B :=
      { (inferInstance : Group B) with
        mul_comm := fun a b =>
          ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).mpr
            (hH.trans le_sup_left)).comm a b }
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
    K ≤ (exteriorSquare_rawRightAddHom H hH).ker := by
  intro K B DG C D
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : K.Normal := by
    change (H ⊔ Subgroup.center G).Normal
    infer_instance
  letI : CommGroup B :=
    { (inferInstance : Group B) with
      mul_comm := fun a b =>
        ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).mpr
          (hH.trans le_sup_left)).comm a b }
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
  rw [sup_le_iff]
  constructor
  · intro x hx
    rw [MonoidHom.mem_ker]
    ext a
    change Additive.ofMul ((exteriorSquare_leftHomB H hH x) (QuotientGroup.mk' K a)) =
      Additive.ofMul 1
    congr 1
    rw [exteriorSquare_leftHomB_mk]
    let ax : DG := ⟨(@commutatorElement G inferInstance).bracket a x,
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩
    change QuotientGroup.mk' D ax = 1
    apply (QuotientGroup.eq_one_iff ax).mpr
    change (@commutatorElement G inferInstance).bracket a x ∈ C
    change (@commutatorElement G inferInstance).bracket a x ∈ ⁅H, (⊤ : Subgroup G)⁆
    rw [Subgroup.commutator_comm H (⊤ : Subgroup G)]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) hx
  · intro z hz
    rw [MonoidHom.mem_ker]
    ext a
    change Additive.ofMul ((exteriorSquare_leftHomB H hH z) (QuotientGroup.mk' K a)) =
      Additive.ofMul 1
    congr 1
    rw [exteriorSquare_leftHomB_mk]
    have hcomm : Commute a z := Subgroup.mem_center_iff.mp hz a
    change QuotientGroup.mk' D
        ⟨(@commutatorElement G inferInstance).bracket a z,
          Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ = 1
    have hsub : (⟨(@commutatorElement G inferInstance).bracket a z,
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) = 1 :=
      Subtype.ext (Commute.commutator_eq hcomm)
    change QuotientGroup.mk' D
        (⟨(@commutatorElement G inferInstance).bracket a z,
          Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) = 1
    rw [hsub]
    rfl

/- accepted add_to_file helper 10 -/
def exteriorSquare_bilinearHom
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let K : Subgroup G := H ⊔ Subgroup.center G
    letI : K.Normal := inferInstance
    let B := G ⧸ K
    letI : CommGroup B :=
      { (inferInstance : Group B) with
        mul_comm := fun a b =>
          ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).mpr
            (hH.trans le_sup_left)).comm a b }
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
    B →* Multiplicative (Additive B →+ Additive (DG ⧸ D)) := by
  intro K B DG C D
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : K.Normal := by
    change (H ⊔ Subgroup.center G).Normal
    infer_instance
  letI : CommGroup B :=
    { (inferInstance : Group B) with
      mul_comm := fun a b =>
        ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).mpr
          (hH.trans le_sup_left)).comm a b }
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
  exact QuotientGroup.lift K (exteriorSquare_rawRightAddHom H hH)
    (exteriorSquare_sup_le_rawRightAddHom_ker H hH)

lemma exteriorSquare_bilinearHom_mk
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let K : Subgroup G := H ⊔ Subgroup.center G
    letI : K.Normal := inferInstance
    let B := G ⧸ K
    letI : CommGroup B :=
      { (inferInstance : Group B) with
        mul_comm := fun a b =>
          ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).mpr
            (hH.trans le_sup_left)).comm a b }
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
    ∀ b : G,
      exteriorSquare_bilinearHom H hH (QuotientGroup.mk' K b) =
        exteriorSquare_rawRightAddHom H hH b := by
  intro K B DG C D b
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : K.Normal := by
    change (H ⊔ Subgroup.center G).Normal
    infer_instance
  letI : CommGroup B :=
    { (inferInstance : Group B) with
      mul_comm := fun a b =>
        ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).mpr
          (hH.trans le_sup_left)).comm a b }
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
  exact QuotientGroup.lift_mk' K (exteriorSquare_sup_le_rawRightAddHom_ker H hH) b

/- accepted add_to_file helper 11 -/
lemma exteriorSquare_bilinearHom_self
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let K : Subgroup G := H ⊔ Subgroup.center G
    letI : K.Normal := inferInstance
    let B := G ⧸ K
    letI : CommGroup B :=
      { (inferInstance : Group B) with
        mul_comm := fun a b =>
          ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).mpr
            (hH.trans le_sup_left)).comm a b }
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
    ∀ x : Additive B,
      (Multiplicative.toAdd (exteriorSquare_bilinearHom H hH (Additive.toMul x))) x = 0 := by
  intro K B DG C D x
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : K.Normal := by
    change (H ⊔ Subgroup.center G).Normal
    infer_instance
  letI : CommGroup B :=
    { (inferInstance : Group B) with
      mul_comm := fun a b =>
        ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).mpr
          (hH.trans le_sup_left)).comm a b }
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective K (Additive.toMul x)
  change (Multiplicative.toAdd (exteriorSquare_bilinearHom H hH (QuotientGroup.mk' K a)))
      (QuotientGroup.mk' K a) = 0
  rw [exteriorSquare_bilinearHom_mk]
  change Additive.ofMul ((exteriorSquare_leftHomB H hH a) (QuotientGroup.mk' K a)) = 0
  rw [exteriorSquare_leftHomB_mk]
  change Additive.ofMul
      (QuotientGroup.mk' D
        ⟨(@commutatorElement G inferInstance).bracket a a,
          Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩) = 0
  congr 1
  have hsub : (⟨(@commutatorElement G inferInstance).bracket a a,
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) = 1 :=
    Subtype.ext (commutatorElement_self a)
  change QuotientGroup.mk' D
      (⟨(@commutatorElement G inferInstance).bracket a a,
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) = 1
  rw [hsub]
  rfl

/- accepted add_to_file helper 12 -/
def exteriorSquare_commutatorAlternatingMap
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let K : Subgroup G := H ⊔ Subgroup.center G
    letI : K.Normal := inferInstance
    let B := G ⧸ K
    letI : CommGroup B :=
      { (inferInstance : Group B) with
        mul_comm := fun a b =>
          ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).mpr
            (hH.trans le_sup_left)).comm a b }
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
    Additive B [⋀^Fin 2]→ₗ[ℤ] Additive (DG ⧸ D) := by
  intro K B DG C D
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : K.Normal := by
    change (H ⊔ Subgroup.center G).Normal
    infer_instance
  letI : CommGroup B :=
    { (inferInstance : Group B) with
      mul_comm := fun a b =>
        ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).mpr
          (hH.trans le_sup_left)).comm a b }
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
  let ψ := exteriorSquare_bilinearHom H hH
  let F : (Fin 2 → Additive B) → Additive (DG ⧸ D) := fun v =>
    (Multiplicative.toAdd (ψ (Additive.toMul (v 1)))) (v 0)
  exact
    { toMultilinearMap :=
        { toFun := F
          map_update_add' := by
            intro _ m i x y
            fin_cases i
            · simp [F]
              exact (Multiplicative.toAdd (ψ (Additive.toMul (m 1)))).map_add x y
            · simp [F]
              exact congrArg (fun z => (Multiplicative.toAdd z) (m 0))
                (map_mul ψ (Additive.toMul x) (Additive.toMul y))
          map_update_smul' := by
            intro _ m i c x
            fin_cases i
            · simp [F]
              exact map_zsmul (Multiplicative.toAdd (ψ (Additive.toMul (m 1)))) c x
            · simp [F]
              exact congrArg (fun z => (Multiplicative.toAdd z) (m 0))
                (map_zpow ψ (Additive.toMul x) c) }
      map_eq_zero_of_eq' := by
        intro v i j hij hne
        fin_cases i <;> fin_cases j
        · exact (hne rfl).elim
        · change v 0 = v 1 at hij
          change (Multiplicative.toAdd (ψ (Additive.toMul (v 1)))) (v 0) = 0
          rw [hij]
          exact exteriorSquare_bilinearHom_self H hH (v 1)
        · change v 1 = v 0 at hij
          change (Multiplicative.toAdd (ψ (Additive.toMul (v 1)))) (v 0) = 0
          rw [hij]
          exact exteriorSquare_bilinearHom_self H hH (v 0)
        · exact (hne rfl).elim }

/- accepted add_to_file helper 13 -/
lemma exteriorSquare_alternatingMap_mk
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let K : Subgroup G := H ⊔ Subgroup.center G
    letI : K.Normal := inferInstance
    let B := G ⧸ K
    letI : CommGroup B :=
      { (inferInstance : Group B) with
        mul_comm := fun a b =>
          ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).mpr
            (hH.trans le_sup_left)).comm a b }
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
    ∀ a b : G,
      exteriorSquare_commutatorAlternatingMap H hH
          ![Additive.ofMul (QuotientGroup.mk' K a),
            Additive.ofMul (QuotientGroup.mk' K b)] =
        Additive.ofMul
          (QuotientGroup.mk' D
            ⟨(@commutatorElement G _).bracket a b,
              Subgroup.commutator_mem_commutator
                (Subgroup.mem_top a) (Subgroup.mem_top b)⟩) := by
  intro K B DG C D a b
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : K.Normal := by
    change (H ⊔ Subgroup.center G).Normal
    infer_instance
  letI : CommGroup B :=
    { (inferInstance : Group B) with
      mul_comm := fun a b =>
        ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).mpr
          (hH.trans le_sup_left)).comm a b }
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
  simp [exteriorSquare_commutatorAlternatingMap]
  change (Multiplicative.toAdd
      (exteriorSquare_bilinearHom H hH (QuotientGroup.mk' K b)))
      (Additive.ofMul (QuotientGroup.mk' K a)) = _
  rw [exteriorSquare_bilinearHom_mk]
  change Additive.ofMul ((exteriorSquare_leftHomB H hH b) (QuotientGroup.mk' K a)) = _
  rw [exteriorSquare_leftHomB_mk]
  rfl

/- verified submission -/
theorem exteriorSquare_surjective_commutatorQuotient
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let K : Subgroup G := H ⊔ Subgroup.center G
    letI : K.Normal := inferInstance
    let B := G ⧸ K
    letI : CommGroup B :=
      { (inferInstance : Group B) with
        mul_comm := fun a b =>
          ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).mpr
            (hH.trans le_sup_left)).comm a b }
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), ⊤⁆
    let C : Subgroup G := ⁅H, ⊤⁆
    letI : C.Normal := inferInstance
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    ∃ f : Multiplicative ↥(ExteriorAlgebra.exteriorPower ℤ 2 (Additive B)) →* (DG ⧸ D),
      Function.Surjective f ∧
        ∀ a b : G,
          f (Multiplicative.ofAdd
            ((exteriorPower.ιMulti ℤ 2)
              ![Additive.ofMul (QuotientGroup.mk' K a),
                Additive.ofMul (QuotientGroup.mk' K b)])) =
            QuotientGroup.mk' D
              ⟨(@commutatorElement G _).bracket a b,
                Subgroup.commutator_mem_commutator
                  (Subgroup.mem_top a) (Subgroup.mem_top b)⟩ := by
  intro K B DG C D
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : K.Normal := by
    change (H ⊔ Subgroup.center G).Normal
    infer_instance
  letI : CommGroup B :=
    { (inferInstance : Group B) with
      mul_comm := fun a b =>
        ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).mpr
          (hH.trans le_sup_left)).comm a b }
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
  let A := exteriorSquare_commutatorAlternatingMap H hH
  let L := exteriorPower.alternatingMapLinearEquiv A
  let f : Multiplicative ↥(ExteriorAlgebra.exteriorPower ℤ 2 (Additive B)) →* (DG ⧸ D) :=
    { toFun := fun x => Additive.toMul (L (Multiplicative.toAdd x))
      map_one' := by
        change Additive.toMul (L 0) = 1
        rw [map_zero]
        rfl
      map_mul' := by
        intro x y
        change Additive.toMul (L (Multiplicative.toAdd x + Multiplicative.toAdd y)) =
          Additive.toMul (L (Multiplicative.toAdd x)) * Additive.toMul (L (Multiplicative.toAdd y))
        rw [map_add]
        rfl }
  have hmap : ∀ a b : G,
      f (Multiplicative.ofAdd
        ((exteriorPower.ιMulti ℤ 2)
          ![Additive.ofMul (QuotientGroup.mk' K a),
            Additive.ofMul (QuotientGroup.mk' K b)])) =
        QuotientGroup.mk' D
          ⟨(@commutatorElement G _).bracket a b,
            Subgroup.commutator_mem_commutator
              (Subgroup.mem_top a) (Subgroup.mem_top b)⟩ := by
    intro a b
    change Additive.toMul
        ((exteriorPower.alternatingMapLinearEquiv A)
          ((exteriorPower.ιMulti ℤ 2)
            ![Additive.ofMul (QuotientGroup.mk' K a),
              Additive.ofMul (QuotientGroup.mk' K b)])) = _
    rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    rw [exteriorSquare_alternatingMap_mk]
    rfl
  refine ⟨f, ?_, hmap⟩
  rw [← MonoidHom.range_eq_top]
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D y
  have hx : x.1 ∈ Subgroup.closure
      {g : G | ∃ g₁ ∈ (⊤ : Subgroup G), ∃ g₂ ∈ (⊤ : Subgroup G),
        (@commutatorElement G inferInstance).bracket g₁ g₂ = g} := by
    have hx' := x.2
    change x.1 ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ at hx'
    rwa [Subgroup.commutator_def] at hx'
  refine Subgroup.closure_induction
      (p := fun g hg =>
        (QuotientGroup.mk' D ⟨g, hg⟩ : DG ⧸ D) ∈ f.range)
      ?_ ?_ ?_ ?_ hx
  · intro g hg
    rcases hg with ⟨a, -, b, -, rfl⟩
    rw [← hmap a b]
    exact ⟨_, rfl⟩
  · change (QuotientGroup.mk' D (1 : DG)) ∈ f.range
    rw [map_one]
    exact f.range.one_mem
  · intro x y hx hy px py
    change (QuotientGroup.mk' D ((⟨x, hx⟩ : DG) * ⟨y, hy⟩)) ∈ f.range
    rw [map_mul]
    exact f.range.mul_mem px py
  · intro x hx px
    change (QuotientGroup.mk' D (⟨x, hx⟩ : DG)⁻¹) ∈ f.range
    rw [map_inv]
    exact f.range.inv_mem px

end Rollout_p2732_exteriorsquare_surjective_commutatorquotie
