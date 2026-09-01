import GraphCertificate
import Mathlib

namespace Rollout_p2674_graded_dual_rational_map_mem_completion

-- graph_id: p2674_graded_dual_rational_map_mem_completion
-- topology_sha256: ee96ffed4839bb111b30a81d1b3d00b895a201f2c741ddc0e91de1722bd55d11
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

#check_dependency_graph "Rollout_p2674_graded_dual_rational_map_mem_completion.graded_dual_rational_map_mem_completion" against "{\"edges\":[{\"conclusion\":{\"name\":\"hfinite_g\",\"statement\":\"∀ (a : ℂ), {α | g α a ≠ 0}.Finite\"},\"graphEdgeId\":\"h_001_hfinite_g\",\"premises\":[{\"name\":\"hcleared\",\"statement\":\"∀ (w' : DirectSum ℂ fun a => Module.Dual ℂ (W a)), ∃ P, (∀ (α : Fin n →₀ ℕ), MvPolynomial.coeff α P = (DirectSum.toModule ℂ ℂ ℂ fun a => (Module.Dual.eval ℂ (W a)) (g α a)) w') ∧ ∀ (z : { z // Function.Injective z }), (∏ i, ∏ j ∈ Finset.Ioi i, (↑z i - ↑z j) ^ p i j) * (f z) w' = (MvPolynomial.eval ↑z) P\"}],\"rawEdgeId\":\"telescope_13\"},{\"conclusion\":{\"name\":\"hD\",\"statement\":\"D ≠ 0\"},\"graphEdgeId\":\"h_002_hd\",\"premises\":[],\"rawEdgeId\":\"telescope_17\"},{\"conclusion\":{\"name\":\"hcomponent\",\"statement\":\"∀ (a : ℂ) (l : Module.Dual ℂ (W a)), (f z) ((DirectSum.lof ℂ ℂ (fun c => Module.Dual ℂ (W c)) a) l) = l (b a)\"},\"graphEdgeId\":\"h_003_hcomponent\",\"premises\":[{\"name\":\"hcleared\",\"statement\":\"∀ (w' : DirectSum ℂ fun a => Module.Dual ℂ (W a)), ∃ P, (∀ (α : Fin n →₀ ℕ), MvPolynomial.coeff α P = (DirectSum.toModule ℂ ℂ ℂ fun a => (Module.Dual.eval ℂ (W a)) (g α a)) w') ∧ ∀ (z : { z // Function.Injective z }), (∏ i, ∏ j ∈ Finset.Ioi i, (↑z i - ↑z j) ^ p i j) * (f z) w' = (MvPolynomial.eval ↑z) P\"},{\"name\":\"hfinite_g\",\"statement\":\"∀ (a : ℂ), {α | g α a ≠ 0}.Finite\"},{\"name\":\"hD\",\"statement\":\"D ≠ 0\"}],\"rawEdgeId\":\"telescope_19\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∃ b, f z = DirectSum.toModule ℂ ℂ ℂ fun a => (Module.Dual.eval ℂ (W a)) (b a)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hcomponent\",\"statement\":\"∀ (a : ℂ) (l : Module.Dual ℂ (W a)), (f z) ((DirectSum.lof ℂ ℂ (fun c => Module.Dual ℂ (W c)) a) l) = l (b a)\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2674_graded_dual_rational_map_mem_completion\",\"reconstructedProofSha256\":\"0046f17857bd64d50d78ba09992033d5aec361a99586c0435defed668a7eded7\",\"selectedEdgeCount\":4,\"theoremName\":\"Rollout_p2674_graded_dual_rational_map_mem_completion.graded_dual_rational_map_mem_completion\",\"topologySha256\":\"ee96ffed4839bb111b30a81d1b3d00b895a201f2c741ddc0e91de1722bd55d11\"}"

namespace Rollout_p2692_hodge_operator_on_two_forms

-- graph_id: p2692_hodge_operator_on_two_forms
-- topology_sha256: f78a667584570d9c4fb9b59661d293e0d2173c9926ebeb29901dc26023276f9e
/- accepted add_to_file helper 1 -/

lemma hodge_star_apply
    (q : ℂ) (V : Type*) [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis (Fin 6) ℂ V) (star : V →ₗ[ℂ] V) (x : V) (μ : ℂ)
    (h0 : star (b 0) = -b 0 + (2 * μ) • b 4)
    (h1 : star (b 1) = b 1)
    (h2 : star (b 2) = (1 / (1 + q ^ 2)) •
        ((2 : ℂ) • b 3 - (q ^ 2 * μ) • b 2))
    (h3 : star (b 3) = (q ^ 2 / (1 + q ^ 2)) •
        ((2 : ℂ) • b 2 + μ • b 3))
    (h4 : star (b 4) = b 4)
    (h5 : star (b 5) = -b 5) :
    star x =
      (-(b.repr x 0)) • b 0 +
      (b.repr x 1) • b 1 +
      (((-(q ^ 2 * μ)) / (1 + q ^ 2)) * (b.repr x 2) +
        ((2 * q ^ 2) / (1 + q ^ 2)) * (b.repr x 3)) • b 2 +
      (((2 : ℂ) / (1 + q ^ 2)) * (b.repr x 2) +
        ((q ^ 2 * μ) / (1 + q ^ 2)) * (b.repr x 3)) • b 3 +
      ((2 * μ) * (b.repr x 0) + (b.repr x 4)) • b 4 +
      (-(b.repr x 5)) • b 5 := by
  have hs := b.sum_repr x
  rw [Fin.sum_univ_six] at hs
  rw [← hs]
  simp [h0, h1, h2, h3, h4, h5]
  module

/- accepted add_to_file helper 2 -/
lemma hodge_star_square
    (q : ℂ) (hq0 : q ≠ 0) (hq_neg_one : q ^ 2 ≠ (-1 : ℂ))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis (Fin 6) ℂ V) (star : V →ₗ[ℂ] V)
    (μ : ℂ) (hμ : μ = 1 - (q ^ 2)⁻¹)
    (h0 : star (b 0) = -b 0 + (2 * μ) • b 4)
    (h1 : star (b 1) = b 1)
    (h2 : star (b 2) = (1 / (1 + q ^ 2)) •
        ((2 : ℂ) • b 3 - (q ^ 2 * μ) • b 2))
    (h3 : star (b 3) = (q ^ 2 / (1 + q ^ 2)) •
        ((2 : ℂ) • b 2 + μ • b 3))
    (h4 : star (b 4) = b 4)
    (h5 : star (b 5) = -b 5) :
    star.comp star = LinearMap.id := by
  ext x
  change star (star x) = x
  have hr : (q ^ 2 : ℂ) ≠ 0 := pow_ne_zero 2 hq0
  have hden : (1 + q ^ 2 : ℂ) ≠ 0 := by
    intro h
    apply hq_neg_one
    linear_combination h
  have hstx := hodge_star_apply q V b star x μ h0 h1 h2 h3 h4 h5
  have hstst := hodge_star_apply q V b star (star x) μ h0 h1 h2 h3 h4 h5
  rw [hstx] at hstst
  rw [hstx, hstst]
  apply b.ext_elem
  intro i
  simp
  fin_cases i <;> simp
  all_goals
    subst μ
    field_simp [hden, hr]
    ring

/- accepted add_to_file helper 3 -/
lemma hodge_ker_selfdual
    (q : ℂ) (hq0 : q ≠ 0) (hq_neg_one : q ^ 2 ≠ (-1 : ℂ))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis (Fin 6) ℂ V) (star : V →ₗ[ℂ] V)
    (μ : ℂ) (hμ : μ = 1 - (q ^ 2)⁻¹)
    (h0 : star (b 0) = -b 0 + (2 * μ) • b 4)
    (h1 : star (b 1) = b 1)
    (h2 : star (b 2) = (1 / (1 + q ^ 2)) •
        ((2 : ℂ) • b 3 - (q ^ 2 * μ) • b 2))
    (h3 : star (b 3) = (q ^ 2 / (1 + q ^ 2)) •
        ((2 : ℂ) • b 2 + μ • b 3))
    (h4 : star (b 4) = b 4)
    (h5 : star (b 5) = -b 5) :
    LinearMap.ker (star - LinearMap.id) =
      Submodule.span ℂ {b 4, b 1, b 2 + b 3} := by
  have hr : (q ^ 2 : ℂ) ≠ 0 := pow_ne_zero 2 hq0
  have hden : (1 + q ^ 2 : ℂ) ≠ 0 := by
    intro h
    apply hq_neg_one
    linear_combination h
  have hfix23 : star (b 2 + b 3) = b 2 + b 3 := by
    apply b.ext_elem
    intro i
    simp [map_add, h2, h3]
    fin_cases i <;> simp
    all_goals
      subst μ
      field_simp [hden, hr]
      ring
  apply le_antisymm
  · intro x hx
    have hfix : star x = x := by
      have h := LinearMap.mem_ker.mp hx
      simpa using sub_eq_zero.mp h
    have hstx := hodge_star_apply q V b star x μ h0 h1 h2 h3 h4 h5
    have hc0 := congrArg (b.coord 0) hfix
    simp [hstx] at hc0
    have ha0 : b.repr x 0 = 0 := CharZero.neg_eq_self_iff.mp hc0
    have hc5 := congrArg (b.coord 5) hfix
    simp [hstx] at hc5
    have ha5 : b.repr x 5 = 0 := CharZero.neg_eq_self_iff.mp hc5
    have hc2 := congrArg (b.coord 2) hfix
    simp [hstx] at hc2
    change (((-(q ^ 2 * μ)) / (1 + q ^ 2)) * (b.repr x 2) +
          ((2 * q ^ 2) / (1 + q ^ 2)) * (b.repr x 3) : ℂ) = b.repr x 2 at hc2
    subst μ
    field_simp [hden, hr] at hc2
    ring_nf at hc2
    have hmul : (2 * q ^ 2 : ℂ) * (b.repr x 3 - b.repr x 2) = 0 := by
      linear_combination hc2
    have hsub : b.repr x 3 - b.repr x 2 = 0 := by
      have hfactor : (2 * q ^ 2 : ℂ) ≠ 0 := mul_ne_zero two_ne_zero hr
      exact (mul_eq_zero.mp hmul).resolve_left hfactor
    have ha23 : b.repr x 2 = b.repr x 3 := (sub_eq_zero.mp hsub).symm
    have hxcomb : x = (b.repr x 4) • b 4 + (b.repr x 1) • b 1 +
        (b.repr x 2) • (b 2 + b 3) := by
      have hs := b.sum_repr x
      rw [Fin.sum_univ_six] at hs
      rw [← hs]
      simp [ha0, ha5, ha23]
      module
    rw [hxcomb]
    apply add_mem
    · apply add_mem
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · rw [Submodule.span_le]
    intro y hy
    have hsy : star y = y := by
      simp at hy
      rcases hy with rfl | rfl | rfl
      · simp [h4]
      · simp [h1]
      · exact hfix23
    simp [hsy]

/- accepted add_to_file helper 4 -/
lemma hodge_ker_antidual
    (q : ℂ) (hq0 : q ≠ 0) (hq_neg_one : q ^ 2 ≠ (-1 : ℂ))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis (Fin 6) ℂ V) (star : V →ₗ[ℂ] V)
    (μ : ℂ) (hμ : μ = 1 - (q ^ 2)⁻¹)
    (h0 : star (b 0) = -b 0 + (2 * μ) • b 4)
    (h1 : star (b 1) = b 1)
    (h2 : star (b 2) = (1 / (1 + q ^ 2)) •
        ((2 : ℂ) • b 3 - (q ^ 2 * μ) • b 2))
    (h3 : star (b 3) = (q ^ 2 / (1 + q ^ 2)) •
        ((2 : ℂ) • b 2 + μ • b 3))
    (h4 : star (b 4) = b 4)
    (h5 : star (b 5) = -b 5) :
    LinearMap.ker (star + LinearMap.id) =
      Submodule.span ℂ {b 5, b 0 - μ • b 4, b 2 - (q ^ 2)⁻¹ • b 3} := by
  have hr : (q ^ 2 : ℂ) ≠ 0 := pow_ne_zero 2 hq0
  have hden : (1 + q ^ 2 : ℂ) ≠ 0 := by
    intro h
    apply hq_neg_one
    linear_combination h
  have hanti04 : star (b 0 - μ • b 4) = -(b 0 - μ • b 4) := by
    rw [map_sub, map_smul, h0, h4]
    module
  have hanti23 : star (b 2 - (q ^ 2)⁻¹ • b 3) =
      -(b 2 - (q ^ 2)⁻¹ • b 3) := by
    apply b.ext_elem
    intro i
    simp [map_sub, h2, h3]
    fin_cases i <;> simp
    all_goals
      subst μ
      field_simp [hden, hr]
      ring
  apply le_antisymm
  · intro x hx
    have hanti : star x = -x := by
      have h := LinearMap.mem_ker.mp hx
      simpa using (eq_neg_iff_add_eq_zero.mpr h)
    have hstx := hodge_star_apply q V b star x μ h0 h1 h2 h3 h4 h5
    have hc1 := congrArg (b.coord 1) hanti
    simp [hstx] at hc1
    have ha1 : b.repr x 1 = 0 := CharZero.neg_eq_self_iff.mp hc1.symm
    have hc4 := congrArg (b.coord 4) hanti
    simp [hstx] at hc4
    change ((2 * μ) * (b.repr x 0) + b.repr x 4 : ℂ) = -b.repr x 4 at hc4
    have hzero2 : (2 : ℂ) * (μ * b.repr x 0 + b.repr x 4) = 0 := by
      linear_combination hc4
    have hzero : μ * b.repr x 0 + b.repr x 4 = 0 :=
      (mul_eq_zero.mp hzero2).resolve_left two_ne_zero
    have ha4 : b.repr x 4 = -μ * b.repr x 0 := by
      linear_combination hzero
    have hc2 := congrArg (b.coord 2) hanti
    simp [hstx] at hc2
    change (((-(q ^ 2 * μ)) / (1 + q ^ 2)) * (b.repr x 2) +
          ((2 * q ^ 2) / (1 + q ^ 2)) * (b.repr x 3) : ℂ) = -b.repr x 2 at hc2
    subst μ
    field_simp [hden, hr] at hc2
    ring_nf at hc2
    have hmul : (2 * q ^ 2 : ℂ) * b.repr x 3 = -2 * b.repr x 2 := by
      linear_combination hc2
    have hmul2 : (q ^ 2 : ℂ) * b.repr x 3 = -b.repr x 2 := by
      have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
      have : (2 : ℂ) * (q ^ 2 * b.repr x 3) = (2 : ℂ) * (-b.repr x 2) := by
        linear_combination hmul
      exact mul_left_cancel₀ h2 this
    have ha3 : b.repr x 3 = -(q ^ 2)⁻¹ * b.repr x 2 := by
      rw [show -(q ^ 2 : ℂ)⁻¹ * b.repr x 2 = (q ^ 2)⁻¹ * (-b.repr x 2) by ring]
      exact ((inv_mul_eq_iff_eq_mul₀ hr).mpr hmul2.symm).symm
    have hxcomb : x = (b.repr x 5) • b 5 +
        (b.repr x 0) • (b 0 - (1 - (q ^ 2)⁻¹) • b 4) +
        (b.repr x 2) • (b 2 - (q ^ 2)⁻¹ • b 3) := by
      have hs := b.sum_repr x
      rw [Fin.sum_univ_six] at hs
      rw [← hs]
      simp [ha1, ha3, ha4]
      module
    rw [hxcomb]
    apply add_mem
    · apply add_mem
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · rw [Submodule.span_le]
    intro y hy
    have hsy : star y = -y := by
      simp at hy
      rcases hy with rfl | rfl | rfl
      · simp [h5]
      · exact hanti04
      · exact hanti23
    simp [hsy]

/- accepted add_to_file helper 5 -/
lemma hodge_selfdual_linearIndependent
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis (Fin 6) ℂ V) :
    LinearIndependent ℂ ![b 4, b 1, b 2 + b 3] := by
  let f : V →ₗ[ℂ] Fin 3 → ℂ :=
    LinearMap.pi ![b.coord 4, b.coord 1, b.coord 2]
  have hcomp : f ∘ ![b 4, b 1, b 2 + b 3] = ⇑(Pi.basisFun ℂ (Fin 3)) := by
    funext i j
    fin_cases i <;> fin_cases j <;> simp [f]
  have hf : LinearIndependent ℂ (f ∘ ![b 4, b 1, b 2 + b 3]) := by
    rw [hcomp]
    exact (Pi.basisFun ℂ (Fin 3)).linearIndependent
  exact LinearIndependent.of_comp f hf

lemma hodge_antidual_linearIndependent
    (q : ℂ) (V : Type*) [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis (Fin 6) ℂ V) (μ : ℂ) :
    LinearIndependent ℂ ![b 5, b 0 - μ • b 4, b 2 - (q ^ 2)⁻¹ • b 3] := by
  let f : V →ₗ[ℂ] Fin 3 → ℂ :=
    LinearMap.pi ![b.coord 5, b.coord 0, b.coord 2]
  have hcomp : f ∘ ![b 5, b 0 - μ • b 4, b 2 - (q ^ 2)⁻¹ • b 3] =
      ⇑(Pi.basisFun ℂ (Fin 3)) := by
    funext i j
    fin_cases i <;> fin_cases j <;> simp [f]
  have hf : LinearIndependent ℂ
      (f ∘ ![b 5, b 0 - μ • b 4, b 2 - (q ^ 2)⁻¹ • b 3]) := by
    rw [hcomp]
    exact (Pi.basisFun ℂ (Fin 3)).linearIndependent
  exact LinearIndependent.of_comp f hf

lemma hodge_finrank_selfdual_span
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis (Fin 6) ℂ V) :
    Module.finrank ℂ (Submodule.span ℂ {b 4, b 1, b 2 + b 3}) = 3 := by
  have hli := hodge_selfdual_linearIndependent V b
  have hset : ({b 4, b 1, b 2 + b 3} : Set V) =
      Set.range ![b 4, b 1, b 2 + b 3] := by
    ext y
    constructor
    · intro hy
      simp at hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨2, by simp⟩
    · intro hy
      rcases hy with ⟨i, rfl⟩
      fin_cases i <;> simp
  rw [hset]
  exact (finrank_span_eq_card hli).trans (by simp)

lemma hodge_finrank_antidual_span
    (q : ℂ) (V : Type*) [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis (Fin 6) ℂ V) (μ : ℂ) :
    Module.finrank ℂ
      (Submodule.span ℂ {b 5, b 0 - μ • b 4, b 2 - (q ^ 2)⁻¹ • b 3}) = 3 := by
  have hli := hodge_antidual_linearIndependent q V b μ
  have hset : ({b 5, b 0 - μ • b 4, b 2 - (q ^ 2)⁻¹ • b 3} : Set V) =
      Set.range ![b 5, b 0 - μ • b 4, b 2 - (q ^ 2)⁻¹ • b 3] := by
    ext y
    constructor
    · intro hy
      simp at hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
      · exact ⟨2, by simp⟩
    · intro hy
      rcases hy with ⟨i, rfl⟩
      fin_cases i <;> simp
  rw [hset]
  exact (finrank_span_eq_card hli).trans (by simp)

/- verified submission -/
theorem hodge_operator_on_two_forms
    (q : ℂ) (hq0 : q ≠ 0) (hq_one : q ^ 2 ≠ (1 : ℂ))
    (hq_neg_one : q ^ 2 ≠ (-1 : ℂ))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis (Fin 6) ℂ V) (star : V →ₗ[ℂ] V) :
    let μ : ℂ := 1 - (q ^ 2)⁻¹
    let e_ab : V := b 0
    let e_ac : V := b 1
    let e_ad : V := b 2
    let e_bc : V := b 3
    let e_bd : V := b 4
    let e_cd : V := b 5
    (star e_ab = -e_ab + (2 * μ) • e_bd ∧
      star e_ac = e_ac ∧
      star e_ad = (1 / (1 + q ^ 2)) •
        ((2 : ℂ) • e_bc - (q ^ 2 * μ) • e_ad) ∧
      star e_bc = (q ^ 2 / (1 + q ^ 2)) •
        ((2 : ℂ) • e_ad + μ • e_bc) ∧
      star e_bd = e_bd ∧
      star e_cd = -e_cd) →
    star.comp star = LinearMap.id ∧
      LinearMap.ker (star - LinearMap.id) =
        Submodule.span ℂ {e_bd, e_ac, e_ad + e_bc} ∧
      LinearMap.ker (star + LinearMap.id) =
        Submodule.span ℂ
          {e_cd, e_ab - μ • e_bd, e_ad - (q ^ 2)⁻¹ • e_bc} ∧
      Module.finrank ℂ (LinearMap.ker (star - LinearMap.id)) = 3 ∧
      Module.finrank ℂ (LinearMap.ker (star + LinearMap.id)) = 3 := by
  intro μ e_ab e_ac e_ad e_bc e_bd e_cd h
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := h
  have hμ : μ = 1 - (q ^ 2)⁻¹ := rfl
  have hsquare : star.comp star = LinearMap.id :=
    hodge_star_square q hq0 hq_neg_one V b star μ hμ h0 h1 h2 h3 h4 h5
  have hker_sd : LinearMap.ker (star - LinearMap.id) =
      Submodule.span ℂ {b 4, b 1, b 2 + b 3} :=
    hodge_ker_selfdual q hq0 hq_neg_one V b star μ hμ h0 h1 h2 h3 h4 h5
  have hker_ad : LinearMap.ker (star + LinearMap.id) =
      Submodule.span ℂ {b 5, b 0 - μ • b 4, b 2 - (q ^ 2)⁻¹ • b 3} :=
    hodge_ker_antidual q hq0 hq_neg_one V b star μ hμ h0 h1 h2 h3 h4 h5
  refine ⟨hsquare, hker_sd, hker_ad, ?_, ?_⟩
  · rw [hker_sd]
    exact hodge_finrank_selfdual_span V b
  · rw [hker_ad]
    exact hodge_finrank_antidual_span q V b μ

end Rollout_p2692_hodge_operator_on_two_forms

#check_dependency_graph "Rollout_p2692_hodge_operator_on_two_forms.hodge_operator_on_two_forms" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"star ∘ₗ star = LinearMap.id ∧ (star - LinearMap.id).ker = Submodule.span ℂ {e_bd, e_ac, e_ad + e_bc} ∧ (star + LinearMap.id).ker = Submodule.span ℂ {e_cd, e_ab - μ • e_bd, e_ad - (q ^ 2)⁻¹ • e_bc} ∧ Module.finrank ℂ ↥(star - LinearMap.id).ker = 3 ∧ Module.finrank ℂ ↥(star + LinearMap.id).ker = 3\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hq0\",\"statement\":\"q ≠ 0\"},{\"name\":\"hq_neg_one\",\"statement\":\"q ^ 2 ≠ -1\"},{\"name\":\"h\",\"statement\":\"star e_ab = -e_ab + (2 * μ) • e_bd ∧ star e_ac = e_ac ∧ star e_ad = (1 / (1 + q ^ 2)) • (2 • e_bc - (q ^ 2 * μ) • e_ad) ∧ star e_bc = (q ^ 2 / (1 + q ^ 2)) • (2 • e_ad + μ • e_bc) ∧ star e_bd = e_bd ∧ star e_cd = -e_cd\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2692_hodge_operator_on_two_forms\",\"reconstructedProofSha256\":\"511cf31754ce326f82da01a926e538b38691d9f621de1a88c78b35f35f930c0f\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p2692_hodge_operator_on_two_forms.hodge_operator_on_two_forms\",\"topologySha256\":\"f78a667584570d9c4fb9b59661d293e0d2173c9926ebeb29901dc26023276f9e\"}"

namespace Rollout_p2697_finite_field_normalized_one_cocycle_iff

-- graph_id: p2697_finite_field_normalized_one_cocycle_iff
-- topology_sha256: 4688cecc6caa9aaae7cb3c31292c9b97c22cc81698adb4908adfe5a123c9c151
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

#check_dependency_graph "Rollout_p2697_finite_field_normalized_one_cocycle_iff.finite_field_normalized_one_cocycle_iff" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(α 0 = 0 ∧ ∀ (x y : ZMod q), α (x + y) = α x + (algebraMap (ZMod p) (GaloisField p 2)) ↑ν ^ x.val * α y) ↔ ∃ r, r ≠ 0 ∧ α 0 = 0 ∧ ∀ (x : ZMod q), x ≠ 0 → α x = r * ∑ j ∈ Finset.range x.val, (algebraMap (ZMod p) (GaloisField p 2)) ↑ν ^ j\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"Fact (Nat.Prime p)\"},{\"name\":\"<generated-instance>\",\"statement\":\"Fact (Nat.Prime q)\"},{\"name\":\"hν\",\"statement\":\"orderOf ν = q\"},{\"name\":\"hα\",\"statement\":\"α ≠ 0\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2697_finite_field_normalized_one_cocycle_iff\",\"reconstructedProofSha256\":\"b5feb0fdc31683c5668e76b00cb56480ece0411b4737e50b6452e14f0ba7512b\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p2697_finite_field_normalized_one_cocycle_iff.finite_field_normalized_one_cocycle_iff\",\"topologySha256\":\"4688cecc6caa9aaae7cb3c31292c9b97c22cc81698adb4908adfe5a123c9c151\"}"

namespace Rollout_p2732_exteriorsquare_surjective_commutatorquotie

-- graph_id: p2732_exteriorsquare_surjective_commutatorquotie
-- topology_sha256: 4c76e8035e3fa2c06ceb6be0f2951f8fb779a8602cf5b04a5536a790c7d79b17
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

#check_dependency_graph "Rollout_p2732_exteriorsquare_surjective_commutatorquotie.exteriorSquare_surjective_commutatorQuotient" against "{\"edges\":[{\"conclusion\":{\"name\":\"hmap\",\"statement\":\"∀ (a b : G), f (Multiplicative.ofAdd ((exteriorPower.ιMulti ℤ 2) ![Additive.ofMul ((QuotientGroup.mk' K) a), Additive.ofMul ((QuotientGroup.mk' K) b)])) = (QuotientGroup.mk' D) ⟨⁅a, b⁆, ⋯⟩\"},\"graphEdgeId\":\"h_001_hmap\",\"premises\":[{\"name\":\"hH\",\"statement\":\"commutator G ≤ H\"}],\"rawEdgeId\":\"telescope_12\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∃ f, Function.Surjective ⇑f ∧ ∀ (a b : G), f (Multiplicative.ofAdd ((exteriorPower.ιMulti ℤ 2) ![Additive.ofMul ((QuotientGroup.mk' K) a), Additive.ofMul ((QuotientGroup.mk' K) b)])) = (QuotientGroup.mk' D) ⟨⁅a, b⁆, ⋯⟩\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hH\",\"statement\":\"commutator G ≤ H\"},{\"name\":\"hmap\",\"statement\":\"∀ (a b : G), f (Multiplicative.ofAdd ((exteriorPower.ιMulti ℤ 2) ![Additive.ofMul ((QuotientGroup.mk' K) a), Additive.ofMul ((QuotientGroup.mk' K) b)])) = (QuotientGroup.mk' D) ⟨⁅a, b⁆, ⋯⟩\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2732_exteriorsquare_surjective_commutatorquotie\",\"reconstructedProofSha256\":\"0e9b57e4a180583873c549fa4a8f637de40a9ead2fac2b86ad29923ef675e6bb\",\"selectedEdgeCount\":2,\"theoremName\":\"Rollout_p2732_exteriorsquare_surjective_commutatorquotie.exteriorSquare_surjective_commutatorQuotient\",\"topologySha256\":\"4c76e8035e3fa2c06ceb6be0f2951f8fb779a8602cf5b04a5536a790c7d79b17\"}"

namespace Rollout_p2753_planeposet_union_islinearorder

-- graph_id: p2753_planeposet_union_islinearorder
-- topology_sha256: 3912a60a684387b05d5689bb47a7924195b241da766a67af7244fb7d2a9fd397
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

#check_dependency_graph "Rollout_p2753_planeposet_union_islinearorder.planePoset_union_isLinearOrder" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"IsLinearOrder P fun x y => leH x y ∨ leR x y\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hH\",\"statement\":\"IsPartialOrder P leH\"},{\"name\":\"hR\",\"statement\":\"IsPartialOrder P leR\"},{\"name\":\"hcompat\",\"statement\":\"∀ {x y : P}, x ≠ y → (leH x y ∨ leH y x ↔ ¬(leR x y ∨ leR y x))\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2753_planeposet_union_islinearorder\",\"reconstructedProofSha256\":\"f47032c34e14a483d358cec8af85aa2ceea28ad2a3d4eba066f481c66d572597\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p2753_planeposet_union_islinearorder.planePoset_union_isLinearOrder\",\"topologySha256\":\"3912a60a684387b05d5689bb47a7924195b241da766a67af7244fb7d2a9fd397\"}"

namespace Rollout_p2763_graded_simple_mul_nonzero

-- graph_id: p2763_graded_simple_mul_nonzero
-- topology_sha256: 98405581fdf2d54215726224b23b9ab12382ea5a6b9e50d5bcb9beb5d4539aa7
/- accepted add_to_file helper 1 -/
lemma graded_exists_finset_decomp
    (G K A : Type*) [Group G] [Field K] [AddCommGroup A] [Module K A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤) (z : A) :
    ∃ s : Finset G, ∃ f : G → A,
      (∀ i ∈ s, f i ∈ 𝒜 i) ∧ ∑ i ∈ s, f i = z := by
  classical
  let e := h_direct.1.linearEquiv h_direct.2
  let d : Π₀ i : G, 𝒜 i := e.symm z
  refine ⟨d.support, fun i => (d i : A), ?_, ?_⟩
  · intro i hi
    exact (d i).property
  · have hz : e d = z := e.apply_symm_apply z
    rw [iSupIndep.linearEquiv_apply, DFinsupp.sumAddHom_apply] at hz
    simpa [DFinsupp.sum, d] using hz

/- accepted add_to_file helper 2 -/
namespace GradedSimpleProof

def sandwichLeftAnn
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A) (a : A) : Submodule K A where
  carrier := {y | ∀ (k : G) (x : A), x ∈ 𝒜 k → a * x * y = 0}
  zero_mem' := by
    intro k x hx
    simp
  add_mem' {y z} hy hz := by
    intro k x hx
    rw [mul_add, hy k x hx, hz k x hx, add_zero]
  smul_mem' c {y} hy := by
    intro k x hx
    rw [mul_smul_comm, hy k x hx, smul_zero]

end GradedSimpleProof

/- accepted add_to_file helper 3 -/
namespace GradedSimpleProof

lemma sandwichLeftAnn_graded
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤)
    (h_mul : ∀ {g h : G} {x y : A}, x ∈ 𝒜 g → y ∈ 𝒜 h → x * y ∈ 𝒜 (g * h))
    {g : G} {a : A} (ha : a ∈ 𝒜 g) :
    iSup (fun i : G => 𝒜 i ⊓ sandwichLeftAnn G K A 𝒜 a) =
      sandwichLeftAnn G K A 𝒜 a := by
  apply le_antisymm
  · apply iSup_le
    intro i
    exact inf_le_right
  · intro y hy
    obtain ⟨s, f, hf, hsum⟩ := graded_exists_finset_decomp G K A 𝒜 h_direct y
    rw [Submodule.mem_iSup]
    intro N hN
    have hcomp : ∀ i ∈ s, f i ∈ sandwichLeftAnn G K A 𝒜 a := by
      intro i hi k x hx
      let c : G := g * k
      have hq : iSupIndep (fun j : G => 𝒜 (c * j)) :=
        h_direct.1.comp (mul_right_injective c)
      have hzero : ∑ j ∈ s, a * x * f j = 0 := by
        calc
          ∑ j ∈ s, a * x * f j = (a * x) * (∑ j ∈ s, f j) := by
            rw [Finset.mul_sum]
          _ = a * x * y := by rw [hsum]
          _ = 0 := hy k x hx
      have hmem : ∀ j ∈ s, a * x * f j ∈ 𝒜 (c * j) := by
        intro j hj
        exact h_mul (h_mul ha hx) (hf j hj)
      exact (iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero
        (fun j : G => 𝒜 (c * j))).1 hq s (fun j => a * x * f j) hmem hzero i hi
    rw [← hsum]
    exact N.sum_mem (fun i hi => hN i ⟨hf i hi, hcomp i hi⟩)

end GradedSimpleProof

/- accepted add_to_file helper 4 -/
namespace GradedSimpleProof

lemma sandwichLeftAnn_left_ideal
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤)
    (a r : A) {y : A}
    (hy : y ∈ sandwichLeftAnn G K A 𝒜 a) :
    r * y ∈ sandwichLeftAnn G K A 𝒜 a := by
  intro k x hx
  obtain ⟨s, f, hf, hsum⟩ := graded_exists_finset_decomp G K A 𝒜 h_direct (x * r)
  calc
    a * x * (r * y) = a * (x * r) * y := by simp [mul_assoc]
    _ = a * (∑ i ∈ s, f i) * y := by rw [← hsum]
    _ = ∑ i ∈ s, a * f i * y := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact hy i (f i) (hf i hi)

lemma sandwichLeftAnn_right_ideal
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (a r : A) {y : A}
    (hy : y ∈ sandwichLeftAnn G K A 𝒜 a) :
    y * r ∈ sandwichLeftAnn G K A 𝒜 a := by
  intro k x hx
  rw [← mul_assoc (a * x) y r, hy k x hx, zero_mul]

end GradedSimpleProof

/- accepted add_to_file helper 5 -/
namespace GradedSimpleProof

def tripleLeftAnn
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A) : Submodule K A where
  carrier := {z | ∀ (k : G) (x : A), x ∈ 𝒜 k →
    ∀ (l : G) (y : A), y ∈ 𝒜 l → z * x * y = 0}
  zero_mem' := by
    intro k x hx l y hy
    simp
  add_mem' {z w} hz hw := by
    intro k x hx l y hy
    rw [add_mul, add_mul, hz k x hx l y hy, hw k x hx l y hy, add_zero]
  smul_mem' c {z} hz := by
    intro k x hx l y hy
    rw [smul_mul_assoc, smul_mul_assoc, hz k x hx l y hy, smul_zero]

end GradedSimpleProof

/- accepted add_to_file helper 6 -/
namespace GradedSimpleProof

lemma tripleLeftAnn_graded
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤)
    (h_mul : ∀ {g h : G} {x y : A}, x ∈ 𝒜 g → y ∈ 𝒜 h → x * y ∈ 𝒜 (g * h)) :
    iSup (fun i : G => 𝒜 i ⊓ tripleLeftAnn G K A 𝒜) =
      tripleLeftAnn G K A 𝒜 := by
  apply le_antisymm
  · apply iSup_le
    intro i
    exact inf_le_right
  · intro z hz
    obtain ⟨s, f, hf, hsum⟩ := graded_exists_finset_decomp G K A 𝒜 h_direct z
    rw [Submodule.mem_iSup]
    intro N hN
    have hcomp : ∀ i ∈ s, f i ∈ tripleLeftAnn G K A 𝒜 := by
      intro i hi k x hx l y hy
      have hinj : Function.Injective (fun j : G => (j * k) * l) :=
        (mul_left_injective l).comp (mul_left_injective k)
      have hq : iSupIndep (fun j : G => 𝒜 ((j * k) * l)) :=
        h_direct.1.comp hinj
      have hzero : ∑ j ∈ s, f j * x * y = 0 := by
        calc
          ∑ j ∈ s, f j * x * y = (∑ j ∈ s, f j) * x * y := by
            rw [Finset.sum_mul, Finset.sum_mul]
          _ = z * x * y := by rw [hsum]
          _ = 0 := hz k x hx l y hy
      have hmem : ∀ j ∈ s, f j * x * y ∈ 𝒜 ((j * k) * l) := by
        intro j hj
        exact h_mul (h_mul (hf j hj) hx) hy
      exact (iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero
        (fun j : G => 𝒜 ((j * k) * l))).1 hq s
        (fun j => f j * x * y) hmem hzero i hi
    rw [← hsum]
    exact N.sum_mem (fun i hi => hN i ⟨hf i hi, hcomp i hi⟩)

end GradedSimpleProof

/- accepted add_to_file helper 7 -/
namespace GradedSimpleProof

lemma tripleLeftAnn_left_ideal
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A) (r : A) {z : A}
    (hz : z ∈ tripleLeftAnn G K A 𝒜) :
    r * z ∈ tripleLeftAnn G K A 𝒜 := by
  intro k x hx l y hy
  calc
    r * z * x * y = r * (z * x * y) := by simp [mul_assoc]
    _ = 0 := by rw [hz k x hx l y hy, mul_zero]

lemma tripleLeftAnn_right_ideal
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤)
    (r : A) {z : A}
    (hz : z ∈ tripleLeftAnn G K A 𝒜) :
    z * r ∈ tripleLeftAnn G K A 𝒜 := by
  intro k x hx l y hy
  obtain ⟨s, f, hf, hsum⟩ := graded_exists_finset_decomp G K A 𝒜 h_direct (r * x)
  calc
    z * r * x * y = z * (r * x) * y := by simp [mul_assoc]
    _ = z * (∑ i ∈ s, f i) * y := by rw [← hsum]
    _ = ∑ i ∈ s, z * f i * y := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact hz i (f i) (hf i hi) l y hy

end GradedSimpleProof

/- accepted add_to_file helper 8 -/
namespace GradedSimpleProof

def homogeneousProductSet
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A] [Module K A]
    (𝒜 : G → Submodule K A) : Set A :=
  {p | ∃ (i : G) (x : A), x ∈ 𝒜 i ∧ ∃ (j : G) (y : A), y ∈ 𝒜 j ∧ p = x * y}

def homogeneousProductSubmodule
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A] [Module K A]
    (𝒜 : G → Submodule K A) : Submodule K A :=
  Submodule.span K (homogeneousProductSet G K A 𝒜)

lemma mem_homogeneousProductSubmodule
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A] [Module K A]
    (𝒜 : G → Submodule K A)
    {i j : G} {x y : A} (hx : x ∈ 𝒜 i) (hy : y ∈ 𝒜 j) :
    x * y ∈ homogeneousProductSubmodule G K A 𝒜 := by
  apply Submodule.subset_span
  exact ⟨i, x, hx, j, y, hy, rfl⟩

end GradedSimpleProof

/- accepted add_to_file helper 9 -/
namespace GradedSimpleProof

lemma homogeneousProductSubmodule_left_ideal
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤)
    (r : A) {p : A} (hp : p ∈ homogeneousProductSubmodule G K A 𝒜) :
    r * p ∈ homogeneousProductSubmodule G K A 𝒜 := by
  unfold homogeneousProductSubmodule at hp ⊢
  refine Submodule.span_induction (fun q hq => ?_) ?_ ?_ ?_ hp
  · obtain ⟨i, x, hx, j, y, hy, rfl⟩ := hq
    obtain ⟨s, f, hf, hsum⟩ := graded_exists_finset_decomp G K A 𝒜 h_direct (r * x)
    have hEq : r * (x * y) = ∑ n ∈ s, f n * y := by
      calc
        r * (x * y) = (r * x) * y := by simp [mul_assoc]
        _ = (∑ n ∈ s, f n) * y := by rw [← hsum]
        _ = ∑ n ∈ s, f n * y := by rw [Finset.sum_mul]
    rw [hEq]
    apply Submodule.sum_mem
    intro n hn
    exact mem_homogeneousProductSubmodule G K A 𝒜 (hf n hn) hy
  · simp
  · intro q₁ q₂ hq₁ hq₂ h₁ h₂
    rw [mul_add]
    exact (Submodule.span K (homogeneousProductSet G K A 𝒜)).add_mem h₁ h₂
  · intro c q hq h
    rw [mul_smul_comm]
    exact (Submodule.span K (homogeneousProductSet G K A 𝒜)).smul_mem c h

end GradedSimpleProof

/- accepted add_to_file helper 10 -/
namespace GradedSimpleProof

lemma homogeneousProductSubmodule_right_ideal
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤)
    (r : A) {p : A} (hp : p ∈ homogeneousProductSubmodule G K A 𝒜) :
    p * r ∈ homogeneousProductSubmodule G K A 𝒜 := by
  unfold homogeneousProductSubmodule at hp ⊢
  refine Submodule.span_induction (fun q hq => ?_) ?_ ?_ ?_ hp
  · obtain ⟨i, x, hx, j, y, hy, rfl⟩ := hq
    obtain ⟨s, f, hf, hsum⟩ := graded_exists_finset_decomp G K A 𝒜 h_direct (y * r)
    have hEq : (x * y) * r = ∑ n ∈ s, x * f n := by
      calc
        (x * y) * r = x * (y * r) := by rw [mul_assoc]
        _ = x * (∑ n ∈ s, f n) := by rw [← hsum]
        _ = ∑ n ∈ s, x * f n := by rw [Finset.mul_sum]
    rw [hEq]
    apply Submodule.sum_mem
    intro n hn
    exact mem_homogeneousProductSubmodule G K A 𝒜 hx (hf n hn)
  · simp
  · intro q₁ q₂ hq₁ hq₂ h₁ h₂
    rw [add_mul]
    exact (Submodule.span K (homogeneousProductSet G K A 𝒜)).add_mem h₁ h₂
  · intro c q hq h
    rw [smul_mul_assoc]
    exact (Submodule.span K (homogeneousProductSet G K A 𝒜)).smul_mem c h

end GradedSimpleProof

/- accepted add_to_file helper 11 -/
namespace GradedSimpleProof

lemma homogeneousProductSubmodule_graded
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_mul : ∀ {g h : G} {x y : A}, x ∈ 𝒜 g → y ∈ 𝒜 h → x * y ∈ 𝒜 (g * h)) :
    iSup (fun i : G => 𝒜 i ⊓ homogeneousProductSubmodule G K A 𝒜) =
      homogeneousProductSubmodule G K A 𝒜 := by
  apply le_antisymm
  · apply iSup_le
    intro i
    exact inf_le_right
  · unfold homogeneousProductSubmodule
    rw [Submodule.span_le]
    intro p hp
    obtain ⟨i, x, hx, j, y, hy, rfl⟩ := hp
    apply Submodule.mem_iSup_of_mem (i * j)
    exact ⟨h_mul hx hy, mem_homogeneousProductSubmodule G K A 𝒜 hx hy⟩

end GradedSimpleProof

/- accepted add_to_file helper 12 -/
namespace GradedSimpleProof

lemma mul_eq_zero_of_mem_homogeneousProductSubmodule
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (hH : tripleLeftAnn G K A 𝒜 = ⊤)
    (u : A) {p : A} (hp : p ∈ homogeneousProductSubmodule G K A 𝒜) :
    u * p = 0 := by
  unfold homogeneousProductSubmodule at hp
  refine Submodule.span_induction (fun q hq => ?_) ?_ ?_ ?_ hp
  · obtain ⟨i, x, hx, j, y, hy, rfl⟩ := hq
    have huH : u ∈ tripleLeftAnn G K A 𝒜 := by
      rw [hH]
      exact Submodule.mem_top
    rw [← mul_assoc]
    exact huH i x hx j y hy
  · simp
  · intro q₁ q₂ hq₁ hq₂ h₁ h₂
    rw [mul_add, h₁, h₂, add_zero]
  · intro c q hq h
    rw [mul_smul_comm, h, smul_zero]

end GradedSimpleProof

/- accepted add_to_file helper 13 -/
namespace GradedSimpleProof

lemma exists_homogeneous_mul_ne_zero
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤)
    (h_nonzero_mul : ∃ x y : A, x * y ≠ 0) :
    ∃ (i : G) (x : A), x ∈ 𝒜 i ∧
      ∃ (j : G) (y : A), y ∈ 𝒜 j ∧ x * y ≠ 0 := by
  obtain ⟨u, v, huv⟩ := h_nonzero_mul
  obtain ⟨su, fu, hfu, hsumu⟩ := graded_exists_finset_decomp G K A 𝒜 h_direct u
  obtain ⟨sv, fv, hfv, hsumv⟩ := graded_exists_finset_decomp G K A 𝒜 h_direct v
  have hprod_sum : (∑ i ∈ su, ∑ j ∈ sv, fu i * fv j) = u * v := by
    calc
      (∑ i ∈ su, ∑ j ∈ sv, fu i * fv j) =
          (∑ i ∈ su, fu i) * (∑ j ∈ sv, fv j) := by
        symm
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = u * v := by rw [hsumu, hsumv]
  have hsum_ne : (∑ i ∈ su, ∑ j ∈ sv, fu i * fv j) ≠ 0 := by
    rwa [hprod_sum]
  obtain ⟨i, hi, hinner⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  obtain ⟨j, hj, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hinner
  exact ⟨i, fu i, hfu i hi, j, fv j, hfv j hj, hp⟩

end GradedSimpleProof

/- verified submission -/
theorem graded_simple_mul_nonzero
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤)
    (h_mul : ∀ {g h : G} {x y : A}, x ∈ 𝒜 g → y ∈ 𝒜 h → x * y ∈ 𝒜 (g * h))
    (h_nonzero_mul : ∃ x y : A, x * y ≠ 0)
    (h_simple : ∀ I : Submodule K A,
      (∀ (r : A) {x : A}, x ∈ I → r * x ∈ I) →
      (∀ (r : A) {x : A}, x ∈ I → x * r ∈ I) →
      iSup (fun g => 𝒜 g ⊓ I) = I → I = ⊥ ∨ I = ⊤)
    {g h : G} {a b : A} (ha : a ∈ 𝒜 g) (hb : b ∈ 𝒜 h)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    ∃ k : G, ∃ x : A, x ∈ 𝒜 k ∧ a * x * b ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  let J : Submodule K A := GradedSimpleProof.sandwichLeftAnn G K A 𝒜 a
  have hbJ : b ∈ J := hcon
  have hJ := h_simple J
    (fun r {x} hx => GradedSimpleProof.sandwichLeftAnn_left_ideal G K A 𝒜 h_direct a r hx)
    (fun r {x} hx => GradedSimpleProof.sandwichLeftAnn_right_ideal G K A 𝒜 a r hx)
    (GradedSimpleProof.sandwichLeftAnn_graded G K A 𝒜 h_direct h_mul ha)
  have hJtop : J = ⊤ := by
    rcases hJ with hJbot | hJtop
    · have hbzero : b = 0 := by
        have hbJ' : b ∈ (⊥ : Submodule K A) := by
          rwa [← hJbot]
        simpa using hbJ'
      exact (hb0 hbzero).elim
    · exact hJtop
  let H : Submodule K A := GradedSimpleProof.tripleLeftAnn G K A 𝒜
  have haH : a ∈ H := by
    intro k x hx l y hy
    have hyJ : y ∈ J := by
      rw [hJtop]
      exact Submodule.mem_top
    exact hyJ k x hx
  have hH := h_simple H
    (fun r {x} hx => GradedSimpleProof.tripleLeftAnn_left_ideal G K A 𝒜 r hx)
    (fun r {x} hx => GradedSimpleProof.tripleLeftAnn_right_ideal G K A 𝒜 h_direct r hx)
    (GradedSimpleProof.tripleLeftAnn_graded G K A 𝒜 h_direct h_mul)
  have hHtop : H = ⊤ := by
    rcases hH with hHbot | hHtop
    · have hazero : a = 0 := by
        have haH' : a ∈ (⊥ : Submodule K A) := by
          rwa [← hHbot]
        simpa using haH'
      exact (ha0 hazero).elim
    · exact hHtop
  let P : Submodule K A := GradedSimpleProof.homogeneousProductSubmodule G K A 𝒜
  obtain ⟨i, x, hx, j, y, hy, hxy⟩ :=
    GradedSimpleProof.exists_homogeneous_mul_ne_zero G K A 𝒜 h_direct h_nonzero_mul
  have hxyP : x * y ∈ P :=
    GradedSimpleProof.mem_homogeneousProductSubmodule G K A 𝒜 hx hy
  have hP := h_simple P
    (fun r {z} hz => GradedSimpleProof.homogeneousProductSubmodule_left_ideal G K A 𝒜 h_direct r hz)
    (fun r {z} hz => GradedSimpleProof.homogeneousProductSubmodule_right_ideal G K A 𝒜 h_direct r hz)
    (GradedSimpleProof.homogeneousProductSubmodule_graded G K A 𝒜 h_mul)
  have hPtop : P = ⊤ := by
    rcases hP with hPbot | hPtop
    · have hxyzero : x * y = 0 := by
        have hxyP' : x * y ∈ (⊥ : Submodule K A) := by
          rwa [← hPbot]
        simpa using hxyP'
      exact (hxy hxyzero).elim
    · exact hPtop
  obtain ⟨u, v, huv⟩ := h_nonzero_mul
  have hvP : v ∈ P := by
    rw [hPtop]
    exact Submodule.mem_top
  have huvzero : u * v = 0 :=
    GradedSimpleProof.mul_eq_zero_of_mem_homogeneousProductSubmodule G K A 𝒜 hHtop u hvP
  exact huv huvzero

end Rollout_p2763_graded_simple_mul_nonzero

#check_dependency_graph "Rollout_p2763_graded_simple_mul_nonzero.graded_simple_mul_nonzero" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∃ k, ∃ x ∈ 𝒜 k, a * x * b ≠ 0\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"IsScalarTower K A A\"},{\"name\":\"<generated-instance>\",\"statement\":\"SMulCommClass K A A\"},{\"name\":\"h_direct\",\"statement\":\"iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤\"},{\"name\":\"h_mul\",\"statement\":\"∀ {g h : G} {x y : A}, x ∈ 𝒜 g → y ∈ 𝒜 h → x * y ∈ 𝒜 (g * h)\"},{\"name\":\"h_nonzero_mul\",\"statement\":\"∃ x y, x * y ≠ 0\"},{\"name\":\"h_simple\",\"statement\":\"∀ (I : Submodule K A), (∀ (r : A) {x : A}, x ∈ I → r * x ∈ I) → (∀ (r : A) {x : A}, x ∈ I → x * r ∈ I) → ⨆ g, 𝒜 g ⊓ I = I → I = ⊥ ∨ I = ⊤\"},{\"name\":\"ha\",\"statement\":\"a ∈ 𝒜 g\"},{\"name\":\"ha0\",\"statement\":\"a ≠ 0\"},{\"name\":\"hb0\",\"statement\":\"b ≠ 0\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2763_graded_simple_mul_nonzero\",\"reconstructedProofSha256\":\"5ba8f4765ac29d60d3f24451667edcb5ed86d3c0eb1b544243a4f7264ca68bcf\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p2763_graded_simple_mul_nonzero.graded_simple_mul_nonzero\",\"topologySha256\":\"98405581fdf2d54215726224b23b9ab12382ea5a6b9e50d5bcb9beb5d4539aa7\"}"

namespace Rollout_p2771_pbw_filtered_quadratic_relations_unique

-- graph_id: p2771_pbw_filtered_quadratic_relations_unique
-- topology_sha256: 777fa7833f8e565a5d771438cc1a0f128e4aa716361332d85c3e8108d8326c4c
/- accepted add_to_file helper 1 -/
lemma graded_proj_eq_of_mem
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {m n : ℕ} {x : T} (hx : x ∈ 𝒯 m) :
    GradedAlgebra.proj 𝒯 n x = if m = n then x else 0 := by
  classical
  rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem 𝒯 hx]
  by_cases h : m = n
  · subst h
    simp
  · simp [DirectSum.of_apply, h]

lemma graded_proj_self
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {n : ℕ} {x : T} (hx : x ∈ 𝒯 n) :
    GradedAlgebra.proj 𝒯 n x = x := by
  simpa using graded_proj_eq_of_mem 𝒯 (m := n) (n := n) hx

lemma graded_proj_mem
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (n : ℕ) (x : T) :
    GradedAlgebra.proj 𝒯 n x ∈ 𝒯 n := by
  classical
  rw [GradedAlgebra.proj_apply]
  exact (((DirectSum.decompose 𝒯) x) n).property

/- accepted add_to_file helper 2 -/
lemma graded_proj_eq_zero_of_mem_iSup_fin
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {n m : ℕ} (hnm : n ≤ m) {x : T}
    (hx : x ∈ ⨆ i : Fin n, 𝒯 (i : ℕ)) :
    GradedAlgebra.proj 𝒯 m x = 0 := by
  classical
  rw [Submodule.mem_iSup] at hx
  apply hx (LinearMap.ker (GradedAlgebra.proj 𝒯 m))
  intro i y hy
  rw [LinearMap.mem_ker, graded_proj_eq_of_mem 𝒯 hy]
  have hne : (i : ℕ) ≠ m := by
    omega
  simp [hne]

/- accepted add_to_file helper 3 -/
lemma graded_mem_iSup_fin_of_proj_eq_zero
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {n : ℕ} {x : T}
    (hx : ∀ m : ℕ, n ≤ m → GradedAlgebra.proj 𝒯 m x = 0) :
    x ∈ ⨆ i : Fin n, 𝒯 (i : ℕ) := by
  classical
  let d := DirectSum.decompose 𝒯 x
  have hsum : (∑ i ∈ d.support, ((d i) : T)) = x := by
    simpa [d] using DirectSum.sum_support_decompose 𝒯 x
  rw [← hsum]
  apply Submodule.sum_mem
  intro i hi
  have hlt : i < n := by
    by_contra hnot
    have hni : n ≤ i := Nat.le_of_not_gt hnot
    have hproj : GradedAlgebra.proj 𝒯 i x = 0 := hx i hni
    have hdi : d i = 0 := by
      apply Subtype.ext
      simpa [d, GradedAlgebra.proj_apply] using hproj
    have : i ∉ d.support := (DFinsupp.notMem_support_iff).2 hdi
    exact this hi
  exact le_iSup (fun j : Fin n => 𝒯 (j : ℕ)) ⟨i, hlt⟩ ((d i).property)

/- accepted add_to_file helper 4 -/
lemma graded_sub_proj_two_mem_iSup_fin_two
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {x : T} (hx : x ∈ ⨆ i : Fin 3, 𝒯 (i : ℕ)) :
    x - GradedAlgebra.proj 𝒯 2 x ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ) := by
  classical
  apply graded_mem_iSup_fin_of_proj_eq_zero 𝒯 (n := 2)
  intro m hm
  by_cases h2 : m = 2
  · subst h2
    rw [map_sub, graded_proj_self 𝒯 (n := 2)
      (x := GradedAlgebra.proj 𝒯 2 x) (graded_proj_mem 𝒯 2 x)]
    simp
  · have hm3 : 3 ≤ m := by omega
    have hxm : GradedAlgebra.proj 𝒯 m x = 0 :=
      graded_proj_eq_zero_of_mem_iSup_fin 𝒯 hm3 hx
    have hpm : GradedAlgebra.proj 𝒯 m (GradedAlgebra.proj 𝒯 2 x) = 0 := by
      rw [graded_proj_eq_of_mem 𝒯 (graded_proj_mem 𝒯 2 x)]
      have h2' : 2 ≠ m := fun h => h2 h.symm
      simp [h2']
    rw [map_sub, hxm, hpm, sub_zero]

/- accepted add_to_file helper 5 -/
lemma graded_proj_two_mul_of_mem_two
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (a s b : T) (hs : s ∈ 𝒯 2) :
    GradedAlgebra.proj 𝒯 2 (a * s * b) =
      GradedAlgebra.proj 𝒯 0 a * s * GradedAlgebra.proj 𝒯 0 b := by
  classical
  let da := DirectSum.decompose 𝒯 a
  let db := DirectSum.decompose 𝒯 b
  have ha : (∑ i ∈ da.support, ((da i) : T)) = a := by
    simpa [da] using DirectSum.sum_support_decompose 𝒯 a
  have hb : (∑ j ∈ db.support, ((db j) : T)) = b := by
    simpa [db] using DirectSum.sum_support_decompose 𝒯 b
  have hterm (i j : ℕ) :
      GradedAlgebra.proj 𝒯 2 (((da i : T) * s) * (db j : T)) =
        if i = 0 ∧ j = 0 then ((da i : T) * s) * (db j : T) else 0 := by
    have hmem : ((da i : T) * s) * (db j : T) ∈ 𝒯 (i + 2 + j) := by
      exact SetLike.mul_mem_graded
        (SetLike.mul_mem_graded (da i).property hs) (db j).property
    rw [graded_proj_eq_of_mem 𝒯 hmem]
    by_cases hij : i + 2 + j = 2
    · have hi : i = 0 := by omega
      have hj : j = 0 := by omega
      simp [hij, hi, hj]
    · have hnot : ¬ (i = 0 ∧ j = 0) := by
        rintro ⟨hi, hj⟩
        omega
      simp [hij, hnot]
  have hsum :
      (∑ i ∈ da.support, ∑ j ∈ db.support,
          GradedAlgebra.proj 𝒯 2 (((da i : T) * s) * (db j : T))) =
        ((da 0 : T) * s) * (db 0 : T) := by
    simp_rw [hterm]
    let f := fun i : ℕ => ∑ j ∈ db.support,
      (if i = 0 ∧ j = 0 then ((da i : T) * s) * (db j : T) else 0)
    have hinner : f 0 = ((da 0 : T) * s) * (db 0 : T) := by
      dsimp [f]
      apply Finset.sum_eq_single 0
      · intro j hj hj0
        simp [hj0]
      · intro h0
        have hdb : db 0 = 0 := (DFinsupp.notMem_support_iff).1 h0
        simp [hdb]
    calc
      (∑ i ∈ da.support, ∑ j ∈ db.support,
          if i = 0 ∧ j = 0 then ((da i : T) * s) * (db j : T) else 0)
          = f 0 := by
        apply Finset.sum_eq_single 0
        · intro i hi hi0
          dsimp [f]
          apply Finset.sum_eq_zero
          intro j hj
          simp [hi0]
        · intro h0
          dsimp [f]
          apply Finset.sum_eq_zero
          intro j hj
          have hda : da 0 = 0 := (DFinsupp.notMem_support_iff).1 h0
          by_cases hj0 : j = 0
          · simp [hj0, hda]
          · simp [hj0]
      _ = ((da 0 : T) * s) * (db 0 : T) := hinner
  calc
    GradedAlgebra.proj 𝒯 2 (a * s * b)
        = GradedAlgebra.proj 𝒯 2
            (∑ i ∈ da.support, ∑ j ∈ db.support,
              ((da i : T) * s) * (db j : T)) := by
          rw [← ha, ← hb]
          rw [Finset.sum_mul, Finset.sum_mul_sum]
    _ = ∑ i ∈ da.support,
          GradedAlgebra.proj 𝒯 2
            (∑ j ∈ db.support, ((da i : T) * s) * (db j : T)) := by
          rw [map_sum]
    _ = ∑ i ∈ da.support, ∑ j ∈ db.support,
          GradedAlgebra.proj 𝒯 2 (((da i : T) * s) * (db j : T)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [map_sum]
    _ = ((da 0 : T) * s) * (db 0 : T) := hsum
    _ = GradedAlgebra.proj 𝒯 0 a * s * GradedAlgebra.proj 𝒯 0 b := by
          have ha0 : GradedAlgebra.proj 𝒯 0 a = (da 0 : T) := by
            simp [GradedAlgebra.proj_apply, da]
          have hb0 : GradedAlgebra.proj 𝒯 0 b = (db 0 : T) := by
            simp [GradedAlgebra.proj_apply, db]
          rw [ha0, hb0]

/- accepted add_to_file helper 6 -/
lemma graded_span_degree_two_low_components
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (S : Set T) (hS : S ⊆ 𝒯 2)
    {x : T} (hx : x ∈ TwoSidedIdeal.span S) :
    ∀ i < 2, (DirectSum.decompose 𝒯 x) i = 0 := by
  classical
  refine TwoSidedIdeal.span_induction
    (p := fun x _ => ∀ i < 2, (DirectSum.decompose 𝒯 x) i = 0)
    ?_ ?_ ?_ ?_ ?_ ?_ hx
  · intro x hx i hi
    rw [DirectSum.decompose_of_mem 𝒯 (hS hx)]
    have hne : 2 ≠ i := by omega
    simp [DirectSum.of_apply, hne]
  · intro i hi
    simp
  · intro x y hx hy ihx ihy i hi
    simp [ihx i hi, ihy i hi]
  · intro x hx ihx i hi
    rw [DirectSum.decompose_neg]
    change - (((DirectSum.decompose 𝒯) x) i) = 0
    rw [ihx i hi, neg_zero]
  · intro a x hx ihx i hi
    rw [DirectSum.decompose_mul]
    exact mul_apply_eq_zero (A := 𝒯)
      (m := 0) (n := 2)
      (by intro j hj; omega)
      ihx hi
  · intro b x hx ihx i hi
    rw [DirectSum.decompose_mul]
    exact mul_apply_eq_zero (A := 𝒯)
      (m := 2) (n := 0)
      ihx
      (by intro j hj; omega)
      (by simpa using hi)

/- accepted add_to_file helper 7 -/
lemma graded_proj_two_mul_left_eq_of_low
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (a x : T)
    (hlow : ∀ i < 2, (DirectSum.decompose 𝒯 x) i = 0) :
    GradedAlgebra.proj 𝒯 2 (a * x) =
      GradedAlgebra.proj 𝒯 2 (a * GradedAlgebra.proj 𝒯 2 x) := by
  classical
  let d := DirectSum.decompose 𝒯 x
  have hsum : (∑ i ∈ d.support, ((d i) : T)) = x := by
    simpa [d] using DirectSum.sum_support_decompose 𝒯 x
  have hterm_zero_of_ne (i : ℕ) (hi : i ≠ 2) :
      GradedAlgebra.proj 𝒯 2 (a * (d i : T)) = 0 := by
    by_cases hlt : i < 2
    · have hdi : d i = 0 := by
        simpa [d] using hlow i hlt
      simp [hdi]
    · have hgt : 2 < i := by omega
      have hcomp : ((DirectSum.decompose 𝒯) (a * (d i : T))) 2 = 0 := by
        rw [DirectSum.decompose_mul, DirectSum.decompose_of_mem 𝒯 (d i).property]
        exact mul_apply_eq_zero (A := 𝒯)
          (m := 0) (n := i)
          (by intro j hj; omega)
          (by
            intro j hj
            have hne : i ≠ j := by omega
            simp [DirectSum.of_apply, hne])
          (by simpa using hgt)
      rw [GradedAlgebra.proj_apply, hcomp]
      rfl
  have hsum_single :
      (∑ i ∈ d.support, GradedAlgebra.proj 𝒯 2 (a * (d i : T))) =
        GradedAlgebra.proj 𝒯 2 (a * (d 2 : T)) := by
    apply Finset.sum_eq_single 2
    · intro i hi hi2
      exact hterm_zero_of_ne i hi2
    · intro h2
      have hd2 : d 2 = 0 := (DFinsupp.notMem_support_iff).1 h2
      simp [hd2]
  calc
    GradedAlgebra.proj 𝒯 2 (a * x)
        = GradedAlgebra.proj 𝒯 2 (a * ∑ i ∈ d.support, ((d i) : T)) := by
          rw [hsum]
    _ = ∑ i ∈ d.support, GradedAlgebra.proj 𝒯 2 (a * (d i : T)) := by
          rw [Finset.mul_sum, map_sum]
    _ = GradedAlgebra.proj 𝒯 2 (a * (d 2 : T)) := hsum_single
    _ = GradedAlgebra.proj 𝒯 2 (a * GradedAlgebra.proj 𝒯 2 x) := by
          rw [GradedAlgebra.proj_apply]
          simp [d]

lemma graded_proj_two_mul_right_eq_of_low
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (x b : T)
    (hlow : ∀ i < 2, (DirectSum.decompose 𝒯 x) i = 0) :
    GradedAlgebra.proj 𝒯 2 (x * b) =
      GradedAlgebra.proj 𝒯 2 (GradedAlgebra.proj 𝒯 2 x * b) := by
  classical
  let d := DirectSum.decompose 𝒯 x
  have hsum : (∑ i ∈ d.support, ((d i) : T)) = x := by
    simpa [d] using DirectSum.sum_support_decompose 𝒯 x
  have hterm_zero_of_ne (i : ℕ) (hi : i ≠ 2) :
      GradedAlgebra.proj 𝒯 2 ((d i : T) * b) = 0 := by
    by_cases hlt : i < 2
    · have hdi : d i = 0 := by
        simpa [d] using hlow i hlt
      simp [hdi]
    · have hgt : 2 < i := by omega
      have hcomp : ((DirectSum.decompose 𝒯) ((d i : T) * b)) 2 = 0 := by
        rw [DirectSum.decompose_mul, DirectSum.decompose_of_mem 𝒯 (d i).property]
        exact mul_apply_eq_zero (A := 𝒯)
          (m := i) (n := 0)
          (by
            intro j hj
            have hne : i ≠ j := by omega
            simp [DirectSum.of_apply, hne])
          (by intro j hj; omega)
          (by simpa using hgt)
      rw [GradedAlgebra.proj_apply, hcomp]
      rfl
  have hsum_single :
      (∑ i ∈ d.support, GradedAlgebra.proj 𝒯 2 ((d i : T) * b)) =
        GradedAlgebra.proj 𝒯 2 ((d 2 : T) * b) := by
    apply Finset.sum_eq_single 2
    · intro i hi hi2
      exact hterm_zero_of_ne i hi2
    · intro h2
      have hd2 : d 2 = 0 := (DFinsupp.notMem_support_iff).1 h2
      simp [hd2]
  calc
    GradedAlgebra.proj 𝒯 2 (x * b)
        = GradedAlgebra.proj 𝒯 2 ((∑ i ∈ d.support, ((d i) : T)) * b) := by
          rw [hsum]
    _ = ∑ i ∈ d.support, GradedAlgebra.proj 𝒯 2 ((d i : T) * b) := by
          rw [Finset.sum_mul, map_sum]
    _ = GradedAlgebra.proj 𝒯 2 ((d 2 : T) * b) := hsum_single
    _ = GradedAlgebra.proj 𝒯 2 (GradedAlgebra.proj 𝒯 2 x * b) := by
          rw [GradedAlgebra.proj_apply]
          simp [d]

/- accepted add_to_file helper 8 -/
lemma graded_degree_two_mem_span_of_degree_two_generators
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (S : Set T) (hS : S ⊆ 𝒯 2)
    {z : T} (hz₂ : z ∈ 𝒯 2)
    (hz : z ∈ TwoSidedIdeal.span S) :
    z ∈ AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ s ∈ S, ∃ b ∈ 𝒯 0, x = a * s * b} := by
  classical
  let C : AddSubgroup T := AddSubgroup.closure
    {x : T | ∃ a ∈ 𝒯 0, ∃ s ∈ S, ∃ b ∈ 𝒯 0, x = a * s * b}
  have hproj_left (a c : T) (hc : c ∈ C) :
      GradedAlgebra.proj 𝒯 2 (a * c) ∈ C := by
    induction hc using AddSubgroup.closure_induction with
    | mem x hx =>
        rcases hx with ⟨u, hu, s, hsS, v, hv, rfl⟩
        have hrewrite :
            GradedAlgebra.proj 𝒯 2 (a * (u * s * v)) =
              GradedAlgebra.proj 𝒯 0 (a * u) * s * GradedAlgebra.proj 𝒯 0 v := by
          simpa [mul_assoc] using
            graded_proj_two_mul_of_mem_two 𝒯 (a * u) s v (hS hsS)
        rw [hrewrite]
        apply AddSubgroup.subset_closure
        exact ⟨GradedAlgebra.proj 𝒯 0 (a * u), graded_proj_mem 𝒯 0 (a * u),
          s, hsS, GradedAlgebra.proj 𝒯 0 v, graded_proj_mem 𝒯 0 v, rfl⟩
    | zero =>
        simp
    | add x y hx hy ihx ihy =>
        rw [mul_add, map_add]
        exact C.add_mem ihx ihy
    | neg x hx ihx =>
        rw [mul_neg, map_neg]
        exact C.neg_mem ihx
  have hproj_right (c b : T) (hc : c ∈ C) :
      GradedAlgebra.proj 𝒯 2 (c * b) ∈ C := by
    induction hc using AddSubgroup.closure_induction with
    | mem x hx =>
        rcases hx with ⟨u, hu, s, hsS, v, hv, rfl⟩
        have hrewrite :
            GradedAlgebra.proj 𝒯 2 ((u * s * v) * b) =
              GradedAlgebra.proj 𝒯 0 u * s * GradedAlgebra.proj 𝒯 0 (v * b) := by
          simpa [mul_assoc] using
            graded_proj_two_mul_of_mem_two 𝒯 u s (v * b) (hS hsS)
        rw [hrewrite]
        apply AddSubgroup.subset_closure
        exact ⟨GradedAlgebra.proj 𝒯 0 u, graded_proj_mem 𝒯 0 u,
          s, hsS, GradedAlgebra.proj 𝒯 0 (v * b), graded_proj_mem 𝒯 0 (v * b), rfl⟩
    | zero =>
        simp
    | add x y hx hy ihx ihy =>
        rw [add_mul, map_add]
        exact C.add_mem ihx ihy
    | neg x hx ihx =>
        rw [neg_mul, map_neg]
        exact C.neg_mem ihx
  have hproj : GradedAlgebra.proj 𝒯 2 z ∈ C := by
    refine TwoSidedIdeal.span_induction
      (p := fun x _ => GradedAlgebra.proj 𝒯 2 x ∈ C)
      ?_ ?_ ?_ ?_ ?_ ?_ hz
    · intro x hx
      rw [graded_proj_self 𝒯 (hS hx)]
      apply AddSubgroup.subset_closure
      exact ⟨1, SetLike.GradedOne.one_mem, x, hx, 1, SetLike.GradedOne.one_mem, by simp⟩
    · simp
    · intro x y hx hy ihx ihy
      rw [map_add]
      exact C.add_mem ihx ihy
    · intro x hx ihx
      rw [map_neg]
      exact C.neg_mem ihx
    · intro a x hx ihx
      rw [graded_proj_two_mul_left_eq_of_low 𝒯 a x
        (graded_span_degree_two_low_components 𝒯 S hS hx)]
      exact hproj_left a (GradedAlgebra.proj 𝒯 2 x) ihx
    · intro b x hx ihx
      rw [graded_proj_two_mul_right_eq_of_low 𝒯 x b
        (graded_span_degree_two_low_components 𝒯 S hS hx)]
      exact hproj_right (GradedAlgebra.proj 𝒯 2 x) b ihx
  rwa [graded_proj_self 𝒯 hz₂] at hproj

/- accepted add_to_file helper 9 -/
lemma graded_proj_mul_left_of_mem_zero
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {a b : T} (ha : a ∈ 𝒯 0) (i : ℕ) :
    GradedAlgebra.proj 𝒯 i (a * b) =
      a * GradedAlgebra.proj 𝒯 i b := by
  classical
  rw [GradedAlgebra.proj_apply, GradedAlgebra.proj_apply,
    DirectSum.coe_decompose_mul_of_left_mem_zero 𝒯 ha]

lemma graded_proj_mul_right_of_mem_zero
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {a b : T} (hb : b ∈ 𝒯 0) (i : ℕ) :
    GradedAlgebra.proj 𝒯 i (a * b) =
      GradedAlgebra.proj 𝒯 i a * b := by
  classical
  rw [GradedAlgebra.proj_apply, GradedAlgebra.proj_apply,
    DirectSum.coe_decompose_mul_of_right_mem_zero 𝒯 hb]

lemma graded_iSup_fin_two_mul_mem_zero
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {a d b : T} (ha : a ∈ 𝒯 0) (hb : b ∈ 𝒯 0)
    (hd : d ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ)) :
    a * d * b ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ) := by
  classical
  apply graded_mem_iSup_fin_of_proj_eq_zero 𝒯 (n := 2)
  intro m hm
  rw [graded_proj_mul_right_of_mem_zero 𝒯 hb,
    graded_proj_mul_left_of_mem_zero 𝒯 ha,
    graded_proj_eq_zero_of_mem_iSup_fin 𝒯 hm hd]
  simp

/- accepted add_to_file helper 10 -/
lemma graded_homogeneous_mem_span_degree_two_eq_zero_of_lt
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (S : Set T) (hS : S ⊆ 𝒯 2)
    {n : ℕ} (hn : n < 2) {x : T}
    (hxn : x ∈ 𝒯 n)
    (hx : x ∈ TwoSidedIdeal.span S) :
    x = 0 := by
  classical
  have hd : (DirectSum.decompose 𝒯 x) n = 0 :=
    graded_span_degree_two_low_components 𝒯 S hS hx n hn
  have hp : GradedAlgebra.proj 𝒯 n x = 0 := by
    rw [GradedAlgebra.proj_apply, hd]
    rfl
  rwa [graded_proj_self 𝒯 hxn] at hp

lemma graded_sub_proj_one_mem_iSup_fin_one
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {x : T} (hx : x ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ)) :
    x - GradedAlgebra.proj 𝒯 1 x ∈ ⨆ i : Fin 1, 𝒯 (i : ℕ) := by
  classical
  apply graded_mem_iSup_fin_of_proj_eq_zero 𝒯 (n := 1)
  intro m hm
  by_cases h1 : m = 1
  · subst h1
    rw [map_sub, graded_proj_self 𝒯 (n := 1)
      (x := GradedAlgebra.proj 𝒯 1 x) (graded_proj_mem 𝒯 1 x)]
    simp
  · have hm2 : 2 ≤ m := by omega
    have hxm : GradedAlgebra.proj 𝒯 m x = 0 :=
      graded_proj_eq_zero_of_mem_iSup_fin 𝒯 hm2 hx
    have hpm : GradedAlgebra.proj 𝒯 m (GradedAlgebra.proj 𝒯 1 x) = 0 := by
      rw [graded_proj_eq_of_mem 𝒯 (graded_proj_mem 𝒯 1 x)]
      have h1' : 1 ≠ m := fun h => h1 h.symm
      simp [h1']
    rw [map_sub, hxm, hpm, sub_zero]

lemma graded_mem_iSup_fin_one
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {x : T} (hx : x ∈ ⨆ i : Fin 1, 𝒯 (i : ℕ)) :
    x ∈ 𝒯 0 := by
  rw [Submodule.mem_iSup] at hx
  apply hx (𝒯 0)
  intro i
  have hi : i = 0 := by omega
  subst hi
  exact le_rfl

/- accepted add_to_file helper 11 -/
lemma pbw_low_ideal_eq_zero
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (P : Set T) (I : TwoSidedIdeal T)
    (hPI : TwoSidedIdeal.span P = I)
    (hPpbw : ∀ (n : ℕ) (x : T), x ∈ 𝒯 n →
      (x ∈ TwoSidedIdeal.span ((GradedAlgebra.proj 𝒯 2) '' P) ↔
        ∃ y ∈ I, x - y ∈ (⨆ i : Fin n, 𝒯 (i : ℕ))))
    {z : T} (hzI : z ∈ I)
    (hzF : z ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ)) :
    z = 0 := by
  classical
  let J : TwoSidedIdeal T :=
    TwoSidedIdeal.span ((GradedAlgebra.proj 𝒯 2) '' P)
  have hJhom : ((GradedAlgebra.proj 𝒯 2) '' P : Set T) ⊆ 𝒯 2 := by
    rintro x ⟨p, hp, rfl⟩
    exact graded_proj_mem 𝒯 2 p
  have hz₁ : GradedAlgebra.proj 𝒯 1 z = 0 := by
    have hz₁mem : GradedAlgebra.proj 𝒯 1 z ∈ 𝒯 1 :=
      graded_proj_mem 𝒯 1 z
    have hsub : z - GradedAlgebra.proj 𝒯 1 z ∈ ⨆ i : Fin 1, 𝒯 (i : ℕ) :=
      graded_sub_proj_one_mem_iSup_fin_one 𝒯 hzF
    have hdiff : GradedAlgebra.proj 𝒯 1 z - z ∈ ⨆ i : Fin 1, 𝒯 (i : ℕ) := by
      have hneg := (⨆ i : Fin 1, 𝒯 (i : ℕ)).neg_mem hsub
      convert hneg using 1
      abel
    have hz₁J : GradedAlgebra.proj 𝒯 1 z ∈ J := by
      exact (hPpbw 1 (GradedAlgebra.proj 𝒯 1 z) hz₁mem).2 ⟨z, hzI, hdiff⟩
    exact graded_homogeneous_mem_span_degree_two_eq_zero_of_lt 𝒯
      ((GradedAlgebra.proj 𝒯 2) '' P) hJhom (by norm_num : 1 < 2)
      hz₁mem hz₁J
  have hzF₁ : z ∈ ⨆ i : Fin 1, 𝒯 (i : ℕ) := by
    have hsub : z - GradedAlgebra.proj 𝒯 1 z ∈ ⨆ i : Fin 1, 𝒯 (i : ℕ) :=
      graded_sub_proj_one_mem_iSup_fin_one 𝒯 hzF
    simpa [hz₁] using hsub
  have hz₀ : z ∈ 𝒯 0 := graded_mem_iSup_fin_one 𝒯 hzF₁
  have hzJ : z ∈ J := by
    exact (hPpbw 0 z hz₀).2 ⟨z, hzI, by simp⟩
  exact graded_homogeneous_mem_span_degree_two_eq_zero_of_lt 𝒯
    ((GradedAlgebra.proj 𝒯 2) '' P) hJhom (by norm_num : 0 < 2)
    hz₀ hzJ

/- accepted add_to_file helper 12 -/
lemma tzero_bimodule_closure_subset_ideal
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (S : Set T) (I : TwoSidedIdeal T) (hS : S ⊆ I)
    {x : T}
    (hx : x ∈ AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ s ∈ S, ∃ b ∈ 𝒯 0, x = a * s * b}) :
    x ∈ I := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
      rcases hx with ⟨a, ha, s, hs, b, hb, rfl⟩
      exact TwoSidedIdeal.mul_mem_right I (a * s) b
        (TwoSidedIdeal.mul_mem_left I a s (hS hs))
  | zero =>
      exact TwoSidedIdeal.zero_mem I
  | add x y hx hy ihx ihy =>
      exact TwoSidedIdeal.add_mem I ihx ihy
  | neg x hx ihx =>
      exact TwoSidedIdeal.neg_mem I ihx

/- accepted add_to_file helper 13 -/
lemma degree_two_generator_closure_approx
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (Q : Set T)
    (hQ₂ : Q ⊆ (⨆ i : Fin 3, 𝒯 (i : ℕ)))
    {x : T}
    (hx : x ∈ AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ ((GradedAlgebra.proj 𝒯 2) '' Q),
        ∃ b ∈ 𝒯 0, x = a * q * b}) :
    ∃ y ∈ AddSubgroup.closure
        {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b},
      x - y ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ) := by
  classical
  let B : AddSubgroup T := AddSubgroup.closure
    {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b}
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
      rcases hx with ⟨a, ha, r, hr, b, hb, rfl⟩
      rcases hr with ⟨q, hq, rfl⟩
      refine ⟨a * q * b, ?_, ?_⟩
      · apply AddSubgroup.subset_closure
        exact ⟨a, ha, q, hq, b, hb, rfl⟩
      · have hlow : GradedAlgebra.proj 𝒯 2 q - q ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ) := by
          have hqF : q ∈ ⨆ i : Fin 3, 𝒯 (i : ℕ) := by
            have hqFset := hQ₂ hq
            rw [Set.iSup_eq_iUnion] at hqFset
            rw [Set.mem_iUnion] at hqFset
            rcases hqFset with ⟨i, hqi⟩
            exact le_iSup (fun j : Fin 3 => 𝒯 (j : ℕ)) i hqi
          have h := graded_sub_proj_two_mem_iSup_fin_two 𝒯 hqF
          have hneg := (⨆ i : Fin 2, 𝒯 (i : ℕ)).neg_mem h
          convert hneg using 1
          abel
        have := graded_iSup_fin_two_mul_mem_zero 𝒯 ha hb hlow
        convert this using 1
        rw [mul_sub, sub_mul]
  | zero =>
      exact ⟨0, B.zero_mem, by simp⟩
  | add x y hx hy ihx ihy =>
      rcases ihx with ⟨x', hx'B, hxx'⟩
      rcases ihy with ⟨y', hy'B, hyy'⟩
      refine ⟨x' + y', B.add_mem hx'B hy'B, ?_⟩
      have hsum := (⨆ i : Fin 2, 𝒯 (i : ℕ)).add_mem hxx' hyy'
      convert hsum using 1
      abel
  | neg x hx ihx =>
      rcases ihx with ⟨x', hx'B, hxx'⟩
      refine ⟨-x', B.neg_mem hx'B, ?_⟩
      have hneg := (⨆ i : Fin 2, 𝒯 (i : ℕ)).neg_mem hxx'
      convert hneg using 1
      abel

/- accepted add_to_file helper 14 -/
lemma pbw_generators_subset_tzero_bimodule_closure
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (P Q : Set T) (I : TwoSidedIdeal T)
    (hP₂ : P ⊆ (⨆ i : Fin 3, 𝒯 (i : ℕ)))
    (hQ₂ : Q ⊆ (⨆ i : Fin 3, 𝒯 (i : ℕ)))
    (hPI : TwoSidedIdeal.span P = I)
    (hQI : TwoSidedIdeal.span Q = I)
    (hPpbw : ∀ (n : ℕ) (x : T), x ∈ 𝒯 n →
      (x ∈ TwoSidedIdeal.span ((GradedAlgebra.proj 𝒯 2) '' P) ↔
        ∃ y ∈ I, x - y ∈ (⨆ i : Fin n, 𝒯 (i : ℕ))))
    (hQpbw : ∀ (n : ℕ) (x : T), x ∈ 𝒯 n →
      (x ∈ TwoSidedIdeal.span ((GradedAlgebra.proj 𝒯 2) '' Q) ↔
        ∃ y ∈ I, x - y ∈ (⨆ i : Fin n, 𝒯 (i : ℕ)))) :
    P ⊆ AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b} := by
  classical
  intro p hp
  have hpFset := hP₂ hp
  have hpF : p ∈ ⨆ i : Fin 3, 𝒯 (i : ℕ) := by
    rw [Set.iSup_eq_iUnion] at hpFset
    rw [Set.mem_iUnion] at hpFset
    rcases hpFset with ⟨i, hpi⟩
    exact le_iSup (fun j : Fin 3 => 𝒯 (j : ℕ)) i hpi
  have hpI : p ∈ I := by
    have h : p ∈ TwoSidedIdeal.span P := TwoSidedIdeal.subset_span hp
    rwa [hPI] at h
  have hp₂mem : GradedAlgebra.proj 𝒯 2 p ∈ 𝒯 2 :=
    graded_proj_mem 𝒯 2 p
  have hp₂diff : GradedAlgebra.proj 𝒯 2 p - p ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ) := by
    have h := graded_sub_proj_two_mem_iSup_fin_two 𝒯 hpF
    have hneg := (⨆ i : Fin 2, 𝒯 (i : ℕ)).neg_mem h
    convert hneg using 1
    abel
  have hp₂J : GradedAlgebra.proj 𝒯 2 p ∈
      TwoSidedIdeal.span ((GradedAlgebra.proj 𝒯 2) '' Q) := by
    exact (hQpbw 2 (GradedAlgebra.proj 𝒯 2 p) hp₂mem).2 ⟨p, hpI, hp₂diff⟩
  have hQhom : ((GradedAlgebra.proj 𝒯 2) '' Q : Set T) ⊆ 𝒯 2 := by
    rintro x ⟨q, hq, rfl⟩
    exact graded_proj_mem 𝒯 2 q
  have hp₂C : GradedAlgebra.proj 𝒯 2 p ∈ AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ ((GradedAlgebra.proj 𝒯 2) '' Q),
        ∃ b ∈ 𝒯 0, x = a * q * b} := by
    exact graded_degree_two_mem_span_of_degree_two_generators 𝒯
      ((GradedAlgebra.proj 𝒯 2) '' Q) hQhom hp₂mem hp₂J
  rcases degree_two_generator_closure_approx 𝒯 Q hQ₂ hp₂C with
    ⟨y, hyB, hp₂y⟩
  have hpyF : p - y ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ) := by
    have hpminus : p - GradedAlgebra.proj 𝒯 2 p ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ) :=
      graded_sub_proj_two_mem_iSup_fin_two 𝒯 hpF
    have hsum := (⨆ i : Fin 2, 𝒯 (i : ℕ)).add_mem hpminus hp₂y
    convert hsum using 1
    abel
  have hQIset : Q ⊆ I := by
    intro q hq
    have h : q ∈ TwoSidedIdeal.span Q := TwoSidedIdeal.subset_span hq
    rwa [hQI] at h
  have hyI : y ∈ I :=
    tzero_bimodule_closure_subset_ideal 𝒯 Q I hQIset hyB
  have hpyI : p - y ∈ I := TwoSidedIdeal.sub_mem I hpI hyI
  have hpy : p - y = 0 := pbw_low_ideal_eq_zero 𝒯 P I hPI hPpbw hpyI hpyF
  have hp_eq : p = y := sub_eq_zero.mp hpy
  rwa [hp_eq]

/- accepted add_to_file helper 15 -/
lemma tzero_bimodule_closure_mul_mem_zero
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (S : Set T) {a x b : T} (ha : a ∈ 𝒯 0) (hb : b ∈ 𝒯 0)
    (hx : x ∈ AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ s ∈ S, ∃ b ∈ 𝒯 0, x = a * s * b}) :
    a * x * b ∈ AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ s ∈ S, ∃ b ∈ 𝒯 0, x = a * s * b} := by
  let C : AddSubgroup T := AddSubgroup.closure
    {x : T | ∃ a ∈ 𝒯 0, ∃ s ∈ S, ∃ b ∈ 𝒯 0, x = a * s * b}
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
      rcases hx with ⟨u, hu, s, hs, v, hv, rfl⟩
      apply AddSubgroup.subset_closure
      refine ⟨a * u, ?_, s, hs, v * b, ?_, ?_⟩
      · exact SetLike.mul_mem_graded ha hu
      · exact SetLike.mul_mem_graded hv hb
      · simp [mul_assoc]
  | zero =>
      simp
  | add x y hx hy ihx ihy =>
      rw [mul_add, add_mul]
      exact C.add_mem ihx ihy
  | neg x hx ihx =>
      rw [mul_neg, neg_mul]
      exact C.neg_mem ihx

lemma tzero_bimodule_closure_le_of_generators_subset
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (P Q : Set T)
    (h : P ⊆ AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b}) :
    AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ p ∈ P, ∃ b ∈ 𝒯 0, x = a * p * b} ≤
    AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b} := by
  rw [AddSubgroup.closure_le]
  intro x hx
  rcases hx with ⟨a, ha, p, hp, b, hb, rfl⟩
  exact tzero_bimodule_closure_mul_mem_zero 𝒯 Q ha hb (h hp)

/- verified submission -/
theorem pbw_filtered_quadratic_relations_unique
    (k T : Type*) [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (P Q : Set T) (I : TwoSidedIdeal T)
    (hP₂ : P ⊆ (⨆ i : Fin 3, 𝒯 (i : ℕ)))
    (hQ₂ : Q ⊆ (⨆ i : Fin 3, 𝒯 (i : ℕ)))
    (hPI : TwoSidedIdeal.span P = I)
    (hQI : TwoSidedIdeal.span Q = I)
    (hPpbw : ∀ (n : ℕ) (x : T), x ∈ 𝒯 n →
      (x ∈ TwoSidedIdeal.span ((GradedAlgebra.proj 𝒯 2) '' P) ↔
        ∃ y ∈ I, x - y ∈ (⨆ i : Fin n, 𝒯 (i : ℕ))))
    (hQpbw : ∀ (n : ℕ) (x : T), x ∈ 𝒯 n →
      (x ∈ TwoSidedIdeal.span ((GradedAlgebra.proj 𝒯 2) '' Q) ↔
        ∃ y ∈ I, x - y ∈ (⨆ i : Fin n, 𝒯 (i : ℕ)))) :
    AddSubgroup.closure {x : T | ∃ a ∈ 𝒯 0, ∃ p ∈ P, ∃ b ∈ 𝒯 0, x = a * p * b} =
        AddSubgroup.closure {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b} ∧
      (((∃ M : AddSubgroup T, (M : Set T) = P ∧
          (∀ (a : 𝒯 0) (x : T), x ∈ M → (a : T) * x ∈ M) ∧
          (∀ (a : 𝒯 0) (x : T), x ∈ M → x * (a : T) ∈ M)) ∧
        (∃ N : AddSubgroup T, (N : Set T) = Q ∧
          (∀ (a : 𝒯 0) (x : T), x ∈ N → (a : T) * x ∈ N) ∧
          (∀ (a : 𝒯 0) (x : T), x ∈ N → x * (a : T) ∈ N))) → P = Q) := by
  classical
  let A : AddSubgroup T := AddSubgroup.closure
    {x : T | ∃ a ∈ 𝒯 0, ∃ p ∈ P, ∃ b ∈ 𝒯 0, x = a * p * b}
  let B : AddSubgroup T := AddSubgroup.closure
    {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b}
  have hPsub : P ⊆ B := by
    simpa [B] using pbw_generators_subset_tzero_bimodule_closure
      𝒯 P Q I hP₂ hQ₂ hPI hQI hPpbw hQpbw
  have hQsub : Q ⊆ A := by
    simpa [A] using pbw_generators_subset_tzero_bimodule_closure
      𝒯 Q P I hQ₂ hP₂ hQI hPI hQpbw hPpbw
  have hAleB : A ≤ B := by
    simpa [A, B] using tzero_bimodule_closure_le_of_generators_subset 𝒯 P Q hPsub
  have hBleA : B ≤ A := by
    simpa [A, B] using tzero_bimodule_closure_le_of_generators_subset 𝒯 Q P hQsub
  have hAB : A = B := le_antisymm hAleB hBleA
  constructor
  · simpa [A, B] using hAB
  · intro hclosed
    rcases hclosed with ⟨hPclosed, hQclosed⟩
    rcases hPclosed with ⟨M, hMP, hMleft, hMright⟩
    rcases hQclosed with ⟨N, hNQ, hNleft, hNright⟩
    have hgenP : {x : T | ∃ a ∈ 𝒯 0, ∃ p ∈ P, ∃ b ∈ 𝒯 0, x = a * p * b} ⊆
        (M : Set T) := by
      intro x hx
      rcases hx with ⟨a, ha, p, hp, b, hb, rfl⟩
      have hpM : p ∈ M := by
        have hpMset : p ∈ (M : Set T) := by
          rw [hMP]
          exact hp
        exact hpMset
      exact hMright ⟨b, hb⟩ ((a : T) * p)
        (hMleft ⟨a, ha⟩ p hpM)
    have hAleM : A ≤ M := by
      have h : AddSubgroup.closure
          {x : T | ∃ a ∈ 𝒯 0, ∃ p ∈ P, ∃ b ∈ 𝒯 0, x = a * p * b} ≤ M :=
        (AddSubgroup.closure_le M).2 hgenP
      simpa [A] using h
    have hMleA : M ≤ A := by
      intro x hx
      have hxP : x ∈ P := by
        have hxset : x ∈ (M : Set T) := hx
        rw [hMP] at hxset
        exact hxset
      apply AddSubgroup.subset_closure
      exact ⟨1, SetLike.GradedOne.one_mem, x, hxP, 1,
        SetLike.GradedOne.one_mem, by simp⟩
    have hAM : A = M := le_antisymm hAleM hMleA
    have hgenQ : {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b} ⊆
        (N : Set T) := by
      intro x hx
      rcases hx with ⟨a, ha, q, hq, b, hb, rfl⟩
      have hqN : q ∈ N := by
        have hqNset : q ∈ (N : Set T) := by
          rw [hNQ]
          exact hq
        exact hqNset
      exact hNright ⟨b, hb⟩ ((a : T) * q)
        (hNleft ⟨a, ha⟩ q hqN)
    have hBleN : B ≤ N := by
      have h : AddSubgroup.closure
          {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b} ≤ N :=
        (AddSubgroup.closure_le N).2 hgenQ
      simpa [B] using h
    have hNleB : N ≤ B := by
      intro x hx
      have hxQ : x ∈ Q := by
        have hxset : x ∈ (N : Set T) := hx
        rw [hNQ] at hxset
        exact hxset
      apply AddSubgroup.subset_closure
      exact ⟨1, SetLike.GradedOne.one_mem, x, hxQ, 1,
        SetLike.GradedOne.one_mem, by simp⟩
    have hBN : B = N := le_antisymm hBleN hNleB
    have hPAsets : P = (A : Set T) := by
      calc
        P = (M : Set T) := hMP.symm
        _ = (A : Set T) := congrArg (fun X : AddSubgroup T => (X : Set T)) hAM.symm
    have hQBsets : Q = (B : Set T) := by
      calc
        Q = (N : Set T) := hNQ.symm
        _ = (B : Set T) := congrArg (fun X : AddSubgroup T => (X : Set T)) hBN.symm
    calc
      P = (A : Set T) := hPAsets
      _ = (B : Set T) := congrArg (fun X : AddSubgroup T => (X : Set T)) hAB
      _ = Q := hQBsets.symm

end Rollout_p2771_pbw_filtered_quadratic_relations_unique

#check_dependency_graph "Rollout_p2771_pbw_filtered_quadratic_relations_unique.pbw_filtered_quadratic_relations_unique" against "{\"edges\":[{\"conclusion\":{\"name\":\"hPsub\",\"statement\":\"P ⊆ ↑B\"},\"graphEdgeId\":\"h_001_hpsub\",\"premises\":[{\"name\":\"hP₂\",\"statement\":\"P ⊆ ⨆ i, ↑(𝒯 ↑i)\"},{\"name\":\"hQ₂\",\"statement\":\"Q ⊆ ⨆ i, ↑(𝒯 ↑i)\"},{\"name\":\"hPI\",\"statement\":\"TwoSidedIdeal.span P = I\"},{\"name\":\"hQI\",\"statement\":\"TwoSidedIdeal.span Q = I\"},{\"name\":\"hPpbw\",\"statement\":\"∀ (n : ℕ), ∀ x ∈ 𝒯 n, x ∈ TwoSidedIdeal.span (⇑(GradedAlgebra.proj 𝒯 2) '' P) ↔ ∃ y ∈ I, x - y ∈ ⨆ i, 𝒯 ↑i\"},{\"name\":\"hQpbw\",\"statement\":\"∀ (n : ℕ), ∀ x ∈ 𝒯 n, x ∈ TwoSidedIdeal.span (⇑(GradedAlgebra.proj 𝒯 2) '' Q) ↔ ∃ y ∈ I, x - y ∈ ⨆ i, 𝒯 ↑i\"}],\"rawEdgeId\":\"telescope_18\"},{\"conclusion\":{\"name\":\"hQsub\",\"statement\":\"Q ⊆ ↑A\"},\"graphEdgeId\":\"h_002_hqsub\",\"premises\":[{\"name\":\"hP₂\",\"statement\":\"P ⊆ ⨆ i, ↑(𝒯 ↑i)\"},{\"name\":\"hQ₂\",\"statement\":\"Q ⊆ ⨆ i, ↑(𝒯 ↑i)\"},{\"name\":\"hPI\",\"statement\":\"TwoSidedIdeal.span P = I\"},{\"name\":\"hQI\",\"statement\":\"TwoSidedIdeal.span Q = I\"},{\"name\":\"hPpbw\",\"statement\":\"∀ (n : ℕ), ∀ x ∈ 𝒯 n, x ∈ TwoSidedIdeal.span (⇑(GradedAlgebra.proj 𝒯 2) '' P) ↔ ∃ y ∈ I, x - y ∈ ⨆ i, 𝒯 ↑i\"},{\"name\":\"hQpbw\",\"statement\":\"∀ (n : ℕ), ∀ x ∈ 𝒯 n, x ∈ TwoSidedIdeal.span (⇑(GradedAlgebra.proj 𝒯 2) '' Q) ↔ ∃ y ∈ I, x - y ∈ ⨆ i, 𝒯 ↑i\"}],\"rawEdgeId\":\"telescope_19\"},{\"conclusion\":{\"name\":\"hAleB\",\"statement\":\"A ≤ B\"},\"graphEdgeId\":\"h_003_haleb\",\"premises\":[{\"name\":\"hPsub\",\"statement\":\"P ⊆ ↑B\"}],\"rawEdgeId\":\"telescope_20\"},{\"conclusion\":{\"name\":\"hBleA\",\"statement\":\"B ≤ A\"},\"graphEdgeId\":\"h_004_hblea\",\"premises\":[{\"name\":\"hQsub\",\"statement\":\"Q ⊆ ↑A\"}],\"rawEdgeId\":\"telescope_21\"},{\"conclusion\":{\"name\":\"hAB\",\"statement\":\"A = B\"},\"graphEdgeId\":\"h_005_hab\",\"premises\":[{\"name\":\"hAleB\",\"statement\":\"A ≤ B\"},{\"name\":\"hBleA\",\"statement\":\"B ≤ A\"}],\"rawEdgeId\":\"telescope_22\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"AddSubgroup.closure {x | ∃ a ∈ 𝒯 0, ∃ p ∈ P, ∃ b ∈ 𝒯 0, x = a * p * b} = AddSubgroup.closure {x | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b} ∧ (((∃ M, ↑M = P ∧ (∀ (a : ↥(𝒯 0)), ∀ x ∈ M, ↑a * x ∈ M) ∧ ∀ (a : ↥(𝒯 0)), ∀ x ∈ M, x * ↑a ∈ M) ∧ ∃ N, ↑N = Q ∧ (∀ (a : ↥(𝒯 0)), ∀ x ∈ N, ↑a * x ∈ N) ∧ ∀ (a : ↥(𝒯 0)), ∀ x ∈ N, x * ↑a ∈ N) → P = Q)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hAB\",\"statement\":\"A = B\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2771_pbw_filtered_quadratic_relations_unique\",\"reconstructedProofSha256\":\"6fc09f55f988453b3e21047cab3f102f788cd0e1b6794dc196c661255e4b046c\",\"selectedEdgeCount\":6,\"theoremName\":\"Rollout_p2771_pbw_filtered_quadratic_relations_unique.pbw_filtered_quadratic_relations_unique\",\"topologySha256\":\"777fa7833f8e565a5d771438cc1a0f128e4aa716361332d85c3e8108d8326c4c\"}"

namespace Rollout_p2823_two_local_inner_derivation_matrix_is_inner

-- graph_id: p2823_two_local_inner_derivation_matrix_is_inner
-- topology_sha256: 1b9699c61657e610aa8a7c31dc7526a9ba513097385778c64a2cc219bdef2544
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

#check_dependency_graph "Rollout_p2823_two_local_inner_derivation_matrix_is_inner.two_local_inner_derivation_matrix_is_inner" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∃ B, ∀ (X : Matrix (Fin n) (Fin n) R), Δ X = B * X - X * B\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hΔ\",\"statement\":\"∀ (X Y : Matrix (Fin n) (Fin n) R), ∃ A, Δ X = A * X - X * A ∧ Δ Y = A * Y - Y * A\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2823_two_local_inner_derivation_matrix_is_inner\",\"reconstructedProofSha256\":\"ce2b9d527a19e0d81ae3b372b2ea9f0ae2eaa6c734c9c8ef157336fb4a970afd\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p2823_two_local_inner_derivation_matrix_is_inner.two_local_inner_derivation_matrix_is_inner\",\"topologySha256\":\"1b9699c61657e610aa8a7c31dc7526a9ba513097385778c64a2cc219bdef2544\"}"

namespace Rollout_p2889_newton_sum_identity

-- graph_id: p2889_newton_sum_identity
-- topology_sha256: 86a1e5f723ab4767e2f23767e35423d77febdd24a773f42fe5a06af671650480
/- verified submission -/

lemma newton_nodal_prod_range_succ {K : Type*} [Field K] (ξ : ℕ → K) (n : ℕ) :
    (∏ j ∈ Finset.range (n + 1), (Polynomial.X - Polynomial.C (ξ j))) =
      (Polynomial.X - Polynomial.C (ξ 0)) *
        ∏ j ∈ Finset.Icc 1 n, (Polynomial.X - Polynomial.C (ξ j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, ih,
        Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]
      ring

lemma newton_step_core {K : Type*} [Field K] (p : Polynomial K) (D b x0 xn : K)
    (hb : b ≠ 0) (hxb : b = x0 - xn) :
    p * Polynomial.C (D⁻¹) +
        ((Polynomial.X - Polynomial.C x0) * p) * Polynomial.C ((D * b)⁻¹) =
      (p * (Polynomial.X - Polynomial.C xn)) * Polynomial.C ((D * b)⁻¹) := by
  have hbc : Polynomial.C (b⁻¹ : K) * Polynomial.C b = (1 : Polynomial K) := by
    rw [← Polynomial.C_mul, inv_mul_cancel₀ hb, Polynomial.C_1]
  have hA : p * Polynomial.C (D⁻¹ : K) =
      p * Polynomial.C (D⁻¹ : K) * Polynomial.C (b⁻¹ : K) * Polynomial.C b := by
    calc
      p * Polynomial.C (D⁻¹ : K) = p * Polynomial.C (D⁻¹ : K) * 1 := by
        rw [mul_one]
      _ = p * Polynomial.C (D⁻¹ : K) *
            (Polynomial.C (b⁻¹ : K) * Polynomial.C b) := by
        rw [← hbc]
      _ = p * Polynomial.C (D⁻¹ : K) * Polynomial.C (b⁻¹ : K) * Polynomial.C b := by
        ring
  calc
    p * Polynomial.C (D⁻¹) +
          ((Polynomial.X - Polynomial.C x0) * p) * Polynomial.C ((D * b)⁻¹)
        = p * Polynomial.C (D⁻¹) * Polynomial.C (b⁻¹) * Polynomial.C b +
            ((Polynomial.X - Polynomial.C x0) * p) * Polynomial.C ((D * b)⁻¹) := by
          exact congrArg
            (fun z => z + ((Polynomial.X - Polynomial.C x0) * p) * Polynomial.C ((D * b)⁻¹))
            hA
    _ = (p * Polynomial.C (D⁻¹) * Polynomial.C (b⁻¹)) *
          (Polynomial.C b + (Polynomial.X - Polynomial.C x0)) := by
          rw [mul_inv, Polynomial.C_mul]
          ring
    _ = (p * Polynomial.C (D⁻¹) * Polynomial.C (b⁻¹)) *
          (Polynomial.X - Polynomial.C xn) := by
          rw [hxb, Polynomial.C_sub]
          ring
    _ = (p * (Polynomial.X - Polynomial.C xn)) * Polynomial.C ((D * b)⁻¹) := by
          rw [mul_inv, Polynomial.C_mul]
          ring

theorem newton_sum_identity
    {K : Type*} [Field K] (d : ℕ) (ξ : ℕ → K)
    (hξ : Set.InjOn ξ (Set.Icc 0 d)) :
    ∑ i ∈ Finset.range (d + 1),
        (∏ j ∈ Finset.range i, (Polynomial.X - Polynomial.C (ξ j))) *
          Polynomial.C ((∏ j ∈ Finset.Icc 1 i, (ξ 0 - ξ j))⁻¹) =
      (∏ j ∈ Finset.Icc 1 d, (Polynomial.X - Polynomial.C (ξ j))) *
        Polynomial.C ((∏ j ∈ Finset.Icc 1 d, (ξ 0 - ξ j))⁻¹) := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Finset.sum_range_succ]
      have hsubset : Set.Icc 0 d ⊆ Set.Icc 0 (d + 1) := by
        intro x hx
        exact ⟨hx.1, Nat.le_trans hx.2 (Nat.le_succ d)⟩
      rw [ih (Set.InjOn.mono hsubset hξ)]
      rw [newton_nodal_prod_range_succ ξ d]
      rw [Finset.prod_Icc_succ_top (a := 1) (b := d)
        (f := fun j => ξ 0 - ξ j) (by omega : 1 ≤ d + 1)]
      rw [Finset.prod_Icc_succ_top (a := 1) (b := d)
        (f := fun j => Polynomial.X - Polynomial.C (ξ j)) (by omega : 1 ≤ d + 1)]
      have hne : ξ 0 ≠ ξ (d + 1) := by
        exact hξ.ne (by simp) (by simp) (Nat.succ_ne_zero d).symm
      exact newton_step_core
        (∏ j ∈ Finset.Icc 1 d, (Polynomial.X - Polynomial.C (ξ j)))
        (∏ j ∈ Finset.Icc 1 d, (ξ 0 - ξ j))
        (ξ 0 - ξ (d + 1)) (ξ 0) (ξ (d + 1))
        (sub_ne_zero_of_ne hne) rfl

end Rollout_p2889_newton_sum_identity

#check_dependency_graph "Rollout_p2889_newton_sum_identity.newton_sum_identity" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∑ i ∈ Finset.range (d + 1), (∏ j ∈ Finset.range i, (Polynomial.X - Polynomial.C (ξ j))) * Polynomial.C (∏ j ∈ Finset.Icc 1 i, (ξ 0 - ξ j))⁻¹ = (∏ j ∈ Finset.Icc 1 d, (Polynomial.X - Polynomial.C (ξ j))) * Polynomial.C (∏ j ∈ Finset.Icc 1 d, (ξ 0 - ξ j))⁻¹\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hξ\",\"statement\":\"Set.InjOn ξ (Set.Icc 0 d)\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2889_newton_sum_identity\",\"reconstructedProofSha256\":\"0dedc31d2fbe09ed290221a5430e1740962d88440287f7d90c9f87d65121ad6c\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p2889_newton_sum_identity.newton_sum_identity\",\"topologySha256\":\"86a1e5f723ab4767e2f23767e35423d77febdd24a773f42fe5a06af671650480\"}"

namespace Rollout_p2920_proposition_3_8

-- graph_id: p2920_proposition_3_8
-- topology_sha256: 072a6258b8a4599f09053e96ae1c5d3b4f28aeefb6ed9495f914f7e8c63fff72
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

#check_dependency_graph "Rollout_p2920_proposition_3_8.proposition_3_8" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let κ := fun x ρ => if ρ.parts.Nodup then (-Polynomial.X) ^ ρ.parts.toFinset.card else 0; let ε := fun a => ∑ s, if h : ∑ i, ↑(s i) = a then ∑ p, ∏ i, κ (↑(s i)) (p i) else 0; let pp := fun a => ∑ s, if h : ∑ i, ↑(s i) = a then ∑ ρ, (1 - Polynomial.X) ^ ∑ i, (ρ i).parts.toFinset.card else 0; let ε₁ := fun a => Polynomial.eval 1 (ε a); ε k = ∑ r ∈ Finset.range (k + 1), Polynomial.C (ε₁ r) * pp (k - r)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2920_proposition_3_8\",\"reconstructedProofSha256\":\"ebb92f473f54b0b7dd3e27eb1b4bb2884ae689e01a898cfc10167c756afb7838\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p2920_proposition_3_8.proposition_3_8\",\"topologySha256\":\"072a6258b8a4599f09053e96ae1c5d3b4f28aeefb6ed9495f914f7e8c63fff72\"}"

namespace Rollout_p2937_coinvariants_addmonoidalgebra_eq_range

-- graph_id: p2937_coinvariants_addmonoidalgebra_eq_range
-- topology_sha256: efb7339bd7ad37f7add4d6ffea20ff5f7f3340ddaf8769ccd6fecd3d777912c5
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

#check_dependency_graph "Rollout_p2937_coinvariants_addmonoidalgebra_eq_range.coinvariants_addMonoidAlgebra_eq_range" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"AlgHom.equalizer c Algebra.TensorProduct.includeRight = (AddMonoidAlgebra.mapDomainAlgHom R R (φ.addSubmonoidComap S)).range\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hφ\",\"statement\":\"Function.Injective ⇑φ\"},{\"name\":\"hexact\",\"statement\":\"Function.Exact ⇑φ ⇑ψ\"},{\"name\":\"hc\",\"statement\":\"∀ (m : ↥S), c (AddMonoidAlgebra.single m 1) = AddMonoidAlgebra.single (ψ ↑m) 1 ⊗ₜ[R] AddMonoidAlgebra.single m 1\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2937_coinvariants_addmonoidalgebra_eq_range\",\"reconstructedProofSha256\":\"f145f7b99448c25ad8b6c5d7a4417cdd290a085a3e80d2c63688691b4f75be37\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p2937_coinvariants_addmonoidalgebra_eq_range.coinvariants_addMonoidAlgebra_eq_range\",\"topologySha256\":\"efb7339bd7ad37f7add4d6ffea20ff5f7f3340ddaf8769ccd6fecd3d777912c5\"}"

namespace Rollout_p3013_finite_compatible_shrinking_lemma

-- graph_id: p3013_finite_compatible_shrinking_lemma
-- topology_sha256: 8b9aca9fc832e636b74f6b231361ef29e13d563e12637c3874475ffa894fc31d
/- accepted add_to_file helper 1 -/
lemma compatible_shrinking_closureInterOfRelClosed
    {X : Type*} [TopologicalSpace X] {O B : Set X}
    (hBsub : B ⊆ O)
    (hB : IsClosed (Subtype.val ⁻¹' B : Set O)) :
    closure B ∩ O = B := by
  apply Set.Subset.antisymm
  · intro x hx
    have h := isClosed_preimage_val.mp hB
    have hx' : x ∈ O ∩ closure (O ∩ B) := by
      refine ⟨hx.2, ?_⟩
      have hcl : closure (O ∩ B) = closure B := by
        rw [Set.inter_eq_right.mpr hBsub]
      simpa [hcl] using hx.1
    exact h hx'
  · intro x hx
    exact ⟨subset_closure hx, hBsub hx⟩

/- accepted add_to_file helper 2 -/
lemma compatible_shrinking_relClosedDiff
    {X : Type*} [TopologicalSpace X] {O Z A : Set X}
    (hZO : Z ⊆ O)
    (hZ : IsClosed (Subtype.val ⁻¹' Z : Set O))
    (hA : IsOpen (Subtype.val ⁻¹' A : Set Z)) :
    IsClosed (Subtype.val ⁻¹' (Z \ A) : Set O) := by
  let B : Set X := Z \ A
  have hBsub : B ⊆ O := fun x hx => hZO hx.1
  have hBsubZ : B ⊆ Z := fun x hx => hx.1
  rw [isClosed_preimage_val]
  intro x hx
  have hxO : x ∈ O := hx.1
  have hxclB : x ∈ closure B := by
    change x ∈ closure (Z \ A)
    have hcl : closure (O ∩ (Z \ A)) = closure (Z \ A) := by
      rw [Set.inter_eq_right.mpr (fun y hy => hZO hy.1)]
    simpa [hcl] using hx.2
  have hxZ : x ∈ Z := by
    have hZchar := isClosed_preimage_val.mp hZ
    have hx' : x ∈ O ∩ closure (O ∩ Z) := by
      refine ⟨hxO, ?_⟩
      have hclZ : closure (O ∩ Z) = closure Z := by
        rw [Set.inter_eq_right.mpr hZO]
      have hBcl : closure B ⊆ closure Z := closure_mono hBsubZ
      simpa [hclZ] using hBcl hxclB
    exact hZchar hx'
  have hxnotA : x ∉ A := by
    intro hxA
    rcases isOpen_induced_iff.mp hA with ⟨V, hVopen, hVA⟩
    have hxV : x ∈ V := by
      have hzV : (⟨x, hxZ⟩ : Z) ∈ Subtype.val ⁻¹' V := by
        rw [hVA]
        exact hxA
      exact hzV
    have hdis : V ∩ B = ∅ := by
      ext y
      constructor
      · intro hy
        have hyZ : y ∈ Z := hy.2.1
        have hyA : y ∈ A := by
          have hzV : (⟨y, hyZ⟩ : Z) ∈ Subtype.val ⁻¹' V := hy.1
          rwa [hVA] at hzV
        exact (hy.2.2 hyA).elim
      · intro hy
        cases hy
    have hmem := (mem_closure_iff.mp hxclB) V hVopen hxV
    exact hmem.ne_empty hdis
  exact ⟨hxZ, hxnotA⟩

/- accepted add_to_file helper 3 -/
noncomputable def testIf (A : Set ℕ) : ℕ := @ite ℕ A.Nonempty (Classical.dec _) 1 0

/- accepted add_to_file helper 4 -/
noncomputable def compatibleDistAux
    {X : Type*} [MetricSpace X] (A : Set X) (x : X) : ℝ :=
  @ite ℝ A.Nonempty (Classical.dec _) (min 1 (Metric.infDist x A)) 1

lemma compatibleDistAux_zero_iff
    {X : Type*} [MetricSpace X] (A : Set X) (x : X) :
    compatibleDistAux A x = 0 ↔ x ∈ closure A := by
  unfold compatibleDistAux
  by_cases hA : A.Nonempty
  · rw [if_pos hA]
    constructor
    · intro h0
      have hd0 : Metric.infDist x A = 0 := by
        by_cases hdle : Metric.infDist x A ≤ 1
        · have hmin := min_eq_right hdle
          rw [hmin] at h0
          exact h0
        · have hmin : min 1 (Metric.infDist x A) = 1 :=
            min_eq_left (le_of_lt (not_le.mp hdle))
          rw [hmin] at h0
          norm_num at h0
      exact (Metric.mem_closure_iff_infDist_zero hA).mpr hd0
    · intro hx
      rw [Metric.infDist_zero_of_mem_closure hx]
      norm_num
  · rw [if_neg hA]
    have hempty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    simp [hempty]

lemma continuous_compatibleDistAux
    {X : Type*} [MetricSpace X] (A : Set X) :
    Continuous fun x => compatibleDistAux A x := by
  unfold compatibleDistAux
  by_cases hA : A.Nonempty
  · have hfun : (fun x => @ite ℝ A.Nonempty (Classical.dec _)
        (min 1 (Metric.infDist x A)) 1) =
        fun x => min 1 (Metric.infDist x A) := by
      funext x
      exact if_pos hA
    rw [hfun]
    exact continuous_const.min (Metric.continuous_infDist_pt A)
  · have hfun : (fun x => @ite ℝ A.Nonempty (Classical.dec _)
        (min 1 (Metric.infDist x A)) 1) = fun _ => 1 := by
      funext x
      exact if_neg hA
    rw [hfun]
    exact continuous_const

/- accepted add_to_file helper 5 -/
lemma compatibleDistAux_nonneg
    {X : Type*} [MetricSpace X] (A : Set X) (x : X) :
    0 ≤ compatibleDistAux A x := by
  unfold compatibleDistAux
  by_cases hA : A.Nonempty
  · rw [if_pos hA]
    exact le_min zero_le_one Metric.infDist_nonneg
  · rw [if_neg hA]
    norm_num

/- accepted add_to_file helper 6 -/
lemma compatible_shrinking_exists_singletons
    {X : Type*} [MetricSpace X]
    {O Z : Set X} (N : ℕ)
    (Zi : Fin N → Set X) (W : Set (Fin N) → Set X)
    (hO : IsOpen O)
    (hZO : Z ⊆ O)
    (hZclosed : IsClosed (Subtype.val ⁻¹' Z : Set O))
    (hZi_subset : ∀ i, Zi i ⊆ Z)
    (hZi_open : ∀ i, IsOpen (Subtype.val ⁻¹' Zi i : Set Z))
    (hW : ∀ K : Set (Fin N), K.Nonempty →
      IsOpen (W K) ∧ W K ⊆ O ∧ W K ∩ Z = ⋂ i ∈ K, Zi i) :
    ∃ V : Fin N → Set X,
      (∀ i, IsOpen (V i) ∧ V i ∩ Z = Zi i) ∧
      ∀ K : Set (Fin N), K.Nonempty → (⋂ i ∈ K, V i) ⊆ W K := by
  classical
  let B : Fin N → Set X := fun i => Z \ Zi i
  let A : Fin N → Set X := fun i => closure (B i)
  let D : Set (Fin N) → Set X := fun K => closure (O \ W K) ∩ (W K)ᶜ
  let d : Fin N → X → ℝ := fun i x => compatibleDistAux (B i) x
  let P : Set (Fin N) → Fin N → Set X := fun K i =>
    {x | x ∈ D K ∧ ∀ j ∈ K, d i x ≤ d j x}
  let S : Fin N → Set (Set (Fin N)) := fun i => {K | K.Nonempty ∧ i ∈ K}
  let E : Fin N → Set X := fun i => A i ∪ ⋃ K ∈ S i, P K i
  have hBsub : ∀ i, B i ⊆ O := by
    intro i x hx
    exact hZO hx.1
  have hBrel : ∀ i, IsClosed (Subtype.val ⁻¹' B i : Set O) := by
    intro i
    exact compatible_shrinking_relClosedDiff hZO hZclosed (hZi_open i)
  have hAtrace : ∀ i, A i ∩ Z = B i := by
    intro i
    have h := compatible_shrinking_closureInterOfRelClosed (hBsub i) (hBrel i)
    apply Set.Subset.antisymm
    · intro x hx
      have hxO : x ∈ O := hZO hx.2
      have hx' : x ∈ A i ∩ O := ⟨hx.1, hxO⟩
      rwa [h] at hx'
    · intro x hx
      exact ⟨subset_closure hx, hx.1⟩
  have hPclosed : ∀ K : Set (Fin N), K.Nonempty → ∀ i, IsClosed (P K i) := by
    intro K hK i
    have hDclosed : IsClosed (D K) := by
      exact isClosed_closure.inter ((hW K hK).1.isClosed_compl)
    have hineq : ∀ j ∈ K, IsClosed {x : X | d i x ≤ d j x} := by
      intro j hj
      exact isClosed_le (continuous_compatibleDistAux (B i))
        (continuous_compatibleDistAux (B j))
    have hbi : IsClosed (⋂ j ∈ K, {x : X | d i x ≤ d j x}) :=
      isClosed_biInter hineq
    have hPeq : P K i = D K ∩ ⋂ j ∈ K, {x : X | d i x ≤ d j x} := by
      ext x
      simp [P]
    rw [hPeq]
    exact hDclosed.inter hbi
  have hSfinite : ∀ i, (S i).Finite := by
    intro i
    exact Set.finite_univ.subset (Set.subset_univ _)
  have hEclosed : ∀ i, IsClosed (E i) := by
    intro i
    apply isClosed_closure.union
    exact (hSfinite i).isClosed_biUnion (by
      intro K hK
      exact hPclosed K hK.1 i)
  have hPtrace : ∀ K : Set (Fin N), K.Nonempty → ∀ i, P K i ∩ Z ⊆ A i := by
    intro K hK i x hx
    have hxP : x ∈ P K i := hx.1
    have hxZ : x ∈ Z := hx.2
    have hxnotW : x ∉ W K := hxP.1.2
    have hnotinter : x ∉ ⋂ j ∈ K, Zi j := by
      intro hxinter
      have hxmem : x ∈ W K ∩ Z := by
        rw [(hW K hK).2.2]
        exact hxinter
      exact hxnotW hxmem.1
    have hnotforall : ¬ ∀ j, j ∈ K → x ∈ Zi j := by
      intro hall
      apply hnotinter
      simpa using hall
    rcases not_forall₂.mp hnotforall with ⟨j, hjK, hxnotj⟩
    have hxBj : x ∈ B j := ⟨hxZ, hxnotj⟩
    have hdj0 : d j x = 0 := by
      exact (compatibleDistAux_zero_iff (B j) x).mpr (subset_closure hxBj)
    have hle : d i x ≤ 0 := by
      simpa [hdj0] using hxP.2 j hjK
    have hdi0 : d i x = 0 := le_antisymm hle (compatibleDistAux_nonneg (B i) x)
    exact (compatibleDistAux_zero_iff (B i) x).mp hdi0
  have hEtrace : ∀ i, E i ∩ Z = B i := by
    intro i
    apply Set.Subset.antisymm
    · intro x hx
      have hxZ : x ∈ Z := hx.2
      have hxE : x ∈ E i := hx.1
      rcases hxE with hxA | hxU
      · have : x ∈ A i ∩ Z := ⟨hxA, hxZ⟩
        rwa [hAtrace i] at this
      · rcases Set.mem_iUnion.mp hxU with ⟨K, hKmem⟩
        rcases Set.mem_iUnion.mp hKmem with ⟨hKS, hxP⟩
        have : x ∈ P K i ∩ Z := ⟨hxP, hxZ⟩
        have hxA := hPtrace K hKS.1 i this
        have : x ∈ A i ∩ Z := ⟨hxA, hxZ⟩
        rwa [hAtrace i] at this
    · intro x hx
      exact ⟨Or.inl (subset_closure hx), hx.1⟩
  have hPcover : ∀ K : Set (Fin N), K.Nonempty → D K ⊆ ⋃ i ∈ K, P K i := by
    intro K hK x hxD
    let s : Finset (Fin N) := K.toFinset
    have hs : s.Nonempty := by
      simpa [s, Set.toFinset_nonempty] using hK
    rcases Finset.exists_min_image s (fun i => d i x) hs with ⟨i, his, hmin⟩
    have hiK : i ∈ K := by simpa [s] using his
    apply Set.mem_iUnion.mpr
    exists i
    apply Set.mem_iUnion.mpr
    exists hiK
    exact ⟨hxD, by
      intro j hjK
      exact hmin j (by simpa [s] using hjK)⟩
  have hEcover : ∀ K : Set (Fin N), K.Nonempty → O \ W K ⊆ ⋃ i ∈ K, E i := by
    intro K hK x hx
    have hxD : x ∈ D K := ⟨subset_closure hx, hx.2⟩
    have hxP := hPcover K hK hxD
    rcases Set.mem_iUnion.mp hxP with ⟨i, himem⟩
    rcases Set.mem_iUnion.mp himem with ⟨hiK, hxi⟩
    apply Set.mem_iUnion.mpr
    exists i
    apply Set.mem_iUnion.mpr
    exists hiK
    exact Or.inr (Set.mem_iUnion.mpr ⟨K,
      Set.mem_iUnion.mpr ⟨⟨hK, hiK⟩, hxi⟩⟩)
  let V : Fin N → Set X := fun i => O ∩ (E i)ᶜ
  refine ⟨V, ?_, ?_⟩
  · intro i
    constructor
    · exact hO.inter (hEclosed i).isOpen_compl
    · apply Set.Subset.antisymm
      · intro x hx
        have hxZ : x ∈ Z := hx.2
        have hxnotE : x ∉ E i := hx.1.2
        have hxnotB : x ∉ B i := by
          intro hxB
          apply hxnotE
          have hxEi : x ∈ E i := Or.inl (subset_closure hxB)
          exact hxEi
        by_contra hnot
        exact hxnotB ⟨hxZ, hnot⟩
      · intro x hx
        have hxZ : x ∈ Z := hZi_subset i hx
        have hxO : x ∈ O := hZO hxZ
        have hxnotE : x ∉ E i := by
          intro hxE
          have hxEZ : x ∈ E i ∩ Z := ⟨hxE, hxZ⟩
          rw [hEtrace i] at hxEZ
          exact hxEZ.2 hx
        exact ⟨⟨hxO, hxnotE⟩, hxZ⟩
  · intro K hK x hx
    rcases hK with ⟨i₀, hi₀⟩
    have hxVi₀ : x ∈ V i₀ := Set.mem_iInter₂.mp hx i₀ hi₀
    have hxO : x ∈ O := hxVi₀.1
    by_contra hxW
    have hxdiff : x ∈ O \ W K := ⟨hxO, hxW⟩
    have hxE := hEcover K ⟨i₀, hi₀⟩ hxdiff
    rcases Set.mem_iUnion.mp hxE with ⟨i, himem⟩
    rcases Set.mem_iUnion.mp himem with ⟨hiK, hxiE⟩
    have hxVi : x ∈ V i := Set.mem_iInter₂.mp hx i hiK
    exact hxVi.2 hxiE

/- verified submission -/
theorem finite_compatible_shrinking_lemma
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    {O Z : Set X} (N : ℕ) (hN : 0 < N)
    (Zi : Fin N → Set X) (W : Set (Fin N) → Set X)
    (hO : IsOpen O) (hOcompact : IsCompact (closure O))
    (hZO : Z ⊆ O)
    (hZclosed : IsClosed (Subtype.val ⁻¹' Z : Set O))
    (hZi_subset : ∀ i, Zi i ⊆ Z)
    (hZi_open : ∀ i, IsOpen (Subtype.val ⁻¹' Zi i : Set Z))
    (hW : ∀ K : Set (Fin N), K.Nonempty →
      IsOpen (W K) ∧ W K ⊆ O ∧ W K ∩ Z = ⋂ i ∈ K, Zi i) :
    ∃ U : Set (Fin N) → Set X,
      (∀ K : Set (Fin N), K.Nonempty →
        IsOpen (U K) ∧ U K ⊆ W K ∧ U K ∩ Z = ⋂ i ∈ K, Zi i) ∧
      ∀ J K : Set (Fin N), J.Nonempty → K.Nonempty →
        U J ∩ U K = U (J ∪ K) := by
  classical
  rcases compatible_shrinking_exists_singletons N Zi W hO hZO hZclosed
      hZi_subset hZi_open hW with ⟨V, hV, hVsub⟩
  let U : Set (Fin N) → Set X := fun K => ⋂ i ∈ K, V i
  refine ⟨U, ?_, ?_⟩
  · intro K hK
    refine ⟨?_, hVsub K hK, ?_⟩
    · exact K.toFinite.isOpen_biInter (fun i hi => (hV i).1)
    · calc
        U K ∩ Z = (⋂ i ∈ K, V i) ∩ Z := rfl
        _ = ⋂ i ∈ K, (V i ∩ Z) := by
          ext x
          constructor
          · intro hx
            have hmem := Set.mem_iInter₂.mp hx.1
            apply Set.mem_iInter₂.mpr
            intro i hi
            exact ⟨hmem i hi, hx.2⟩
          · intro hx
            have hall := Set.mem_iInter₂.mp hx
            rcases hK with ⟨i₀, hi₀⟩
            constructor
            · apply Set.mem_iInter₂.mpr
              intro i hi
              exact (hall i hi).1
            · exact (hall i₀ hi₀).2
        _ = ⋂ i ∈ K, Zi i := by
          simp [fun i => (hV i).2]
  · intro J K hJ hK
    ext x
    simp [U, Set.mem_union, or_imp, forall_and]

end Rollout_p3013_finite_compatible_shrinking_lemma

#check_dependency_graph "Rollout_p3013_finite_compatible_shrinking_lemma.finite_compatible_shrinking_lemma" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∃ U, (∀ (K : Set (Fin N)), K.Nonempty → IsOpen (U K) ∧ U K ⊆ W K ∧ U K ∩ Z = ⋂ i ∈ K, Zi i) ∧ ∀ (J K : Set (Fin N)), J.Nonempty → K.Nonempty → U J ∩ U K = U (J ∪ K)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hO\",\"statement\":\"IsOpen O\"},{\"name\":\"hZO\",\"statement\":\"Z ⊆ O\"},{\"name\":\"hZclosed\",\"statement\":\"IsClosed (Subtype.val ⁻¹' Z)\"},{\"name\":\"hZi_subset\",\"statement\":\"∀ (i : Fin N), Zi i ⊆ Z\"},{\"name\":\"hZi_open\",\"statement\":\"∀ (i : Fin N), IsOpen (Subtype.val ⁻¹' Zi i)\"},{\"name\":\"hW\",\"statement\":\"∀ (K : Set (Fin N)), K.Nonempty → IsOpen (W K) ∧ W K ⊆ O ∧ W K ∩ Z = ⋂ i ∈ K, Zi i\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p3013_finite_compatible_shrinking_lemma\",\"reconstructedProofSha256\":\"5f17a7ff424ed6b8ce9c9d2327c5207d3fdb5da6c55f6e40efd1305f2b5f2569\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p3013_finite_compatible_shrinking_lemma.finite_compatible_shrinking_lemma\",\"topologySha256\":\"8b9aca9fc832e636b74f6b231361ef29e13d563e12637c3874475ffa894fc31d\"}"

namespace Rollout_p3019_laurent_circulant_kernel

-- graph_id: p3019_laurent_circulant_kernel
-- topology_sha256: 63d6015b119f90a9baba38749e4205742c89b29c8136c262b83a135dc804b604
/- accepted add_to_file helper 1 -/
lemma eq_of_forall_sub_natCast_zmod
    {m a : ℕ} [NeZero m] {α : Type*} {v : ZMod m → α}
    (hcop : Nat.Coprime a m)
    (h : ∀ i : ZMod m, v i = v (i - (a : ZMod m))) :
    ∀ i j : ZMod m, v i = v j := by
  let u : ZMod m := a
  have hu : IsUnit u := by
    dsimp [u]
    exact (ZMod.isUnit_iff_coprime a m).2 hcop
  have hiter : ∀ (c : ℕ) (i : ZMod m), v i = v (i - (c : ZMod m) * u) := by
    intro c
    induction c with
    | zero =>
        intro i
        simp
    | succ c hc =>
        intro i
        calc
          v i = v (i - (c : ZMod m) * u) := hc i
          _ = v ((i - (c : ZMod m) * u) - u) := h _
          _ = v (i - ((c + 1 : ℕ) : ZMod m) * u) := by
            congr 1
            simp [Nat.cast_add, add_mul]
            ring
  intro i j
  let c : ℕ := (((i - j) * u⁻¹).val)
  have hcast : (c : ZMod m) = (i - j) * u⁻¹ := by
    dsimp [c]
    simpa using (ZMod.natCast_val ((i - j) * u⁻¹) : (((i - j) * u⁻¹).val : ZMod m) = ((i - j) * u⁻¹).cast)
  have hcu : (c : ZMod m) * u = i - j := by
    rw [hcast]
    calc
      ((i - j) * u⁻¹) * u = (i - j) * (u⁻¹ * u) := by ring
      _ = i - j := by rw [ZMod.inv_mul_of_unit u hu]; ring
  calc
    v i = v (i - (c : ZMod m) * u) := hiter c i
    _ = v j := by
      rw [hcu]
      congr 1
      abel

/- accepted add_to_file helper 2 -/
noncomputable def laurentCirculantB
    (a b : ℕ) [NeZero (a + b)] (ε : ℤ) :
    Matrix (ZMod (a + b)) (ZMod (a + b)) (LaurentPolynomial ℤ) := fun i j =>
  if i - j = ((-(a : ℤ) : ℤ) : ZMod (a + b)) then
    LaurentPolynomial.C ε * LaurentPolynomial.T 1
  else if i - j ∈ (Finset.Ico 1 a).image
      (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a + b))) then
    1 + LaurentPolynomial.C ε * LaurentPolynomial.T 1
  else if i - j = 0 then
    1 - LaurentPolynomial.C ε * LaurentPolynomial.T 1
  else if i - j ∈ (Finset.Ico 1 a).image
      (fun k : ℕ => (k : ZMod (a + b))) then
    -1 - LaurentPolynomial.C ε * LaurentPolynomial.T 1
  else if i - j = (a : ZMod (a + b)) then
    -1
  else
    0

/- accepted add_to_file helper 3 -/
lemma sum_ite_eq_image_ite
    {ι α R : Type*} [DecidableEq ι] [DecidableEq α] [Semiring R]
    (s : Finset ι) (f : ι → α) (d : α)
    (hinj : Set.InjOn f s) :
    (∑ k ∈ s, (if d = f k then (1 : R) else 0)) =
      if d ∈ s.image f then 1 else 0 := by
  by_cases hd : d ∈ s.image f
  · rw [if_pos hd]
    rcases Finset.mem_image.mp hd with ⟨k, hk, hkd⟩
    rw [Finset.sum_eq_single_of_mem k hk]
    · rw [← hkd]
      simp
    · intro l hl hlk
      have hfl : f l ≠ d := by
        intro hfl
        apply hlk
        apply hinj hl hk
        rw [hfl, hkd]
      rw [if_neg]
      exact ne_comm.mp hfl
  · rw [if_neg hd]
    apply Finset.sum_eq_zero
    intro k hk
    have hne : d ≠ f k := by
      intro h
      exact hd (Finset.mem_image.mpr ⟨k, hk, h.symm⟩)
    rw [if_neg hne]

/- accepted add_to_file helper 4 -/
lemma zmod_natCast_injOn_Ico_one
    {m a : ℕ} [NeZero m] (ham : a < m) :
    Set.InjOn (fun k : ℕ => (k : ZMod m)) (Finset.Ico 1 a) := by
  intro k hk l hl hkl
  have hklt : k < m := lt_trans (Finset.mem_Ico.mp hk).2 ham
  have hllt : l < m := lt_trans (Finset.mem_Ico.mp hl).2 ham
  have hmod : k % m = l % m := (ZMod.natCast_eq_natCast_iff' k l m).mp hkl
  rwa [Nat.mod_eq_of_lt hklt, Nat.mod_eq_of_lt hllt] at hmod

lemma zmod_int_sub_natCast_injOn_Ico_one
    {m a : ℕ} [NeZero m] (ham : a < m) :
    Set.InjOn
      (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod m))
      (Finset.Ico 1 a) := by
  intro k hk l hl hkl
  have hcast : (k : ZMod m) = (l : ZMod m) := by
    have h := congrArg (fun z : ZMod m => z + (a : ZMod m)) hkl
    simpa using h
  exact zmod_natCast_injOn_Ico_one ham hk hl hcast

/- accepted add_to_file helper 5 -/
lemma zmod_intCast_ne_of_abs_sub_lt {m : ℕ} [NeZero m] {x y : ℤ}
    (hdiff : |x - y| < (m : ℤ)) (hxy : x ≠ y) :
    (x : ZMod m) ≠ (y : ZMod m) := by
  intro h
  have hmod : x ≡ y [ZMOD (m : ℤ)] :=
    (ZMod.intCast_eq_intCast_iff x y m).mp h
  have hdvd : (m : ℤ) ∣ y - x := Int.modEq_iff_dvd.mp hmod
  have hzero : y - x = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd hdvd
    rw [abs_sub_comm]
    exact hdiff
  exact hxy (by omega)

/- accepted add_to_file helper 6 -/
lemma zmod_neg_a_not_mem_shift_image
    (a b : ℕ) [NeZero (a+b)] :
    (((-(a : ℤ) : ℤ) : ZMod (a+b)) ∉
      (Finset.Ico 1 a).image (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))) := by
  intro h
  rcases Finset.mem_image.mp h with ⟨k,hk,hka⟩
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have hk2 : k < a := (Finset.mem_Ico.mp hk).2
  have hne := zmod_intCast_ne_of_abs_sub_lt (m:=a+b)
    (x:=-(a:ℤ)) (y:=(k:ℤ)-(a:ℤ)) ?_ ?_
  · exact hne hka.symm
  · have hrewrite : (-(a : ℤ) : ℤ) - ((k : ℤ) - (a : ℤ)) = -(k : ℤ) := by ring
    rw [hrewrite, abs_neg]
    norm_num
    omega
  · omega

lemma zmod_neg_a_ne_zero (a b : ℕ) [NeZero (a+b)] (ha : 0 < a) (hab : a < b) :
    (((-(a : ℤ) : ℤ) : ZMod (a+b)) ≠ 0) := by
  have hneInt : (((-(a : ℤ) : ℤ) : ZMod (a+b)) ≠ ((0 : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b) (x:=-(a:ℤ)) (y:=0)
    · rw [sub_zero, abs_neg]
      norm_num
      omega
    · omega
  simpa using hneInt

lemma zmod_neg_a_not_mem_nat_image
    (a b : ℕ) [NeZero (a+b)] (hab : a < b) :
    (((-(a : ℤ) : ℤ) : ZMod (a+b)) ∉
      (Finset.Ico 1 a).image (fun k : ℕ => (k : ZMod (a+b)))) := by
  intro h
  rcases Finset.mem_image.mp h with ⟨k,hk,hka⟩
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have hk2 : k < a := (Finset.mem_Ico.mp hk).2
  have hneInt : (((-(a : ℤ) : ℤ) : ZMod (a+b)) ≠ (((k : ℤ) : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b) (x:=-(a:ℤ)) (y:=(k:ℤ))
    · have hrewrite : (-(a : ℤ) : ℤ) - (k : ℤ) = -(((a + k : ℕ) : ℤ)) := by
        norm_num
        ring
      rw [hrewrite, abs_neg]
      have hnonneg : 0 ≤ (((a + k : ℕ) : ℤ)) := by positivity
      rw [abs_of_nonneg hnonneg]
      have hlt : a + k < a + b := by omega
      exact_mod_cast hlt
    · omega
  have hne : (((-(a : ℤ) : ℤ) : ZMod (a+b)) ≠ (k : ZMod (a+b))) := by
    simpa using hneInt
  exact hne hka.symm

lemma zmod_neg_a_ne_a (a b : ℕ) [NeZero (a+b)] (ha : 0 < a) (hab : a < b) :
    (((-(a : ℤ) : ℤ) : ZMod (a+b)) ≠ (a : ZMod (a+b))) := by
  have hneInt : (((-(a : ℤ) : ℤ) : ZMod (a+b)) ≠ (((a : ℤ) : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b) (x:=-(a:ℤ)) (y:=(a:ℤ))
    · have hrewrite : (-(a : ℤ) : ℤ) - (a : ℤ) = -(((2 * a : ℕ) : ℤ)) := by
        norm_num
        ring
      rw [hrewrite, abs_neg]
      have hnonneg : 0 ≤ (((2 * a : ℕ) : ℤ)) := by positivity
      rw [abs_of_nonneg hnonneg]
      have hlt : 2 * a < a + b := by omega
      exact_mod_cast hlt
    · omega
  simpa using hneInt

/- accepted add_to_file helper 7 -/
lemma zmod_shift_image_ne_zero
    (a b : ℕ) [NeZero (a+b)] {d : ZMod (a+b)}
    (hd : d ∈ (Finset.Ico 1 a).image
      (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))) :
    d ≠ 0 := by
  rcases Finset.mem_image.mp hd with ⟨k,hk,rfl⟩
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have hk2 : k < a := (Finset.mem_Ico.mp hk).2
  have hneInt : ((((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)) ≠ ((0 : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b)
      (x:=(k:ℤ)-(a:ℤ)) (y:=0)
    · rw [sub_zero]
      have hrewrite : (k : ℤ) - (a : ℤ) = -(((a - k : ℕ) : ℤ)) := by
        omega
      rw [hrewrite, abs_neg]
      have hnonneg : 0 ≤ (((a - k : ℕ) : ℤ)) := by positivity
      rw [abs_of_nonneg hnonneg]
      have hknat : a - k < a + b := by omega
      exact_mod_cast hknat
    · omega
  simpa using hneInt

lemma zmod_shift_image_disjoint_nat_image
    (a b : ℕ) [NeZero (a+b)] (hab : a < b) {d : ZMod (a+b)}
    (hd : d ∈ (Finset.Ico 1 a).image
      (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))) :
    d ∉ (Finset.Ico 1 a).image (fun k : ℕ => (k : ZMod (a+b))) := by
  rcases Finset.mem_image.mp hd with ⟨k,hk,rfl⟩
  intro hP
  rcases Finset.mem_image.mp hP with ⟨l,hl,hkl⟩
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have hk2 : k < a := (Finset.mem_Ico.mp hk).2
  have hl1 : 1 ≤ l := (Finset.mem_Ico.mp hl).1
  have hl2 : l < a := (Finset.mem_Ico.mp hl).2
  have hneInt : ((((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)) ≠ (((l : ℤ) : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b)
      (x:=(k:ℤ)-(a:ℤ)) (y:=(l:ℤ))
    · have hrewrite : ((k : ℤ) - (a : ℤ)) - (l : ℤ) =
          -((((a + l) - k : ℕ) : ℤ)) := by
        omega
      rw [hrewrite, abs_neg]
      have hnonneg : 0 ≤ ((((a + l) - k : ℕ) : ℤ)) := by positivity
      rw [abs_of_nonneg hnonneg]
      have hlt : (a + l) - k < a + b := by omega
      exact_mod_cast hlt
    · omega
  have hne : ((((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)) ≠ (l : ZMod (a+b))) := by
    simpa using hneInt
  exact hne hkl.symm

lemma zmod_shift_image_ne_a
    (a b : ℕ) [NeZero (a+b)] (hab : a < b) {d : ZMod (a+b)}
    (hd : d ∈ (Finset.Ico 1 a).image
      (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))) :
    d ≠ (a : ZMod (a+b)) := by
  rcases Finset.mem_image.mp hd with ⟨k,hk,rfl⟩
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have hk2 : k < a := (Finset.mem_Ico.mp hk).2
  have hneInt : ((((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)) ≠ (((a : ℤ) : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b)
      (x:=(k:ℤ)-(a:ℤ)) (y:=(a:ℤ))
    · have hrewrite : ((k : ℤ) - (a : ℤ)) - (a : ℤ) =
          -(((2 * a - k : ℕ) : ℤ)) := by
        omega
      rw [hrewrite, abs_neg]
      have hnonneg : 0 ≤ (((2 * a - k : ℕ) : ℤ)) := by positivity
      rw [abs_of_nonneg hnonneg]
      have hlt : 2 * a - k < a + b := by omega
      exact_mod_cast hlt
    · omega
  simpa using hneInt

/- accepted add_to_file helper 8 -/
lemma zmod_zero_not_mem_nat_image
    (a b : ℕ) [NeZero (a+b)] :
    (0 : ZMod (a+b)) ∉
      (Finset.Ico 1 a).image (fun k : ℕ => (k : ZMod (a+b))) := by
  intro h
  rcases Finset.mem_image.mp h with ⟨k,hk,hka⟩
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have hk2 : k < a := (Finset.mem_Ico.mp hk).2
  have hneInt : (((0 : ℤ) : ZMod (a+b)) ≠ (((k : ℤ) : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b)
      (x:=0) (y:=(k:ℤ))
    · rw [zero_sub, abs_neg]
      norm_num
      omega
    · omega
  have hne : (0 : ZMod (a+b)) ≠ (k : ZMod (a+b)) := by
    simpa using hneInt
  exact hne hka.symm

lemma zmod_zero_ne_a (a b : ℕ) [NeZero (a+b)] (ha : 0 < a) (hab : a < b) :
    (0 : ZMod (a+b)) ≠ (a : ZMod (a+b)) := by
  have hneInt : (((0 : ℤ) : ZMod (a+b)) ≠ (((a : ℤ) : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b) (x:=0) (y:=(a:ℤ))
    · rw [zero_sub, abs_neg]
      norm_num
      omega
    · omega
  simpa using hneInt

lemma zmod_nat_image_ne_a
    (a b : ℕ) [NeZero (a+b)] {d : ZMod (a+b)}
    (hd : d ∈ (Finset.Ico 1 a).image (fun k : ℕ => (k : ZMod (a+b)))) :
    d ≠ (a : ZMod (a+b)) := by
  rcases Finset.mem_image.mp hd with ⟨k,hk,rfl⟩
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have hk2 : k < a := (Finset.mem_Ico.mp hk).2
  have hneInt : ((((k : ℤ) : ℤ) : ZMod (a+b)) ≠ (((a : ℤ) : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b)
      (x:=(k:ℤ)) (y:=(a:ℤ))
    · have hrewrite : (k : ℤ) - (a : ℤ) = -(((a - k : ℕ) : ℤ)) := by
        omega
      rw [hrewrite, abs_neg]
      have hnonneg : 0 ≤ (((a - k : ℕ) : ℤ)) := by positivity
      rw [abs_of_nonneg hnonneg]
      have hlt : a - k < a + b := by omega
      exact_mod_cast hlt
    · omega
  have hne : ((k : ZMod (a+b)) ≠ (a : ZMod (a+b))) := by
    simpa using hneInt
  exact hne

/- accepted add_to_file helper 9 -/
lemma zmod_a_not_mem_shift_image
    (a b : ℕ) [NeZero (a+b)] (hab : a < b) :
    (a : ZMod (a+b)) ∉
      (Finset.Ico 1 a).image
        (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b))) := by
  intro h
  exact zmod_shift_image_ne_a a b hab h rfl

lemma zmod_a_not_mem_nat_image
    (a b : ℕ) [NeZero (a+b)] :
    (a : ZMod (a+b)) ∉
      (Finset.Ico 1 a).image (fun k : ℕ => (k : ZMod (a+b))) := by
  intro h
  exact zmod_nat_image_ne_a a b h rfl

/- accepted add_to_file helper 10 -/
lemma zmod_zero_not_mem_shift_image
    (a b : ℕ) [NeZero (a+b)] :
    (0 : ZMod (a+b)) ∉
      (Finset.Ico 1 a).image
        (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b))) := by
  intro h
  exact zmod_shift_image_ne_zero a b h rfl

/- accepted add_to_file helper 11 -/
lemma laurentCirculantB_eq_sum
    (a b : ℕ) [NeZero (a + b)] (ha : 0 < a) (hab : a < b) (ε : ℤ) :
    let t : LaurentPolynomial ℤ := LaurentPolynomial.C ε * LaurentPolynomial.T 1
    let D : ZMod (a+b) → Matrix (ZMod (a+b)) (ZMod (a+b)) (LaurentPolynomial ℤ) :=
      fun c i j => if i - j = c then 1 else 0
    laurentCirculantB a b ε =
      t • D (((-(a : ℤ) : ℤ) : ZMod (a+b))) +
      (1 + t) • (∑ k ∈ Finset.Ico 1 a, D (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b))) +
      (1 - t) • D 0 +
      (-1 - t) • (∑ k ∈ Finset.Ico 1 a, D (k : ZMod (a+b))) +
      (-1) • D (a : ZMod (a+b)) := by
  intro t D
  apply Matrix.ext
  intro i j
  have ham : a < a + b := Nat.lt_add_of_pos_right (Nat.lt_trans ha hab)
  simp only [laurentCirculantB, D, Matrix.add_apply, Matrix.smul_apply]
  rw [Matrix.sum_apply i j (Finset.Ico 1 a)
    (fun x => (fun i j => if i - j = (((x : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)) then (1:LaurentPolynomial ℤ) else 0))]
  rw [Matrix.sum_apply i j (Finset.Ico 1 a)
    (fun x => (fun i j => if i - j = (x : ZMod (a+b)) then (1:LaurentPolynomial ℤ) else 0))]
  rw [sum_ite_eq_image_ite (Finset.Ico 1 a)
    (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b))) (i-j)
    (zmod_int_sub_natCast_injOn_Ico_one ham)]
  rw [sum_ite_eq_image_ite (Finset.Ico 1 a)
    (fun k : ℕ => (k : ZMod (a+b))) (i-j)
    (zmod_natCast_injOn_Ico_one ham)]
  by_cases hA : i - j = (((-(a : ℤ) : ℤ) : ZMod (a+b)))
  · have hN := zmod_neg_a_not_mem_shift_image a b
    have hZ := zmod_neg_a_ne_zero a b ha hab
    have hP := zmod_neg_a_not_mem_nat_image a b hab
    have hAp := zmod_neg_a_ne_a a b ha hab
    simp only [hA, hN, hZ, hP, hAp, if_true, if_false, smul_eq_mul, mul_one, mul_zero,
      add_zero, zero_add, neg_mul, one_mul]
    ring
  · by_cases hN : i - j ∈ (Finset.Ico 1 a).image
        (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))
    · have hZ : i - j ≠ 0 := zmod_shift_image_ne_zero a b hN
      have hP : i - j ∉ (Finset.Ico 1 a).image (fun k : ℕ => (k : ZMod (a+b))) :=
        zmod_shift_image_disjoint_nat_image a b hab hN
      have hAp : i - j ≠ (a : ZMod (a+b)) := zmod_shift_image_ne_a a b hab hN
      simp only [hA, hN, hZ, hP, hAp, if_true, if_false, smul_eq_mul, mul_one, mul_zero,
        add_zero, zero_add, neg_mul, one_mul]
      ring
    · by_cases hZ : i - j = 0
      · have hA0 : (0 : ZMod (a+b)) ≠ (((-(a : ℤ) : ℤ) : ZMod (a+b))) :=
          (zmod_neg_a_ne_zero a b ha hab).symm
        have hN0 := zmod_zero_not_mem_shift_image a b
        have hP0 := zmod_zero_not_mem_nat_image a b
        have hAp0 := zmod_zero_ne_a a b ha hab
        simp only [hZ, hA0, hN0, hP0, hAp0, if_true, if_false, smul_eq_mul, mul_one, mul_zero,
          add_zero, zero_add, neg_mul, one_mul]
        ring
      · by_cases hP : i - j ∈ (Finset.Ico 1 a).image (fun k : ℕ => (k : ZMod (a+b)))
        · have hAp : i - j ≠ (a : ZMod (a+b)) := zmod_nat_image_ne_a a b hP
          simp only [hA, hN, hZ, hP, hAp, if_true, if_false, smul_eq_mul, mul_one, mul_zero,
            add_zero, zero_add, neg_mul, one_mul]
          ring
        · by_cases hAp : i - j = (a : ZMod (a+b))
          · have hA' : (a : ZMod (a+b)) ≠ (((-(a : ℤ) : ℤ) : ZMod (a+b))) :=
              (zmod_neg_a_ne_a a b ha hab).symm
            have hN' := zmod_a_not_mem_shift_image a b hab
            have hZ' := (zmod_zero_ne_a a b ha hab).symm
            have hP' := zmod_a_not_mem_nat_image a b
            simp only [hAp, hA', hN', hZ', hP', if_true, if_false, smul_eq_mul, mul_one, mul_zero,
              add_zero, zero_add, neg_mul, one_mul]
            ring
          · simp only [hA, hN, hZ, hP, hAp, if_true, if_false, smul_eq_mul, mul_one, mul_zero,
              add_zero, zero_add, neg_mul, one_mul]
            ring

/- accepted add_to_file helper 12 -/
lemma zmod_diag_mulVec {m : ℕ} [NeZero m] {R : Type*} [Ring R]
    (c : ZMod m) (v : ZMod m → R) (i : ZMod m) :
    Matrix.mulVec ((fun i j : ZMod m => if i - j = c then (1 : R) else 0) :
      Matrix (ZMod m) (ZMod m) R) v i =
      v (i - c) := by
  rw [Matrix.mulVec]
  simp [dotProduct]
  rw [Finset.sum_eq_single (i - c)]
  · simp
  · intro x _ hx
    have hne : i - x ≠ c := by
      intro h
      apply hx
      rw [← h]
      abel
    simp [hne]
  · simp

/- accepted add_to_file helper 13 -/
lemma zmod_shift_interval_sum
    (a b : ℕ) [NeZero (a+b)] (ha : 0 < a)
    (v : ZMod (a+b) → LaurentPolynomial ℤ) (r : ZMod (a+b)) :
    (∑ k ∈ Finset.Ico 1 a,
      v (r - (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))) =
    ∑ j ∈ Finset.range (a-1), v (r + ((j + 1 : ℕ) : ZMod (a+b))) := by
  let m := a - 1
  let g : ℕ → LaurentPolynomial ℤ := fun z => v (r + ((z + 1 : ℕ) : ZMod (a+b)))
  have hpoint :
      (∑ k ∈ Finset.Ico 1 a,
        v (r - (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))) =
      ∑ j ∈ Finset.range m, g (m - 1 - j) := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < a - 1 := Finset.mem_range.mp hj
    dsimp [g, m] at hj ⊢
    have hnat : a - 1 - 1 - j + 1 = a - 1 - j := by omega
    rw [hnat]
    congr 1
    rw [Nat.cast_sub (by omega : j ≤ a - 1)]
    rw [Nat.cast_sub (by omega : 1 ≤ a)]
    push_cast
    abel
  rw [hpoint]
  simpa [g, m] using (Finset.sum_range_reflect g m)

/- accepted add_to_file helper 14 -/
lemma zmod_window_pos_sum
    (a b : ℕ) [NeZero (a+b)]
    (v : ZMod (a+b) → LaurentPolynomial ℤ) (r : ZMod (a+b)) :
    (∑ k ∈ Finset.Ico 1 (a+1),
      v ((r + (a : ZMod (a+b))) - (k : ZMod (a+b)))) =
    ∑ j ∈ Finset.range a, v (r + (j : ZMod (a+b))) := by
  let g : ℕ → LaurentPolynomial ℤ := fun z => v (r + (z : ZMod (a+b)))
  have hpoint :
      (∑ k ∈ Finset.Ico 1 (a+1),
        v ((r + (a : ZMod (a+b))) - (k : ZMod (a+b)))) =
      ∑ j ∈ Finset.range a, g (a - 1 - j) := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < a := Finset.mem_range.mp hj
    dsimp [g]
    congr 1
    rw [Nat.cast_sub (by omega : j ≤ a - 1)]
    rw [Nat.cast_sub (by omega : 1 ≤ a)]
    push_cast
    abel
  rw [hpoint]
  simpa [g] using (Finset.sum_range_reflect g a)

/- accepted add_to_file helper 15 -/
lemma zmod_window_pos_succ_sum
    (a b : ℕ) [NeZero (a+b)]
    (v : ZMod (a+b) → LaurentPolynomial ℤ) (r : ZMod (a+b)) :
    (∑ k ∈ Finset.Ico 1 (a+1),
      v ((r + (a : ZMod (a+b)) + 1) - (k : ZMod (a+b)))) =
    ∑ j ∈ Finset.range a, v (r + ((j + 1 : ℕ) : ZMod (a+b))) := by
  let g : ℕ → LaurentPolynomial ℤ := fun z => v (r + ((z + 1 : ℕ) : ZMod (a+b)))
  have hpoint :
      (∑ k ∈ Finset.Ico 1 (a+1),
        v ((r + (a : ZMod (a+b)) + 1) - (k : ZMod (a+b)))) =
      ∑ j ∈ Finset.range a, g (a - 1 - j) := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < a := Finset.mem_range.mp hj
    dsimp [g]
    have hnat : a - 1 - j + 1 = a - j := by omega
    rw [hnat]
    congr 1
    rw [Nat.cast_sub (by omega : j ≤ a)]
    push_cast
    abel
  rw [hpoint]
  simpa [g] using (Finset.sum_range_reflect g a)

/- accepted add_to_file helper 16 -/
lemma zmod_window_neg_sum
    (a b : ℕ) [NeZero (a+b)]
    (v : ZMod (a+b) → LaurentPolynomial ℤ) (r : ZMod (a+b)) :
    (∑ k ∈ Finset.Ico 1 (a+1), v (r - (k : ZMod (a+b)))) =
      ∑ j ∈ Finset.range a, v (r - ((j + 1 : ℕ) : ZMod (a+b))) := by
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  norm_num [Nat.add_comm]

/- accepted add_to_file helper 17 -/
lemma zmod_window_neg_succ_sum
    (a b : ℕ) [NeZero (a+b)]
    (v : ZMod (a+b) → LaurentPolynomial ℤ) (r : ZMod (a+b)) :
    (∑ k ∈ Finset.Ico 1 (a+1), v ((r + 1) - (k : ZMod (a+b)))) =
      ∑ j ∈ Finset.range a, v (r - (j : ZMod (a+b))) := by
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  push_cast
  abel

/- accepted add_to_file helper 18 -/
lemma laurentCirculantB_mulVec_factor
    (a b : ℕ) [NeZero (a + b)] (ha : 0 < a) (hab : a < b) (ε : ℤ)
    (v : ZMod (a+b) → LaurentPolynomial ℤ) (r : ZMod (a+b)) :
    let t : LaurentPolynomial ℤ := LaurentPolynomial.C ε * LaurentPolynomial.T 1
    let w : ZMod (a+b) → LaurentPolynomial ℤ := fun x =>
      ∑ k ∈ Finset.Ico 1 (a+1), v (x - (k : ZMod (a+b)))
    (laurentCirculantB a b ε).mulVec v r =
      (w (r + (a : ZMod (a+b))) - w r) +
        t * (w (r + (a : ZMod (a+b)) + 1) - w (r + 1)) := by
  intro t w
  have hdirect :
      (laurentCirculantB a b ε).mulVec v r =
      t * v (r - (((-(a : ℤ) : ℤ) : ZMod (a+b)))) +
      (1 + t) * (∑ k ∈ Finset.Ico 1 a,
        v (r - (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))) +
      (1 - t) * v r +
      (-1 - t) * (∑ k ∈ Finset.Ico 1 a,
        v (r - (k : ZMod (a+b)))) +
      (-1) * v (r - (a : ZMod (a+b))) := by
    let D : ZMod (a+b) → Matrix (ZMod (a+b)) (ZMod (a+b)) (LaurentPolynomial ℤ) :=
      fun c i j => if i - j = c then 1 else 0
    have hB := laurentCirculantB_eq_sum a b ha hab ε
    rw [show laurentCirculantB a b ε =
        t • D (((-(a : ℤ) : ℤ) : ZMod (a+b))) +
        (1 + t) • (∑ k ∈ Finset.Ico 1 a, D (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b))) +
        (1 - t) • D 0 +
        (-1 - t) • (∑ k ∈ Finset.Ico 1 a, D (k : ZMod (a+b))) +
        (-1) • D (a : ZMod (a+b)) from hB]
    simp [D, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sum_mulVec, zmod_diag_mulVec]
    rw [Matrix.neg_mulVec]
    change - Matrix.mulVec ((fun i j : ZMod (a+b) => if i - j = (a : ZMod (a+b)) then (1 : LaurentPolynomial ℤ) else 0) :
        Matrix (ZMod (a+b)) (ZMod (a+b)) (LaurentPolynomial ℤ)) v r = -v (r - (a : ZMod (a+b)))
    rw [zmod_diag_mulVec]
  have hNmid :
      (∑ k ∈ Finset.Ico 1 a,
        v (r - (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))) =
      ∑ j ∈ Finset.range (a-1), v (r + ((j + 1 : ℕ) : ZMod (a+b))) :=
    zmod_shift_interval_sum a b ha v r
  have hPmid :
      (∑ k ∈ Finset.Ico 1 a, v (r - (k : ZMod (a+b)))) =
      ∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b))) := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    norm_num [Nat.add_comm]
  have hS0 :
      (∑ j ∈ Finset.range a, v (r + (j : ZMod (a+b)))) =
      (∑ j ∈ Finset.range (a-1), v (r + ((j + 1 : ℕ) : ZMod (a+b)))) + v r := by
    have ha1 : a = (a - 1) + 1 := by omega
    have hrange : Finset.range a = Finset.range ((a - 1) + 1) := congrArg Finset.range ha1
    calc
      (∑ j ∈ Finset.range a, v (r + (j : ZMod (a+b))))
          = ∑ j ∈ Finset.range ((a - 1) + 1), v (r + (j : ZMod (a+b))) := by rw [hrange]
      _ = (∑ j ∈ Finset.range (a-1), v (r + ((j + 1 : ℕ) : ZMod (a+b)))) + v r := by
          rw [Finset.sum_range_succ']
          simp
  have hS1 :
      (∑ j ∈ Finset.range a, v (r + ((j + 1 : ℕ) : ZMod (a+b)))) =
      (∑ j ∈ Finset.range (a-1), v (r + ((j + 1 : ℕ) : ZMod (a+b)))) +
        v (r + (a : ZMod (a+b))) := by
    have ha1 : a = (a - 1) + 1 := by omega
    have hrange : Finset.range a = Finset.range ((a - 1) + 1) := congrArg Finset.range ha1
    calc
      (∑ j ∈ Finset.range a, v (r + ((j + 1 : ℕ) : ZMod (a+b))))
          = ∑ j ∈ Finset.range ((a - 1) + 1), v (r + ((j + 1 : ℕ) : ZMod (a+b))) := by rw [hrange]
      _ = (∑ j ∈ Finset.range (a-1), v (r + ((j + 1 : ℕ) : ZMod (a+b)))) +
            v (r + (a : ZMod (a+b))) := by
          rw [Finset.sum_range_succ]
          congr 1
          congr 1
          have hnat : a - 1 + 1 = a := by omega
          exact congrArg (fun z : ZMod (a+b) => r + z)
            (congrArg (fun n : ℕ => (n : ZMod (a+b))) hnat)
  have hT0 :
      (∑ j ∈ Finset.range a, v (r - ((j + 1 : ℕ) : ZMod (a+b)))) =
      (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) +
        v (r - (a : ZMod (a+b))) := by
    have ha1 : a = (a - 1) + 1 := by omega
    have hrange : Finset.range a = Finset.range ((a - 1) + 1) := congrArg Finset.range ha1
    calc
      (∑ j ∈ Finset.range a, v (r - ((j + 1 : ℕ) : ZMod (a+b))))
          = ∑ j ∈ Finset.range ((a - 1) + 1), v (r - ((j + 1 : ℕ) : ZMod (a+b))) := by rw [hrange]
      _ = (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) +
            v (r - (a : ZMod (a+b))) := by
          rw [Finset.sum_range_succ]
          congr 1
          congr 1
          have hnat : a - 1 + 1 = a := by omega
          exact congrArg (fun z : ZMod (a+b) => r - z)
            (congrArg (fun n : ℕ => (n : ZMod (a+b))) hnat)
  have hT1 :
      (∑ j ∈ Finset.range a, v (r - (j : ZMod (a+b)))) =
      v r + (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) := by
    have ha1 : a = (a - 1) + 1 := by omega
    have hrange : Finset.range a = Finset.range ((a - 1) + 1) := congrArg Finset.range ha1
    calc
      (∑ j ∈ Finset.range a, v (r - (j : ZMod (a+b))))
          = ∑ j ∈ Finset.range ((a - 1) + 1), v (r - (j : ZMod (a+b))) := by rw [hrange]
      _ = (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) + v r := by
          rw [Finset.sum_range_succ']
          simp
      _ = v r + (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) := by
          rw [add_comm]
  calc
    (laurentCirculantB a b ε).mulVec v r = _ := hdirect
    _ = (w (r + (a : ZMod (a+b))) - w r) +
        t * (w (r + (a : ZMod (a+b)) + 1) - w (r + 1)) := by
      dsimp [w]
      rw [zmod_window_pos_sum, zmod_window_neg_sum,
        zmod_window_pos_succ_sum, zmod_window_neg_succ_sum]
      rw [hS0, hS1, hT0, hT1, hNmid, hPmid]
      have hend : r - (((-(a : ℤ) : ℤ) : ZMod (a+b))) = r + (a : ZMod (a+b)) := by
        push_cast
        ring
      rw [hend]
      ring

/- accepted add_to_file helper 19 -/
lemma zmod_recur_eq_zero
    {m : ℕ} [NeZero m] {R : Type*} [CommRing R] [IsDomain R]
    {t : R} {x : ZMod m → R}
    (h : ∀ r : ZMod m, x r + t * x (r + 1) = 0)
    (ht : t ^ m ≠ (-1 : R) ^ m) :
    ∀ r : ZMod m, x r = 0 := by
  have hiter : ∀ (c : ℕ) (r : ZMod m),
      t ^ c * x (r + (c : ZMod m)) = (-1 : R) ^ c * x r := by
    intro c
    induction c with
    | zero =>
        intro r
        simp
    | succ c hc =>
        intro r
        have hstep : t * x ((r + (c : ZMod m)) + 1) = - x (r + (c : ZMod m)) :=
          eq_neg_of_add_eq_zero_right (h (r + (c : ZMod m)))
        have hindex : r + (((c + 1 : ℕ) : ZMod m)) = (r + (c : ZMod m)) + 1 := by
          simp [Nat.cast_add]
          ring
        calc
          t ^ (c + 1) * x (r + (((c + 1 : ℕ) : ZMod m)))
              = (t ^ c * t) * x ((r + (c : ZMod m)) + 1) := by
                rw [pow_succ, hindex]
          _ = t ^ c * (t * x ((r + (c : ZMod m)) + 1)) := by rw [mul_assoc]
          _ = t ^ c * (- x (r + (c : ZMod m))) := by rw [hstep]
          _ = - (t ^ c * x (r + (c : ZMod m))) := by ring
          _ = - ((-1 : R) ^ c * x r) := by rw [hc r]
          _ = (-1 : R) ^ (c + 1) * x r := by
                rw [pow_succ]
                ring
  intro r
  have hm := hiter m r
  have hcast : ((m : ZMod m) = 0) := by simp
  rw [hcast, add_zero] at hm
  have hprod : (t ^ m - (-1 : R) ^ m) * x r = 0 := by
    rw [sub_mul]
    rw [hm]
    ring
  have hcoeff : t ^ m - (-1 : R) ^ m ≠ 0 := sub_ne_zero.mpr ht
  exact (mul_eq_zero.mp hprod).resolve_left hcoeff

/- accepted add_to_file helper 20 -/
lemma laurent_neg_one_t_pow_ne
    (m n : ℕ) [NeZero m] :
    let t : LaurentPolynomial ℤ := LaurentPolynomial.C ((-1 : ℤ) ^ n) * LaurentPolynomial.T 1
    t ^ m ≠ (-1 : LaurentPolynomial ℤ) ^ m := by
  intro t
  have hε : ((-1 : ℤ) ^ n) ≠ 0 := by norm_num
  have hpow : t ^ m =
      LaurentPolynomial.C (((-1 : ℤ) ^ n) ^ m) * LaurentPolynomial.T (m : ℤ) := by
    dsimp [t]
    rw [mul_pow, map_pow, LaurentPolynomial.T_pow]
    simp
  have hdeg1 : (t ^ m).degree = (m : ℤ) := by
    rw [hpow]
    exact LaurentPolynomial.degree_C_mul_T (m : ℤ) (((-1 : ℤ) ^ n) ^ m)
      (pow_ne_zero m hε)
  have hconst : (-1 : LaurentPolynomial ℤ) ^ m =
      LaurentPolynomial.C (((-1 : ℤ) ^ m)) := by
    simp
  have hdeg2 : ((-1 : LaurentPolynomial ℤ) ^ m).degree = 0 := by
    rw [hconst]
    exact LaurentPolynomial.degree_C (pow_ne_zero m (by norm_num : (-1 : ℤ) ≠ 0))
  intro ht
  have hmdeg : (m : ℤ) = (0 : WithBot ℤ) := by
    calc
      (m : ℤ) = (t ^ m).degree := hdeg1.symm
      _ = ((-1 : LaurentPolynomial ℤ) ^ m).degree := congrArg LaurentPolynomial.degree ht
      _ = 0 := hdeg2
  have hmpos : (0 : WithBot ℤ) < (m : ℤ) := by
    have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    exact_mod_cast hm
  rw [hmdeg] at hmpos
  exact (lt_irrefl (0 : WithBot ℤ)) hmpos

/- accepted add_to_file helper 21 -/
lemma zmod_window_succ_sub
    (a b : ℕ) [NeZero (a+b)] (ha : 0 < a)
    (v : ZMod (a+b) → LaurentPolynomial ℤ) (r : ZMod (a+b)) :
    (∑ k ∈ Finset.Ico 1 (a+1), v ((r + 1) - (k : ZMod (a+b)))) -
      (∑ k ∈ Finset.Ico 1 (a+1), v (r - (k : ZMod (a+b)))) =
    v r - v (r - (a : ZMod (a+b))) := by
  rw [zmod_window_neg_succ_sum, zmod_window_neg_sum]
  have hT0 :
      (∑ j ∈ Finset.range a, v (r - ((j + 1 : ℕ) : ZMod (a+b)))) =
      (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) +
        v (r - (a : ZMod (a+b))) := by
    have ha1 : a = (a - 1) + 1 := by omega
    have hrange : Finset.range a = Finset.range ((a - 1) + 1) := congrArg Finset.range ha1
    calc
      (∑ j ∈ Finset.range a, v (r - ((j + 1 : ℕ) : ZMod (a+b))))
          = ∑ j ∈ Finset.range ((a - 1) + 1), v (r - ((j + 1 : ℕ) : ZMod (a+b))) := by rw [hrange]
      _ = (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) +
            v (r - (a : ZMod (a+b))) := by
          rw [Finset.sum_range_succ]
          congr 1
          congr 1
          have hnat : a - 1 + 1 = a := by omega
          exact congrArg (fun z : ZMod (a+b) => r - z)
            (congrArg (fun n : ℕ => (n : ZMod (a+b))) hnat)
  have hT1 :
      (∑ j ∈ Finset.range a, v (r - (j : ZMod (a+b)))) =
      v r + (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) := by
    have ha1 : a = (a - 1) + 1 := by omega
    have hrange : Finset.range a = Finset.range ((a - 1) + 1) := congrArg Finset.range ha1
    calc
      (∑ j ∈ Finset.range a, v (r - (j : ZMod (a+b))))
          = ∑ j ∈ Finset.range ((a - 1) + 1), v (r - (j : ZMod (a+b))) := by rw [hrange]
      _ = (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) + v r := by
          rw [Finset.sum_range_succ']
          simp
      _ = v r + (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) := by
          rw [add_comm]
  rw [hT0, hT1]
  ring

/- verified submission -/
theorem laurent_circulant_kernel
    (a b n : ℕ) (ha : 0 < a) (hab : a < b) (hab_coprime : Nat.Coprime a b)
    (hn : 3 ≤ n) :
    let _ : NeZero (a + b) := ⟨Nat.ne_of_gt (Nat.add_pos_left ha b)⟩
    let R := LaurentPolynomial ℤ
    let ε : ℤ := (-1) ^ n
    let q : R := LaurentPolynomial.T 1
    let B : Matrix (ZMod (a + b)) (ZMod (a + b)) R := fun i j =>
      if i - j = ((-(a : ℤ) : ℤ) : ZMod (a + b)) then
        LaurentPolynomial.C ε * q
      else if i - j ∈ (Finset.Ico 1 a).image
          (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a + b))) then
        1 + LaurentPolynomial.C ε * q
      else if i - j = 0 then
        1 - LaurentPolynomial.C ε * q
      else if i - j ∈ (Finset.Ico 1 a).image
          (fun k : ℕ => (k : ZMod (a + b))) then
        -1 - LaurentPolynomial.C ε * q
      else if i - j = (a : ZMod (a + b)) then
        -1
      else
        0
    ∀ v : ZMod (a + b) → R, B.mulVec v = 0 → ∀ i j, v i = v j := by
  intro hNe R ε q B v hv i j
  have hv' : (laurentCirculantB a b ε).mulVec v = 0 := by
    change B.mulVec v = 0
    exact hv
  let t : LaurentPolynomial ℤ := LaurentPolynomial.C ε * LaurentPolynomial.T 1
  let w : ZMod (a+b) → LaurentPolynomial ℤ := fun x =>
    ∑ k ∈ Finset.Ico 1 (a+1), v (x - (k : ZMod (a+b)))
  let x : ZMod (a+b) → LaurentPolynomial ℤ := fun r =>
    w (r + (a : ZMod (a+b))) - w r
  have hrec : ∀ r : ZMod (a+b), x r + t * x (r + 1) = 0 := by
    intro r
    have hfac := laurentCirculantB_mulVec_factor a b ha hab ε v r
    have hidx : r + (a : ZMod (a+b)) + 1 = (r + 1) + (a : ZMod (a+b)) := by abel
    calc
      x r + t * x (r + 1) =
          (w (r + (a : ZMod (a+b))) - w r) +
            t * (w (r + (a : ZMod (a+b)) + 1) - w (r + 1)) := by
            show (w (r + (a : ZMod (a+b))) - w r) +
                t * (w ((r + 1) + (a : ZMod (a+b))) - w (r + 1)) =
              (w (r + (a : ZMod (a+b))) - w r) +
                t * (w (r + (a : ZMod (a+b)) + 1) - w (r + 1))
            rw [hidx]
      _ = (laurentCirculantB a b ε).mulVec v r := hfac.symm
      _ = 0 := congrFun hv' r
  have ht : t ^ (a+b) ≠ (-1 : LaurentPolynomial ℤ) ^ (a+b) := by
    simpa [t, ε] using laurent_neg_one_t_pow_ne (a+b) n
  have hx : ∀ r : ZMod (a+b), x r = 0 :=
    zmod_recur_eq_zero hrec ht
  have hcop : Nat.Coprime a (a+b) := by
    exact Nat.coprime_self_add_right.2 hab_coprime
  have hwinv : ∀ r : ZMod (a+b), w r = w (r - (a : ZMod (a+b))) := by
    intro r
    have hxr := hx (r - (a : ZMod (a+b)))
    have h := sub_eq_zero.mp hxr
    have hidx : (r - (a : ZMod (a+b))) + (a : ZMod (a+b)) = r := by abel
    rw [hidx] at h
    exact h
  have hweq : ∀ i j : ZMod (a+b), w i = w j :=
    eq_of_forall_sub_natCast_zmod hcop hwinv
  have hvinv : ∀ r : ZMod (a+b), v r = v (r - (a : ZMod (a+b))) := by
    intro r
    have hdiff : w (r+1) - w r = 0 := sub_eq_zero.mpr (hweq (r+1) r)
    have htel := zmod_window_succ_sub a b ha v r
    have hzero : v r - v (r - (a : ZMod (a+b))) = 0 := by
      calc
        v r - v (r - (a : ZMod (a+b))) = w (r+1) - w r := by
          show v r - v (r - (a : ZMod (a+b))) =
            (∑ k ∈ Finset.Ico 1 (a+1), v ((r + 1) - (k : ZMod (a+b)))) -
              (∑ k ∈ Finset.Ico 1 (a+1), v (r - (k : ZMod (a+b))))
          exact htel.symm
        _ = 0 := hdiff
    exact sub_eq_zero.mp hzero
  exact eq_of_forall_sub_natCast_zmod hcop hvinv i j

end Rollout_p3019_laurent_circulant_kernel

#check_dependency_graph "Rollout_p3019_laurent_circulant_kernel.laurent_circulant_kernel" against "{\"edges\":[{\"conclusion\":{\"name\":\"hNe\",\"statement\":\"NeZero (a + b)\"},\"graphEdgeId\":\"h_001_hne\",\"premises\":[{\"name\":\"ha\",\"statement\":\"0 < a\"}],\"rawEdgeId\":\"telescope_7\"},{\"conclusion\":{\"name\":\"hcop\",\"statement\":\"a.Coprime (a + b)\"},\"graphEdgeId\":\"h_006_hcop\",\"premises\":[{\"name\":\"hab_coprime\",\"statement\":\"a.Coprime b\"}],\"rawEdgeId\":\"telescope_23\"},{\"conclusion\":{\"name\":\"hv'\",\"statement\":\"(Rollout_p3019_laurent_circulant_kernel.laurentCirculantB a b ε).mulVec v = 0\"},\"graphEdgeId\":\"h_002_hv\",\"premises\":[{\"name\":\"hNe\",\"statement\":\"NeZero (a + b)\"},{\"name\":\"hv\",\"statement\":\"B.mulVec v = 0\"}],\"rawEdgeId\":\"telescope_16\"},{\"conclusion\":{\"name\":\"ht\",\"statement\":\"t ^ (a + b) ≠ (-1) ^ (a + b)\"},\"graphEdgeId\":\"h_004_ht\",\"premises\":[{\"name\":\"hNe\",\"statement\":\"NeZero (a + b)\"}],\"rawEdgeId\":\"telescope_21\"},{\"conclusion\":{\"name\":\"hrec\",\"statement\":\"∀ (r : ZMod (a + b)), x r + t * x (r + 1) = 0\"},\"graphEdgeId\":\"h_003_hrec\",\"premises\":[{\"name\":\"ha\",\"statement\":\"0 < a\"},{\"name\":\"hab\",\"statement\":\"a < b\"},{\"name\":\"hNe\",\"statement\":\"NeZero (a + b)\"},{\"name\":\"hv'\",\"statement\":\"(Rollout_p3019_laurent_circulant_kernel.laurentCirculantB a b ε).mulVec v = 0\"}],\"rawEdgeId\":\"telescope_20\"},{\"conclusion\":{\"name\":\"hx\",\"statement\":\"∀ (r : ZMod (a + b)), x r = 0\"},\"graphEdgeId\":\"h_005_hx\",\"premises\":[{\"name\":\"hNe\",\"statement\":\"NeZero (a + b)\"},{\"name\":\"hrec\",\"statement\":\"∀ (r : ZMod (a + b)), x r + t * x (r + 1) = 0\"},{\"name\":\"ht\",\"statement\":\"t ^ (a + b) ≠ (-1) ^ (a + b)\"}],\"rawEdgeId\":\"telescope_22\"},{\"conclusion\":{\"name\":\"hwinv\",\"statement\":\"∀ (r : ZMod (a + b)), w r = w (r - ↑a)\"},\"graphEdgeId\":\"h_007_hwinv\",\"premises\":[{\"name\":\"hx\",\"statement\":\"∀ (r : ZMod (a + b)), x r = 0\"}],\"rawEdgeId\":\"telescope_24\"},{\"conclusion\":{\"name\":\"hweq\",\"statement\":\"∀ (i j : ZMod (a + b)), w i = w j\"},\"graphEdgeId\":\"h_008_hweq\",\"premises\":[{\"name\":\"hNe\",\"statement\":\"NeZero (a + b)\"},{\"name\":\"hcop\",\"statement\":\"a.Coprime (a + b)\"},{\"name\":\"hwinv\",\"statement\":\"∀ (r : ZMod (a + b)), w r = w (r - ↑a)\"}],\"rawEdgeId\":\"telescope_25\"},{\"conclusion\":{\"name\":\"hvinv\",\"statement\":\"∀ (r : ZMod (a + b)), v r = v (r - ↑a)\"},\"graphEdgeId\":\"h_009_hvinv\",\"premises\":[{\"name\":\"ha\",\"statement\":\"0 < a\"},{\"name\":\"hNe\",\"statement\":\"NeZero (a + b)\"},{\"name\":\"hweq\",\"statement\":\"∀ (i j : ZMod (a + b)), w i = w j\"}],\"rawEdgeId\":\"telescope_26\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"v i = v j\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hNe\",\"statement\":\"NeZero (a + b)\"},{\"name\":\"hcop\",\"statement\":\"a.Coprime (a + b)\"},{\"name\":\"hvinv\",\"statement\":\"∀ (r : ZMod (a + b)), v r = v (r - ↑a)\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p3019_laurent_circulant_kernel\",\"reconstructedProofSha256\":\"b6a8aeb5f6cba14cd040dcebf37ed3a15e11ecc23519a9600b29aa44d45044e4\",\"selectedEdgeCount\":10,\"theoremName\":\"Rollout_p3019_laurent_circulant_kernel.laurent_circulant_kernel\",\"topologySha256\":\"63d6015b119f90a9baba38749e4205742c89b29c8136c262b83a135dc804b604\"}"

namespace Rollout_p3094_finite_multiplicative_ratio_sums

-- graph_id: p3094_finite_multiplicative_ratio_sums
-- topology_sha256: 0f727dd412e7486054192c1914622fb71cd63ecb637578f20f992a8d2ee24e80
/- verified submission -/
theorem finite_multiplicative_ratio_sums
    {I : Type*} [Fintype I] [Nonempty I]
    (r : I × I → ℝ)
    (hr_pos : ∀ e d : I, 0 < r (e, d))
    (hr_mul : ∀ e d b : I, r (e, d) = r (e, b) * r (b, d)) :
    ∀ b : I,
      (∑ e : I, (∑ d : I, r (d, e))⁻¹) =
          (∑ e : I, r (b, e)) / (∑ d : I, (r (d, b))⁻¹) ∧
      (∑ e : I, r (b, e)) / (∑ d : I, (r (d, b))⁻¹) =
          (∑ e : I, r (e, b)) / (∑ d : I, r (d, b)) ∧
      (∑ e : I, r (e, b)) / (∑ d : I, r (d, b)) = 1 := by
  intro b
  have hdiag : ∀ e : I, r (e, e) = 1 := by
    intro e
    have hz : r (e, e) ≠ 0 := ne_of_gt (hr_pos e e)
    have h : r (e, e) * r (e, e) = r (e, e) * 1 := by
      rw [mul_one]
      exact (hr_mul e e e).symm
    exact mul_left_cancel₀ hz h
  have hinv : ∀ e d : I, (r (e, d))⁻¹ = r (d, e) := by
    intro e d
    have hone : r (e, d) * r (d, e) = 1 := by
      rw [← hdiag e]
      exact (hr_mul e e d).symm
    exact inv_eq_of_mul_eq_one_right hone
  have hsum_pos : ∀ e : I, 0 < ∑ d : I, r (d, e) := by
    intro e
    exact Finset.sum_pos (fun d _ => hr_pos d e) Finset.univ_nonempty
  have hsum_ne : ∀ e : I, (∑ d : I, r (d, e)) ≠ 0 := by
    intro e
    exact ne_of_gt (hsum_pos e)
  have hA : (∑ e : I, (∑ d : I, r (d, e))⁻¹) = 1 := by
    have hterm : ∀ e : I,
        (∑ d : I, r (d, e))⁻¹ =
          r (e, b) / (∑ d : I, r (d, b)) := by
      intro e
      calc
        (∑ d : I, r (d, e))⁻¹
            = ((∑ d : I, r (d, b)) / r (e, b))⁻¹ := by
              congr 1
              rw [div_eq_mul_inv, Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro d _
              calc
                r (d, e) = r (d, b) * r (b, e) := hr_mul d e b
                _ = r (d, b) * (r (e, b))⁻¹ := by rw [hinv e b]
        _ = r (e, b) / (∑ d : I, r (d, b)) := inv_div _ _
    calc
      (∑ e : I, (∑ d : I, r (d, e))⁻¹)
          = ∑ e : I, r (e, b) / (∑ d : I, r (d, b)) := by
            apply Finset.sum_congr rfl
            intro e _
            exact hterm e
      _ = (∑ e : I, r (e, b)) / (∑ d : I, r (d, b)) := by
            rw [← Finset.sum_div]
      _ = (∑ d : I, r (d, b)) / (∑ d : I, r (d, b)) := rfl
      _ = 1 := div_self (hsum_ne b)
  have hB : (∑ e : I, r (b, e)) / (∑ d : I, (r (d, b))⁻¹) = 1 := by
    have hden : (∑ d : I, (r (d, b))⁻¹) = ∑ e : I, r (b, e) := by
      apply Finset.sum_congr rfl
      intro d _
      exact hinv d b
    have hnum_pos : 0 < ∑ e : I, r (b, e) :=
      Finset.sum_pos (fun e _ => hr_pos b e) Finset.univ_nonempty
    rw [hden]
    exact div_self (ne_of_gt hnum_pos)
  have hC : (∑ e : I, r (e, b)) / (∑ d : I, r (d, b)) = 1 := by
    have hnum : (∑ e : I, r (e, b)) = ∑ d : I, r (d, b) := rfl
    rw [hnum]
    exact div_self (hsum_ne b)
  exact ⟨hA.trans hB.symm, hB.trans hC.symm, hC⟩

end Rollout_p3094_finite_multiplicative_ratio_sums

#check_dependency_graph "Rollout_p3094_finite_multiplicative_ratio_sums.finite_multiplicative_ratio_sums" against "{\"edges\":[{\"conclusion\":{\"name\":\"hdiag\",\"statement\":\"∀ (e : I), r (e, e) = 1\"},\"graphEdgeId\":\"h_001_hdiag\",\"premises\":[{\"name\":\"hr_pos\",\"statement\":\"∀ (e d : I), 0 < r (e, d)\"},{\"name\":\"hr_mul\",\"statement\":\"∀ (e d b : I), r (e, d) = r (e, b) * r (b, d)\"}],\"rawEdgeId\":\"telescope_7\"},{\"conclusion\":{\"name\":\"hsum_pos\",\"statement\":\"∀ (e : I), 0 < ∑ d, r (d, e)\"},\"graphEdgeId\":\"h_003_hsum_pos\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"Nonempty I\"},{\"name\":\"hr_pos\",\"statement\":\"∀ (e d : I), 0 < r (e, d)\"}],\"rawEdgeId\":\"telescope_9\"},{\"conclusion\":{\"name\":\"hinv\",\"statement\":\"∀ (e d : I), (r (e, d))⁻¹ = r (d, e)\"},\"graphEdgeId\":\"h_002_hinv\",\"premises\":[{\"name\":\"hr_mul\",\"statement\":\"∀ (e d b : I), r (e, d) = r (e, b) * r (b, d)\"},{\"name\":\"hdiag\",\"statement\":\"∀ (e : I), r (e, e) = 1\"}],\"rawEdgeId\":\"telescope_8\"},{\"conclusion\":{\"name\":\"hsum_ne\",\"statement\":\"∀ (e : I), ∑ d, r (d, e) ≠ 0\"},\"graphEdgeId\":\"h_004_hsum_ne\",\"premises\":[{\"name\":\"hsum_pos\",\"statement\":\"∀ (e : I), 0 < ∑ d, r (d, e)\"}],\"rawEdgeId\":\"telescope_10\"},{\"conclusion\":{\"name\":\"hA\",\"statement\":\"∑ e, (∑ d, r (d, e))⁻¹ = 1\"},\"graphEdgeId\":\"h_005_ha\",\"premises\":[{\"name\":\"hr_mul\",\"statement\":\"∀ (e d b : I), r (e, d) = r (e, b) * r (b, d)\"},{\"name\":\"hinv\",\"statement\":\"∀ (e d : I), (r (e, d))⁻¹ = r (d, e)\"},{\"name\":\"hsum_ne\",\"statement\":\"∀ (e : I), ∑ d, r (d, e) ≠ 0\"}],\"rawEdgeId\":\"telescope_11\"},{\"conclusion\":{\"name\":\"hB\",\"statement\":\"(∑ e, r (b, e)) / ∑ d, (r (d, b))⁻¹ = 1\"},\"graphEdgeId\":\"h_006_hb\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"Nonempty I\"},{\"name\":\"hr_pos\",\"statement\":\"∀ (e d : I), 0 < r (e, d)\"},{\"name\":\"hinv\",\"statement\":\"∀ (e d : I), (r (e, d))⁻¹ = r (d, e)\"}],\"rawEdgeId\":\"telescope_12\"},{\"conclusion\":{\"name\":\"hC\",\"statement\":\"(∑ e, r (e, b)) / ∑ d, r (d, b) = 1\"},\"graphEdgeId\":\"h_007_hc\",\"premises\":[{\"name\":\"hsum_ne\",\"statement\":\"∀ (e : I), ∑ d, r (d, e) ≠ 0\"}],\"rawEdgeId\":\"telescope_13\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∑ e, (∑ d, r (d, e))⁻¹ = (∑ e, r (b, e)) / ∑ d, (r (d, b))⁻¹ ∧ (∑ e, r (b, e)) / ∑ d, (r (d, b))⁻¹ = (∑ e, r (e, b)) / ∑ d, r (d, b) ∧ (∑ e, r (e, b)) / ∑ d, r (d, b) = 1\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hA\",\"statement\":\"∑ e, (∑ d, r (d, e))⁻¹ = 1\"},{\"name\":\"hB\",\"statement\":\"(∑ e, r (b, e)) / ∑ d, (r (d, b))⁻¹ = 1\"},{\"name\":\"hC\",\"statement\":\"(∑ e, r (e, b)) / ∑ d, r (d, b) = 1\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p3094_finite_multiplicative_ratio_sums\",\"reconstructedProofSha256\":\"dd870d418b7e4a9c7dfbcc6a7842cad3d95e9c2fa01b5b02f991ba2c7e7ccd6e\",\"selectedEdgeCount\":8,\"theoremName\":\"Rollout_p3094_finite_multiplicative_ratio_sums.finite_multiplicative_ratio_sums\",\"topologySha256\":\"0f727dd412e7486054192c1914622fb71cd63ecb637578f20f992a8d2ee24e80\"}"

namespace Rollout_p3114_dimension_three_evaluation_of_asymptotic_c

-- graph_id: p3114_dimension_three_evaluation_of_asymptotic_c
-- topology_sha256: f3ac9afe8a0768f21a7fcd2874352f2bb2ead0abe5b84fdd5a46b71d0f19fc12
/- accepted add_to_file helper 1 -/
lemma arccot_integrand_hasDerivAt (a x : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun y : ℝ => (1 + a ^ 2) * Real.arctan (y / a) - a * y)
      ((1 - x ^ 2) * a / (a ^ 2 + x ^ 2)) x := by
  have hden : a ^ 2 + x ^ 2 ≠ 0 := by
    positivity
  have hderiv_arctan : HasDerivAt (fun y : ℝ => Real.arctan (y / a)) (a / (a ^ 2 + x ^ 2)) x := by
    have hdiv : HasDerivAt (fun y : ℝ => y / a) (1 / a) x := by
      simpa [div_eq_mul_inv] using (hasDerivAt_id x).mul_const (a⁻¹)
    convert (Real.hasDerivAt_arctan (x / a)).comp x hdiv using 1
    field_simp [ha]
  have hconst := hderiv_arctan.const_mul (1 + a ^ 2)
  have hlin : HasDerivAt (fun y : ℝ => a * y) a x := by
    simpa using (hasDerivAt_id x).const_mul a
  convert hconst.sub hlin using 1
  field_simp [hden]
  ring

lemma asymptotic_integrand_integral_of_ne_zero (a : ℝ) (ha : a ≠ 0) :
    (∫ η in (-1 : ℝ)..1,
      if a = 0 ∧ η = 0 then 0
      else (1 - η ^ 2) * a / (a ^ 2 + η ^ 2)) =
      2 * (1 + a ^ 2) * Real.arctan (1 / a) - 2 * a := by
  let F : ℝ → ℝ := fun x => (1 + a ^ 2) * Real.arctan (x / a) - a * x
  let f' : ℝ → ℝ := fun x => (1 - x ^ 2) * a / (a ^ 2 + x ^ 2)
  have hder : deriv F = f' := by
    funext x
    exact (arccot_integrand_hasDerivAt a x ha).deriv
  have hdiff : ∀ x ∈ Set.uIcc (-1 : ℝ) 1, DifferentiableAt ℝ F x := by
    intro x hx
    exact (arccot_integrand_hasDerivAt a x ha).differentiableAt
  have hcont : ContinuousOn f' (Set.uIcc (-1 : ℝ) 1) := by
    intro x hx
    fun_prop (disch := positivity)
  have hftc := intervalIntegral.integral_deriv_eq_sub' F hder hdiff hcont
  simp [ha, F, f'] at hftc ⊢
  rw [hftc]
  have hneg : Real.arctan (-1 / a) = -Real.arctan (1 / a) := by
    rw [show -1 / a = -(1 / a) by ring, Real.arctan_neg]
  rw [hneg]
  ring

lemma asymptotic_integrand_integral_zero :
    (∫ η in (-1 : ℝ)..1,
      if (0 : ℝ) = 0 ∧ η = 0 then 0
      else (1 - η ^ 2) * (0 : ℝ) / ((0 : ℝ) ^ 2 + η ^ 2)) = 0 := by
  simp

/- verified submission -/
theorem dimension_three_evaluation_of_asymptotic_coefficient :
    let H : ℝ → ℝ := fun a => if a < 0 then 0 else if a = 0 then 1 / 2 else 1
    let arccot : ℝ → ℝ := fun a => Real.pi / 2 - Real.arctan a
    let κ : ℝ → ℝ := fun a =>
      (1 / (4 * Real.pi)) *
        (-(1 / (2 * Real.pi)) *
            (∫ η in (-1 : ℝ)..1,
              if a = 0 ∧ η = 0 then 0
              else (1 - η ^ 2) * a / (a ^ 2 + η ^ 2))
          - 1 / 4 + H a * (1 + a ^ 2))
    ∀ a : ℝ,
      κ a =
        (1 / (4 * Real.pi)) *
          (-1 / 4 - (1 + a ^ 2) * arccot a / Real.pi +
            (1 + a ^ 2) + a / Real.pi) := by
  dsimp only
  intro a
  by_cases ha0 : a = 0
  · subst a
    simp [asymptotic_integrand_integral_zero, Real.pi_ne_zero]
    field_simp [Real.pi_ne_zero]
    ring
  · by_cases hneg : a < 0
    · have hI := asymptotic_integrand_integral_of_ne_zero a ha0
      have hrec : Real.arctan (1 / a) = -(Real.pi / 2) - Real.arctan a := by
        simpa [one_div] using Real.arctan_inv_of_neg hneg
      rw [hI, hrec]
      simp [ha0, hneg, Real.pi_ne_zero]
      field_simp [Real.pi_ne_zero]
      ring
    · have hpos : 0 < a := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm ha0)
      have hI := asymptotic_integrand_integral_of_ne_zero a ha0
      have hrec : Real.arctan (1 / a) = Real.pi / 2 - Real.arctan a := by
        simpa [one_div] using Real.arctan_inv_of_pos hpos
      rw [hI, hrec]
      simp [ha0, hneg, Real.pi_ne_zero]
      field_simp [Real.pi_ne_zero]
      ring

end Rollout_p3114_dimension_three_evaluation_of_asymptotic_c

#check_dependency_graph "Rollout_p3114_dimension_three_evaluation_of_asymptotic_c.dimension_three_evaluation_of_asymptotic_coefficient" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let H := fun a => if a < 0 then 0 else if a = 0 then 1 / 2 else 1; let arccot := fun a => Real.pi / 2 - Real.arctan a; let κ := fun a => 1 / (4 * Real.pi) * ((-(1 / (2 * Real.pi)) * ∫ (η : ℝ) in -1..1, if a = 0 ∧ η = 0 then 0 else (1 - η ^ 2) * a / (a ^ 2 + η ^ 2)) - 1 / 4 + H a * (1 + a ^ 2)); ∀ (a : ℝ), κ a = 1 / (4 * Real.pi) * (-1 / 4 - (1 + a ^ 2) * arccot a / Real.pi + (1 + a ^ 2) + a / Real.pi)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p3114_dimension_three_evaluation_of_asymptotic_c\",\"reconstructedProofSha256\":\"53a6ab6fd52d027d35bf80cc15f77b78347ea02056e1506fb6576ec97f6784c0\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p3114_dimension_three_evaluation_of_asymptotic_c.dimension_three_evaluation_of_asymptotic_coefficient\",\"topologySha256\":\"f3ac9afe8a0768f21a7fcd2874352f2bb2ead0abe5b84fdd5a46b71d0f19fc12\"}"

namespace Rollout_p3184_levykhintchine_increment_bound

-- graph_id: p3184_levykhintchine_increment_bound
-- topology_sha256: 23545fecef4f1ff04645c5d928169ac23e01358909956c9b1a0cd1de6e02c090
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

#check_dependency_graph "Rollout_p3184_levykhintchine_increment_bound.levyKhintchine_increment_bound" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(∀ (u : ℝ), ‖(fun u => Complex.exp (↑Δ * (Complex.I * ↑u * ↑b - ↑σ2 * ↑u ^ 2 / 2 + ∫ (x : ℝ), (Complex.exp (Complex.I * ↑u * ↑x) - 1 - Complex.I * ↑u * ↑x) * ↑↑(n x)))) u - 1‖ ≤ Δ * |u| * ((fun u => |b| + ∫ (v : ℝ) in Set.Icc (min 0 u) (max 0 u), ‖(fun v => ∫ (x : ℝ), Complex.exp (Complex.I * ↑v * ↑x) * (fun x => ↑(x ^ 2 * ↑(n x))) x) v‖) u + σ2 * |u|)) ∧ (MeasureTheory.Integrable (fun v => ∫ (x : ℝ), Complex.exp (Complex.I * ↑v * ↑x) * (fun x => ↑(x ^ 2 * ↑(n x))) x) MeasureTheory.volume → ∀ (u : ℝ), ‖(fun u => Complex.exp (↑Δ * (Complex.I * ↑u * ↑b - ↑σ2 * ↑u ^ 2 / 2 + ∫ (x : ℝ), (Complex.exp (Complex.I * ↑u * ↑x) - 1 - Complex.I * ↑u * ↑x) * ↑↑(n x)))) u - 1‖ ≤ Δ * |u| * ((|b| + ∫ (v : ℝ), ‖(fun v => ∫ (x : ℝ), Complex.exp (Complex.I * ↑v * ↑x) * (fun x => ↑(x ^ 2 * ↑(n x))) x) v‖) + σ2 * |u|))\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hσ2\",\"statement\":\"0 ≤ σ2\"},{\"name\":\"hΔ\",\"statement\":\"0 ≤ Δ\"},{\"name\":\"hn2\",\"statement\":\"MeasureTheory.Integrable (fun x => x ^ 2 * ↑(n x)) MeasureTheory.volume\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p3184_levykhintchine_increment_bound\",\"reconstructedProofSha256\":\"a1f7540e9b6b442bfcfd05618d3ccbc7a622015324db146cc8ed61c57591b303\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p3184_levykhintchine_increment_bound.levyKhintchine_increment_bound\",\"topologySha256\":\"23545fecef4f1ff04645c5d928169ac23e01358909956c9b1a0cd1de6e02c090\"}"

namespace Rollout_p3186_simple_selection_adjusted_control

-- graph_id: p3186_simple_selection_adjusted_control
-- topology_sha256: b0f7f4c727852f78068688119b340d3a29b8ebac79c40c2a5cff0c871b481cac
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

#check_dependency_graph "Rollout_p3186_simple_selection_adjusted_control.simple_selection_adjusted_control" against "{\"edges\":[{\"conclusion\":{\"name\":\"hF_measurable\",\"statement\":\"Measurable F\"},\"graphEdgeId\":\"h_001_hf_measurable\",\"premises\":[{\"name\":\"hP_measurable\",\"statement\":\"∀ (i : Fin m), Measurable (P i)\"}],\"rawEdgeId\":\"telescope_22\"},{\"conclusion\":{\"name\":\"hY_measurable\",\"statement\":\"Measurable Y\"},\"graphEdgeId\":\"h_002_hy_measurable\",\"premises\":[{\"name\":\"hS_measurable\",\"statement\":\"∀ (s : Finset (Fin m)), MeasurableSet (S ⁻¹' {s})\"},{\"name\":\"hC_measurable\",\"statement\":\"∀ (i : Fin m) (α : ℝ), Measurable (C i α)\"}],\"rawEdgeId\":\"telescope_23\"},{\"conclusion\":{\"name\":\"hY_nonneg\",\"statement\":\"0 ≤ᵐ[μ] fun ω => Y (F ω)\"},\"graphEdgeId\":\"h_004_hy_nonneg\",\"premises\":[{\"name\":\"hC_nonnegative\",\"statement\":\"∀ (i : Fin m) (α : ℝ) (p : Fin (n i) → ↑(Set.Icc 0 1)), 0 ≤ C i α p\"}],\"rawEdgeId\":\"telescope_25\"},{\"conclusion\":{\"name\":\"hfun\",\"statement\":\"(fun ω => if (S fun i => P i ω).card = 0 then 0 else (∑ i ∈ S fun j => P j ω, C i (↑(S fun j => P j ω).card * q / ↑m) (P i ω)) / ↑(S fun j => P j ω).card) = fun ω => Y (F ω)\"},\"graphEdgeId\":\"h_006_hfun\",\"premises\":[],\"rawEdgeId\":\"telescope_27\"},{\"conclusion\":{\"name\":\"hνprob\",\"statement\":\"∀ (j : Fin m), MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.map (P j) μ)\"},\"graphEdgeId\":\"h_007_h_prob\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"MeasureTheory.IsProbabilityMeasure μ\"},{\"name\":\"hP_measurable\",\"statement\":\"∀ (i : Fin m), Measurable (P i)\"}],\"rawEdgeId\":\"telescope_28\"},{\"conclusion\":{\"name\":\"hjoint_infinite\",\"statement\":\"MeasureTheory.Measure.map F μ = MeasureTheory.Measure.infinitePi fun j => MeasureTheory.Measure.map (P j) μ\"},\"graphEdgeId\":\"h_008_hjoint_infinite\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"MeasureTheory.IsProbabilityMeasure μ\"},{\"name\":\"hP_measurable\",\"statement\":\"∀ (i : Fin m), Measurable (P i)\"},{\"name\":\"hP_independent\",\"statement\":\"ProbabilityTheory.iIndepFun P μ\"}],\"rawEdgeId\":\"telescope_29\"},{\"conclusion\":{\"name\":\"hpi_bound\",\"statement\":\"(∫⁻ (x : (i : Fin m) → Fin (n i) → ↑(Set.Icc 0 1)), ENNReal.ofReal (Y x) ∂MeasureTheory.Measure.pi fun j => MeasureTheory.Measure.map (P j) μ) ≤ ENNReal.ofReal q\"},\"graphEdgeId\":\"h_013_hpi_bound\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"MeasureTheory.IsProbabilityMeasure μ\"},{\"name\":\"hm\",\"statement\":\"0 < m\"},{\"name\":\"hq\",\"statement\":\"q ∈ Set.Icc 0 1\"},{\"name\":\"hP_measurable\",\"statement\":\"∀ (i : Fin m), Measurable (P i)\"},{\"name\":\"hS_measurable\",\"statement\":\"∀ (s : Finset (Fin m)), MeasurableSet (S ⁻¹' {s})\"},{\"name\":\"hS_simple\",\"statement\":\"∀ (i : Fin m) (x y : (i : Fin m) → Fin (n i) → ↑(Set.Icc 0 1)), (∀ (j : Fin m), j ≠ i → x j = y j) → i ∈ S x → i ∈ S y → (S x).card = (S y).card\"},{\"name\":\"hC_measurable\",\"statement\":\"∀ (i : Fin m) (α : ℝ), Measurable (C i α)\"},{\"name\":\"hC_nonnegative\",\"statement\":\"∀ (i : Fin m) (α : ℝ) (p : Fin (n i) → ↑(Set.Icc 0 1)), 0 ≤ C i α p\"},{\"name\":\"hC_valid\",\"statement\":\"∀ (i : Fin m), ∀ α ∈ Set.Icc 0 1, MeasureTheory.Integrable (fun ω => C i α (P i ω)) μ ∧ ∫ (ω : Ω), C i α (P i ω) ∂μ ≤ α\"}],\"rawEdgeId\":\"telescope_34\"},{\"conclusion\":{\"name\":\"hYF_measurable\",\"statement\":\"Measurable fun ω => Y (F ω)\"},\"graphEdgeId\":\"h_003_hyf_measurable\",\"premises\":[{\"name\":\"hF_measurable\",\"statement\":\"Measurable F\"},{\"name\":\"hY_measurable\",\"statement\":\"Measurable Y\"}],\"rawEdgeId\":\"telescope_24\"},{\"conclusion\":{\"name\":\"hjoint\",\"statement\":\"MeasureTheory.Measure.map F μ = MeasureTheory.Measure.pi fun j => MeasureTheory.Measure.map (P j) μ\"},\"graphEdgeId\":\"h_009_hjoint\",\"premises\":[{\"name\":\"hνprob\",\"statement\":\"∀ (j : Fin m), MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.map (P j) μ)\"},{\"name\":\"hjoint_infinite\",\"statement\":\"MeasureTheory.Measure.map F μ = MeasureTheory.Measure.infinitePi fun j => MeasureTheory.Measure.map (P j) μ\"}],\"rawEdgeId\":\"telescope_30\"},{\"conclusion\":{\"name\":\"hYenn_measurable\",\"statement\":\"Measurable fun x => ENNReal.ofReal (Y x)\"},\"graphEdgeId\":\"h_010_hyenn_measurable\",\"premises\":[{\"name\":\"hY_measurable\",\"statement\":\"Measurable Y\"}],\"rawEdgeId\":\"telescope_31\"},{\"conclusion\":{\"name\":\"hintegral_eq\",\"statement\":\"∫ (ω : Ω), Y (F ω) ∂μ = (∫⁻ (ω : Ω), ENNReal.ofReal (Y (F ω)) ∂μ).toReal\"},\"graphEdgeId\":\"h_005_hintegral_eq\",\"premises\":[{\"name\":\"hYF_measurable\",\"statement\":\"Measurable fun ω => Y (F ω)\"},{\"name\":\"hY_nonneg\",\"statement\":\"0 ≤ᵐ[μ] fun ω => Y (F ω)\"}],\"rawEdgeId\":\"telescope_26\"},{\"conclusion\":{\"name\":\"hlintegral_map\",\"statement\":\"∫⁻ (x : Rollout_p3186_simple_selection_adjusted_control.SimpleSelectionAdjustedControl.PTuple m n), ENNReal.ofReal (Y x) ∂MeasureTheory.Measure.map F μ = ∫⁻ (ω : Ω), ENNReal.ofReal (Y (F ω)) ∂μ\"},\"graphEdgeId\":\"h_011_hlintegral_map\",\"premises\":[{\"name\":\"hF_measurable\",\"statement\":\"Measurable F\"},{\"name\":\"hYenn_measurable\",\"statement\":\"Measurable fun x => ENNReal.ofReal (Y x)\"}],\"rawEdgeId\":\"telescope_32\"},{\"conclusion\":{\"name\":\"hlintegral_source_pi\",\"statement\":\"∫⁻ (ω : Ω), ENNReal.ofReal (Y (F ω)) ∂μ = ∫⁻ (x : (i : Fin m) → Fin (n i) → ↑(Set.Icc 0 1)), ENNReal.ofReal (Y x) ∂MeasureTheory.Measure.pi fun j => MeasureTheory.Measure.map (P j) μ\"},\"graphEdgeId\":\"h_012_hlintegral_source_pi\",\"premises\":[{\"name\":\"hjoint\",\"statement\":\"MeasureTheory.Measure.map F μ = MeasureTheory.Measure.pi fun j => MeasureTheory.Measure.map (P j) μ\"},{\"name\":\"hlintegral_map\",\"statement\":\"∫⁻ (x : Rollout_p3186_simple_selection_adjusted_control.SimpleSelectionAdjustedControl.PTuple m n), ENNReal.ofReal (Y x) ∂MeasureTheory.Measure.map F μ = ∫⁻ (ω : Ω), ENNReal.ofReal (Y (F ω)) ∂μ\"}],\"rawEdgeId\":\"telescope_33\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∫ (ω : Ω), if (S fun i => P i ω).card = 0 then 0 else (∑ i ∈ S fun j => P j ω, C i (↑(S fun j => P j ω).card * q / ↑m) (P i ω)) / ↑(S fun j => P j ω).card ∂μ ≤ q\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hq\",\"statement\":\"q ∈ Set.Icc 0 1\"},{\"name\":\"hintegral_eq\",\"statement\":\"∫ (ω : Ω), Y (F ω) ∂μ = (∫⁻ (ω : Ω), ENNReal.ofReal (Y (F ω)) ∂μ).toReal\"},{\"name\":\"hfun\",\"statement\":\"(fun ω => if (S fun i => P i ω).card = 0 then 0 else (∑ i ∈ S fun j => P j ω, C i (↑(S fun j => P j ω).card * q / ↑m) (P i ω)) / ↑(S fun j => P j ω).card) = fun ω => Y (F ω)\"},{\"name\":\"hlintegral_source_pi\",\"statement\":\"∫⁻ (ω : Ω), ENNReal.ofReal (Y (F ω)) ∂μ = ∫⁻ (x : (i : Fin m) → Fin (n i) → ↑(Set.Icc 0 1)), ENNReal.ofReal (Y x) ∂MeasureTheory.Measure.pi fun j => MeasureTheory.Measure.map (P j) μ\"},{\"name\":\"hpi_bound\",\"statement\":\"(∫⁻ (x : (i : Fin m) → Fin (n i) → ↑(Set.Icc 0 1)), ENNReal.ofReal (Y x) ∂MeasureTheory.Measure.pi fun j => MeasureTheory.Measure.map (P j) μ) ≤ ENNReal.ofReal q\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p3186_simple_selection_adjusted_control\",\"reconstructedProofSha256\":\"5035cc1119a29234c5660e64d79be03567d38c84028b5ff846fcd5905bdc0460\",\"selectedEdgeCount\":14,\"theoremName\":\"Rollout_p3186_simple_selection_adjusted_control.simple_selection_adjusted_control\",\"topologySha256\":\"b0f7f4c727852f78068688119b340d3a29b8ebac79c40c2a5cff0c871b481cac\"}"

namespace Rollout_p3255_horseshoelikepenalty_strictconcave

-- graph_id: p3255_horseshoelikepenalty_strictconcave
-- topology_sha256: 35d8c5ea9a37d2b8ec8b339d43d5d2f09b426f320a12ddbb467aa4c09e83f31b
/- accepted add_to_file helper 1 -/

open Set Real Filter

lemma h_hasDerivAt {a x : ℝ} (ha : 0 < a) (hx : x ≠ 0) :
    HasDerivAt (fun x => Real.log (1 + a / x ^ 2))
      (-2 * a / (x * (x ^ 2 + a))) x := by
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hdiv : HasDerivAt (fun x : ℝ => a / x ^ 2)
      ((0 * x ^ 2 - a * (2 * x)) / (x ^ 2) ^ 2) x := by
    exact (hasDerivAt_const x a).div hsq (pow_ne_zero 2 hx)
  have harg : HasDerivAt (fun x : ℝ => 1 + a / x ^ 2)
      (0 + (0 * x ^ 2 - a * (2 * x)) / (x ^ 2) ^ 2) x := by
    exact (hasDerivAt_const x 1).add hdiv
  have hne : (1 + a / x ^ 2) ≠ 0 := by
    positivity
  have hlog := harg.log hne
  convert hlog using 1
  field_simp [hx, ha.ne']
  ring

lemma h_deriv2_hasDerivAt {a x : ℝ} (ha : 0 < a) (hx : x ≠ 0) :
    HasDerivAt (fun x => -2 * a / (x * (x ^ 2 + a)))
      (2 * a * (3 * x ^ 2 + a) / (x ^ 2 * (x ^ 2 + a) ^ 2)) x := by
  have hinner : HasDerivAt (fun x : ℝ => x ^ 2 + a) (2 * x) x := by
    convert ((hasDerivAt_pow 2 x).add (hasDerivAt_const x a)) using 1
    ring
  have hd : HasDerivAt (fun x : ℝ => x * (x ^ 2 + a))
      (1 * (x ^ 2 + a) + x * (2 * x)) x := by
    exact (hasDerivAt_id x).mul hinner
  have hden : x * (x ^ 2 + a) ≠ 0 := by
    positivity
  have hdiv := (hasDerivAt_const x (-2 * a)).div hd hden
  convert hdiv using 1
  field_simp [hx, ha.ne']
  ring

/- accepted add_to_file helper 2 -/
lemma pen_hasDerivAt {a x : ℝ} (ha : 0 < a) (hx : x ≠ 0) :
    HasDerivAt (fun x => -Real.log (Real.log (1 + a / x ^ 2)))
      (2 * a / (x * (x ^ 2 + a) * Real.log (1 + a / x ^ 2))) x := by
  have hh := h_hasDerivAt ha hx
  have hpos : 0 < Real.log (1 + a / x ^ 2) := by
    apply Real.log_pos
    have hq : 0 < a / x ^ 2 := by positivity
    linarith
  have hlog := hh.log (ne_of_gt hpos)
  have hneg := hlog.neg
  convert hneg using 1
  field_simp [hx, ha.ne', ne_of_gt hpos]

/- accepted add_to_file helper 3 -/
lemma pen_deriv2_hasDerivAt {a x : ℝ} (ha : 0 < a) (hx : x ≠ 0) :
    HasDerivAt
      (fun x => 2 * a / (x * (x ^ 2 + a) * Real.log (1 + a / x ^ 2)))
      (-2 * a * ((3 * x ^ 2 + a) * Real.log (1 + a / x ^ 2) - 2 * a) /
        ((x * (x ^ 2 + a)) ^ 2 * (Real.log (1 + a / x ^ 2)) ^ 2)) x := by
  have hinner : HasDerivAt (fun x : ℝ => x ^ 2 + a) (2 * x) x := by
    convert ((hasDerivAt_pow 2 x).add (hasDerivAt_const x a)) using 1
    ring
  have hD : HasDerivAt (fun x : ℝ => x * (x ^ 2 + a))
      (1 * (x ^ 2 + a) + x * (2 * x)) x := by
    exact (hasDerivAt_id x).mul hinner
  have hH := h_hasDerivAt ha hx
  have hden : HasDerivAt
      (fun x : ℝ => x * (x ^ 2 + a) * Real.log (1 + a / x ^ 2))
      ((1 * (x ^ 2 + a) + x * (2 * x)) * Real.log (1 + a / x ^ 2) +
        x * (x ^ 2 + a) * (-2 * a / (x * (x ^ 2 + a)))) x := by
    exact hD.mul hH
  have hHpos : 0 < Real.log (1 + a / x ^ 2) := by
    apply Real.log_pos
    have hq : 0 < a / x ^ 2 := by positivity
    linarith
  have hDne : x * (x ^ 2 + a) ≠ 0 := by positivity
  have hdenne : x * (x ^ 2 + a) * Real.log (1 + a / x ^ 2) ≠ 0 :=
    mul_ne_zero hDne (ne_of_gt hHpos)
  have hdiv := (hasDerivAt_const x (2 * a)).div hden hdenne
  convert hdiv using 1
  field_simp [hx, ha.ne', ne_of_gt hHpos, hDne]
  ring

/- accepted add_to_file helper 4 -/
lemma pen_second_factor_pos {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    0 < (3 * x ^ 2 + a) * Real.log (1 + a / x ^ 2) - 2 * a := by
  let r : ℝ := a / x ^ 2
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hlog : 2 * r / (r + 2) < Real.log (1 + r) := Real.lt_log_one_add_of_pos hr
  have hfrac : 2 * r / (r + 3) < 2 * r / (r + 2) := by
    have hnum : 0 < 2 * r := by positivity
    have hd23 : 0 < r + 2 := by positivity
    have hdle : r + 2 < r + 3 := by linarith
    exact div_lt_div_of_pos_left hnum hd23 hdle
  have hlow : 2 * r / (r + 3) < Real.log (1 + r) := lt_trans hfrac hlog
  have hlow' : 2 * r < (r + 3) * Real.log (1 + r) := by
    rw [mul_comm (r + 3)]
    exact (div_lt_iff₀ (by positivity : 0 < r + 3)).mp hlow
  have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx
  have hmul : 0 < x ^ 2 * ((r + 3) * Real.log (1 + r) - 2 * r) :=
    mul_pos hx2 (sub_pos.mpr hlow')
  have hreq : x ^ 2 * ((r + 3) * Real.log (1 + r) - 2 * r) =
      (3 * x ^ 2 + a) * Real.log (1 + a / x ^ 2) - 2 * a := by
    dsimp [r]
    field_simp [ne_of_gt hx]
    ring
  rwa [hreq] at hmul

/- accepted add_to_file helper 5 -/
lemma pen_strictConcaveOn_pos {a : ℝ} (ha : 0 < a) :
    StrictConcaveOn ℝ (Ioi 0)
      (fun x => -Real.log (Real.log (1 + a / x ^ 2))) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Ioi 0)
  · intro x hx
    exact (pen_hasDerivAt ha (ne_of_gt hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hev : (fun y => deriv (fun x => -Real.log (Real.log (1 + a / x ^ 2))) y)
        =ᶠ[nhds x]
        fun y => 2 * a / (y * (y ^ 2 + a) * Real.log (1 + a / y ^ 2)) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact (pen_hasDerivAt ha (ne_of_gt hy)).deriv
    have h2 : deriv (deriv (fun x => -Real.log (Real.log (1 + a / x ^ 2)))) x =
        -2 * a * ((3 * x ^ 2 + a) * Real.log (1 + a / x ^ 2) - 2 * a) /
          ((x * (x ^ 2 + a)) ^ 2 * (Real.log (1 + a / x ^ 2)) ^ 2) := by
      rw [hev.deriv_eq]
      exact (pen_deriv2_hasDerivAt ha (ne_of_gt hx)).deriv
    have hiter : deriv^[2] (fun x => -Real.log (Real.log (1 + a / x ^ 2))) x =
        deriv (deriv (fun x => -Real.log (Real.log (1 + a / x ^ 2)))) x := rfl
    rw [hiter, h2]
    have hfactor := pen_second_factor_pos ha hx
    have hLpos : 0 < Real.log (1 + a / x ^ 2) := by
      apply Real.log_pos
      have hq : 0 < a / x ^ 2 := div_pos ha (sq_pos_of_pos hx)
      linarith
    have hnum : -2 * a *
        ((3 * x ^ 2 + a) * Real.log (1 + a / x ^ 2) - 2 * a) < 0 := by
      have hcoef : -2 * a < 0 := by nlinarith
      exact mul_neg_of_neg_of_pos hcoef hfactor
    have hden : 0 < (x * (x ^ 2 + a)) ^ 2 *
        (Real.log (1 + a / x ^ 2)) ^ 2 := by
      have hD : 0 < x * (x ^ 2 + a) := by
        exact mul_pos hx (add_pos (sq_pos_of_pos hx) ha)
      exact mul_pos (sq_pos_of_pos hD) (sq_pos_of_pos hLpos)
    exact div_neg_of_neg_of_pos hnum hden

/- verified submission -/
theorem horseshoeLikePenalty_strictConcave (a : ℝ) (ha : 0 < a) :
    let pen_a : ℝ → ℝ := fun x => -Real.log (Real.log (1 + a / x ^ 2))
    ∀ x y t : ℝ,
      x ≠ y →
      ((0 < x ∧ 0 < y) ∨ (x < 0 ∧ y < 0)) →
      0 < t →
      t < 1 →
      pen_a (t * x + (1 - t) * y) >
        t * pen_a x + (1 - t) * pen_a y := by
  dsimp
  intro x y t hxy hs ht ht1
  have hsc := pen_strictConcaveOn_pos ha
  have ht' : 0 < 1 - t := sub_pos.mpr ht1
  have hsum : t + (1 - t) = 1 := by ring
  rcases hs with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact hsc.2 hx hy hxy ht ht' hsum
  · let u : ℝ := -x
    let v : ℝ := -y
    have hu : 0 < u := by
      dsimp [u]
      linarith
    have hv : 0 < v := by
      dsimp [v]
      linarith
    have huv : u ≠ v := by
      intro huv_eq
      apply hxy
      dsimp [u, v] at huv_eq
      linarith
    have hmain := hsc.2 hu hv huv ht ht' hsum
    have hcomb : t * u + (1 - t) * v = -(t * x + (1 - t) * y) := by
      dsimp [u, v]
      ring
    have hsqcomb : (-(t * x + (1 - t) * y)) ^ 2 =
        (t * x + (1 - t) * y) ^ 2 := by ring
    have hsqx : (-x) ^ 2 = x ^ 2 := by ring
    have hsqy : (-y) ^ 2 = y ^ 2 := by ring
    dsimp [u, v] at hmain
    rw [hcomb, hsqcomb, hsqx, hsqy] at hmain
    exact hmain

end Rollout_p3255_horseshoelikepenalty_strictconcave

#check_dependency_graph "Rollout_p3255_horseshoelikepenalty_strictconcave.horseshoeLikePenalty_strictConcave" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let pen_a := fun x => -Real.log (Real.log (1 + a / x ^ 2)); ∀ (x y t : ℝ), x ≠ y → 0 < x ∧ 0 < y ∨ x < 0 ∧ y < 0 → 0 < t → t < 1 → pen_a (t * x + (1 - t) * y) > t * pen_a x + (1 - t) * pen_a y\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"ha\",\"statement\":\"0 < a\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p3255_horseshoelikepenalty_strictconcave\",\"reconstructedProofSha256\":\"41101667f44f50494fabd24699c51bd975f8acf936333a2d7c4512aa4f09cec5\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p3255_horseshoelikepenalty_strictconcave.horseshoeLikePenalty_strictConcave\",\"topologySha256\":\"35d8c5ea9a37d2b8ec8b339d43d5d2f09b426f320a12ddbb467aa4c09e83f31b\"}"
