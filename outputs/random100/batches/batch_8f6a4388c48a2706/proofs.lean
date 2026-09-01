import Mathlib

/- Generated only to amortize Mathlib loading during graph export. -/

namespace Rollout_p2692_hodge_operator_on_two_forms

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

namespace Rollout_p2116_pendant_branch_laplacian_eigenvector_decay

/- accepted add_to_file helper 1 -/
lemma pendant_neighborFinset_interior
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 1 ≤ k)
    (i : Fin k → V)
    (hbranch : ∀ a b : Fin k,
      G.Adj (i a) (i b) ↔ a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (hexternal : ∃ x : V,
      x ∉ Set.range i ∧
      G.Adj (i ⟨0, hk⟩) x ∧
      ∀ (a : Fin k) (v : V), v ∉ Set.range i → G.Adj (i a) v →
        a = ⟨0, hk⟩ ∧ v = x)
    (a : Fin k) (ha : 0 < a.val) (hs : a.val + 1 < k) :
    G.neighborFinset (i a) =
      {i ⟨a.val - 1, by omega⟩, i ⟨a.val + 1, hs⟩} := by
  ext v
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hAdj
    by_cases hv : v ∈ Set.range i
    · rcases hv with ⟨b, rfl⟩
      have hb := (hbranch a b).mp hAdj
      rcases hb with h | h
      · right
        have hbv : b.val = a.val + 1 := by omega
        exact congrArg i (Fin.ext hbv)
      · left
        have hbv : b.val = a.val - 1 := by omega
        exact congrArg i (Fin.ext hbv)
    · rcases hexternal with ⟨x, hxrange, hxadj, huniq⟩
      obtain ⟨ha0, hvx⟩ := huniq a v hv hAdj
      have : a.val = 0 := congrArg Fin.val ha0
      omega
  · intro hv
    rcases hv with hv | hv
    · subst v
      have hpred : a.val - 1 + 1 = a.val := by omega
      exact (hbranch a ⟨a.val - 1, by omega⟩).mpr (Or.inr hpred)
    · subst v
      exact (hbranch a ⟨a.val + 1, hs⟩).mpr (Or.inl rfl)

lemma pendant_neighborFinset_last
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 1 ≤ k)
    (i : Fin k → V)
    (hbranch : ∀ a b : Fin k,
      G.Adj (i a) (i b) ↔ a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (hexternal : ∃ x : V,
      x ∉ Set.range i ∧
      G.Adj (i ⟨0, hk⟩) x ∧
      ∀ (a : Fin k) (v : V), v ∉ Set.range i → G.Adj (i a) v →
        a = ⟨0, hk⟩ ∧ v = x)
    (a : Fin k) (ha : 0 < a.val) (hs : a.val + 1 = k) :
    G.neighborFinset (i a) =
      {i ⟨a.val - 1, by omega⟩} := by
  ext v
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hAdj
    by_cases hv : v ∈ Set.range i
    · rcases hv with ⟨b, rfl⟩
      have hb := (hbranch a b).mp hAdj
      rcases hb with h | h
      · have : b.val = k := by omega
        omega
      · have hbv : b.val = a.val - 1 := by omega
        exact congrArg i (Fin.ext hbv)
    · rcases hexternal with ⟨x, hxrange, hxadj, huniq⟩
      obtain ⟨ha0, hvx⟩ := huniq a v hv hAdj
      have : a.val = 0 := congrArg Fin.val ha0
      omega
  · intro hv
    subst v
    have hpred : a.val - 1 + 1 = a.val := by omega
    exact (hbranch a ⟨a.val - 1, by omega⟩).mpr (Or.inr hpred)

/- accepted add_to_file helper 2 -/
theorem pendant_eigen_last
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 1 ≤ k)
    (i : Fin k → V)
    (hbranch : ∀ a b : Fin k,
      G.Adj (i a) (i b) ↔ a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (hexternal : ∃ x : V,
      x ∉ Set.range i ∧
      G.Adj (i ⟨0, hk⟩) x ∧
      ∀ (a : Fin k) (v : V), v ∉ Set.range i → G.Adj (i a) v →
        a = ⟨0, hk⟩ ∧ v = x)
    (lam : ℝ)
    (φ : V → ℝ)
    (heigen : (G.lapMatrix ℝ).mulVec φ = lam • φ)
    (j : Fin k) (hj : j.val + 1 < k)
    (hjd : j.val + 2 = k) :
    φ (i j) = (1 - lam) * φ (i ⟨j.val + 1, hj⟩) := by
  have hpos : 0 < (⟨j.val + 1, hj⟩ : Fin k).val := by
    change 0 < j.val + 1
    omega
  have hlast : (⟨j.val + 1, hj⟩ : Fin k).val + 1 = k := by
    change j.val + 1 + 1 = k
    omega
  have hneigh := pendant_neighborFinset_last G hk i hbranch hexternal
      ⟨j.val + 1, hj⟩ hpos hlast
  have hpred : (⟨(⟨j.val + 1, hj⟩ : Fin k).val - 1, by omega⟩ : Fin k) = j := by
    apply Fin.ext
    change j.val + 1 - 1 = j.val
    omega
  have hcard : (G.neighborFinset (i ⟨j.val + 1, hj⟩)).card = 1 := by
    rw [hneigh]
    simp
  have hdeg : G.degree (i ⟨j.val + 1, hj⟩) = 1 := by
    rw [← G.card_neighborFinset_eq_degree, hcard]
  have hEq := congrFun heigen (i ⟨j.val + 1, hj⟩)
  rw [SimpleGraph.lapMatrix_mulVec_apply] at hEq
  rw [hdeg, hneigh] at hEq
  simp [hpred] at hEq
  linarith

/- accepted add_to_file helper 3 -/
theorem pendant_eigen_interior
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 1 ≤ k)
    (i : Fin k → V)
    (hi : Function.Injective i)
    (hbranch : ∀ a b : Fin k,
      G.Adj (i a) (i b) ↔ a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (hexternal : ∃ x : V,
      x ∉ Set.range i ∧
      G.Adj (i ⟨0, hk⟩) x ∧
      ∀ (a : Fin k) (v : V), v ∉ Set.range i → G.Adj (i a) v →
        a = ⟨0, hk⟩ ∧ v = x)
    (lam : ℝ)
    (φ : V → ℝ)
    (heigen : (G.lapMatrix ℝ).mulVec φ = lam • φ)
    (j : Fin k) (hj : j.val + 1 < k) (hj2 : j.val + 2 < k) :
    φ (i j) + φ (i ⟨j.val + 2, hj2⟩) =
      (2 - lam) * φ (i ⟨j.val + 1, hj⟩) := by
  let s : Fin k := ⟨j.val + 1, hj⟩
  have hsval : s.val = j.val + 1 := rfl
  have hs_pos : 0 < s.val := by
    rw [hsval]
    omega
  have hs_succ : s.val + 1 < k := by
    rw [hsval]
    omega
  have hneigh := pendant_neighborFinset_interior G hk i hbranch hexternal s hs_pos hs_succ
  have hpred : (⟨s.val - 1, by omega⟩ : Fin k) = j := by
    apply Fin.ext
    change s.val - 1 = j.val
    omega
  have hnext : (⟨s.val + 1, hs_succ⟩ : Fin k) = ⟨j.val + 2, hj2⟩ := by
    apply Fin.ext
    change s.val + 1 = j.val + 2
    omega
  have hne : (⟨s.val - 1, by omega⟩ : Fin k) ≠ ⟨s.val + 1, hs_succ⟩ := by
    intro h
    have hv := congrArg Fin.val h
    change s.val - 1 = s.val + 1 at hv
    omega
  have hvne : i ⟨s.val - 1, by omega⟩ ≠ i ⟨s.val + 1, hs_succ⟩ := by
    intro h
    exact hne (hi h)
  have hcard : (G.neighborFinset (i s)).card = 2 := by
    rw [hneigh]
    exact Finset.card_pair hvne
  have hdeg : G.degree (i s) = 2 := by
    rw [← G.card_neighborFinset_eq_degree, hcard]
  have hEq := congrFun heigen (i s)
  rw [SimpleGraph.lapMatrix_mulVec_apply] at hEq
  rw [hdeg, hneigh] at hEq
  rw [Finset.sum_pair hvne] at hEq
  simp [hpred, hnext] at hEq
  linarith

/- accepted add_to_file helper 4 -/
theorem pendant_adjacent_decay
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 1 ≤ k)
    (i : Fin k → V)
    (hi : Function.Injective i)
    (hbranch : ∀ a b : Fin k,
      G.Adj (i a) (i b) ↔ a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (hexternal : ∃ x : V,
      x ∉ Set.range i ∧
      G.Adj (i ⟨0, hk⟩) x ∧
      ∀ (a : Fin k) (v : V), v ∉ Set.range i → G.Adj (i a) v →
        a = ⟨0, hk⟩ ∧ v = x)
    (lam : ℝ) (hlam : 4 < lam)
    (φ : V → ℝ)
    (heigen : (G.lapMatrix ℝ).mulVec φ = lam • φ) :
    ∀ (j : Fin k) (hj : j.val + 1 < k),
      |φ (i ⟨j.val + 1, hj⟩)| ≤
        (2 / (lam - 2)) * |φ (i j)| := by
  let γ : ℝ := 2 / (lam - 2)
  have ht : 0 < lam - 2 := by nlinarith
  have hγpos : 0 < γ := by
    dsimp [γ]
    positivity
  have hγlt : γ < 1 := by
    dsimp [γ]
    rw [div_lt_one ht]
    nlinarith
  have Haux : ∀ d : ℕ, ∀ (j : Fin k) (hj : j.val + 1 < k),
      j.val + d + 2 = k →
      |φ (i ⟨j.val + 1, hj⟩)| ≤ γ * |φ (i j)| := by
    intro d
    induction d with
    | zero =>
        intro j hj hdist
        have hjd : j.val + 2 = k := by omega
        have heq := pendant_eigen_last G hk i hbranch hexternal lam φ heigen j hj hjd
        have hAbs : |φ (i j)| = (lam - 1) * |φ (i ⟨j.val + 1, hj⟩)| := by
          rw [heq]
          rw [abs_mul]
          have hneg : 1 - lam < 0 := by nlinarith
          rw [abs_of_neg hneg]
          ring
        have hcoef : 1 ≤ γ * (lam - 1) := by
          dsimp [γ]
          field_simp [ne_of_gt ht]
          nlinarith
        calc
          |φ (i ⟨j.val + 1, hj⟩)| = 1 * |φ (i ⟨j.val + 1, hj⟩)| := by
            rw [one_mul]
          _ ≤ (γ * (lam - 1)) * |φ (i ⟨j.val + 1, hj⟩)| :=
            mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
          _ = γ * ((lam - 1) * |φ (i ⟨j.val + 1, hj⟩)|) := by ring
          _ = γ * |φ (i j)| := by rw [← hAbs]
    | succ d ih =>
        intro j hj hdist
        have hj2 : j.val + 2 < k := by omega
        let s : Fin k := ⟨j.val + 1, hj⟩
        have hsval : s.val = j.val + 1 := rfl
        have hs : s.val + 1 < k := by
          rw [hsval]
          omega
        have hsdist : s.val + d + 2 = k := by
          rw [hsval]
          omega
        have hnext := ih s hs hsdist
        have hnext' : |φ (i ⟨j.val + 2, hj2⟩)| ≤ γ * |φ (i s)| := by
          simpa [s] using hnext
        have heq := pendant_eigen_interior G hk i hi hbranch hexternal lam φ heigen j hj hj2
        have hAbs : |φ (i j) + φ (i ⟨j.val + 2, hj2⟩)| =
            (lam - 2) * |φ (i s)| := by
          rw [heq]
          rw [abs_mul]
          have hneg : 2 - lam < 0 := by nlinarith
          rw [abs_of_neg hneg]
          have hsdef : s = ⟨j.val + 1, hj⟩ := rfl
          rw [hsdef]
          ring
        have hineq0 : (lam - 2) * |φ (i s)| ≤
            |φ (i j)| + |φ (i ⟨j.val + 2, hj2⟩)| := by
          rw [← hAbs]
          exact abs_add_le _ _
        have hineq : (lam - 2) * |φ (i s)| ≤
            |φ (i j)| + γ * |φ (i s)| := by
          nlinarith
        have hsub : (lam - 2 - γ) * |φ (i s)| ≤ |φ (i j)| := by
          nlinarith
        have hcoef : 1 ≤ γ * (lam - 2 - γ) := by
          dsimp [γ]
          have htgt : 2 < lam - 2 := by nlinarith
          have htsq : 4 < (lam - 2)^2 := by
            nlinarith [mul_lt_mul_of_pos_left htgt ht]
          field_simp [ne_of_gt ht]
          nlinarith
        calc
          |φ (i ⟨j.val + 1, hj⟩)| = 1 * |φ (i ⟨j.val + 1, hj⟩)| := by
            rw [one_mul]
          _ ≤ (γ * (lam - 2 - γ)) * |φ (i ⟨j.val + 1, hj⟩)| :=
            mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
          _ = γ * ((lam - 2 - γ) * |φ (i ⟨j.val + 1, hj⟩)|) := by ring
          _ ≤ γ * |φ (i j)| := by
            have hsub' : (lam - 2 - γ) * |φ (i ⟨j.val + 1, hj⟩)| ≤ |φ (i j)| := by
              simpa [s] using hsub
            exact mul_le_mul_of_nonneg_left hsub' hγpos.le
  intro j hj
  exact Haux (k - (j.val + 2)) j hj (by omega)

/- verified submission -/
theorem pendant_branch_laplacian_eigenvector_decay
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : 1 ≤ k)
    (i : Fin k → V)
    (hi : Function.Injective i)
    (hbranch : ∀ a b : Fin k,
      G.Adj (i a) (i b) ↔ a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (hexternal : ∃ x : V,
      x ∉ Set.range i ∧
      G.Adj (i ⟨0, hk⟩) x ∧
      ∀ (a : Fin k) (v : V), v ∉ Set.range i → G.Adj (i a) v →
        a = ⟨0, hk⟩ ∧ v = x)
    (lam : ℝ) (hlam : 4 < lam)
    (φ : V → ℝ) (hφ : φ ≠ 0)
    (heigen : (G.lapMatrix ℝ).mulVec φ = lam • φ) :
    let γ : ℝ := 2 / (lam - 2)
    0 < γ ∧ γ < 1 ∧
      (∀ (j : Fin k) (hj : j.val + 1 < k),
        |φ (i ⟨j.val + 1, hj⟩)| ≤ γ * |φ (i j)|) ∧
      ∀ j : Fin k, |φ (i j)| ≤ γ ^ j.val * |φ (i ⟨0, hk⟩)| := by
  dsimp only
  set γ : ℝ := 2 / (lam - 2) with hγdef
  have ht : 0 < lam - 2 := by nlinarith
  have hγpos : 0 < γ := by
    rw [hγdef]
    positivity
  have hγlt : γ < 1 := by
    rw [hγdef, div_lt_one ht]
    nlinarith
  have hadj := pendant_adjacent_decay G hk i hi hbranch hexternal lam hlam φ heigen
  refine ⟨hγpos, hγlt, ?_, ?_⟩
  · intro j hj
    rw [hγdef]
    exact hadj j hj
  · have Hpow_aux : ∀ n : ℕ, ∀ j : Fin k, j.val = n →
        |φ (i j)| ≤ γ ^ j.val * |φ (i ⟨0, hk⟩)| := by
      intro n
      induction n with
      | zero =>
          intro j hjval
          have hzero : j = ⟨0, hk⟩ := Fin.ext (by omega)
          rw [hzero]
          simp
      | succ n ih =>
          intro j hjval
          have hnlt : n < k := by omega
          let p : Fin k := ⟨n, hnlt⟩
          have hsproof : p.val + 1 < k := by
            dsimp [p]
            omega
          have hjp : j = ⟨p.val + 1, hsproof⟩ := by
            apply Fin.ext
            dsimp [p]
            omega
          calc
            |φ (i j)| = |φ (i ⟨p.val + 1, hsproof⟩)| := congrArg (fun v => |φ (i v)|) hjp
            _ ≤ γ * |φ (i p)| := by
              rw [hγdef]
              exact hadj p hsproof
            _ ≤ γ * (γ ^ n * |φ (i ⟨0, hk⟩)|) := by
              have hpval : p.val = n := rfl
              exact mul_le_mul_of_nonneg_left (ih p hpval) hγpos.le
            _ = γ ^ (n + 1) * |φ (i ⟨0, hk⟩)| := by
              rw [pow_succ]
              ring
            _ = γ ^ j.val * |φ (i ⟨0, hk⟩)| := by
              rw [hjval]
    intro j
    exact Hpow_aux j.val j rfl

end Rollout_p2116_pendant_branch_laplacian_eigenvector_decay

namespace Rollout_p1136_entropy_number_approximation

/- accepted add_to_file helper 1 -/
lemma exists_isCover_encard_le_of_externalCoveringNumber_le
    {Z : Type*} [PseudoEMetricSpace Z] {ε : NNReal} {A : Set Z} {m : ℕ}
    (h : Metric.externalCoveringNumber ε A ≤ (m : ℕ∞)) :
    ∃ C : Set Z, Metric.IsCover ε A C ∧ C.encard ≤ (m : ℕ∞) := by
  unfold Metric.externalCoveringNumber at h
  have hlt : (⨅ C : Set Z, ⨅ _ : Metric.IsCover ε A C, C.encard) < (m : ℕ∞) + 1 :=
    lt_of_le_of_lt h ((ENat.lt_add_one_iff (ENat.coe_ne_top m)).mpr le_rfl)
  rcases (iInf_lt_iff.mp hlt) with ⟨C, hC⟩
  rcases (iInf_lt_iff.mp hC) with ⟨hCcover, hCcard⟩
  exact ⟨C, hCcover, (ENat.lt_add_one_iff (ENat.coe_ne_top m)).mp hCcard⟩

/- accepted add_to_file helper 2 -/
lemma exists_covering_radius_lt_of_iInf_lt
    {Z W : Type*} [PseudoEMetricSpace Z] {A : Set Z} {m : ℕ} {r : ENNReal}
    (h : (⨅ (ε : NNReal), ⨅ (_ : 0 < ε),
      ⨅ (_ : Metric.externalCoveringNumber ε A ≤ (m : ℕ∞)), (ε : ENNReal)) < r) :
    ∃ ε : NNReal, 0 < ε ∧ Metric.externalCoveringNumber ε A ≤ (m : ℕ∞) ∧
      (ε : ENNReal) < r := by
  rcases (iInf_lt_iff.mp h) with ⟨ε, hε⟩
  rcases (iInf_lt_iff.mp hε) with ⟨hεpos, hεcover⟩
  rcases (iInf_lt_iff.mp hεcover) with ⟨hcover, hεlt⟩
  exact ⟨ε, hεpos, hcover, hεlt⟩

/- accepted add_to_file helper 3 -/
lemma iInf_covering_radius_le
    {Z : Type*} [PseudoEMetricSpace Z] {A : Set Z} {m : ℕ} {r : NNReal}
    (hr : 0 < r) (hc : Metric.externalCoveringNumber r A ≤ (m : ℕ∞)) :
    (⨅ (ε : NNReal), ⨅ (_ : 0 < ε),
      ⨅ (_ : Metric.externalCoveringNumber ε A ≤ (m : ℕ∞)), (ε : ENNReal)) ≤
      (r : ENNReal) := by
  exact iInf_le_of_le r (iInf_le_of_le hr (iInf_le_of_le hc le_rfl))

/- accepted add_to_file helper 4 -/
lemma card_mul_two_pow_pred_le_pow {c n : ℕ} (hn : 0 < n) :
    (c : ℕ∞) * (2 ^ (n - 1) : ℕ∞) ≤ (2 ^ (n + Nat.log 2 c) : ℕ∞) := by
  have hc : c ≤ 2 ^ (Nat.log 2 c + 1) :=
    Nat.le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) c)
  have hmul : c * 2 ^ (n - 1) ≤ 2 ^ (Nat.log 2 c + 1) * 2 ^ (n - 1) :=
    Nat.mul_le_mul_right _ hc
  have hpow : 2 ^ (Nat.log 2 c + 1) * 2 ^ (n - 1) = 2 ^ (n + Nat.log 2 c) := by
    rw [← pow_add]
    congr 1
    omega
  exact_mod_cast hmul.trans_eq hpow

/- accepted add_to_file helper 5 -/
lemma exists_covering_radius_lt_of_iInf_lt'
    {Z : Type*} [PseudoEMetricSpace Z] {A : Set Z} {m : ℕ} {r : ENNReal}
    (h : (⨅ (ε : NNReal), ⨅ (_ : 0 < ε),
      ⨅ (_ : Metric.externalCoveringNumber ε A ≤ (m : ℕ∞)), (ε : ENNReal)) < r) :
    ∃ ε : NNReal, 0 < ε ∧ Metric.externalCoveringNumber ε A ≤ (m : ℕ∞) ∧
      (ε : ENNReal) < r := by
  rcases (iInf_lt_iff.mp h) with ⟨ε, hε⟩
  rcases (iInf_lt_iff.mp hε) with ⟨hεpos, hεcover⟩
  rcases (iInf_lt_iff.mp hεcover) with ⟨hcover, hεlt⟩
  exact ⟨ε, hεpos, hcover, hεlt⟩

/- verified submission -/
theorem entropy_number_approximation
    (𝕜 : Type*) [RCLike 𝕜]
    (X Y : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (Γ : Type*) [Fintype Γ] [Nonempty Γ]
    (V : X →ₗ[𝕜] Y) (Vγ : Γ → X →ₗ[𝕜] Y)
    (n : ℕ) (hn : 0 < n) :
    let e : ℕ → (X →ₗ[𝕜] Y) → ENNReal := fun k T ↦
      ⨅ (ε : NNReal) (_ : 0 < ε)
        (_ : Metric.externalCoveringNumber ε (T '' Metric.closedBall (0 : X) 1) ≤
          2 ^ (k - 1)),
        (ε : ENNReal)
    e (n + Nat.log 2 (Fintype.card Γ) + 1) V ≤
      (⨆ γ : Γ, e n (Vγ γ)) +
        (⨆ (x : X) (_ : ‖x‖ ≤ 1),
          ⨅ γ : Γ, ENNReal.ofReal ‖V x - Vγ γ x‖) := by
  let e : ℕ → (X →ₗ[𝕜] Y) → ENNReal := fun k T ↦
    ⨅ (ε : NNReal) (_ : 0 < ε)
      (_ : Metric.externalCoveringNumber ε (T '' Metric.closedBall (0 : X) 1) ≤
        2 ^ (k - 1)),
      (ε : ENNReal)
  let A : ENNReal := ⨆ γ : Γ, e n (Vγ γ)
  let B : ENNReal := ⨆ (x : X) (_ : ‖x‖ ≤ 1),
    ⨅ γ : Γ, ENNReal.ofReal ‖V x - Vγ γ x‖
  change e (n + Nat.log 2 (Fintype.card Γ) + 1) V ≤ A + B
  by_cases htop : A + B = ⊤
  · rw [htop]
    exact le_top
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  by_cases hεtop : ε = ⊤
  · rw [hεtop]
    simp
  have hA : A ≠ ⊤ := by
    intro h
    apply htop
    rw [h]
    simp
  have hB : B ≠ ⊤ := by
    intro h
    apply htop
    rw [h]
    simp
  let η : ENNReal := ε / 2
  have hηpos : 0 < η := ENNReal.div_pos (ne_of_gt hε) (by norm_num)
  have hηne : η ≠ 0 := ne_of_gt hηpos
  have hrad : ∀ γ : Γ, ∃ r : NNReal, 0 < r ∧
      Metric.externalCoveringNumber r (Vγ γ '' Metric.closedBall (0 : X) 1) ≤
        ((2 ^ (n - 1) : ℕ) : ℕ∞) ∧
      (r : ENNReal) < A + η := by
    intro γ
    apply exists_covering_radius_lt_of_iInf_lt'
    have hle : e n (Vγ γ) ≤ A := by
      exact le_iSup (fun γ : Γ => e n (Vγ γ)) γ
    exact lt_of_le_of_lt hle (ENNReal.lt_add_right hA hηne)
  choose r hrpos hrcov hrlt using hrad
  have hcover : ∀ γ : Γ, ∃ C : Set Y,
      Metric.IsCover (r γ) (Vγ γ '' Metric.closedBall (0 : X) 1) C ∧
      C.encard ≤ ((2 ^ (n - 1) : ℕ) : ℕ∞) := by
    intro γ
    exact exists_isCover_encard_le_of_externalCoveringNumber_le (hrcov γ)
  choose C hCcover hCcard using hcover
  have htarget_top : A + B + ε ≠ ⊤ := by
    rw [ENNReal.add_ne_top]
    exact ⟨htop, hεtop⟩
  have htarget_zero : A + B + ε ≠ 0 := by
    intro h
    have hεzero : ε = 0 := (add_eq_zero.mp h).2
    exact (ne_of_gt hε) hεzero
  let R : NNReal := (A + B + ε).toNNReal
  have hRpos : 0 < R := ENNReal.toNNReal_pos htarget_zero htarget_top
  have hR_coe : (R : ENNReal) = A + B + ε := ENNReal.coe_toNNReal htarget_top
  have hVcover : Metric.IsCover R (V '' Metric.closedBall (0 : X) 1)
      (⋃ γ : Γ, C γ) := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hxnorm : ‖x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hb_le : (⨅ γ : Γ, ENNReal.ofReal ‖V x - Vγ γ x‖) ≤ B := by
      have hinner : (⨅ γ : Γ, ENNReal.ofReal ‖V x - Vγ γ x‖) ≤
          ⨆ (_ : ‖x‖ ≤ 1), ⨅ γ : Γ, ENNReal.ofReal ‖V x - Vγ γ x‖ := by
        exact le_iSup
          (fun _ : ‖x‖ ≤ 1 => ⨅ γ : Γ, ENNReal.ofReal ‖V x - Vγ γ x‖) hxnorm
      exact hinner.trans
        (le_iSup
          (fun x : X => ⨆ (_ : ‖x‖ ≤ 1),
            ⨅ γ : Γ, ENNReal.ofReal ‖V x - Vγ γ x‖) x)
    have hb_lt : (⨅ γ : Γ, ENNReal.ofReal ‖V x - Vγ γ x‖) < B + η :=
      lt_of_le_of_lt hb_le (ENNReal.lt_add_right hB hηne)
    rcases iInf_lt_iff.mp hb_lt with ⟨γ, hγ⟩
    have hyγ : Vγ γ x ∈ Vγ γ '' Metric.closedBall (0 : X) 1 := ⟨x, hx, rfl⟩
    rcases hCcover γ hyγ with ⟨z, hzC, hz⟩
    have happrox : edist (V x) (Vγ γ x) < B + η := by
      rw [edist_dist, dist_eq_norm]
      exact hγ
    have hsum : (B + η) + (A + η) = A + B + ε := by
      calc
        (B + η) + (A + η) = B + (η + (A + η)) := by rw [add_assoc]
        _ = B + (A + (η + η)) := by
          congr 1
          calc
            η + (A + η) = (η + A) + η := by rw [← add_assoc]
            _ = (A + η) + η := by rw [add_comm η A]
            _ = A + (η + η) := by rw [add_assoc]
        _ = B + A + (η + η) := by rw [← add_assoc]
        _ = A + B + (η + η) := by rw [add_comm B A]
        _ = A + B + ε := by rw [ENNReal.add_halves]
    have hzlt : edist (V x) z < (R : ENNReal) := by
      calc
        edist (V x) z ≤ edist (V x) (Vγ γ x) + edist (Vγ γ x) z :=
          edist_triangle _ _ _
        _ < (B + η) + (A + η) :=
          ENNReal.add_lt_add happrox (lt_of_le_of_lt hz (hrlt γ))
        _ = A + B + ε := hsum
        _ = (R : ENNReal) := hR_coe.symm
    exact ⟨z, Set.mem_iUnion.2 ⟨γ, hzC⟩, hzlt.le⟩
  have hCunion : (⋃ γ : Γ, C γ).encard ≤
      ((2 ^ (n + Nat.log 2 (Fintype.card Γ)) : ℕ) : ℕ∞) := by
    calc
      (⋃ γ : Γ, C γ).encard ≤ ∑ γ : Γ, (C γ).encard :=
        Set.encard_iUnion_le_of_fintype C
      _ ≤ Finset.univ.card • ((2 ^ (n - 1) : ℕ) : ℕ∞) := by
        exact Finset.sum_le_card_nsmul Finset.univ (fun γ : Γ => (C γ).encard)
          ((2 ^ (n - 1) : ℕ) : ℕ∞) (by intro γ _; exact hCcard γ)
      _ = (Fintype.card Γ : ℕ∞) * ((2 ^ (n - 1) : ℕ) : ℕ∞) := by
        rw [Finset.card_univ, nsmul_eq_mul]
      _ ≤ ((2 ^ (n + Nat.log 2 (Fintype.card Γ)) : ℕ) : ℕ∞) :=
        card_mul_two_pow_pred_le_pow hn
  have hnum : Metric.externalCoveringNumber R (V '' Metric.closedBall (0 : X) 1) ≤
      (2 ^ (n + Nat.log 2 (Fintype.card Γ) + 1 - 1) : ℕ∞) := by
    calc
      Metric.externalCoveringNumber R (V '' Metric.closedBall (0 : X) 1) ≤
          (⋃ γ : Γ, C γ).encard :=
        Metric.IsCover.externalCoveringNumber_le_encard hVcover
      _ ≤ ((2 ^ (n + Nat.log 2 (Fintype.card Γ)) : ℕ) : ℕ∞) := hCunion
      _ = (2 ^ (n + Nat.log 2 (Fintype.card Γ) + 1 - 1) : ℕ∞) := rfl
  calc
    e (n + Nat.log 2 (Fintype.card Γ) + 1) V ≤ (R : ENNReal) := by
      exact iInf_covering_radius_le hRpos hnum
    _ = A + B + ε := hR_coe

end Rollout_p1136_entropy_number_approximation

namespace Rollout_p1299_convexpolytope_trace_latticeembedding

/- accepted add_to_file helper 1 -/
lemma Convex.sum_mem_divisionRing
    {R E ι : Type*} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup E] [Module R E]
    {s : Set E} (hs : Convex R s) {t : Finset ι} {w : ι → R} {z : ι → E}
    (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1)
    (hz : ∀ i ∈ t, z i ∈ s) :
    ∑ i ∈ t, w i • z i ∈ s := by
  classical
  induction t using Finset.induction generalizing w with
  | empty =>
      simp at h₁
  | insert i t hi ih =>
      have hsum : w i + ∑ j ∈ t, w j = 1 := by
        simpa [hi] using h₁
      by_cases hwi : w i = 1
      · have hsumt : ∑ j ∈ t, w j = 0 := by
          have : 1 + ∑ j ∈ t, w j = 1 := by simpa [hwi] using hsum
          exact add_eq_left.mp this
        have hzero : ∀ j ∈ t, w j = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => h₀ j (Finset.mem_insert_of_mem hj))).mp hsumt
        have hweighted_zero : ∑ j ∈ t, w j • z j = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          rw [hzero j hj, zero_smul]
        have hzmem : z i ∈ s := hz i (Finset.mem_insert_self i t)
        rw [Finset.sum_insert hi, hweighted_zero, hwi, one_smul, add_zero]
        exact hzmem
      · set r : R := ∑ j ∈ t, w j with hrdef
        have hrnonneg : 0 ≤ r := by
          rw [hrdef]
          exact Finset.sum_nonneg (fun j hj => h₀ j (Finset.mem_insert_of_mem hj))
        have hwile : w i ≤ 1 := by
          rw [← hsum]
          exact le_add_of_nonneg_right hrnonneg
        have hwilt : w i < 1 := lt_of_le_of_ne hwile hwi
        have hsum' : r + w i = 1 := by
          simpa [hrdef, add_comm] using hsum
        have hr_eq : r = 1 - w i := eq_sub_of_add_eq hsum'
        have hwi_eq : w i = 1 - r := eq_sub_of_add_eq hsum
        have hrle : r ≤ 1 := by
          rw [← hsum']
          exact le_add_of_nonneg_right (h₀ i (Finset.mem_insert_self i t))
        have hrpos : 0 < r := by
          rw [hr_eq]
          exact sub_pos.mpr hwilt
        let w' : ι → R := fun j => r⁻¹ * w j
        have hw'₀ : ∀ j ∈ t, 0 ≤ w' j := by
          intro j hj
          exact mul_nonneg (inv_nonneg.mpr hrnonneg)
            (h₀ j (Finset.mem_insert_of_mem hj))
        have hw'₁ : ∑ j ∈ t, w' j = 1 := by
          calc
            ∑ j ∈ t, w' j = r⁻¹ * r := by
              rw [hrdef]
              exact (Finset.mul_sum t w r⁻¹).symm
            _ = 1 := inv_mul_cancel₀ hrpos.ne'
        have hy : ∑ j ∈ t, w' j • z j ∈ s :=
          ih (fun j hj => hw'₀ j hj) hw'₁ (fun j hj => hz j (Finset.mem_insert_of_mem hj))
        have hrest : ∑ j ∈ t, w j • z j = r • ∑ j ∈ t, w' j • z j := by
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          calc
            w j • z j = ((r * r⁻¹) * w j) • z j := by
              rw [mul_inv_cancel₀ hrpos.ne', one_mul]
            _ = (r * (r⁻¹ * w j)) • z j := by rw [mul_assoc]
            _ = r • ((r⁻¹ * w j) • z j) := mul_smul r (r⁻¹ * w j) (z j)
            _ = r • (w' j • z j) := rfl
        rw [Finset.sum_insert hi, hrest, hwi_eq]
        exact hs (hz i (Finset.mem_insert_self i t)) hy (sub_nonneg.mpr hrle) hrnonneg
          (sub_add_cancel 1 r)

/- accepted add_to_file helper 2 -/
lemma convexHull_eq_divisionRing
    {R E : Type*} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup E] [Module R E] (s : Set E) :
    convexHull R s =
      {x | ∃ (ι : Type) (t : Finset ι) (w : ι → R) (z : ι → E),
        (∀ i ∈ t, 0 ≤ w i) ∧ (∑ i ∈ t, w i = 1) ∧
        (∀ i ∈ t, z i ∈ s) ∧ (∑ i ∈ t, w i • z i) = x} := by
  classical
  apply Set.Subset.antisymm
  · apply convexHull_min
    · intro x hx
      refine ⟨PUnit, {PUnit.unit}, fun _ => 1, fun _ => x, ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · simpa using hx
      · simp
    · intro x hx y hy a b ha hb hab
      rcases hx with ⟨ιx, tx, wx, zx, hwx₀, hwx₁, hzx, hxeq⟩
      rcases hy with ⟨ιy, ty, wy, zy, hwy₀, hwy₁, hzy, hyeq⟩
      refine ⟨ιx ⊕ ιy, tx.disjSum ty,
        Sum.elim (fun i => a * wx i) (fun j => b * wy j), Sum.elim zx zy,
        ?_, ?_, ?_, ?_⟩
      · intro k hk
        rcases Finset.mem_disjSum.mp hk with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
        · exact mul_nonneg ha (hwx₀ i hi)
        · exact mul_nonneg hb (hwy₀ j hj)
      · simp only [Finset.sum_disjSum, Sum.elim_inl, Sum.elim_inr]
        rw [← Finset.mul_sum tx wx a, hwx₁]
        rw [← Finset.mul_sum ty wy b, hwy₁]
        simpa using hab
      · intro k hk
        rcases Finset.mem_disjSum.mp hk with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
        · exact hzx i hi
        · exact hzy j hj
      · calc
          (∑ k ∈ tx.disjSum ty,
              Sum.elim (fun i => a * wx i) (fun j => b * wy j) k • Sum.elim zx zy k)
              = a • (∑ i ∈ tx, wx i • zx i) + b • (∑ j ∈ ty, wy j • zy j) := by
                simp only [Finset.sum_disjSum, Sum.elim_inl, Sum.elim_inr]
                congr 1
                · rw [Finset.smul_sum]
                  apply Finset.sum_congr rfl
                  intro i hi
                  exact mul_smul a (wx i) (zx i)
                · rw [Finset.smul_sum]
                  apply Finset.sum_congr rfl
                  intro j hj
                  exact mul_smul b (wy j) (zy j)
          _ = a • x + b • y := by rw [hxeq, hyeq]
  · intro x hx
    rcases hx with ⟨ι, t, w, z, hw₀, hw₁, hz, hxeq⟩
    rw [← hxeq]
    exact Convex.sum_mem_divisionRing (convex_convexHull R s) hw₀ hw₁
      (fun i hi => subset_convexHull R s (hz i hi))

/- accepted add_to_file helper 3 -/
lemma mem_convexHull_finset_divisionRing
    {R E : Type*} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup E] [Module R E] {s : Finset E} {x : E} :
    x ∈ convexHull R (↑s : Set E) ↔
      ∃ w : E → R, (∀ y ∈ s, 0 ≤ w y) ∧ (∑ y ∈ s, w y = 1) ∧
        (∑ y ∈ s, w y • y) = x := by
  classical
  constructor
  · intro hx
    rw [convexHull_eq_divisionRing (↑s : Set E)] at hx
    rcases hx with ⟨ι, t, u, z, hu₀, hu₁, hz, hxeq⟩
    let w : E → R := fun y => ∑ i ∈ t.filter (fun i => z i = y), u i
    refine ⟨w, ?_, ?_, ?_⟩
    · intro y hy
      exact Finset.sum_nonneg (fun i hi => hu₀ i (Finset.mem_filter.mp hi).1)
    · calc
        ∑ y ∈ s, w y = ∑ y ∈ s, ∑ i ∈ t.filter (fun i => z i = y), u i := rfl
        _ = ∑ i ∈ t, u i := by
          exact Finset.sum_fiberwise_of_maps_to (fun i hi => by simpa using hz i hi) u
        _ = 1 := hu₁
    · calc
        ∑ y ∈ s, w y • y
            = ∑ y ∈ s, ∑ i ∈ t.filter (fun i => z i = y), u i • z i := by
              apply Finset.sum_congr rfl
              intro y hy
              calc
                w y • y = (∑ i ∈ t.filter (fun i => z i = y), u i) • y := rfl
                _ = ∑ i ∈ t.filter (fun i => z i = y), u i • y := Finset.sum_smul
                _ = ∑ i ∈ t.filter (fun i => z i = y), u i • z i := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [Finset.mem_filter] at hi
                  rw [hi.2]
        _ = ∑ i ∈ t, u i • z i := by
          exact Finset.sum_fiberwise_of_maps_to (fun i hi => by simpa using hz i hi)
            (fun i => u i • z i)
        _ = x := hxeq
  · intro hx
    rcases hx with ⟨w, hw₀, hw₁, hxeq⟩
    rw [← hxeq]
    exact Convex.sum_mem_divisionRing (convex_convexHull R (↑s : Set E)) hw₀ hw₁
      (fun y hy => subset_convexHull R (↑s : Set E) (by simpa using hy))

/- accepted add_to_file helper 4 -/
lemma exists_convexCombination_coeff_lt_one_divisionRing
    {R E : Type*} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup E] [Module R E]
    {s : Finset E} {a p : E} (ha : a ∈ s)
    (hp : p ∈ convexHull R (↑s : Set E)) (hpa : p ≠ a) :
    ∃ w : E → R, (∀ y ∈ s, 0 ≤ w y) ∧ (∑ y ∈ s, w y = 1) ∧
      (∑ y ∈ s, w y • y) = p ∧ w a < 1 := by
  classical
  rcases (mem_convexHull_finset_divisionRing.mp hp) with ⟨w, hw₀, hw₁, hwp⟩
  refine ⟨w, hw₀, hw₁, hwp, ?_⟩
  have hwale : w a ≤ 1 := by
    calc
      w a ≤ ∑ y ∈ s, w y := Finset.single_le_sum hw₀ ha
      _ = 1 := hw₁
  refine lt_of_le_of_ne hwale ?_
  intro hwa
  have herase_sum : ∑ y ∈ s.erase a, w y = 0 := by
    have h := Finset.sum_erase_add s w ha
    rw [hwa, hw₁] at h
    exact add_eq_right.mp h
  have hzero : ∀ y ∈ s.erase a, w y = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun y hy => hw₀ y (Finset.mem_of_mem_erase hy))).mp herase_sum
  have hsum_single : ∑ y ∈ s, w y • y = w a • a := by
    apply Finset.sum_eq_single_of_mem a ha
    intro y hy hya
    have hyerase : y ∈ s.erase a := Finset.mem_erase.mpr ⟨hya, hy⟩
    rw [hzero y hyerase, zero_smul]
  have : p = a := by
    rw [← hwp, hsum_single, hwa, one_smul]
  exact hpa this

/- accepted add_to_file helper 5 -/
lemma mem_convexHull_erase_of_combination_self_divisionRing
    {R E : Type*} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup E] [Module R E] [DecidableEq E]
    {s : Finset E} {a : E} (ha : a ∈ s) {w : E → R}
    (hw₀ : ∀ y ∈ s, 0 ≤ w y) (hw₁ : ∑ y ∈ s, w y = 1)
    (hwa : w a < 1) (hsum : ∑ y ∈ s, w y • y = a) :
    a ∈ convexHull R (↑(s.erase a) : Set E) := by
  classical
  set r : R := 1 - w a with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]
    exact sub_pos.mpr hwa
  let v : E → R := fun y => r⁻¹ * w y
  have hv₀ : ∀ y ∈ s.erase a, 0 ≤ v y := by
    intro y hy
    exact mul_nonneg (inv_nonneg.mpr hrpos.le)
      (hw₀ y (Finset.mem_of_mem_erase hy))
  have hsum_erase_w : ∑ y ∈ s.erase a, w y = r := by
    rw [hrdef, Finset.sum_erase_eq_sub ha, hw₁]
  have hv₁ : ∑ y ∈ s.erase a, v y = 1 := by
    calc
      ∑ y ∈ s.erase a, v y = r⁻¹ * ∑ y ∈ s.erase a, w y := by
        exact (Finset.mul_sum (s.erase a) w r⁻¹).symm
      _ = r⁻¹ * r := by rw [hsum_erase_w]
      _ = 1 := inv_mul_cancel₀ hrpos.ne'
  have hweighted_erase : ∑ y ∈ s.erase a, w y • y = r • a := by
    have hdecomp := Finset.sum_erase_add s (fun y => w y • y) ha
    rw [hsum] at hdecomp
    calc
      ∑ y ∈ s.erase a, w y • y = a - w a • a := eq_sub_of_add_eq hdecomp
      _ = (1 : R) • a - w a • a := by rw [one_smul]
      _ = (1 - w a) • a := (sub_smul (1 : R) (w a) a).symm
      _ = r • a := rfl
  have hvsum : ∑ y ∈ s.erase a, v y • y = a := by
    calc
      ∑ y ∈ s.erase a, v y • y
          = ∑ y ∈ s.erase a, r⁻¹ • (w y • y) := by
            apply Finset.sum_congr rfl
            intro y hy
            exact mul_smul r⁻¹ (w y) y
      _ = r⁻¹ • ∑ y ∈ s.erase a, w y • y := (Finset.smul_sum).symm
      _ = r⁻¹ • (r • a) := by rw [hweighted_erase]
      _ = (r⁻¹ * r) • a := (mul_smul r⁻¹ r a).symm
      _ = a := by rw [inv_mul_cancel₀ hrpos.ne', one_smul]
  exact mem_convexHull_finset_divisionRing.mpr ⟨v, hv₀, hv₁, hvsum⟩

/- accepted add_to_file helper 6 -/
lemma mem_convexHull_erase_of_mem_openSegment_left_ne_divisionRing
    {R E : Type*} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup E] [Module R E] [DecidableEq E]
    {s : Finset E} {a x₁ x₂ : E} (ha : a ∈ s)
    (hx₁ : x₁ ∈ convexHull R (↑s : Set E))
    (hx₂ : x₂ ∈ convexHull R (↑s : Set E))
    (hseg : a ∈ openSegment R x₁ x₂) (hx₁a : x₁ ≠ a) :
    a ∈ convexHull R (↑(s.erase a) : Set E) := by
  classical
  rcases hseg with ⟨c₁, c₂, hc₁, hc₂, hcsum, hcombo⟩
  rcases exists_convexCombination_coeff_lt_one_divisionRing ha hx₁ hx₁a with
    ⟨w₁, hw₁₀, hw₁₁, hw₁sum, hw₁a⟩
  rcases (mem_convexHull_finset_divisionRing.mp hx₂) with ⟨w₂, hw₂₀, hw₂₁, hw₂sum⟩
  let u : E → R := fun y => c₁ * w₁ y + c₂ * w₂ y
  have hu₀ : ∀ y ∈ s, 0 ≤ u y := by
    intro y hy
    exact add_nonneg (mul_nonneg hc₁.le (hw₁₀ y hy))
      (mul_nonneg hc₂.le (hw₂₀ y hy))
  have hu₁ : ∑ y ∈ s, u y = 1 := by
    calc
      ∑ y ∈ s, u y = ∑ y ∈ s, (c₁ * w₁ y + c₂ * w₂ y) := rfl
      _ = 1 := by
        rw [Finset.sum_add_distrib]
        rw [← Finset.mul_sum s w₁ c₁, hw₁₁]
        rw [← Finset.mul_sum s w₂ c₂, hw₂₁]
        simpa using hcsum
  have hw₂a : w₂ a ≤ 1 := by
    calc
      w₂ a ≤ ∑ y ∈ s, w₂ y := Finset.single_le_sum hw₂₀ ha
      _ = 1 := hw₂₁
  have hua : u a < 1 := by
    calc
      u a = c₁ * w₁ a + c₂ * w₂ a := rfl
      _ < c₁ * 1 + c₂ * 1 :=
        add_lt_add_of_lt_of_le
          (mul_lt_mul_of_pos_left hw₁a hc₁)
          (mul_le_mul_of_nonneg_left hw₂a hc₂.le)
      _ = 1 := by simpa using hcsum
  have husum : ∑ y ∈ s, u y • y = a := by
    calc
      ∑ y ∈ s, u y • y = ∑ y ∈ s, (c₁ * w₁ y + c₂ * w₂ y) • y := rfl
      _ = ∑ y ∈ s, (c₁ • (w₁ y • y) + c₂ • (w₂ y • y)) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [add_smul, mul_smul, mul_smul]
      _ = c₁ • (∑ y ∈ s, w₁ y • y) + c₂ • (∑ y ∈ s, w₂ y • y) := by
        rw [Finset.sum_add_distrib, Finset.smul_sum, Finset.smul_sum]
      _ = c₁ • x₁ + c₂ • x₂ := by rw [hw₁sum, hw₂sum]
      _ = a := hcombo
  exact mem_convexHull_erase_of_combination_self_divisionRing ha hu₀ hu₁ hua husum

/- accepted add_to_file helper 7 -/
lemma convexHull_erase_eq_of_not_extremePoint_divisionRing
    {R E : Type*} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup E] [Module R E] [DecidableEq E]
    {s : Finset E} {a : E} (ha : a ∈ s)
    (hne : a ∉ Set.extremePoints R (convexHull R (↑s : Set E))) :
    convexHull R (↑(s.erase a) : Set E) = convexHull R (↑s : Set E) := by
  classical
  have haP : a ∈ convexHull R (↑s : Set E) :=
    subset_convexHull R (↑s : Set E) (by simpa using ha)
  rw [mem_extremePoints] at hne
  push Not at hne
  rcases hne haP with ⟨x₁, hx₁, x₂, hx₂, hseg, hnot⟩
  have hamem : a ∈ convexHull R (↑(s.erase a) : Set E) := by
    by_cases hx₁a : x₁ = a
    · have hx₂a : x₂ ≠ a := hnot hx₁a
      have hseg' : a ∈ openSegment R x₂ x₁ := by
        rwa [openSegment_symm]
      exact mem_convexHull_erase_of_mem_openSegment_left_ne_divisionRing
        ha hx₂ hx₁ hseg' hx₂a
    · exact mem_convexHull_erase_of_mem_openSegment_left_ne_divisionRing
        ha hx₁ hx₂ hseg hx₁a
  apply Set.Subset.antisymm
  · exact convexHull_mono (by intro y hy; simpa using (Finset.erase_subset a s hy))
  · apply convexHull_min
    · intro y hy
      by_cases hya : y = a
      · rwa [hya]
      · apply subset_convexHull R (↑(s.erase a) : Set E)
        exact (Finset.mem_erase (a := y) (b := a) (s := s)).mpr
          ⟨hya, by simpa using hy⟩
    · exact convex_convexHull R (↑(s.erase a) : Set E)

/- accepted add_to_file helper 8 -/
lemma convexHull_subset_convexHull_of_extremePoints_subset_divisionRing
    {R E : Type*} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup E] [Module R E] [DecidableEq E]
    {C : Set E} (s : Finset E)
    (hC : C ⊆ convexHull R (↑s : Set E))
    (hext : Set.extremePoints R (convexHull R (↑s : Set E)) ⊆ C) :
    convexHull R (↑s : Set E) ⊆ convexHull R C := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
      by_cases hall : ∀ a ∈ s, a ∈ C
      · exact convexHull_mono (by
          intro a ha
          exact hall a (by simpa using ha))
      · push Not at hall
        rcases hall with ⟨a, ha, haC⟩
        have haext : a ∉ Set.extremePoints R (convexHull R (↑s : Set E)) := by
          intro h
          exact haC (hext h)
        have herase : convexHull R (↑(s.erase a) : Set E) =
            convexHull R (↑s : Set E) :=
          convexHull_erase_eq_of_not_extremePoint_divisionRing ha haext
        have hC_erase : C ⊆ convexHull R (↑(s.erase a) : Set E) := by
          rw [herase]
          exact hC
        have hext_erase :
            Set.extremePoints R (convexHull R (↑(s.erase a) : Set E)) ⊆ C := by
          rw [herase]
          exact hext
        have hsub := ih (s.erase a) (Finset.erase_ssubset ha) hC_erase hext_erase
        rw [← herase]
        exact hsub

/- verified submission -/
theorem convexPolytope_trace_latticeEmbedding
    {F V L : Type*} [DivisionRing F] [LinearOrder F] [IsStrictOrderedRing F]
    [AddCommGroup V] [Module F V] [Lattice L]
    (φ : L → Set V) (Ω : Set V)
    (hpoly : ∀ x : L, ∃ A : Set V, A.Finite ∧ convexHull F A = φ x)
    (hinj : Function.Injective φ)
    (hmeet : ∀ x y : L, φ (x ⊓ y) = φ x ∩ φ y)
    (hjoin : ∀ x y : L, φ (x ⊔ y) = convexHull F (φ x ∪ φ y))
    (hextreme : ∀ x : L, Set.extremePoints F (φ x) ⊆ Ω) :
    let ψ : L → Set V := fun x => φ x ∩ Ω
    Function.Injective ψ ∧
      (∀ x : L, Ω ∩ convexHull F (ψ x) = ψ x) ∧
      (∀ x y : L, ψ (x ⊓ y) = ψ x ∩ ψ y) ∧
      (∀ x y : L, ψ (x ⊔ y) = Ω ∩ convexHull F (ψ x ∪ ψ y)) ∧
      ∀ x : L, convexHull F (ψ x) = φ x := by
  classical
  let ψ : L → Set V := fun x => φ x ∩ Ω
  have hconv : ∀ x : L, convexHull F (ψ x) = φ x := by
    intro x
    rcases hpoly x with ⟨A, hAfin, hA⟩
    let s : Finset V := hAfin.toFinset
    have hsA : (↑s : Set V) = A := hAfin.coe_toFinset
    have hφ : φ x = convexHull F (↑s : Set V) := by
      rw [hsA, ← hA]
    have hψ_sub : ψ x ⊆ convexHull F (↑s : Set V) := by
      intro p hp
      rw [← hφ]
      exact hp.1
    have hext_sub :
        Set.extremePoints F (convexHull F (↑s : Set V)) ⊆ ψ x := by
      intro p hp
      constructor
      · rw [hφ]
        exact extremePoints_subset hp
      · apply hextreme x
        simpa [hφ] using hp
    have hsub : convexHull F (↑s : Set V) ⊆ convexHull F (ψ x) :=
      convexHull_subset_convexHull_of_extremePoints_subset_divisionRing s hψ_sub hext_sub
    have hrev : convexHull F (ψ x) ⊆ convexHull F (↑s : Set V) := by
      apply convexHull_min hψ_sub
      exact convex_convexHull F (↑s : Set V)
    calc
      convexHull F (ψ x) = convexHull F (↑s : Set V) :=
        Set.Subset.antisymm hrev hsub
      _ = φ x := hφ.symm
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    apply hinj
    rw [← hconv x, ← hconv y, hxy]
  refine ⟨hψinj, ?_, ?_, ?_, hconv⟩
  · intro x
    rw [hconv x]
    ext p
    simp [and_comm]
  · intro x y
    ext p
    simp [hmeet, and_assoc, and_left_comm, and_comm]
  · intro x y
    have hunion : convexHull F (ψ x ∪ ψ y) = convexHull F (φ x ∪ φ y) := by
      apply Set.Subset.antisymm
      · apply convexHull_min
        · intro p hp
          rcases hp with hp | hp
          · exact subset_convexHull F (φ x ∪ φ y) (Or.inl hp.1)
          · exact subset_convexHull F (φ x ∪ φ y) (Or.inr hp.1)
        · exact convex_convexHull F (φ x ∪ φ y)
      · apply convexHull_min
        · intro p hp
          rcases hp with hp | hp
          · have hp' : p ∈ convexHull F (ψ x) := by
              rw [hconv x]
              exact hp
            exact convexHull_mono Set.subset_union_left hp'
          · have hp' : p ∈ convexHull F (ψ y) := by
              rw [hconv y]
              exact hp
            exact convexHull_mono Set.subset_union_right hp'
        · exact convex_convexHull F (ψ x ∪ ψ y)
    change φ (x ⊔ y) ∩ Ω = Ω ∩ convexHull F (ψ x ∪ ψ y)
    rw [hjoin, hunion]
    ext p
    simp [and_comm]

end Rollout_p1299_convexpolytope_trace_latticeembedding

namespace Rollout_p0252_reciprocal_eq_neg_one_pow_of_roots_abs_one

/- accepted add_to_file helper 1 -/

open Polynomial

lemma reverse_quadratic_unit (a : ℝ) :
    (X ^ 2 - C (2 * a) * X + C (1 : ℝ)).reverse =
      X ^ 2 - C (2 * a) * X + C (1 : ℝ) := by
  let q : Polynomial ℝ := X ^ 2 - C (2 * a) * X + C (1 : ℝ)
  have hdeg : q.natDegree = 2 := by
    dsimp [q]
    compute_degree!
  change q.reverse = q
  ext k
  rw [Polynomial.coeff_reverse, hdeg]
  by_cases hk : k ≤ 2
  · interval_cases k <;> simp [Polynomial.revAt_le, q, Polynomial.coeff_one]
  · have hkgt : 2 < k := Nat.lt_of_not_ge hk
    have hzero : q.coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      simpa [hdeg] using hkgt
    simp [Polynomial.revAt_eq_self_of_lt hkgt, hzero]

lemma reverse_X_sub_C_neg_one :
    (X - C (-1 : ℝ)).reverse = X - C (-1 : ℝ) := by
  let q : Polynomial ℝ := X - C (-1 : ℝ)
  have hdeg : q.natDegree = 1 := by
    dsimp [q]
    compute_degree!
  change q.reverse = q
  ext k
  rw [Polynomial.coeff_reverse, hdeg]
  by_cases hk : k ≤ 1
  · interval_cases k <;> simp [Polynomial.revAt_le, q, Polynomial.coeff_one]
  · have hkgt : 1 < k := Nat.lt_of_not_ge hk
    have hzero : q.coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      simpa [hdeg] using hkgt
    simp [Polynomial.revAt_eq_self_of_lt hkgt, hzero]

lemma reverse_X_sub_C_one_pow (n : ℕ) :
    ((X - C (1 : ℝ)) ^ n).reverse = ((-1 : ℝ) ^ n) • (X - C (1 : ℝ)) ^ n := by
  let A : Polynomial ℝ := X - C (1 : ℝ)
  have hbase : A.reverse = C (-1 : ℝ) * A := by
    have hdeg : A.natDegree = 1 := by
      dsimp [A]
      compute_degree!
    ext k
    rw [Polynomial.coeff_reverse, hdeg]
    by_cases hk : k ≤ 1
    · interval_cases k <;> simp [Polynomial.revAt_le, A, Polynomial.coeff_one]
    · have hkgt : 1 < k := Nat.lt_of_not_ge hk
      have hzero : A.coeff k = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        simpa [hdeg] using hkgt
      simp [Polynomial.revAt_eq_self_of_lt hkgt, hzero]
  have hrevpow : (A ^ n).reverse = A.reverse ^ n := by
    induction n with
    | zero =>
        change (C (1 : ℝ)).reverse = (C (1 : ℝ)) ^ 0
        rw [Polynomial.reverse_C]
        simp
    | succ n ih =>
        rw [pow_succ, Polynomial.reverse_mul_of_domain, ih, pow_succ]
  change (A ^ n).reverse = ((-1 : ℝ) ^ n) • A ^ n
  rw [hrevpow, hbase, mul_pow, ← map_pow, ← Polynomial.smul_eq_C_mul]

/- accepted add_to_file helper 2 -/
lemma isRoot_real_of_map_isRoot_of_im_eq_zero
    (f : Polynomial ℝ) {z : ℂ} (him : z.im = 0)
    (hz : (f.map (algebraMap ℝ ℂ)).IsRoot z) : f.IsRoot z.re := by
  let r := z.re
  have hzr : z = (r : ℂ) := by
    apply Complex.ext <;> simp [r, him]
  have hrootmap : (f.map (algebraMap ℝ ℂ)).IsRoot (r : ℂ) := by
    simpa [hzr] using hz
  rw [Polynomial.IsRoot.def, Polynomial.eval_map] at hrootmap
  have heval₂ := Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) r (p := f)
  have hmapzero : algebraMap ℝ ℂ (f.eval r) = 0 := by
    rw [show algebraMap ℝ ℂ r = (r : ℂ) by rfl] at heval₂
    exact heval₂ ▸ hrootmap
  rw [Polynomial.IsRoot.def]
  exact (RingHom.injective (algebraMap ℝ ℂ)) hmapzero

lemma aeval_eq_zero_of_map_isRoot
    (f : Polynomial ℝ) {z : ℂ}
    (hz : (f.map (algebraMap ℝ ℂ)).IsRoot z) :
    (Polynomial.aeval z) f = 0 := by
  rw [Polynomial.IsRoot.def, Polynomial.eval_map] at hz
  rw [Polynomial.aeval_def]
  exact hz

/- accepted add_to_file helper 3 -/
lemma reverse_eq_self_of_roots_norm_one_of_not_root_one
    (f : Polynomial ℝ) (hf : f ≠ 0)
    (hroots : ∀ z : ℂ, (f.map (algebraMap ℝ ℂ)).IsRoot z → ‖z‖ = 1)
    (h1 : ¬ f.IsRoot 1) :
    f.reverse = f := by
  let P : ℕ → Prop := fun n =>
    ∀ g : Polynomial ℝ, g.natDegree = n → g ≠ 0 →
      (∀ z : ℂ, (g.map (algebraMap ℝ ℂ)).IsRoot z → ‖z‖ = 1) →
      ¬ g.IsRoot 1 → g.reverse = g
  have H : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro g hdeg hg0 hgroots hg1
        by_cases hconst : g.natDegree = 0
        · rw [Polynomial.eq_C_of_natDegree_eq_zero hconst, Polynomial.reverse_C]
        · have hFdeg : (g.map (algebraMap ℝ ℂ)).degree ≠ 0 := by
            rw [Polynomial.degree_map, Polynomial.degree_eq_natDegree hg0]
            exact_mod_cast hconst
          obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hFdeg
          have hzn : ‖z‖ = 1 := hgroots z hz
          by_cases him : z.im = 0
          · have hrroot : g.IsRoot z.re :=
              isRoot_real_of_map_isRoot_of_im_eq_zero g him hz
            have habs : |z.re| = 1 := by
              have hzr : z = (z.re : ℂ) := by
                apply Complex.ext <;> simp [him]
              rw [hzr] at hzn
              simpa using hzn
            have hrneg : z.re = -1 := by
              rcases eq_or_eq_neg_of_abs_eq habs with hr | hr
              · exfalso
                exact hg1 (by rwa [hr] at hrroot)
              · exact hr
            have hdvd : X - C (-1 : ℝ) ∣ g := by
              rw [Polynomial.dvd_iff_isRoot]
              simpa [hrneg] using hrroot
            rcases hdvd with ⟨h, gh⟩
            have hh0 : h ≠ 0 := by
              intro hh
              apply hg0
              rw [gh, hh, mul_zero]
            have hroots_h : ∀ w : ℂ, (h.map (algebraMap ℝ ℂ)).IsRoot w → ‖w‖ = 1 := by
              intro w hw
              have hgw : (g.map (algebraMap ℝ ℂ)).IsRoot w := by
                rw [gh, Polynomial.map_mul]
                exact Polynomial.root_mul.2 (Or.inr hw)
              exact hgroots w hgw
            have h1_h : ¬ h.IsRoot 1 := by
              intro hh
              have hrootg : g.IsRoot 1 := by
                rw [gh]
                exact Polynomial.root_mul.2 (Or.inr hh)
              exact hg1 hrootg
            have hq0 : X - C (-1 : ℝ) ≠ 0 := (Polynomial.monic_X_sub_C _).ne_zero
            have hdegmul : g.natDegree = (X - C (-1 : ℝ)).natDegree + h.natDegree := by
              rw [gh, Polynomial.natDegree_mul hq0 hh0]
            have hqdeg : (X - C (-1 : ℝ)).natDegree = 1 := by
              compute_degree!
            have hhlt : h.natDegree < n := by
              rw [← hdeg, hdegmul, hqdeg]
              omega
            have hhrev : h.reverse = h :=
              ih h.natDegree hhlt h rfl hh0 hroots_h h1_h
            rw [gh, Polynomial.reverse_mul_of_domain, reverse_X_sub_C_neg_one, hhrev]
          · have haeval : (Polynomial.aeval z) g = 0 :=
              aeval_eq_zero_of_map_isRoot g hz
            have hdvd : X ^ 2 - C (2 * z.re) * X + C (1 : ℝ) ∣ g := by
              have h := Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero g haeval him
              have hnormsq : ‖z‖ ^ 2 = (1 : ℝ) := by
                rw [hzn]
                norm_num
              simpa [hnormsq] using h
            rcases hdvd with ⟨h, gh⟩
            have hh0 : h ≠ 0 := by
              intro hh
              apply hg0
              rw [gh, hh, mul_zero]
            have hroots_h : ∀ w : ℂ, (h.map (algebraMap ℝ ℂ)).IsRoot w → ‖w‖ = 1 := by
              intro w hw
              have hgw : (g.map (algebraMap ℝ ℂ)).IsRoot w := by
                rw [gh, Polynomial.map_mul]
                exact Polynomial.root_mul.2 (Or.inr hw)
              exact hgroots w hgw
            have h1_h : ¬ h.IsRoot 1 := by
              intro hh
              have hrootg : g.IsRoot 1 := by
                rw [gh]
                exact Polynomial.root_mul.2 (Or.inr hh)
              exact hg1 hrootg
            have hq0 : X ^ 2 - C (2 * z.re) * X + C (1 : ℝ) ≠ 0 := by
              have hdegq : (X ^ 2 - C (2 * z.re) * X + C (1 : ℝ)).natDegree = 2 := by
                compute_degree!
              intro hq
              rw [hq] at hdegq
              norm_num at hdegq
            have hdegmul : g.natDegree =
                (X ^ 2 - C (2 * z.re) * X + C (1 : ℝ)).natDegree + h.natDegree := by
              rw [gh, Polynomial.natDegree_mul hq0 hh0]
            have hqdeg : (X ^ 2 - C (2 * z.re) * X + C (1 : ℝ)).natDegree = 2 := by
              compute_degree!
            have hhlt : h.natDegree < n := by
              rw [← hdeg, hdegmul, hqdeg]
              omega
            have hhrev : h.reverse = h :=
              ih h.natDegree hhlt h rfl hh0 hroots_h h1_h
            rw [gh, Polynomial.reverse_mul_of_domain, reverse_quadratic_unit, hhrev]
  exact H f.natDegree f rfl hf hroots h1

/- verified submission -/
theorem reciprocal_eq_neg_one_pow_of_roots_abs_one
    (f : Polynomial ℝ) (n : ℕ) (hf : f ≠ 0)
    (hroots : ∀ z : ℂ, (f.map (algebraMap ℝ ℂ)).IsRoot z → ‖z‖ = 1)
    (hn : f.rootMultiplicity 1 = n) :
    f.reverse = ((-1 : ℝ) ^ n) • f := by
  let A : Polynomial ℝ := X - C (1 : ℝ)
  have hdvd : A ^ n ∣ f := by
    have h := Polynomial.pow_rootMultiplicity_dvd f (1 : ℝ)
    rwa [hn] at h
  rcases hdvd with ⟨g, hfg⟩
  have hg0 : g ≠ 0 := by
    intro hg
    apply hf
    rw [hfg, hg, mul_zero]
  have hnotg : ¬ g.IsRoot 1 := by
    intro hgroot
    have hlin : A ∣ g := by
      rw [Polynomial.dvd_iff_isRoot]
      exact hgroot
    rcases hlin with ⟨h, gh⟩
    have hbig : A ^ (n + 1) ∣ f := by
      use h
      rw [hfg, gh]
      change A ^ n * (A * h) = A ^ (n + 1) * h
      rw [pow_succ]
      ring
    have hnot := Polynomial.pow_rootMultiplicity_not_dvd hf (1 : ℝ)
    rw [hn] at hnot
    exact hnot hbig
  have hgroots : ∀ z : ℂ, (g.map (algebraMap ℝ ℂ)).IsRoot z → ‖z‖ = 1 := by
    intro z hz
    have hrootf : (f.map (algebraMap ℝ ℂ)).IsRoot z := by
      rw [hfg, Polynomial.map_mul]
      exact Polynomial.root_mul.2 (Or.inr hz)
    exact hroots z hrootf
  have hgrev : g.reverse = g :=
    reverse_eq_self_of_roots_norm_one_of_not_root_one g hg0 hgroots hnotg
  rw [hfg, Polynomial.reverse_mul_of_domain, reverse_X_sub_C_one_pow, hgrev, smul_mul_assoc]

end Rollout_p0252_reciprocal_eq_neg_one_pow_of_roots_abs_one

namespace Rollout_p0644_collapse_set_partialorder_iff_ordconnected

/- verified submission -/
theorem collapse_set_partialOrder_iff_ordConnected
    {P : Type*} [PartialOrder P] (B : Set P) (hB : B.Nonempty) :
    let Q := Sum {x : P // x ∉ B} Unit
    let r : Q → Q → Prop := fun x y =>
      match x, y with
      | Sum.inr _, Sum.inr _ => True
      | Sum.inr _, Sum.inl y => ∃ b ∈ B, b ≤ y.1
      | Sum.inl x, Sum.inr _ => ∃ b ∈ B, x.1 ≤ b
      | Sum.inl x, Sum.inl y =>
          x.1 ≤ y.1 ∨ ∃ b ∈ B, ∃ b' ∈ B, x.1 ≤ b ∧ b' ≤ y.1
    IsPartialOrder Q r ↔ B.OrdConnected := by
  let Q := Sum {x : P // x ∉ B} Unit
  let r : Q → Q → Prop := fun x y =>
      match x, y with
      | Sum.inr _, Sum.inr _ => True
      | Sum.inr _, Sum.inl y => ∃ b ∈ B, b ≤ y.1
      | Sum.inl x, Sum.inr _ => ∃ b ∈ B, x.1 ≤ b
      | Sum.inl x, Sum.inl y =>
          x.1 ≤ y.1 ∨ ∃ b ∈ B, ∃ b' ∈ B, x.1 ≤ b ∧ b' ≤ y.1
  change IsPartialOrder Q r ↔ B.OrdConnected
  have _ : B.Nonempty := hB
  constructor
  · intro hpo
    refine Set.OrdConnected.mk ?_
    intro x hx y hy z hz
    rcases Set.mem_Icc.mp hz with ⟨hxz, hzy⟩
    by_contra hzB
    let zq : {x : P // x ∉ B} := ⟨z, hzB⟩
    have hstar_z : r (Sum.inr ()) (Sum.inl zq) := ⟨x, hx, hxz⟩
    have hz_star : r (Sum.inl zq) (Sum.inr ()) := ⟨y, hy, hzy⟩
    have heq := hpo.antisymm (Sum.inr ()) (Sum.inl zq) hstar_z hz_star
    cases heq
  · intro hconn
    have hconvex : ∀ {x y z : P}, x ∈ B → y ∈ B → x ≤ z → z ≤ y → z ∈ B := by
      intro x y z hx hy hxz hzy
      exact hconn.out' hx hy (Set.mem_Icc.mpr ⟨hxz, hzy⟩)
    have hrefl : ∀ q : Q, r q q := by
      intro q
      cases q with
      | inl x =>
          exact Or.inl le_rfl
      | inr u =>
          trivial
    have htrans : ∀ a b c : Q, r a b → r b c → r a c := by
      intro a b c hab hbc
      cases a with
      | inl x =>
          cases b with
          | inl y =>
              cases c with
              | inl z =>
                  rcases hab with hxy | ⟨b₁, hb₁, b₂, hb₂, hxb₁, hb₂y⟩
                  · rcases hbc with hyz | ⟨c₁, hc₁, c₂, hc₂, hyc₁, hc₂z⟩
                    · exact Or.inl (le_trans hxy hyz)
                    · exact Or.inr ⟨c₁, hc₁, c₂, hc₂, le_trans hxy hyc₁, hc₂z⟩
                  · rcases hbc with hyz | ⟨c₁, hc₁, c₂, hc₂, hyc₁, hc₂z⟩
                    · exact Or.inr ⟨b₁, hb₁, b₂, hb₂, hxb₁, le_trans hb₂y hyz⟩
                    · exact Or.inr ⟨b₁, hb₁, c₂, hc₂, hxb₁, hc₂z⟩
              | inr z =>
                  rcases hbc with ⟨c', hc', hyc'⟩
                  rcases hab with hxy | ⟨b₁, hb₁, b₂, hb₂, hxb₁, hb₂y⟩
                  · exact ⟨c', hc', le_trans hxy hyc'⟩
                  · exact ⟨b₁, hb₁, hxb₁⟩
          | inr y =>
              cases c with
              | inl z =>
                  rcases hab with ⟨b₁, hb₁, hxb₁⟩
                  rcases hbc with ⟨b₂, hb₂, hb₂z⟩
                  exact Or.inr ⟨b₁, hb₁, b₂, hb₂, hxb₁, hb₂z⟩
              | inr z =>
                  exact hab
      | inr x =>
          cases b with
          | inl y =>
              cases c with
              | inl z =>
                  rcases hbc with hyz | ⟨c₁, hc₁, c₂, hc₂, hyc₁, hc₂z⟩
                  · rcases hab with ⟨b', hb', hb'y⟩
                    exact ⟨b', hb', le_trans hb'y hyz⟩
                  · exact ⟨c₂, hc₂, hc₂z⟩
              | inr z =>
                  trivial
          | inr y =>
              exact hbc
    have hanti : ∀ a b : Q, r a b → r b a → a = b := by
      intro a b hab hba
      cases a with
      | inl x =>
          cases b with
          | inl y =>
              rcases hab with hxy | ⟨b₁, hb₁, b₂, hb₂, hxb₁, hb₂y⟩
              · rcases hba with hyx | ⟨c₁, hc₁, c₂, hc₂, hyc₁, hc₂x⟩
                · exact congrArg Sum.inl (Subtype.ext (le_antisymm hxy hyx))
                · exfalso
                  exact y.2 (hconvex hc₂ hc₁ (le_trans hc₂x hxy) hyc₁)
              · rcases hba with hyx | ⟨c₁, hc₁, c₂, hc₂, hyc₁, hc₂x⟩
                · exfalso
                  exact x.2 (hconvex hb₂ hb₁ (le_trans hb₂y hyx) hxb₁)
                · exfalso
                  exact y.2 (hconvex hb₂ hc₁ hb₂y hyc₁)
          | inr y =>
              rcases hab with ⟨b₁, hb₁, hxb₁⟩
              rcases hba with ⟨b₂, hb₂, hb₂x⟩
              exfalso
              exact x.2 (hconvex hb₂ hb₁ hb₂x hxb₁)
      | inr x =>
          cases b with
          | inl y =>
              rcases hab with ⟨b₁, hb₁, hb₁y⟩
              rcases hba with ⟨b₂, hb₂, hyb₂⟩
              exfalso
              exact y.2 (hconvex hb₁ hb₂ hb₁y hyb₂)
          | inr y =>
              rfl
    letI : Std.Refl r := ⟨hrefl⟩
    letI : IsTrans Q r := ⟨htrans⟩
    letI : IsPreorder Q r := IsPreorder.mk
    letI : Std.Antisymm r := ⟨hanti⟩
    exact IsPartialOrder.mk

end Rollout_p0644_collapse_set_partialorder_iff_ordconnected

namespace Rollout_p1227_discrete_add_subgroup_covering

/- accepted add_to_file helper 1 -/

open scoped Pointwise Topology
open Filter Set

lemma cover_nat_scale_of_local_cover
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K : Set E) (L : AddSubgroup E)
    (hK_zero : (0 : E) ∈ K)
    (hK_star : StarConvex ℝ 0 K)
    (ε ε₁ : ℝ) (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (q : ℕ) (hq_pos : 0 < q)
    (hq_recip : (q : ℝ) + 1 > 1 / (1 - ε))
    (hε₁ : ε₁ = (q : ℝ) * ε)
    (hcover : K ⊆ Set.image2 (· + ·) (L : Set E)
      ((fun x => ε • x) '' K)) :
    ∀ m : ℕ,
      (fun x => (m : ℝ) • x) '' K ⊆
        Set.image2 (· + ·) (L : Set E)
          ((fun x => ε₁ • x) '' K) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro y hy
      rcases hy with ⟨k, hk, rfl⟩
      have hkcover := hcover hk
      rw [Set.mem_image2] at hkcover
      rcases hkcover with ⟨l, hl, z, hz, hlz⟩
      rcases hz with ⟨k', hk', rfl⟩
      by_cases hmq : m ≤ q
      · let k₂ : E := ((m : ℝ) / (q : ℝ)) • k'
        have hk₂ : k₂ ∈ K := by
          dsimp [k₂]
          apply hK_star.smul_mem hk'
          · positivity
          · have hm : (m : ℝ) ≤ q := by exact_mod_cast hmq
            have hq : (0 : ℝ) < q := by exact_mod_cast hq_pos
            exact (div_le_one hq).2 hm
        refine Set.mem_image2.2 ⟨m • l, AddSubgroup.nsmul_mem L hl m,
          ε₁ • k₂, Set.mem_image_of_mem (fun x => ε₁ • x) hk₂, ?_⟩
        change m • l + ε₁ • k₂ = (m : ℝ) • k
        rw [← hlz]
        simp only [hε₁]
        rw [smul_add]
        congr 1
        · norm_cast
        · dsimp [k₂]
          rw [← smul_assoc, ← smul_assoc]
          congr 1
          change ((q : ℝ) * ε) * ((m : ℝ) * (q : ℝ)⁻¹) = (m : ℝ) * ε
          field_simp [show (q : ℝ) ≠ 0 by positivity]
      · have hm_pos : 0 < m := lt_trans hq_pos (Nat.not_le.mp hmq)
        let r : ℕ := ⌈(m : ℝ) * ε⌉₊
        have hmr_real : (m : ℝ) * ε < (m : ℝ) - 1 := by
          have hmgt : (m : ℝ) > 1 / (1 - ε) := by
            have hmq_nat : q + 1 ≤ m := Nat.succ_le_of_lt (Nat.not_le.mp hmq)
            have hm_q : (q : ℝ) + 1 ≤ m := by exact_mod_cast hmq_nat
            exact lt_of_lt_of_le hq_recip hm_q
          have hden : 0 < 1 - ε := sub_pos.mpr hε_lt_one
          have hmreal : (0 : ℝ) < m := by positivity
          have h1 : (1 : ℝ) / m < 1 - ε := (one_div_lt hmreal hden).2 hmgt
          have hmul := mul_lt_mul_of_pos_left h1 hmreal
          field_simp [show (m : ℝ) ≠ 0 by positivity] at hmul
          nlinarith
        have hrlt : r < m := by
          have hle : r ≤ m - 1 := by
            rw [Nat.ceil_le]
            have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
              rw [Nat.cast_sub (Nat.succ_le_iff.mpr hm_pos)]
              simp
            rw [hcast]
            exact le_of_lt hmr_real
          exact lt_of_le_of_lt hle (Nat.pred_lt hm_pos.ne')
        have hzscale : (m * ε : ℝ) • k' ∈ (fun x => (r : ℝ) • x) '' K := by
          by_cases hr : r = 0
          · have hnonpos : (m : ℝ) * ε ≤ 0 := by
              have hle0 : (m : ℝ) * ε ≤ (r : ℝ) := Nat.le_ceil _
              rw [hr] at hle0
              simpa using hle0
            have hzero : (m : ℝ) * ε = 0 := le_antisymm hnonpos (mul_nonneg (by positivity) hε_pos.le)
            refine ⟨0, hK_zero, ?_⟩
            simp [hzero]
          · refine ⟨((m * ε : ℝ) / r) • k', ?_, ?_⟩
            · apply hK_star.smul_mem hk'
              · positivity
              · have hceil : (m : ℝ) * ε ≤ r := Nat.le_ceil _
                have hrpos : (0 : ℝ) < r := by positivity
                exact (div_le_one hrpos).2 hceil
            · change (r : ℝ) • (((m * ε : ℝ) / r) • k') = (m * ε : ℝ) • k'
              rw [← smul_assoc]
              congr 1
              change (r : ℝ) * ((m * ε : ℝ) * (r : ℝ)⁻¹) = (m * ε : ℝ)
              field_simp [show (r : ℝ) ≠ 0 by positivity]
        have hzcover := ih r hrlt hzscale
        rw [Set.mem_image2] at hzcover
        rcases hzcover with ⟨l₂, hl₂, z₂, hz₂, hl₂z⟩
        rcases hz₂ with ⟨k₂, hk₂, rfl⟩
        refine Set.mem_image2.2 ⟨m • l + l₂,
          L.add_mem (AddSubgroup.nsmul_mem L hl m) hl₂,
          ε₁ • k₂, Set.mem_image_of_mem (fun x => ε₁ • x) hk₂, ?_⟩
        change m • l + l₂ + ε₁ • k₂ = (m : ℝ) • k
        rw [← hlz]
        calc
          m • l + l₂ + ε₁ • k₂ = (m : ℝ) • l + (l₂ + ε₁ • k₂) := by
            norm_cast
            abel
          _ = (m : ℝ) • l + (m * ε : ℝ) • k' := by rw [hl₂z]
          _ = (m : ℝ) • (l + ε • k') := by
            simp [smul_add, smul_smul, mul_comm]

lemma exists_nat_scale_mem_of_zero_mem_interior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (hK_nhds : (0 : E) ∈ interior K) :
    ∀ x : E, ∃ m : ℕ, x ∈ (fun y => (m : ℝ) • y) '' K := by
  intro x
  have hcont : ContinuousAt (fun c : ℝ => c • x) 0 := by
    exact continuousAt_id.smul continuousAt_const
  have hnhds : interior K ∈ 𝓝 (0 : E) := isOpen_interior.mem_nhds hK_nhds
  have hev : ∀ᶠ c : ℝ in 𝓝 0, c • x ∈ interior K := by
    have ht : Tendsto (fun c : ℝ => c • x) (𝓝 0) (𝓝 (0 : E)) := by
      simpa using hcont.tendsto
    exact ht hnhds
  rw [Metric.eventually_nhds_iff] at hev
  rcases hev with ⟨δ, hδ, hδ'⟩
  rcases exists_nat_one_div_lt hδ with ⟨m, hm⟩
  let M : ℕ := m + 1
  have hdist : dist ((1 : ℝ) / M) 0 < δ := by
    rw [Real.dist_eq, sub_zero]
    have hpos : (0 : ℝ) < 1 / M := by positivity
    rw [abs_of_pos hpos]
    simpa [M] using hm
  have hmem : ((1 : ℝ) / M) • x ∈ interior K := hδ' hdist
  refine ⟨M, ((1 : ℝ) / M) • x, interior_subset hmem, ?_⟩
  change (M : ℝ) • (((1 : ℝ) / M) • x) = x
  rw [← smul_assoc]
  change ((M : ℝ) * (1 / M)) • x = x
  have hcoeff : (M : ℝ) * (1 / M) = 1 := by
    field_simp [show (M : ℝ) ≠ 0 by positivity]
  rw [hcoeff, one_smul]

/- verified submission -/
theorem discrete_add_subgroup_covering
    (n : ℕ) (hn : 1 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (L : AddSubgroup (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (hK_compact : IsCompact K)
    (hK_nhds : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K)
    (hK_star : StarConvex ℝ 0 K)
    (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) (hε₀_lt_one : ε₀ < 1)
    (hcover : K ⊆ Set.image2 (· + ·) (L : Set (EuclideanSpace ℝ (Fin n)))
      ((fun x => ε₀ • x) '' K)) :
    let ε₁ : ℝ := (((⌊ε₀ / (1 - ε₀)⌋ : ℤ) + 1 : ℤ) : ℝ) * ε₀
    Set.univ = Set.image2 (· + ·) (L : Set (EuclideanSpace ℝ (Fin n)))
      ((fun x => ε₁ • x) '' K) := by
  let q : ℕ := (((⌊ε₀ / (1 - ε₀)⌋ : ℤ) + 1 : ℤ).toNat)
  let ε₁ : ℝ := (((⌊ε₀ / (1 - ε₀)⌋ : ℤ) + 1 : ℤ) : ℝ) * ε₀
  change Set.univ = Set.image2 (· + ·) (L : Set (EuclideanSpace ℝ (Fin n)))
      ((fun x => ε₁ • x) '' K)
  have ha_pos : 0 < ε₀ / (1 - ε₀) := by
    exact div_pos hε₀_pos (sub_pos.mpr hε₀_lt_one)
  have hfloor_nonneg : 0 ≤ ⌊ε₀ / (1 - ε₀)⌋ := Int.floor_nonneg.mpr ha_pos.le
  have hq_nonneg_int : 0 ≤ (⌊ε₀ / (1 - ε₀)⌋ : ℤ) + 1 := by omega
  have hq_pos : 0 < q := by
    dsimp [q]
    omega
  have hq_cast_int : (q : ℤ) = (⌊ε₀ / (1 - ε₀)⌋ : ℤ) + 1 := by
    dsimp [q]
    exact Int.toNat_of_nonneg hq_nonneg_int
  have hq_cast : (q : ℝ) = (((⌊ε₀ / (1 - ε₀)⌋ : ℤ) + 1 : ℤ) : ℝ) := by
    exact_mod_cast hq_cast_int
  have hrecip : 1 / (1 - ε₀) = ε₀ / (1 - ε₀) + 1 := by
    field_simp [sub_ne_zero.mpr hε₀_lt_one.ne']
    ring
  have hq_recip : (q : ℝ) + 1 > 1 / (1 - ε₀) := by
    rw [hrecip, hq_cast]
    have hfloor := Int.lt_floor_add_one (ε₀ / (1 - ε₀))
    norm_num at hfloor ⊢
  have hε₁ : ε₁ = (q : ℝ) * ε₀ := by
    dsimp [ε₁]
    rw [hq_cast]
  have hscale :=
    cover_nat_scale_of_local_cover K L (interior_subset hK_nhds) hK_star
      ε₀ ε₁ hε₀_pos hε₀_lt_one q hq_pos hq_recip hε₁ hcover
  ext x
  constructor
  · intro _
    rcases exists_nat_scale_mem_of_zero_mem_interior K hK_nhds x with ⟨m, hm⟩
    exact hscale m hm
  · intro _
    simp

end Rollout_p1227_discrete_add_subgroup_covering

namespace Rollout_p0412_almosttrivial_and_almostfinite_of_shortexa

/- accepted add_to_file helper 1 -/
lemma torsion_map_le {R A B : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
    (u : A →ₗ[R] B) :
    Submodule.torsion R A ≤ Submodule.comap u (Submodule.torsion R B) := by
  intro a ha
  change u a ∈ Submodule.torsion R B
  rw [Submodule.mem_torsion_iff] at ha ⊢
  rcases ha with ⟨r, hr⟩
  use r
  rw [Submonoid.smul_def] at hr ⊢
  rw [← map_smul, hr, map_zero]

lemma torsion_reflect_of_injective {R A B : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
    (u : A →ₗ[R] B) (hu : Function.Injective u) {a : A}
    (ha : u a ∈ Submodule.torsion R B) : a ∈ Submodule.torsion R A := by
  rw [Submodule.mem_torsion_iff] at ha ⊢
  rcases ha with ⟨r, hr⟩
  use r
  rw [Submonoid.smul_def] at hr ⊢
  apply hu
  rw [map_smul, hr, map_zero]

/- accepted add_to_file helper 2 -/
lemma exists_nonzero_annihilates_torsion_of_isNoetherian
    {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [IsNoetherian R M] :
    ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M, r • m = 0 := by
  have hfin : Module.Finite R (Submodule.torsion R M) :=
    Module.IsNoetherian.finite R (Submodule.torsion R M)
  rcases Submodule.annihilator_top_inter_nonZeroDivisors
      (M := Submodule.torsion R M) (Submodule.torsion_isTorsion (R := R) (M := M)) with ⟨r, hrann, hrnz⟩
  refine ⟨r, nonZeroDivisors.ne_zero hrnz, ?_⟩
  intro m
  exact Module.isTorsionBySet_annihilator_top R (Submodule.torsion R M)
    (a := ⟨r, hrann⟩) (x := m)

/- accepted add_to_file helper 3 -/
lemma torsion_right_annihilated_of_shortExact
    {R M₀ M₁ M₂ : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₀] [Module R M₁] [Module R M₂]
    (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂)
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hT₁ : ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₁, r • m = 0)
    [Module.Finite R (M₁ ⧸ Submodule.torsion R M₁)] [IsNoetherianRing R] :
    ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₂, r • m = 0 := by
  let Q₀ := M₀ ⧸ Submodule.torsion R M₀
  let Q₁ := M₁ ⧸ Submodule.torsion R M₁
  let qF : Q₀ →ₗ[R] Q₁ :=
    Submodule.mapQ (Submodule.torsion R M₀) (Submodule.torsion R M₁) f (torsion_map_le f)
  let C := Q₁ ⧸ qF.range
  haveI : Module.Finite R C := by
    exact Module.Finite.quotient R qF.range
  haveI : IsNoetherian R C := isNoetherian_of_isNoetherianRing_of_finite R C
  rcases exists_nonzero_annihilates_torsion_of_isNoetherian (R := R) (M := C) with ⟨b, hb0, hb⟩
  rcases hT₁ with ⟨a, ha0, ha⟩
  refine ⟨a * b, mul_ne_zero ha0 hb0, ?_⟩
  intro z
  rcases hg (z : M₂) with ⟨x, hx⟩
  have hclass : Submodule.Quotient.mk (Submodule.Quotient.mk x : Q₁) ∈ Submodule.torsion R C := by
    rw [Submodule.mem_torsion_iff]
    have hzmem : (z : M₂) ∈ Submodule.torsion R M₂ := z.property
    rw [Submodule.mem_torsion_iff] at hzmem
    rcases hzmem with ⟨c, hc⟩
    use c
    rw [Submonoid.smul_def] at hc ⊢
    have hgx : g ((c : R) • x) = 0 := by
      rw [map_smul, hx, hc]
    rcases ((hfg ((c : R) • x)).mp hgx) with ⟨y, hy⟩
    have hinner : (c : R) • (Submodule.Quotient.mk x : Q₁) =
        Submodule.Quotient.mk ((c : R) • x : M₁) := by
      calc
        (c : R) • (Submodule.Quotient.mk x : Q₁)
            = (c : R) • (Submodule.mkQ (Submodule.torsion R M₁)) x := rfl
        _ = (Submodule.mkQ (Submodule.torsion R M₁)) ((c : R) • x) := by
              exact (map_smul (Submodule.mkQ (Submodule.torsion R M₁)) (c : R) x).symm
        _ = Submodule.Quotient.mk ((c : R) • x : M₁) := rfl
    have houter : (c : R) • (Submodule.Quotient.mk (Submodule.Quotient.mk x : Q₁) : C) =
        Submodule.Quotient.mk ((c : R) • (Submodule.Quotient.mk x : Q₁) : Q₁) := by
      calc
        (c : R) • (Submodule.Quotient.mk (Submodule.Quotient.mk x : Q₁) : C)
            = (c : R) • (Submodule.mkQ qF.range) (Submodule.Quotient.mk x : Q₁) := rfl
        _ = (Submodule.mkQ qF.range) ((c : R) • (Submodule.Quotient.mk x : Q₁)) := by
              exact (map_smul (Submodule.mkQ qF.range) (c : R)
                (Submodule.Quotient.mk x : Q₁)).symm
        _ = Submodule.Quotient.mk ((c : R) • (Submodule.Quotient.mk x : Q₁) : Q₁) := rfl
    have hq : (c : R) • (Submodule.Quotient.mk (Submodule.Quotient.mk x : Q₁) : C) =
        (Submodule.Quotient.mk (qF (Submodule.Quotient.mk y : Q₀) : Q₁) : C) := by
      rw [houter, hinner, ← hy]
      exact congrArg (fun u : Q₁ => (Submodule.Quotient.mk u : C))
        (Submodule.mapQ_apply (Submodule.torsion R M₀)
          (Submodule.torsion R M₁) f y).symm
    rw [hq]
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  have hbclass := hb ⟨Submodule.Quotient.mk (Submodule.Quotient.mk x : Q₁), hclass⟩
  have hbmem : Submodule.Quotient.mk (b • x : M₁) ∈ qF.range := by
    have hbclass' : Submodule.Quotient.mk (Submodule.Quotient.mk (b • x : M₁) : Q₁) = (0 : C) := by
      have hv : b • (Submodule.Quotient.mk (Submodule.Quotient.mk x : Q₁) : C) = 0 := by
        exact congrArg Subtype.val hbclass
      have hinner : b • (Submodule.Quotient.mk x : Q₁) =
          Submodule.Quotient.mk (b • x : M₁) := by
        calc
          b • (Submodule.Quotient.mk x : Q₁)
              = b • (Submodule.mkQ (Submodule.torsion R M₁)) x := rfl
          _ = (Submodule.mkQ (Submodule.torsion R M₁)) (b • x) := by
                exact (map_smul (Submodule.mkQ (Submodule.torsion R M₁)) b x).symm
          _ = Submodule.Quotient.mk (b • x : M₁) := rfl
      have houter : b • (Submodule.Quotient.mk (Submodule.Quotient.mk x : Q₁) : C) =
          Submodule.Quotient.mk (b • (Submodule.Quotient.mk x : Q₁) : Q₁) := by
        calc
          b • (Submodule.Quotient.mk (Submodule.Quotient.mk x : Q₁) : C)
              = b • (Submodule.mkQ qF.range) (Submodule.Quotient.mk x : Q₁) := rfl
          _ = (Submodule.mkQ qF.range) (b • (Submodule.Quotient.mk x : Q₁)) := by
                exact (map_smul (Submodule.mkQ qF.range) b
                  (Submodule.Quotient.mk x : Q₁)).symm
          _ = Submodule.Quotient.mk (b • (Submodule.Quotient.mk x : Q₁) : Q₁) := rfl
      rw [houter, hinner] at hv
      exact hv
    rw [Submodule.Quotient.mk_eq_zero] at hbclass'
    exact hbclass'
  rcases hbmem with ⟨q₀, hq₀⟩
  rcases Submodule.Quotient.mk_surjective (Submodule.torsion R M₀) q₀ with ⟨y, rfl⟩
  have hqmap : qF (Submodule.Quotient.mk y : Q₀) = Submodule.Quotient.mk (f y : M₁) := by
    change (Submodule.mapQ (Submodule.torsion R M₀) (Submodule.torsion R M₁) f
      (torsion_map_le f)) (Submodule.Quotient.mk y) = Submodule.Quotient.mk (f y)
    exact Submodule.mapQ_apply (Submodule.torsion R M₀) (Submodule.torsion R M₁) f y
  have hq₀' : Submodule.Quotient.mk (b • x : M₁) = Submodule.Quotient.mk (f y : M₁) :=
    hq₀.symm.trans hqmap
  have hdiff : b • x - f y ∈ Submodule.torsion R M₁ := by
    exact (Submodule.Quotient.eq (Submodule.torsion R M₁)).mp hq₀'
  have hakill : a • (b • x - f y) = 0 := by
    have := congrArg Subtype.val (ha ⟨b • x - f y, hdiff⟩)
    simpa using this
  have hgkill : g (a • (b • x - f y)) = 0 := by
    rw [hakill, map_zero]
  have hgf : g (f y) = 0 := by
    exact (hfg (f y)).mpr ⟨y, rfl⟩
  have hmain : (a * b) • g x = 0 := by
    rw [map_smul, map_sub, map_smul, hgf, sub_zero] at hgkill
    rw [smul_smul] at hgkill
    exact hgkill
  ext
  rw [hx] at hmain
  exact hmain

/- accepted add_to_file helper 4 -/
lemma finite_quotient_middle_of_shortExact
    {R M₀ M₁ M₂ : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₀] [Module R M₁] [Module R M₂]
    (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂)
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hT₂ : ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₂, r • m = 0)
    [Module.Finite R (M₀ ⧸ Submodule.torsion R M₀)]
    [Module.Finite R (M₂ ⧸ Submodule.torsion R M₂)] [IsNoetherianRing R] :
    Module.Finite R (M₁ ⧸ Submodule.torsion R M₁) := by
  let Q₀ := M₀ ⧸ Submodule.torsion R M₀
  let Q₁ := M₁ ⧸ Submodule.torsion R M₁
  let Q₂ := M₂ ⧸ Submodule.torsion R M₂
  let qF : Q₀ →ₗ[R] Q₁ :=
    Submodule.mapQ (Submodule.torsion R M₀) (Submodule.torsion R M₁) f (torsion_map_le f)
  let qG : Q₁ →ₗ[R] Q₂ :=
    Submodule.mapQ (Submodule.torsion R M₁) (Submodule.torsion R M₂) g (torsion_map_le g)
  have hqG_surj : Function.Surjective qG := by
    intro z
    rcases Submodule.Quotient.mk_surjective (Submodule.torsion R M₂) z with ⟨m, rfl⟩
    rcases hg m with ⟨x, hx⟩
    use Submodule.Quotient.mk x
    have hmap : qG (Submodule.Quotient.mk x : Q₁) = Submodule.Quotient.mk (g x : M₂) := by
      change (Submodule.mapQ (Submodule.torsion R M₁) (Submodule.torsion R M₂) g
        (torsion_map_le g)) (Submodule.Quotient.mk x) = Submodule.Quotient.mk (g x)
      exact Submodule.mapQ_apply (Submodule.torsion R M₁) (Submodule.torsion R M₂) g x
    rw [hmap, hx]
  rcases hT₂ with ⟨b, hb0, hb⟩
  let bm : Q₁ →ₗ[R] Q₁ := b • LinearMap.id
  have hLfg : qF.range.FG := by
    exact Module.Finite.iff_fg.mp (Module.Finite.range qF)
  have hmaple : Submodule.map bm qG.ker ≤ qF.range := by
    intro y hy
    rw [Submodule.mem_map] at hy
    rcases hy with ⟨x, hxK, rfl⟩
    rcases Submodule.Quotient.mk_surjective (Submodule.torsion R M₁) x with ⟨m, rfl⟩
    have hzero : qG (Submodule.Quotient.mk m : Q₁) = 0 := LinearMap.mem_ker.mp hxK
    have hqGmap : qG (Submodule.Quotient.mk m : Q₁) = Submodule.Quotient.mk (g m : M₂) := by
      change (Submodule.mapQ (Submodule.torsion R M₁) (Submodule.torsion R M₂) g
        (torsion_map_le g)) (Submodule.Quotient.mk m) = Submodule.Quotient.mk (g m)
      exact Submodule.mapQ_apply (Submodule.torsion R M₁) (Submodule.torsion R M₂) g m
    have hgtors : g m ∈ Submodule.torsion R M₂ := by
      rw [hqGmap, Submodule.Quotient.mk_eq_zero] at hzero
      exact hzero
    have hbkill : b • g m = 0 := by
      have := congrArg Subtype.val (hb ⟨g m, hgtors⟩)
      simpa using this
    have hgb : g (b • m) = 0 := by
      rw [map_smul, hbkill]
    rcases ((hfg (b • m)).mp hgb) with ⟨y, hy⟩
    change b • (Submodule.Quotient.mk m : Q₁) ∈ qF.range
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    have hqFmap : qF (Submodule.Quotient.mk y : Q₀) = Submodule.Quotient.mk (f y : M₁) := by
      change (Submodule.mapQ (Submodule.torsion R M₀) (Submodule.torsion R M₁) f
        (torsion_map_le f)) (Submodule.Quotient.mk y) = Submodule.Quotient.mk (f y)
      exact Submodule.mapQ_apply (Submodule.torsion R M₀) (Submodule.torsion R M₁) f y
    rw [hqFmap, hy]
    calc
      Submodule.Quotient.mk (b • m : M₁)
          = b • (Submodule.mkQ (Submodule.torsion R M₁)) m := by
            exact map_smul (Submodule.mkQ (Submodule.torsion R M₁)) b m
      _ = b • (Submodule.Quotient.mk m : Q₁) := rfl
  have hmapfg : (Submodule.map bm qG.ker).FG :=
    Submodule.FG.of_le hLfg hmaple
  have hkerbot : qG.ker ⊓ bm.ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rcases hx with ⟨-, hxb⟩
    have hbzero : bm x = 0 := LinearMap.mem_ker.mp hxb
    change b • x = 0 at hbzero
    apply smul_right_injective Q₁ hb0
    change b • x = b • (0 : Q₁)
    rw [hbzero, smul_zero]
  have hkerfg : (qG.ker ⊓ bm.ker).FG := by
    rw [hkerbot]
    exact Submodule.fg_bot
  have hKfg : qG.ker.FG := Submodule.fg_of_fg_map_of_fg_inf_ker bm hmapfg hkerfg
  haveI : Module.Finite R qG.ker := Module.Finite.iff_fg.mpr hKfg
  have hexact : Function.Exact qG.ker.subtype qG := by
    intro x
    constructor
    · intro hx
      exact ⟨⟨x, LinearMap.mem_ker.mpr hx⟩, rfl⟩
    · intro hx
      rcases hx with ⟨y, hy⟩
      have : qG (y : Q₁) = 0 := LinearMap.mem_ker.mp y.property
      rw [← hy]
      exact this
  exact Module.Finite.of_exact hexact hqG_surj

/- accepted add_to_file helper 5 -/
lemma torsion_middle_annihilated_of_shortExact
    {R M₀ M₁ M₂ : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₀] [Module R M₁] [Module R M₂]
    (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂)
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hT₀ : ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₀, r • m = 0)
    (hT₂ : ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₂, r • m = 0) :
    ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₁, r • m = 0 := by
  rcases hT₀ with ⟨a, ha0, ha⟩
  rcases hT₂ with ⟨b, hb0, hb⟩
  refine ⟨a * b, mul_ne_zero ha0 hb0, ?_⟩
  intro z
  have hgz : g (z : M₁) ∈ Submodule.torsion R M₂ := torsion_map_le g z.property
  have hbkill : b • g (z : M₁) = 0 := by
    have := congrArg Subtype.val (hb ⟨g (z : M₁), hgz⟩)
    simpa using this
  have hgb : g (b • (z : M₁)) = 0 := by
    rw [map_smul, hbkill]
  rcases ((hfg (b • (z : M₁))).mp hgb) with ⟨y, hy⟩
  have hfy : f y ∈ Submodule.torsion R M₁ := by
    rw [hy]
    exact (Submodule.torsion R M₁).smul_mem b z.property
  have hytor : y ∈ Submodule.torsion R M₀ :=
    torsion_reflect_of_injective f hf hfy
  have hakill : a • y = 0 := by
    have := congrArg Subtype.val (ha ⟨y, hytor⟩)
    simpa using this
  have hfzero : f (a • y) = 0 := by
    rw [hakill, map_zero]
  have hmain : (a * b) • (z : M₁) = 0 := by
    rw [map_smul, hy] at hfzero
    rw [smul_smul] at hfzero
    exact hfzero
  ext
  exact hmain

/- accepted add_to_file helper 6 -/
lemma finite_quotient_left_of_shortExact
    {R M₀ M₁ : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M₀] [AddCommGroup M₁]
    [Module R M₀] [Module R M₁]
    (f : M₀ →ₗ[R] M₁) (hf : Function.Injective f)
    [Module.Finite R (M₁ ⧸ Submodule.torsion R M₁)] [IsNoetherianRing R] :
    Module.Finite R (M₀ ⧸ Submodule.torsion R M₀) := by
  let Q₀ := M₀ ⧸ Submodule.torsion R M₀
  let Q₁ := M₁ ⧸ Submodule.torsion R M₁
  let qF : Q₀ →ₗ[R] Q₁ :=
    Submodule.mapQ (Submodule.torsion R M₀) (Submodule.torsion R M₁) f (torsion_map_le f)
  have hqF_inj : Function.Injective qF := by
    intro x y hxy
    rcases Submodule.Quotient.mk_surjective (Submodule.torsion R M₀) x with ⟨x, rfl⟩
    rcases Submodule.Quotient.mk_surjective (Submodule.torsion R M₀) y with ⟨y, rfl⟩
    have hxmap : qF (Submodule.Quotient.mk x : Q₀) = Submodule.Quotient.mk (f x : M₁) := by
      change (Submodule.mapQ (Submodule.torsion R M₀) (Submodule.torsion R M₁) f
        (torsion_map_le f)) (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x)
      exact Submodule.mapQ_apply (Submodule.torsion R M₀) (Submodule.torsion R M₁) f x
    have hymap : qF (Submodule.Quotient.mk y : Q₀) = Submodule.Quotient.mk (f y : M₁) := by
      change (Submodule.mapQ (Submodule.torsion R M₀) (Submodule.torsion R M₁) f
        (torsion_map_le f)) (Submodule.Quotient.mk y) = Submodule.Quotient.mk (f y)
      exact Submodule.mapQ_apply (Submodule.torsion R M₀) (Submodule.torsion R M₁) f y
    rw [hxmap, hymap] at hxy
    have hdiff : f x - f y ∈ Submodule.torsion R M₁ :=
      (Submodule.Quotient.eq (Submodule.torsion R M₁)).mp hxy
    have hfdiff : f (x - y) ∈ Submodule.torsion R M₁ := by
      rw [map_sub]
      exact hdiff
    have htor : x - y ∈ Submodule.torsion R M₀ :=
      torsion_reflect_of_injective f hf hfdiff
    exact (Submodule.Quotient.eq (Submodule.torsion R M₀)).mpr htor
  haveI : IsNoetherian R Q₁ := isNoetherian_of_isNoetherianRing_of_finite R Q₁
  exact Module.Finite.of_injective qF hqF_inj

/- accepted add_to_file helper 7 -/
lemma finite_quotient_right_of_shortExact
    {R M₁ M₂ : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₁] [Module R M₂]
    (g : M₁ →ₗ[R] M₂) (hg : Function.Surjective g)
    [Module.Finite R (M₁ ⧸ Submodule.torsion R M₁)] :
    Module.Finite R (M₂ ⧸ Submodule.torsion R M₂) := by
  let Q₁ := M₁ ⧸ Submodule.torsion R M₁
  let Q₂ := M₂ ⧸ Submodule.torsion R M₂
  let qG : Q₁ →ₗ[R] Q₂ :=
    Submodule.mapQ (Submodule.torsion R M₁) (Submodule.torsion R M₂) g (torsion_map_le g)
  have hqG_surj : Function.Surjective qG := by
    intro z
    rcases Submodule.Quotient.mk_surjective (Submodule.torsion R M₂) z with ⟨m, rfl⟩
    rcases hg m with ⟨x, hx⟩
    use Submodule.Quotient.mk x
    have hmap : qG (Submodule.Quotient.mk x : Q₁) = Submodule.Quotient.mk (g x : M₂) := by
      change (Submodule.mapQ (Submodule.torsion R M₁) (Submodule.torsion R M₂) g
        (torsion_map_le g)) (Submodule.Quotient.mk x) = Submodule.Quotient.mk (g x)
      exact Submodule.mapQ_apply (Submodule.torsion R M₁) (Submodule.torsion R M₂) g x
    rw [hmap, hx]
  exact Module.Finite.of_surjective qG hqG_surj

/- accepted add_to_file helper 8 -/
lemma torsion_left_annihilated_of_shortExact
    {R M₀ M₁ : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M₀] [AddCommGroup M₁]
    [Module R M₀] [Module R M₁]
    (f : M₀ →ₗ[R] M₁) (hf : Function.Injective f)
    (hT₁ : ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₁, r • m = 0) :
    ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₀, r • m = 0 := by
  rcases hT₁ with ⟨a, ha0, ha⟩
  refine ⟨a, ha0, ?_⟩
  intro z
  have hfz : f (z : M₀) ∈ Submodule.torsion R M₁ := torsion_map_le f z.property
  have hkill : a • f (z : M₀) = 0 := by
    have := congrArg Subtype.val (ha ⟨f (z : M₀), hfz⟩)
    simpa using this
  have hfkill : f (a • (z : M₀)) = 0 := by
    rw [map_smul, hkill]
  have hmain : a • (z : M₀) = 0 := hf (by rw [hfkill, map_zero])
  ext
  exact hmain

/- verified submission -/
theorem almostTrivial_and_almostFinite_of_shortExact
    {R : Type*} [CommRing R] [IsDomain R]
    {M₀ M₁ M₂ : Type*}
    [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₀] [Module R M₁] [Module R M₂]
    (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂)
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    ((∃ r : R, r ≠ 0 ∧ ∀ m : M₁, r • m = 0) ↔
      (∃ r : R, r ≠ 0 ∧ ∀ m : M₀, r • m = 0) ∧
      (∃ r : R, r ≠ 0 ∧ ∀ m : M₂, r • m = 0)) ∧
    (IsNoetherianRing R →
      (((∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₁, r • m = 0) ∧
          Module.Finite R (M₁ ⧸ Submodule.torsion R M₁)) ↔
        ((∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₀, r • m = 0) ∧
          Module.Finite R (M₀ ⧸ Submodule.torsion R M₀)) ∧
        ((∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₂, r • m = 0) ∧
          Module.Finite R (M₂ ⧸ Submodule.torsion R M₂)))) := by
  constructor
  · constructor
    · intro h
      rcases h with ⟨r, hr0, hr⟩
      constructor
      · refine ⟨r, hr0, ?_⟩
        intro m
        apply hf
        rw [map_smul, hr (f m), map_zero]
      · refine ⟨r, hr0, ?_⟩
        intro z
        rcases hg z with ⟨m, rfl⟩
        rw [← map_smul, hr m, map_zero]
    · intro h
      rcases h with ⟨⟨a, ha0, ha⟩, ⟨b, hb0, hb⟩⟩
      refine ⟨a * b, mul_ne_zero ha0 hb0, ?_⟩
      intro m
      have hgb : g (b • m) = 0 := by
        rw [map_smul, hb (g m)]
      rcases ((hfg (b • m)).mp hgb) with ⟨y, hy⟩
      have hfy : f (a • y) = 0 := by
        rw [ha y, map_zero]
      rw [map_smul, hy] at hfy
      rw [smul_smul] at hfy
      exact hfy
  · intro hNoeth
    haveI : IsNoetherianRing R := hNoeth
    constructor
    · intro hA
      rcases hA with ⟨hT₁, hF₁⟩
      haveI : Module.Finite R (M₁ ⧸ Submodule.torsion R M₁) := hF₁
      have hT₀ := torsion_left_annihilated_of_shortExact f hf hT₁
      have hF₀ := finite_quotient_left_of_shortExact f hf
      have hF₂ := finite_quotient_right_of_shortExact g hg
      have hT₂ := torsion_right_annihilated_of_shortExact f g hfg hg hT₁
      exact ⟨⟨hT₀, hF₀⟩, ⟨hT₂, hF₂⟩⟩
    · intro hA
      rcases hA with ⟨⟨hT₀, hF₀⟩, ⟨hT₂, hF₂⟩⟩
      haveI : Module.Finite R (M₀ ⧸ Submodule.torsion R M₀) := hF₀
      haveI : Module.Finite R (M₂ ⧸ Submodule.torsion R M₂) := hF₂
      have hT₁ := torsion_middle_annihilated_of_shortExact f g hf hfg hT₀ hT₂
      have hF₁ := finite_quotient_middle_of_shortExact f g hfg hg hT₂
      exact ⟨hT₁, hF₁⟩

end Rollout_p0412_almosttrivial_and_almostfinite_of_shortexa

namespace Rollout_p0273_weighted_one_dimensional_dirichlet_lower_b

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

end Rollout_p0273_weighted_one_dimensional_dirichlet_lower_b
