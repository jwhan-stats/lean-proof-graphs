import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p2692_hodge_operator_on_two_forms
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: f78a667584570d9c4fb9b59661d293e0d2173c9926ebeb29901dc26023276f9e
-- reconstructed_proof_sha256: 511cf31754ce326f82da01a926e538b38691d9f621de1a88c78b35f35f930c0f
-- selected_edge_count: 1

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


#check_dependency_graph "hodge_operator_on_two_forms" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"star ∘ₗ star = LinearMap.id ∧ (star - LinearMap.id).ker = Submodule.span ℂ {e_bd, e_ac, e_ad + e_bc} ∧ (star + LinearMap.id).ker = Submodule.span ℂ {e_cd, e_ab - μ • e_bd, e_ad - (q ^ 2)⁻¹ • e_bc} ∧ Module.finrank ℂ ↥(star - LinearMap.id).ker = 3 ∧ Module.finrank ℂ ↥(star + LinearMap.id).ker = 3\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hq0\",\"statement\":\"q ≠ 0\"},{\"name\":\"hq_neg_one\",\"statement\":\"q ^ 2 ≠ -1\"},{\"name\":\"h\",\"statement\":\"star e_ab = -e_ab + (2 * μ) • e_bd ∧ star e_ac = e_ac ∧ star e_ad = (1 / (1 + q ^ 2)) • (2 • e_bc - (q ^ 2 * μ) • e_ad) ∧ star e_bc = (q ^ 2 / (1 + q ^ 2)) • (2 • e_ad + μ • e_bc) ∧ star e_bd = e_bd ∧ star e_cd = -e_cd\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2692_hodge_operator_on_two_forms\",\"reconstructedProofSha256\":\"511cf31754ce326f82da01a926e538b38691d9f621de1a88c78b35f35f930c0f\",\"selectedEdgeCount\":1,\"theoremName\":\"hodge_operator_on_two_forms\",\"topologySha256\":\"f78a667584570d9c4fb9b59661d293e0d2173c9926ebeb29901dc26023276f9e\"}"
