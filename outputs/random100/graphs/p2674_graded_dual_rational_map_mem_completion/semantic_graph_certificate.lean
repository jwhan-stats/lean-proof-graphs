import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p2674_graded_dual_rational_map_mem_completion
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: ee96ffed4839bb111b30a81d1b3d00b895a201f2c741ddc0e91de1722bd55d11
-- reconstructed_proof_sha256: 0046f17857bd64d50d78ba09992033d5aec361a99586c0435defed668a7eded7
-- selected_edge_count: 4

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


#check_dependency_graph "graded_dual_rational_map_mem_completion" against "{\"edges\":[{\"conclusion\":{\"name\":\"hfinite_g\",\"statement\":\"∀ (a : ℂ), {α | g α a ≠ 0}.Finite\"},\"graphEdgeId\":\"h_001_hfinite_g\",\"premises\":[{\"name\":\"hcleared\",\"statement\":\"∀ (w' : DirectSum ℂ fun a => Module.Dual ℂ (W a)), ∃ P, (∀ (α : Fin n →₀ ℕ), MvPolynomial.coeff α P = (DirectSum.toModule ℂ ℂ ℂ fun a => (Module.Dual.eval ℂ (W a)) (g α a)) w') ∧ ∀ (z : { z // Function.Injective z }), (∏ i, ∏ j ∈ Finset.Ioi i, (↑z i - ↑z j) ^ p i j) * (f z) w' = (MvPolynomial.eval ↑z) P\"}],\"rawEdgeId\":\"telescope_13\"},{\"conclusion\":{\"name\":\"hD\",\"statement\":\"D ≠ 0\"},\"graphEdgeId\":\"h_002_hd\",\"premises\":[],\"rawEdgeId\":\"telescope_17\"},{\"conclusion\":{\"name\":\"hcomponent\",\"statement\":\"∀ (a : ℂ) (l : Module.Dual ℂ (W a)), (f z) ((DirectSum.lof ℂ ℂ (fun c => Module.Dual ℂ (W c)) a) l) = l (b a)\"},\"graphEdgeId\":\"h_003_hcomponent\",\"premises\":[{\"name\":\"hcleared\",\"statement\":\"∀ (w' : DirectSum ℂ fun a => Module.Dual ℂ (W a)), ∃ P, (∀ (α : Fin n →₀ ℕ), MvPolynomial.coeff α P = (DirectSum.toModule ℂ ℂ ℂ fun a => (Module.Dual.eval ℂ (W a)) (g α a)) w') ∧ ∀ (z : { z // Function.Injective z }), (∏ i, ∏ j ∈ Finset.Ioi i, (↑z i - ↑z j) ^ p i j) * (f z) w' = (MvPolynomial.eval ↑z) P\"},{\"name\":\"hfinite_g\",\"statement\":\"∀ (a : ℂ), {α | g α a ≠ 0}.Finite\"},{\"name\":\"hD\",\"statement\":\"D ≠ 0\"}],\"rawEdgeId\":\"telescope_19\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∃ b, f z = DirectSum.toModule ℂ ℂ ℂ fun a => (Module.Dual.eval ℂ (W a)) (b a)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hcomponent\",\"statement\":\"∀ (a : ℂ) (l : Module.Dual ℂ (W a)), (f z) ((DirectSum.lof ℂ ℂ (fun c => Module.Dual ℂ (W c)) a) l) = l (b a)\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2674_graded_dual_rational_map_mem_completion\",\"reconstructedProofSha256\":\"0046f17857bd64d50d78ba09992033d5aec361a99586c0435defed668a7eded7\",\"selectedEdgeCount\":4,\"theoremName\":\"graded_dual_rational_map_mem_completion\",\"topologySha256\":\"ee96ffed4839bb111b30a81d1b3d00b895a201f2c741ddc0e91de1722bd55d11\"}"
