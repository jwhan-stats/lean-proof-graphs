import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p2937_coinvariants_addmonoidalgebra_eq_range
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: efb7339bd7ad37f7add4d6ffea20ff5f7f3340ddaf8769ccd6fecd3d777912c5
-- reconstructed_proof_sha256: f145f7b99448c25ad8b6c5d7a4417cdd290a085a3e80d2c63688691b4f75be37
-- selected_edge_count: 1

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


#check_dependency_graph "coinvariants_addMonoidAlgebra_eq_range" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"AlgHom.equalizer c Algebra.TensorProduct.includeRight = (AddMonoidAlgebra.mapDomainAlgHom R R (φ.addSubmonoidComap S)).range\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hφ\",\"statement\":\"Function.Injective ⇑φ\"},{\"name\":\"hexact\",\"statement\":\"Function.Exact ⇑φ ⇑ψ\"},{\"name\":\"hc\",\"statement\":\"∀ (m : ↥S), c (AddMonoidAlgebra.single m 1) = AddMonoidAlgebra.single (ψ ↑m) 1 ⊗ₜ[R] AddMonoidAlgebra.single m 1\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2937_coinvariants_addmonoidalgebra_eq_range\",\"reconstructedProofSha256\":\"f145f7b99448c25ad8b6c5d7a4417cdd290a085a3e80d2c63688691b4f75be37\",\"selectedEdgeCount\":1,\"theoremName\":\"coinvariants_addMonoidAlgebra_eq_range\",\"topologySha256\":\"efb7339bd7ad37f7add4d6ffea20ff5f7f3340ddaf8769ccd6fecd3d777912c5\"}"
