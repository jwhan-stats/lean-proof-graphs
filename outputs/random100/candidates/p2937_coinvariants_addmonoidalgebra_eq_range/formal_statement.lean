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
      (AddMonoidAlgebra.mapDomainAlgHom R R (φ.addSubmonoidComap S)).range := by sorry
