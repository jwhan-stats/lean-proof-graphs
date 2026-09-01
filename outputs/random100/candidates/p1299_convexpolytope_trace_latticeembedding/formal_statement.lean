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
      ∀ x : L, convexHull F (ψ x) = φ x := by sorry
