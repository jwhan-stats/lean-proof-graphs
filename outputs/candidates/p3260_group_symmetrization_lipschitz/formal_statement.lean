theorem group_symmetrization_lipschitz
    (D : ℕ)
    (X : Set (EuclideanSpace ℝ (Fin D)))
    (G : Type*) [Group G] [Fintype G] [MulAction G X]
    (hact : ∀ (g : G) (x y : X),
      ‖(↑(g • x) : EuclideanSpace ℝ (Fin D)) - ↑(g • y)‖ ≤
        ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖)
    (L : ℝ) (hL : 0 ≤ L)
    (f : X → ℝ)
    (hf : ∀ x y : X,
      |f x - f y| ≤ L * ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖) :
    ∀ x y : X,
      |((∑ g : G, f (g • x)) / (Fintype.card G : ℝ)) -
          ((∑ g : G, f (g • y)) / (Fintype.card G : ℝ))| ≤
        L * ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖ := by sorry
