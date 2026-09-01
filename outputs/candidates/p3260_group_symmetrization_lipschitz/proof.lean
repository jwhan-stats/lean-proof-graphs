import Mathlib

/- verified submission -/
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
        L * ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖ := by
  intro x y
  let C : ℝ := Fintype.card G
  have hCpos : 0 < C := by
    dsimp [C]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hterm : ∀ g : G,
      |f (g • x) - f (g • y)| ≤
        L * ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖ := by
    intro g
    calc
      |f (g • x) - f (g • y)| ≤
          L * ‖(↑(g • x) : EuclideanSpace ℝ (Fin D)) - ↑(g • y)‖ :=
        hf (g • x) (g • y)
      _ ≤ L * ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖ :=
        mul_le_mul_of_nonneg_left (hact g x y) hL
  have hsum :
      |(∑ g : G, f (g • x)) - (∑ g : G, f (g • y))| ≤
        C * (L * ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖) := by
    calc
      |(∑ g : G, f (g • x)) - (∑ g : G, f (g • y))|
          = |∑ g : G, (f (g • x) - f (g • y))| := by
            rw [← Finset.sum_sub_distrib]
      _ ≤ ∑ g : G, |f (g • x) - f (g • y)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ g : G, L * ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖ := by
        exact Finset.sum_le_sum fun g _ => hterm g
      _ = C * (L * ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖) := by
        dsimp [C]
        rw [Finset.sum_const, Finset.card_univ]
        norm_num
  have hdiv :
      |((∑ g : G, f (g • x)) / C) - ((∑ g : G, f (g • y)) / C)| ≤
        L * ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖ := by
    rw [← sub_div, abs_div, abs_of_nonneg hCpos.le]
    exact (div_le_iff₀ hCpos).2 (by simpa [mul_comm] using hsum)
  dsimp [C] at hdiv
  exact hdiv
