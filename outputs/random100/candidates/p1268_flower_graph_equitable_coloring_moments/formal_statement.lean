theorem flower_graph_equitable_coloring_moments
    (n k : ℕ) (hn : 3 ≤ n) :
    let V := Unit ⊕ (Fin n ⊕ Fin n)
    let F : SimpleGraph V := SimpleGraph.fromRel fun a b =>
      (∃ i : Fin n, a = Sum.inl () ∧ b = Sum.inr (Sum.inl i)) ∨
      (∃ i : Fin n,
        a = Sum.inr (Sum.inl i) ∧
          b = Sum.inr (Sum.inl ((finRotate n) i))) ∨
      (∃ i : Fin n, a = Sum.inr (Sum.inl i) ∧ b = Sum.inr (Sum.inr i)) ∨
      (∃ i : Fin n, a = Sum.inl () ∧ b = Sum.inr (Sum.inr i))
    ∀ f : F.Coloring (Fin k),
      Function.Surjective f →
      (∀ i j : Fin k,
        Nat.dist (f.colorClass i).ncard (f.colorClass j).ncard ≤ 1) →
      (∀ ℓ : ℕ, ℓ < k →
        ¬ ∃ g : F.Coloring (Fin ℓ),
          Function.Surjective g ∧
          (∀ i j : Fin ℓ,
            Nat.dist (g.colorClass i).ncard (g.colorClass j).ncard ≤ 1)) →
      (∀ i j : Fin k, i ≤ j →
        (f.colorClass j).ncard ≤ (f.colorClass i).ncard) →
      let X : V → ℝ := fun x => (↑((f x).val + 1) : ℝ)
      let μ := @PMF.toMeasure V ⊤ (PMF.uniformOfFintype V)
      @MeasureTheory.integral V ℝ _ _ ⊤ μ X =
          ((n : ℝ) + 1) ^ 2 / (2 * (n : ℝ) + 1) ∧
        @ProbabilityTheory.variance V ⊤ X μ =
          ((n : ℝ) ^ 4 + 2 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 + (n : ℝ)) /
            (3 * (2 * (n : ℝ) + 1) ^ 2) := by sorry
