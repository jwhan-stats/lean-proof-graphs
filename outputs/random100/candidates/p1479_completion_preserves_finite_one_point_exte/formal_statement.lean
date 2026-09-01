theorem completion_preserves_finite_one_point_extension
    (A : Type*) [MetricSpace A]
    (hdiam : Metric.diam (Set.univ : Set A) = 1)
    (hext : ∀ (F : Set A), F.Finite →
      ∀ f : F → Set.Icc (0 : ℝ) 1,
        (∀ x y : F,
          |(f x : ℝ) - (f y : ℝ)| ≤ dist (x : A) (y : A) ∧
            dist (x : A) (y : A) ≤ (f x : ℝ) + (f y : ℝ)) →
        ∃ z : A, ∀ x : F, dist z (x : A) = (f x : ℝ)) :
    Metric.diam (Set.univ : Set (UniformSpace.Completion A)) = 1 ∧
      ∀ (F : Set (UniformSpace.Completion A)), F.Finite →
        ∀ f : F → Set.Icc (0 : ℝ) 1,
          (∀ x y : F,
            |(f x : ℝ) - (f y : ℝ)| ≤
                dist (x : UniformSpace.Completion A) (y : UniformSpace.Completion A) ∧
              dist (x : UniformSpace.Completion A) (y : UniformSpace.Completion A) ≤
                (f x : ℝ) + (f y : ℝ)) →
          ∃ z : UniformSpace.Completion A, ∀ x : F,
            dist z (x : UniformSpace.Completion A) = (f x : ℝ) := by sorry
