theorem weighted_pointwise_inequality_on_circle :
    ∃ C : ℝ, 0 < C ∧
      ∀ f : ℝ → ℝ,
        Function.Periodic f (2 * Real.pi) →
        AbsolutelyContinuousOnInterval f (-Real.pi) Real.pi →
        f 0 = 0 →
        MeasureTheory.IntegrableOn
          (fun x : ℝ => |deriv f x| ^ 2 / Real.sin (x / 2) ^ 2)
          (Set.Icc (-Real.pi) Real.pi) →
        essSup
            (fun x : ℝ => |f x| / |Real.sin (x / 2)|)
            (MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi)) ≤
          C * Real.sqrt
            (∫ x in Set.Icc (-Real.pi) Real.pi,
              |deriv f x| ^ 2 / Real.sin (x / 2) ^ 2) := by sorry
