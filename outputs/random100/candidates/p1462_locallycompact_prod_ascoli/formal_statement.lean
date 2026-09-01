theorem locallyCompact_prod_ascoli
    (Z X : Type*) [TopologicalSpace Z] [T35Space Z] [LocallyCompactSpace Z]
    [TopologicalSpace X] [T35Space X]
    (hX : ∀ K : Set C(X, ℝ), IsCompact K →
      Continuous (fun p : K × X => (p.1 : C(X, ℝ)) p.2)) :
    ∀ K : Set C(Z × X, ℝ), IsCompact K →
      Continuous (fun p : K × (Z × X) => (p.1 : C(Z × X, ℝ)) p.2) := by sorry
