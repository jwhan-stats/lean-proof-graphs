theorem common_coincidence_point_of_ordered_metric_contraction
    {X : Type*} [Nonempty X] [PartialOrder X] [MetricSpace X] [CompleteSpace X]
    (f g H : X → X) (β : NNReal → NNReal)
    (hregular : ∀ (z : ℕ → X) (a : X), Monotone z →
      Filter.Tendsto z Filter.atTop (nhds a) → ∀ n, z n ≤ a)
    (hf_range : Set.range f ⊆ Set.range H)
    (hg_range : Set.range g ⊆ Set.range H)
    (hH_closed : IsClosed (Set.range H))
    (hfg_inc : ∀ x y, H y = f x → f x ≤ g y)
    (hgf_inc : ∀ x y, H y = g x → g x ≤ f y)
    (hβ_lt_one : ∀ t, β t < 1)
    (hβ_zero : ∀ t : ℕ → NNReal,
      Filter.Tendsto (fun n => β (t n)) Filter.atTop (nhds 1) →
        Filter.Tendsto t Filter.atTop (nhds 0))
    (hcontract : ∀ x y, (H x ≤ H y ∨ H y ≤ H x) →
      nndist (f x) (g y) ≤ β (nndist (H x) (H y)) * nndist (H x) (H y)) :
    ∃ u, f u = g u ∧ g u = H u := by sorry
