theorem not_biorderable_of_product_conjugates_eq_one
    {G : Type*} [Group G]
    (h : ∃ (g : G) (k : ℕ) (x : Fin k → G),
      g ≠ 1 ∧ 1 ≤ k ∧ (List.ofFn (fun i => (x i)⁻¹ * g * x i)).prod = 1) :
    ¬ ∃ r : G → G → Prop,
      IsStrictTotalOrder G r ∧
        (∀ a b c : G, r a b ↔ r (c * a) (c * b)) ∧
        (∀ a b c : G, r a b ↔ r (a * c) (b * c)) := by sorry
