theorem planePoset_union_isLinearOrder
    {P : Type*} [Finite P]
    (leH leR : P → P → Prop)
    (hH : IsPartialOrder P leH)
    (hR : IsPartialOrder P leR)
    (hcompat : ∀ {x y : P}, x ≠ y →
      ((leH x y ∨ leH y x) ↔ ¬ (leR x y ∨ leR y x))) :
    IsLinearOrder P (fun x y => leH x y ∨ leR x y) := by sorry
