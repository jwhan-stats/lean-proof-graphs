theorem collapse_set_partialOrder_iff_ordConnected
    {P : Type*} [PartialOrder P] (B : Set P) (hB : B.Nonempty) :
    let Q := Sum {x : P // x ∉ B} Unit
    let r : Q → Q → Prop := fun x y =>
      match x, y with
      | Sum.inr _, Sum.inr _ => True
      | Sum.inr _, Sum.inl y => ∃ b ∈ B, b ≤ y.1
      | Sum.inl x, Sum.inr _ => ∃ b ∈ B, x.1 ≤ b
      | Sum.inl x, Sum.inl y =>
          x.1 ≤ y.1 ∨ ∃ b ∈ B, ∃ b' ∈ B, x.1 ≤ b ∧ b' ≤ y.1
    IsPartialOrder Q r ↔ B.OrdConnected := by sorry
