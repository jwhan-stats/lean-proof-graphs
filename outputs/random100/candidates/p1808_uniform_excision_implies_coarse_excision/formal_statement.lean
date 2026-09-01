theorem uniform_excision_implies_coarse_excision
    {X : Type*} [UniformSpace X] (A B : Set X) :
    let generated : SetRel X X → Set (SetRel X X) := fun R =>
      {E | ∀ 𝒞 : Set (SetRel X X),
        R ∈ 𝒞 →
        SetRel.id ∈ 𝒞 →
        (∀ ⦃S T : SetRel X X⦄, S ∈ 𝒞 → T ⊆ S → T ∈ 𝒞) →
        (∀ ⦃S T : SetRel X X⦄, S ∈ 𝒞 → T ∈ 𝒞 → S ∪ T ∈ 𝒞) →
        (∀ ⦃S : SetRel X X⦄, S ∈ 𝒞 → S.inv ∈ 𝒞) →
        (∀ ⦃S T : SetRel X X⦄, S ∈ 𝒞 → T ∈ 𝒞 → S.comp T ∈ 𝒞) →
        E ∈ 𝒞}
    let coarse : Set (SetRel X X) :=
      {E | ∀ R ∈ uniformity X, E ∈ generated R}
    A ∪ B = Set.univ →
    (∃ E ∈ uniformity X, E ∈ coarse) →
    (∃ U ∈ uniformity X,
      ∃ κ : OrderDual {W : SetRel X X // W ⊆ U} → OrderDual (SetRel X X),
        Monotone κ ∧
        (∀ V ∈ uniformity X,
          ∃ W : {W : SetRel X X // W ⊆ U},
            W.1 ∈ uniformity X ∧
              OrderDual.ofDual (κ (OrderDual.toDual W)) ⊆ V) ∧
        (∀ W : {W : SetRel X X // W ⊆ U},
          W.1.image A ∩ W.1.image B ⊆
            (OrderDual.ofDual (κ (OrderDual.toDual W))).image (A ∩ B))) →
    ∀ V ∈ coarse, ∃ T ∈ coarse,
      V.image A ∩ V.image B ⊆ T.image (A ∩ B) := by sorry
