theorem finite_G_set_subcategory_contains_all_monomorphisms
    (G : Type*) [Group G] [Finite G]
    (D : CategoryTheory.MorphismProperty (Action (FintypeCat) G))
    (hD_id : {X Y : Action (FintypeCat) G} → (f : X ⟶ Y) →
      D f → D (CategoryTheory.CategoryStruct.id X) ∧
        D (CategoryTheory.CategoryStruct.id Y))
    (hD_comp : D.IsStableUnderComposition)
    (hD_pullback : D.IsStableUnderBaseChange)
    (hD_coproduct : D.IsStableUnderFiniteCoproducts)
    (hD_empty : D (CategoryTheory.Limits.initial.to
      (CategoryTheory.Limits.terminal (Action (FintypeCat) G)))) :
    CategoryTheory.MorphismProperty.monomorphisms (Action (FintypeCat) G) ≤ D := by sorry
