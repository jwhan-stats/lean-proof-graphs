theorem projective_iff_projective_in_thick_subcategory
    {C : Type u} [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C]
    [CategoryTheory.EnoughProjectives C]
    (S : CategoryTheory.ObjectProperty C)
    [S.IsStableUnderRetracts]
    (hS : ∀ (T : CategoryTheory.ShortComplex C), T.ShortExact →
      (S T.X₁ ∧ S T.X₂ → S T.X₃) ∧
      (S T.X₁ ∧ S T.X₃ → S T.X₂) ∧
      (S T.X₂ ∧ S T.X₃ → S T.X₁))
    (hproj : ∀ (P : C), CategoryTheory.Projective P → S P) :
    ∀ (Q : C), S Q →
      (CategoryTheory.Projective Q ↔
        ∀ (T : CategoryTheory.ShortComplex C), T.X₃ = Q →
          S T.X₁ → S T.X₂ → T.ShortExact →
            CategoryTheory.IsSplitEpi T.g) := by sorry
