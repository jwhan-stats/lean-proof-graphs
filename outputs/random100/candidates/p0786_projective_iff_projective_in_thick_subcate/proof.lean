import Mathlib

/- verified submission -/
open CategoryTheory

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
            CategoryTheory.IsSplitEpi T.g) := by
  intro Q hQ
  constructor
  · intro hQproj T hT hS₁ hS₂ hTexact
    subst Q
    letI : CategoryTheory.Epi T.g := hTexact.epi_g
    exact CategoryTheory.IsSplitEpi.mk'
      ⟨CategoryTheory.Projective.factorThru (𝟙 T.X₃) T.g,
        CategoryTheory.Projective.factorThru_comp (𝟙 T.X₃) T.g⟩
  · intro h
    let T : CategoryTheory.ShortComplex C :=
      CategoryTheory.ShortComplex.kernelSequence (CategoryTheory.Projective.π Q)
    haveI : CategoryTheory.Mono T.f := by
      dsimp [T]
      infer_instance
    haveI : CategoryTheory.Epi T.g := by
      dsimp [T]
      exact CategoryTheory.Projective.π_epi Q
    have hTexact : T.ShortExact := by
      exact CategoryTheory.ShortComplex.ShortExact.mk
        (CategoryTheory.ShortComplex.kernelSequence_exact (CategoryTheory.Projective.π Q))
    have hS₂ : S T.X₂ := by
      exact hproj T.X₂ (by
        simpa [T] using CategoryTheory.Projective.projective_over Q)
    have hS₃ : S T.X₃ := by
      simpa [T] using hQ
    have hS₁ : S T.X₁ :=
      (hS T hTexact).2.2 ⟨hS₂, hS₃⟩
    have hsplit : CategoryTheory.IsSplitEpi T.g :=
      h T (by simp [T]) hS₁ hS₂ hTexact
    have hsplitπ : CategoryTheory.IsSplitEpi (CategoryTheory.Projective.π Q) := by
      simpa [T] using hsplit
    letI : CategoryTheory.IsSplitEpi (CategoryTheory.Projective.π Q) := hsplitπ
    exact CategoryTheory.Retract.projective
      ⟨CategoryTheory.section_ (CategoryTheory.Projective.π Q),
        CategoryTheory.Projective.π Q,
        CategoryTheory.IsSplitEpi.id (CategoryTheory.Projective.π Q)⟩
