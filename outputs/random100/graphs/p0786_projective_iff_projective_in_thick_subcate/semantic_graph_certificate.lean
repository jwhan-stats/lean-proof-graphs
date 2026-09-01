import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p0786_projective_iff_projective_in_thick_subcate
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 0e507526b3dc3c2fe382547187da09f38ad1d12154a2fa062539f87c58d855eb
-- reconstructed_proof_sha256: 9af942818e116aad491584bc5ca3299979d17eed29e03ac8b0e131bad4011d16
-- selected_edge_count: 1

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


#check_dependency_graph "projective_iff_projective_in_thick_subcategory" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"CategoryTheory.Projective Q ↔ ∀ (T : CategoryTheory.ShortComplex C), T.X₃ = Q → S T.X₁ → S T.X₂ → T.ShortExact → CategoryTheory.IsSplitEpi T.g\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"CategoryTheory.EnoughProjectives C\"},{\"name\":\"hS\",\"statement\":\"∀ (T : CategoryTheory.ShortComplex C), T.ShortExact → (S T.X₁ ∧ S T.X₂ → S T.X₃) ∧ (S T.X₁ ∧ S T.X₃ → S T.X₂) ∧ (S T.X₂ ∧ S T.X₃ → S T.X₁)\"},{\"name\":\"hproj\",\"statement\":\"∀ (P : C), CategoryTheory.Projective P → S P\"},{\"name\":\"hQ\",\"statement\":\"S Q\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0786_projective_iff_projective_in_thick_subcate\",\"reconstructedProofSha256\":\"9af942818e116aad491584bc5ca3299979d17eed29e03ac8b0e131bad4011d16\",\"selectedEdgeCount\":1,\"theoremName\":\"projective_iff_projective_in_thick_subcategory\",\"topologySha256\":\"0e507526b3dc3c2fe382547187da09f38ad1d12154a2fa062539f87c58d855eb\"}"
