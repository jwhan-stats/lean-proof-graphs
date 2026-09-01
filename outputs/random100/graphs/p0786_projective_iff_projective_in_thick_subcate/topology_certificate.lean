import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0786_projective_iff_projective_in_thick_subcate
-- topology_sha256: 0e507526b3dc3c2fe382547187da09f38ad1d12154a2fa062539f87c58d855eb
namespace TopologyCertificate_p0786_projective_iff_projective_in_thick_subcate

-- N001 = hproj: ∀ (P : C), CategoryTheory.Projective P → S P
-- N002 = hQ: S Q
-- N003 = hS: ∀ (T : CategoryTheory.ShortComplex C), T.ShortExact → (S T.X₁ ∧ S T.X₂ → S T.X₃) ∧ (S T.X₁ ∧ S T.X₃ → S T.X₂) ∧ (S T.X₂ ∧ S T.X₃ → S T.X₁)
-- N004 = inst._@.proofs.968698635._hygCtx._hyg.9: CategoryTheory.EnoughProjectives C
-- N005 = goal: CategoryTheory.Projective Q ↔ ∀ (T : CategoryTheory.ShortComplex C), T.X₃ = Q → S T.X₁ → S T.X₂ → T.ShortExact → CategoryTheory.IsSplitEpi T.g

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N004 → N003 → N001 → N002 → N005)
    : N005 := by
  have H_N005 : N005 := E001 B004 B003 B001 B002
  exact H_N005

end TopologyCertificate_p0786_projective_iff_projective_in_thick_subcate
