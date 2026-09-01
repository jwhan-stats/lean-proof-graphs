import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0378_finite_g_set_subcategory_contains_all_mono
-- topology_sha256: c7aa6e819654a31c1b25326607ad68d547a4afb2514a948524abcfdf1173b344
namespace TopologyCertificate_p0378_finite_g_set_subcategory_contains_all_mono

-- N001 = hD_coproduct: D.IsStableUnderFiniteCoproducts
-- N002 = hD_empty: D (CategoryTheory.Limits.initial.to (⊤_ Action FintypeCat G))
-- N003 = hD_id: ∀ {X Y : Action FintypeCat G} (f : X ⟶ Y), D f → D (CategoryTheory.CategoryStruct.id X) ∧ D (CategoryTheory.CategoryStruct.id Y)
-- N004 = hD_pullback: D.IsStableUnderBaseChange
-- N005 = hf: CategoryTheory.MorphismProperty.monomorphisms (Action FintypeCat G) f
-- N006 = inst._@.proofs.1466848982._hygCtx._hyg.6: Finite G
-- N007 = htruth: D (Rollout_p0378_finite_g_set_subcategory_contains_all_mono.FiniteGSetProof.truthU G)
-- N008 = goal: D f

-- E001 represents h_001_htruth
-- E002 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (N008 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (E001 : N006 → N003 → N004 → N001 → N002 → N007)
    (E002 : N004 → N005 → N007 → N008)
    : N008 := by
  have H_N007 : N007 := E001 B006 B003 B004 B001 B002
  have H_N008 : N008 := E002 B004 B005 H_N007
  exact H_N008

end TopologyCertificate_p0378_finite_g_set_subcategory_contains_all_mono
