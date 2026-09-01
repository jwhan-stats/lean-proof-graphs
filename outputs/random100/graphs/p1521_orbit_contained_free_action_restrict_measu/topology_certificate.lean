import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1521_orbit_contained_free_action_restrict_measu
-- topology_sha256: 471b6781f1c3079dd6b581fa595b17e813a968fe878903ea9c3212fb04a978f3
namespace TopologyCertificate_p1521_orbit_contained_free_action_restrict_measu

-- N001 = hB: MeasurableSet B
-- N002 = hc_free: ∀ (y : Y), MulAction.stabilizer Γ y = ⊥
-- N003 = horbit: ∀ (δ : Δ) (y : Y), ∃ γ, δ • y = γ • y
-- N004 = inst._@.proofs.2709197330._hygCtx._hyg.35: MeasurableConstSMul Δ Y
-- N005 = inst._@.proofs.2709197330._hygCtx._hyg.20: StandardBorelSpace Y
-- N006 = inst._@.proofs.2709197330._hygCtx._hyg.11: Countable Γ
-- N007 = inst._@.proofs.2709197330._hygCtx._hyg.31: MeasurableConstSMul Γ Y
-- N008 = inst._@.proofs.2709197330._hygCtx._hyg.119: MeasureTheory.SMulInvariantMeasure Γ Y μ
-- N009 = hS_meas: ∀ (γ : Γ), MeasurableSet (S γ)
-- N010 = hB_eq: B = ⋃ γ, B ∩ S γ
-- N011 = hC_disjoint: Pairwise (Function.onFun Disjoint fun γ => B ∩ S γ)
-- N012 = himage_eq: (fun y => δ • y) '' B = ⋃ γ, γ • (B ∩ S γ)
-- N013 = hT_disjoint: Pairwise (Function.onFun Disjoint fun γ => γ • (B ∩ S γ))
-- N014 = hC_meas: ∀ (γ : Γ), MeasurableSet (B ∩ S γ)
-- N015 = hT_meas: ∀ (γ : Γ), MeasurableSet (γ • (B ∩ S γ))
-- N016 = goal: μ ((fun y => δ • y) '' B) = μ B

-- E001 represents h_001_hs_meas
-- E002 represents h_002_hb_eq
-- E003 represents h_004_hc_disjoint
-- E004 represents h_005_himage_eq
-- E005 represents h_007_ht_disjoint
-- E006 represents h_003_hc_meas
-- E007 represents h_006_ht_meas
-- E008 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (N008 : Prop)
    (N009 : Prop)
    (N010 : Prop)
    (N011 : Prop)
    (N012 : Prop)
    (N013 : Prop)
    (N014 : Prop)
    (N015 : Prop)
    (N016 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (B007 : N007)
    (B008 : N008)
    (E001 : N005 → N007 → N004 → N009)
    (E002 : N003 → N010)
    (E003 : N002 → N011)
    (E004 : N003 → N012)
    (E005 : N002 → N013)
    (E006 : N001 → N009 → N014)
    (E007 : N007 → N014 → N015)
    (E008 : N006 → N008 → N010 → N014 → N011 → N012 → N015 → N013 → N016)
    : N016 := by
  have H_N009 : N009 := E001 B005 B007 B004
  have H_N010 : N010 := E002 B003
  have H_N011 : N011 := E003 B002
  have H_N012 : N012 := E004 B003
  have H_N013 : N013 := E005 B002
  have H_N014 : N014 := E006 B001 H_N009
  have H_N015 : N015 := E007 B007 H_N014
  have H_N016 : N016 := E008 B006 B008 H_N010 H_N014 H_N011 H_N012 H_N015 H_N013
  exact H_N016

end TopologyCertificate_p1521_orbit_contained_free_action_restrict_measu
