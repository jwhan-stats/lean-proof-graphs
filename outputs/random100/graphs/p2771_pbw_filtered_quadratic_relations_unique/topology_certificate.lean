import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2771_pbw_filtered_quadratic_relations_unique
-- topology_sha256: 777fa7833f8e565a5d771438cc1a0f128e4aa716361332d85c3e8108d8326c4c
namespace TopologyCertificate_p2771_pbw_filtered_quadratic_relations_unique

-- N001 = hP₂: P ⊆ ⨆ i, ↑(𝒯 ↑i)
-- N002 = hPI: TwoSidedIdeal.span P = I
-- N003 = hPpbw: ∀ (n : ℕ), ∀ x ∈ 𝒯 n, x ∈ TwoSidedIdeal.span (⇑(GradedAlgebra.proj 𝒯 2) '' P) ↔ ∃ y ∈ I, x - y ∈ ⨆ i, 𝒯 ↑i
-- N004 = hQ₂: Q ⊆ ⨆ i, ↑(𝒯 ↑i)
-- N005 = hQI: TwoSidedIdeal.span Q = I
-- N006 = hQpbw: ∀ (n : ℕ), ∀ x ∈ 𝒯 n, x ∈ TwoSidedIdeal.span (⇑(GradedAlgebra.proj 𝒯 2) '' Q) ↔ ∃ y ∈ I, x - y ∈ ⨆ i, 𝒯 ↑i
-- N007 = hPsub: P ⊆ ↑B
-- N008 = hQsub: Q ⊆ ↑A
-- N009 = hAleB: A ≤ B
-- N010 = hBleA: B ≤ A
-- N011 = hAB: A = B
-- N012 = goal: AddSubgroup.closure {x | ∃ a ∈ 𝒯 0, ∃ p ∈ P, ∃ b ∈ 𝒯 0, x = a * p * b} = AddSubgroup.closure {x | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b} ∧ (((∃ M, ↑M = P ∧ (∀ (a : ↥(𝒯 0)), ∀ x ∈ M, ↑a * x ∈ M) ∧ ∀ (a : ↥(𝒯 0)), ∀ x ∈ M, x * ↑a ∈ M) ∧ ∃ N, ↑N = Q ∧ (∀ (a : ↥(𝒯 0)), ∀ x ∈ N, ↑a * x ∈ N) ∧ ∀ (a : ↥(𝒯 0)), ∀ x ∈ N, x * ↑a ∈ N) → P = Q)

-- E001 represents h_001_hpsub
-- E002 represents h_002_hqsub
-- E003 represents h_003_haleb
-- E004 represents h_004_hblea
-- E005 represents h_005_hab
-- E006 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (E001 : N001 → N004 → N002 → N005 → N003 → N006 → N007)
    (E002 : N001 → N004 → N002 → N005 → N003 → N006 → N008)
    (E003 : N007 → N009)
    (E004 : N008 → N010)
    (E005 : N009 → N010 → N011)
    (E006 : N011 → N012)
    : N012 := by
  have H_N007 : N007 := E001 B001 B004 B002 B005 B003 B006
  have H_N008 : N008 := E002 B001 B004 B002 B005 B003 B006
  have H_N009 : N009 := E003 H_N007
  have H_N010 : N010 := E004 H_N008
  have H_N011 : N011 := E005 H_N009 H_N010
  have H_N012 : N012 := E006 H_N011
  exact H_N012

end TopologyCertificate_p2771_pbw_filtered_quadratic_relations_unique
