import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1639_relative_commuting_probability_le
-- topology_sha256: 238ee4d8a7cc5f36548c7db5590c508e76736bd9d1fa902a5b8e58d80fd2b1f5
namespace TopologyCertificate_p1639_relative_commuting_probability_le

-- N001 = inst._@.proofs.3607020331._hygCtx._hyg.13: N.Normal
-- N002 = inst._@.proofs.3607020331._hygCtx._hyg.6: Finite G
-- N003 = hnat: A ≤ B * C
-- N004 = hK: Nat.card ↥I * Nat.card ↥Kbar = Nat.card ↥K
-- N005 = hG: Nat.card (G ⧸ N) * Nat.card ↥N = Nat.card G
-- N006 = hnonneg: 0 ≤ ↑(Nat.card ↥K) * ↑(Nat.card G)
-- N007 = hden: ↑(Nat.card ↥K) * ↑(Nat.card G) = ↑(Nat.card ↥Kbar) * ↑(Nat.card (G ⧸ N)) * (↑(Nat.card ↥I) * ↑(Nat.card ↥N))
-- N008 = hnum: ↑A ≤ ↑(B * C)
-- N009 = hfactor: ↑B / (↑(Nat.card ↥Kbar) * ↑(Nat.card (G ⧸ N))) * (↑C / (↑(Nat.card ↥I) * ↑(Nat.card ↥N))) = ↑(B * C) / (↑(Nat.card ↥K) * ↑(Nat.card G))
-- N010 = goal: ↑A / (↑(Nat.card ↥K) * ↑(Nat.card G)) ≤ ↑(Nat.card { p // Commute (↑p.1) p.2 }) / (↑(Nat.card ↥Kbar) * ↑(Nat.card (G ⧸ N))) * (↑(Nat.card { p // Commute (↑p.1) p.2 }) / (↑(Nat.card ↥(Subgroup.comap N.subtype K)) * ↑(Nat.card ↥N)))

-- E001 represents h_001_hnat
-- E002 represents h_002_hk
-- E003 represents h_003_hg
-- E004 represents h_006_hnonneg
-- E005 represents h_004_hden
-- E006 represents h_005_hnum
-- E007 represents h_007_hfactor
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
    (B001 : N001)
    (B002 : N002)
    (E001 : N002 → N001 → N003)
    (E002 : N002 → N001 → N004)
    (E003 : N005)
    (E004 : N006)
    (E005 : N001 → N004 → N005 → N007)
    (E006 : N003 → N008)
    (E007 : N001 → N007 → N009)
    (E008 : N001 → N008 → N006 → N009 → N010)
    : N010 := by
  have H_N003 : N003 := E001 B002 B001
  have H_N004 : N004 := E002 B002 B001
  have H_N005 : N005 := E003
  have H_N006 : N006 := E004
  have H_N007 : N007 := E005 B001 H_N004 H_N005
  have H_N008 : N008 := E006 H_N003
  have H_N009 : N009 := E007 B001 H_N007
  have H_N010 : N010 := E008 B001 H_N008 H_N006 H_N009
  exact H_N010

end TopologyCertificate_p1639_relative_commuting_probability_le
