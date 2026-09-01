import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0824_finite_category_mobius_zero
-- topology_sha256: fc0062b16cdb74302d0b069d001d3a9330b4878c76acd8c358807a4adc79c636
namespace TopologyCertificate_p0824_finite_category_mobius_zero

-- N001 = hμζ: ∀ (a c : A), ∑ b, μ a b * ↑(Fintype.card (b ⟶ c)) = if a = c then 1 else 0
-- N002 = hζμ: ∀ (a c : A), ∑ b, ↑(Fintype.card (a ⟶ b)) * μ b c = if a = c then 1 else 0
-- N003 = hab: IsEmpty (a ⟶ b)
-- N004 = hMZ: M * ζ = 1
-- N005 = hZM: ζ * M = 1
-- N006 = hζtri: ζ.BlockTriangular label
-- N007 = hbcard: Fintype.card (b ⟶ b) ≠ 0
-- N008 = hμtri: ζ⁻¹.BlockTriangular label
-- N009 = hinv: ζ⁻¹ = M
-- N010 = hlt: label b < label a
-- N011 = hzero: ζ⁻¹ a b = 0
-- N012 = this: M a b = 0
-- N013 = goal: M a b = 0

-- E001 represents h_001_hmz
-- E002 represents h_002_hzm
-- E003 represents h_003_h_tri
-- E004 represents h_006_hbcard
-- E005 represents h_004_h_tri
-- E006 represents h_005_hinv
-- E007 represents h_007_hlt
-- E008 represents h_008_hzero
-- E009 represents h_009_this
-- E010 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N001 → N004)
    (E002 : N002 → N005)
    (E003 : N006)
    (E004 : N007)
    (E005 : N005 → N006 → N008)
    (E006 : N004 → N009)
    (E007 : N003 → N007 → N010)
    (E008 : N008 → N010 → N011)
    (E009 : N009 → N011 → N012)
    (E010 : N012 → N013)
    : N013 := by
  have H_N004 : N004 := E001 B001
  have H_N005 : N005 := E002 B002
  have H_N006 : N006 := E003
  have H_N007 : N007 := E004
  have H_N008 : N008 := E005 H_N005 H_N006
  have H_N009 : N009 := E006 H_N004
  have H_N010 : N010 := E007 B003 H_N007
  have H_N011 : N011 := E008 H_N008 H_N010
  have H_N012 : N012 := E009 H_N009 H_N011
  have H_N013 : N013 := E010 H_N012
  exact H_N013

end TopologyCertificate_p0824_finite_category_mobius_zero
