import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p3094_finite_multiplicative_ratio_sums
-- topology_sha256: 0f727dd412e7486054192c1914622fb71cd63ecb637578f20f992a8d2ee24e80
namespace TopologyCertificate_p3094_finite_multiplicative_ratio_sums

-- N001 = hr_mul: ∀ (e d b : I), r (e, d) = r (e, b) * r (b, d)
-- N002 = hr_pos: ∀ (e d : I), 0 < r (e, d)
-- N003 = inst._@.proofs.1328577087._hygCtx._hyg.6: Nonempty I
-- N004 = hdiag: ∀ (e : I), r (e, e) = 1
-- N005 = hsum_pos: ∀ (e : I), 0 < ∑ d, r (d, e)
-- N006 = hinv: ∀ (e d : I), (r (e, d))⁻¹ = r (d, e)
-- N007 = hsum_ne: ∀ (e : I), ∑ d, r (d, e) ≠ 0
-- N008 = hA: ∑ e, (∑ d, r (d, e))⁻¹ = 1
-- N009 = hB: (∑ e, r (b, e)) / ∑ d, (r (d, b))⁻¹ = 1
-- N010 = hC: (∑ e, r (e, b)) / ∑ d, r (d, b) = 1
-- N011 = goal: ∑ e, (∑ d, r (d, e))⁻¹ = (∑ e, r (b, e)) / ∑ d, (r (d, b))⁻¹ ∧ (∑ e, r (b, e)) / ∑ d, (r (d, b))⁻¹ = (∑ e, r (e, b)) / ∑ d, r (d, b) ∧ (∑ e, r (e, b)) / ∑ d, r (d, b) = 1

-- E001 represents h_001_hdiag
-- E002 represents h_003_hsum_pos
-- E003 represents h_002_hinv
-- E004 represents h_004_hsum_ne
-- E005 represents h_005_ha
-- E006 represents h_006_hb
-- E007 represents h_007_hc
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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N002 → N001 → N004)
    (E002 : N003 → N002 → N005)
    (E003 : N001 → N004 → N006)
    (E004 : N005 → N007)
    (E005 : N001 → N006 → N007 → N008)
    (E006 : N003 → N002 → N006 → N009)
    (E007 : N007 → N010)
    (E008 : N008 → N009 → N010 → N011)
    : N011 := by
  have H_N004 : N004 := E001 B002 B001
  have H_N005 : N005 := E002 B003 B002
  have H_N006 : N006 := E003 B001 H_N004
  have H_N007 : N007 := E004 H_N005
  have H_N008 : N008 := E005 B001 H_N006 H_N007
  have H_N009 : N009 := E006 B003 B002 H_N006
  have H_N010 : N010 := E007 H_N007
  have H_N011 : N011 := E008 H_N008 H_N009 H_N010
  exact H_N011

end TopologyCertificate_p3094_finite_multiplicative_ratio_sums
