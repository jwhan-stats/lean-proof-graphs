import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0960_antitone_monotone_power_sum_inequality
-- topology_sha256: e4cd917d0aebd07d32c97b0a51e0e5210516236764cf68793d96a95ef4c7844f
namespace TopologyCertificate_p0960_antitone_monotone_power_sum_inequality

-- N001 = ha: ∀ (i : Fin k), 0 ≤ a i
-- N002 = ha_antitone: Antitone a
-- N003 = hb: ∀ (i : Fin k), 0 ≤ b i
-- N004 = hb_monotone: Monotone b
-- N005 = hs: 1 ≤ s
-- N006 = hWnonneg: ∀ (i j : Fin k), 0 ≤ W i j
-- N007 = hU: ∑ i, ∑ j, U i j = C * D
-- N008 = hV: ∑ i, ∑ j, V i j = A * B
-- N009 = hsumW: 0 ≤ ∑ i, ∑ j, W i j
-- N010 = hUs: ∑ i, ∑ j, U j i = C * D
-- N011 = hVs: ∑ i, ∑ j, V j i = A * B
-- N012 = hsumEq: ∑ i, ∑ j, W i j = 2 * (C * D - A * B)
-- N013 = hdiff: 0 ≤ C * D - A * B
-- N014 = hle: A * B ≤ C * D
-- N015 = goal: (∑ i, (a i).rpow s) * ∑ i, a i ^ 2 * b i ≤ (∑ i, (a i).rpow (s + 1)) * ∑ i, a i * b i

-- E001 represents h_001_hwnonneg
-- E002 represents h_003_hu
-- E003 represents h_005_hv
-- E004 represents h_002_hsumw
-- E005 represents h_004_hus
-- E006 represents h_006_hvs
-- E007 represents h_007_hsumeq
-- E008 represents h_008_hdiff
-- E009 represents h_009_hle
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
    (N014 : Prop)
    (N015 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (E001 : N005 → N001 → N003 → N002 → N004 → N006)
    (E002 : N007)
    (E003 : N008)
    (E004 : N006 → N009)
    (E005 : N007 → N010)
    (E006 : N008 → N011)
    (E007 : N007 → N010 → N008 → N011 → N012)
    (E008 : N009 → N012 → N013)
    (E009 : N013 → N014)
    (E010 : N014 → N015)
    : N015 := by
  have H_N006 : N006 := E001 B005 B001 B003 B002 B004
  have H_N007 : N007 := E002
  have H_N008 : N008 := E003
  have H_N009 : N009 := E004 H_N006
  have H_N010 : N010 := E005 H_N007
  have H_N011 : N011 := E006 H_N008
  have H_N012 : N012 := E007 H_N007 H_N010 H_N008 H_N011
  have H_N013 : N013 := E008 H_N009 H_N012
  have H_N014 : N014 := E009 H_N013
  have H_N015 : N015 := E010 H_N014
  exact H_N015

end TopologyCertificate_p0960_antitone_monotone_power_sum_inequality
