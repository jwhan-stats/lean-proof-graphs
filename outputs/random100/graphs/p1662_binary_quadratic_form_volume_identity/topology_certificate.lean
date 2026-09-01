import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1662_binary_quadratic_form_volume_identity
-- topology_sha256: 36740eb1859b61cc84e98c0fba8102c8ee8ee7c1504f40a8dff4ff09d88d2761
namespace TopologyCertificate_p1662_binary_quadratic_form_volume_identity

-- N001 = ha: 0 < a
-- N002 = hc: c < 0
-- N003 = hlampos: 0 < lam
-- N004 = hlamroot: ↑a * lam ^ 2 + ↑b * lam + ↑c = 0
-- N005 = hmupos: 0 < mu
-- N006 = hmuroot: ↑a * mu ^ 2 + ↑(-2 * a - b) * mu + ↑(a + b + c) = 0
-- N007 = hmuunique: ∀ (x : ℝ), 0 < x → ↑a * x ^ 2 + ↑(-2 * a - b) * x + ↑(a + b + c) = 0 → x = mu
-- N008 = hsum: a + b + c < 0
-- N009 = hA: 0 < ↑a
-- N010 = hC: ↑c < 0
-- N011 = hsumR: ↑a + ↑b + ↑c < 0
-- N012 = hmurootR: ↑a * mu ^ 2 + (-2 * ↑a - ↑b) * mu + (↑a + ↑b + ↑c) = 0
-- N013 = hmuunique': ∀ (x : ℝ), 0 < x → ↑a * x ^ 2 + (-2 * ↑a - ↑b) * x + (↑a + ↑b + ↑c) = 0 → x = mu
-- N014 = hlamne: lam ≠ 0
-- N015 = hfmu: ↑a + (-2 * ↑a - ↑b) + (↑a + ↑b + ↑c) = ↑c
-- N016 = hlamgt: 1 < lam
-- N017 = hmu_at_one: ↑a + (-2 * ↑a - ↑b) + (↑a + ↑b + ↑c) < 0
-- N018 = hrel: 1 - ↑c / (↑a * lam) = mu
-- N019 = hAne: ↑a ≠ 0
-- N020 = hCne: ↑c ≠ 0
-- N021 = hsumne: ↑a + ↑b + ↑c ≠ 0
-- N022 = hmu_gt: 1 < mu
-- N023 = hcdiv: ↑c / (↑a * lam) = -(↑b / ↑a) - lam
-- N024 = hVlam: ↑a * lam * (lam - 1) * (1 + 1 / lam ^ 2 + 1 / (lam - 1) ^ 2) = ↑a * (lam ^ 2 - lam) + 2 * ↑a + ↑a * (↑a * lam + ↑b) / ↑c - ↑a * (↑a * lam + ↑a + ↑b) / (↑a + ↑b + ↑c)
-- N025 = hmlin: mu = lam + 1 + ↑b / ↑a
-- N026 = hVmu: ↑a * mu * (mu - 1) * (1 + 1 / mu ^ 2 + 1 / (mu - 1) ^ 2) = ↑a * (mu ^ 2 - mu) + 2 * ↑a + ↑a * (↑a * mu + (-2 * ↑a - ↑b)) / (↑a + ↑b + ↑c) - ↑a * (↑a * mu + ↑a + (-2 * ↑a - ↑b)) / (↑a + (-2 * ↑a - ↑b) + (↑a + ↑b + ↑c))
-- N027 = hquad: ↑a * (lam ^ 2 - lam) + ↑a * (mu ^ 2 - mu) = ↑b + ↑b ^ 2 / ↑a - 2 * ↑c
-- N028 = hrC: ↑a * (↑a * lam + ↑b) / ↑c - ↑a * (↑a * mu - ↑a - ↑b) / ↑c = ↑a * ↑b / ↑c
-- N029 = hrD: -↑a * (↑a * lam + ↑a + ↑b) / (↑a + ↑b + ↑c) + ↑a * (↑a * mu - 2 * ↑a - ↑b) / (↑a + ↑b + ↑c) = -↑a * (2 * ↑a + ↑b) / (↑a + ↑b + ↑c)
-- N030 = goal: ↑a * lam * (lam - 1) * (1 + 1 / lam ^ 2 + 1 / (lam - 1) ^ 2) + ↑a * mu * (mu - 1) * (1 + 1 / mu ^ 2 + 1 / (mu - 1) ^ 2) = 4 * ↑a + ↑b + ↑b ^ 2 / ↑a + ↑a * ↑b / ↑c - 2 * ↑c - ↑a * (2 * ↑a + ↑b) / (↑a + ↑b + ↑c)

-- E001 represents h_001_ha
-- E002 represents h_002_hc
-- E003 represents h_003_hsumr
-- E004 represents h_005_hmurootr
-- E005 represents h_008_hmuunique
-- E006 represents h_011_hlamne
-- E007 represents h_018_hfmu
-- E008 represents h_004_hlamgt
-- E009 represents h_006_hmu_at_one
-- E010 represents h_009_hrel
-- E011 represents h_010_hane
-- E012 represents h_012_hcne
-- E013 represents h_013_hsumne
-- E014 represents h_007_hmu_gt
-- E015 represents h_014_hcdiv
-- E016 represents h_016_hvlam
-- E017 represents h_015_hmlin
-- E018 represents h_017_hvmu
-- E019 represents h_019_hquad
-- E020 represents h_020_hrc
-- E021 represents h_021_hrd
-- E022 represents h_goal

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
    (N017 : Prop)
    (N018 : Prop)
    (N019 : Prop)
    (N020 : Prop)
    (N021 : Prop)
    (N022 : Prop)
    (N023 : Prop)
    (N024 : Prop)
    (N025 : Prop)
    (N026 : Prop)
    (N027 : Prop)
    (N028 : Prop)
    (N029 : Prop)
    (N030 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (B007 : N007)
    (B008 : N008)
    (E001 : N001 → N009)
    (E002 : N002 → N010)
    (E003 : N008 → N011)
    (E004 : N006 → N012)
    (E005 : N007 → N013)
    (E006 : N003 → N014)
    (E007 : N015)
    (E008 : N004 → N003 → N009 → N010 → N011 → N016)
    (E009 : N010 → N017)
    (E010 : N004 → N003 → N009 → N010 → N013 → N018)
    (E011 : N009 → N019)
    (E012 : N010 → N020)
    (E013 : N011 → N021)
    (E014 : N005 → N009 → N011 → N012 → N017 → N022)
    (E015 : N004 → N019 → N014 → N023)
    (E016 : N004 → N003 → N009 → N010 → N011 → N016 → N024)
    (E017 : N018 → N023 → N025)
    (E018 : N005 → N009 → N011 → N012 → N017 → N022 → N026)
    (E019 : N004 → N019 → N025 → N027)
    (E020 : N019 → N020 → N025 → N028)
    (E021 : N019 → N021 → N025 → N029)
    (E022 : N024 → N026 → N015 → N027 → N028 → N029 → N030)
    : N030 := by
  have H_N009 : N009 := E001 B001
  have H_N010 : N010 := E002 B002
  have H_N011 : N011 := E003 B008
  have H_N012 : N012 := E004 B006
  have H_N013 : N013 := E005 B007
  have H_N014 : N014 := E006 B003
  have H_N015 : N015 := E007
  have H_N016 : N016 := E008 B004 B003 H_N009 H_N010 H_N011
  have H_N017 : N017 := E009 H_N010
  have H_N018 : N018 := E010 B004 B003 H_N009 H_N010 H_N013
  have H_N019 : N019 := E011 H_N009
  have H_N020 : N020 := E012 H_N010
  have H_N021 : N021 := E013 H_N011
  have H_N022 : N022 := E014 B005 H_N009 H_N011 H_N012 H_N017
  have H_N023 : N023 := E015 B004 H_N019 H_N014
  have H_N024 : N024 := E016 B004 B003 H_N009 H_N010 H_N011 H_N016
  have H_N025 : N025 := E017 H_N018 H_N023
  have H_N026 : N026 := E018 B005 H_N009 H_N011 H_N012 H_N017 H_N022
  have H_N027 : N027 := E019 B004 H_N019 H_N025
  have H_N028 : N028 := E020 H_N019 H_N020 H_N025
  have H_N029 : N029 := E021 H_N019 H_N021 H_N025
  have H_N030 : N030 := E022 H_N024 H_N026 H_N015 H_N027 H_N028 H_N029
  exact H_N030

end TopologyCertificate_p1662_binary_quadratic_form_volume_identity
