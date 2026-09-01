import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0971_derivwithin_neg_of_positive_solution
-- topology_sha256: 253a8736d821304a70bd1dc324f603e5e16229c1ee25c0de4161930c7617de03
namespace TopologyCertificate_p0971_derivwithin_neg_of_positive_solution

-- N001 = hΦ: ContDiffOn ℝ 1 Φ (Set.Icc 0 β)
-- N002 = hβ: 0 < β
-- N003 = hf0: f 0 = 0
-- N004 = hfpos: ∀ t ∈ Set.Ioc 0 β, 0 < f t
-- N005 = hlam: 0 < lam
-- N006 = hn: 2 ≤ n
-- N007 = hODE: ∀ t ∈ Set.Ioo 0 β, deriv Φ t + lam * f t ^ (n - 1) * ψ (T t) = 0
-- N008 = ht: t ∈ Set.Ioc 0 β
-- N009 = hTpos: ∀ t ∈ Set.Ioo 0 β, 0 < T t
-- N010 = hψneg_iff: ∀ (s : ℝ), ψ s < 0 ↔ s < 0
-- N011 = hψpos_iff: ∀ (s : ℝ), 0 < ψ s ↔ 0 < s
-- N012 = hn1: n - 1 ≠ 0
-- N013 = htpos: 0 < t
-- N014 = htβ: t ≤ β
-- N015 = hmem0: 0 ∈ Set.Icc 0 β
-- N016 = hderivneg: ∀ t ∈ interior (Set.Icc 0 β), deriv Φ t < 0
-- N017 = hΦ0: Φ 0 = 0
-- N018 = hmemt: t ∈ Set.Icc 0 β
-- N019 = hf_t: 0 < f t
-- N020 = hanti: StrictAntiOn Φ (Set.Icc 0 β)
-- N021 = hpow: 0 < f t ^ (n - 1)
-- N022 = hΦt_neg: Φ t < 0
-- N023 = hprod_neg: f t ^ (n - 1) * ψ (derivWithin T (Set.Icc 0 β) t) < 0
-- N024 = hψderiv_neg: ψ (derivWithin T (Set.Icc 0 β) t) < 0
-- N025 = goal: derivWithin T (Set.Icc 0 β) t < 0

-- E001 represents h_001_h_neg_iff
-- E002 represents h_002_h_pos_iff
-- E003 represents h_005_hn1
-- E004 represents h_007_htpos
-- E005 represents h_008_ht
-- E006 represents h_009_hmem0
-- E007 represents h_003_hderivneg
-- E008 represents h_006_h_0
-- E009 represents h_010_hmemt
-- E010 represents h_013_hf_t
-- E011 represents h_004_hanti
-- E012 represents h_014_hpow
-- E013 represents h_011_h_t_neg
-- E014 represents h_012_hprod_neg
-- E015 represents h_015_h_deriv_neg
-- E016 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (B007 : N007)
    (B008 : N008)
    (B009 : N009)
    (E001 : N010)
    (E002 : N011)
    (E003 : N006 → N012)
    (E004 : N008 → N013)
    (E005 : N008 → N014)
    (E006 : N002 → N015)
    (E007 : N005 → N004 → N007 → N009 → N011 → N016)
    (E008 : N003 → N012 → N017)
    (E009 : N013 → N014 → N018)
    (E010 : N004 → N013 → N014 → N019)
    (E011 : N001 → N016 → N020)
    (E012 : N019 → N021)
    (E013 : N020 → N017 → N013 → N015 → N018 → N022)
    (E014 : N022 → N023)
    (E015 : N023 → N021 → N024)
    (E016 : N010 → N024 → N025)
    : N025 := by
  have H_N010 : N010 := E001
  have H_N011 : N011 := E002
  have H_N012 : N012 := E003 B006
  have H_N013 : N013 := E004 B008
  have H_N014 : N014 := E005 B008
  have H_N015 : N015 := E006 B002
  have H_N016 : N016 := E007 B005 B004 B007 B009 H_N011
  have H_N017 : N017 := E008 B003 H_N012
  have H_N018 : N018 := E009 H_N013 H_N014
  have H_N019 : N019 := E010 B004 H_N013 H_N014
  have H_N020 : N020 := E011 B001 H_N016
  have H_N021 : N021 := E012 H_N019
  have H_N022 : N022 := E013 H_N020 H_N017 H_N013 H_N015 H_N018
  have H_N023 : N023 := E014 H_N022
  have H_N024 : N024 := E015 H_N023 H_N021
  have H_N025 : N025 := E016 H_N010 H_N024
  exact H_N025

end TopologyCertificate_p0971_derivwithin_neg_of_positive_solution
