import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0273_weighted_one_dimensional_dirichlet_lower_b
-- topology_sha256: 85a9ca16859e3f43eb966e57535a3693c8d641cc05d9875fedaae5db579da175
namespace TopologyCertificate_p0273_weighted_one_dimensional_dirichlet_lower_b

-- N001 = hθ0: 0 < θ₀
-- N002 = hθ1: θ₀ < 2 * Real.pi
-- N003 = hφac: AbsolutelyContinuousOnInterval φ 0 (2 * Real.pi)
-- N004 = hφderivL2: MeasureTheory.MemLp (deriv φ) 2 (MeasureTheory.volume.restrict (Set.Icc 0 (2 * Real.pi)))
-- N005 = hφend: φ (2 * Real.pi) - φ 0 = 2 * Real.pi
-- N006 = hαmeas: AEMeasurable α (MeasureTheory.volume.restrict (Set.Icc 0 (2 * Real.pi)))
-- N007 = hαmeasure: (MeasureTheory.volume.restrict (Set.Icc 0 (2 * Real.pi))) {θ | α θ = b ^ 2} = ENNReal.ofReal θ₀
-- N008 = hαvalues: ∀ᵐ (θ : ℝ) ∂MeasureTheory.volume.restrict (Set.Icc 0 (2 * Real.pi)), α θ ∈ {b ^ 2, 1}
-- N009 = hb0: 0 < b
-- N010 = hb1: b < 1
-- N011 = h0le: 0 ≤ 2 * Real.pi
-- N012 = hcs: L ^ 2 ≤ C * D
-- N013 = hD: D = 2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1)
-- N014 = hLnonneg: 0 ≤ L
-- N015 = hb2lt1: b ^ 2 < 1
-- N016 = hinterval_to_restrict: ∀ (f : ℝ → ℝ), ∫ (θ : ℝ) in 0..2 * Real.pi, f θ = ∫ (θ : ℝ), f θ ∂μ
-- N017 = hinv_gt_one: 1 < (b ^ 2)⁻¹
-- N018 = hIntg: ∫ (θ : ℝ), deriv φ θ ∂μ = 2 * Real.pi
-- N019 = hdenpos: 0 < 2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1)
-- N020 = hCeq: ∫ (θ : ℝ) in 0..2 * Real.pi, α θ * |deriv φ θ| ^ 2 = C
-- N021 = hLlower: 2 * Real.pi ≤ L
-- N022 = hTsq_le_Lsq: (2 * Real.pi) ^ 2 ≤ L ^ 2
-- N023 = hmain: 2 * Real.pi ^ 2 / (2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1)) ≤ 1 / 2 * C
-- N024 = goal: 1 / 2 * ∫ (θ : ℝ) in 0..2 * Real.pi, α θ * |deriv φ θ| ^ 2 ≥ 2 * Real.pi ^ 2 / (2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1))

-- E001 represents h_001_h0le
-- E002 represents h_003_hcs
-- E003 represents h_004_hd
-- E004 represents h_007_hlnonneg
-- E005 represents h_010_hb2lt1
-- E006 represents h_002_hinterval_to_restrict
-- E007 represents h_011_hinv_gt_one
-- E008 represents h_005_hintg
-- E009 represents h_012_hdenpos
-- E010 represents h_014_hceq
-- E011 represents h_006_hllower
-- E012 represents h_008_htsq_le_lsq
-- E013 represents h_013_hmain
-- E014 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (B007 : N007)
    (B008 : N008)
    (B009 : N009)
    (B010 : N010)
    (E001 : N011)
    (E002 : N009 → N010 → N006 → N008 → N004 → N012)
    (E003 : N009 → N010 → N001 → N002 → N006 → N008 → N007 → N013)
    (E004 : N014)
    (E005 : N009 → N010 → N015)
    (E006 : N011 → N016)
    (E007 : N009 → N015 → N017)
    (E008 : N003 → N005 → N016 → N018)
    (E009 : N009 → N010 → N001 → N002 → N017 → N019)
    (E010 : N016 → N020)
    (E011 : N011 → N018 → N021)
    (E012 : N011 → N021 → N014 → N022)
    (E013 : N012 → N013 → N022 → N019 → N023)
    (E014 : N023 → N020 → N024)
    : N024 := by
  have H_N011 : N011 := E001
  have H_N012 : N012 := E002 B009 B010 B006 B008 B004
  have H_N013 : N013 := E003 B009 B010 B001 B002 B006 B008 B007
  have H_N014 : N014 := E004
  have H_N015 : N015 := E005 B009 B010
  have H_N016 : N016 := E006 H_N011
  have H_N017 : N017 := E007 B009 H_N015
  have H_N018 : N018 := E008 B003 B005 H_N016
  have H_N019 : N019 := E009 B009 B010 B001 B002 H_N017
  have H_N020 : N020 := E010 H_N016
  have H_N021 : N021 := E011 H_N011 H_N018
  have H_N022 : N022 := E012 H_N011 H_N021 H_N014
  have H_N023 : N023 := E013 H_N012 H_N013 H_N022 H_N019
  have H_N024 : N024 := E014 H_N023 H_N020
  exact H_N024

end TopologyCertificate_p0273_weighted_one_dimensional_dirichlet_lower_b
