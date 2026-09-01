import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p3186_simple_selection_adjusted_control
-- topology_sha256: b0f7f4c727852f78068688119b340d3a29b8ebac79c40c2a5cff0c871b481cac
namespace TopologyCertificate_p3186_simple_selection_adjusted_control

-- N001 = hC_measurable: ∀ (i : Fin m) (α : ℝ), Measurable (C i α)
-- N002 = hC_nonnegative: ∀ (i : Fin m) (α : ℝ) (p : Fin (n i) → ↑(Set.Icc 0 1)), 0 ≤ C i α p
-- N003 = hC_valid: ∀ (i : Fin m), ∀ α ∈ Set.Icc 0 1, MeasureTheory.Integrable (fun ω => C i α (P i ω)) μ ∧ ∫ (ω : Ω), C i α (P i ω) ∂μ ≤ α
-- N004 = hm: 0 < m
-- N005 = hP_independent: ProbabilityTheory.iIndepFun P μ
-- N006 = hP_measurable: ∀ (i : Fin m), Measurable (P i)
-- N007 = hq: q ∈ Set.Icc 0 1
-- N008 = hS_measurable: ∀ (s : Finset (Fin m)), MeasurableSet (S ⁻¹' {s})
-- N009 = hS_simple: ∀ (i : Fin m) (x y : (i : Fin m) → Fin (n i) → ↑(Set.Icc 0 1)), (∀ (j : Fin m), j ≠ i → x j = y j) → i ∈ S x → i ∈ S y → (S x).card = (S y).card
-- N010 = inst._@.proofs.72374644._hygCtx._hyg.8: MeasureTheory.IsProbabilityMeasure μ
-- N011 = hF_measurable: Measurable F
-- N012 = hY_measurable: Measurable Y
-- N013 = hY_nonneg: 0 ≤ᵐ[μ] fun ω => Y (F ω)
-- N014 = hfun: (fun ω => if (S fun i => P i ω).card = 0 then 0 else (∑ i ∈ S fun j => P j ω, C i (↑(S fun j => P j ω).card * q / ↑m) (P i ω)) / ↑(S fun j => P j ω).card) = fun ω => Y (F ω)
-- N015 = hνprob: ∀ (j : Fin m), MeasureTheory.IsProbabilityMeasure (MeasureTheory.Measure.map (P j) μ)
-- N016 = hjoint_infinite: MeasureTheory.Measure.map F μ = MeasureTheory.Measure.infinitePi fun j => MeasureTheory.Measure.map (P j) μ
-- N017 = hpi_bound: (∫⁻ (x : (i : Fin m) → Fin (n i) → ↑(Set.Icc 0 1)), ENNReal.ofReal (Y x) ∂MeasureTheory.Measure.pi fun j => MeasureTheory.Measure.map (P j) μ) ≤ ENNReal.ofReal q
-- N018 = hYF_measurable: Measurable fun ω => Y (F ω)
-- N019 = hjoint: MeasureTheory.Measure.map F μ = MeasureTheory.Measure.pi fun j => MeasureTheory.Measure.map (P j) μ
-- N020 = hYenn_measurable: Measurable fun x => ENNReal.ofReal (Y x)
-- N021 = hintegral_eq: ∫ (ω : Ω), Y (F ω) ∂μ = (∫⁻ (ω : Ω), ENNReal.ofReal (Y (F ω)) ∂μ).toReal
-- N022 = hlintegral_map: ∫⁻ (x : Rollout_p3186_simple_selection_adjusted_control.SimpleSelectionAdjustedControl.PTuple m n), ENNReal.ofReal (Y x) ∂MeasureTheory.Measure.map F μ = ∫⁻ (ω : Ω), ENNReal.ofReal (Y (F ω)) ∂μ
-- N023 = hlintegral_source_pi: ∫⁻ (ω : Ω), ENNReal.ofReal (Y (F ω)) ∂μ = ∫⁻ (x : (i : Fin m) → Fin (n i) → ↑(Set.Icc 0 1)), ENNReal.ofReal (Y x) ∂MeasureTheory.Measure.pi fun j => MeasureTheory.Measure.map (P j) μ
-- N024 = goal: ∫ (ω : Ω), if (S fun i => P i ω).card = 0 then 0 else (∑ i ∈ S fun j => P j ω, C i (↑(S fun j => P j ω).card * q / ↑m) (P i ω)) / ↑(S fun j => P j ω).card ∂μ ≤ q

-- E001 represents h_001_hf_measurable
-- E002 represents h_002_hy_measurable
-- E003 represents h_004_hy_nonneg
-- E004 represents h_006_hfun
-- E005 represents h_007_h_prob
-- E006 represents h_008_hjoint_infinite
-- E007 represents h_013_hpi_bound
-- E008 represents h_003_hyf_measurable
-- E009 represents h_009_hjoint
-- E010 represents h_010_hyenn_measurable
-- E011 represents h_005_hintegral_eq
-- E012 represents h_011_hlintegral_map
-- E013 represents h_012_hlintegral_source_pi
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
    (E001 : N006 → N011)
    (E002 : N008 → N001 → N012)
    (E003 : N002 → N013)
    (E004 : N014)
    (E005 : N010 → N006 → N015)
    (E006 : N010 → N006 → N005 → N016)
    (E007 : N010 → N004 → N007 → N006 → N008 → N009 → N001 → N002 → N003 → N017)
    (E008 : N011 → N012 → N018)
    (E009 : N015 → N016 → N019)
    (E010 : N012 → N020)
    (E011 : N018 → N013 → N021)
    (E012 : N011 → N020 → N022)
    (E013 : N019 → N022 → N023)
    (E014 : N007 → N021 → N014 → N023 → N017 → N024)
    : N024 := by
  have H_N011 : N011 := E001 B006
  have H_N012 : N012 := E002 B008 B001
  have H_N013 : N013 := E003 B002
  have H_N014 : N014 := E004
  have H_N015 : N015 := E005 B010 B006
  have H_N016 : N016 := E006 B010 B006 B005
  have H_N017 : N017 := E007 B010 B004 B007 B006 B008 B009 B001 B002 B003
  have H_N018 : N018 := E008 H_N011 H_N012
  have H_N019 : N019 := E009 H_N015 H_N016
  have H_N020 : N020 := E010 H_N012
  have H_N021 : N021 := E011 H_N018 H_N013
  have H_N022 : N022 := E012 H_N011 H_N020
  have H_N023 : N023 := E013 H_N019 H_N022
  have H_N024 : N024 := E014 B007 H_N021 H_N014 H_N023 H_N017
  exact H_N024

end TopologyCertificate_p3186_simple_selection_adjusted_control
