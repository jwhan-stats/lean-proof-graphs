import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1089_logarithmic_average_bound
-- topology_sha256: 3b0de1941c8929d9339458ece58933b5a7be4f50c1f8629973513c008d4dd8c3
namespace TopologyCertificate_p1089_logarithmic_average_bound

-- N001 = ha: ∀ (n : { n // 0 < n }), ‖a n‖ ≤ 1
-- N002 = hB: B.Nonempty
-- N003 = hq: 0 < q
-- N004 = hS: 0 < S
-- N005 = hperiod: ∀ (i j : ℕ), w (i * q + j) = w j
-- N006 = htarget_period: target = (↑q)⁻¹ * ∑ j ∈ Finset.range q, w j ^ 2
-- N007 = hboundN: ∀ (N : ℕ), 0 < N → ‖A N a - Lℂ fun m => A (N / ↑m) fun k => a ⟨↑m * ↑k, ⋯⟩‖ ≤ √target + K / ↑N
-- N008 = hmain: ∀ (ε : ℝ), 0 < ε → Filter.limsup (fun N => ‖A N a - Lℂ fun m => A (N / ↑m) fun k => a ⟨↑m * ↑k, ⋯⟩‖) Filter.atTop ≤ √target + ε
-- N009 = goal: Filter.limsup (fun N => ‖A N a - Lℂ fun m => A (N / ↑m) fun k => a ⟨↑m * ↑k, ⋯⟩‖) Filter.atTop ≤ √(Lℝ fun m => Lℝ fun n => ↑((↑n).gcd ↑m) - 1)

-- E001 represents h_001_hq
-- E002 represents h_002_hs
-- E003 represents h_005_hperiod
-- E004 represents h_006_htarget_period
-- E005 represents h_007_hboundn
-- E006 represents h_008_hmain
-- E007 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (E001 : N003)
    (E002 : N002 → N004)
    (E003 : N005)
    (E004 : N002 → N006)
    (E005 : N002 → N001 → N003 → N004 → N005 → N006 → N007)
    (E006 : N007 → N008)
    (E007 : N008 → N009)
    : N009 := by
  have H_N003 : N003 := E001
  have H_N004 : N004 := E002 B002
  have H_N005 : N005 := E003
  have H_N006 : N006 := E004 B002
  have H_N007 : N007 := E005 B002 B001 H_N003 H_N004 H_N005 H_N006
  have H_N008 : N008 := E006 H_N007
  have H_N009 : N009 := E007 H_N008
  exact H_N009

end TopologyCertificate_p1089_logarithmic_average_bound
