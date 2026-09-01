import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2476_approximatepointspectrum_subset_closure_sc
-- topology_sha256: 0c595635aee944b581bdaea9c8a2ecb86c55cb527f19e24cd9f57e497d699998
namespace TopologyCertificate_p2476_approximatepointspectrum_subset_closure_sc

-- N001 = hw: w ∈ {w | ∃ x, (∀ (n : ℕ), ‖x n‖ = 1) ∧ Filter.Tendsto (fun n => ‖T (x n) - w • x n‖) Filter.atTop (nhds 0)}
-- N002 = goal: w ∈ closure {z | ∃ x, ‖x‖ = 1 ∧ let a := (inner ℂ (T x) x).re; let b := √(‖T x‖ ^ 2 - a ^ 2); z = ↑a + Complex.I * ↑b ∨ z = ↑a - Complex.I * ↑b}

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    : N002 := by
  have H_N002 : N002 := E001 B001
  exact H_N002

end TopologyCertificate_p2476_approximatepointspectrum_subset_closure_sc
