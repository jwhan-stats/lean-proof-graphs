import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p2476_approximatepointspectrum_subset_closure_sc
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 0c595635aee944b581bdaea9c8a2ecb86c55cb527f19e24cd9f57e497d699998
-- reconstructed_proof_sha256: 5d8ea053d9be55b631b620d799cac392ef98ec73b3e2af01ed7eef248a1ede21
-- selected_edge_count: 1

/- accepted add_to_file helper 1 -/
lemma srg_sqrt_sq_add_sq_le_abs_add {u q : ℝ} (hq : 0 ≤ q) :
    Real.sqrt (u ^ 2 + q ^ 2) ≤ |u| + q := by
  apply le_of_sq_le_sq
  · rw [Real.sq_sqrt (by positivity)]
    nlinarith [sq_abs u, abs_nonneg u, hq]
  · positivity

lemma srg_abs_sub_sqrt_sq_add_sq_le {u q : ℝ} (hq : 0 ≤ q) :
    |(|u| - Real.sqrt (u ^ 2 + q ^ 2))| ≤ q := by
  have hupper : Real.sqrt (u ^ 2 + q ^ 2) ≤ |u| + q :=
    srg_sqrt_sq_add_sq_le_abs_add hq
  have hlower : |u| ≤ Real.sqrt (u ^ 2 + q ^ 2) := by
    apply Real.abs_le_sqrt
    nlinarith [sq_nonneg q]
  rw [abs_sub_le_iff]
  constructor
  · nlinarith [Real.sqrt_nonneg (u ^ 2 + q ^ 2)]
  · nlinarith

lemma scaledRelativeGraph_polar_approx
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) {x : H} (hx : ‖x‖ = 1) (w : ℂ) :
    ∃ z : ℂ,
      (let a : ℝ := (inner ℂ (T x) x).re
       let b : ℝ := Real.sqrt (‖T x‖ ^ 2 - a ^ 2)
       z = (a : ℂ) + Complex.I * (b : ℂ) ∨
         z = (a : ℂ) - Complex.I * (b : ℂ)) ∧
      dist w z ≤ 2 * ‖T x - w • x‖ := by
  let α : ℂ := inner ℂ (T x) x
  let c : ℂ := star α
  let y : H := T x - c • x
  let a : ℝ := α.re
  let b : ℝ := Real.sqrt (‖T x‖ ^ 2 - a ^ 2)
  have hyx : inner ℂ y x = 0 := by
    dsimp [y, c, α]
    rw [inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K, hx]
    simp
  have hxy : inner ℂ x y = 0 := (inner_eq_zero_symm).1 hyx
  have hortho : inner ℂ (c • x) y = 0 := by
    rw [inner_smul_left, hxy]
    simp
  have hpyth : ‖c • x + y‖ ^ 2 = ‖c • x‖ ^ 2 + ‖y‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (c • x) y hortho
    nlinarith
  have hTxeq : c • x + y = T x := by
    simp [y]
  rw [hTxeq] at hpyth
  have hc : ‖c • x‖ = ‖c‖ := by
    simp [norm_smul, hx]
  have hcn : ‖c • x‖ ^ 2 = ‖c‖ ^ 2 := by
    rw [hc]
  have hcre : c.re = a := by
    dsimp [c, a, α]
  have hc_sq : ‖c‖ ^ 2 = a ^ 2 + c.im ^ 2 := by
    calc
      ‖c‖ ^ 2 = Complex.normSq c := by
        rw [Complex.normSq_eq_norm_sq]
      _ = c.re * c.re + c.im * c.im := by
        rw [Complex.normSq_apply]
      _ = a ^ 2 + c.im ^ 2 := by
        rw [hcre]
        ring
  have hb_sq : ‖T x‖ ^ 2 - a ^ 2 = c.im ^ 2 + ‖y‖ ^ 2 := by
    nlinarith
  have hb : b = Real.sqrt (c.im ^ 2 + ‖y‖ ^ 2) := by
    dsimp [b]
    rw [hb_sq]
  have horthod : inner ℂ ((c - w) • x) y = 0 := by
    rw [inner_smul_left, hxy]
    simp
  have hdeq : T x - w • x = (c - w) • x + y := by
    rw [sub_smul]
    simp [y]
  have hpythd : ‖(c - w) • x + y‖ ^ 2 = ‖(c - w) • x‖ ^ 2 + ‖y‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ((c - w) • x) y horthod
    nlinarith
  rw [← hdeq] at hpythd
  have hcwn : ‖(c - w) • x‖ = ‖c - w‖ := by
    simp [norm_smul, hx]
  have hcwnsq : ‖(c - w) • x‖ ^ 2 = ‖c - w‖ ^ 2 := by
    rw [hcwn]
  have hcw_sq : ‖c - w‖ ^ 2 ≤ ‖T x - w • x‖ ^ 2 := by
    nlinarith [sq_nonneg ‖y‖]
  have hy_sq : ‖y‖ ^ 2 ≤ ‖T x - w • x‖ ^ 2 := by
    nlinarith [sq_nonneg ‖c - w‖]
  have hcw_le : ‖c - w‖ ≤ ‖T x - w • x‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hcw_sq
  have hy_le : ‖y‖ ≤ ‖T x - w • x‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hy_sq
  have hsqrt_abs : |(|c.im| - Real.sqrt (c.im ^ 2 + ‖y‖ ^ 2))| ≤ ‖y‖ :=
    srg_abs_sub_sqrt_sq_add_sq_le (norm_nonneg y)
  have hsqrt_abs' : |(|c.im| - b)| ≤ ‖y‖ := by
    simpa [hb] using hsqrt_abs
  by_cases hcim : 0 ≤ c.im
  · refine ⟨a + Complex.I * (b : ℂ), Or.inl rfl, ?_⟩
    have hcdiff :
        c - ((c.re : ℂ) + Complex.I * (b : ℂ)) =
          Complex.I * ((c.im - b : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simp
    have hz : (a : ℂ) + Complex.I * (b : ℂ) =
        (c.re : ℂ) + Complex.I * (b : ℂ) := by
      rw [hcre]
    have hnorm_cz : ‖c - ((a : ℂ) + Complex.I * (b : ℂ))‖ = |c.im - b| := by
      rw [hz, hcdiff]
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have him : |c.im - b| ≤ ‖y‖ := by
      have hcabs : |c.im| = c.im := abs_of_nonneg hcim
      have h := hsqrt_abs'
      rw [hcabs] at h
      exact h
    calc
      dist w ((a : ℂ) + Complex.I * (b : ℂ))
          ≤ dist w c + dist c ((a : ℂ) + Complex.I * (b : ℂ)) :=
        dist_triangle w c _
      _ = ‖w - c‖ + ‖c - ((a : ℂ) + Complex.I * (b : ℂ))‖ := by
        rw [dist_eq_norm, dist_eq_norm]
      _ ≤ ‖T x - w • x‖ + ‖y‖ := by
        gcongr
        · rw [norm_sub_rev]
          exact hcw_le
        · rw [hnorm_cz]
          exact him
      _ ≤ 2 * ‖T x - w • x‖ := by
        nlinarith
  · have hcimneg : c.im < 0 := lt_of_not_ge hcim
    refine ⟨a - Complex.I * (b : ℂ), Or.inr rfl, ?_⟩
    have hcdiff :
        c - ((c.re : ℂ) - Complex.I * (b : ℂ)) =
          Complex.I * ((c.im + b : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simp
    have hz : (a : ℂ) - Complex.I * (b : ℂ) =
        (c.re : ℂ) - Complex.I * (b : ℂ) := by
      rw [hcre]
    have hnorm_cz : ‖c - ((a : ℂ) - Complex.I * (b : ℂ))‖ = |c.im + b| := by
      rw [hz, hcdiff]
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have him : |c.im + b| ≤ ‖y‖ := by
      have hEq : |c.im + b| = |(|c.im| - b)| := by
        rw [abs_of_neg hcimneg]
        rw [show -c.im - b = -(c.im + b) by ring]
        rw [abs_neg]
      rw [hEq]
      exact hsqrt_abs'
    calc
      dist w ((a : ℂ) - Complex.I * (b : ℂ))
          ≤ dist w c + dist c ((a : ℂ) - Complex.I * (b : ℂ)) :=
        dist_triangle w c _
      _ = ‖w - c‖ + ‖c - ((a : ℂ) - Complex.I * (b : ℂ))‖ := by
        rw [dist_eq_norm, dist_eq_norm]
      _ ≤ ‖T x - w • x‖ + ‖y‖ := by
        gcongr
        · rw [norm_sub_rev]
          exact hcw_le
        · rw [hnorm_cz]
          exact him
      _ ≤ 2 * ‖T x - w • x‖ := by
        nlinarith

/- verified submission -/
theorem approximatePointSpectrum_subset_closure_scaledRelativeGraph_polar
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) :
    {w : ℂ |
        ∃ x : ℕ → H,
          (∀ n : ℕ, ‖x n‖ = 1) ∧
            Filter.Tendsto (fun n : ℕ => ‖T (x n) - w • x n‖)
              Filter.atTop (nhds 0)} ⊆
      closure
        {z : ℂ |
          ∃ x : H, ‖x‖ = 1 ∧
            let a : ℝ := (inner ℂ (T x) x).re
            let b : ℝ := Real.sqrt (‖T x‖ ^ 2 - a ^ 2)
            z = (a : ℂ) + Complex.I * (b : ℂ) ∨
              z = (a : ℂ) - Complex.I * (b : ℂ)} := by
  intro w hw
  rcases hw with ⟨x, hxnorm, hlim⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hδ : 0 < ε / 2 := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (ε / 2) hδ
  have hr : ‖T (x N) - w • x N‖ < ε / 2 := by
    have h := hN N le_rfl
    simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using h
  obtain ⟨z, hzgraph, hzdist⟩ :=
    scaledRelativeGraph_polar_approx T (hxnorm N) w
  refine ⟨z, ?_, ?_⟩
  · exact ⟨x N, hxnorm N, hzgraph⟩
  · calc
      dist w z ≤ 2 * ‖T (x N) - w • x N‖ := hzdist
      _ < ε := by nlinarith


#check_dependency_graph "approximatePointSpectrum_subset_closure_scaledRelativeGraph_polar" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"w ∈ closure {z | ∃ x, ‖x‖ = 1 ∧ let a := (inner ℂ (T x) x).re; let b := √(‖T x‖ ^ 2 - a ^ 2); z = ↑a + Complex.I * ↑b ∨ z = ↑a - Complex.I * ↑b}\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hw\",\"statement\":\"w ∈ {w | ∃ x, (∀ (n : ℕ), ‖x n‖ = 1) ∧ Filter.Tendsto (fun n => ‖T (x n) - w • x n‖) Filter.atTop (nhds 0)}\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2476_approximatepointspectrum_subset_closure_sc\",\"reconstructedProofSha256\":\"5d8ea053d9be55b631b620d799cac392ef98ec73b3e2af01ed7eef248a1ede21\",\"selectedEdgeCount\":1,\"theoremName\":\"approximatePointSpectrum_subset_closure_scaledRelativeGraph_polar\",\"topologySha256\":\"0c595635aee944b581bdaea9c8a2ecb86c55cb527f19e24cd9f57e497d699998\"}"
