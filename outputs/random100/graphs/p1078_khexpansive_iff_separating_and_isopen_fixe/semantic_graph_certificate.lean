import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1078_khexpansive_iff_separating_and_isopen_fixe
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 1d21a2c271cc6d89ca8dd8b3bb2cfd8d6957cb59c12c94472e01d3e82f68c8b9
-- reconstructed_proof_sha256: de379f18f56776441b114786daf0a381730e90673f496ebdb56d06e795acaa41
-- selected_edge_count: 1

/- accepted add_to_file helper 1 -/
lemma flow_apply_neg_left
    {Λ : Type*} (φ : ℝ × Λ → Λ)
    (hzero : ∀ x : Λ, φ (0, x) = x)
    (hadd : ∀ (t u : ℝ) (x : Λ), φ (t + u, x) = φ (t, φ (u, x)))
    (t : ℝ) (x : Λ) : φ (-t, φ (t, x)) = x := by
  have h := hadd (-t) t x
  have hz := hzero x
  norm_num at h
  rw [hz] at h
  exact h.symm

lemma flow_apply_neg_right
    {Λ : Type*} (φ : ℝ × Λ → Λ)
    (hzero : ∀ x : Λ, φ (0, x) = x)
    (hadd : ∀ (t u : ℝ) (x : Λ), φ (t + u, x) = φ (t, φ (u, x)))
    (t : ℝ) (x : Λ) : φ (t, φ (-t, x)) = x := by
  have h := hadd t (-t) x
  have hz := hzero x
  norm_num at h
  rw [hz] at h
  exact h.symm

lemma flow_period_nat
    {Λ : Type*} (φ : ℝ × Λ → Λ)
    (hzero : ∀ x : Λ, φ (0, x) = x)
    (hadd : ∀ (t u : ℝ) (x : Λ), φ (t + u, x) = φ (t, φ (u, x)))
    {u : ℝ} {x : Λ} (hper : φ (u, x) = x) (n : ℕ) :
    φ ((n : ℝ) * u, x) = x := by
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
      have hcalc : ((n + 1 : ℕ) : ℝ) * u = u + (n : ℝ) * u := by
        rw [Nat.cast_add, Nat.cast_one]
        ring
      rw [hcalc, hadd, ih, hper]

lemma flow_period_int
    {Λ : Type*} (φ : ℝ × Λ → Λ)
    (hzero : ∀ x : Λ, φ (0, x) = x)
    (hadd : ∀ (t u : ℝ) (x : Λ), φ (t + u, x) = φ (t, φ (u, x)))
    {u : ℝ} {x : Λ} (hper : φ (u, x) = x) (k : ℤ) :
    φ ((k : ℝ) * u, x) = x := by
  cases k with
  | ofNat n =>
      simpa using flow_period_nat φ hzero hadd hper n
  | negSucc n =>
      let q : ℝ := (((n + 1 : ℕ) : ℝ) * u)
      have hnq : φ (q, x) = x := flow_period_nat φ hzero hadd hper (n + 1)
      have hneg := hadd (-q) q x
      have hz := hzero x
      norm_num at hneg
      rw [hz, hnq] at hneg
      have hcast : ((Int.negSucc n : ℤ) : ℝ) * u = -q := by
        dsimp [q]
        rw [Nat.cast_add, Nat.cast_one]
        norm_num [Int.negSucc]
        ring
      rw [hcast]
      exact hneg.symm

lemma fixed_of_flow_fixed
    {Λ : Type*} (φ : ℝ × Λ → Λ)
    (hzero : ∀ x : Λ, φ (0, x) = x)
    (hadd : ∀ (t u : ℝ) (x : Λ), φ (t + u, x) = φ (t, φ (u, x)))
    {t : ℝ} {x : Λ}
    (h : ∀ r : ℝ, φ (r, φ (t, x)) = φ (t, x)) :
    ∀ r : ℝ, φ (r, x) = x := by
  have hxt : x = φ (t, x) := by
    have hneg := h (-t)
    rw [flow_apply_neg_left φ hzero hadd t x] at hneg
    exact hneg
  intro r
  calc
    φ (r, x) = φ ((r - t) + t, x) := by ring_nf
    _ = φ (r - t, φ (t, x)) := hadd (r - t) t x
    _ = φ (t, x) := h (r - t)
    _ = x := hxt.symm

/- accepted add_to_file helper 2 -/
lemma exists_pos_no_small_period_of_isOpen_fixed
    {Λ : Type*} [MetricSpace Λ] [CompactSpace Λ]
    (φ : ℝ × Λ → Λ)
    (hcont : Continuous φ)
    (hzero : ∀ x : Λ, φ (0, x) = x)
    (hadd : ∀ (t u : ℝ) (x : Λ), φ (t + u, x) = φ (t, φ (u, x)))
    (hfix : IsOpen {x : Λ | ∀ t : ℝ, φ (t, x) = x}) :
    ∃ η : ℝ, 0 < η ∧
      ∀ x : Λ, x ∉ {x : Λ | ∀ t : ℝ, φ (t, x) = x} →
        ∀ u : ℝ, 0 < |u| → |u| < η → φ (u, x) ≠ x := by
  classical
  by_contra hnone
  push_neg at hnone
  let F : Set Λ := {x : Λ | ∀ t : ℝ, φ (t, x) = x}
  have hseq : ∀ n : ℕ, ∃ x : Λ, ∃ u : ℝ,
      x ∉ F ∧ 0 < |u| ∧ |u| < 1 / ((n : ℝ) + 1) ∧ φ (u, x) = x := by
    intro n
    have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    rcases hnone _ hn with ⟨x, hx, u, hupos, hu, hper⟩
    exact ⟨x, u, hx, hupos, hu, hper⟩
  choose x u hx hupos hub hper using hseq
  have hCclosed : IsClosed Fᶜ := hfix.isClosed_compl
  have hCcompact : IsCompact Fᶜ := hCclosed.isCompact
  have hxC : ∀ n : ℕ, x n ∈ Fᶜ := by
    intro n
    exact hx n
  rcases hCcompact.tendsto_subseq hxC with ⟨xLim, hxLimC, ρ, hρmono, hxlim⟩
  have hρtop : Filter.Tendsto ρ Filter.atTop Filter.atTop := hρmono.tendsto_atTop
  have hone : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hg : Filter.Tendsto (fun n : ℕ => 1 / ((ρ n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    hone.comp hρtop
  have hpabs : Filter.Tendsto (fun n : ℕ => |u (ρ n)|) Filter.atTop (nhds 0) := by
    apply squeeze_zero
    · intro n
      exact abs_nonneg _
    · intro n
      exact le_of_lt (hub (ρ n))
    · exact hg
  have hpne : ∀ n : ℕ, u (ρ n) ≠ 0 := fun n => abs_pos.mp (hupos (ρ n))
  have hfixed : ∀ T : ℝ, φ (T, xLim) = xLim := by
    intro T
    let k : ℕ → ℤ := fun n => round (T / u (ρ n))
    let τ : ℕ → ℝ := fun n => (k n : ℝ) * u (ρ n)
    have hbound : ∀ n : ℕ, |τ n - T| ≤ |u (ρ n)| / 2 := by
      intro n
      calc
        |τ n - T| = |u (ρ n)| * |(k n : ℝ) - T / u (ρ n)| := by
          rw [← abs_mul]
          apply congrArg abs
          dsimp [τ, k]
          field_simp [hpne n]
        _ ≤ |u (ρ n)| * (1 / 2) := by
          gcongr
          dsimp [k]
          rw [abs_sub_comm]
          exact abs_sub_round (T / u (ρ n))
        _ = |u (ρ n)| / 2 := by ring
    have hsubabs : Filter.Tendsto (fun n : ℕ => |τ n - T|) Filter.atTop (nhds 0) := by
      apply squeeze_zero
      · intro n
        exact abs_nonneg _
      · intro n
        exact hbound n
      · simpa using hpabs.div_const 2
    have hsub0 : Filter.Tendsto (fun n : ℕ => τ n - T) Filter.atTop (nhds 0) :=
      (tendsto_zero_iff_abs_tendsto_zero (fun n : ℕ => τ n - T)).mpr hsubabs
    have hτ : Filter.Tendsto τ Filter.atTop (nhds T) := by
      have hconst : Filter.Tendsto (fun _ : ℕ => T) Filter.atTop (nhds T) := tendsto_const_nhds
      have h := hsub0.add hconst
      simpa using h
    have hpern : ∀ n : ℕ, φ (τ n, x (ρ n)) = x (ρ n) := by
      intro n
      exact flow_period_int φ hzero hadd (hper (ρ n)) (k n)
    have hpair : Filter.Tendsto (fun n : ℕ => (τ n, x (ρ n))) Filter.atTop (nhds (T, xLim)) :=
      hτ.prodMk_nhds hxlim
    have hlimφ : Filter.Tendsto (fun n : ℕ => φ (τ n, x (ρ n))) Filter.atTop
        (nhds (φ (T, xLim))) := by
      exact (hcont.tendsto (T, xLim)).comp hpair
    have hlimx : Filter.Tendsto (fun n : ℕ => φ (τ n, x (ρ n))) Filter.atTop
        (nhds xLim) := by
      have hfun : (fun n : ℕ => φ (τ n, x (ρ n))) = fun n : ℕ => x (ρ n) := by
        funext n
        exact hpern n
      simpa [hfun] using hxlim
    exact tendsto_nhds_unique hlimφ hlimx
  have hxLimF : xLim ∈ F := hfixed
  exact hxLimC hxLimF

/- accepted add_to_file helper 3 -/
lemma exists_pos_flow_displacement_of_isOpen_fixed
    {Λ : Type*} [MetricSpace Λ] [CompactSpace Λ]
    (φ : ℝ × Λ → Λ)
    (hcont : Continuous φ)
    (hzero : ∀ x : Λ, φ (0, x) = x)
    (hadd : ∀ (t u : ℝ) (x : Λ), φ (t + u, x) = φ (t, φ (u, x)))
    (hfix : IsOpen {x : Λ | ∀ t : ℝ, φ (t, x) = x}) :
    ∃ τ e : ℝ, 0 < τ ∧ 0 < e ∧
      ∀ x : Λ, x ∉ {x : Λ | ∀ t : ℝ, φ (t, x) = x} →
        e ≤ dist (φ (τ, x)) x ∧ e ≤ dist (φ (-τ, x)) x := by
  rcases exists_pos_no_small_period_of_isOpen_fixed φ hcont hzero hadd hfix with
    ⟨η, hη, hnoper⟩
  let F : Set Λ := {x : Λ | ∀ t : ℝ, φ (t, x) = x}
  let τ : ℝ := η / 2
  have hτ : 0 < τ := by positivity
  have hτlt : τ < η := by
    dsimp [τ]
    linarith
  have hCclosed : IsClosed Fᶜ := hfix.isClosed_compl
  have hCcompact : IsCompact Fᶜ := hCclosed.isCompact
  have hflowτ : Continuous fun x : Λ => φ (τ, x) := by
    exact hcont.comp (continuous_const.prodMk continuous_id)
  have hdistτ : Continuous fun x : Λ => dist (φ (τ, x)) x :=
    hflowτ.dist continuous_id
  have hposτ : ∀ x ∈ Fᶜ, 0 < dist (φ (τ, x)) x := by
    intro x hx
    have hne : φ (τ, x) ≠ x := by
      apply hnoper x hx τ
      · rw [abs_of_pos hτ]
        exact hτ
      · rw [abs_of_pos hτ]
        exact hτlt
    exact dist_pos.mpr hne
  rcases hCcompact.exists_forall_le' hdistτ.continuousOn hposτ with ⟨eτ, heτ, hleτ⟩
  have hflow_negτ : Continuous fun x : Λ => φ (-τ, x) := by
    exact hcont.comp (continuous_const.prodMk continuous_id)
  have hdist_negτ : Continuous fun x : Λ => dist (φ (-τ, x)) x :=
    hflow_negτ.dist continuous_id
  have hpos_negτ : ∀ x ∈ Fᶜ, 0 < dist (φ (-τ, x)) x := by
    intro x hx
    have hne : φ (-τ, x) ≠ x := by
      apply hnoper x hx (-τ)
      · rw [abs_neg, abs_of_pos hτ]
        exact hτ
      · rw [abs_neg, abs_of_pos hτ]
        exact hτlt
    exact dist_pos.mpr hne
  rcases hCcompact.exists_forall_le' hdist_negτ.continuousOn hpos_negτ with
    ⟨e_neg, he_neg, hle_neg⟩
  refine ⟨τ, min eτ e_neg, hτ, lt_min heτ he_neg, ?_⟩
  intro x hx
  have hxC : x ∈ Fᶜ := hx
  constructor
  · exact le_trans (min_le_left _ _) (hleτ x hxC)
  · exact le_trans (min_le_right _ _) (hle_neg x hxC)

/- accepted add_to_file helper 4 -/
lemma nonfixed_flow_of_nonfixed
    {Λ : Type*} (φ : ℝ × Λ → Λ)
    (hzero : ∀ x : Λ, φ (0, x) = x)
    (hadd : ∀ (t u : ℝ) (x : Λ), φ (t + u, x) = φ (t, φ (u, x)))
    {t : ℝ} {x : Λ}
    (hx : x ∉ {x : Λ | ∀ t : ℝ, φ (t, x) = x}) :
    φ (t, x) ∉ {x : Λ | ∀ t : ℝ, φ (t, x) = x} := by
  intro h
  exact hx (fixed_of_flow_fixed φ hzero hadd h)

/- accepted add_to_file helper 5 -/
lemma isClosed_fixedPoints_of_continuous_flow
    {Λ : Type*} [MetricSpace Λ]
    (φ : ℝ × Λ → Λ)
    (hcont : Continuous φ) :
    IsClosed {x : Λ | ∀ t : ℝ, φ (t, x) = x} := by
  rw [Set.setOf_forall]
  apply isClosed_iInter
  intro t
  have hflow : Continuous fun x : Λ => φ (t, x) :=
    hcont.comp (continuous_const.prodMk continuous_id)
  exact isClosed_eq hflow continuous_id

/- accepted add_to_file helper 6 -/
lemma exists_pos_fixed_nonfixed_dist
    {Λ : Type*} [MetricSpace Λ] [CompactSpace Λ]
    (φ : ℝ × Λ → Λ)
    (hcont : Continuous φ)
    (hfix : IsOpen {x : Λ | ∀ t : ℝ, φ (t, x) = x}) :
    ∃ r : ℝ, 0 < r ∧
      ∀ x : Λ, x ∈ {x : Λ | ∀ t : ℝ, φ (t, x) = x} →
        ∀ z : Λ, z ∉ {x : Λ | ∀ t : ℝ, φ (t, x) = x} →
          r < dist x z := by
  let F : Set Λ := {x : Λ | ∀ t : ℝ, φ (t, x) = x}
  have hFclosed : IsClosed F := isClosed_fixedPoints_of_continuous_flow φ hcont
  have hCclosed : IsClosed Fᶜ := hfix.isClosed_compl
  have hCcompact : IsCompact Fᶜ := hCclosed.isCompact
  have hdisj : Disjoint Fᶜ F := disjoint_compl_left
  rcases Metric.exists_pos_forall_lt_edist hCcompact hFclosed hdisj with ⟨r, hr, hrpos⟩
  refine ⟨r, ?_, ?_⟩
  · exact_mod_cast hr
  · intro x hxF z hzF
    have hzC : z ∈ Fᶜ := hzF
    have hnedist := hrpos z hzC x hxF
    have hzx : z ≠ x := by
      intro hzx_eq
      subst hzx_eq
      exact hzF hxF
    have hdistpos : 0 < dist z x := dist_pos.mpr hzx
    have hof : ENNReal.ofReal (r : ℝ) < ENNReal.ofReal (dist z x) := by
      rw [ENNReal.ofReal_coe_nnreal]
      simpa [edist_dist] using hnedist
    have hreal : (r : ℝ) < dist z x :=
      (ENNReal.ofReal_lt_ofReal_iff hdistpos).mp hof
    rwa [dist_comm] at hreal

/- accepted add_to_file helper 7 -/
lemma reparam_surjective_of_nonfixed
    {Λ : Type*} [MetricSpace Λ] [CompactSpace Λ]
    (φ : ℝ × Λ → Λ)
    (hzero : ∀ x : Λ, φ (0, x) = x)
    (hadd : ∀ (t u : ℝ) (x : Λ), φ (t + u, x) = φ (t, φ (u, x)))
    {x : Λ} (hx : x ∉ {x : Λ | ∀ t : ℝ, φ (t, x) = x})
    {s : ℝ → ℝ} (hs : Continuous s) (hs0 : s 0 = 0)
    {τ e δ : ℝ} (hτ : 0 < τ)
    (hdis : ∀ z : Λ, z ∉ {x : Λ | ∀ t : ℝ, φ (t, x) = x} →
      e ≤ dist (φ (τ, z)) z ∧ e ≤ dist (φ (-τ, z)) z)
    (hA : ∀ t : ℝ, dist (φ (t, x)) (φ (s t, x)) < δ)
    (hδe : δ < e) :
    Function.Surjective s := by
  let F : Set Λ := {x : Λ | ∀ t : ℝ, φ (t, x) = x}
  let u : ℝ → ℝ := fun t => s t - t
  have hucont : Continuous u := hs.sub continuous_id
  have hu0 : u 0 = 0 := by
    dsimp [u]
    simp [hs0]
  have hbound : ∀ t : ℝ, |u t| < τ := by
    intro t
    by_contra hnot
    have htaule : τ ≤ |u t| := le_of_not_gt hnot
    let v : ℝ → ℝ := fun r => |u r|
    have hvcont : Continuous v := hucont.abs
    have hv0 : v 0 = 0 := by
      dsimp [v]
      simp [hu0]
    have hexists : ∃ t0 : ℝ, |u t0| = τ := by
      by_cases ht : 0 ≤ t
      · have hsubset : Set.Icc (v 0) (v t) ⊆ v '' Set.Icc 0 t :=
          intermediate_value_Icc ht hvcont.continuousOn
        have hτmem : τ ∈ Set.Icc (v 0) (v t) := by
          constructor
          · rw [hv0]
            exact le_of_lt hτ
          · exact htaule
        rcases hsubset hτmem with ⟨t0, ht0, ht0val⟩
        exact ⟨t0, ht0val⟩
      · have ht0 : t ≤ 0 := le_of_not_ge ht
        have hsubset : Set.Icc (v 0) (v t) ⊆ v '' Set.Icc t 0 :=
          intermediate_value_Icc' ht0 hvcont.continuousOn
        have hτmem : τ ∈ Set.Icc (v 0) (v t) := by
          constructor
          · rw [hv0]
            exact le_of_lt hτ
          · exact htaule
        rcases hsubset hτmem with ⟨t0, ht0range, ht0val⟩
        exact ⟨t0, ht0val⟩
    rcases hexists with ⟨t0, ht0abs⟩
    let z : Λ := φ (t0, x)
    have hz : z ∉ F := by
      dsimp [z, F]
      exact nonfixed_flow_of_nonfixed φ hzero hadd hx
    have hfloweq : φ (u t0, z) = φ (s t0, x) := by
      dsimp [u, z]
      have hh := hadd (s t0 - t0) t0 x
      have hsum : s t0 - t0 + t0 = s t0 := by ring
      rw [hsum] at hh
      exact hh.symm
    have hA0 : dist z (φ (u t0, z)) < δ := by
      have h0 := hA t0
      rw [← hfloweq] at h0
      exact h0
    rcases hdis z hz with ⟨hlowτ, hlow_negτ⟩
    rcases eq_or_eq_neg_of_abs_eq ht0abs with hu_eq | hu_eq
    · have hsmall : dist (φ (τ, z)) z < δ := by
        rw [hu_eq, dist_comm] at hA0
        exact hA0
      exact (not_lt_of_ge hlowτ) (lt_trans hsmall hδe)
    · have hsmall : dist (φ (-τ, z)) z < δ := by
        rw [hu_eq, dist_comm] at hA0
        exact hA0
      exact (not_lt_of_ge hlow_negτ) (lt_trans hsmall hδe)
  intro r
  let a : ℝ := r - τ
  let b : ℝ := r + τ
  have ha : s a < r := by
    have hb := hbound a
    rcases abs_lt.mp hb with ⟨hleft, hright⟩
    dsimp [u, a] at hright
    linarith
  have hb : r < s b := by
    have hbnd := hbound b
    rcases abs_lt.mp hbnd with ⟨hleft, hright⟩
    dsimp [u, b] at hleft
    linarith
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith
  have hsubset : Set.Icc (s a) (s b) ⊆ s '' Set.Icc a b :=
    intermediate_value_Icc hab hs.continuousOn
  have hmem : r ∈ Set.Icc (s a) (s b) := ⟨le_of_lt ha, le_of_lt hb⟩
  rcases hsubset hmem with ⟨t, ht, hts⟩
  exact ⟨t, hts⟩

/- verified submission -/
theorem khExpansive_iff_separating_and_isOpen_fixedPoints
    {Λ : Type*} [MetricSpace Λ] [CompactSpace Λ]
    (φ : ℝ × Λ → Λ)
    (hcont : Continuous φ)
    (hzero : ∀ x : Λ, φ (0, x) = x)
    (hadd : ∀ (t u : ℝ) (x : Λ), φ (t + u, x) = φ (t, φ (u, x))) :
    (∃ δ : ℝ, 0 < δ ∧
      ∀ (x y : Λ) (s : ℝ → ℝ), Continuous s → s 0 = 0 →
        ((∀ t : ℝ, dist (φ (t, x)) (φ (s t, x)) < δ) ∧
          (∀ t : ℝ, dist (φ (t, x)) (φ (s t, y)) < δ)) →
        y ∈ Set.range (fun t : ℝ => φ (t, x))) ↔
      ((∃ α : ℝ, 0 < α ∧
        ∀ x y : Λ,
          (∀ t : ℝ, dist (φ (t, x)) (φ (t, y)) < α) →
          y ∈ Set.range (fun t : ℝ => φ (t, x))) ∧
        IsOpen {x : Λ | ∀ t : ℝ, φ (t, x) = x}) := by
  constructor
  · intro h
    rcases h with ⟨δ, hδ, hK⟩
    constructor
    · refine ⟨δ, hδ, ?_⟩
      intro x y hxy
      apply hK x y (fun t : ℝ => t) continuous_id rfl
      constructor
      · intro t
        simpa using hδ
      · exact hxy
    · rw [isOpen_iff_forall_mem_open]
      intro x hx
      have hsub : Metric.ball x δ ⊆ {x : Λ | ∀ t : ℝ, φ (t, x) = x} := by
        intro y hy
        have hy' : dist x y < δ := by
          rw [dist_comm]
          exact hy
        have horb : y ∈ Set.range (fun t : ℝ => φ (t, x)) := by
          apply hK x y (fun _ : ℝ => 0) continuous_const rfl
          constructor
          · intro t
            have hxt : φ (t, x) = x := hx t
            rw [hxt, hzero]
            simpa using hδ
          · intro t
            have hxt : φ (t, x) = x := hx t
            rw [hxt, hzero]
            exact hy'
        rcases horb with ⟨t, rfl⟩
        change ∀ u : ℝ, φ (u, φ (t, x)) = φ (t, x)
        rw [hx t]
        exact hx
      exact ⟨Metric.ball x δ, hsub, Metric.isOpen_ball, Metric.mem_ball_self hδ⟩
  · intro h
    rcases h with ⟨⟨α, hα, hsep⟩, hfix⟩
    rcases exists_pos_flow_displacement_of_isOpen_fixed φ hcont hzero hadd hfix with
      ⟨τ, e, hτ, he, hdis⟩
    rcases exists_pos_fixed_nonfixed_dist φ hcont hfix with ⟨r, hr, hrdist⟩
    let δ : ℝ := min (min (α / 3) (e / 2)) (r / 2)
    have hδ : 0 < δ := by
      dsimp [δ]
      exact lt_min (lt_min (by positivity) (by positivity)) (by positivity)
    have hδ_le_α3 : δ ≤ α / 3 := by
      dsimp [δ]
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    have hδ_le_e2 : δ ≤ e / 2 := by
      dsimp [δ]
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    have hδ_le_r2 : δ ≤ r / 2 := by
      dsimp [δ]
      exact min_le_right _ _
    have hδ_lt_e : δ < e := by
      have : e / 2 < e := by linarith
      exact lt_of_le_of_lt hδ_le_e2 this
    have hδ_lt_r : δ < r := by
      have : r / 2 < r := by linarith
      exact lt_of_le_of_lt hδ_le_r2 this
    have hδ_lt_α : δ < α := by
      have : α / 3 < α := by linarith
      exact lt_of_le_of_lt hδ_le_α3 this
    have h2δ_lt_α : 2 * δ < α := by
      have hle : 2 * δ ≤ 2 * (α / 3) := by
        exact mul_le_mul_of_nonneg_left hδ_le_α3 (by norm_num)
      have : 2 * (α / 3) < α := by linarith
      exact lt_of_le_of_lt hle this
    refine ⟨δ, hδ, ?_⟩
    intro x y s hs hs0 hcond
    by_cases hxF : x ∈ {x : Λ | ∀ t : ℝ, φ (t, x) = x}
    · have hxy : dist x y < δ := by
        have h0 := hcond.2 0
        have hx0 : φ (0, x) = x := hzero x
        have hsy : φ (s 0, y) = y := by
          rw [hs0, hzero]
        simpa [hx0, hsy] using h0
      have hyF : y ∈ {x : Λ | ∀ t : ℝ, φ (t, x) = x} := by
        by_contra hyC
        have hrlt : r < dist x y := hrdist x hxF y hyC
        have : dist x y < r := lt_trans hxy hδ_lt_r
        exact (not_lt_of_ge (le_of_lt hrlt)) this
      apply hsep x y
      intro t
      rw [hxF t, hyF t]
      exact lt_trans hxy hδ_lt_α
    · have hsurj : Function.Surjective s :=
        reparam_surjective_of_nonfixed φ hzero hadd hxF hs hs0 hτ hdis hcond.1 hδ_lt_e
      apply hsep x y
      intro q
      rcases hsurj q with ⟨t, ht⟩
      have hA : dist (φ (q, x)) (φ (t, x)) < δ := by
        have h0 := hcond.1 t
        rw [ht] at h0
        rwa [dist_comm] at h0
      have hB : dist (φ (t, x)) (φ (q, y)) < δ := by
        have h0 := hcond.2 t
        rwa [ht] at h0
      calc
        dist (φ (q, x)) (φ (q, y))
            ≤ dist (φ (q, x)) (φ (t, x)) + dist (φ (t, x)) (φ (q, y)) :=
              dist_triangle _ _ _
        _ < δ + δ := add_lt_add hA hB
        _ = 2 * δ := by ring
        _ < α := h2δ_lt_α


#check_dependency_graph "khExpansive_iff_separating_and_isOpen_fixedPoints" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(∃ δ, 0 < δ ∧ ∀ (x y : Λ) (s : ℝ → ℝ), Continuous s → s 0 = 0 → ((∀ (t : ℝ), dist (φ (t, x)) (φ (s t, x)) < δ) ∧ ∀ (t : ℝ), dist (φ (t, x)) (φ (s t, y)) < δ) → y ∈ Set.range fun t => φ (t, x)) ↔ (∃ α, 0 < α ∧ ∀ (x y : Λ), (∀ (t : ℝ), dist (φ (t, x)) (φ (t, y)) < α) → y ∈ Set.range fun t => φ (t, x)) ∧ IsOpen {x | ∀ (t : ℝ), φ (t, x) = x}\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"CompactSpace Λ\"},{\"name\":\"hcont\",\"statement\":\"Continuous φ\"},{\"name\":\"hzero\",\"statement\":\"∀ (x : Λ), φ (0, x) = x\"},{\"name\":\"hadd\",\"statement\":\"∀ (t u : ℝ) (x : Λ), φ (t + u, x) = φ (t, φ (u, x))\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1078_khexpansive_iff_separating_and_isopen_fixe\",\"reconstructedProofSha256\":\"de379f18f56776441b114786daf0a381730e90673f496ebdb56d06e795acaa41\",\"selectedEdgeCount\":1,\"theoremName\":\"khExpansive_iff_separating_and_isOpen_fixedPoints\",\"topologySha256\":\"1d21a2c271cc6d89ca8dd8b3bb2cfd8d6957cb59c12c94472e01d3e82f68c8b9\"}"
