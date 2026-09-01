import Mathlib

/- accepted add_to_file helper 1 -/
lemma not_cauchySeq_far_pair
    {X : Type*} [MetricSpace X] {u : ℕ → X}
    {ε : ℝ} (hε : 0 < ε)
    (hbad : ∀ N : ℕ, ∃ m ≥ N, ∃ n ≥ N, ε ≤ dist (u m) (u n)) :
    ∀ N : ℕ, ∃ m n : ℕ, N ≤ m ∧ m < n ∧ ε ≤ dist (u m) (u n) ∧
      ∀ j : ℕ, m < j → j < n → dist (u m) (u j) < ε := by
  classical
  intro N
  let P : ℕ → Prop := fun m => N ≤ m ∧ ∃ n, m < n ∧ ε ≤ dist (u m) (u n)
  have hP : ∃ m, P m := by
    obtain ⟨m, hmN, n, hnN, hmn⟩ := hbad N
    rcases lt_trichotomy m n with hlt | heq | hgt
    · exact ⟨m, hmN, n, hlt, hmn⟩
    · subst n
      have : ε ≤ 0 := by simpa [dist_self] using hmn
      linarith
    · refine ⟨n, hnN, m, hgt, ?_⟩
      rwa [dist_comm]
  let m := Nat.find hP
  have hm : P m := Nat.find_spec hP
  obtain ⟨hmN, n₀, hmn₀, hfar₀⟩ := hm
  let Q : ℕ → Prop := fun n => m < n ∧ ε ≤ dist (u m) (u n)
  have hQ : ∃ n, Q n := ⟨n₀, hmn₀, hfar₀⟩
  let n := Nat.find hQ
  have hn : Q n := Nat.find_spec hQ
  refine ⟨m, n, hmN, hn.1, hn.2, ?_⟩
  intro j hmj hjn
  have hnot : ¬ Q j := Nat.find_min hQ hjn
  have : ¬ ε ≤ dist (u m) (u j) := by
    intro hj
    exact hnot ⟨hmj, hj⟩
  exact lt_of_not_ge this

/- accepted add_to_file helper 2 -/
lemma not_cauchySeq_subseq
    {X : Type*} [MetricSpace X] {u : ℕ → X}
    (h : ¬ CauchySeq u) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ m n : ℕ → ℕ,
      StrictMono m ∧ StrictMono n ∧
      ∀ k : ℕ,
        m k < n k ∧
        ε ≤ dist (u (m k)) (u (n k)) ∧
        dist (u (m k)) (u (n k)) <
          ε + dist (u (n k - 1)) (u (n k)) := by
  classical
  rw [Metric.cauchySeq_iff] at h
  push Not at h
  obtain ⟨ε, hε, hbad⟩ := h
  let PairProp : ℕ × ℕ → Prop := fun p =>
    p.1 < p.2 ∧ ε ≤ dist (u p.1) (u p.2) ∧
      ∀ j : ℕ, p.1 < j → j < p.2 → dist (u p.1) (u j) < ε
  let PairAt : ℕ → Type := fun N => {p : ℕ × ℕ // N ≤ p.1 ∧ PairProp p}
  have hpair_exists : ∀ N : ℕ, Nonempty (PairAt N) := by
    intro N
    obtain ⟨m, n, hmN, hmn, hfar, hmin⟩ :=
      not_cauchySeq_far_pair (u := u) hε hbad N
    exact ⟨⟨(m, n), hmN, hmn, hfar, hmin⟩⟩
  let choosePair : ∀ N : ℕ, PairAt N := fun N => Classical.choice (hpair_exists N)
  let state : ℕ → Σ N : ℕ, PairAt N := fun k =>
    Nat.rec ⟨0, choosePair 0⟩
      (fun k prev =>
        ⟨max (prev.2.1.2 + 1) (k + 1),
          choosePair (max (prev.2.1.2 + 1) (k + 1))⟩) k
  let m : ℕ → ℕ := fun k => (state k).2.1.1
  let n : ℕ → ℕ := fun k => (state k).2.1.2
  have hpair : ∀ k, PairProp (m k, n k) := fun k => (state k).2.2.2
  have hm_lt_n : ∀ k, m k < n k := fun k => (hpair k).1
  have hnext : ∀ k, n k < m (k + 1) := by
    intro k
    have hlow : max (n k + 1) (k + 1) ≤ m (k + 1) := by
      change max ((state k).2.1.2 + 1) (k + 1) ≤
        (state (k + 1)).2.1.1
      rw [show state (k + 1) =
        ⟨max ((state k).2.1.2 + 1) (k + 1),
          choosePair (max ((state k).2.1.2 + 1) (k + 1))⟩ from rfl]
      exact (choosePair (max ((state k).2.1.2 + 1) (k + 1))).2.1
    exact lt_of_lt_of_le (Nat.lt_succ_self _) ((le_max_left _ _).trans hlow)
  have hm_strict : StrictMono m :=
    strictMono_nat_of_lt_succ (fun k => (hm_lt_n k).trans (hnext k))
  have hn_strict : StrictMono n :=
    strictMono_nat_of_lt_succ (fun k => (hnext k).trans (hm_lt_n (k + 1)))
  refine ⟨ε, hε, m, n, hm_strict, hn_strict, ?_⟩
  intro k
  refine ⟨hm_lt_n k, (hpair k).2.1, ?_⟩
  have hprev : dist (u (m k)) (u (n k - 1)) < ε := by
    by_cases hlt : m k < n k - 1
    · exact (hpair k).2.2 (n k - 1) hlt (Nat.sub_one_lt_of_lt (hm_lt_n k))
    · have hle1 : n k - 1 ≤ m k := Nat.le_of_not_gt hlt
      have hle2 : m k ≤ n k - 1 := Nat.le_pred_of_lt (hm_lt_n k)
      have heq : n k - 1 = m k := le_antisymm hle1 hle2
      rw [heq, dist_self]
      exact hε
  calc
    dist (u (m k)) (u (n k)) ≤
        dist (u (m k)) (u (n k - 1)) + dist (u (n k - 1)) (u (n k)) :=
      dist_triangle _ _ _
    _ < ε + dist (u (n k - 1)) (u (n k)) := add_lt_add_left hprev _

/- accepted add_to_file helper 3 -/
lemma tendsto_zero_of_succ_le_beta_mul
    {β : NNReal → NNReal}
    (hβ_lt_one : ∀ t, β t < 1)
    (hβ_zero : ∀ t : ℕ → NNReal,
      Filter.Tendsto (fun n => β (t n)) Filter.atTop (nhds 1) →
        Filter.Tendsto t Filter.atTop (nhds 0))
    {r : ℕ → NNReal}
    (hstep : ∀ n, r (n + 1) ≤ β (r n) * r n) :
    Filter.Tendsto r Filter.atTop (nhds 0) := by
  have hdec : ∀ n, r (n + 1) ≤ r n := by
    intro n
    calc
      r (n + 1) ≤ β (r n) * r n := hstep n
      _ ≤ 1 * r n := mul_le_mul_right' (le_of_lt (hβ_lt_one _)) _
      _ = r n := one_mul _
  let L : NNReal := ⨅ i, r i
  have hbdd : BddBelow (Set.range r) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact zero_le _⟩
  have hanti : Antitone r := antitone_nat_of_succ_le hdec
  have hlim : Filter.Tendsto r Filter.atTop (nhds L) :=
    tendsto_atTop_ciInf hanti hbdd
  by_cases hL : L = 0
  · simpa [L, hL] using hlim
  · have hLpos : 0 < L := lt_of_le_of_ne' (zero_le L) hL
    have hlimR : Filter.Tendsto (fun n => (r n : ℝ)) Filter.atTop (nhds (L : ℝ)) :=
      (NNReal.tendsto_coe).2 hlim
    have hlimNext : Filter.Tendsto (fun n => r (n + 1)) Filter.atTop (nhds L) :=
      hlim.comp (Filter.tendsto_add_atTop_nat 1)
    have hlimNextR : Filter.Tendsto (fun n => (r (n + 1) : ℝ)) Filter.atTop
        (nhds (L : ℝ)) :=
      (NNReal.tendsto_coe).2 hlimNext
    have hLneR : (L : ℝ) ≠ 0 := by
      exact_mod_cast ne_of_gt hLpos
    have hq : Filter.Tendsto (fun n => (r (n + 1) : ℝ) / (r n : ℝ))
        Filter.atTop (nhds 1) := by
      have hdiv := hlimNextR.div hlimR hLneR
      simpa [div_self hLneR] using hdiv
    have hq_le : (fun n => (r (n + 1) : ℝ) / (r n : ℝ)) ≤
        fun n => (β (r n) : ℝ) := by
      intro n
      have hLrn : L ≤ r n := ciInf_le hbdd n
      have hrpos : (0 : ℝ) < (r n : ℝ) := by
        exact_mod_cast hLpos.trans_le hLrn
      have hsR : (r (n + 1) : ℝ) ≤ (β (r n) : ℝ) * (r n : ℝ) := by
        exact_mod_cast hstep n
      exact (div_le_iff₀ hrpos).2 hsR
    have hβ_le_one : (fun n => (β (r n) : ℝ)) ≤ fun _ => (1 : ℝ) := by
      intro n
      exact_mod_cast le_of_lt (hβ_lt_one (r n))
    have hβ_tendstoR : Filter.Tendsto (fun n => (β (r n) : ℝ))
        Filter.atTop (nhds (1 : ℝ)) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le hq tendsto_const_nhds hq_le hβ_le_one
    have hβ_tendsto : Filter.Tendsto (fun n => β (r n)) Filter.atTop (nhds 1) :=
      (NNReal.tendsto_coe).1 hβ_tendstoR
    have hzero := hβ_zero r hβ_tendsto
    have hLeq : L = 0 := tendsto_nhds_unique hlim hzero
    exact False.elim (hL hLeq)

/- accepted add_to_file helper 4 -/
lemma cauchySeq_of_ordered_beta_contraction
    {X : Type*} [PartialOrder X] [MetricSpace X]
    {y : ℕ → X} {β : NNReal → NNReal}
    (hβ_lt_one : ∀ t, β t < 1)
    (hβ_zero : ∀ t : ℕ → NNReal,
      Filter.Tendsto (fun n => β (t n)) Filter.atTop (nhds 1) →
        Filter.Tendsto t Filter.atTop (nhds 0))
    (hmono : Monotone y)
    (hcross : ∀ m n : ℕ, m < n →
      nndist (y (m + 1)) (y (n + 1)) ≤
        β (nndist (y m) (y n)) * nndist (y m) (y n)) :
    CauchySeq y := by
  let r : ℕ → NNReal := fun k => nndist (y k) (y (k + 1))
  have hr_step : ∀ k, r (k + 1) ≤ β (r k) * r k := by
    intro k
    exact hcross k (k + 1) (Nat.lt_succ_self k)
  have hr0 : Filter.Tendsto r Filter.atTop (nhds 0) :=
    tendsto_zero_of_succ_le_beta_mul hβ_lt_one hβ_zero hr_step
  have hr0_real : Filter.Tendsto (fun k => dist (y k) (y (k + 1)))
      Filter.atTop (nhds 0) := by
    have hcoe : Filter.Tendsto (fun k => (r k : ℝ)) Filter.atTop (nhds 0) :=
      (NNReal.tendsto_coe).2 hr0
    have heq : (fun k => (r k : ℝ)) =ᶠ[Filter.atTop]
        fun k => dist (y k) (y (k + 1)) := by
      refine Filter.Eventually.of_forall ?_
      intro k
      change (nndist (y k) (y (k + 1)) : ℝ) = dist (y k) (y (k + 1))
      rw [dist_nndist]
    exact Filter.Tendsto.congr' heq hcoe
  by_contra hc
  obtain ⟨ε, hε, m, n, hmstrict, hnstrict, hpair⟩ := not_cauchySeq_subseq hc
  have hmn : ∀ k, m k < n k := fun k => (hpair k).1
  have hlower : ∀ k, ε ≤ dist (y (m k)) (y (n k)) := fun k => (hpair k).2.1
  have hupper : ∀ k, dist (y (m k)) (y (n k)) <
      ε + dist (y (n k - 1)) (y (n k)) := fun k => (hpair k).2.2
  have hnpos : ∀ k, 0 < n k := fun k => Nat.zero_lt_of_lt (hmn k)
  have hn_pred_tendsto : Filter.Tendsto (fun k => n k - 1) Filter.atTop Filter.atTop :=
    (Filter.tendsto_sub_atTop_nat 1).comp hnstrict.tendsto_atTop
  have hsmall_nn : Filter.Tendsto (fun k => r (n k - 1)) Filter.atTop (nhds 0) :=
    hr0.comp hn_pred_tendsto
  have hsmall : Filter.Tendsto (fun k => dist (y (n k - 1)) (y (n k)))
      Filter.atTop (nhds 0) := by
    have hcoe : Filter.Tendsto (fun k => (r (n k - 1) : ℝ)) Filter.atTop (nhds 0) :=
      (NNReal.tendsto_coe).2 hsmall_nn
    have heq : (fun k => (r (n k - 1) : ℝ)) =ᶠ[Filter.atTop]
        fun k => dist (y (n k - 1)) (y (n k)) := by
      refine Filter.Eventually.of_forall ?_
      intro k
      change (nndist (y (n k - 1)) (y (n k - 1 + 1)) : ℝ) =
        dist (y (n k - 1)) (y (n k))
      rw [Nat.sub_one_add_one (ne_of_gt (hnpos k)), dist_nndist]
    exact Filter.Tendsto.congr' heq hcoe
  have hε_small : Filter.Tendsto (fun k => ε + dist (y (n k - 1)) (y (n k)))
      Filter.atTop (nhds ε) := by
    have hcst : Filter.Tendsto (fun _ : ℕ => ε) Filter.atTop (nhds ε) :=
      tendsto_const_nhds
    have h := hcst.add hsmall
    simpa only [add_zero] using h
  have hD : Filter.Tendsto (fun k => dist (y (m k)) (y (n k)))
      Filter.atTop (nhds ε) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hε_small
      (fun k => hlower k) (fun k => le_of_lt (hupper k))
  have hm_step : Filter.Tendsto (fun k => dist (y (m k + 1)) (y (m k)))
      Filter.atTop (nhds 0) := by
    have h := hr0_real.comp hmstrict.tendsto_atTop
    change Filter.Tendsto (fun k => dist (y (m k)) (y (m k + 1)))
      Filter.atTop (nhds 0) at h
    have heq : (fun k => dist (y (m k)) (y (m k + 1))) =
        fun k => dist (y (m k + 1)) (y (m k)) := by
      funext k
      exact dist_comm _ _
    rw [heq] at h
    exact h
  have hn_step : Filter.Tendsto (fun k => dist (y (n k)) (y (n k + 1)))
      Filter.atTop (nhds 0) := by
    have h := hr0_real.comp hnstrict.tendsto_atTop
    change Filter.Tendsto (fun k => dist (y (n k)) (y (n k + 1)))
      Filter.atTop (nhds 0) at h
    exact h
  have hS : Filter.Tendsto
      (fun k => dist (y (m k + 1)) (y (m k)) +
        dist (y (n k + 1)) (y (n k)))
      Filter.atTop (nhds 0) := by
    have hn_step' : Filter.Tendsto (fun k => dist (y (n k + 1)) (y (n k)))
        Filter.atTop (nhds 0) := by
      have heq : (fun k => dist (y (n k)) (y (n k + 1))) =
          fun k => dist (y (n k + 1)) (y (n k)) := by
        funext k
        exact dist_comm _ _
      rw [heq] at hn_step
      exact hn_step
    have h := hm_step.add hn_step'
    simpa only [add_zero] using h
  have hDshift : Filter.Tendsto (fun k => dist (y (m k + 1)) (y (n k + 1)))
      Filter.atTop (nhds ε) := by
    have hlowT : Filter.Tendsto
        (fun k => dist (y (m k)) (y (n k)) -
          (dist (y (m k + 1)) (y (m k)) + dist (y (n k + 1)) (y (n k))))
        Filter.atTop (nhds ε) := by
      have h := hD.sub hS
      simpa only [sub_zero] using h
    have hhighT : Filter.Tendsto
        (fun k => dist (y (m k)) (y (n k)) +
          (dist (y (m k + 1)) (y (m k)) + dist (y (n k + 1)) (y (n k))))
        Filter.atTop (nhds ε) := by
      have h := hD.add hS
      simpa only [add_zero] using h
    have hlow : (fun k => dist (y (m k)) (y (n k)) -
          (dist (y (m k + 1)) (y (m k)) + dist (y (n k + 1)) (y (n k)))) ≤
        fun k => dist (y (m k + 1)) (y (n k + 1)) := by
      intro k
      have hdiff := dist_dist_dist_le (y (m k + 1)) (y (n k + 1)) (y (m k)) (y (n k))
      rw [Real.dist_eq] at hdiff
      have hparts := (abs_sub_le_iff.mp hdiff).2
      linarith
    have hhigh : (fun k => dist (y (m k + 1)) (y (n k + 1))) ≤
        fun k => dist (y (m k)) (y (n k)) +
          (dist (y (m k + 1)) (y (m k)) + dist (y (n k + 1)) (y (n k))) := by
      intro k
      have hdiff := dist_dist_dist_le (y (m k + 1)) (y (n k + 1)) (y (m k)) (y (n k))
      rw [Real.dist_eq] at hdiff
      have hparts := (abs_sub_le_iff.mp hdiff).1
      linarith
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlowT hhighT hlow hhigh
  let t : ℕ → NNReal := fun k => nndist (y (m k)) (y (n k))
  have hq : Filter.Tendsto
      (fun k => dist (y (m k + 1)) (y (n k + 1)) /
        dist (y (m k)) (y (n k)))
      Filter.atTop (nhds 1) := by
    have hεne : ε ≠ 0 := ne_of_gt hε
    have hdiv := hDshift.div hD hεne
    simpa [div_self hεne] using hdiv
  have hq_le : (fun k => dist (y (m k + 1)) (y (n k + 1)) /
        dist (y (m k)) (y (n k))) ≤ fun k => (β (t k) : ℝ) := by
    intro k
    have hDpos : 0 < dist (y (m k)) (y (n k)) := hε.trans_le (hlower k)
    have hcrossR : dist (y (m k + 1)) (y (n k + 1)) ≤
        (β (t k) : ℝ) * dist (y (m k)) (y (n k)) := by
      have hc := hcross (m k) (n k) (hmn k)
      change nndist (y (m k + 1)) (y (n k + 1)) ≤ β (t k) * t k at hc
      calc
        dist (y (m k + 1)) (y (n k + 1)) =
            (nndist (y (m k + 1)) (y (n k + 1)) : ℝ) := dist_nndist _ _
        _ ≤ (β (t k) * t k : NNReal) := by exact_mod_cast hc
        _ = (β (t k) : ℝ) * dist (y (m k)) (y (n k)) := by
          rw [NNReal.coe_mul, dist_nndist]
    exact (div_le_iff₀ hDpos).2 hcrossR
  have hβ_le_one : (fun k => (β (t k) : ℝ)) ≤ fun _ => (1 : ℝ) := by
    intro k
    exact_mod_cast le_of_lt (hβ_lt_one (t k))
  have hβ_tendstoR : Filter.Tendsto (fun k => (β (t k) : ℝ))
      Filter.atTop (nhds (1 : ℝ)) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hq tendsto_const_nhds hq_le hβ_le_one
  have hβ_tendsto : Filter.Tendsto (fun k => β (t k)) Filter.atTop (nhds 1) :=
    (NNReal.tendsto_coe).1 hβ_tendstoR
  have ht0 : Filter.Tendsto t Filter.atTop (nhds 0) := hβ_zero t hβ_tendsto
  have hD0 : Filter.Tendsto (fun k => dist (y (m k)) (y (n k)))
      Filter.atTop (nhds 0) := by
    have hcoe : Filter.Tendsto (fun k => (t k : ℝ)) Filter.atTop (nhds 0) :=
      (NNReal.tendsto_coe).2 ht0
    have heq : (fun k => (t k : ℝ)) =ᶠ[Filter.atTop]
        fun k => dist (y (m k)) (y (n k)) := by
      refine Filter.Eventually.of_forall ?_
      intro k
      change (nndist (y (m k)) (y (n k)) : ℝ) = dist (y (m k)) (y (n k))
      rw [dist_nndist]
    exact Filter.Tendsto.congr' heq hcoe
  have hε0 : ε = 0 := tendsto_nhds_unique hD hD0
  exact (ne_of_gt hε) hε0

/- verified submission -/
theorem common_coincidence_point_of_ordered_metric_contraction
    {X : Type*} [Nonempty X] [PartialOrder X] [MetricSpace X] [CompleteSpace X]
    (f g H : X → X) (β : NNReal → NNReal)
    (hregular : ∀ (z : ℕ → X) (a : X), Monotone z →
      Filter.Tendsto z Filter.atTop (nhds a) → ∀ n, z n ≤ a)
    (hf_range : Set.range f ⊆ Set.range H)
    (hg_range : Set.range g ⊆ Set.range H)
    (hH_closed : IsClosed (Set.range H))
    (hfg_inc : ∀ x y, H y = f x → f x ≤ g y)
    (hgf_inc : ∀ x y, H y = g x → g x ≤ f y)
    (hβ_lt_one : ∀ t, β t < 1)
    (hβ_zero : ∀ t : ℕ → NNReal,
      Filter.Tendsto (fun n => β (t n)) Filter.atTop (nhds 1) →
        Filter.Tendsto t Filter.atTop (nhds 0))
    (hcontract : ∀ x y, (H x ≤ H y ∨ H y ≤ H x) →
      nndist (f x) (g y) ≤ β (nndist (H x) (H y)) * nndist (H x) (H y)) :
    ∃ u, f u = g u ∧ g u = H u := by
  classical
  have hf_eq_g : ∀ x, f x = g x := by
    intro x
    have hle := hcontract x x (Or.inl le_rfl)
    rw [nndist_self, mul_zero] at hle
    have hzero : nndist (f x) (g x) = 0 := le_antisymm hle (zero_le _)
    exact nndist_eq_zero.mp hzero
  obtain ⟨a₀⟩ := (inferInstance : Nonempty X)
  let next : ∀ x : X, {y : X // H y = f x} := fun x =>
    ⟨Classical.choose (hf_range ⟨x, rfl⟩), Classical.choose_spec (hf_range ⟨x, rfl⟩)⟩
  let a : ℕ → X := fun n => Nat.rec a₀ (fun _ x => (next x).1) n
  have ha : ∀ n, H (a (n + 1)) = f (a n) := by
    intro n
    exact (next (a n)).2
  let y : ℕ → X := fun n => H (a (n + 1))
  have hy_succ : ∀ n, y n ≤ y (n + 1) := by
    intro n
    have h := hfg_inc (a n) (a (n + 1)) (ha n)
    change f (a n) ≤ g (a (n + 1)) at h
    rw [← hf_eq_g (a (n + 1))] at h
    change H (a (n + 1)) ≤ H (a (n + 2))
    rw [ha n, ha (n + 1)]
    exact h
  have hmono : Monotone y := monotone_nat_of_le_succ hy_succ
  have hcross : ∀ m n : ℕ, m < n →
      nndist (y (m + 1)) (y (n + 1)) ≤
        β (nndist (y m) (y n)) * nndist (y m) (y n) := by
    intro m n hmn
    have hcomp : H (a (m + 1)) ≤ H (a (n + 1)) := hmono hmn.le
    have hc := hcontract (a (m + 1)) (a (n + 1)) (Or.inl hcomp)
    change nndist (f (a (m + 1))) (g (a (n + 1))) ≤
      β (nndist (y m) (y n)) * nndist (y m) (y n) at hc
    rw [← ha (m + 1), ← hf_eq_g (a (n + 1)), ← ha (n + 1)] at hc
    exact hc
  have hycauchy : CauchySeq y :=
    cauchySeq_of_ordered_beta_contraction hβ_lt_one hβ_zero hmono hcross
  let L : X := Filter.atTop.limUnder y
  have hyL : Filter.Tendsto y Filter.atTop (nhds L) :=
    hycauchy.tendsto_limUnder
  have hy_le_L : ∀ n, y n ≤ L := hregular y L hmono hyL
  have hy_mem : ∀ n, y n ∈ Set.range H := fun n => ⟨a (n + 1), rfl⟩
  have hL_mem : L ∈ Set.range H :=
    hH_closed.mem_of_tendsto hyL (Filter.Eventually.of_forall hy_mem)
  obtain ⟨u, huH⟩ := hL_mem
  have hbound : ∀ n, nndist (y (n + 1)) (f u) ≤ nndist (y n) L := by
    intro n
    have hcomp : H (a (n + 1)) ≤ H u := by
      change y n ≤ H u
      rw [huH]
      exact hy_le_L n
    have hc := hcontract (a (n + 1)) u (Or.inl hcomp)
    change nndist (f (a (n + 1))) (g u) ≤
      β (nndist (y n) (H u)) * nndist (y n) (H u) at hc
    rw [← ha (n + 1), ← hf_eq_g u, huH] at hc
    calc
      nndist (y (n + 1)) (f u) ≤ β (nndist (y n) L) * nndist (y n) L := hc
      _ ≤ 1 * nndist (y n) L := mul_le_mul_right' (le_of_lt (hβ_lt_one _)) _
      _ = nndist (y n) L := one_mul _
  have hdL : Filter.Tendsto (fun n => nndist (y n) L) Filter.atTop (nhds 0) := by
    have hconst : Filter.Tendsto (fun _ : ℕ => L) Filter.atTop (nhds L) :=
      tendsto_const_nhds
    have h := hyL.nndist hconst
    simpa using h
  have htarget_nn : Filter.Tendsto (fun n => nndist (y (n + 1)) (f u))
      Filter.atTop (nhds 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hdL
      (fun n => zero_le _) hbound
  have htarget_dist : Filter.Tendsto (fun n => dist (y (n + 1)) (f u))
      Filter.atTop (nhds 0) := by
    have hcoe : Filter.Tendsto (fun n => (nndist (y (n + 1)) (f u) : ℝ))
        Filter.atTop (nhds 0) := (NNReal.tendsto_coe).2 htarget_nn
    have heq : (fun n => (nndist (y (n + 1)) (f u) : ℝ)) =ᶠ[Filter.atTop]
        fun n => dist (y (n + 1)) (f u) := by
      refine Filter.Eventually.of_forall ?_
      intro n
      exact (dist_nndist _ _).symm
    exact Filter.Tendsto.congr' heq hcoe
  have hyshift_fu : Filter.Tendsto (fun n => y (n + 1)) Filter.atTop (nhds (f u)) :=
    tendsto_iff_dist_tendsto_zero.2 htarget_dist
  have hyshift_L : Filter.Tendsto (fun n => y (n + 1)) Filter.atTop (nhds L) :=
    hyL.comp (Filter.tendsto_add_atTop_nat 1)
  have hL_eq_fu : L = f u := tendsto_nhds_unique hyshift_L hyshift_fu
  have hfu_eq_Hu : f u = H u := by
    rw [← hL_eq_fu, huH]
  exact ⟨u, hf_eq_g u, by
    rw [← hf_eq_g u]
    exact hfu_eq_Hu⟩
