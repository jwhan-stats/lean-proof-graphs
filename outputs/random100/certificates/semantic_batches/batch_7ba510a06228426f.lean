import GraphCertificate
import Mathlib

namespace Rollout_p1335_quarter_stratifiable_diagonal_isgdelta_and

-- graph_id: p1335_quarter_stratifiable_diagonal_isgdelta_and
-- topology_sha256: f6d5f2b5cdd3ab71e8e47d685829467cee1447f2787f921b97cf0a3b7dda70a0
/- verified submission -/
theorem quarter_stratifiable_diagonal_isGDelta_and_countable_pseudocharacter
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (g : ℕ → X → Set X)
    (hg_open : ∀ n a, IsOpen (g n a))
    (hg_cover : ∀ n, ⋃ a, g n a = Set.univ)
    (hg_converges : ∀ (x : X) (a : ℕ → X),
      (∀ n, x ∈ g n (a n)) → Filter.Tendsto a Filter.atTop (nhds x)) :
    (∃ G : ℕ → Set (X × X),
      (∀ n, IsOpen (G n)) ∧
      Set.diagonal X = ⋂ n, G n) ∧
    ∀ x : X, ∃ V : ℕ → Set X,
      (∀ n, IsOpen (V n) ∧ x ∈ V n) ∧
      ⋂ n, V n = {x} := by
  classical
  constructor
  · refine ⟨fun n => ⋃ a, (g n a) ×ˢ (g n a), ?_, ?_⟩
    · intro n
      exact isOpen_iUnion fun a => (hg_open n a).prod (hg_open n a)
    · ext p
      constructor
      · intro hp
        rw [Set.mem_diagonal_iff] at hp
        rw [Set.mem_iInter]
        intro n
        have hc : p.1 ∈ ⋃ a, g n a := by
          rw [hg_cover n]
          trivial
        rw [Set.mem_iUnion] at hc
        rcases hc with ⟨a, hpa⟩
        rw [Set.mem_iUnion]
        exact ⟨a, by
          rw [Set.mem_prod]
          exact ⟨hpa, by simpa [hp] using hpa⟩⟩
      · intro hp
        rw [Set.mem_diagonal_iff]
        have hchoice : ∀ n, ∃ a, p.1 ∈ g n a ∧ p.2 ∈ g n a := by
          intro n
          have hpn : p ∈ ⋃ a, (g n a) ×ˢ (g n a) := Set.mem_iInter.mp hp n
          rw [Set.mem_iUnion] at hpn
          rcases hpn with ⟨a, hpa⟩
          exact ⟨a, Set.mem_prod.mp hpa⟩
        choose a ha using hchoice
        have hlim₁ := hg_converges p.1 a fun n => (ha n).1
        have hlim₂ := hg_converges p.2 a fun n => (ha n).2
        exact tendsto_nhds_unique hlim₁ hlim₂
  · intro x
    have hchoice : ∀ n, ∃ a, x ∈ g n a := by
      intro n
      have hx : x ∈ ⋃ a, g n a := by
        rw [hg_cover n]
        trivial
      rw [Set.mem_iUnion] at hx
      exact hx
    choose a ha using hchoice
    refine ⟨fun n => g n (a n), ?_, ?_⟩
    · intro n
      exact ⟨hg_open n (a n), ha n⟩
    · ext y
      constructor
      · intro hy
        have hy' : ∀ n, y ∈ g n (a n) := Set.mem_iInter.mp hy
        have hlimy := hg_converges y a hy'
        have hlimx := hg_converges x a ha
        have hyx : y = x := tendsto_nhds_unique hlimy hlimx
        simpa [hyx]
      · intro hy
        have hyx : y = x := by simpa using hy
        rw [Set.mem_iInter]
        intro n
        simpa [hyx] using ha n

end Rollout_p1335_quarter_stratifiable_diagonal_isgdelta_and

#check_dependency_graph "Rollout_p1335_quarter_stratifiable_diagonal_isgdelta_and.quarter_stratifiable_diagonal_isGDelta_and_countable_pseudocharacter" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(∃ G, (∀ (n : ℕ), IsOpen (G n)) ∧ Set.diagonal X = ⋂ n, G n) ∧ ∀ (x : X), ∃ V, (∀ (n : ℕ), IsOpen (V n) ∧ x ∈ V n) ∧ ⋂ n, V n = {x}\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"T2Space X\"},{\"name\":\"hg_open\",\"statement\":\"∀ (n : ℕ) (a : X), IsOpen (g n a)\"},{\"name\":\"hg_cover\",\"statement\":\"∀ (n : ℕ), ⋃ a, g n a = Set.univ\"},{\"name\":\"hg_converges\",\"statement\":\"∀ (x : X) (a : ℕ → X), (∀ (n : ℕ), x ∈ g n (a n)) → Filter.Tendsto a Filter.atTop (nhds x)\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1335_quarter_stratifiable_diagonal_isgdelta_and\",\"reconstructedProofSha256\":\"f30b800ea441ff0858d2c732e8184e5df22da3d512019b72e53f35ae716c25a0\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1335_quarter_stratifiable_diagonal_isgdelta_and.quarter_stratifiable_diagonal_isGDelta_and_countable_pseudocharacter\",\"topologySha256\":\"f6d5f2b5cdd3ab71e8e47d685829467cee1447f2787f921b97cf0a3b7dda70a0\"}"

namespace Rollout_p1355_locallycontinuousmeasurableonecocycle_iff_

-- graph_id: p1355_locallycontinuousmeasurableonecocycle_iff_
-- topology_sha256: eab7bd635f5869034ed81523c6751d4339c777d86cff6e90df03171b19b7338b
/- verified submission -/
theorem locallyContinuousMeasurableOneCocycle_iff_continuousCrossedHomomorphism
    {G A : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [DistribMulAction G A] [ContinuousSMul G A]
    [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace A] [BorelSpace A]
    (c : G → A) :
    (Measurable c ∧
        (∀ s t : G, c (s * t) = c s + s • c t) ∧
        ∃ U : Set G, IsOpen U ∧ (1 : G) ∈ U ∧ ContinuousOn c U) ↔
      (Continuous c ∧ ∀ s t : G, c (s * t) = c s + s • c t) := by
  constructor
  · rintro ⟨hmeas, hcoc, U, hUopen, h1U, hcU⟩
    have hc1 : ContinuousAt c 1 := hcU.continuousAt (hUopen.mem_nhds h1U)
    have hcont : Continuous c := by
      rw [continuous_iff_continuousAt]
      intro g
      have hceq : c = fun x => c g + g • c (g⁻¹ * x) := by
        funext x
        calc
          c x = c (g * (g⁻¹ * x)) := by
            congr 1
            rw [← mul_assoc, mul_inv_cancel, one_mul]
          _ = c g + g • c (g⁻¹ * x) := hcoc g (g⁻¹ * x)
      rw [hceq]
      have hgx : ContinuousAt (fun x : G => g⁻¹ * x) g :=
        continuousAt_const.mul continuousAt_id
      have hc1g : ContinuousAt c (g⁻¹ * g) := by
        rw [inv_mul_cancel]
        exact hc1
      have hinner : ContinuousAt (fun x : G => c (g⁻¹ * x)) g :=
        ContinuousAt.comp hc1g hgx
      exact continuousAt_const.add (hinner.const_smul g)
    exact ⟨hcont, hcoc⟩
  · rintro ⟨hcont, hcoc⟩
    exact ⟨hcont.measurable, hcoc, Set.univ, isOpen_univ, Set.mem_univ 1, hcont.continuousOn⟩

end Rollout_p1355_locallycontinuousmeasurableonecocycle_iff_

#check_dependency_graph "Rollout_p1355_locallycontinuousmeasurableonecocycle_iff_.locallyContinuousMeasurableOneCocycle_iff_continuousCrossedHomomorphism" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(Measurable c ∧ (∀ (s t : G), c (s * t) = c s + s • c t) ∧ ∃ U, IsOpen U ∧ 1 ∈ U ∧ ContinuousOn c U) ↔ Continuous c ∧ ∀ (s t : G), c (s * t) = c s + s • c t\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"IsTopologicalGroup G\"},{\"name\":\"<generated-instance>\",\"statement\":\"IsTopologicalAddGroup A\"},{\"name\":\"<generated-instance>\",\"statement\":\"ContinuousSMul G A\"},{\"name\":\"<generated-instance>\",\"statement\":\"BorelSpace G\"},{\"name\":\"<generated-instance>\",\"statement\":\"BorelSpace A\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1355_locallycontinuousmeasurableonecocycle_iff_\",\"reconstructedProofSha256\":\"ae0d24f25696f54ce1167414a5110a3cff4a6684f0810477cd99beefaeed2e94\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1355_locallycontinuousmeasurableonecocycle_iff_.locallyContinuousMeasurableOneCocycle_iff_continuousCrossedHomomorphism\",\"topologySha256\":\"eab7bd635f5869034ed81523c6751d4339c777d86cff6e90df03171b19b7338b\"}"

namespace Rollout_p1362_common_coincidence_point_of_ordered_metric

-- graph_id: p1362_common_coincidence_point_of_ordered_metric
-- topology_sha256: 78e4ae4bf05249dce38e5d4dbc12c701bc55911baceeacadef29b6de62e91336
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

end Rollout_p1362_common_coincidence_point_of_ordered_metric

#check_dependency_graph "Rollout_p1362_common_coincidence_point_of_ordered_metric.common_coincidence_point_of_ordered_metric_contraction" against "{\"edges\":[{\"conclusion\":{\"name\":\"hf_eq_g\",\"statement\":\"∀ (x : X), f x = g x\"},\"graphEdgeId\":\"h_001_hf_eq_g\",\"premises\":[{\"name\":\"hcontract\",\"statement\":\"∀ (x y : X), H x ≤ H y ∨ H y ≤ H x → nndist (f x) (g y) ≤ β (nndist (H x) (H y)) * nndist (H x) (H y)\"}],\"rawEdgeId\":\"telescope_18\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∃ u, f u = g u ∧ g u = H u\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"Nonempty X\"},{\"name\":\"<generated-instance>\",\"statement\":\"CompleteSpace X\"},{\"name\":\"hregular\",\"statement\":\"∀ (z : ℕ → X) (a : X), Monotone z → Filter.Tendsto z Filter.atTop (nhds a) → ∀ (n : ℕ), z n ≤ a\"},{\"name\":\"hf_range\",\"statement\":\"Set.range f ⊆ Set.range H\"},{\"name\":\"hH_closed\",\"statement\":\"IsClosed (Set.range H)\"},{\"name\":\"hfg_inc\",\"statement\":\"∀ (x y : X), H y = f x → f x ≤ g y\"},{\"name\":\"hβ_lt_one\",\"statement\":\"∀ (t : NNReal), β t < 1\"},{\"name\":\"hβ_zero\",\"statement\":\"∀ (t : ℕ → NNReal), Filter.Tendsto (fun n => β (t n)) Filter.atTop (nhds 1) → Filter.Tendsto t Filter.atTop (nhds 0)\"},{\"name\":\"hcontract\",\"statement\":\"∀ (x y : X), H x ≤ H y ∨ H y ≤ H x → nndist (f x) (g y) ≤ β (nndist (H x) (H y)) * nndist (H x) (H y)\"},{\"name\":\"hf_eq_g\",\"statement\":\"∀ (x : X), f x = g x\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1362_common_coincidence_point_of_ordered_metric\",\"reconstructedProofSha256\":\"ceae85017b034b6623d4a36c366ba36c766efd22f5ba99119a865a3f08218e57\",\"selectedEdgeCount\":2,\"theoremName\":\"Rollout_p1362_common_coincidence_point_of_ordered_metric.common_coincidence_point_of_ordered_metric_contraction\",\"topologySha256\":\"78e4ae4bf05249dce38e5d4dbc12c701bc55911baceeacadef29b6de62e91336\"}"

namespace Rollout_p1371_decktransformation_eq_id_of_fixed_point

-- graph_id: p1371_decktransformation_eq_id_of_fixed_point
-- topology_sha256: 49b9b585e041fe141c9e7bf83d6fcded9c12a63a2cdd4f73c72e7081daaf95bf
/- verified submission -/
theorem deckTransformation_eq_id_of_fixed_point
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [PathConnectedSpace E]
    (p : E → B) (hp : Continuous p)
    (arc_lifting : ∀ (f : C(Set.Icc (0 : ℝ) 1, B))
      (t₀ : Set.Icc (0 : ℝ) 1) (e₀ : E), p e₀ = f t₀ →
        ∃! g : C(Set.Icc (0 : ℝ) 1, E),
          (∀ t, p (g t) = f t) ∧ g t₀ = e₀)
    (h : E ≃ₜ E) (hdeck : p ∘ h = p)
    {e : E} (he : h e = e) :
    h = Homeomorph.refl E := by
  apply Homeomorph.ext
  intro x
  let γ : Path e x := PathConnectedSpace.somePath e x
  let f : C(Set.Icc (0 : ℝ) 1, B) := ⟨fun t => p (γ t), hp.comp γ.continuous⟩
  let g₁ : C(Set.Icc (0 : ℝ) 1, E) := ⟨fun t => γ t, γ.continuous⟩
  let g₂ : C(Set.Icc (0 : ℝ) 1, E) := ⟨fun t => h (γ t), h.continuous.comp γ.continuous⟩
  have hbase : p e = f 0 := by
    exact (congrArg p γ.source).symm
  have huniq := arc_lifting f 0 e hbase
  have hg₁ : (∀ t, p (g₁ t) = f t) ∧ g₁ 0 = e := by
    constructor
    · intro t
      rfl
    · exact γ.source
  have hg₂ : (∀ t, p (g₂ t) = f t) ∧ g₂ 0 = e := by
    constructor
    · intro t
      exact congrFun hdeck (γ t)
    · calc
        g₂ 0 = h (γ 0) := rfl
        _ = h e := congrArg h γ.source
        _ = e := he
  have hg : g₁ = g₂ := huniq.unique hg₁ hg₂
  have hx : γ 1 = h (γ 1) := congrArg (fun g : C(Set.Icc (0 : ℝ) 1, E) => g 1) hg
  calc
    h x = h (γ 1) := by rw [γ.target]
    _ = γ 1 := hx.symm
    _ = x := γ.target

end Rollout_p1371_decktransformation_eq_id_of_fixed_point

#check_dependency_graph "Rollout_p1371_decktransformation_eq_id_of_fixed_point.deckTransformation_eq_id_of_fixed_point" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"h = Homeomorph.refl E\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"PathConnectedSpace E\"},{\"name\":\"hp\",\"statement\":\"Continuous p\"},{\"name\":\"arc_lifting\",\"statement\":\"∀ (f : C(↑(Set.Icc 0 1), B)) (t₀ : ↑(Set.Icc 0 1)) (e₀ : E), p e₀ = f t₀ → ∃! g, (∀ (t : ↑(Set.Icc 0 1)), p (g t) = f t) ∧ g t₀ = e₀\"},{\"name\":\"hdeck\",\"statement\":\"p ∘ ⇑h = p\"},{\"name\":\"he\",\"statement\":\"h e = e\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1371_decktransformation_eq_id_of_fixed_point\",\"reconstructedProofSha256\":\"3c86b6251648168860a318a665f1cbd4177bacc040ae1d3e3aa41632e6f90926\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1371_decktransformation_eq_id_of_fixed_point.deckTransformation_eq_id_of_fixed_point\",\"topologySha256\":\"49b9b585e041fe141c9e7bf83d6fcded9c12a63a2cdd4f73c72e7081daaf95bf\"}"

namespace Rollout_p1384_scale_prod

-- graph_id: p1384_scale_prod
-- topology_sha256: 1da667801e740c52d6105a512b20eae005a2c477a38b9219361ad9b071c19e8b
/- accepted add_to_file helper 1 -/
lemma subgroup_map_prodMap {G H : Type*} [Group G] [Group H]
    (P : Subgroup G) (Q : Subgroup H)
    (f : G →* G) (g : H →* H) :
    (P.prod Q).map (f.prodMap g) = (P.map f).prod (Q.map g) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, hfx⟩
    change y ∈ P.prod Q at hy
    rw [Subgroup.mem_prod] at hy
    rw [← hfx]
    change (f y.1, g y.2) ∈ (P.map f).prod (Q.map g)
    rw [Subgroup.mem_prod]
    constructor
    · exact ⟨y.1, hy.1, rfl⟩
    · exact ⟨y.2, hy.2, rfl⟩
  · intro hx
    change x ∈ (P.map f).prod (Q.map g) at hx
    rw [Subgroup.mem_prod] at hx
    rcases hx with ⟨⟨y1, hy1, hf1⟩, ⟨y2, hy2, hf2⟩⟩
    use (y1, y2)
    constructor
    · change (y1, y2) ∈ P.prod Q
      rw [Subgroup.mem_prod]
      exact ⟨hy1, hy2⟩
    · cases x
      simp_all

lemma subgroup_prodEquiv_map {G H : Type*} [Group G] [Group H]
    (P : Subgroup G) (Q : Subgroup H)
    (f : G →* G) (g : H →* H) :
    Subgroup.map (↑(Subgroup.prodEquiv (P.map f) (Q.map g)))
      ((P.prod Q).subgroupOf ((P.map f).prod (Q.map g))) =
      (P.subgroupOf (P.map f)).prod (Q.subgroupOf (Q.map g)) := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨y, hy, hzy⟩
    change y ∈ ((P.prod Q).subgroupOf ((P.map f).prod (Q.map g))) at hy
    rw [← hzy]
    change Subgroup.prodEquiv (P.map f) (Q.map g) y ∈
      (P.subgroupOf (P.map f)).prod (Q.subgroupOf (Q.map g))
    rw [Subgroup.mem_prod]
    rcases y with ⟨⟨p,q⟩, hpq⟩
    rw [Subgroup.mem_prod] at hpq
    constructor
    · exact hy.1
    · exact hy.2
  · intro hz
    change z ∈ (P.subgroupOf (P.map f)).prod (Q.subgroupOf (Q.map g)) at hz
    rw [Subgroup.mem_prod] at hz
    use (Subgroup.prodEquiv (P.map f) (Q.map g)).symm z
    constructor
    · change (Subgroup.prodEquiv (P.map f) (Q.map g)).symm z ∈
        ((P.prod Q).subgroupOf ((P.map f).prod (Q.map g)))
      rcases z with ⟨⟨p,hp⟩,⟨q,hq⟩⟩
      exact hz
    · simp

lemma relIndex_prod_map {G H : Type*} [Group G] [Group H]
    (P : Subgroup G) (Q : Subgroup H)
    (f : G →* G) (g : H →* H) :
    (P.prod Q).relIndex ((P.prod Q).map (f.prodMap g)) =
      P.relIndex (P.map f) * Q.relIndex (Q.map g) := by
  rw [subgroup_map_prodMap]
  unfold Subgroup.relIndex
  rw [← Subgroup.index_map_equiv
    ((P.prod Q).subgroupOf ((P.map f).prod (Q.map g)))
    (Subgroup.prodEquiv (P.map f) (Q.map g)),
    subgroup_prodEquiv_map, Subgroup.index_prod]

lemma exists_compact_open_subgroup_subset {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    {U : Set G} (hU : IsOpen U) (h1U : 1 ∈ U) :
    ∃ S : Subgroup G, IsCompact (S : Set G) ∧ IsOpen (S : Set G) ∧ (S : Set G) ⊆ U := by
  obtain ⟨L, hL, h1L, hLU⟩ := exists_compact_subset hU h1U
  have hclopenbasis := loc_compact_Haus_tot_disc_of_zero_dim (H := G)
  have hLn : interior L ∈ nhds (1 : G) := isOpen_interior.mem_nhds h1L
  rw [hclopenbasis.mem_nhds_iff] at hLn
  rcases hLn with ⟨K, hKclopen, h1K, hKL⟩
  have hKcompact : IsCompact K :=
    hL.of_isClosed_subset hKclopen.isClosed (hKL.trans interior_subset)
  have hKopen : IsOpen K := hKclopen.isOpen
  obtain ⟨D, hDn, hDK⟩ := compact_open_separated_mul_left hKcompact hKopen
    (show K ⊆ K from subset_rfl)
  have hDnint : interior D ∈ nhds (1 : G) := interior_mem_nhds.2 hDn
  have hclopenbasis2 := loc_compact_Haus_tot_disc_of_zero_dim (H := G)
  have hb := (hclopenbasis2.mem_nhds_iff).mp hDnint
  rcases hb with ⟨C0, hC0, h1C0, hC0D⟩
  let C : Set G := C0 ∩ C0⁻¹
  have hCclopen : IsClopen C :=
    hC0.inter ⟨hC0.isClosed.inv, hC0.isOpen.inv⟩
  have h1C : 1 ∈ C := by
    constructor
    · exact h1C0
    · simpa [Set.mem_inv] using h1C0
  have hCD : C ⊆ D := by
    intro c hc
    exact interior_subset (hC0D hc.1)
  have hCinvD : ∀ c ∈ C, c⁻¹ ∈ D := by
    intro c hc
    exact interior_subset (hC0D (by simpa [Set.mem_inv] using hc.2))
  let S : Subgroup G := Subgroup.closure C
  have hSK : (S : Set G) ⊆ K := by
    intro x hx
    induction hx using Subgroup.closure_induction_left with
    | one =>
        exact h1K
    | mul_left c hc y hy hycK =>
        exact hDK (Set.mul_mem_mul (hCD hc) hycK)
    | inv_mul_cancel c hc y hy hycK =>
        exact hDK (Set.mul_mem_mul (hCinvD c hc) hycK)
  have hSopen : IsOpen (S : Set G) := by
    apply Subgroup.isOpen_of_mem_nhds S (g := 1)
    exact Filter.mem_of_superset (hCclopen.isOpen.mem_nhds h1C) Subgroup.subset_closure
  have hScompact : IsCompact (S : Set G) :=
    hKcompact.of_isClosed_subset (S.isClosed_of_isOpen hSopen) hSK
  exact ⟨S, hScompact, hSopen, hSK.trans ((hKL.trans interior_subset).trans hLU)⟩

/- accepted add_to_file helper 2 -/
lemma continuousMulEquiv_image_compact_open {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (φ : G ≃ₜ* G) {U : Subgroup G}
    (hUc : IsCompact (U : Set G)) (hUo : IsOpen (U : Set G)) :
    IsCompact ((U.map φ.toMulEquiv.toMonoidHom : Subgroup G) : Set G) ∧
      IsOpen ((U.map φ.toMulEquiv.toMonoidHom : Subgroup G) : Set G) := by
  constructor
  · rw [Subgroup.coe_map]
    exact hUc.image φ.toHomeomorph.continuous
  · rw [Subgroup.coe_map]
    exact φ.toHomeomorph.isOpenMap _ hUo

lemma relIndex_ne_zero_of_compact_open {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (φ : G ≃ₜ* G) {U : Subgroup G}
    (hUc : IsCompact (U : Set G)) (hUo : IsOpen (U : Set G)) :
    U.relIndex (U.map φ.toMulEquiv.toMonoidHom) ≠ 0 := by
  obtain ⟨hfc, hfo⟩ := continuousMulEquiv_image_compact_open φ hUc hUo
  let K : Subgroup G := U.map φ.toMulEquiv.toMonoidHom
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hfc
  have hsubopen : IsOpen ((U.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
    rw [Subgroup.coe_subgroupOf]
    exact hUo.preimage continuous_subtype_val
  have hfin : Finite (↥K ⧸ U.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen (U.subgroupOf K) hsubopen
  haveI := hfin
  have hfi : (U.subgroupOf K).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hne : (U.subgroupOf K).index ≠ 0 := Subgroup.finiteIndex_iff.mp hfi
  simpa [Subgroup.relIndex, K] using hne

/- accepted add_to_file helper 3 -/
lemma continuousMulEquiv_prod_image_compact_open {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (φ : G ≃ₜ* G) (ψ : H ≃ₜ* H) {U : Subgroup (G × H)}
    (hUc : IsCompact (U : Set (G × H))) (hUo : IsOpen (U : Set (G × H))) :
    IsCompact ((U.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom) :
      Subgroup (G × H)) : Set (G × H)) ∧
    IsOpen ((U.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom) :
      Subgroup (G × H)) : Set (G × H)) := by
  let e : (G × H) ≃ₜ (G × H) := Homeomorph.prodCongr φ.toHomeomorph ψ.toHomeomorph
  have hmap : ((U.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom) :
      Subgroup (G × H)) : Set (G × H)) = e '' (U : Set (G × H)) := by
    rw [Subgroup.coe_map]
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, by ext <;> rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, by ext <;> rfl⟩
  constructor
  · rw [hmap]
    exact hUc.image e.continuous
  · rw [hmap]
    exact e.isOpenMap _ hUo

lemma relIndex_ne_zero_of_compact_open_prod {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (φ : G ≃ₜ* G) (ψ : H ≃ₜ* H) {U : Subgroup (G × H)}
    (hUc : IsCompact (U : Set (G × H))) (hUo : IsOpen (U : Set (G × H))) :
    U.relIndex (U.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom)) ≠ 0 := by
  obtain ⟨hfc, hfo⟩ := continuousMulEquiv_prod_image_compact_open φ ψ hUc hUo
  let K : Subgroup (G × H) :=
    U.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom)
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hfc
  have hsubopen : IsOpen ((U.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
    rw [Subgroup.coe_subgroupOf]
    exact hUo.preimage continuous_subtype_val
  have hfin : Finite (↥K ⧸ U.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen (U.subgroupOf K) hsubopen
  haveI := hfin
  have hfi : (U.subgroupOf K).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hne : (U.subgroupOf K).index ≠ 0 := Subgroup.finiteIndex_iff.mp hfi
  simpa [Subgroup.relIndex, K] using hne

/- accepted add_to_file helper 4 -/
lemma Subgroup.index_eq_map_mul_relIndex_ker {X Y : Type*} [Group X] [Group Y]
    (q : X →* Y) (hsurj : Function.Surjective q) (R : Subgroup X)
    (hkerR : q.ker.relIndex R ≠ 0) :
    R.index = (R.map q).index * R.relIndex q.ker := by
  let K : Subgroup X := q.ker
  let J : Subgroup X := R ⊔ K
  have hmap : (R.map q).index = J.index := by
    have h := Subgroup.index_map R q
    have hrange : q.range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
    rw [hrange, Subgroup.index_top, Nat.mul_one] at h
    simpa [J, K] using h
  have hrel_eq : R.relIndex J = R.relIndex K := by
    have hsup : K.relIndex J = K.relIndex R := by
      simpa [J] using (Subgroup.relIndex_sup_right R K)
    have hinf := Subgroup.relIndex_inf_mul_relIndex R K J
    have hKJ : K ⊓ J = K := by
      exact inf_eq_left.mpr (show K ≤ J from le_sup_right)
    rw [hKJ, hsup] at hinf
    have hchain := Subgroup.relIndex_mul_relIndex (R ⊓ K) R J
      (show R ⊓ K ≤ R from inf_le_left)
      (show R ≤ J from le_sup_left)
    have hI_R : (R ⊓ K).relIndex R = K.relIndex R := by
      rw [inf_comm]
      exact Subgroup.inf_relIndex_right K R
    rw [hI_R] at hchain
    have hcancel : K.relIndex R * R.relIndex K = K.relIndex R * R.relIndex J := by
      calc
        K.relIndex R * R.relIndex K = R.relIndex K * K.relIndex R := Nat.mul_comm _ _
        _ = (R ⊓ K).relIndex J := hinf
        _ = K.relIndex R * R.relIndex J := hchain.symm
    exact (Nat.mul_left_cancel (Nat.pos_of_ne_zero (by simpa [K] using hkerR)) hcancel).symm
  have htrans := Subgroup.relIndex_mul_index (H := R) (K := J) le_sup_left
  rw [hrel_eq, ← hmap, Nat.mul_comm] at htrans
  exact htrans.symm

/- accepted add_to_file helper 5 -/
lemma subgroup_map_fst_compact_open {G H : Type*}
    [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H]
    {U : Subgroup (G × H)}
    (hUc : IsCompact (U : Set (G × H))) (hUo : IsOpen (U : Set (G × H))) :
    IsCompact ((U.map (MonoidHom.fst G H) : Subgroup G) : Set G) ∧
      IsOpen ((U.map (MonoidHom.fst G H) : Subgroup G) : Set G) := by
  constructor
  · rw [Subgroup.coe_map]
    exact hUc.image continuous_fst
  · rw [Subgroup.coe_map]
    exact isOpenMap_fst _ hUo

lemma subgroup_comap_inr_compact_open {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TotallyDisconnectedSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {U : Subgroup (G × H)}
    (hUc : IsCompact (U : Set (G × H))) (hUo : IsOpen (U : Set (G × H))) :
    IsCompact ((U.comap (MonoidHom.inr G H) : Subgroup H) : Set H) ∧
      IsOpen ((U.comap (MonoidHom.inr G H) : Subgroup H) : Set H) := by
  let f : H →ₜ* G × H := ContinuousMonoidHom.inr G H
  have hpre : ((U.comap (MonoidHom.inr G H) : Subgroup H) : Set H) =
      (fun h : H => ((1 : G), h)) ⁻¹' (U : Set (G × H)) := by
    rw [Subgroup.coe_comap]
    rfl
  have hemb : Topology.IsClosedEmbedding (fun h : H => ((1 : G), h)) := by
    refine Topology.IsClosedEmbedding.mk
      (show Topology.IsEmbedding (Prod.mk (1 : G)) from isEmbedding_prodMkRight (1 : G)) ?_
    have hrange : Set.range (fun h : H => ((1 : G), h)) = ({1} : Set G) ×ˢ Set.univ := by
      ext x
      constructor
      · rintro ⟨h, rfl⟩
        exact ⟨rfl, trivial⟩
      · rintro ⟨hx, -⟩
        rcases x with ⟨g,h⟩
        simp at hx
        subst g
        exact ⟨h, rfl⟩
    rw [hrange]
    exact isClosed_singleton.prod isClosed_univ
  constructor
  · rw [hpre]
    exact hemb.isCompact_preimage hUc
  · rw [hpre]
    exact hUo.preimage f.continuous

/- accepted add_to_file helper 6 -/
lemma Subgroup.index_ne_zero_of_isOpen_of_compact {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K : Subgroup G} (hK : IsCompact (K : Set G))
    {R : Subgroup ↥K} (hR : IsOpen (R : Set ↥K)) :
    R.index ≠ 0 := by
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  have hfin : Finite (↥K ⧸ R) := Subgroup.quotient_finite_of_isOpen R hR
  haveI := hfin
  have hfi : R.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.finiteIndex_iff.mp hfi

/- accepted add_to_file helper 7 -/
noncomputable def kernelFstProdEquiv {G H : Type*} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H]
    (φ : G ≃ₜ* G) (ψ : H ≃ₜ* H) (U : Subgroup (G × H)) :
    let F := φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom
    let X := U.map F
    let B := U.comap (MonoidHom.inr G H)
    let Bf := B.map ψ.toMulEquiv.toMonoidHom
    let q0 := (MonoidHom.fst G H).comp X.subtype
    Bf ≃* q0.rangeRestrict.ker := by
  intro F X B Bf q0
  let e : ↥Bf →* ↥q0.rangeRestrict.ker :=
    (((MonoidHom.inr G H).comp (Bf.subtype)).codRestrict X (by
      intro y
      rcases y with ⟨y, hyBf⟩
      rcases hyBf with ⟨b, hbB, hby⟩
      subst y
      have hm : F (1, b) ∈ X := ⟨(1, b), hbB, rfl⟩
      simpa [F] using hm)).codRestrict q0.rangeRestrict.ker (by
        intro y
        rcases y with ⟨y, hyBf⟩
        rcases hyBf with ⟨b, hbB, hby⟩
        subst y
        simp [q0])
  have hinj : Function.Injective e := by
    intro y z hyz
    apply Subtype.ext
    exact congrArg (fun x : ↥q0.rangeRestrict.ker => (x.1.1.2 : H)) hyz
  have hsurj : Function.Surjective e := by
    intro z
    rcases z with ⟨x, hxker⟩
    rcases x with ⟨x, hxX⟩
    have hq : q0.rangeRestrict ⟨x, hxX⟩ = 1 := hxker
    rcases hxX with ⟨u, hu, hux⟩
    subst x
    have hqval : q0 ⟨F u, by exact ⟨u, hu, rfl⟩⟩ = 1 := congrArg Subtype.val hq
    have hφ : φ u.1 = 1 := by
      simpa [q0, F] using hqval
    have hu1 : u.1 = 1 := by
      apply φ.toMulEquiv.injective
      simpa using hφ
    have huj : u = ((1 : G), u.2) := by
      ext
      · exact hu1
      · rfl
    refine ⟨⟨ψ u.2, ⟨u.2, ?_, rfl⟩⟩, ?_⟩
    · change ((1 : G), u.2) ∈ U
      rw [← huj]
      exact hu
    · ext : 2
      exact Prod.ext hφ.symm rfl
  exact MulEquiv.ofBijective e ⟨hinj, hsurj⟩

/- accepted add_to_file helper 8 -/
lemma kernel_fst_prod_equiv_map {G H : Type*} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H]
    (φ : G ≃ₜ* G) (ψ : H ≃ₜ* H) (U : Subgroup (G × H)) :
    let F := φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom
    let X := U.map F
    let B := U.comap (MonoidHom.inr G H)
    let Bf := B.map ψ.toMulEquiv.toMonoidHom
    let q0 := (MonoidHom.fst G H).comp X.subtype
    Subgroup.map (↑(kernelFstProdEquiv φ ψ U))
      ((B.subgroupOf Bf)) =
      ((U.subgroupOf X).subgroupOf q0.rangeRestrict.ker) := by
  intro F X B Bf q0
  let E := kernelFstProdEquiv φ ψ U
  ext z
  constructor
  · intro hz
    rcases hz with ⟨y, hyB, hEy⟩
    change y ∈ B.subgroupOf Bf at hyB
    change y.val ∈ B at hyB
    rw [← hEy]
    change (E y) ∈ (U.subgroupOf X).subgroupOf q0.rangeRestrict.ker
    change ((E y).val.val : G × H) ∈ U
    change (((1 : G), y.val) : G × H) ∈ U
    exact hyB
  · intro hz
    change z ∈ (U.subgroupOf X).subgroupOf q0.rangeRestrict.ker at hz
    change (z.val.val : G × H) ∈ U at hz
    refine ⟨E.symm z, ?_, ?_⟩
    · change (E.symm z).val ∈ B
      have hyval : (E.symm z).val = z.val.val.2 := by
        have h := congrArg (fun w : ↥q0.rangeRestrict.ker => w.val.val.2)
          (MulEquiv.apply_symm_apply E z)
        simpa [E, kernelFstProdEquiv] using h
      rw [hyval]
      have hfst : z.val.val.1 = 1 := by
        have hq := z.property
        change q0.rangeRestrict z.val = 1 at hq
        have hqval : q0 z.val = 1 := congrArg Subtype.val hq
        simpa [q0] using hqval
      have hzval : z.val.val = ((1 : G), z.val.val.2) := by
        ext
        · exact hfst
        · rfl
      change (((1 : G), z.val.val.2) : G × H) ∈ U
      rw [← hzval]
      exact hz
    · exact MulEquiv.apply_symm_apply E z

/- accepted add_to_file helper 9 -/
lemma relIndex_rangeRestrict_ker_fst {G H : Type*} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H]
    (φ : G ≃ₜ* G) (ψ : H ≃ₜ* H) (U : Subgroup (G × H)) :
    let F := φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom
    let X := U.map F
    let B := U.comap (MonoidHom.inr G H)
    let Bf := B.map ψ.toMulEquiv.toMonoidHom
    let q0 := (MonoidHom.fst G H).comp X.subtype
    (U.subgroupOf X).relIndex q0.rangeRestrict.ker = B.relIndex Bf := by
  intro F X B Bf q0
  unfold Subgroup.relIndex
  rw [← Subgroup.index_map_equiv (B.subgroupOf Bf) (kernelFstProdEquiv φ ψ U),
    kernel_fst_prod_equiv_map]

/- accepted add_to_file helper 10 -/
lemma Subgroup.map_index_mul_relIndex_ker_le_index {X Y : Type*} [Group X] [Group Y]
    (q : X →* Y) (hsurj : Function.Surjective q) (R : Subgroup X)
    [Finite (↥(R ⊔ q.ker) ⧸ R.subgroupOf (R ⊔ q.ker))] :
    (R.map q).index * R.relIndex q.ker ≤ R.index := by
  let K : Subgroup X := q.ker
  let J : Subgroup X := R ⊔ K
  have hmap : (R.map q).index = J.index := by
    have h := Subgroup.index_map R q
    have hrange : q.range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
    rw [hrange, Subgroup.index_top, Nat.mul_one] at h
    simpa [J, K] using h
  have htrans := Subgroup.relIndex_mul_index (H := R) (K := J) le_sup_left
  have hle : R.relIndex K ≤ R.relIndex J := by
    let e : ↥K ⧸ R.subgroupOf K ↪ ↥J ⧸ R.subgroupOf J :=
      Subgroup.quotientSubgroupOfEmbeddingOfLE R (show K ≤ J from le_sup_right)
    have hcard := Nat.card_le_card_of_injective e e.injective
    unfold Subgroup.relIndex
    rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
    simpa [J, K] using hcard
  calc
    (R.map q).index * R.relIndex q.ker = J.index * R.relIndex K := by rw [hmap]
    _ ≤ J.index * R.relIndex J := Nat.mul_le_mul_left _ hle
    _ = R.relIndex J * J.index := Nat.mul_comm _ _
    _ = R.index := htrans

/- accepted add_to_file helper 11 -/
lemma scale_prod_lower {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [TotallyDisconnectedSpace H]
    (φ : G ≃ₜ* G) (ψ : H ≃ₜ* H)
    {U : Subgroup (G × H)}
    (hUc : IsCompact (U : Set (G × H))) (hUo : IsOpen (U : Set (G × H))) :
    sInf {n : ℕ | ∃ V : Subgroup G,
      IsCompact (V : Set G) ∧ IsOpen (V : Set G) ∧
        n = V.relIndex (V.map φ.toMulEquiv.toMonoidHom)} *
    sInf {n : ℕ | ∃ W : Subgroup H,
      IsCompact (W : Set H) ∧ IsOpen (W : Set H) ∧
        n = W.relIndex (W.map ψ.toMulEquiv.toMonoidHom)} ≤
    U.relIndex (U.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom)) := by
  let SG : Set ℕ := {n : ℕ | ∃ V : Subgroup G,
    IsCompact (V : Set G) ∧ IsOpen (V : Set G) ∧
      n = V.relIndex (V.map φ.toMulEquiv.toMonoidHom)}
  let SH : Set ℕ := {n : ℕ | ∃ W : Subgroup H,
    IsCompact (W : Set H) ∧ IsOpen (W : Set H) ∧
      n = W.relIndex (W.map ψ.toMulEquiv.toMonoidHom)}
  have hGne : SG.Nonempty := by
    obtain ⟨S,hSc,hSo,-⟩ := exists_compact_open_subgroup_subset (G := G)
      isOpen_univ (Set.mem_univ 1)
    exact ⟨S.relIndex (S.map φ.toMulEquiv.toMonoidHom), S, hSc, hSo, rfl⟩
  have hHne : SH.Nonempty := by
    obtain ⟨S,hSc,hSo,-⟩ := exists_compact_open_subgroup_subset (G := H)
      isOpen_univ (Set.mem_univ 1)
    exact ⟨S.relIndex (S.map ψ.toMulEquiv.toMonoidHom), S, hSc, hSo, rfl⟩
  let F := φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom
  let X : Subgroup (G × H) := U.map F
  let A : Subgroup G := U.map (MonoidHom.fst G H)
  let Af : Subgroup G := A.map φ.toMulEquiv.toMonoidHom
  let B : Subgroup H := U.comap (MonoidHom.inr G H)
  let Bf : Subgroup H := B.map ψ.toMulEquiv.toMonoidHom
  let q0 : ↥X →* G := (MonoidHom.fst G H).comp X.subtype
  let p : ↥X →* ↥q0.range := q0.rangeRestrict
  let R : Subgroup ↥X := U.subgroupOf X
  obtain ⟨hXc,hXo⟩ := continuousMulEquiv_prod_image_compact_open φ ψ hUc hUo
  obtain ⟨hAc,hAo⟩ := subgroup_map_fst_compact_open hUc hUo
  obtain ⟨hAfc,hAfo⟩ := continuousMulEquiv_image_compact_open φ hAc hAo
  obtain ⟨hBc,hBo⟩ := subgroup_comap_inr_compact_open hUc hUo
  obtain ⟨hBfc,hBfo⟩ := continuousMulEquiv_image_compact_open ψ hBc hBo
  have hRopen : IsOpen (R : Set ↥X) := by
    rw [Subgroup.coe_subgroupOf]
    exact hUo.preimage continuous_subtype_val
  have hrange : q0.range = Af := by
    ext a
    constructor
    · rintro ⟨x, hxa⟩
      rcases x with ⟨x, hxX⟩
      rw [← hxa]
      rcases hxX with ⟨u, hu, hux⟩
      subst x
      refine ⟨u.1, ?_, rfl⟩
      exact ⟨u, hu, rfl⟩
    · rintro ⟨v, hv, hva⟩
      rw [← hva]
      rcases hv with ⟨u, hu, hu1⟩
      rw [← hu1]
      refine ⟨⟨(φ u.1, ψ u.2), ?_⟩, ?_⟩
      · exact ⟨u, hu, rfl⟩
      · rfl
  haveI : CompactSpace ↥X := isCompact_iff_compactSpace.mp hXc
  haveI : CompactSpace ↥q0.range := by
    rw [hrange]
    exact isCompact_iff_compactSpace.mp hAfc
  have hq0cont : Continuous q0 := continuous_fst.comp continuous_subtype_val
  have hpcont : Continuous p := by
    exact hq0cont.subtype_mk (fun x => ⟨x, rfl⟩)
  have hpopen : IsOpenMap p :=
    MonoidHom.isOpenMap_of_sigmaCompact p q0.rangeRestrict_surjective hpcont
  have hpRopen : IsOpen ((R.map p : Subgroup ↥q0.range) : Set ↥q0.range) := by
    rw [Subgroup.coe_map]
    exact hpopen _ hRopen
  have hpRfinite : Finite (↥q0.range ⧸ R.map p) :=
    Subgroup.quotient_finite_of_isOpen (R.map p) hpRopen
  haveI := hpRfinite
  have hpRfi : (R.map p).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let eA : ↥Af ≃* ↥q0.range := MulEquiv.subgroupCongr hrange.symm
  let Dq : Subgroup ↥q0.range := (A.subgroupOf Af).map ↑eA
  have hpR_le_Dq : R.map p ≤ Dq := by
    intro z hz
    rcases hz with ⟨r, hrR, hpr⟩
    rw [← hpr]
    refine ⟨eA.symm (p r), ?_, eA.apply_symm_apply _⟩
    change (eA.symm (p r)).val ∈ A
    change (r.val.1 : G) ∈ A
    change r.val ∈ U at hrR
    exact ⟨r.val, hrR, rfl⟩
  have hfirst_index : A.relIndex Af ≤ (R.map p).index := by
    have hD : Dq.index = A.relIndex Af := by
      dsimp [Dq]
      rw [Subgroup.index_map_equiv]
      rfl
    rw [← hD]
    exact Subgroup.index_antitone hpR_le_Dq
  have hsG : sInf SG ≤ A.relIndex Af :=
    Nat.sInf_le ⟨A,hAc,hAo,rfl⟩
  have hsG' : sInf SG ≤ (R.map p).index := hsG.trans hfirst_index
  have hsH : sInf SH ≤ B.relIndex Bf :=
    Nat.sInf_le ⟨B,hBc,hBo,rfl⟩
  have hfactor : R.relIndex p.ker = B.relIndex Bf := by
    simpa [F,X,B,Bf,q0,p,R] using relIndex_rangeRestrict_ker_fst φ ψ U
  have hsH' : sInf SH ≤ R.relIndex p.ker := by
    rw [hfactor]
    exact hsH
  have hJopen : IsOpen ((R ⊔ p.ker : Subgroup ↥X) : Set ↥X) := by
    let RO : OpenSubgroup ↥X := { toSubgroup := R, isOpen' := hRopen }
    exact Subgroup.isOpen_of_openSubgroup (R ⊔ p.ker) (U := RO) le_sup_left
  have hJcompact : IsCompact ((R ⊔ p.ker : Subgroup ↥X) : Set ↥X) := by
    exact isCompact_univ.of_isClosed_subset ((R ⊔ p.ker).isClosed_of_isOpen hJopen)
      (Set.subset_univ _)
  have hRsubJopen : IsOpen ((R.subgroupOf (R ⊔ p.ker) : Subgroup ↥(R ⊔ p.ker)) :
      Set ↥(R ⊔ p.ker)) := by
    rw [Subgroup.coe_subgroupOf]
    exact hRopen.preimage continuous_subtype_val
  have hJfinite : Finite (↥(R ⊔ p.ker) ⧸ R.subgroupOf (R ⊔ p.ker)) := by
    haveI : CompactSpace ↥(R ⊔ p.ker) := isCompact_iff_compactSpace.mp hJcompact
    exact Subgroup.quotient_finite_of_isOpen _ hRsubJopen
  haveI := hJfinite
  have hdecomp := Subgroup.map_index_mul_relIndex_ker_le_index p
    q0.rangeRestrict_surjective R
  rw [hfactor] at hdecomp
  have hdecomp' : (R.map p).index * B.relIndex Bf ≤ U.relIndex X := by
    simpa [Subgroup.relIndex, R] using hdecomp
  have hmul : sInf SG * sInf SH ≤ (R.map p).index * B.relIndex Bf := by
    exact Nat.mul_le_mul hsG' hsH
  exact hmul.trans hdecomp'

/- verified submission -/
theorem scale_prod
    {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [TotallyDisconnectedSpace H]
    (φ : G ≃ₜ* G) (ψ : H ≃ₜ* H) :
    sInf {n : ℕ | ∃ U : Subgroup (G × H),
      IsCompact (U : Set (G × H)) ∧ IsOpen (U : Set (G × H)) ∧
        n = U.relIndex (U.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom))} =
      sInf {n : ℕ | ∃ V : Subgroup G,
        IsCompact (V : Set G) ∧ IsOpen (V : Set G) ∧
          n = V.relIndex (V.map φ.toMulEquiv.toMonoidHom)} *
      sInf {n : ℕ | ∃ W : Subgroup H,
        IsCompact (W : Set H) ∧ IsOpen (W : Set H) ∧
          n = W.relIndex (W.map ψ.toMulEquiv.toMonoidHom)} := by
  let SP : Set ℕ := {n : ℕ | ∃ U : Subgroup (G × H),
    IsCompact (U : Set (G × H)) ∧ IsOpen (U : Set (G × H)) ∧
      n = U.relIndex (U.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom))}
  let SG : Set ℕ := {n : ℕ | ∃ V : Subgroup G,
    IsCompact (V : Set G) ∧ IsOpen (V : Set G) ∧
      n = V.relIndex (V.map φ.toMulEquiv.toMonoidHom)}
  let SH : Set ℕ := {n : ℕ | ∃ W : Subgroup H,
    IsCompact (W : Set H) ∧ IsOpen (W : Set H) ∧
      n = W.relIndex (W.map ψ.toMulEquiv.toMonoidHom)}
  have hPne : SP.Nonempty := by
    obtain ⟨S,hSc,hSo,-⟩ := exists_compact_open_subgroup_subset (G := G × H)
      isOpen_univ (Set.mem_univ 1)
    exact ⟨S.relIndex (S.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom)),
      S, hSc, hSo, rfl⟩
  have hGne : SG.Nonempty := by
    obtain ⟨S,hSc,hSo,-⟩ := exists_compact_open_subgroup_subset (G := G)
      isOpen_univ (Set.mem_univ 1)
    exact ⟨S.relIndex (S.map φ.toMulEquiv.toMonoidHom), S, hSc, hSo, rfl⟩
  have hHne : SH.Nonempty := by
    obtain ⟨S,hSc,hSo,-⟩ := exists_compact_open_subgroup_subset (G := H)
      isOpen_univ (Set.mem_univ 1)
    exact ⟨S.relIndex (S.map ψ.toMulEquiv.toMonoidHom), S, hSc, hSo, rfl⟩
  apply le_antisymm
  · obtain ⟨V,hVc,hVo,hVmin⟩ := Nat.sInf_mem hGne
    obtain ⟨W,hWc,hWo,hWmin⟩ := Nat.sInf_mem hHne
    have hprod_mem : sInf SG * sInf SH ∈ SP := by
      refine ⟨V.prod W, ?_, ?_, ?_⟩
      · rw [Subgroup.coe_prod]
        exact hVc.prod hWc
      · rw [Subgroup.coe_prod]
        exact hVo.prod hWo
      · calc
          sInf SG * sInf SH =
              V.relIndex (V.map φ.toMulEquiv.toMonoidHom) *
                W.relIndex (W.map ψ.toMulEquiv.toMonoidHom) := by
            rw [hVmin, hWmin]
          _ = (V.prod W).relIndex
              ((V.prod W).map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom)) := by
            exact (relIndex_prod_map V W φ.toMulEquiv.toMonoidHom ψ.toMulEquiv.toMonoidHom).symm
    exact Nat.sInf_le hprod_mem
  · apply le_csInf hPne
    intro n hn
    rcases hn with ⟨U,hUc,hUo,hn⟩
    rw [hn]
    exact scale_prod_lower φ ψ hUc hUo

end Rollout_p1384_scale_prod

#check_dependency_graph "Rollout_p1384_scale_prod.scale_prod" against "{\"edges\":[{\"conclusion\":{\"name\":\"hPne\",\"statement\":\"SP.Nonempty\"},\"graphEdgeId\":\"h_001_hpne\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"IsTopologicalGroup G\"},{\"name\":\"<generated-instance>\",\"statement\":\"LocallyCompactSpace G\"},{\"name\":\"<generated-instance>\",\"statement\":\"TotallyDisconnectedSpace G\"},{\"name\":\"<generated-instance>\",\"statement\":\"IsTopologicalGroup H\"},{\"name\":\"<generated-instance>\",\"statement\":\"LocallyCompactSpace H\"},{\"name\":\"<generated-instance>\",\"statement\":\"TotallyDisconnectedSpace H\"}],\"rawEdgeId\":\"telescope_17\"},{\"conclusion\":{\"name\":\"hGne\",\"statement\":\"SG.Nonempty\"},\"graphEdgeId\":\"h_002_hgne\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"IsTopologicalGroup G\"},{\"name\":\"<generated-instance>\",\"statement\":\"LocallyCompactSpace G\"},{\"name\":\"<generated-instance>\",\"statement\":\"TotallyDisconnectedSpace G\"}],\"rawEdgeId\":\"telescope_18\"},{\"conclusion\":{\"name\":\"hHne\",\"statement\":\"SH.Nonempty\"},\"graphEdgeId\":\"h_003_hhne\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"IsTopologicalGroup H\"},{\"name\":\"<generated-instance>\",\"statement\":\"LocallyCompactSpace H\"},{\"name\":\"<generated-instance>\",\"statement\":\"TotallyDisconnectedSpace H\"}],\"rawEdgeId\":\"telescope_19\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"sInf {n | ∃ U, IsCompact ↑U ∧ IsOpen ↑U ∧ n = U.relIndex (Subgroup.map (φ.toMonoidHom.prodMap ψ.toMonoidHom) U)} = sInf {n | ∃ V, IsCompact ↑V ∧ IsOpen ↑V ∧ n = V.relIndex (Subgroup.map φ.toMonoidHom V)} * sInf {n | ∃ W, IsCompact ↑W ∧ IsOpen ↑W ∧ n = W.relIndex (Subgroup.map ψ.toMonoidHom W)}\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"IsTopologicalGroup G\"},{\"name\":\"<generated-instance>\",\"statement\":\"LocallyCompactSpace G\"},{\"name\":\"<generated-instance>\",\"statement\":\"TotallyDisconnectedSpace G\"},{\"name\":\"<generated-instance>\",\"statement\":\"IsTopologicalGroup H\"},{\"name\":\"<generated-instance>\",\"statement\":\"LocallyCompactSpace H\"},{\"name\":\"<generated-instance>\",\"statement\":\"TotallyDisconnectedSpace H\"},{\"name\":\"hPne\",\"statement\":\"SP.Nonempty\"},{\"name\":\"hGne\",\"statement\":\"SG.Nonempty\"},{\"name\":\"hHne\",\"statement\":\"SH.Nonempty\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1384_scale_prod\",\"reconstructedProofSha256\":\"34199488470e5da349edf7403291821d8cdb498fcc7d7e556d007843922f8486\",\"selectedEdgeCount\":4,\"theoremName\":\"Rollout_p1384_scale_prod.scale_prod\",\"topologySha256\":\"1da667801e740c52d6105a512b20eae005a2c477a38b9219361ad9b071c19e8b\"}"

namespace Rollout_p1462_locallycompact_prod_ascoli

-- graph_id: p1462_locallycompact_prod_ascoli
-- topology_sha256: 2ae746cbc6be46666faafa2b65013d41608ef6d88274e4b722e55de0f80ebd1f
/- accepted add_to_file helper 1 -/

open Set

lemma continuous_sectionMap_real
    (Z X : Type*) [TopologicalSpace Z] [LocallyCompactSpace Z] [TopologicalSpace X] :
    Continuous
      (fun p : C(Z × X, ℝ) × Z =>
        (⟨fun x => p.1 (p.2, x),
          p.1.continuous.comp (Continuous.prodMk_right p.2)⟩ : C(X, ℝ))) := by
  rw [ContinuousMap.continuous_compactOpen]
  intro C hC U hU
  rw [isOpen_iff_forall_mem_open]
  rintro ⟨f, z⟩ hf
  have hn : IsOpen (f ⁻¹' U) := hU.preimage f.continuous
  have hprod : ({z} : Set Z) ×ˢ C ⊆ f ⁻¹' U := by
    rintro ⟨z', x⟩ ⟨hz', hx⟩
    simp at hz'
    subst z'
    exact hf hx
  obtain ⟨V, W, hV, hW, hzV, hCW, hVW⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := z)) hC hn hprod
  obtain ⟨L, hL, hzL, hLV⟩ := exists_compact_subset hV (hzV rfl)
  refine ⟨{g : C(Z × X, ℝ) | Set.MapsTo g (L ×ˢ C) U} ×ˢ interior L, ?_,
    (ContinuousMap.isOpen_setOf_mapsTo (hL.prod hC) hU).prod isOpen_interior,
    ⟨?_, hzL⟩⟩
  · rintro ⟨g, z'⟩ ⟨hg, hz'⟩
    intro x hx
    exact hg ⟨interior_subset hz', hx⟩
  · rintro ⟨z', x⟩ ⟨hz', hx⟩
    exact hVW ⟨hLV hz', hCW hx⟩

/- verified submission -/
theorem locallyCompact_prod_ascoli
    (Z X : Type*) [TopologicalSpace Z] [T35Space Z] [LocallyCompactSpace Z]
    [TopologicalSpace X] [T35Space X]
    (hX : ∀ K : Set C(X, ℝ), IsCompact K →
      Continuous (fun p : K × X => (p.1 : C(X, ℝ)) p.2)) :
    ∀ K : Set C(Z × X, ℝ), IsCompact K →
      Continuous (fun p : K × (Z × X) => (p.1 : C(Z × X, ℝ)) p.2) := by
  intro K hK
  let Φ : C(Z × X, ℝ) × Z → C(X, ℝ) := fun p =>
    ⟨fun x => p.1 (p.2, x),
      p.1.continuous.comp (Continuous.prodMk_right p.2)⟩
  have hΦ : Continuous Φ := continuous_sectionMap_real Z X
  rw [continuous_iff_continuousAt]
  rintro ⟨f, ⟨z, x⟩⟩
  obtain ⟨L, hL, hzL, -⟩ := exists_compact_subset isOpen_univ (Set.mem_univ z)
  let A : Set C(X, ℝ) := Φ '' (K ×ˢ L)
  have hA : IsCompact A := (hK.prod hL).image hΦ
  have hEv : Continuous (fun p : A × X => (p.1 : C(X, ℝ)) p.2) := hX A hA
  let S : Set (K × (Z × X)) := (fun p => p.2.1) ⁻¹' interior L
  have hS : IsOpen S := isOpen_interior.preimage (continuous_fst.comp continuous_snd)
  have hval : Continuous (Subtype.val : S → K × (Z × X)) := continuous_subtype_val
  have hCproj : Continuous (fun s : S => ((s.1.1 : K) : C(Z × X, ℝ))) := by
    exact continuous_subtype_val.comp (continuous_fst.comp hval)
  have hZproj : Continuous (fun s : S => s.1.2.1) := by
    exact continuous_fst.comp (continuous_snd.comp hval)
  have hXproj : Continuous (fun s : S => s.1.2.2) := by
    exact continuous_snd.comp (continuous_snd.comp hval)
  have hsec : Continuous (fun s : S => Φ (((s.1.1 : K) : C(Z × X, ℝ)), s.1.2.1)) :=
    hΦ.comp (hCproj.prodMk hZproj)
  have hmem : ∀ s : S, Φ (((s.1.1 : K) : C(Z × X, ℝ)), s.1.2.1) ∈ A := by
    intro s
    refine Set.mem_image_of_mem Φ ?_
    exact ⟨s.1.1.property, interior_subset s.2⟩
  have hsecA : Continuous
      (fun s : S => (⟨Φ (((s.1.1 : K) : C(Z × X, ℝ)), s.1.2.1), hmem s⟩ : A)) :=
    hsec.codRestrict hmem
  have hpair : Continuous
      (fun s : S =>
        ((⟨Φ (((s.1.1 : K) : C(Z × X, ℝ)), s.1.2.1), hmem s⟩ : A), s.1.2.2)) :=
    hsecA.prodMk hXproj
  have hloc : Continuous
      (fun s : S => ((⟨Φ (((s.1.1 : K) : C(Z × X, ℝ)), s.1.2.1), hmem s⟩ : A) : C(X, ℝ)) s.1.2.2) :=
    hEv.comp hpair
  have hloc' : Continuous
      ((fun p : K × (Z × X) => (p.1 : C(Z × X, ℝ)) p.2) ∘ (Subtype.val : S → K × (Z × X))) := by
    convert hloc using 1
  let ps : S := ⟨⟨f, ⟨z, x⟩⟩, hzL⟩
  exact (hS.isOpenEmbedding_subtypeVal.continuousAt_iff (x := ps)).mp
    (hloc'.continuousAt (x := ps))

end Rollout_p1462_locallycompact_prod_ascoli

#check_dependency_graph "Rollout_p1462_locallycompact_prod_ascoli.locallyCompact_prod_ascoli" against "{\"edges\":[{\"conclusion\":{\"name\":\"hΦ\",\"statement\":\"Continuous Φ\"},\"graphEdgeId\":\"h_001_h\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"LocallyCompactSpace Z\"}],\"rawEdgeId\":\"telescope_11\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"Continuous fun p => ↑p.1 p.2\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"LocallyCompactSpace Z\"},{\"name\":\"hX\",\"statement\":\"∀ (K : Set C(X, ℝ)), IsCompact K → Continuous fun p => ↑p.1 p.2\"},{\"name\":\"hK\",\"statement\":\"IsCompact K\"},{\"name\":\"hΦ\",\"statement\":\"Continuous Φ\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1462_locallycompact_prod_ascoli\",\"reconstructedProofSha256\":\"222fec63c4a43f24385f508de85fa4cc7571db5e728cc922a31fc7e30836e17c\",\"selectedEdgeCount\":2,\"theoremName\":\"Rollout_p1462_locallycompact_prod_ascoli.locallyCompact_prod_ascoli\",\"topologySha256\":\"2ae746cbc6be46666faafa2b65013d41608ef6d88274e4b722e55de0f80ebd1f\"}"

namespace Rollout_p1479_completion_preserves_finite_one_point_exte

-- graph_id: p1479_completion_preserves_finite_one_point_exte
-- topology_sha256: 39b1009545f4bff0a670c51396fb742561c861c05ae85f94cd168a4c403d40dc
/- accepted add_to_file helper 1 -/
lemma completion_diam_eq
    (A : Type*) [MetricSpace A] :
    Metric.diam (Set.univ : Set (UniformSpace.Completion A)) =
      Metric.diam (Set.univ : Set A) := by
  have hclosure : closure (Set.range (UniformSpace.Completion.coe' : A → UniformSpace.Completion A)) = Set.univ :=
    UniformSpace.Completion.denseRange_coe.closure_range
  calc
    Metric.diam (Set.univ : Set (UniformSpace.Completion A))
        = Metric.diam (closure (Set.range (UniformSpace.Completion.coe' : A → UniformSpace.Completion A))) := by
          rw [hclosure]
    _ = Metric.diam (Set.range (UniformSpace.Completion.coe' : A → UniformSpace.Completion A)) :=
          Metric.diam_closure _
    _ = Metric.diam (Set.univ : Set A) :=
          UniformSpace.Completion.coe_isometry.diam_range

lemma dist_le_one_of_diam_one
    {X : Type*} [PseudoMetricSpace X]
    (h : Metric.diam (Set.univ : Set X) = 1) (x y : X) :
    dist x y ≤ 1 := by
  have hed : Metric.ediam (Set.univ : Set X) ≠ ⊤ := by
    intro he
    simp [Metric.diam, he] at h
  exact (Metric.dist_le_diam_of_mem' hed (Set.mem_univ x) (Set.mem_univ y)).trans_eq h

lemma exists_extension_on_range
    {A : Type*} [MetricSpace A]
    (hext : ∀ (F : Set A), F.Finite →
      ∀ f : F → Set.Icc (0 : ℝ) 1,
        (∀ x y : F,
          |(f x : ℝ) - (f y : ℝ)| ≤ dist (x : A) (y : A) ∧
            dist (x : A) (y : A) ≤ (f x : ℝ) + (f y : ℝ)) →
        ∃ z : A, ∀ x : F, dist z (x : A) = (f x : ℝ))
    {ι : Type*} [Finite ι] {a : ι → A} (ha : Function.Injective a)
    (r : ι → Set.Icc (0 : ℝ) 1)
    (hcompat : ∀ i j : ι,
      |(r i : ℝ) - (r j : ℝ)| ≤ dist (a i) (a j) ∧
        dist (a i) (a j) ≤ (r i : ℝ) + (r j : ℝ)) :
    ∃ z : A, ∀ i : ι, dist z (a i) = (r i : ℝ) := by
  classical
  let idx : Set.range a → ι := fun y => Classical.choose y.2
  let rr : Set.range a → Set.Icc (0 : ℝ) 1 := fun y => r (idx y)
  have hidx : ∀ y : Set.range a, a (idx y) = y.1 := by
    intro y
    exact Classical.choose_spec y.2
  obtain ⟨z, hz⟩ := hext (Set.range a) (Set.finite_range a) rr (by
    intro x y
    simpa [rr, idx, hidx x, hidx y] using hcompat (idx x) (idx y))
  refine ⟨z, fun i => ?_⟩
  have hmem : a i ∈ Set.range a := Set.mem_range_self i
  have hz' := hz ⟨a i, hmem⟩
  have hid : idx ⟨a i, hmem⟩ = i := ha (hidx ⟨a i, hmem⟩)
  simpa [rr, hid] using hz'

/- accepted add_to_file helper 2 -/
lemma exists_isometric_approx_fin
    {A : Type*} [MetricSpace A]
    (hext : ∀ (F : Set A), F.Finite →
      ∀ f : F → Set.Icc (0 : ℝ) 1,
        (∀ x y : F,
          |(f x : ℝ) - (f y : ℝ)| ≤ dist (x : A) (y : A) ∧
            dist (x : A) (y : A) ≤ (f x : ℝ) + (f y : ℝ)) →
        ∃ z : A, ∀ x : F, dist z (x : A) = (f x : ℝ))
    (hdiamX : Metric.diam (Set.univ : Set (UniformSpace.Completion A)) = 1) :
    ∀ (n : ℕ) (x : Fin n → UniformSpace.Completion A),
      Function.Injective x → ∀ {ε : ℝ}, 0 < ε →
        ∃ a : Fin n → A,
          (∀ i, dist ((a i : UniformSpace.Completion A)) (x i) < ε) ∧
          (∀ i j, dist (a i) (a j) = dist (x i) (x j)) := by
  intro n
  induction n with
  | zero =>
      intro x hx ε hε
      refine ⟨fun i => i.elim0, ?_, ?_⟩
      · intro i; exact i.elim0
      · intro i; exact i.elim0
  | succ n ih =>
      intro x hx ε hε
      by_cases hn : n = 0
      · subst n
        obtain ⟨b, hb⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt
          (x 0) hε
        refine ⟨fun _ => b, ?_, ?_⟩
        · intro i
          have hi : i = 0 := by
            ext
            omega
          subst i
          rw [dist_comm ((b : UniformSpace.Completion A)) (x 0)]
          exact hb
        · intro i j
          have hi : i = 0 := by
            ext
            omega
          have hj : j = 0 := by
            ext
            omega
          subst i
          subst j
          simp
      · haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
        let D : Fin n → ℝ := fun j => dist (x j.castSucc) (x (Fin.last n))
        obtain ⟨j0, -, hmin⟩ := Finset.exists_min_image Finset.univ D Finset.univ_nonempty
        let m : ℝ := D j0
        have hmpos : 0 < m := by
          dsimp [m, D]
          rw [dist_pos]
          intro hxy
          exact Fin.castSucc_ne_last j0 (hx hxy)
        have hmle : ∀ j : Fin n, m ≤ D j := fun j => hmin j (Finset.mem_univ j)
        have hmle_one : m ≤ 1 := by
          dsimp [m, D]
          exact dist_le_one_of_diam_one hdiamX (x j0.castSucc) (x (Fin.last n))
        let ρ : ℝ := min (m / 2) (ε / 2)
        have hρpos : 0 < ρ := by positivity
        have hρle_mhalf : ρ ≤ m / 2 := min_le_left _ _
        have hρle_ehalf : ρ ≤ ε / 2 := min_le_right _ _
        have hρle_one : ρ ≤ 1 := by linarith
        let c : ℝ := ρ / 4
        have hcpos : 0 < c := by positivity
        have hxres : Function.Injective (fun j : Fin n => x j.castSucc) := by
          intro i j h
          exact Fin.castSucc_injective n (hx h)
        obtain ⟨aold, haold_approx, haold_dist⟩ := ih
          (fun j : Fin n => x j.castSucc) hxres hcpos
        obtain ⟨b, hb⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt
          (x (Fin.last n)) hcpos
        have haold_inj : Function.Injective aold := by
          intro i j h
          have hd : dist (x i.castSucc) (x j.castSucc) = 0 := by
            rw [← haold_dist i j, h, dist_self]
          have hxij : x i.castSucc = x j.castSucc := dist_eq_zero.mp hd
          exact Fin.castSucc_injective n (hx hxij)
        have herr : ∀ j : Fin n,
            |dist (aold j) b - D j| < ρ / 2 := by
          intro j
          have hupper : dist (aold j) b < D j + ρ / 2 := by
            have h1 : dist ((aold j : UniformSpace.Completion A)) ((b : UniformSpace.Completion A)) ≤
                dist ((aold j : UniformSpace.Completion A)) (x j.castSucc) +
                  dist (x j.castSucc) ((b : UniformSpace.Completion A)) :=
              dist_triangle _ _ _
            have h2 : dist (x j.castSucc) ((b : UniformSpace.Completion A)) ≤
                dist (x j.castSucc) (x (Fin.last n)) +
                  dist (x (Fin.last n)) ((b : UniformSpace.Completion A)) :=
              dist_triangle _ _ _
            have hA := haold_approx j
            rw [UniformSpace.Completion.dist_eq (aold j) b] at h1
            dsimp [D, c] at *
            linarith
          have hlower : D j < dist (aold j) b + ρ / 2 := by
            have h1 : dist (x j.castSucc) (x (Fin.last n)) ≤
                dist (x j.castSucc) ((aold j : UniformSpace.Completion A)) +
                  dist ((aold j : UniformSpace.Completion A)) (x (Fin.last n)) :=
              dist_triangle _ _ _
            have h2 : dist ((aold j : UniformSpace.Completion A)) (x (Fin.last n)) ≤
                dist ((aold j : UniformSpace.Completion A)) ((b : UniformSpace.Completion A)) +
                  dist ((b : UniformSpace.Completion A)) (x (Fin.last n)) :=
              dist_triangle _ _ _
            have hA := haold_approx j
            have hA' : dist (x j.castSucc) ((aold j : UniformSpace.Completion A)) < c := by
              rw [dist_comm (x j.castSucc) ((aold j : UniformSpace.Completion A))]
              exact hA
            have hB' : dist ((b : UniformSpace.Completion A)) (x (Fin.last n)) < c := by
              rw [dist_comm ((b : UniformSpace.Completion A)) (x (Fin.last n))]
              exact hb
            rw [UniformSpace.Completion.dist_eq (aold j) b] at h2
            dsimp [D, c] at *
            linarith
          rw [abs_lt]
          constructor <;> linarith
        have hρle_Dhalf : ∀ j : Fin n, ρ ≤ D j / 2 := by
          intro j
          have hmj := hmle j
          linarith
        have hab_pos : ∀ j : Fin n, 0 < dist (aold j) b := by
          intro j
          have hlt := (abs_lt.mp (herr j)).1
          have hDj : 0 < D j := lt_of_lt_of_le hmpos (hmle j)
          have hρD := hρle_Dhalf j
          linarith
        let g : Option (Fin n) → A := fun
          | none => b
          | some j => aold j
        have hg_inj : Function.Injective g := by
          intro p q hpq
          cases p with
          | none =>
              cases q with
              | none => rfl
              | some j =>
                  have h : dist (aold j) b = 0 := by
                    dsimp [g] at hpq
                    rw [← hpq, dist_self]
                  exact False.elim ((ne_of_gt (hab_pos j)) h)
          | some i =>
              cases q with
              | none =>
                  have h : dist (aold i) b = 0 := by
                    dsimp [g] at hpq
                    rw [hpq, dist_self]
                  exact False.elim ((ne_of_gt (hab_pos i)) h)
              | some j =>
                  dsimp [g] at hpq
                  exact congrArg some (haold_inj hpq)
        let r : Option (Fin n) → Set.Icc (0 : ℝ) 1 := fun
          | none => ⟨ρ, ⟨le_of_lt hρpos, hρle_one⟩⟩
          | some j => ⟨D j, ⟨dist_nonneg, dist_le_one_of_diam_one hdiamX _ _⟩⟩
        have hcompat : ∀ p q : Option (Fin n),
            |(r p : ℝ) - (r q : ℝ)| ≤ dist (g p) (g q) ∧
              dist (g p) (g q) ≤ (r p : ℝ) + (r q : ℝ) := by
          intro p q
          cases p with
          | none =>
              cases q with
              | none =>
                  simp [g, r, hρpos.le]
              | some j =>
                  have herr' : |dist b (aold j) - D j| < ρ / 2 := by
                    rw [dist_comm b (aold j)]
                    exact herr j
                  have hlt := abs_lt.mp herr'
                  have hρD := hρle_Dhalf j
                  constructor
                  · rw [abs_sub_le_iff]
                    change ρ - D j ≤ dist b (aold j) ∧ D j - ρ ≤ dist b (aold j)
                    constructor <;> linarith [hlt.1, hlt.2, hρD, hρpos.le,
                      (dist_nonneg : 0 ≤ dist b (aold j))]
                  · change dist b (aold j) ≤ ρ + D j
                    linarith
          | some i =>
              cases q with
              | none =>
                  have hlt := abs_lt.mp (herr i)
                  have hρD := hρle_Dhalf i
                  constructor
                  · rw [abs_sub_le_iff]
                    change D i - ρ ≤ dist (aold i) b ∧ ρ - D i ≤ dist (aold i) b
                    constructor <;> linarith [hlt.1, hlt.2, hρD, hρpos.le,
                      (dist_nonneg : 0 ≤ dist (aold i) b)]
                  · change dist (aold i) b ≤ D i + ρ
                    linarith
              | some j =>
                  constructor
                  · rw [abs_sub_le_iff]
                    change D i - D j ≤ dist (aold i) (aold j) ∧
                      D j - D i ≤ dist (aold i) (aold j)
                    rw [haold_dist i j]
                    constructor
                    · have htri := dist_triangle (x i.castSucc) (x j.castSucc) (x (Fin.last n))
                      dsimp [D] at htri ⊢
                      linarith
                    · have htri := dist_triangle (x j.castSucc) (x i.castSucc) (x (Fin.last n))
                      have htri' : dist (x j.castSucc) (x (Fin.last n)) ≤
                          dist (x i.castSucc) (x j.castSucc) +
                            dist (x i.castSucc) (x (Fin.last n)) := by
                        rw [dist_comm (x j.castSucc) (x i.castSucc)] at htri
                        exact htri
                      dsimp [D] at htri' ⊢
                      linarith
                  · change dist (aold i) (aold j) ≤ D i + D j
                    rw [haold_dist i j]
                    have htri := dist_triangle (x i.castSucc) (x (Fin.last n)) (x j.castSucc)
                    have htri' : dist (x i.castSucc) (x j.castSucc) ≤
                        dist (x i.castSucc) (x (Fin.last n)) +
                          dist (x j.castSucc) (x (Fin.last n)) := by
                      rw [dist_comm (x (Fin.last n)) (x j.castSucc)] at htri
                      exact htri
                    dsimp [D] at htri' ⊢
                    linarith
        obtain ⟨z, hz⟩ := exists_extension_on_range hext hg_inj r hcompat
        let anew : Fin (n + 1) → A := Fin.lastCases z aold
        have hanew_approx : ∀ i : Fin (n + 1),
            dist ((anew i : UniformSpace.Completion A)) (x i) < ε := by
          intro i
          refine Fin.lastCases ?_ ?_ i
          · have hzb : dist z b = ρ := by
              simpa [r] using hz none
            have h1 : dist ((z : UniformSpace.Completion A)) (x (Fin.last n)) ≤
                dist ((z : UniformSpace.Completion A)) ((b : UniformSpace.Completion A)) +
                  dist ((b : UniformSpace.Completion A)) (x (Fin.last n)) :=
              dist_triangle _ _ _
            rw [UniformSpace.Completion.dist_eq z b] at h1
            have hb' : dist ((b : UniformSpace.Completion A)) (x (Fin.last n)) < c := by
              rw [dist_comm ((b : UniformSpace.Completion A)) (x (Fin.last n))]
              exact hb
            have hgoal : dist ((z : UniformSpace.Completion A)) (x (Fin.last n)) < ε := by
              dsimp [c] at *
              linarith
            simpa only [anew, Fin.lastCases_last] using hgoal
          · intro j
            have hA := haold_approx j
            have hgoal : dist ((aold j : UniformSpace.Completion A)) (x j.castSucc) < ε := by
              dsimp [c] at hA
              linarith
            simpa only [anew, Fin.lastCases_castSucc] using hgoal
        have hanew_dist : ∀ i j : Fin (n + 1),
            dist (anew i) (anew j) = dist (x i) (x j) := by
          intro i j
          refine Fin.lastCases ?_ ?_ i
          · refine Fin.lastCases ?_ ?_ j
            · simp only [anew, Fin.lastCases_last, dist_self]
            · intro k
              have hzk : dist z (aold k) = D k := by
                simpa [r] using hz (some k)
              simp only [anew, Fin.lastCases_last, Fin.lastCases_castSucc]
              rw [hzk]
              exact dist_comm (x k.castSucc) (x (Fin.last n))
          · intro k
            refine Fin.lastCases ?_ ?_ j
            · have hzk : dist z (aold k) = D k := by
                simpa [r] using hz (some k)
              simp only [anew, Fin.lastCases_last, Fin.lastCases_castSucc]
              rw [dist_comm (aold k) z, hzk]
            · intro l
              simp only [anew, Fin.lastCases_castSucc]
              exact haold_dist k l
        refine ⟨anew, hanew_approx, hanew_dist⟩

/- accepted add_to_file helper 3 -/
lemma completion_extension_fin
    {A : Type*} [MetricSpace A]
    (hext : ∀ (F : Set A), F.Finite →
      ∀ f : F → Set.Icc (0 : ℝ) 1,
        (∀ x y : F,
          |(f x : ℝ) - (f y : ℝ)| ≤ dist (x : A) (y : A) ∧
            dist (x : A) (y : A) ≤ (f x : ℝ) + (f y : ℝ)) →
        ∃ z : A, ∀ x : F, dist z (x : A) = (f x : ℝ))
    (hdiamX : Metric.diam (Set.univ : Set (UniformSpace.Completion A)) = 1)
    {n : ℕ} (x : Fin n → UniformSpace.Completion A) (hx : Function.Injective x)
    (r : Fin n → Set.Icc (0 : ℝ) 1)
    (hcompat : ∀ i j : Fin n,
      |(r i : ℝ) - (r j : ℝ)| ≤ dist (x i) (x j) ∧
        dist (x i) (x j) ≤ (r i : ℝ) + (r j : ℝ)) :
    ∃ z : UniformSpace.Completion A, ∀ i : Fin n,
      dist z (x i) = (r i : ℝ) := by
  classical
  by_cases hn : n = 0
  · subst n
    let e : (∅ : Set A) → Set.Icc (0 : ℝ) 1 := fun y => ⟨0, by norm_num⟩
    obtain ⟨a, -⟩ := hext ∅ Set.finite_empty e (by
      intro y
      exact False.elim y.2)
    exact ⟨(a : UniformSpace.Completion A), fun i => i.elim0⟩
  · haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    by_cases hzero : ∃ i : Fin n, (r i : ℝ) = 0
    · obtain ⟨i, hi⟩ := hzero
      refine ⟨x i, fun j => ?_⟩
      have hpair := hcompat i j
      have hle : (r j : ℝ) ≤ dist (x i) (x j) := by
        have h := hpair.1
        rw [hi, zero_sub, abs_neg, abs_of_nonneg (r j).2.1] at h
        exact h
      have hge : dist (x i) (x j) ≤ (r j : ℝ) := by
        simpa [hi] using hpair.2
      exact le_antisymm hge hle
    · have hrpos : ∀ i : Fin n, 0 < (r i : ℝ) := by
        intro i
        exact lt_of_le_of_ne (r i).2.1 (by
          intro h
          exact hzero ⟨i, h.symm⟩)
      obtain ⟨i0, hi0⟩ := Finite.exists_min (fun i : Fin n => (r i : ℝ))
      let R : ℝ := r i0
      have hRpos : 0 < R := hrpos i0
      have hRle : ∀ i : Fin n, R ≤ (r i : ℝ) := hi0
      have hRle_one : R ≤ 1 := (r i0).2.2
      let δ : ℕ → ℝ := fun k => R / 2 / 2 ^ k
      have hδpos : ∀ k, 0 < δ k := by
        intro k
        dsimp [δ]
        positivity
      have hδsucc : ∀ k, δ (k + 1) = δ k / 2 := by
        intro k
        dsimp [δ]
        ring_nf
      have hδle_halfR : ∀ k, δ k ≤ R / 2 := by
        intro k
        induction k with
        | zero =>
            dsimp [δ]
            linarith
        | succ k ih =>
            rw [hδsucc]
            linarith
      have hδlt_r : ∀ k i, δ k < (r i : ℝ) := by
        intro k i
        have h1 := hδle_halfR k
        have h2 := hRle i
        have h3 := hrpos i
        linarith
      have hδle_one : ∀ k, δ k ≤ 1 := by
        intro k
        have h1 := hδle_halfR k
        linarith
      let ε : ℕ → ℝ := fun k => δ k / 8
      have hεpos : ∀ k, 0 < ε k := fun k => by positivity
      have hex : ∀ k : ℕ, ∃ a : Fin n → A,
          (∀ i, dist ((a i : UniformSpace.Completion A)) (x i) < ε k) ∧
          (∀ i j, dist (a i) (a j) = dist (x i) (x j)) := by
        intro k
        exact exists_isometric_approx_fin hext hdiamX n x hx (hεpos k)
      let a : ℕ → Fin n → A := fun k => Classical.choose (hex k)
      have ha : ∀ k,
          (∀ i, dist (((a k) i : UniformSpace.Completion A)) (x i) < ε k) ∧
          (∀ i j, dist ((a k) i) ((a k) j) = dist (x i) (x j)) := by
        intro k
        exact Classical.choose_spec (hex k)
      have ha_inj : ∀ k, Function.Injective (a k) := by
        intro k i j h
        have hd : dist (x i) (x j) = 0 := by
          rw [← (ha k).2 i j, h, dist_self]
        exact hx (dist_eq_zero.mp hd)
      have hcompatA : ∀ k i j,
          |(r i : ℝ) - (r j : ℝ)| ≤ dist ((a k) i) ((a k) j) ∧
            dist ((a k) i) ((a k) j) ≤ (r i : ℝ) + (r j : ℝ) := by
        intro k i j
        simpa [(ha k).2 i j] using hcompat i j
      obtain ⟨z0, hz0⟩ := exists_extension_on_range hext (ha_inj 0) r (hcompatA 0)
      have step : ∀ k (z : A), (∀ i, dist z ((a k) i) = (r i : ℝ)) →
          ∃ w : A, dist w z = δ k ∧
            ∀ i, dist w ((a (k + 1)) i) = (r i : ℝ) := by
        intro k z hz
        have herr : ∀ i, |dist z ((a (k + 1)) i) - (r i : ℝ)| < δ k / 4 := by
          intro i
          have hold : dist ((z : UniformSpace.Completion A)) (((a k) i : UniformSpace.Completion A)) =
              (r i : ℝ) := by
            rw [UniformSpace.Completion.dist_eq]
            exact hz i
          have hupper : dist z ((a (k + 1)) i) < (r i : ℝ) + δ k / 4 := by
            have h1 : dist ((z : UniformSpace.Completion A)) (((a (k + 1)) i : UniformSpace.Completion A)) ≤
                dist ((z : UniformSpace.Completion A)) (x i) +
                  dist (x i) (((a (k + 1)) i : UniformSpace.Completion A)) :=
              dist_triangle _ _ _
            have h2 : dist ((z : UniformSpace.Completion A)) (x i) ≤
                dist ((z : UniformSpace.Completion A)) (((a k) i : UniformSpace.Completion A)) +
                  dist (((a k) i : UniformSpace.Completion A)) (x i) :=
              dist_triangle _ _ _
            have hnew' : dist (x i) (((a (k + 1)) i : UniformSpace.Completion A)) < ε (k+1) := by
              rw [dist_comm (x i) (((a (k+1)) i : UniformSpace.Completion A))]
              exact (ha (k+1)).1 i
            have hold' : dist (((a k) i : UniformSpace.Completion A)) (x i) < ε k :=
              (ha k).1 i
            rw [UniformSpace.Completion.dist_eq z ((a (k+1)) i)] at h1
            rw [hold] at h2
            have hs := hδsucc k
            have hδp := hδpos k
            dsimp [ε] at *
            linarith
          have hlower : (r i : ℝ) < dist z ((a (k + 1)) i) + δ k / 4 := by
            have h1 : dist ((z : UniformSpace.Completion A)) (((a k) i : UniformSpace.Completion A)) ≤
                dist ((z : UniformSpace.Completion A)) (x i) +
                  dist (x i) (((a k) i : UniformSpace.Completion A)) :=
              dist_triangle _ _ _
            have h2 : dist ((z : UniformSpace.Completion A)) (x i) ≤
                dist ((z : UniformSpace.Completion A)) (((a (k + 1)) i : UniformSpace.Completion A)) +
                  dist (((a (k + 1)) i : UniformSpace.Completion A)) (x i) :=
              dist_triangle _ _ _
            have hold' : dist (x i) (((a k) i : UniformSpace.Completion A)) < ε k := by
              rw [dist_comm (x i) (((a k) i : UniformSpace.Completion A))]
              exact (ha k).1 i
            have hnew' : dist (((a (k + 1)) i : UniformSpace.Completion A)) (x i) < ε (k+1) :=
              (ha (k+1)).1 i
            rw [hold] at h1
            rw [UniformSpace.Completion.dist_eq z ((a (k+1)) i)] at h2
            have hs := hδsucc k
            have hδp := hδpos k
            dsimp [ε] at *
            linarith
          rw [abs_lt]
          constructor <;> linarith
        have hdistpos : ∀ i, 0 < dist z ((a (k + 1)) i) := by
          intro i
          have hlt := (abs_lt.mp (herr i)).1
          have hδr := hδlt_r k i
          have hδp := hδpos k
          linarith
        let g : Option (Fin n) → A := fun
          | none => z
          | some i => (a (k + 1)) i
        have hg_inj : Function.Injective g := by
          intro p q hpq
          cases p with
          | none =>
              cases q with
              | none => rfl
              | some i =>
                  have h : dist z ((a (k+1)) i) = 0 := by
                    dsimp [g] at hpq
                    rw [← hpq, dist_self]
                  exact False.elim ((ne_of_gt (hdistpos i)) h)
          | some i =>
              cases q with
              | none =>
                  have h : dist z ((a (k+1)) i) = 0 := by
                    dsimp [g] at hpq
                    rw [hpq, dist_self]
                  exact False.elim ((ne_of_gt (hdistpos i)) h)
              | some j =>
                  dsimp [g] at hpq
                  exact congrArg some ((ha_inj (k+1)) hpq)
        let rr : Option (Fin n) → Set.Icc (0 : ℝ) 1 := fun
          | none => ⟨δ k, ⟨(hδpos k).le, hδle_one k⟩⟩
          | some i => r i
        have hcompg : ∀ p q : Option (Fin n),
            |(rr p : ℝ) - (rr q : ℝ)| ≤ dist (g p) (g q) ∧
              dist (g p) (g q) ≤ (rr p : ℝ) + (rr q : ℝ) := by
          intro p q
          cases p with
          | none =>
              cases q with
              | none =>
                  simp [g, rr, (hδpos k).le]
              | some i =>
                  have hlt := abs_lt.mp (herr i)
                  have hδr := hδlt_r k i
                  constructor
                  · rw [abs_sub_le_iff]
                    change δ k - (r i : ℝ) ≤ dist z ((a (k+1)) i) ∧
                      (r i : ℝ) - δ k ≤ dist z ((a (k+1)) i)
                    constructor <;> linarith [hlt.1, hlt.2, hδr,
                      (dist_nonneg : 0 ≤ dist z ((a (k+1)) i))]
                  · change dist z ((a (k+1)) i) ≤ δ k + (r i : ℝ)
                    linarith
          | some i =>
              cases q with
              | none =>
                  have herr' : |dist ((a (k+1)) i) z - (r i : ℝ)| < δ k / 4 := by
                    rw [dist_comm ((a (k+1)) i) z]
                    exact herr i
                  have hlt := abs_lt.mp herr'
                  have hδr := hδlt_r k i
                  constructor
                  · rw [abs_sub_le_iff]
                    change (r i : ℝ) - δ k ≤ dist ((a (k+1)) i) z ∧
                      δ k - (r i : ℝ) ≤ dist ((a (k+1)) i) z
                    constructor <;> linarith [hlt.1, hlt.2, hδr,
                      (dist_nonneg : 0 ≤ dist ((a (k+1)) i) z)]
                  · change dist ((a (k+1)) i) z ≤ (r i : ℝ) + δ k
                    linarith
              | some j =>
                  simpa [g, rr, (ha (k+1)).2 i j] using hcompat i j
        obtain ⟨w, hw⟩ := exists_extension_on_range hext hg_inj rr hcompg
        refine ⟨w, ?_, ?_⟩
        · simpa [rr] using hw none
        · intro i
          simpa [rr] using hw (some i)
      let next : ℕ → A → A := fun k z =>
        if hz : (∀ i, dist z ((a k) i) = (r i : ℝ)) then
          Classical.choose (step k z hz)
        else z
      let zseq : ℕ → A := Nat.rec (motive := fun _ => A) z0 (fun k z => next k z)
      have hzsolves : ∀ k i, dist (zseq k) ((a k) i) = (r i : ℝ) := by
        intro k
        induction k with
        | zero =>
            intro i
            exact hz0 i
        | succ k ih =>
            change ∀ i, dist (next k (zseq k)) ((a (k+1)) i) = (r i : ℝ)
            dsimp [next]
            rw [dif_pos ih]
            exact (Classical.choose_spec (step k (zseq k) ih)).2
      have hzstep : ∀ k, dist (zseq (k + 1)) (zseq k) = δ k := by
        intro k
        change dist (next k (zseq k)) (zseq k) = δ k
        dsimp [next]
        rw [dif_pos (hzsolves k)]
        exact (Classical.choose_spec (step k (zseq k) (hzsolves k))).1
      have hsummableδ : Summable δ := by
        dsimp [δ]
        exact summable_geometric_two' R
      let y : ℕ → UniformSpace.Completion A := fun k => (zseq k : UniformSpace.Completion A)
      have hsummableY : Summable (fun k => dist (y k) (y (k+1))) := by
        have hfun : (fun k => dist (y k) (y (k+1))) = δ := by
          funext k
          calc dist (y k) (y (k+1))
              = dist (zseq k) (zseq (k+1)) := by
                  dsimp [y]
                  exact UniformSpace.Completion.dist_eq _ _
          _ = dist (zseq (k+1)) (zseq k) := dist_comm _ _
          _ = δ k := hzstep k
        rw [hfun]
        exact hsummableδ
      have hcauchy : CauchySeq y := cauchySeq_of_summable_dist hsummableY
      obtain ⟨z, hzlim⟩ := cauchySeq_tendsto_of_complete hcauchy
      refine ⟨z, fun i => ?_⟩
      have hδzero : Filter.Tendsto δ Filter.atTop (nhds 0) :=
        hsummableδ.tendsto_atTop_zero
      have hεzero : Filter.Tendsto ε Filter.atTop (nhds 0) := by
        simpa [ε] using hδzero.div_const 8
      have happrox_tendsto : Filter.Tendsto
          (fun k => (((a k) i : UniformSpace.Completion A))) Filter.atTop (nhds (x i)) := by
        rw [tendsto_iff_dist_tendsto_zero]
        exact squeeze_zero (fun k => dist_nonneg) (fun k => ((ha k).1 i).le) hεzero
      have hdist_tendsto : Filter.Tendsto
          (fun k => dist (y k) (((a k) i : UniformSpace.Completion A)))
          Filter.atTop (nhds (dist z (x i))) :=
        hzlim.dist happrox_tendsto
      have hterm_tendsto : Filter.Tendsto
          (fun k => dist (y k) (((a k) i : UniformSpace.Completion A)))
          Filter.atTop (nhds (r i : ℝ)) := by
        apply Filter.Tendsto.congr' _ tendsto_const_nhds
        exact Filter.Eventually.of_forall (fun k => by
          have heq : dist (y k) (((a k) i : UniformSpace.Completion A)) = (r i : ℝ) := by
            calc dist (y k) (((a k) i : UniformSpace.Completion A))
                = dist (zseq k) ((a k) i) := by
                    dsimp [y]
                    exact UniformSpace.Completion.dist_eq _ _
            _ = (r i : ℝ) := hzsolves k i
          exact heq.symm)
      exact tendsto_nhds_unique hdist_tendsto hterm_tendsto

/- verified submission -/
theorem completion_preserves_finite_one_point_extension
    (A : Type*) [MetricSpace A]
    (hdiam : Metric.diam (Set.univ : Set A) = 1)
    (hext : ∀ (F : Set A), F.Finite →
      ∀ f : F → Set.Icc (0 : ℝ) 1,
        (∀ x y : F,
          |(f x : ℝ) - (f y : ℝ)| ≤ dist (x : A) (y : A) ∧
            dist (x : A) (y : A) ≤ (f x : ℝ) + (f y : ℝ)) →
        ∃ z : A, ∀ x : F, dist z (x : A) = (f x : ℝ)) :
    Metric.diam (Set.univ : Set (UniformSpace.Completion A)) = 1 ∧
      ∀ (F : Set (UniformSpace.Completion A)), F.Finite →
        ∀ f : F → Set.Icc (0 : ℝ) 1,
          (∀ x y : F,
            |(f x : ℝ) - (f y : ℝ)| ≤
                dist (x : UniformSpace.Completion A) (y : UniformSpace.Completion A) ∧
              dist (x : UniformSpace.Completion A) (y : UniformSpace.Completion A) ≤
                (f x : ℝ) + (f y : ℝ)) →
          ∃ z : UniformSpace.Completion A, ∀ x : F,
            dist z (x : UniformSpace.Completion A) = (f x : ℝ) := by
  classical
  have hdiamX : Metric.diam (Set.univ : Set (UniformSpace.Completion A)) = 1 := by
    rw [completion_diam_eq A, hdiam]
  refine ⟨hdiamX, ?_⟩
  intro F hF f hcompat
  letI := hF.fintype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin F
  let x : Fin n → UniformSpace.Completion A := fun i => (e.symm i : UniformSpace.Completion A)
  have hx : Function.Injective x := by
    intro i j h
    apply e.symm.injective
    exact Subtype.ext h
  let r : Fin n → Set.Icc (0 : ℝ) 1 := fun i => f (e.symm i)
  have hcompatFin : ∀ i j : Fin n,
      |(r i : ℝ) - (r j : ℝ)| ≤ dist (x i) (x j) ∧
        dist (x i) (x j) ≤ (r i : ℝ) + (r j : ℝ) := by
    intro i j
    exact hcompat (e.symm i) (e.symm j)
  obtain ⟨z, hz⟩ := completion_extension_fin hext hdiamX x hx r hcompatFin
  refine ⟨z, fun y => ?_⟩
  have hy := hz (e y)
  simpa [x, r] using hy

end Rollout_p1479_completion_preserves_finite_one_point_exte

#check_dependency_graph "Rollout_p1479_completion_preserves_finite_one_point_exte.completion_preserves_finite_one_point_extension" against "{\"edges\":[{\"conclusion\":{\"name\":\"hdiamX\",\"statement\":\"Metric.diam Set.univ = 1\"},\"graphEdgeId\":\"h_001_hdiamx\",\"premises\":[{\"name\":\"hdiam\",\"statement\":\"Metric.diam Set.univ = 1\"}],\"rawEdgeId\":\"telescope_4\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"Metric.diam Set.univ = 1 ∧ ∀ (F : Set (UniformSpace.Completion A)), F.Finite → ∀ (f : ↑F → ↑(Set.Icc 0 1)), (∀ (x y : ↑F), |↑(f x) - ↑(f y)| ≤ dist ↑x ↑y ∧ dist ↑x ↑y ≤ ↑(f x) + ↑(f y)) → ∃ z, ∀ (x : ↑F), dist z ↑x = ↑(f x)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hext\",\"statement\":\"∀ (F : Set A), F.Finite → ∀ (f : ↑F → ↑(Set.Icc 0 1)), (∀ (x y : ↑F), |↑(f x) - ↑(f y)| ≤ dist ↑x ↑y ∧ dist ↑x ↑y ≤ ↑(f x) + ↑(f y)) → ∃ z, ∀ (x : ↑F), dist z ↑x = ↑(f x)\"},{\"name\":\"hdiamX\",\"statement\":\"Metric.diam Set.univ = 1\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1479_completion_preserves_finite_one_point_exte\",\"reconstructedProofSha256\":\"f502da8ed39d6421ae6092cb084ca49db2da3d85286746dc885524a997d1bd54\",\"selectedEdgeCount\":2,\"theoremName\":\"Rollout_p1479_completion_preserves_finite_one_point_exte.completion_preserves_finite_one_point_extension\",\"topologySha256\":\"39b1009545f4bff0a670c51396fb742561c861c05ae85f94cd168a4c403d40dc\"}"

namespace Rollout_p1494_p_adic_solenoid_only_periodic_point

-- graph_id: p1494_p_adic_solenoid_only_periodic_point
-- topology_sha256: 3f89eab81a87f5fb87faadc8e5b9321d877ac94dd5afae1efdb5824852a46a7d
/- accepted add_to_file helper 1 -/
lemma solenoid_iterate_apply (k m : ℕ) (z : ℕ → ℂ) (n : ℕ) :
    ((fun w : ℕ → ℂ => fun n => w n ^ k)^[m] z) n = z n ^ k ^ m := by
  induction m generalizing z with
  | zero =>
      simp
  | succ m ih =>
      rw [Function.iterate_succ_apply]
      rw [ih (fun n => z n ^ k)]
      simp [pow_succ, pow_mul, mul_comm]

lemma pow_sub_one_eq_one_of_pow_eq_self
    (a : ℂ) (ha : a ≠ 0) {K : ℕ} (hK : 0 < K) (h : a ^ K = a) :
    a ^ (K - 1) = 1 := by
  have hK' : K = K - 1 + 1 := (Nat.succ_pred_eq_of_pos hK).symm
  have hpow : a ^ (K - 1) * a = a ^ K := by
    rw [← pow_succ, ← hK']
  have hmul : a ^ (K - 1) * a = 1 * a := by
    calc
      a ^ (K - 1) * a = a ^ K := hpow
      _ = a := h
      _ = 1 * a := by rw [one_mul]
  exact mul_right_cancel₀ ha hmul

lemma prime_power_order_forward
    (z : ℕ → ℂ) (P : ℕ → ℕ)
    (hcompat : ∀ n, z n = z (n + 1) ^ P n)
    {p a N j : ℕ} (hle : N ≤ j)
    (hdiv : p ^ a ∣ orderOf (z N)) :
    p ^ a ∣ orderOf (z j) := by
  induction hle with
  | refl => exact hdiv
  | step hle ih =>
      rename_i n
      have hpow_dvd : orderOf (z (n + 1) ^ P n) ∣ orderOf (z (n + 1)) :=
        orderOf_pow_dvd (P n)
      have hord_eq : orderOf (z n) = orderOf (z (n + 1) ^ P n) := by
        rw [hcompat n]
      exact dvd_trans ih (hord_eq.symm ▸ hpow_dvd)

lemma prime_power_order_of_prime_power
    (x : ℂ) {p a : ℕ} (hp : Nat.Prime p) (ha : 0 < a)
    (h : p ^ a ∣ orderOf (x ^ p)) :
    p ^ (a + 1) ∣ orderOf x := by
  have hd : p ^ a ∣ orderOf x := dvd_trans h (orderOf_pow_dvd p)
  have hp_dvd : p ∣ orderOf x :=
    dvd_trans (dvd_pow_self p (Nat.ne_of_gt ha)) hd
  have hgcd : Nat.gcd (orderOf x) p = p := Nat.gcd_eq_right hp_dvd
  have hquot : p ^ a ∣ orderOf x / p := by
    have h' := h
    rw [orderOf_pow' x hp.ne_zero, hgcd] at h'
    exact h'
  obtain ⟨c, hc⟩ := hp_dvd
  have hc_div : p * c / p = c := Nat.mul_div_cancel_left c hp.pos
  have hdivc : p ^ a ∣ c := by
    have h' := hquot
    rw [hc, hc_div] at h'
    exact h'
  obtain ⟨b, hb⟩ := hdivc
  use b
  rw [hc, hb]
  ring

lemma exists_prime_power_order_forward
    (P : ℕ → ℕ)
    (hP_recurrent : ∀ q, Nat.Prime q → ∀ N, ∃ n, N ≤ n ∧ P n = q)
    (z : ℕ → ℂ)
    (hcompat : ∀ n, z n = z (n + 1) ^ P n)
    {p : ℕ} (hp : Nat.Prime p)
    (a N : ℕ) (hdiv : p ∣ orderOf (z N)) :
    ∃ M, p ^ (a + 1) ∣ orderOf (z M) := by
  induction a generalizing N with
  | zero =>
      exact ⟨N, by simpa using hdiv⟩
  | succ a ih =>
      obtain ⟨M, hM⟩ := ih N hdiv
      obtain ⟨j, hMj, hPj⟩ := hP_recurrent p hp M
      have hdivj : p ^ (a + 1) ∣ orderOf (z j) :=
        prime_power_order_forward z P hcompat hMj hM
      have hdivpow : p ^ (a + 1) ∣ orderOf (z (j + 1) ^ p) := by
        rw [hcompat j, hPj] at hdivj
        exact hdivj
      have hnext : p ^ (a + 1 + 1) ∣ orderOf (z (j + 1)) :=
        prime_power_order_of_prime_power (z (j + 1)) hp (Nat.succ_pos a) hdivpow
      exact ⟨j + 1, hnext⟩

/- verified submission -/
theorem p_adic_solenoid_only_periodic_point
    (P : ℕ → ℕ)
    (hP_prime : ∀ n, Nat.Prime (P n))
    (hP_recurrent : ∀ q, Nat.Prime q → ∀ N, ∃ n, N ≤ n ∧ P n = q)
    (k : ℕ) (hk : 2 ≤ k) :
    ∀ z : ℕ → ℂ,
      ((∀ n, ‖z n‖ = 1) ∧
        ∀ n, z n = z (n + 1) ^ P n) →
      ((∃ m, 0 < m ∧
          Function.IsPeriodicPt (fun w : ℕ → ℂ => fun n => w n ^ k) m z) ↔
        z = fun _ => 1) := by
  intro z hz
  obtain ⟨hznorm, hcompat⟩ := hz
  constructor
  · rintro ⟨m, hm, hper⟩
    funext n
    have hKtwo : 2 ≤ k ^ m := by
      calc
        2 ≤ 2 ^ m := Nat.le_self_pow (Nat.ne_of_gt hm) 2
        _ ≤ k ^ m := Nat.pow_le_pow_left hk m
    have hKpos : 0 < k ^ m := by omega
    have ht : 0 < k ^ m - 1 := by omega
    have hfix : (fun w : ℕ → ℂ => fun n => w n ^ k)^[m] z = z := hper
    have hcoord : ∀ n, z n ^ k ^ m = z n := by
      intro n
      have hn := congrFun hfix n
      rwa [solenoid_iterate_apply k m z n] at hn
    have hroot : ∀ n, z n ^ (k ^ m - 1) = 1 := by
      intro n
      have hzne : z n ≠ 0 := by
        intro hz0
        have hnorm := hznorm n
        rw [hz0] at hnorm
        norm_num at hnorm
      exact pow_sub_one_eq_one_of_pow_eq_self (z n) hzne hKpos (hcoord n)
    by_contra hzn
    have hord_ne_one : orderOf (z n) ≠ 1 := by
      intro hord
      exact hzn (orderOf_eq_one_iff.mp hord)
    obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hord_ne_one
    obtain ⟨M, hM⟩ :=
      exists_prime_power_order_forward P hP_recurrent z hcompat hr (k ^ m - 1) n hrdvd
    have hfin : IsOfFinOrder (z M) := by
      exact isOfFinOrder_iff_pow_eq_one.mpr ⟨k ^ m - 1, ht, hroot M⟩
    have hordMpos : 0 < orderOf (z M) := orderOf_pos_iff.mpr hfin
    have hpow_le : r ^ (k ^ m - 1 + 1) ≤ orderOf (z M) :=
      Nat.le_of_dvd hordMpos hM
    have horder_le : orderOf (z M) ≤ k ^ m - 1 :=
      orderOf_le_of_pow_eq_one ht (hroot M)
    have hpow_le_t : r ^ (k ^ m - 1 + 1) ≤ k ^ m - 1 :=
      le_trans hpow_le horder_le
    have hbig : k ^ m - 1 < r ^ (k ^ m - 1 + 1) := by
      exact lt_trans (Nat.lt_succ_self (k ^ m - 1)) (Nat.lt_pow_self hr.two_le)
    exact (not_lt_of_ge hpow_le_t) hbig
  · intro hz1
    refine ⟨1, Nat.one_pos, ?_⟩
    rw [hz1]
    simp [Function.IsPeriodicPt, Function.IsFixedPt]

end Rollout_p1494_p_adic_solenoid_only_periodic_point

#check_dependency_graph "Rollout_p1494_p_adic_solenoid_only_periodic_point.p_adic_solenoid_only_periodic_point" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(∃ m, 0 < m ∧ Function.IsPeriodicPt (fun w n => w n ^ k) m z) ↔ z = fun x => 1\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hP_recurrent\",\"statement\":\"∀ (q : ℕ), Nat.Prime q → ∀ (N : ℕ), ∃ n, N ≤ n ∧ P n = q\"},{\"name\":\"hk\",\"statement\":\"2 ≤ k\"},{\"name\":\"hz\",\"statement\":\"(∀ (n : ℕ), ‖z n‖ = 1) ∧ ∀ (n : ℕ), z n = z (n + 1) ^ P n\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1494_p_adic_solenoid_only_periodic_point\",\"reconstructedProofSha256\":\"5777737a5a34723c7fc4050338be996e114afef9bbaa06f1900d5a99256822a4\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1494_p_adic_solenoid_only_periodic_point.p_adic_solenoid_only_periodic_point\",\"topologySha256\":\"3f89eab81a87f5fb87faadc8e5b9321d877ac94dd5afae1efdb5824852a46a7d\"}"

namespace Rollout_p1499_countablytight_iff_prod_firstcountable

-- graph_id: p1499_countablytight_iff_prod_firstcountable
-- topology_sha256: 6d791668e76419bbfe9379e31a02f72cf68e3d1b1e9e38d859c818bd9a9bb10a
/- accepted add_to_file helper 1 -/
lemma countablyTight_prod_firstCountable
    {X : Type u} [TopologicalSpace X]
    (hX : ∀ (A : Set X) (x : X), x ∈ closure A →
      ∃ B : Set X, B ⊆ A ∧ B.Countable ∧ x ∈ closure B)
    {Y : Type v} [TopologicalSpace Y] [FirstCountableTopology Y] :
    ∀ (A : Set (X × Y)) (p : X × Y), p ∈ closure A →
      ∃ B : Set (X × Y), B ⊆ A ∧ B.Countable ∧ p ∈ closure B := by
  intro A p hp
  obtain ⟨V, hV⟩ := (Filter.isCountablyGenerated_iff_exists_antitone_basis.mp
    (FirstCountableTopology.nhds_generated_countable p.2))
  let C : ℕ → Set X := fun n => Prod.fst '' (A ∩ (Set.univ ×ˢ V n))
  have hVn : ∀ n, V n ∈ nhds p.2 := by
    intro n
    exact hV.mem_iff.mpr ⟨n, subset_rfl⟩
  have hpC : ∀ n, p.1 ∈ closure (C n) := by
    intro n
    rw [mem_closure_iff_nhds]
    intro U hU
    have hprod : U ×ˢ V n ∈ nhds p := by
      rw [mem_nhds_prod_iff]
      exact ⟨U, hU, V n, hVn n, subset_rfl⟩
    obtain ⟨q, hqprod, hqA⟩ := (mem_closure_iff_nhds.mp hp) (U ×ˢ V n) hprod
    rcases hqprod with ⟨hqU, hqV⟩
    refine ⟨q.1, hqU, ?_⟩
    exact ⟨q, ⟨hqA, ⟨trivial, hqV⟩⟩, rfl⟩
  choose BX hBXsub hBXcount hpBX using fun n => hX (C n) p.1 (hpC n)
  have hchoose : ∀ n, ∀ x : BX n, ∃ q : X × Y, q ∈ A ∧ q.2 ∈ V n ∧ q.1 = x.1 := by
    intro n x
    have hxC : (x : X) ∈ C n := hBXsub n x.2
    rcases hxC with ⟨q, hq, hq1⟩
    rcases hq with ⟨hqA, hqprod⟩
    rcases hqprod with ⟨-, hqV⟩
    exact ⟨q, hqA, hqV, hq1⟩
  choose f hfA hfV hf1 using hchoose
  let D : ℕ → Set (X × Y) := fun n => Set.range (f n)
  let Bset : Set (X × Y) := ⋃ n, D n
  refine ⟨Bset, ?_, ?_, ?_⟩
  · intro q hq
    rw [Set.mem_iUnion] at hq
    rcases hq with ⟨n, hn⟩
    rcases hn with ⟨x, rfl⟩
    exact hfA n x
  · have hDcount : ∀ n, (D n).Countable := by
      intro n
      haveI : Countable (BX n) := (hBXcount n).to_subtype
      exact Set.countable_range (f n)
    exact Set.countable_iUnion hDcount
  · rw [mem_closure_iff_nhds]
    intro W hW
    obtain ⟨U, hU, T, hT, hUT⟩ := mem_nhds_prod_iff.mp hW
    obtain ⟨n, hnVT⟩ := hV.mem_iff.mp hT
    obtain ⟨z, hzU, hzB⟩ := (mem_closure_iff_nhds.mp (hpBX n)) U hU
    refine ⟨f n ⟨z, hzB⟩, hUT ?_, ?_⟩
    · constructor
      · rw [hf1 n ⟨z, hzB⟩]
        exact hzU
      · exact hnVT (hfV n ⟨z, hzB⟩)
    · rw [Set.mem_iUnion]
      exact ⟨n, ⟨⟨z, hzB⟩, rfl⟩⟩

/- verified submission -/
theorem countablyTight_iff_prod_firstCountable {X : Type u} [TopologicalSpace X] :
    (∀ (A : Set X) (x : X), x ∈ closure A →
      ∃ B : Set X, B ⊆ A ∧ B.Countable ∧ x ∈ closure B) ↔
      ∀ (Y : Type v) [TopologicalSpace Y] [FirstCountableTopology Y],
        ∀ (A : Set (X × Y)) (p : X × Y), p ∈ closure A →
          ∃ B : Set (X × Y), B ⊆ A ∧ B.Countable ∧ p ∈ closure B := by
  constructor
  · intro hX Y _ _
    exact countablyTight_prod_firstCountable hX
  · intro hprod A x hx
    let Z : Type v := ULift.{v} PUnit
    let h : X × Z ≃ₜ X := Homeomorph.prodUnique X Z
    have hp : h.symm x ∈ closure (⇑h ⁻¹' A) := by
      have hmem : h.symm x ∈ ⇑h ⁻¹' closure A := by
        simpa using hx
      rwa [h.preimage_closure A] at hmem
    obtain ⟨B0, hB0A, hB0count, hB0cl⟩ := hprod Z (⇑h ⁻¹' A) (h.symm x) hp
    refine ⟨⇑h '' B0, ?_, hB0count.image ⇑h, ?_⟩
    · intro z hz
      rcases hz with ⟨q, hqB0, rfl⟩
      exact hB0A hqB0
    · have hxcl : h (h.symm x) ∈ closure (⇑h '' B0) := by
        rw [← h.image_closure B0]
        exact ⟨h.symm x, hB0cl, rfl⟩
      simpa using hxcl

end Rollout_p1499_countablytight_iff_prod_firstcountable

#check_dependency_graph "Rollout_p1499_countablytight_iff_prod_firstcountable.countablyTight_iff_prod_firstCountable" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(∀ (A : Set X), ∀ x ∈ closure A, ∃ B ⊆ A, B.Countable ∧ x ∈ closure B) ↔ ∀ (Y : Type v) [inst : TopologicalSpace Y] [FirstCountableTopology Y] (A : Set (X × Y)), ∀ p ∈ closure A, ∃ B ⊆ A, B.Countable ∧ p ∈ closure B\"},\"graphEdgeId\":\"h_goal\",\"premises\":[],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1499_countablytight_iff_prod_firstcountable\",\"reconstructedProofSha256\":\"9758ee59b088a34d5fae47675ab257a7179614cc5e931f5eda41c99d0c62f89d\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1499_countablytight_iff_prod_firstcountable.countablyTight_iff_prod_firstCountable\",\"topologySha256\":\"6d791668e76419bbfe9379e31a02f72cf68e3d1b1e9e38d859c818bd9a9bb10a\"}"

namespace Rollout_p1521_orbit_contained_free_action_restrict_measu

-- graph_id: p1521_orbit_contained_free_action_restrict_measu
-- topology_sha256: 471b6781f1c3079dd6b581fa595b17e813a968fe878903ea9c3212fb04a978f3
/- verified submission -/

open scoped Pointwise

lemma smul_eq_of_smul_eq_smul_of_stabilizer_bot
    {G X : Type*} [Group G] [MulAction G X]
    (hfree : ∀ x : X, MulAction.stabilizer G x = ⊥)
    {x : X} {a b : G} (h : a • x = b • x) : a = b := by
  have hmem : b⁻¹ * a ∈ MulAction.stabilizer G x := by
    rw [MulAction.mem_stabilizer_iff]
    calc
      (b⁻¹ * a) • x = b⁻¹ • (a • x) := by simp [mul_smul]
      _ = b⁻¹ • (b • x) := by rw [h]
      _ = x := by simp
  rw [hfree x] at hmem
  have hone : b⁻¹ * a = 1 := Subgroup.mem_bot.mp hmem
  exact (inv_mul_eq_one.mp hone).symm

theorem orbit_contained_free_action_restrict_measure_preserving
    {Γ Δ Y : Type*} [Group Γ] [Group Δ] [Countable Γ] [Countable Δ]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    [MulAction Γ Y] [MulAction Δ Y]
    [MeasurableConstSMul Γ Y] [MeasurableConstSMul Δ Y]
    (hc_free : ∀ y : Y, MulAction.stabilizer Γ y = ⊥)
    (hd_free : ∀ y : Y, MulAction.stabilizer Δ y = ⊥)
    (horbit : ∀ (δ : Δ) (y : Y), ∃ γ : Γ, δ • y = γ • y)
    (A : Set Y) (hA_meas : MeasurableSet A)
    (hA_inv : ∀ δ : Δ, (fun y : Y => δ • y) '' A = A)
    (μ : MeasureTheory.Measure Y) [MeasureTheory.IsProbabilityMeasure μ]
    [MeasureTheory.SMulInvariantMeasure Γ Y μ]
    (hμA : μ A = 1) :
    ∀ (δ : Δ) (B : Set Y), MeasurableSet B → B ⊆ A →
      μ ((fun y : Y => δ • y) '' B) = μ B := by
  letI := upgradeStandardBorel Y
  intro δ B hB hBA
  let S : Γ → Set Y := fun γ ↦ {y | δ • y = γ • y}
  have hS_meas : ∀ γ : Γ, MeasurableSet (S γ) := by
    intro γ
    exact measurableSet_eq_fun
      (MeasurableConstSMul.measurable_const_smul δ)
      (MeasurableConstSMul.measurable_const_smul γ)
  have hB_eq : B = ⋃ γ : Γ, B ∩ S γ := by
    ext y
    constructor
    · intro hy
      rcases horbit δ y with ⟨γ, hγ⟩
      exact Set.mem_iUnion.2 ⟨γ, hy, hγ⟩
    · intro hy
      rcases Set.mem_iUnion.1 hy with ⟨γ, hy⟩
      exact hy.1
  have hC_meas : ∀ γ : Γ, MeasurableSet (B ∩ S γ) := by
    intro γ
    exact hB.inter (hS_meas γ)
  have hC_disjoint : Pairwise (Function.onFun Disjoint fun γ : Γ ↦ B ∩ S γ) := by
    intro γ₁ γ₂ hne
    rw [Function.onFun, Set.disjoint_left]
    intro y hy₁ hy₂
    apply hne
    exact smul_eq_of_smul_eq_smul_of_stabilizer_bot hc_free
      (hy₁.2.symm.trans hy₂.2)
  have himage_eq :
      (fun y : Y ↦ δ • y) '' B = ⋃ γ : Γ, γ • (B ∩ S γ) := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hyB, hyx⟩
      rcases horbit δ y with ⟨γ, hγ⟩
      apply Set.mem_iUnion.2
      use γ
      rw [Set.mem_smul_set]
      exact ⟨y, ⟨hyB, hγ⟩, hγ ▸ hyx⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨γ, hxγ⟩
      rw [Set.mem_smul_set] at hxγ
      rcases hxγ with ⟨y, hy, hyx⟩
      exact ⟨y, hy.1, hy.2.trans hyx⟩
  have hT_meas : ∀ γ : Γ, MeasurableSet (γ • (B ∩ S γ)) := by
    intro γ
    exact (hC_meas γ).const_smul γ
  have hT_disjoint :
      Pairwise (Function.onFun Disjoint fun γ : Γ ↦ γ • (B ∩ S γ)) := by
    intro γ₁ γ₂ hne
    rw [Function.onFun, Set.disjoint_left]
    intro x hx₁ hx₂
    rw [Set.mem_smul_set] at hx₁ hx₂
    rcases hx₁ with ⟨y₁, hy₁, hx₁⟩
    rcases hx₂ with ⟨y₂, hy₂, hx₂⟩
    have hy : y₁ = y₂ := by
      apply smul_left_cancel δ
      calc
        δ • y₁ = γ₁ • y₁ := hy₁.2
        _ = x := hx₁
        _ = γ₂ • y₂ := hx₂.symm
        _ = δ • y₂ := hy₂.2.symm
    apply hne
    subst y₂
    exact smul_eq_of_smul_eq_smul_of_stabilizer_bot hc_free
      (by
        calc
          γ₁ • y₁ = x := hx₁
          _ = γ₂ • y₁ := hx₂.symm)
  calc
    μ ((fun y : Y ↦ δ • y) '' B)
        = μ (⋃ γ : Γ, γ • (B ∩ S γ)) := by rw [himage_eq]
    _ = ∑' γ : Γ, μ (γ • (B ∩ S γ)) :=
        MeasureTheory.measure_iUnion hT_disjoint hT_meas
    _ = ∑' γ : Γ, μ (B ∩ S γ) := by
        simp [MeasureTheory.measure_smul]
    _ = μ (⋃ γ : Γ, B ∩ S γ) :=
        (MeasureTheory.measure_iUnion hC_disjoint hC_meas).symm
    _ = μ B := by rw [← hB_eq]

end Rollout_p1521_orbit_contained_free_action_restrict_measu

#check_dependency_graph "Rollout_p1521_orbit_contained_free_action_restrict_measu.orbit_contained_free_action_restrict_measure_preserving" against "{\"edges\":[{\"conclusion\":{\"name\":\"hS_meas\",\"statement\":\"∀ (γ : Γ), MeasurableSet (S γ)\"},\"graphEdgeId\":\"h_001_hs_meas\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"StandardBorelSpace Y\"},{\"name\":\"<generated-instance>\",\"statement\":\"MeasurableConstSMul Γ Y\"},{\"name\":\"<generated-instance>\",\"statement\":\"MeasurableConstSMul Δ Y\"}],\"rawEdgeId\":\"telescope_28\"},{\"conclusion\":{\"name\":\"hB_eq\",\"statement\":\"B = ⋃ γ, B ∩ S γ\"},\"graphEdgeId\":\"h_002_hb_eq\",\"premises\":[{\"name\":\"horbit\",\"statement\":\"∀ (δ : Δ) (y : Y), ∃ γ, δ • y = γ • y\"}],\"rawEdgeId\":\"telescope_29\"},{\"conclusion\":{\"name\":\"hC_disjoint\",\"statement\":\"Pairwise (Function.onFun Disjoint fun γ => B ∩ S γ)\"},\"graphEdgeId\":\"h_004_hc_disjoint\",\"premises\":[{\"name\":\"hc_free\",\"statement\":\"∀ (y : Y), MulAction.stabilizer Γ y = ⊥\"}],\"rawEdgeId\":\"telescope_31\"},{\"conclusion\":{\"name\":\"himage_eq\",\"statement\":\"(fun y => δ • y) '' B = ⋃ γ, γ • (B ∩ S γ)\"},\"graphEdgeId\":\"h_005_himage_eq\",\"premises\":[{\"name\":\"horbit\",\"statement\":\"∀ (δ : Δ) (y : Y), ∃ γ, δ • y = γ • y\"}],\"rawEdgeId\":\"telescope_32\"},{\"conclusion\":{\"name\":\"hT_disjoint\",\"statement\":\"Pairwise (Function.onFun Disjoint fun γ => γ • (B ∩ S γ))\"},\"graphEdgeId\":\"h_007_ht_disjoint\",\"premises\":[{\"name\":\"hc_free\",\"statement\":\"∀ (y : Y), MulAction.stabilizer Γ y = ⊥\"}],\"rawEdgeId\":\"telescope_34\"},{\"conclusion\":{\"name\":\"hC_meas\",\"statement\":\"∀ (γ : Γ), MeasurableSet (B ∩ S γ)\"},\"graphEdgeId\":\"h_003_hc_meas\",\"premises\":[{\"name\":\"hB\",\"statement\":\"MeasurableSet B\"},{\"name\":\"hS_meas\",\"statement\":\"∀ (γ : Γ), MeasurableSet (S γ)\"}],\"rawEdgeId\":\"telescope_30\"},{\"conclusion\":{\"name\":\"hT_meas\",\"statement\":\"∀ (γ : Γ), MeasurableSet (γ • (B ∩ S γ))\"},\"graphEdgeId\":\"h_006_ht_meas\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"MeasurableConstSMul Γ Y\"},{\"name\":\"hC_meas\",\"statement\":\"∀ (γ : Γ), MeasurableSet (B ∩ S γ)\"}],\"rawEdgeId\":\"telescope_33\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"μ ((fun y => δ • y) '' B) = μ B\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"Countable Γ\"},{\"name\":\"<generated-instance>\",\"statement\":\"MeasureTheory.SMulInvariantMeasure Γ Y μ\"},{\"name\":\"hB_eq\",\"statement\":\"B = ⋃ γ, B ∩ S γ\"},{\"name\":\"hC_meas\",\"statement\":\"∀ (γ : Γ), MeasurableSet (B ∩ S γ)\"},{\"name\":\"hC_disjoint\",\"statement\":\"Pairwise (Function.onFun Disjoint fun γ => B ∩ S γ)\"},{\"name\":\"himage_eq\",\"statement\":\"(fun y => δ • y) '' B = ⋃ γ, γ • (B ∩ S γ)\"},{\"name\":\"hT_meas\",\"statement\":\"∀ (γ : Γ), MeasurableSet (γ • (B ∩ S γ))\"},{\"name\":\"hT_disjoint\",\"statement\":\"Pairwise (Function.onFun Disjoint fun γ => γ • (B ∩ S γ))\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1521_orbit_contained_free_action_restrict_measu\",\"reconstructedProofSha256\":\"5537b82aff44aef04ef1a6e1227e009fee9631f7a7fe9c2ed0f3aea63119fee4\",\"selectedEdgeCount\":8,\"theoremName\":\"Rollout_p1521_orbit_contained_free_action_restrict_measu.orbit_contained_free_action_restrict_measure_preserving\",\"topologySha256\":\"471b6781f1c3079dd6b581fa595b17e813a968fe878903ea9c3212fb04a978f3\"}"

namespace Rollout_p1530_inverse_along_mem_bicommutant

-- graph_id: p1530_inverse_along_mem_bicommutant
-- topology_sha256: b46fcaa3152d6c46b1095bf53141771c7e60801a5c82e999fd8954042fb790bd
/- verified submission -/
theorem inverse_along_mem_bicommutant {S : Type*} [Semigroup S] {a d b : S}
    (hbad : b * a * d = d) (hdab : d * a * b = d)
    (hbd : ∃ x y : S, b = d * x ∧ b = y * d) :
    ∀ c : S, c * a = a * c → c * d = d * c → c * b = b * c := by
  rcases hbd with ⟨x, y, hbx, hby⟩
  intro c hca hcd
  have hyad : y * d * a * d = d := by
    simpa [hby] using hbad
  have hdadx : d * a * d * x = d := by
    simpa [hbx, mul_assoc] using hdab
  calc
    c * b = d * c * x := by
      calc
        c * b = c * (d * x) := by rw [hbx]
        _ = c * d * x := by rw [mul_assoc]
        _ = d * c * x := by rw [hcd]
    _ = y * d * a * d * c * x := by
      rw [hyad]
    _ = y * d * a * c * d * x := by
      have h : y * d * a * (d * c) * x = y * d * a * (c * d) * x := by
        rw [hcd]
      simpa [mul_assoc] using h
    _ = y * d * c * a * d * x := by
      have h : y * d * (a * c) * d * x = y * d * (c * a) * d * x := by
        rw [← hca]
      simpa [mul_assoc] using h
    _ = y * c * d * a * d * x := by
      have h : y * (d * c) * a * d * x = y * (c * d) * a * d * x := by
        rw [hcd]
      simpa [mul_assoc] using h
    _ = y * c * d := by
      have h : y * c * (d * a * d * x) = y * c * d := by
        rw [hdadx]
      simpa [mul_assoc] using h
    _ = y * d * c := by
      rw [mul_assoc, hcd, ← mul_assoc]
    _ = b * c := by
      rw [← hby]

end Rollout_p1530_inverse_along_mem_bicommutant

#check_dependency_graph "Rollout_p1530_inverse_along_mem_bicommutant.inverse_along_mem_bicommutant" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∀ (c : S), c * a = a * c → c * d = d * c → c * b = b * c\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hbad\",\"statement\":\"b * a * d = d\"},{\"name\":\"hdab\",\"statement\":\"d * a * b = d\"},{\"name\":\"hbd\",\"statement\":\"∃ x y, b = d * x ∧ b = y * d\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1530_inverse_along_mem_bicommutant\",\"reconstructedProofSha256\":\"d0b7ac0bd21f6d7f9cc1eab953c262573b5c36f6ca7507ec968bf8b07254cd45\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1530_inverse_along_mem_bicommutant.inverse_along_mem_bicommutant\",\"topologySha256\":\"b46fcaa3152d6c46b1095bf53141771c7e60801a5c82e999fd8954042fb790bd\"}"

namespace Rollout_p1552_index_two_infinite_cyclic_classification

-- graph_id: p1552_index_two_infinite_cyclic_classification
-- topology_sha256: b970c05a80a45b5cb42281387b00efc48d0120f20aec20b1b700ceda483f090b
/- accepted add_to_file helper 1 -/

open Subgroup

/-- Two-sided normal forms for a group generated by an involution and a conjugated generator. -/
def twoSidedNF {G : Type*} [Group G] (a b : G) : Set G :=
  {x | ∃ c : Bool, ∃ k : ℤ, x = if c then a * b ^ k else b ^ k}

lemma one_mem_twoSidedNF {G : Type*} [Group G] (a b : G) :
    (1 : G) ∈ twoSidedNF a b := by
  refine ⟨false, 0, ?_⟩
  simp

lemma generator_left_mem_twoSidedNF {G : Type*} [Group G] (a b : G) :
    a ∈ twoSidedNF a b := by
  refine ⟨true, 0, ?_⟩
  simp

lemma generator_right_mem_twoSidedNF {G : Type*} [Group G] (a b : G) :
    b ∈ twoSidedNF a b := by
  refine ⟨false, 1, ?_⟩
  simp

lemma zpow_conjugate_eq_neg {G : Type*} [Group G] {a b : G}
    (hconj : a * b * a⁻¹ = b⁻¹) (k : ℤ) :
    a * b ^ k = b ^ (-k) * a := by
  have h : (a * b * a⁻¹) ^ k = (b⁻¹) ^ k := congrArg (fun x => x ^ k) hconj
  rw [conj_zpow] at h
  calc
    a * b ^ k = (a * b ^ k * a⁻¹) * a := by group
    _ = (b⁻¹) ^ k * a := by rw [h]
    _ = b ^ (-k) * a := by rw [inv_zpow']

lemma zpow_mul_eq_left {G : Type*} [Group G] {a b : G}
    (hconj : a * b * a⁻¹ = b⁻¹) (k : ℤ) :
    b ^ k * a = a * b ^ (-k) := by
  simpa using (zpow_conjugate_eq_neg hconj (-k)).symm

/- accepted add_to_file helper 2 -/
lemma twoSidedNF_mul_of_inversion {G : Type*} [Group G] {a b : G}
    (hconj : a * b * a⁻¹ = b⁻¹) (hsq : a * a = 1)
    {x y : G} (hx : x ∈ twoSidedNF a b) (hy : y ∈ twoSidedNF a b) :
    x * y ∈ twoSidedNF a b := by
  rcases hx with ⟨cx, k, rfl⟩
  rcases hy with ⟨cy, l, rfl⟩
  cases cx <;> cases cy
  · refine ⟨false, k + l, ?_⟩
    simp [zpow_add]
  · refine ⟨true, l - k, ?_⟩
    simp
    calc
      b ^ k * (a * b ^ l) = (b ^ k * a) * b ^ l := by group
      _ = (a * b ^ (-k)) * b ^ l := by rw [zpow_mul_eq_left hconj]
      _ = a * b ^ (l - k) := by
        rw [mul_assoc, ← zpow_add]
        ring_nf
  · refine ⟨true, k + l, ?_⟩
    simp
    rw [mul_assoc, ← zpow_add]
  · refine ⟨false, l - k, ?_⟩
    simp
    calc
      (a * b ^ k) * (a * b ^ l) = ((a * b ^ k) * a) * b ^ l := by group
      _ = ((b ^ (-k) * a) * a) * b ^ l := by rw [zpow_conjugate_eq_neg hconj]
      _ = (b ^ (-k) * (a * a)) * b ^ l := by group
      _ = b ^ (l - k) := by
        rw [hsq, mul_one, ← zpow_add]
        ring_nf

lemma twoSidedNF_inv_of_inversion {G : Type*} [Group G] {a b : G}
    (hconj : a * b * a⁻¹ = b⁻¹) (hsq : a * a = 1)
    {x : G} (hx : x ∈ twoSidedNF a b) :
    x⁻¹ ∈ twoSidedNF a b := by
  rcases hx with ⟨c, k, rfl⟩
  cases c
  · refine ⟨false, -k, ?_⟩
    simp [zpow_neg]
  · have hainv : a⁻¹ = a := by
      apply inv_eq_of_mul_eq_one_left hsq
    refine ⟨true, k, ?_⟩
    simp only [↓reduceIte]
    calc
      (a * b ^ k)⁻¹ = b ^ (-k) * a := by
        rw [mul_inv_rev, hainv, zpow_neg]
      _ = a * b ^ k := by
        rw [zpow_mul_eq_left hconj (-k), neg_neg]

/- accepted add_to_file helper 3 -/
lemma twoSidedNF_eq_univ_of_inversion {G : Type*} [Group G] (a b : G)
    (hconj : a * b * a⁻¹ = b⁻¹) (hsq : a * a = 1)
    (hgen : Subgroup.closure {a, b} = ⊤) :
    twoSidedNF a b = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  have hx : x ∈ Subgroup.closure {a, b} := by simp [hgen]
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      simp at hy
      rcases hy with rfl | rfl
      · exact generator_left_mem_twoSidedNF y b
      · exact generator_right_mem_twoSidedNF a y
  | one => exact one_mem_twoSidedNF a b
  | mul y z hy hz ihy ihz =>
      exact twoSidedNF_mul_of_inversion hconj hsq ihy ihz
  | inv y hy ihy =>
      exact twoSidedNF_inv_of_inversion hconj hsq ihy

/- accepted add_to_file helper 4 -/
lemma zpow_commute_left {G : Type*} [Group G] {a b : G}
    (hcomm : a * b = b * a) (k : ℤ) :
    b ^ k * a = a * b ^ k :=
  (Commute.zpow_right hcomm k).symm.eq

/- accepted add_to_file helper 5 -/
lemma twoSidedNF_mul_of_commute_square {G : Type*} [Group G] {a b : G}
    (hcomm : a * b = b * a) {n : ℤ} (hsq : a * a = b ^ (2 * n))
    {x y : G} (hx : x ∈ twoSidedNF a b) (hy : y ∈ twoSidedNF a b) :
    x * y ∈ twoSidedNF a b := by
  rcases hx with ⟨cx, k, rfl⟩
  rcases hy with ⟨cy, l, rfl⟩
  cases cx <;> cases cy
  · refine ⟨false, k + l, ?_⟩
    simp [zpow_add]
  · refine ⟨true, k + l, ?_⟩
    simp
    calc
      b ^ k * (a * b ^ l) = (b ^ k * a) * b ^ l := by group
      _ = (a * b ^ k) * b ^ l := by rw [zpow_commute_left hcomm]
      _ = a * b ^ (k + l) := by
        rw [mul_assoc, ← zpow_add]
  · refine ⟨true, k + l, ?_⟩
    simp
    rw [mul_assoc, ← zpow_add]
  · refine ⟨false, 2 * n + k + l, ?_⟩
    simp
    calc
      (a * b ^ k) * (a * b ^ l) = (a * (b ^ k * a)) * b ^ l := by group
      _ = (a * (a * b ^ k)) * b ^ l := by rw [zpow_commute_left hcomm]
      _ = ((a * a) * b ^ k) * b ^ l := by group
      _ = b ^ (2 * n + k + l) := by
        rw [hsq, ← zpow_add, ← zpow_add]

/- accepted add_to_file helper 6 -/
lemma twoSidedNF_inv_of_commute_square {G : Type*} [Group G] {a b : G}
    (hcomm : a * b = b * a) {n : ℤ} (hsq : a * a = b ^ (2 * n))
    {x : G} (hx : x ∈ twoSidedNF a b) :
    x⁻¹ ∈ twoSidedNF a b := by
  rcases hx with ⟨c, k, rfl⟩
  cases c
  · refine ⟨false, -k, ?_⟩
    simp [zpow_neg]
  · refine ⟨true, -k - 2 * n, ?_⟩
    simp only [↓reduceIte]
    apply inv_eq_of_mul_eq_one_left
    calc
      (a * b ^ (-k - 2 * n)) * (a * b ^ k)
          = (a * (b ^ (-k - 2 * n) * a)) * b ^ k := by group
      _ = (a * (a * b ^ (-k - 2 * n))) * b ^ k := by
        rw [zpow_commute_left hcomm]
      _ = ((a * a) * b ^ (-k - 2 * n)) * b ^ k := by group
      _ = 1 := by
        rw [hsq, ← zpow_add, ← zpow_add]
        have hzero : 2 * n + (-k - 2 * n) + k = 0 := by ring
        rw [hzero]
        simp

lemma twoSidedNF_eq_univ_of_commute_square {G : Type*} [Group G] (a b : G)
    (hcomm : a * b = b * a) {n : ℤ} (hsq : a * a = b ^ (2 * n))
    (hgen : Subgroup.closure {a, b} = ⊤) :
    twoSidedNF a b = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro x
  have hx : x ∈ Subgroup.closure {a, b} := by simp [hgen]
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
      simp at hy
      rcases hy with rfl | rfl
      · exact generator_left_mem_twoSidedNF y b
      · exact generator_right_mem_twoSidedNF a y
  | one => exact one_mem_twoSidedNF a b
  | mul y z hy hz ihy ihz =>
      exact twoSidedNF_mul_of_commute_square hcomm hsq ihy ihz
  | inv y hy ihy =>
      exact twoSidedNF_inv_of_commute_square hcomm hsq ihy

/- accepted add_to_file helper 7 -/
noncomputable def mulEquivOfTwoSidedNF {P K : Type*} [Group P] [Group K]
    (f : P →* K) (a b : P) (v t : K)
    (fa : f a = v) (fb : f b = t)
    (hnf : twoSidedNF a b = Set.univ)
    (hgenK : Subgroup.closure {v, t} = ⊤)
    (hvH : v ∉ Subgroup.zpowers t)
    (htinj : Function.Injective fun k : ℤ => t ^ k) :
    P ≃* K := by
  have hsubset : ({v, t} : Set K) ⊆ f.range := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl
    · exact ⟨a, fa⟩
    · exact ⟨b, fb⟩
  have hle : Subgroup.closure {v, t} ≤ f.range := (Subgroup.closure_le _).mpr hsubset
  have hrange : f.range = ⊤ := by
    apply top_unique
    rwa [hgenK] at hle
  have hsurj : Function.Surjective f := MonoidHom.range_eq_top.mp hrange
  have hker : f.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro p hp
    rw [MonoidHom.mem_ker] at hp
    have hpnf : p ∈ twoSidedNF a b := by
      rw [hnf]
      trivial
    rcases hpnf with ⟨c, k, rfl⟩
    cases c
    · have ht : t ^ k = 1 := by
        simpa [fb] using hp
      have hk : k = 0 := by
        apply htinj
        simpa using ht
      simp [hk]
    · have hvt : v * t ^ k = 1 := by
        simpa [fa, fb] using hp
      have hv_eq : v = t ^ (-k) := by
        calc
          v = (v * t ^ k) * (t ^ k)⁻¹ := by group
          _ = (t ^ k)⁻¹ := by rw [hvt, one_mul]
          _ = t ^ (-k) := by rw [zpow_neg]
      have hvmem : v ∈ Subgroup.zpowers t := by
        rw [Subgroup.mem_zpowers_iff]
        exact ⟨-k, hv_eq.symm⟩
      exact False.elim (hvH hvmem)
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
  exact MulEquiv.ofBijective f ⟨hinj, hsurj⟩

/- accepted add_to_file helper 8 -/
def classificationCommRels (n : ℤ) : Set (FreeGroup (Fin 2)) :=
  {FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) *
      (FreeGroup.of (0 : Fin 2))⁻¹ * (FreeGroup.of (1 : Fin 2))⁻¹,
    (FreeGroup.of (0 : Fin 2)) ^ (2 : ℕ) *
      ((FreeGroup.of (1 : Fin 2)) ^ (2 * n))⁻¹}

def classificationInvRels : Set (FreeGroup (Fin 2)) :=
  {FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) *
      (FreeGroup.of (0 : Fin 2))⁻¹ * FreeGroup.of (1 : Fin 2),
    (FreeGroup.of (0 : Fin 2)) ^ (2 : ℕ)}

/- accepted add_to_file helper 9 -/
lemma mem_zpowers_coe_generator {G : Type*} [Group G] (u : G)
    (y : Subgroup.zpowers u) :
    y ∈ Subgroup.zpowers (⟨u, Subgroup.mem_zpowers u⟩ : Subgroup.zpowers u) := by
  rcases y with ⟨x, hx⟩
  rw [Subgroup.mem_zpowers_iff] at hx ⊢
  rcases hx with ⟨q, rfl⟩
  refine ⟨q, ?_⟩
  ext
  simp

noncomputable def zmodTwoEquivZpowers {G : Type*} [Group G] (u : G)
    (hu : orderOf u = 2) :
    Multiplicative (ZMod 2) ≃* Subgroup.zpowers u := by
  refine zmodMulEquivOfGenerator (g := ⟨u, Subgroup.mem_zpowers u⟩) ?_ ?_
  · intro y
    exact mem_zpowers_coe_generator u y
  · rw [Nat.card_zpowers]
    change orderOf u = 2
    exact hu

/- accepted add_to_file helper 10 -/
noncomputable def zmodTwoHomOfOrderTwo {G : Type*} [Group G] (u : G)
    (hu : orderOf u = 2) : Multiplicative (ZMod 2) →* G :=
  (Subgroup.zpowers u).subtype.comp (zmodTwoEquivZpowers u hu).toMonoidHom

lemma zmodTwoHomOfOrderTwo_apply_one {G : Type*} [Group G] (u : G)
    (hu : orderOf u = 2) :
    zmodTwoHomOfOrderTwo u hu (Multiplicative.ofAdd (1 : ZMod 2)) = u := by
  simp [zmodTwoHomOfOrderTwo, zmodTwoEquivZpowers]

/- accepted add_to_file helper 11 -/
lemma mem_zpowers_multiplicative_int_one (z : Multiplicative ℤ) :
    z ∈ Subgroup.zpowers (Multiplicative.ofAdd (1 : ℤ)) := by
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨Multiplicative.toAdd z, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [Int.toAdd_zpow]
  simp

lemma mem_zpowers_multiplicative_zmod_two_one (c : Multiplicative (ZMod 2)) :
    c ∈ Subgroup.zpowers (Multiplicative.ofAdd (1 : ZMod 2)) := by
  rw [Subgroup.mem_zpowers_iff]
  fin_cases c
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

lemma closure_pair_product_int_zmod_two :
    Subgroup.closure
      ({(1, Multiplicative.ofAdd (1 : ZMod 2)),
        (Multiplicative.ofAdd (1 : ℤ), 1)} :
        Set (Multiplicative ℤ × Multiplicative (ZMod 2))) = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro x
  rcases x with ⟨z, c⟩
  have hz := mem_zpowers_multiplicative_int_one z
  have hc := mem_zpowers_multiplicative_zmod_two_one c
  rw [Subgroup.mem_zpowers_iff] at hz hc
  rcases hz with ⟨q, hq⟩
  rcases hc with ⟨w, hw⟩
  rw [← hq, ← hw]
  let a : Multiplicative ℤ × Multiplicative (ZMod 2) :=
    (1, Multiplicative.ofAdd (1 : ZMod 2))
  let b : Multiplicative ℤ × Multiplicative (ZMod 2) :=
    (Multiplicative.ofAdd (1 : ℤ), 1)
  have hprod : ((Multiplicative.ofAdd (1 : ℤ)) ^ q,
      (Multiplicative.ofAdd (1 : ZMod 2)) ^ w) = b ^ q * a ^ w := by
    ext <;> simp [a, b]
  rw [hprod]
  exact mul_mem
    (zpow_mem (Subgroup.subset_closure (by simp [a, b])) q)
    (zpow_mem (Subgroup.subset_closure (by simp [a, b])) w)

/- accepted add_to_file helper 12 -/
lemma not_isOfFinOrder_of_infinite_zpowers {G : Type*} [Group G] {t : G}
    (htinf : Infinite (Subgroup.zpowers t)) : ¬IsOfFinOrder t := by
  intro ht
  haveI : Infinite (Subgroup.zpowers t) := htinf
  haveI : Finite (Subgroup.zpowers t) := ht.finite_zpowers.to_subtype
  exact not_finite (Subgroup.zpowers t)

lemma zpow_injective_of_infinite_zpowers {G : Type*} [Group G] {t : G}
    (htinf : Infinite (Subgroup.zpowers t)) :
    Function.Injective fun k : ℤ => t ^ k :=
  injective_zpow_iff_not_isOfFinOrder.mpr
    (not_isOfFinOrder_of_infinite_zpowers htinf)

lemma not_mem_zpowers_of_closure_eq_top_index_two {G : Type*} [Group G] {v t : G}
    (hgen : Subgroup.closure {v, t} = ⊤)
    (hindex : (Subgroup.zpowers t).index = 2) :
    v ∉ Subgroup.zpowers t := by
  intro hv
  have hsubset : ({v, t} : Set G) ⊆ Subgroup.zpowers t := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl
    · exact hv
    · exact Subgroup.mem_zpowers x
  have hle : Subgroup.closure {v, t} ≤ Subgroup.zpowers t :=
    (Subgroup.closure_le _).mpr hsubset
  have htop : (⊤ : Subgroup G) ≤ Subgroup.zpowers t := by
    rwa [hgen] at hle
  have h_eq : Subgroup.zpowers t = ⊤ := top_unique htop
  have hindex1 : (Subgroup.zpowers t).index = 1 :=
    Subgroup.index_eq_one.mpr h_eq
  omega

/- accepted add_to_file helper 13 -/
lemma sq_mem_zpowers_of_index_two {G : Type*} [Group G] {v t : G}
    (hindex : (Subgroup.zpowers t).index = 2) :
    v * v ∈ Subgroup.zpowers t := by
  haveI : (Subgroup.zpowers t).Normal :=
    Subgroup.normal_of_index_eq_two hindex
  let H := Subgroup.zpowers t
  have hcard : Nat.card (G ⧸ H) = 2 := by
    rw [← Subgroup.index_eq_card, hindex]
  have hq : ((QuotientGroup.mk' H) v) ^ 2 = 1 := by
    have h := pow_card_eq_one' (x := (QuotientGroup.mk' H) v)
    rwa [hcard] at h
  have hq2 : (QuotientGroup.mk' H) (v ^ (2 : ℕ)) = 1 := by
    simpa using hq
  have hmem : v ^ (2 : ℕ) ∈ H := (QuotientGroup.eq_one_iff _).mp hq2
  simpa [sq] using hmem

/- accepted add_to_file helper 14 -/
lemma conjugation_cases_of_index_two {G : Type*} [Group G] {v t : G}
    (hindex : (Subgroup.zpowers t).index = 2)
    (htinj : Function.Injective fun k : ℤ => t ^ k) :
    v * t = t * v ∨ v * t * v⁻¹ = t⁻¹ := by
  haveI hnormal : (Subgroup.zpowers t).Normal :=
    Subgroup.normal_of_index_eq_two hindex
  have hmem1 : v * t * v⁻¹ ∈ Subgroup.zpowers t :=
    hnormal.conj_mem t (Subgroup.mem_zpowers t) v
  rw [Subgroup.mem_zpowers_iff] at hmem1
  rcases hmem1 with ⟨m, hm⟩
  have hconj : v * t * v⁻¹ = t ^ m := hm.symm
  have hmem2 : v⁻¹ * t * v ∈ Subgroup.zpowers t :=
    hnormal.conj_mem' t (Subgroup.mem_zpowers t) v
  rw [Subgroup.mem_zpowers_iff] at hmem2
  rcases hmem2 with ⟨l, hl⟩
  have hconji : v⁻¹ * t * v = t ^ l := hl.symm
  have hcycle : t = t ^ (l * m) := by
    calc
      t = v⁻¹ * (v * t * v⁻¹) * v := by group
      _ = v⁻¹ * t ^ m * v := by rw [hconj]
      _ = (v⁻¹ * t * v) ^ m := by
        have hz := (conj_zpow (a := v⁻¹) (b := t) (i := m)).symm
        simpa using hz
      _ = (t ^ l) ^ m := by rw [hconji]
      _ = t ^ (l * m) := (zpow_mul t l m).symm
  have hlm : l * m = 1 := by
    apply htinj
    calc
      t ^ (l * m) = t := hcycle.symm
      _ = t ^ (1 : ℤ) := by simp
  have hm_cases : m = 1 ∨ m = -1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hlm with hl1 | hlneg1
    · left
      simpa [hl1] using hlm
    · right
      have hnegm : -m = 1 := by
        simpa [hlneg1] using hlm
      omega
  rcases hm_cases with hm1 | hmneg1
  · left
    have hconj1 : v * t * v⁻¹ = t := by simpa [hm1] using hconj
    calc
      v * t = (v * t * v⁻¹) * v := by group
      _ = t * v := by rw [hconj1]
  · right
    simpa [hmneg1] using hconj

/- accepted add_to_file helper 15 -/
lemma no_torsion_of_commute_square_odd {K : Type*} [Group K] {v t : K} {s : ℤ}
    (hgen : Subgroup.closure {v, t} = ⊤)
    (hcomm : v * t = t * v)
    (hv2 : v * v = t ^ (2 * s + 1))
    (htinj : Function.Injective fun k : ℤ => t ^ k)
    (htors : ∃ x : K, x ≠ 1 ∧ IsOfFinOrder x) : False := by
  let w : K := v * t ^ (-s)
  have hw2 : w * w = t := by
    dsimp [w]
    calc
      (v * t ^ (-s)) * (v * t ^ (-s))
          = (v * (t ^ (-s) * v)) * t ^ (-s) := by group
      _ = (v * (v * t ^ (-s))) * t ^ (-s) := by
        rw [zpow_commute_left hcomm]
      _ = ((v * v) * t ^ (-s)) * t ^ (-s) := by group
      _ = t := by
        rw [hv2, ← zpow_add, ← zpow_add]
        have hone : 2 * s + 1 + -s + -s = 1 := by ring
        rw [hone]
        simp
  have ht_mem : t ∈ Subgroup.zpowers w := by
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨2, ?_⟩
    rw [← hw2, zpow_ofNat, pow_two]
  have hv_mem : v ∈ Subgroup.zpowers w := by
    rw [Subgroup.mem_zpowers_iff]
    refine ⟨1 + 2 * s, ?_⟩
    calc
      w ^ (1 + 2 * s) = w * w ^ (2 * s) := by rw [zpow_add]; simp
      _ = w * (w * w) ^ s := by
        rw [zpow_mul w 2 s, zpow_ofNat, pow_two]
      _ = w * t ^ s := by rw [hw2]
      _ = v := by
        dsimp [w]
        calc
          (v * t ^ (-s)) * t ^ s = v * (t ^ (-s) * t ^ s) := by group
          _ = v := by rw [← zpow_add]; simp
  have hsubset : ({v, t} : Set K) ⊆ Subgroup.zpowers w := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl
    · exact hv_mem
    · exact ht_mem
  have hle : Subgroup.closure {v, t} ≤ Subgroup.zpowers w :=
    (Subgroup.closure_le _).mpr hsubset
  have hall : ∀ x : K, x ∈ Subgroup.zpowers w := by
    intro x
    have htop : (⊤ : Subgroup K) ≤ Subgroup.zpowers w := by
      rwa [hgen] at hle
    exact htop trivial
  rcases htors with ⟨x, hxne, hxfin⟩
  have hxmem := hall x
  rw [Subgroup.mem_zpowers_iff] at hxmem
  rcases hxmem with ⟨q, hq⟩
  have hx2 : x * x = t ^ q := by
    calc
      x * x = w ^ q * w ^ q := by rw [hq]
      _ = w ^ (q + q) := by rw [← zpow_add]
      _ = w ^ (2 * q) := by ring_nf
      _ = (w * w) ^ q := by
        rw [zpow_mul w 2 q, zpow_ofNat, pow_two]
      _ = t ^ q := by rw [hw2]
  have htqfin : IsOfFinOrder (t ^ q) := by
    rw [← hx2, ← pow_two x]
    exact hxfin.pow
  rcases isOfFinOrder_iff_pow_eq_one.mp htqfin with ⟨N, hNpos, hN⟩
  have hpow : t ^ (q * (N : ℤ)) = 1 := by
    calc
      t ^ (q * (N : ℤ)) = (t ^ q) ^ (N : ℤ) := zpow_mul t q N
      _ = 1 := by simpa using hN
  have hqN : q * (N : ℤ) = 0 := by
    apply htinj
    simpa using hpow
  have hNne : (N : ℤ) ≠ 0 := by omega
  have hq0 : q = 0 := by
    rcases mul_eq_zero.mp hqN with hq0 | hN0
    · exact hq0
    · exact False.elim (hNne hN0)
  apply hxne
  rw [← hq, hq0]
  simp

/- accepted add_to_file helper 16 -/
lemma square_exponent_even_of_torsion {K : Type*} [Group K] {v t : K} {r : ℤ}
    (hgen : Subgroup.closure {v, t} = ⊤)
    (hcomm : v * t = t * v)
    (hv2 : v * v = t ^ r)
    (htinj : Function.Injective fun k : ℤ => t ^ k)
    (htors : ∃ x : K, x ≠ 1 ∧ IsOfFinOrder x) :
    Even r := by
  by_contra hnot
  have hodd : Odd r := Int.not_even_iff_odd.mp hnot
  rcases hodd.exists_bit1 with ⟨s, hs⟩
  rw [hs] at hv2
  exact no_torsion_of_commute_square_odd hgen hcomm hv2 htinj htors

/- accepted add_to_file helper 17 -/
lemma presentedGroup_fin_two_closure_pair (rels : Set (FreeGroup (Fin 2))) :
    Subgroup.closure
      ({PresentedGroup.of (rels := rels) (0 : Fin 2),
        PresentedGroup.of (rels := rels) (1 : Fin 2)} :
        Set (PresentedGroup rels)) = ⊤ := by
  have hset :
      ({PresentedGroup.of (rels := rels) (0 : Fin 2),
        PresentedGroup.of (rels := rels) (1 : Fin 2)} :
        Set (PresentedGroup rels)) = Set.range (PresentedGroup.of (rels := rels)) := by
    ext x
    constructor
    · intro hx
      simp at hx
      rcases hx with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
  rw [hset]
  exact PresentedGroup.closure_range_of rels

/- accepted add_to_file helper 18 -/
noncomputable def presentedCommEquiv {K : Type*} [Group K] (v t : K) (n : ℤ)
    (hcomm : v * t = t * v)
    (hsq : v * v = t ^ (2 * n))
    (hgen : Subgroup.closure {v, t} = ⊤)
    (hvH : v ∉ Subgroup.zpowers t)
    (htinj : Function.Injective fun k : ℤ => t ^ k) :
    PresentedGroup (classificationCommRels n) ≃* K := by
  let a : PresentedGroup (classificationCommRels n) := PresentedGroup.of 0
  let b : PresentedGroup (classificationCommRels n) := PresentedGroup.of 1
  have hrel1 : a * b * a⁻¹ * b⁻¹ = 1 := by
    have h := PresentedGroup.one_of_mem
      (rels := classificationCommRels n)
      (x := FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) *
        (FreeGroup.of (0 : Fin 2))⁻¹ * (FreeGroup.of (1 : Fin 2))⁻¹)
      (by simp [classificationCommRels])
    change a * b * a⁻¹ * b⁻¹ = 1 at h
    exact h
  have hcommP : a * b = b * a := by
    calc
      a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [hrel1, one_mul]
  have hrel2 : a ^ (2 : ℕ) * (b ^ (2 * n))⁻¹ = 1 := by
    have h := PresentedGroup.one_of_mem
      (rels := classificationCommRels n)
      (x := (FreeGroup.of (0 : Fin 2)) ^ (2 : ℕ) *
        ((FreeGroup.of (1 : Fin 2)) ^ (2 * n))⁻¹)
      (by simp [classificationCommRels])
    change a ^ (2 : ℕ) * (b ^ (2 * n))⁻¹ = 1 at h
    exact h
  have hsqP : a * a = b ^ (2 * n) := by
    have h := mul_inv_eq_one.mp hrel2
    simpa [sq] using h
  have hnf := twoSidedNF_eq_univ_of_commute_square a b hcommP hsqP
    (presentedGroup_fin_two_closure_pair (classificationCommRels n))
  let φ : Fin 2 → K := fun i => if i = 0 then v else t
  have hrels : ∀ r ∈ classificationCommRels n, (FreeGroup.lift φ) r = 1 := by
    intro r hr
    simp [classificationCommRels] at hr
    rcases hr with rfl | rfl
    · simp [φ]
      calc
        v * t * v⁻¹ * t⁻¹ = (v * t) * (v⁻¹ * t⁻¹) := by group
        _ = (t * v) * (v⁻¹ * t⁻¹) := by rw [hcomm]
        _ = 1 := by group
    · simp [φ]
      calc
        v ^ 2 * (t ^ (2 * n))⁻¹ = (v * v) * (t ^ (2 * n))⁻¹ := by rw [sq]
        _ = 1 := by rw [hsq, mul_inv_cancel]
  let f : PresentedGroup (classificationCommRels n) →* K := PresentedGroup.toGroup hrels
  have fa : f a = v := by
    simp [f, a, φ, PresentedGroup.toGroup.of]
  have fb : f b = t := by
    simp [f, b, φ, PresentedGroup.toGroup.of]
  exact mulEquivOfTwoSidedNF f a b v t fa fb hnf hgen hvH htinj

/- accepted add_to_file helper 19 -/
lemma presentedCommEquiv_apply_of_zero {K : Type*} [Group K] (v t : K) (n : ℤ)
    (hcomm : v * t = t * v) (hsq : v * v = t ^ (2 * n))
    (hgen : Subgroup.closure {v, t} = ⊤)
    (hvH : v ∉ Subgroup.zpowers t)
    (htinj : Function.Injective fun k : ℤ => t ^ k) :
    presentedCommEquiv v t n hcomm hsq hgen hvH htinj
      (PresentedGroup.of (0 : Fin 2)) = v := by
  simp [presentedCommEquiv, mulEquivOfTwoSidedNF, PresentedGroup.toGroup.of]

lemma presentedCommEquiv_apply_of_one {K : Type*} [Group K] (v t : K) (n : ℤ)
    (hcomm : v * t = t * v) (hsq : v * v = t ^ (2 * n))
    (hgen : Subgroup.closure {v, t} = ⊤)
    (hvH : v ∉ Subgroup.zpowers t)
    (htinj : Function.Injective fun k : ℤ => t ^ k) :
    presentedCommEquiv v t n hcomm hsq hgen hvH htinj
      (PresentedGroup.of (1 : Fin 2)) = t := by
  simp [presentedCommEquiv, mulEquivOfTwoSidedNF, PresentedGroup.toGroup.of]

/- accepted add_to_file helper 20 -/
noncomputable def presentedInvEquiv {K : Type*} [Group K] (v t : K)
    (hconj : v * t * v⁻¹ = t⁻¹)
    (hsq : v * v = 1)
    (hgen : Subgroup.closure {v, t} = ⊤)
    (hvH : v ∉ Subgroup.zpowers t)
    (htinj : Function.Injective fun k : ℤ => t ^ k) :
    PresentedGroup classificationInvRels ≃* K := by
  let a : PresentedGroup classificationInvRels := PresentedGroup.of 0
  let b : PresentedGroup classificationInvRels := PresentedGroup.of 1
  have hrel1 : a * b * a⁻¹ * b = 1 := by
    have h := PresentedGroup.one_of_mem
      (rels := classificationInvRels)
      (x := FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) *
        (FreeGroup.of (0 : Fin 2))⁻¹ * FreeGroup.of (1 : Fin 2))
      (by simp [classificationInvRels])
    change a * b * a⁻¹ * b = 1 at h
    exact h
  have hconjP : a * b * a⁻¹ = b⁻¹ := by
    calc
      a * b * a⁻¹ = (a * b * a⁻¹ * b) * b⁻¹ := by group
      _ = b⁻¹ := by rw [hrel1, one_mul]
  have hrel2 : a ^ (2 : ℕ) = 1 := by
    have h := PresentedGroup.one_of_mem
      (rels := classificationInvRels)
      (x := (FreeGroup.of (0 : Fin 2)) ^ (2 : ℕ))
      (by simp [classificationInvRels])
    change a ^ (2 : ℕ) = 1 at h
    exact h
  have hsqP : a * a = 1 := by
    simpa [sq] using hrel2
  have hnf := twoSidedNF_eq_univ_of_inversion a b hconjP hsqP
    (presentedGroup_fin_two_closure_pair classificationInvRels)
  let φ : Fin 2 → K := fun i => if i = 0 then v else t
  have hrels : ∀ r ∈ classificationInvRels, (FreeGroup.lift φ) r = 1 := by
    intro r hr
    simp [classificationInvRels] at hr
    rcases hr with rfl | rfl
    · simp [φ]
      rw [hconj, inv_mul_cancel]
    · simp [φ]
      rw [sq, hsq]
  let f : PresentedGroup classificationInvRels →* K := PresentedGroup.toGroup hrels
  have fa : f a = v := by
    simp [f, a, φ, PresentedGroup.toGroup.of]
  have fb : f b = t := by
    simp [f, b, φ, PresentedGroup.toGroup.of]
  exact mulEquivOfTwoSidedNF f a b v t fa fb hnf hgen hvH htinj

lemma presentedInvEquiv_apply_of_zero {K : Type*} [Group K] (v t : K)
    (hconj : v * t * v⁻¹ = t⁻¹) (hsq : v * v = 1)
    (hgen : Subgroup.closure {v, t} = ⊤)
    (hvH : v ∉ Subgroup.zpowers t)
    (htinj : Function.Injective fun k : ℤ => t ^ k) :
    presentedInvEquiv v t hconj hsq hgen hvH htinj
      (PresentedGroup.of (0 : Fin 2)) = v := by
  simp [presentedInvEquiv, mulEquivOfTwoSidedNF, PresentedGroup.toGroup.of]

lemma presentedInvEquiv_apply_of_one {K : Type*} [Group K] (v t : K)
    (hconj : v * t * v⁻¹ = t⁻¹) (hsq : v * v = 1)
    (hgen : Subgroup.closure {v, t} = ⊤)
    (hvH : v ∉ Subgroup.zpowers t)
    (htinj : Function.Injective fun k : ℤ => t ^ k) :
    presentedInvEquiv v t hconj hsq hgen hvH htinj
      (PresentedGroup.of (1 : Fin 2)) = t := by
  simp [presentedInvEquiv, mulEquivOfTwoSidedNF, PresentedGroup.toGroup.of]

/- accepted add_to_file helper 21 -/
noncomputable def directProductEquivOfCommute {K : Type*} [Group K] (v t : K) (n : ℤ)
    (hcomm : v * t = t * v)
    (hv2 : v * v = t ^ (2 * n))
    (hgen : Subgroup.closure {v, t} = ⊤)
    (hvH : v ∉ Subgroup.zpowers t)
    (htinj : Function.Injective fun k : ℤ => t ^ k) :
    Multiplicative ℤ × Multiplicative (ZMod 2) ≃* K := by
  let u : K := v * t ^ (-n)
  have hu2 : u * u = 1 := by
    dsimp [u]
    calc
      (v * t ^ (-n)) * (v * t ^ (-n))
          = (v * (t ^ (-n) * v)) * t ^ (-n) := by group
      _ = (v * (v * t ^ (-n))) * t ^ (-n) := by
        rw [zpow_commute_left hcomm]
      _ = ((v * v) * t ^ (-n)) * t ^ (-n) := by group
      _ = 1 := by
        rw [hv2, ← zpow_add, ← zpow_add]
        have hzero : 2 * n + -n + -n = 0 := by ring
        rw [hzero]
        simp
  have hu_ne : u ≠ 1 := by
    intro hu1
    have hv_eq : v = t ^ n := by
      calc
        v = (v * t ^ (-n)) * t ^ n := by group
        _ = u * t ^ n := rfl
        _ = t ^ n := by rw [hu1, one_mul]
    have hvmem : v ∈ Subgroup.zpowers t := by
      rw [Subgroup.mem_zpowers_iff]
      exact ⟨n, hv_eq.symm⟩
    exact hvH hvmem
  have hu2pow : u ^ (2 : ℕ) = 1 := by
    rw [sq]
    exact hu2
  have hu_order : orderOf u = 2 := orderOf_eq_prime hu2pow hu_ne
  let fT : Multiplicative ℤ →* K := zpowersHom K t
  let fC : Multiplicative (ZMod 2) →* K := zmodTwoHomOfOrderTwo u hu_order
  have htu : Commute u t := by
    have hvt : Commute v t := hcomm
    have htn : Commute (t ^ (-n)) t :=
      (Commute.refl t).zpow_left (-n)
    exact hvt.mul_left htn
  have hcomm_fg : ∀ (z : Multiplicative ℤ) (c : Multiplicative (ZMod 2)),
      Commute (fT z) (fC c) := by
    intro z c
    have hz : fT z = t ^ Multiplicative.toAdd z := by
      simp [fT, zpowersHom_apply]
    have hc_mem : fC c ∈ Subgroup.zpowers u := by
      change ((zmodTwoEquivZpowers u hu_order) c : K) ∈ Subgroup.zpowers u
      exact ((zmodTwoEquivZpowers u hu_order) c).property
    rw [Subgroup.mem_zpowers_iff] at hc_mem
    rcases hc_mem with ⟨q, hq⟩
    rw [hz, ← hq]
    exact (Commute.zpow_zpow htu q (Multiplicative.toAdd z)).symm
  let F : Multiplicative ℤ × Multiplicative (ZMod 2) →* K :=
    MonoidHom.noncommCoprod fT fC hcomm_fg
  let a : Multiplicative ℤ × Multiplicative (ZMod 2) :=
    (1, Multiplicative.ofAdd (1 : ZMod 2))
  let b : Multiplicative ℤ × Multiplicative (ZMod 2) :=
    (Multiplicative.ofAdd (1 : ℤ), 1)
  have hcomm_ab : a * b = b * a := by
    ext <;> simp [a, b]
  have hsq_ab : a * a = b ^ (2 * (0 : ℤ)) := by
    ext <;> simp [a, b] <;> decide
  have hnf := twoSidedNF_eq_univ_of_commute_square a b hcomm_ab hsq_ab
    closure_pair_product_int_zmod_two
  have fa : F a = u := by
    simp [F, a, MonoidHom.noncommCoprod_apply, fT, fC,
      zmodTwoHomOfOrderTwo_apply_one, zpowersHom_apply]
  have fb : F b = t := by
    simp [F, b, MonoidHom.noncommCoprod_apply, fT, fC, zpowersHom_apply]
  have huH : u ∉ Subgroup.zpowers t := by
    intro humem
    rw [Subgroup.mem_zpowers_iff] at humem
    rcases humem with ⟨q, hq⟩
    have hv_mem : v ∈ Subgroup.zpowers t := by
      have hv_eq : v = u * t ^ n := by
        dsimp [u]
        group
      rw [hv_eq]
      exact mul_mem ⟨q, hq⟩ (zpow_mem (Subgroup.mem_zpowers t) n)
    exact hvH hv_mem
  have hgen_ut : Subgroup.closure {u, t} = ⊤ := by
    have hu_base : u ∈ Subgroup.closure {u, t} :=
      Subgroup.subset_closure (by simp)
    have ht_base : t ∈ Subgroup.closure {u, t} :=
      Subgroup.subset_closure (by simp)
    have hv_mem : v ∈ Subgroup.closure {u, t} := by
      have hv_eq : v = u * t ^ n := by
        dsimp [u]
        group
      rw [hv_eq]
      exact mul_mem hu_base (zpow_mem ht_base n)
    have hsubset : ({v, t} : Set K) ⊆ Subgroup.closure {u, t} := by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl
      · exact hv_mem
      · exact ht_base
    have hle : Subgroup.closure {v, t} ≤ Subgroup.closure {u, t} :=
      (Subgroup.closure_le _).mpr hsubset
    apply top_unique
    rwa [hgen] at hle
  exact mulEquivOfTwoSidedNF F a b u t fa fb hnf hgen_ut huH htinj

/- accepted add_to_file helper 22 -/
lemma multiplicative_zmod_two_one_mul_self :
    Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2) = 1 := by
  apply Multiplicative.toAdd.injective
  simp
  decide

/- accepted add_to_file helper 23 -/
abbrev ZModTwoMult : Type := Multiplicative (ZMod 2)
abbrev InfiniteDihedralModel : Type := Monoid.Coprod ZModTwoMult ZModTwoMult

/- accepted add_to_file helper 24 -/
lemma closure_infinite_dihedral_pair :
    Subgroup.closure
      ({Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ZMod 2)),
        Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ZMod 2)) *
          Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ZMod 2))} :
        Set InfiniteDihedralModel) = ⊤ := by
  let x : InfiniteDihedralModel := Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ZMod 2))
  let y : InfiniteDihedralModel := Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ZMod 2))
  let b : InfiniteDihedralModel := x * y
  have hx2 : x * x = 1 := by
    calc
      x * x = Monoid.Coprod.inl
        (Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2)) := by
        simp [x]
      _ = 1 := by simp [multiplicative_zmod_two_one_mul_self]
  have hy_eq : y = x * b := by
    dsimp [b]
    calc
      y = (x * x) * y := by rw [hx2, one_mul]
      _ = x * (x * y) := by group
  let S : Subgroup InfiniteDihedralModel := Subgroup.closure {x, b}
  have hxS : x ∈ S := Subgroup.subset_closure (by simp [S, x, b])
  have hbS : b ∈ S := Subgroup.subset_closure (by simp [S, x, b])
  have hyS : y ∈ S := by
    rw [hy_eq]
    exact mul_mem hxS hbS
  have hinl_le : Monoid.Coprod.inl.range ≤ S := by
    intro z hz
    rcases hz with ⟨c, rfl⟩
    have hc := mem_zpowers_multiplicative_zmod_two_one c
    rw [Subgroup.mem_zpowers_iff] at hc
    rcases hc with ⟨q, hq⟩
    rw [← hq]
    have hxpow : Monoid.Coprod.inl ((Multiplicative.ofAdd (1 : ZMod 2)) ^ q) = x ^ q := by
      simp [x]
    have hmem : x ^ q ∈ S := zpow_mem hxS q
    simpa [← hxpow] using hmem
  have hinr_le : Monoid.Coprod.inr.range ≤ S := by
    intro z hz
    rcases hz with ⟨c, rfl⟩
    have hc := mem_zpowers_multiplicative_zmod_two_one c
    rw [Subgroup.mem_zpowers_iff] at hc
    rcases hc with ⟨q, hq⟩
    rw [← hq]
    have hypow : Monoid.Coprod.inr ((Multiplicative.ofAdd (1 : ZMod 2)) ^ q) = y ^ q := by
      simp [y]
    have hmem : y ^ q ∈ S := zpow_mem hyS q
    simpa [← hypow] using hmem
  have hjoin : Monoid.Coprod.inl.range ⊔ Monoid.Coprod.inr.range ≤ S :=
    sup_le hinl_le hinr_le
  have htop_le : (⊤ : Subgroup InfiniteDihedralModel) ≤ S := by
    rw [← (Monoid.Coprod.codisjoint_range_inl_range_inr.eq_top)]
    exact hjoin
  have hS : S = ⊤ := top_unique htop_le
  simpa [S, x, b] using hS

/- accepted add_to_file helper 25 -/
noncomputable def infiniteDihedralEquivOfInversion {K : Type*} [Group K] (v t : K)
    (hconj : v * t * v⁻¹ = t⁻¹)
    (hsq : v * v = 1)
    (hgen : Subgroup.closure {v, t} = ⊤)
    (hvH : v ∉ Subgroup.zpowers t)
    (htinj : Function.Injective fun k : ℤ => t ^ k) :
    InfiniteDihedralModel ≃* K := by
  have hv_ne : v ≠ 1 := by
    intro hv1
    rw [hv1] at hvH
    exact hvH (Subgroup.one_mem _)
  have hv2pow : v ^ (2 : ℕ) = 1 := by
    rw [sq]
    exact hsq
  have hv_order : orderOf v = 2 := orderOf_eq_prime hv2pow hv_ne
  let w : K := v * t
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_left hsq
  have hvtv : v * t * v = t⁻¹ := by
    simpa [hvinv] using hconj
  have hw2 : w * w = 1 := by
    dsimp [w]
    calc
      (v * t) * (v * t) = ((v * t) * v) * t := by group
      _ = 1 := by rw [hvtv, inv_mul_cancel]
  have hw_ne : w ≠ 1 := by
    intro hw1
    have ht_eq : t = v := by
      calc
        t = v⁻¹ * (v * t) := by group
        _ = v⁻¹ * w := by dsimp [w]
        _ = v⁻¹ := by rw [hw1, mul_one]
        _ = v := hvinv
    have hvmem : v ∈ Subgroup.zpowers t := by
      rw [← ht_eq]
      exact Subgroup.mem_zpowers t
    exact hvH hvmem
  have hw2pow : w ^ (2 : ℕ) = 1 := by
    rw [sq]
    exact hw2
  have hw_order : orderOf w = 2 := orderOf_eq_prime hw2pow hw_ne
  let fV : ZModTwoMult →* K := zmodTwoHomOfOrderTwo v hv_order
  let fW : ZModTwoMult →* K := zmodTwoHomOfOrderTwo w hw_order
  let F : InfiniteDihedralModel →* K := Monoid.Coprod.lift fV fW
  let a : InfiniteDihedralModel := Monoid.Coprod.inl (Multiplicative.ofAdd (1 : ZMod 2))
  let y : InfiniteDihedralModel := Monoid.Coprod.inr (Multiplicative.ofAdd (1 : ZMod 2))
  let b : InfiniteDihedralModel := a * y
  have hx2 : a * a = 1 := by
    calc
      a * a = Monoid.Coprod.inl
        (Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2)) := by
        simp [a]
      _ = 1 := by simp [multiplicative_zmod_two_one_mul_self]
  have hy2 : y * y = 1 := by
    calc
      y * y = Monoid.Coprod.inr
        (Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2)) := by
        simp [y]
      _ = 1 := by simp [multiplicative_zmod_two_one_mul_self]
  have hxinv : a⁻¹ = a := inv_eq_of_mul_eq_one_left hx2
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_left hy2
  have hconj_ab : a * b * a⁻¹ = b⁻¹ := by
    calc
      a * b * a⁻¹ = ((a * a) * y) * a := by
        dsimp [b]
        rw [hxinv]
        group
      _ = y * a := by rw [hx2, one_mul]
      _ = b⁻¹ := by
        dsimp [b]
        rw [mul_inv_rev, hxinv, hyinv]
  have hnf := twoSidedNF_eq_univ_of_inversion a b hconj_ab hx2
    closure_infinite_dihedral_pair
  have fa : F a = v := by
    simp [F, a, fV, Monoid.Coprod.lift_comp_inl, zmodTwoHomOfOrderTwo_apply_one]
  have fy : F y = w := by
    simp [F, y, fW, Monoid.Coprod.lift_comp_inr, zmodTwoHomOfOrderTwo_apply_one]
  have fb : F b = t := by
    calc
      F b = F a * F y := by simp [b]
      _ = v * (v * t) := by rw [fa, fy]
      _ = t := by
        calc
          v * (v * t) = (v * v) * t := by group
          _ = t := by rw [hsq, one_mul]
  exact mulEquivOfTwoSidedNF F a b v t fa fb hnf hgen hvH htinj

/- verified submission -/
theorem index_two_infinite_cyclic_classification
    {K : Type*} [Group K] (v t : K)
    (hgen : Subgroup.closure {v, t} = ⊤)
    (htinf : Infinite (Subgroup.zpowers t))
    (hindex : (Subgroup.zpowers t).index = 2)
    (htors : ∃ x : K, x ≠ 1 ∧ IsOfFinOrder x) :
    (∃ n : ℤ,
      ∃ e : PresentedGroup
          ({FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) *
              (FreeGroup.of (0 : Fin 2))⁻¹ * (FreeGroup.of (1 : Fin 2))⁻¹,
            (FreeGroup.of (0 : Fin 2)) ^ (2 : ℕ) *
              ((FreeGroup.of (1 : Fin 2)) ^ (2 * n))⁻¹} :
            Set (FreeGroup (Fin 2))) ≃* K,
        e (PresentedGroup.of (0 : Fin 2)) = v ∧
        e (PresentedGroup.of (1 : Fin 2)) = t ∧
        Nonempty (K ≃* Multiplicative ℤ × Multiplicative (ZMod 2))) ∨
    (∃ e : PresentedGroup
          ({FreeGroup.of (0 : Fin 2) * FreeGroup.of (1 : Fin 2) *
              (FreeGroup.of (0 : Fin 2))⁻¹ * FreeGroup.of (1 : Fin 2),
            (FreeGroup.of (0 : Fin 2)) ^ (2 : ℕ)} :
            Set (FreeGroup (Fin 2))) ≃* K,
        e (PresentedGroup.of (0 : Fin 2)) = v ∧
        e (PresentedGroup.of (1 : Fin 2)) = t ∧
        Nonempty
          (K ≃* Monoid.Coprod (Multiplicative (ZMod 2))
            (Multiplicative (ZMod 2)))) := by
  have htinj : Function.Injective fun k : ℤ => t ^ k :=
    zpow_injective_of_infinite_zpowers htinf
  have hvH : v ∉ Subgroup.zpowers t :=
    not_mem_zpowers_of_closure_eq_top_index_two hgen hindex
  have hv2mem : v * v ∈ Subgroup.zpowers t :=
    sq_mem_zpowers_of_index_two (v := v) (t := t) hindex
  rw [Subgroup.mem_zpowers_iff] at hv2mem
  rcases hv2mem with ⟨r, hr⟩
  have hv2 : v * v = t ^ r := hr.symm
  have hcases := conjugation_cases_of_index_two (v := v) (t := t) hindex htinj
  rcases hcases with hcomm | hconj
  · have heven : Even r :=
      square_exponent_even_of_torsion hgen hcomm hv2 htinj htors
    rcases even_iff_exists_two_mul.mp heven with ⟨n, hn⟩
    have hv2n : v * v = t ^ (2 * n) := by
      simpa [hn] using hv2
    let e := presentedCommEquiv v t n hcomm hv2n hgen hvH htinj
    refine Or.inl ?_
    refine ⟨n, e, ?_, ?_, ?_⟩
    · exact presentedCommEquiv_apply_of_zero v t n hcomm hv2n hgen hvH htinj
    · exact presentedCommEquiv_apply_of_one v t n hcomm hv2n hgen hvH htinj
    · exact ⟨(directProductEquivOfCommute v t n hcomm hv2n hgen hvH htinj).symm⟩
  · have hvr : v * v = t ^ (-r) := by
      calc
        v * v = v * (v * v) * v⁻¹ := by group
        _ = v * t ^ r * v⁻¹ := by rw [hv2]
        _ = (v * t * v⁻¹) ^ r := by
          simpa using (conj_zpow (a := v) (b := t) (i := r)).symm
        _ = (t⁻¹) ^ r := by rw [hconj]
        _ = t ^ (-r) := by rw [inv_zpow']
    have hrneg : r = -r := by
      have htr : t ^ r = t ^ (-r) := by
        rw [← hv2, hvr]
      exact htinj htr
    have hr0 : r = 0 := by omega
    have hsq : v * v = 1 := by
      rw [hv2, hr0]
      simp
    let e := presentedInvEquiv v t hconj hsq hgen hvH htinj
    refine Or.inr ?_
    refine ⟨e, ?_, ?_, ?_⟩
    · exact presentedInvEquiv_apply_of_zero v t hconj hsq hgen hvH htinj
    · exact presentedInvEquiv_apply_of_one v t hconj hsq hgen hvH htinj
    · exact ⟨(infiniteDihedralEquivOfInversion v t hconj hsq hgen hvH htinj).symm⟩

end Rollout_p1552_index_two_infinite_cyclic_classification

#check_dependency_graph "Rollout_p1552_index_two_infinite_cyclic_classification.index_two_infinite_cyclic_classification" against "{\"edges\":[{\"conclusion\":{\"name\":\"htinj\",\"statement\":\"Function.Injective fun k => t ^ k\"},\"graphEdgeId\":\"h_001_htinj\",\"premises\":[{\"name\":\"htinf\",\"statement\":\"Infinite ↥(Subgroup.zpowers t)\"}],\"rawEdgeId\":\"telescope_8\"},{\"conclusion\":{\"name\":\"hvH\",\"statement\":\"v ∉ Subgroup.zpowers t\"},\"graphEdgeId\":\"h_002_hvh\",\"premises\":[{\"name\":\"hgen\",\"statement\":\"Subgroup.closure {v, t} = ⊤\"},{\"name\":\"hindex\",\"statement\":\"(Subgroup.zpowers t).index = 2\"}],\"rawEdgeId\":\"telescope_9\"},{\"conclusion\":{\"name\":\"hv2mem\",\"statement\":\"v * v ∈ Subgroup.zpowers t\"},\"graphEdgeId\":\"h_003_hv2mem\",\"premises\":[{\"name\":\"hindex\",\"statement\":\"(Subgroup.zpowers t).index = 2\"}],\"rawEdgeId\":\"telescope_10\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(∃ n e, e (PresentedGroup.of 0) = v ∧ e (PresentedGroup.of 1) = t ∧ Nonempty (K ≃* Multiplicative ℤ × Multiplicative (ZMod 2))) ∨ ∃ e, e (PresentedGroup.of 0) = v ∧ e (PresentedGroup.of 1) = t ∧ Nonempty (K ≃* Monoid.Coprod (Multiplicative (ZMod 2)) (Multiplicative (ZMod 2)))\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hgen\",\"statement\":\"Subgroup.closure {v, t} = ⊤\"},{\"name\":\"hindex\",\"statement\":\"(Subgroup.zpowers t).index = 2\"},{\"name\":\"htors\",\"statement\":\"∃ x, x ≠ 1 ∧ IsOfFinOrder x\"},{\"name\":\"htinj\",\"statement\":\"Function.Injective fun k => t ^ k\"},{\"name\":\"hvH\",\"statement\":\"v ∉ Subgroup.zpowers t\"},{\"name\":\"hv2mem\",\"statement\":\"v * v ∈ Subgroup.zpowers t\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1552_index_two_infinite_cyclic_classification\",\"reconstructedProofSha256\":\"ca16ec0b4eb68fc59e6e018796ea3e9ad62d3dfff9476d84e70f557d46735815\",\"selectedEdgeCount\":4,\"theoremName\":\"Rollout_p1552_index_two_infinite_cyclic_classification.index_two_infinite_cyclic_classification\",\"topologySha256\":\"b970c05a80a45b5cb42281387b00efc48d0120f20aec20b1b700ceda483f090b\"}"

namespace Rollout_p1639_relative_commuting_probability_le

-- graph_id: p1639_relative_commuting_probability_le
-- topology_sha256: 238ee4d8a7cc5f36548c7db5590c508e76736bd9d1fa902a5b8e58d80fd2b1f5
/- accepted add_to_file helper 1 -/
open scoped BigOperators

lemma natCard_commute_pairs_eq_sum {M : Type*} [Group M] [Fintype M] (L : Subgroup M) :
    Nat.card {p : L × M // Commute (p.1 : M) p.2} =
      ∑ x : M, Nat.card {l : L // Commute (l : M) x} := by
  classical
  let e : {p : L × M // Commute (p.1 : M) p.2} ≃
      (Σ x : M, {l : L // Commute (l : M) x}) :=
    { toFun := fun p => ⟨p.1.2, ⟨p.1.1, p.2⟩⟩
      invFun := fun q => ⟨⟨q.2.1, q.1⟩, q.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  rw [Nat.card_eq_fintype_card, Fintype.card_congr e, Fintype.card_sigma]
  congr with x
  exact (Nat.card_eq_fintype_card (α := {l : L // Commute (l : M) x})).symm

lemma coset_centralizer_sum_le_commute_pairs
    {G : Type*} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] [Fintype N]
    (I : Subgroup N) [Fintype I] (x : G) :
    ∑ n : N, Nat.card {i : I // Commute ((i : N) : G) (x * (n : G))} ≤
      Nat.card {p : I × N // Commute (p.1 : N) p.2} := by
  classical
  let base : I → N := fun i =>
    if h : ∃ n : N, Commute ((i : N) : G) (x * (n : G)) then
      Classical.choose h
    else 1
  have hbase : ∀ (i : I) {n : N},
      Commute ((i : N) : G) (x * (n : G)) →
      Commute ((i : N) : G) (x * (base i : G)) := by
    intro i n hn
    dsimp [base]
    rw [dif_pos (show ∃ n : N, Commute ((i : N) : G) (x * (n : G)) from ⟨n, hn⟩)]
    exact Classical.choose_spec (show ∃ n : N, Commute ((i : N) : G) (x * (n : G)) from ⟨n, hn⟩)
  have conj_of_comm : ∀ (i : I) {n : N},
      Commute ((i : N) : G) (x * (n : G)) →
      (n : G) * ((i : N) : G) =
        x⁻¹ * ((i : N) : G) * x * (n : G) := by
    intro i n hn
    calc
      (n : G) * ((i : N) : G) = x⁻¹ * ((x * (n : G)) * ((i : N) : G)) := by group
      _ = x⁻¹ * (((i : N) : G) * (x * (n : G))) := by rw [hn.eq]
      _ = x⁻¹ * ((i : N) : G) * x * (n : G) := by group
  have commute_diff : ∀ (i : I) {n : N},
      Commute ((i : N) : G) (x * (n : G)) →
      Commute ((base i)⁻¹ * n : N) (i : N) := by
    intro i n hn
    have hb := hbase i hn
    have hnG := conj_of_comm i hn
    have hbG := conj_of_comm i hb
    have hbG' : (base i : G)⁻¹ * (x⁻¹ * ((i : N) : G) * x) =
        ((i : N) : G) * (base i : G)⁻¹ := by
      calc
        (base i : G)⁻¹ * (x⁻¹ * ((i : N) : G) * x)
            = (base i : G)⁻¹ *
                ((x⁻¹ * ((i : N) : G) * x) * (base i : G)) *
                (base i : G)⁻¹ := by group
        _ = (base i : G)⁻¹ * ((base i : G) * ((i : N) : G)) *
              (base i : G)⁻¹ := by rw [← hbG]
        _ = ((i : N) : G) * (base i : G)⁻¹ := by group
    have hdG : (((base i)⁻¹ * n : N) : G) * ((i : N) : G) =
        ((i : N) : G) * (((base i)⁻¹ * n : N) : G) := by
      calc
        (((base i)⁻¹ * n : N) : G) * ((i : N) : G)
            = (base i : G)⁻¹ * ((n : G) * ((i : N) : G)) := by
              simp; group
        _ = (base i : G)⁻¹ *
              (x⁻¹ * ((i : N) : G) * x * (n : G)) := by rw [hnG]
        _ = ((base i : G)⁻¹ * (x⁻¹ * ((i : N) : G) * x)) * (n : G) := by group
        _ = (((i : N) : G) * (base i : G)⁻¹) * (n : G) := by rw [hbG']
        _ = ((i : N) : G) * (((base i)⁻¹ * n : N) : G) := by
              simp; group
    show ((base i)⁻¹ * n : N) * (i : N) = (i : N) * ((base i)⁻¹ * n : N)
    exact Subtype.ext hdG
  let F : (Σ n : N, {i : I // Commute ((i : N) : G) (x * (n : G))}) →
      {p : I × N // Commute (p.1 : N) p.2} :=
    fun q => ⟨⟨q.2.1, (base q.2.1)⁻¹ * q.1⟩, (commute_diff q.2.1 q.2.2).symm⟩
  have hF : Function.Injective F := by
    intro a b hab
    rcases a with ⟨n, i, hi⟩
    rcases b with ⟨m, j, hj⟩
    have hp : ((i, (base i)⁻¹ * n) : I × N) =
        (j, (base j)⁻¹ * m) := congrArg Subtype.val hab
    have hij : i = j := congrArg Prod.fst hp
    subst j
    have hnm : n = m := mul_left_cancel (congrArg Prod.snd hp)
    subst m
    rfl
  calc
    ∑ n : N, Nat.card {i : I // Commute ((i : N) : G) (x * (n : G))}
        = Nat.card (Σ n : N, {i : I // Commute ((i : N) : G) (x * (n : G))}) := by
          rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
          congr with n
          exact Nat.card_eq_fintype_card (α := {i : I // Commute ((i : N) : G) (x * (n : G))})
    _ ≤ Nat.card {p : I × N // Commute (p.1 : N) p.2} := by
          rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
          exact Fintype.card_le_of_injective F hF

/- accepted add_to_file helper 2 -/
lemma centralizer_card_le_map_mul_comap
    {G Q : Type*} [Group G] [Group Q] [Fintype G] [Fintype Q]
    (f : G →* Q) (K : Subgroup G) [Fintype K]
    [Fintype (K.map f)] [Fintype (K.comap f.ker.subtype)] (x : G) :
    Nat.card {k : K // Commute (k : G) x} ≤
      Nat.card {u : K.map f // Commute (u : Q) (f x)} *
        Nat.card {i : K.comap f.ker.subtype // Commute ((i : f.ker) : G) x} := by
  classical
  let A := {k : K // Commute (k : G) x}
  let B := {u : K.map f // Commute (u : Q) (f x)}
  let I := {i : K.comap f.ker.subtype // Commute ((i : f.ker) : G) x}
  let im : A → B := fun a =>
    ⟨⟨f (a.1 : G), Subgroup.mem_map_of_mem f a.1.2⟩, a.2.map f⟩
  let base : B → A := fun b =>
    if h : ∃ a : A, im a = b then
      Classical.choose h
    else ⟨1, by simp⟩
  have hbase : ∀ (b : B), (∃ a : A, im a = b) →
      im (base b) = b ∧ Commute ((base b : K) : G) x := by
    intro b hb
    dsimp [base]
    rw [dif_pos hb]
    exact ⟨Classical.choose_spec hb, (Classical.choose hb).2⟩
  let dfun : A → f.ker := fun a =>
    ⟨(a.1 : G) * ((base (im a) : K) : G)⁻¹, by
      obtain ⟨him, _⟩ := hbase (im a) ⟨a, rfl⟩
      rw [MonoidHom.mem_ker]
      have himv : f ((base (im a) : K) : G) = f (a.1 : G) := by
        have := congrArg (fun z : B => (z.1 : Q)) him
        simpa [im] using this
      simp [map_mul, map_inv, himv]⟩
  let jfun : A → K.comap f.ker.subtype := fun a =>
    ⟨dfun a, by
      change ((dfun a : f.ker) : G) ∈ K
      dsimp [dfun]
      exact K.mul_mem a.1.2 (K.inv_mem (base (im a)).1.2)⟩
  let F : A → B × I := fun a =>
    ⟨im a, ⟨jfun a, by
      obtain ⟨_, hcomm⟩ := hbase (im a) ⟨a, rfl⟩
      exact a.2.mul_left ((hcomm.symm.inv_right).symm)⟩⟩
  have hF : Function.Injective F := by
    intro a b hab
    have him : im a = im b := congrArg Prod.fst hab
    have hbaseeq : base (im a) = base (im b) := congrArg base him
    have hival : jfun a = jfun b := by
      have := congrArg Subtype.val (congrArg Prod.snd hab)
      simpa [F] using this
    have hd : ((dfun a : f.ker) : G) = ((dfun b : f.ker) : G) := by
      have := congrArg (fun z : K.comap f.ker.subtype => ((z : f.ker) : G)) hival
      simpa [jfun] using this
    have hmul :
        (a.1 : G) * ((base (im a) : K) : G)⁻¹ =
          (b.1 : G) * ((base (im b) : K) : G)⁻¹ := by
      simpa [dfun] using hd
    have hG : (a.1 : G) = (b.1 : G) := by
      calc
        (a.1 : G) = ((a.1 : G) * ((base (im a) : K) : G)⁻¹) *
            ((base (im a) : K) : G) := by group
        _ = ((b.1 : G) * ((base (im b) : K) : G)⁻¹) *
              ((base (im a) : K) : G) := by rw [hmul]
        _ = ((b.1 : G) * ((base (im b) : K) : G)⁻¹) *
              ((base (im b) : K) : G) := by rw [hbaseeq]
        _ = (b.1 : G) := by group
    apply Subtype.ext
    exact Subtype.ext hG
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  calc
    Fintype.card A ≤ Fintype.card (B × I) := Fintype.card_le_of_injective F hF
    _ = Fintype.card B * Fintype.card I := Fintype.card_prod B I

/- accepted add_to_file helper 3 -/
lemma commute_pairs_card_le_quotient_mul_comap
    {G : Type*} [Group G] [Fintype G]
    (N K : Subgroup G) [N.Normal] [Fintype (G ⧸ N)] :
    let π : G →* G ⧸ N := QuotientGroup.mk' N
    let Kbar : Subgroup (G ⧸ N) := K.map π
    Nat.card {p : K × G // Commute (p.1 : G) p.2} ≤
      Nat.card {p : Kbar × (G ⧸ N) // Commute (p.1 : G ⧸ N) p.2} *
        Nat.card {p : (K.comap N.subtype) × N // Commute (p.1 : N) p.2} := by
  classical
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  let Kbar : Subgroup (G ⧸ N) := K.map π
  let I : Subgroup N := K.comap N.subtype
  let cA : G → ℕ := fun x => Nat.card {k : K // Commute (k : G) x}
  let cB : G ⧸ N → ℕ := fun q =>
    Nat.card {u : Kbar // Commute (u : G ⧸ N) q}
  let cI : G → ℕ := fun x =>
    Nat.card {i : I // Commute ((i : N) : G) x}
  have hpoint : ∀ x : G, cA x ≤ cB (π x) * cI x := by
    intro x
    have h := centralizer_card_le_map_mul_comap π K x
    rw [show π.ker = N by simp [π, QuotientGroup.ker_mk']] at h
    exact h
  let lift : G ⧸ N → G := fun q => Classical.choose (QuotientGroup.mk'_surjective N q)
  have hlift : ∀ q : G ⧸ N, π (lift q) = q :=
    fun q => Classical.choose_spec (QuotientGroup.mk'_surjective N q)
  let efib : ∀ q : G ⧸ N, {x : G // π x = q} ≃ N := fun q =>
    { toFun := fun x =>
        ⟨(lift q)⁻¹ * (x : G), by
          rw [← QuotientGroup.eq_one_iff (N := N)]
          change π ((lift q)⁻¹ * (x : G)) = 1
          simp [map_mul, map_inv, hlift q, x.property]⟩
      invFun := fun n =>
        ⟨lift q * (n : G), by
          simp [π, map_mul, hlift q]⟩
      left_inv := fun x => by
        apply Subtype.ext
        group
      right_inv := fun n => by
        apply Subtype.ext
        group }
  have hfiber_sum : ∀ q : G ⧸ N,
      (∑ z : {x : G // π x = q}, cI (z : G)) =
        ∑ n : N, cI (lift q * (n : G)) := by
    intro q
    exact (Fintype.sum_equiv (efib q).symm
      (fun n : N => cI (lift q * (n : G)))
      (fun z : {x : G // π x = q} => cI (z : G))
      (fun n => rfl)).symm
  have hcoset : ∀ q : G ⧸ N,
      (∑ z : {x : G // π x = q}, cI (z : G)) ≤
        Nat.card {p : I × N // Commute (p.1 : N) p.2} := by
    intro q
    rw [hfiber_sum q]
    exact coset_centralizer_sum_le_commute_pairs N I (lift q)
  calc
    Nat.card {p : K × G // Commute (p.1 : G) p.2}
        = ∑ x : G, cA x := natCard_commute_pairs_eq_sum K
    _ ≤ ∑ x : G, cB (π x) * cI x := by
          exact Finset.sum_le_sum (fun x _ => hpoint x)
    _ = ∑ q : G ⧸ N, ∑ z : {x : G // π x = q}, cB (π (z : G)) * cI (z : G) := by
          exact (Fintype.sum_fiberwise π (fun x : G => cB (π x) * cI x)).symm
    _ = ∑ q : G ⧸ N, ∑ z : {x : G // π x = q}, cB q * cI (z : G) := by
          congr with q
          congr with z
          rw [z.property]
    _ = ∑ q : G ⧸ N, cB q * (∑ z : {x : G // π x = q}, cI (z : G)) := by
          congr with q
          rw [Finset.mul_sum]
    _ ≤ ∑ q : G ⧸ N, cB q *
          Nat.card {p : I × N // Commute (p.1 : N) p.2} := by
          exact Finset.sum_le_sum (fun q _ => mul_le_mul_left' (hcoset q) (cB q))
    _ = (∑ q : G ⧸ N, cB q) *
          Nat.card {p : I × N // Commute (p.1 : N) p.2} := by
          rw [Finset.sum_mul]
    _ = Nat.card {p : Kbar × (G ⧸ N) // Commute (p.1 : G ⧸ N) p.2} *
          Nat.card {p : I × N // Commute (p.1 : N) p.2} := by
          rw [natCard_commute_pairs_eq_sum Kbar]

/- accepted add_to_file helper 4 -/
lemma card_comap_mul_card_map_quotient
    {G : Type*} [Group G]
    (N K : Subgroup G) [N.Normal] :
    let π : G →* G ⧸ N := QuotientGroup.mk' N
    Nat.card (K.comap N.subtype) * Nat.card (K.map π) = Nat.card K := by
  classical
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  let I : Subgroup N := K.comap N.subtype
  let J : Subgroup K := N.subgroupOf K
  have hrel : N.relIndex K = Nat.card (K.map π) := by
    have h := Subgroup.relIndex_ker K π
    rw [show π.ker = N by simp [π, QuotientGroup.ker_mk']] at h
    exact h
  have hIeq : Nat.card I = Nat.card J := by
    let e : I ≃ J :=
      { toFun := fun i => ⟨⟨(i.1 : G), i.2⟩, i.1.2⟩
        invFun := fun j => ⟨⟨(j.1 : G), j.2⟩, j.1.2⟩
        left_inv := fun i => rfl
        right_inv := fun j => rfl }
    exact Nat.card_congr e
  have hJ : Nat.card J * J.index = Nat.card K := Subgroup.card_mul_index J
  calc
    Nat.card I * Nat.card (K.map π) = Nat.card J * N.relIndex K := by
      rw [hIeq, hrel]
    _ = Nat.card J * J.index := rfl
    _ = Nat.card K := hJ

/- verified submission -/
theorem relative_commuting_probability_le
    {G : Type*} [Group G] [Finite G]
    (N K : Subgroup G) [N.Normal] :
    let π : G →* G ⧸ N := QuotientGroup.mk' N
    let Kbar : Subgroup (G ⧸ N) := K.map π
    (Nat.card {p : K × G // Commute (p.1 : G) p.2} : ℚ) /
        ((Nat.card K : ℚ) * (Nat.card G : ℚ)) ≤
      ((Nat.card {p : Kbar × (G ⧸ N) // Commute (p.1 : G ⧸ N) p.2} : ℚ) /
          ((Nat.card Kbar : ℚ) * (Nat.card (G ⧸ N) : ℚ))) *
        ((Nat.card {p : (K.comap N.subtype) × N // Commute (p.1 : N) p.2} : ℚ) /
          ((Nat.card (K.comap N.subtype) : ℚ) * (Nat.card N : ℚ))) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (G ⧸ N) := Fintype.ofFinite (G ⧸ N)
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  let Kbar : Subgroup (G ⧸ N) := K.map π
  let I : Subgroup N := K.comap N.subtype
  let A : ℕ := Nat.card {p : K × G // Commute (p.1 : G) p.2}
  let B : ℕ := Nat.card {p : Kbar × (G ⧸ N) // Commute (p.1 : G ⧸ N) p.2}
  let C : ℕ := Nat.card {p : I × N // Commute (p.1 : N) p.2}
  have hnat : A ≤ B * C := by
    simpa [A, B, C, π, Kbar, I] using
      commute_pairs_card_le_quotient_mul_comap N K
  have hK : Nat.card I * Nat.card Kbar = Nat.card K := by
    simpa [I, Kbar, π] using card_comap_mul_card_map_quotient N K
  have hG : Nat.card (G ⧸ N) * Nat.card N = Nat.card G :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup N).symm
  have hden : (Nat.card K : ℚ) * (Nat.card G : ℚ) =
      ((Nat.card Kbar : ℚ) * (Nat.card (G ⧸ N) : ℚ)) *
        ((Nat.card I : ℚ) * (Nat.card N : ℚ)) := by
    have hdenNat : Nat.card K * Nat.card G =
        (Nat.card Kbar * Nat.card (G ⧸ N)) * (Nat.card I * Nat.card N) := by
      rw [← hK, ← hG]
      ring
    exact_mod_cast hdenNat
  have hnum : (A : ℚ) ≤ ((B * C : ℕ) : ℚ) := by
    exact_mod_cast hnat
  have hnonneg : 0 ≤ (Nat.card K : ℚ) * (Nat.card G : ℚ) := by
    positivity
  have hfactor : ((B : ℚ) /
        ((Nat.card Kbar : ℚ) * (Nat.card (G ⧸ N) : ℚ))) *
      ((C : ℚ) / ((Nat.card I : ℚ) * (Nat.card N : ℚ))) =
      ((B * C : ℕ) : ℚ) / ((Nat.card K : ℚ) * (Nat.card G : ℚ)) := by
    rw [div_mul_div_comm]
    have hnumcast : (B : ℚ) * (C : ℚ) = ((B * C : ℕ) : ℚ) := by
      norm_num
    have hdencast : ((Nat.card Kbar : ℚ) * (Nat.card (G ⧸ N) : ℚ)) *
        ((Nat.card I : ℚ) * (Nat.card N : ℚ)) =
        (Nat.card K : ℚ) * (Nat.card G : ℚ) := hden.symm
    rw [hnumcast, hdencast]
  calc
    (A : ℚ) / ((Nat.card K : ℚ) * (Nat.card G : ℚ)) ≤
        ((B * C : ℕ) : ℚ) / ((Nat.card K : ℚ) * (Nat.card G : ℚ)) :=
      div_le_div_of_nonneg_right hnum hnonneg
    _ = ((B : ℚ) /
          ((Nat.card Kbar : ℚ) * (Nat.card (G ⧸ N) : ℚ))) *
        ((C : ℚ) / ((Nat.card I : ℚ) * (Nat.card N : ℚ))) := hfactor.symm
    _ = ((Nat.card {p : Kbar × (G ⧸ N) // Commute (p.1 : G ⧸ N) p.2} : ℚ) /
          ((Nat.card Kbar : ℚ) * (Nat.card (G ⧸ N) : ℚ))) *
        ((Nat.card {p : (K.comap N.subtype) × N // Commute (p.1 : N) p.2} : ℚ) /
          ((Nat.card (K.comap N.subtype) : ℚ) * (Nat.card N : ℚ))) := rfl

end Rollout_p1639_relative_commuting_probability_le

#check_dependency_graph "Rollout_p1639_relative_commuting_probability_le.relative_commuting_probability_le" against "{\"edges\":[{\"conclusion\":{\"name\":\"hnat\",\"statement\":\"A ≤ B * C\"},\"graphEdgeId\":\"h_001_hnat\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"Finite G\"},{\"name\":\"<generated-instance>\",\"statement\":\"N.Normal\"}],\"rawEdgeId\":\"telescope_12\"},{\"conclusion\":{\"name\":\"hK\",\"statement\":\"Nat.card ↥I * Nat.card ↥Kbar = Nat.card ↥K\"},\"graphEdgeId\":\"h_002_hk\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"Finite G\"},{\"name\":\"<generated-instance>\",\"statement\":\"N.Normal\"}],\"rawEdgeId\":\"telescope_13\"},{\"conclusion\":{\"name\":\"hG\",\"statement\":\"Nat.card (G ⧸ N) * Nat.card ↥N = Nat.card G\"},\"graphEdgeId\":\"h_003_hg\",\"premises\":[],\"rawEdgeId\":\"telescope_14\"},{\"conclusion\":{\"name\":\"hnonneg\",\"statement\":\"0 ≤ ↑(Nat.card ↥K) * ↑(Nat.card G)\"},\"graphEdgeId\":\"h_006_hnonneg\",\"premises\":[],\"rawEdgeId\":\"telescope_17\"},{\"conclusion\":{\"name\":\"hden\",\"statement\":\"↑(Nat.card ↥K) * ↑(Nat.card G) = ↑(Nat.card ↥Kbar) * ↑(Nat.card (G ⧸ N)) * (↑(Nat.card ↥I) * ↑(Nat.card ↥N))\"},\"graphEdgeId\":\"h_004_hden\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"N.Normal\"},{\"name\":\"hK\",\"statement\":\"Nat.card ↥I * Nat.card ↥Kbar = Nat.card ↥K\"},{\"name\":\"hG\",\"statement\":\"Nat.card (G ⧸ N) * Nat.card ↥N = Nat.card G\"}],\"rawEdgeId\":\"telescope_15\"},{\"conclusion\":{\"name\":\"hnum\",\"statement\":\"↑A ≤ ↑(B * C)\"},\"graphEdgeId\":\"h_005_hnum\",\"premises\":[{\"name\":\"hnat\",\"statement\":\"A ≤ B * C\"}],\"rawEdgeId\":\"telescope_16\"},{\"conclusion\":{\"name\":\"hfactor\",\"statement\":\"↑B / (↑(Nat.card ↥Kbar) * ↑(Nat.card (G ⧸ N))) * (↑C / (↑(Nat.card ↥I) * ↑(Nat.card ↥N))) = ↑(B * C) / (↑(Nat.card ↥K) * ↑(Nat.card G))\"},\"graphEdgeId\":\"h_007_hfactor\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"N.Normal\"},{\"name\":\"hden\",\"statement\":\"↑(Nat.card ↥K) * ↑(Nat.card G) = ↑(Nat.card ↥Kbar) * ↑(Nat.card (G ⧸ N)) * (↑(Nat.card ↥I) * ↑(Nat.card ↥N))\"}],\"rawEdgeId\":\"telescope_18\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"↑A / (↑(Nat.card ↥K) * ↑(Nat.card G)) ≤ ↑(Nat.card { p // Commute (↑p.1) p.2 }) / (↑(Nat.card ↥Kbar) * ↑(Nat.card (G ⧸ N))) * (↑(Nat.card { p // Commute (↑p.1) p.2 }) / (↑(Nat.card ↥(Subgroup.comap N.subtype K)) * ↑(Nat.card ↥N)))\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"N.Normal\"},{\"name\":\"hnum\",\"statement\":\"↑A ≤ ↑(B * C)\"},{\"name\":\"hnonneg\",\"statement\":\"0 ≤ ↑(Nat.card ↥K) * ↑(Nat.card G)\"},{\"name\":\"hfactor\",\"statement\":\"↑B / (↑(Nat.card ↥Kbar) * ↑(Nat.card (G ⧸ N))) * (↑C / (↑(Nat.card ↥I) * ↑(Nat.card ↥N))) = ↑(B * C) / (↑(Nat.card ↥K) * ↑(Nat.card G))\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1639_relative_commuting_probability_le\",\"reconstructedProofSha256\":\"cb6c150eab58d9a70eca0d44089c03967e53e1c410f9bd5faf1089f338ed94a8\",\"selectedEdgeCount\":8,\"theoremName\":\"Rollout_p1639_relative_commuting_probability_le.relative_commuting_probability_le\",\"topologySha256\":\"238ee4d8a7cc5f36548c7db5590c508e76736bd9d1fa902a5b8e58d80fd2b1f5\"}"

namespace Rollout_p1662_binary_quadratic_form_volume_identity

/-!
Concrete semantic dependency-graph certificate for rollout p1662.

Every `edge_h...` theorem below has the concrete proposition premises recorded
for that selected hyperedge.  The final theorem composes those edge proofs and
restates the original rollout theorem exactly.  The original theorem itself is
not used as a shortcut.
-/

-- graph_id: p1662_binary_quadratic_form_volume_identity
-- certificate_kind: reviewed_edge_theorems
-- topology_sha256: 36740eb1859b61cc84e98c0fba8102c8ee8ee7c1504f40a8dff4ff09d88d2761
-- reconstructed_proof_sha256: 21afe756275a961c4381bc5359a7ca8d9972574331648a2f3086e58cfa9305f8
-- selected_edge_count: 22

namespace P1662ConcreteSemanticGraph

/- Atomic rollout helpers, including their executable proofs. -/

private lemma quadratic_root_gt_one {A B C q : ℝ}
    (hA : 0 < A) (hC : C < 0) (h1 : A + B + C < 0)
    (hqpos : 0 < q) (hqroot : A * q ^ 2 + B * q + C = 0) :
    1 < q := by
  have hAne : A ≠ 0 := ne_of_gt hA
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hfactor : A + B + C = A * (1 - q) * (1 - C / (A * q)) := by
    field_simp [hAne, hqne]
    nlinarith [hqroot]
  have hAq : 0 < A * q := mul_pos hA hqpos
  have hfrac : C / (A * q) < 0 := div_neg_of_neg_of_pos hC hAq
  have hy : 0 < 1 - C / (A * q) := by linarith
  have hprod : A * (1 - q) * (1 - C / (A * q)) < 0 := by
    rw [← hfactor]
    exact h1
  have hAX : A * (1 - q) < 0 := by
    exact neg_of_mul_neg_left hprod hy.le
  have hx : 1 - q < 0 := by
    exact neg_of_mul_neg_right hAX hA.le
  linarith

private lemma transformed_root_relation {A B C lam mu : ℝ}
    (hA : 0 < A) (hC : C < 0)
    (hlampos : 0 < lam)
    (hlamroot : A * lam ^ 2 + B * lam + C = 0)
    (hmuunique : ∀ x : ℝ, 0 < x →
      A * x ^ 2 + (-2 * A - B) * x + (A + B + C) = 0 → x = mu) :
    1 - C / (A * lam) = mu := by
  have hAne : A ≠ 0 := ne_of_gt hA
  have hlamne : lam ≠ 0 := ne_of_gt hlampos
  let r : ℝ := C / (A * lam)
  have hrneg : r < 0 := by
    dsimp [r]
    exact div_neg_of_neg_of_pos hC (mul_pos hA hlampos)
  have hother : A * r ^ 2 + B * r + C = 0 := by
    dsimp [r]
    field_simp [hAne, hlamne]
    nlinarith [hlamroot]
  have hxpos : 0 < 1 - r := by linarith
  have hxroot : A * (1 - r) ^ 2 + (-2 * A - B) * (1 - r) + (A + B + C) = 0 := by
    nlinarith [hother]
  have hx : 1 - r = mu := hmuunique (1-r) hxpos hxroot
  dsimp [r] at hx
  exact hx

private lemma quadratic_volume_eq {A B C x : ℝ}
    (hA : 0 < A) (hC : C < 0) (h1 : A + B + C < 0)
    (hxpos : 0 < x) (hxgt : 1 < x)
    (hxroot : A * x ^ 2 + B * x + C = 0) :
    A * x * (x - 1) * (1 + 1 / x ^ 2 + 1 / (x - 1) ^ 2) =
      A * (x ^ 2 - x) + 2 * A + A * (A * x + B) / C -
        A * (A * x + A + B) / (A + B + C) := by
  have hAne : A ≠ 0 := ne_of_gt hA
  have hCne : C ≠ 0 := ne_of_lt hC
  have h1ne : A+B+C ≠0 := ne_of_lt h1
  have hxne : x≠0 := ne_of_gt hxpos
  have hx1ne : x-1≠0 := by nlinarith
  have hinvx : 1 / x = -(A * x + B) / C := by
    field_simp [hCne,hxne]
    nlinarith [hxroot]
  have hinvx1 : 1 / (x-1) = -(A * x + A + B) / (A+B+C) := by
    field_simp [h1ne,hx1ne]
    nlinarith [hxroot]
  have hdecomp :
      A * x * (x - 1) * (1 + 1 / x ^ 2 + 1 / (x - 1) ^ 2) =
        A * (x ^ 2 - x) + A * (1 - 1 / x) + A * (1 + 1 / (x - 1)) := by
    field_simp [hxne,hx1ne]
    ring
  rw [hdecomp, hinvx, hinvx1]
  field_simp [hCne,h1ne]
  ring

private lemma quadratic_sum_from_relation {A B C lam mu : ℝ}
    (hA : A ≠ 0)
    (hroot : A * lam ^ 2 + B * lam + C = 0)
    (hrel : mu = lam + 1 + B / A) :
    A * (lam ^ 2 - lam) + A * (mu ^ 2 - mu) =
      B + B ^ 2 / A - 2 * C := by
  have hrootA : A ^ 2 * lam ^ 2 + A * B * lam + A * C = 0 := by
    have h := congrArg (fun t : ℝ => A * t) hroot
    ring_nf at h ⊢
    exact h
  rw [hrel]
  field_simp [hA]
  ring_nf
  nlinarith [hrootA]

private lemma rational_c_sum_from_relation {A B C lam mu : ℝ}
    (hA : A ≠ 0) (hC : C ≠ 0)
    (hrel : mu = lam + 1 + B / A) :
    A * (A * lam + B) / C -
        A * (A * mu - A - B) / C = A * B / C := by
  rw [hrel]
  field_simp [hA,hC]
  ring

private lemma rational_d_sum_from_relation {A B C lam mu : ℝ}
    (hA : A ≠ 0) (hd : A+B+C ≠ 0)
    (hrel : mu = lam + 1 + B / A) :
    - A * (A * lam + A + B) / (A+B+C) +
        A * (A * mu - 2*A - B) / (A+B+C) =
      - A * (2*A+B)/(A+B+C) := by
  rw [hrel]
  field_simp [hA,hd]
  ring

/- Concrete selected hyperedges.  The theorem arguments are exactly the
proposition premises recorded for each graph edge; ordinary data parameters
are not graph nodes. -/

theorem edge_h_001_ha {a : ℤ} (ha : 0 < a) : 0 < (a : ℝ) := by
  exact_mod_cast ha

theorem edge_h_002_hc {c : ℤ} (hc : c < 0) : (c : ℝ) < 0 := by
  exact_mod_cast hc

theorem edge_h_003_hsumr {a b c : ℤ} (hsum : a + b + c < 0) :
    (a : ℝ) + (b : ℝ) + (c : ℝ) < 0 := by
  exact_mod_cast hsum

theorem edge_h_004_hlamgt {a b c : ℤ} {lam : ℝ}
    (hlamroot : (a : ℝ) * lam ^ 2 + (b : ℝ) * lam + (c : ℝ) = 0)
    (hlampos : 0 < lam)
    (hA : 0 < (a : ℝ))
    (hC : (c : ℝ) < 0)
    (hsumR : (a : ℝ) + (b : ℝ) + (c : ℝ) < 0) :
    1 < lam := by
  exact quadratic_root_gt_one hA hC hsumR hlampos hlamroot

theorem edge_h_005_hmurootr {a b c : ℤ} {mu : ℝ}
    (hmuroot :
      (a : ℝ) * mu ^ 2 + ((-2 * a - b : ℤ) : ℝ) * mu +
        ((a + b + c : ℤ) : ℝ) = 0) :
    (a : ℝ) * mu ^ 2 + (-2 * (a : ℝ) - (b : ℝ)) * mu +
      ((a : ℝ) + (b : ℝ) + (c : ℝ)) = 0 := by
  push_cast at hmuroot
  convert hmuroot using 1 <;> ring_nf

theorem edge_h_006_hmu_at_one {a b c : ℤ}
    (hC : (c : ℝ) < 0) :
    (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) +
      ((a : ℝ) + (b : ℝ) + (c : ℝ)) < 0 := by
  have h : (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) +
      ((a : ℝ) + (b : ℝ) + (c : ℝ)) = (c : ℝ) := by ring
  rw [h]
  exact hC

theorem edge_h_007_hmu_gt {a b c : ℤ} {mu : ℝ}
    (hmupos : 0 < mu)
    (hA : 0 < (a : ℝ))
    (hsumR : (a : ℝ) + (b : ℝ) + (c : ℝ) < 0)
    (hmurootR :
      (a : ℝ) * mu ^ 2 + (-2 * (a : ℝ) - (b : ℝ)) * mu +
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) = 0)
    (hmu_at_one :
      (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) +
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) < 0) :
    1 < mu := by
  exact quadratic_root_gt_one hA hsumR hmu_at_one hmupos hmurootR

theorem edge_h_008_hmuunique {a b c : ℤ} {mu : ℝ}
    (hmuunique : ∀ x : ℝ,
      0 < x →
        (a : ℝ) * x ^ 2 + ((-2 * a - b : ℤ) : ℝ) * x +
          ((a + b + c : ℤ) : ℝ) = 0 →
        x = mu) :
    ∀ x : ℝ, 0 < x →
      (a : ℝ) * x ^ 2 + (-2 * (a : ℝ) - (b : ℝ)) * x +
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) = 0 → x = mu := by
  intro x hx hxroot
  apply hmuunique x hx
  push_cast
  convert hxroot using 1 <;> ring_nf

theorem edge_h_009_hrel {a b c : ℤ} {lam mu : ℝ}
    (hlamroot : (a : ℝ) * lam ^ 2 + (b : ℝ) * lam + (c : ℝ) = 0)
    (hlampos : 0 < lam)
    (hA : 0 < (a : ℝ))
    (hC : (c : ℝ) < 0)
    (hmuunique' : ∀ x : ℝ, 0 < x →
      (a : ℝ) * x ^ 2 + (-2 * (a : ℝ) - (b : ℝ)) * x +
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) = 0 → x = mu) :
    1 - (c : ℝ) / ((a : ℝ) * lam) = mu := by
  exact transformed_root_relation hA hC hlampos hlamroot hmuunique'

theorem edge_h_010_hane {a : ℤ}
    (hA : 0 < (a : ℝ)) : (a : ℝ) ≠ 0 := by
  exact ne_of_gt hA

theorem edge_h_011_hlamne {lam : ℝ}
    (hlampos : 0 < lam) : lam ≠ 0 := by
  exact ne_of_gt hlampos

theorem edge_h_012_hcne {c : ℤ}
    (hC : (c : ℝ) < 0) : (c : ℝ) ≠ 0 := by
  exact ne_of_lt hC

theorem edge_h_013_hsumne {a b c : ℤ}
    (hsumR : (a : ℝ) + (b : ℝ) + (c : ℝ) < 0) :
    (a : ℝ) + (b : ℝ) + (c : ℝ) ≠ 0 := by
  exact ne_of_lt hsumR

theorem edge_h_014_hcdiv {a b c : ℤ} {lam : ℝ}
    (hlamroot : (a : ℝ) * lam ^ 2 + (b : ℝ) * lam + (c : ℝ) = 0)
    (hAne : (a : ℝ) ≠ 0)
    (hlamne : lam ≠ 0) :
    (c : ℝ) / ((a : ℝ) * lam) = -((b : ℝ) / (a : ℝ)) - lam := by
  field_simp [hAne,hlamne]
  nlinarith [hlamroot]

theorem edge_h_015_hmlin {a b c : ℤ} {lam mu : ℝ}
    (hrel : 1 - (c : ℝ) / ((a : ℝ) * lam) = mu)
    (hcdiv : (c : ℝ) / ((a : ℝ) * lam) = -((b : ℝ) / (a : ℝ)) - lam) :
    mu = lam + 1 + (b : ℝ) / (a : ℝ) := by
  linarith [hrel,hcdiv]

theorem edge_h_016_hvlam {a b c : ℤ} {lam : ℝ}
    (hlamroot : (a : ℝ) * lam ^ 2 + (b : ℝ) * lam + (c : ℝ) = 0)
    (hlampos : 0 < lam)
    (hA : 0 < (a : ℝ))
    (hC : (c : ℝ) < 0)
    (hsumR : (a : ℝ) + (b : ℝ) + (c : ℝ) < 0)
    (hlamgt : 1 < lam) :
    (a : ℝ) * lam * (lam - 1) *
        (1 + 1 / lam ^ 2 + 1 / (lam - 1) ^ 2) =
      (a : ℝ) * (lam ^ 2 - lam) + 2 * (a : ℝ) +
        (a : ℝ) * ((a : ℝ) * lam + (b : ℝ)) / (c : ℝ) -
        (a : ℝ) * ((a : ℝ) * lam + (a : ℝ) + (b : ℝ)) /
          ((a : ℝ) + (b : ℝ) + (c : ℝ)) := by
  exact quadratic_volume_eq hA hC hsumR hlampos hlamgt hlamroot

theorem edge_h_017_hvmu {a b c : ℤ} {mu : ℝ}
    (hmupos : 0 < mu)
    (hA : 0 < (a : ℝ))
    (hsumR : (a : ℝ) + (b : ℝ) + (c : ℝ) < 0)
    (hmurootR :
      (a : ℝ) * mu ^ 2 + (-2 * (a : ℝ) - (b : ℝ)) * mu +
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) = 0)
    (hmu_at_one :
      (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) +
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) < 0)
    (hmu_gt : 1 < mu) :
    (a : ℝ) * mu * (mu - 1) *
        (1 + 1 / mu ^ 2 + 1 / (mu - 1) ^ 2) =
      (a : ℝ) * (mu ^ 2 - mu) + 2 * (a : ℝ) +
        (a : ℝ) * ((a : ℝ) * mu + (-2 * (a : ℝ) - (b : ℝ))) /
          ((a : ℝ) + (b : ℝ) + (c : ℝ)) -
        (a : ℝ) * ((a : ℝ) * mu + (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ))) /
          ((a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) +
            ((a : ℝ) + (b : ℝ) + (c : ℝ))) := by
  exact quadratic_volume_eq hA hsumR hmu_at_one hmupos hmu_gt hmurootR

theorem edge_h_018_hfmu (a b c : ℤ) :
    (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) +
      ((a : ℝ) + (b : ℝ) + (c : ℝ)) = (c : ℝ) := by
  ring

theorem edge_h_019_hquad {a b c : ℤ} {lam mu : ℝ}
    (hlamroot : (a : ℝ) * lam ^ 2 + (b : ℝ) * lam + (c : ℝ) = 0)
    (hAne : (a : ℝ) ≠ 0)
    (hmlin : mu = lam + 1 + (b : ℝ) / (a : ℝ)) :
    (a : ℝ) * (lam ^ 2 - lam) + (a : ℝ) * (mu ^ 2 - mu) =
      (b : ℝ) + (b : ℝ) ^ 2 / (a : ℝ) - 2 * (c : ℝ) := by
  exact quadratic_sum_from_relation hAne hlamroot hmlin

theorem edge_h_020_hrc {a b c : ℤ} {lam mu : ℝ}
    (hAne : (a : ℝ) ≠ 0)
    (hCne : (c : ℝ) ≠ 0)
    (hmlin : mu = lam + 1 + (b : ℝ) / (a : ℝ)) :
    (a : ℝ) * ((a : ℝ) * lam + (b : ℝ)) / (c : ℝ) -
      (a : ℝ) * ((a : ℝ) * mu - (a : ℝ) - (b : ℝ)) / (c : ℝ) =
        (a : ℝ) * (b : ℝ) / (c : ℝ) := by
  exact rational_c_sum_from_relation hAne hCne hmlin

theorem edge_h_021_hrd {a b c : ℤ} {lam mu : ℝ}
    (hAne : (a : ℝ) ≠ 0)
    (hsumne : (a : ℝ) + (b : ℝ) + (c : ℝ) ≠ 0)
    (hmlin : mu = lam + 1 + (b : ℝ) / (a : ℝ)) :
    - (a : ℝ) * ((a : ℝ) * lam + (a : ℝ) + (b : ℝ)) /
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) +
      (a : ℝ) * ((a : ℝ) * mu - 2 * (a : ℝ) - (b : ℝ)) /
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) =
      - (a : ℝ) * (2 * (a : ℝ) + (b : ℝ)) /
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) := by
  exact rational_d_sum_from_relation hAne hsumne hmlin

theorem edge_h_goal {a b c : ℤ} {lam mu : ℝ}
    (hVlam :
      (a : ℝ) * lam * (lam - 1) *
          (1 + 1 / lam ^ 2 + 1 / (lam - 1) ^ 2) =
        (a : ℝ) * (lam ^ 2 - lam) + 2 * (a : ℝ) +
          (a : ℝ) * ((a : ℝ) * lam + (b : ℝ)) / (c : ℝ) -
          (a : ℝ) * ((a : ℝ) * lam + (a : ℝ) + (b : ℝ)) /
            ((a : ℝ) + (b : ℝ) + (c : ℝ)))
    (hVmu :
      (a : ℝ) * mu * (mu - 1) *
          (1 + 1 / mu ^ 2 + 1 / (mu - 1) ^ 2) =
        (a : ℝ) * (mu ^ 2 - mu) + 2 * (a : ℝ) +
          (a : ℝ) * ((a : ℝ) * mu + (-2 * (a : ℝ) - (b : ℝ))) /
            ((a : ℝ) + (b : ℝ) + (c : ℝ)) -
          (a : ℝ) * ((a : ℝ) * mu + (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ))) /
            ((a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) +
              ((a : ℝ) + (b : ℝ) + (c : ℝ))))
    (hfmu :
      (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) +
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) = (c : ℝ))
    (hquad :
      (a : ℝ) * (lam ^ 2 - lam) + (a : ℝ) * (mu ^ 2 - mu) =
        (b : ℝ) + (b : ℝ) ^ 2 / (a : ℝ) - 2 * (c : ℝ))
    (hrC :
      (a : ℝ) * ((a : ℝ) * lam + (b : ℝ)) / (c : ℝ) -
        (a : ℝ) * ((a : ℝ) * mu - (a : ℝ) - (b : ℝ)) / (c : ℝ) =
          (a : ℝ) * (b : ℝ) / (c : ℝ))
    (hrD :
      - (a : ℝ) * ((a : ℝ) * lam + (a : ℝ) + (b : ℝ)) /
          ((a : ℝ) + (b : ℝ) + (c : ℝ)) +
        (a : ℝ) * ((a : ℝ) * mu - 2 * (a : ℝ) - (b : ℝ)) /
          ((a : ℝ) + (b : ℝ) + (c : ℝ)) =
        - (a : ℝ) * (2 * (a : ℝ) + (b : ℝ)) /
          ((a : ℝ) + (b : ℝ) + (c : ℝ))) :
    (a : ℝ) * lam * (lam - 1) *
          (1 + 1 / lam ^ 2 + 1 / (lam - 1) ^ 2) +
        (a : ℝ) * mu * (mu - 1) *
          (1 + 1 / mu ^ 2 + 1 / (mu - 1) ^ 2) =
      4 * (a : ℝ) + (b : ℝ) + (b : ℝ) ^ 2 / (a : ℝ) +
        (a : ℝ) * (b : ℝ) / (c : ℝ) - 2 * (c : ℝ) -
        (a : ℝ) * (2 * (a : ℝ) + (b : ℝ)) /
          ((a : ℝ) + (b : ℝ) + (c : ℝ)) := by
  rw [hfmu] at hVmu
  rw [hVlam, hVmu]
  have harrange :
      ((a : ℝ) * (lam ^ 2 - lam) + 2 * (a : ℝ) +
          (a : ℝ) * ((a : ℝ) * lam + (b : ℝ)) / (c : ℝ) -
          (a : ℝ) * ((a : ℝ) * lam + (a : ℝ) + (b : ℝ)) /
            ((a : ℝ) + (b : ℝ) + (c : ℝ))) +
        ((a : ℝ) * (mu ^ 2 - mu) + 2 * (a : ℝ) +
          (a : ℝ) * ((a : ℝ) * mu + (-2 * (a : ℝ) - (b : ℝ))) /
            ((a : ℝ) + (b : ℝ) + (c : ℝ)) -
          (a : ℝ) * ((a : ℝ) * mu + (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ))) /
            (c : ℝ)) =
      ((a : ℝ) * (lam ^ 2 - lam) + (a : ℝ) * (mu ^ 2 - mu)) +
        4 * (a : ℝ) +
        ((a : ℝ) * ((a : ℝ) * lam + (b : ℝ)) / (c : ℝ) -
          (a : ℝ) * ((a : ℝ) * mu - (a : ℝ) - (b : ℝ)) / (c : ℝ)) +
        (- (a : ℝ) * ((a : ℝ) * lam + (a : ℝ) + (b : ℝ)) /
            ((a : ℝ) + (b : ℝ) + (c : ℝ)) +
          (a : ℝ) * ((a : ℝ) * mu - 2 * (a : ℝ) - (b : ℝ)) /
            ((a : ℝ) + (b : ℝ) + (c : ℝ))) := by
    ring
  rw [harrange, hquad, hrC, hrD]
  ring

/- Exact final anchor: the original theorem statement, proved only by the
concrete graph edges above. -/

theorem graph_derives_binary_quadratic_form_volume_identity
    (D a b c : ℤ) (lam mu : ℝ)
    (hDpos : 0 < D)
    (hDnsq : ¬ IsSquare D)
    (hDmod : D % 4 = 0 ∨ D % 4 = 1)
    (hdisc : b ^ 2 - 4 * a * c = D)
    (ha : 0 < a)
    (hc : c < 0)
    (hsum : a + b + c < 0)
    (hlamroot : (a : ℝ) * lam ^ 2 + (b : ℝ) * lam + (c : ℝ) = 0)
    (hlampos : 0 < lam)
    (hlamunique : ∀ x : ℝ,
      0 < x → (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0 → x = lam)
    (hmuroot :
      (a : ℝ) * mu ^ 2 + ((-2 * a - b : ℤ) : ℝ) * mu +
        ((a + b + c : ℤ) : ℝ) = 0)
    (hmupos : 0 < mu)
    (hmuunique : ∀ x : ℝ,
      0 < x →
        (a : ℝ) * x ^ 2 + ((-2 * a - b : ℤ) : ℝ) * x +
          ((a + b + c : ℤ) : ℝ) = 0 →
        x = mu) :
    (a : ℝ) * lam * (lam - 1) *
          (1 + 1 / lam ^ 2 + 1 / (lam - 1) ^ 2) +
        (a : ℝ) * mu * (mu - 1) *
          (1 + 1 / mu ^ 2 + 1 / (mu - 1) ^ 2) =
      4 * (a : ℝ) + (b : ℝ) + (b : ℝ) ^ 2 / (a : ℝ) +
        (a : ℝ) * (b : ℝ) / (c : ℝ) - 2 * (c : ℝ) -
        (a : ℝ) * (2 * (a : ℝ) + (b : ℝ)) /
          ((a : ℝ) + (b : ℝ) + (c : ℝ)) := by
  have hA := edge_h_001_ha ha
  have hC := edge_h_002_hc hc
  have hsumR := edge_h_003_hsumr hsum
  have hlamgt := edge_h_004_hlamgt hlamroot hlampos hA hC hsumR
  have hmurootR := edge_h_005_hmurootr hmuroot
  have hmu_at_one := edge_h_006_hmu_at_one (a := a) (b := b) hC
  have hmu_gt := edge_h_007_hmu_gt hmupos hA hsumR hmurootR hmu_at_one
  have hmuunique' := edge_h_008_hmuunique hmuunique
  have hrel := edge_h_009_hrel hlamroot hlampos hA hC hmuunique'
  have hAne := edge_h_010_hane hA
  have hlamne := edge_h_011_hlamne hlampos
  have hCne := edge_h_012_hcne hC
  have hsumne := edge_h_013_hsumne hsumR
  have hcdiv := edge_h_014_hcdiv hlamroot hAne hlamne
  have hmlin := edge_h_015_hmlin hrel hcdiv
  have hVlam := edge_h_016_hvlam hlamroot hlampos hA hC hsumR hlamgt
  have hVmu := edge_h_017_hvmu hmupos hA hsumR hmurootR hmu_at_one hmu_gt
  have hfmu := edge_h_018_hfmu a b c
  have hquad := edge_h_019_hquad hlamroot hAne hmlin
  have hrC := edge_h_020_hrc hAne hCne hmlin
  have hrD := edge_h_021_hrd hAne hsumne hmlin
  exact edge_h_goal hVlam hVmu hfmu hquad hrC hrD

end P1662ConcreteSemanticGraph

/- Generated exact graph/type bridge. Do not edit this section.
Each example applies the reviewed concrete edge theorem to precisely
the premise and conclusion propositions rendered in graph.json. -/
-- generated_bridge_topology_sha256: 36740eb1859b61cc84e98c0fba8102c8ee8ee7c1504f40a8dff4ff09d88d2761
namespace ConcreteGraphTypeBridge_p1662_binary_quadratic_form_volume_identity

variable (a b c : ℤ)
variable (lam mu : ℝ)

-- graph edge: h_001_ha
example
    (P001 : 0 < a)
    : 0 < (a : ℝ) := by
  exact P1662ConcreteSemanticGraph.edge_h_001_ha (a := a) P001

-- graph edge: h_002_hc
example
    (P001 : c < 0)
    : (c : ℝ) < 0 := by
  exact P1662ConcreteSemanticGraph.edge_h_002_hc (c := c) P001

-- graph edge: h_003_hsumr
example
    (P001 : a + b + c < 0)
    : (a : ℝ) + (b : ℝ) + (c : ℝ) < 0 := by
  exact P1662ConcreteSemanticGraph.edge_h_003_hsumr (a := a) (b := b) (c := c) P001

-- graph edge: h_005_hmurootr
example
    (P001 : (a : ℝ) * mu ^ 2 + ((-2 * a - b : ℤ) : ℝ) * mu + ((a + b + c : ℤ) : ℝ) = 0)
    : (a : ℝ) * mu ^ 2 + (-2 * (a : ℝ) - (b : ℝ)) * mu + ((a : ℝ) + (b : ℝ) + (c : ℝ)) = 0 := by
  exact P1662ConcreteSemanticGraph.edge_h_005_hmurootr (a := a) (b := b) (c := c) (mu := mu) P001

-- graph edge: h_008_hmuunique
example
    (P001 : ∀ (x : ℝ), 0 < x → (a : ℝ) * x ^ 2 + ((-2 * a - b : ℤ) : ℝ) * x + ((a + b + c : ℤ) : ℝ) = 0 → x = mu)
    : ∀ (x : ℝ), 0 < x → (a : ℝ) * x ^ 2 + (-2 * (a : ℝ) - (b : ℝ)) * x + ((a : ℝ) + (b : ℝ) + (c : ℝ)) = 0 → x = mu := by
  exact P1662ConcreteSemanticGraph.edge_h_008_hmuunique (a := a) (b := b) (c := c) (mu := mu) P001

-- graph edge: h_011_hlamne
example
    (P001 : 0 < lam)
    : lam ≠ 0 := by
  exact P1662ConcreteSemanticGraph.edge_h_011_hlamne (lam := lam) P001

-- graph edge: h_018_hfmu
example
    : (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) + ((a : ℝ) + (b : ℝ) + (c : ℝ)) = (c : ℝ) := by
  exact P1662ConcreteSemanticGraph.edge_h_018_hfmu (a := a) (b := b) (c := c)

-- graph edge: h_004_hlamgt
example
    (P001 : (a : ℝ) * lam ^ 2 + (b : ℝ) * lam + (c : ℝ) = 0)
    (P002 : 0 < lam)
    (P003 : 0 < (a : ℝ))
    (P004 : (c : ℝ) < 0)
    (P005 : (a : ℝ) + (b : ℝ) + (c : ℝ) < 0)
    : 1 < lam := by
  exact P1662ConcreteSemanticGraph.edge_h_004_hlamgt (a := a) (b := b) (c := c) (lam := lam) P001 P002 P003 P004 P005

-- graph edge: h_006_hmu_at_one
example
    (P001 : (c : ℝ) < 0)
    : (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) + ((a : ℝ) + (b : ℝ) + (c : ℝ)) < 0 := by
  exact P1662ConcreteSemanticGraph.edge_h_006_hmu_at_one (a := a) (b := b) (c := c) P001

-- graph edge: h_009_hrel
example
    (P001 : (a : ℝ) * lam ^ 2 + (b : ℝ) * lam + (c : ℝ) = 0)
    (P002 : 0 < lam)
    (P003 : 0 < (a : ℝ))
    (P004 : (c : ℝ) < 0)
    (P005 : ∀ (x : ℝ), 0 < x → (a : ℝ) * x ^ 2 + (-2 * (a : ℝ) - (b : ℝ)) * x + ((a : ℝ) + (b : ℝ) + (c : ℝ)) = 0 → x = mu)
    : 1 - (c : ℝ) / ((a : ℝ) * lam) = mu := by
  exact P1662ConcreteSemanticGraph.edge_h_009_hrel (a := a) (b := b) (c := c) (lam := lam) (mu := mu) P001 P002 P003 P004 P005

-- graph edge: h_010_hane
example
    (P001 : 0 < (a : ℝ))
    : (a : ℝ) ≠ 0 := by
  exact P1662ConcreteSemanticGraph.edge_h_010_hane (a := a) P001

-- graph edge: h_012_hcne
example
    (P001 : (c : ℝ) < 0)
    : (c : ℝ) ≠ 0 := by
  exact P1662ConcreteSemanticGraph.edge_h_012_hcne (c := c) P001

-- graph edge: h_013_hsumne
example
    (P001 : (a : ℝ) + (b : ℝ) + (c : ℝ) < 0)
    : (a : ℝ) + (b : ℝ) + (c : ℝ) ≠ 0 := by
  exact P1662ConcreteSemanticGraph.edge_h_013_hsumne (a := a) (b := b) (c := c) P001

-- graph edge: h_007_hmu_gt
example
    (P001 : 0 < mu)
    (P002 : 0 < (a : ℝ))
    (P003 : (a : ℝ) + (b : ℝ) + (c : ℝ) < 0)
    (P004 : (a : ℝ) * mu ^ 2 + (-2 * (a : ℝ) - (b : ℝ)) * mu + ((a : ℝ) + (b : ℝ) + (c : ℝ)) = 0)
    (P005 : (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) + ((a : ℝ) + (b : ℝ) + (c : ℝ)) < 0)
    : 1 < mu := by
  exact P1662ConcreteSemanticGraph.edge_h_007_hmu_gt (a := a) (b := b) (c := c) (mu := mu) P001 P002 P003 P004 P005

-- graph edge: h_014_hcdiv
example
    (P001 : (a : ℝ) * lam ^ 2 + (b : ℝ) * lam + (c : ℝ) = 0)
    (P002 : (a : ℝ) ≠ 0)
    (P003 : lam ≠ 0)
    : (c : ℝ) / ((a : ℝ) * lam) = -((b : ℝ) / (a : ℝ)) - lam := by
  exact P1662ConcreteSemanticGraph.edge_h_014_hcdiv (a := a) (b := b) (c := c) (lam := lam) P001 P002 P003

-- graph edge: h_016_hvlam
example
    (P001 : (a : ℝ) * lam ^ 2 + (b : ℝ) * lam + (c : ℝ) = 0)
    (P002 : 0 < lam)
    (P003 : 0 < (a : ℝ))
    (P004 : (c : ℝ) < 0)
    (P005 : (a : ℝ) + (b : ℝ) + (c : ℝ) < 0)
    (P006 : 1 < lam)
    : (a : ℝ) * lam * (lam - 1) * (1 + 1 / lam ^ 2 + 1 / (lam - 1) ^ 2) = (a : ℝ) * (lam ^ 2 - lam) + 2 * (a : ℝ) + (a : ℝ) * ((a : ℝ) * lam + (b : ℝ)) / (c : ℝ) - (a : ℝ) * ((a : ℝ) * lam + (a : ℝ) + (b : ℝ)) / ((a : ℝ) + (b : ℝ) + (c : ℝ)) := by
  exact P1662ConcreteSemanticGraph.edge_h_016_hvlam (a := a) (b := b) (c := c) (lam := lam) P001 P002 P003 P004 P005 P006

-- graph edge: h_015_hmlin
example
    (P001 : 1 - (c : ℝ) / ((a : ℝ) * lam) = mu)
    (P002 : (c : ℝ) / ((a : ℝ) * lam) = -((b : ℝ) / (a : ℝ)) - lam)
    : mu = lam + 1 + (b : ℝ) / (a : ℝ) := by
  exact P1662ConcreteSemanticGraph.edge_h_015_hmlin (a := a) (b := b) (c := c) (lam := lam) (mu := mu) P001 P002

-- graph edge: h_017_hvmu
example
    (P001 : 0 < mu)
    (P002 : 0 < (a : ℝ))
    (P003 : (a : ℝ) + (b : ℝ) + (c : ℝ) < 0)
    (P004 : (a : ℝ) * mu ^ 2 + (-2 * (a : ℝ) - (b : ℝ)) * mu + ((a : ℝ) + (b : ℝ) + (c : ℝ)) = 0)
    (P005 : (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) + ((a : ℝ) + (b : ℝ) + (c : ℝ)) < 0)
    (P006 : 1 < mu)
    : (a : ℝ) * mu * (mu - 1) * (1 + 1 / mu ^ 2 + 1 / (mu - 1) ^ 2) = (a : ℝ) * (mu ^ 2 - mu) + 2 * (a : ℝ) + (a : ℝ) * ((a : ℝ) * mu + (-2 * (a : ℝ) - (b : ℝ))) / ((a : ℝ) + (b : ℝ) + (c : ℝ)) - (a : ℝ) * ((a : ℝ) * mu + (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ))) / ((a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) + ((a : ℝ) + (b : ℝ) + (c : ℝ))) := by
  exact P1662ConcreteSemanticGraph.edge_h_017_hvmu (a := a) (b := b) (c := c) (mu := mu) P001 P002 P003 P004 P005 P006

-- graph edge: h_019_hquad
example
    (P001 : (a : ℝ) * lam ^ 2 + (b : ℝ) * lam + (c : ℝ) = 0)
    (P002 : (a : ℝ) ≠ 0)
    (P003 : mu = lam + 1 + (b : ℝ) / (a : ℝ))
    : (a : ℝ) * (lam ^ 2 - lam) + (a : ℝ) * (mu ^ 2 - mu) = (b : ℝ) + (b : ℝ) ^ 2 / (a : ℝ) - 2 * (c : ℝ) := by
  exact P1662ConcreteSemanticGraph.edge_h_019_hquad (a := a) (b := b) (c := c) (lam := lam) (mu := mu) P001 P002 P003

-- graph edge: h_020_hrc
example
    (P001 : (a : ℝ) ≠ 0)
    (P002 : (c : ℝ) ≠ 0)
    (P003 : mu = lam + 1 + (b : ℝ) / (a : ℝ))
    : (a : ℝ) * ((a : ℝ) * lam + (b : ℝ)) / (c : ℝ) - (a : ℝ) * ((a : ℝ) * mu - (a : ℝ) - (b : ℝ)) / (c : ℝ) = (a : ℝ) * (b : ℝ) / (c : ℝ) := by
  exact P1662ConcreteSemanticGraph.edge_h_020_hrc (a := a) (b := b) (c := c) (lam := lam) (mu := mu) P001 P002 P003

-- graph edge: h_021_hrd
example
    (P001 : (a : ℝ) ≠ 0)
    (P002 : (a : ℝ) + (b : ℝ) + (c : ℝ) ≠ 0)
    (P003 : mu = lam + 1 + (b : ℝ) / (a : ℝ))
    : -(a : ℝ) * ((a : ℝ) * lam + (a : ℝ) + (b : ℝ)) / ((a : ℝ) + (b : ℝ) + (c : ℝ)) + (a : ℝ) * ((a : ℝ) * mu - 2 * (a : ℝ) - (b : ℝ)) / ((a : ℝ) + (b : ℝ) + (c : ℝ)) = -(a : ℝ) * (2 * (a : ℝ) + (b : ℝ)) / ((a : ℝ) + (b : ℝ) + (c : ℝ)) := by
  exact P1662ConcreteSemanticGraph.edge_h_021_hrd (a := a) (b := b) (c := c) (lam := lam) (mu := mu) P001 P002 P003

-- graph edge: h_goal
example
    (P001 : (a : ℝ) * lam * (lam - 1) * (1 + 1 / lam ^ 2 + 1 / (lam - 1) ^ 2) = (a : ℝ) * (lam ^ 2 - lam) + 2 * (a : ℝ) + (a : ℝ) * ((a : ℝ) * lam + (b : ℝ)) / (c : ℝ) - (a : ℝ) * ((a : ℝ) * lam + (a : ℝ) + (b : ℝ)) / ((a : ℝ) + (b : ℝ) + (c : ℝ)))
    (P002 : (a : ℝ) * mu * (mu - 1) * (1 + 1 / mu ^ 2 + 1 / (mu - 1) ^ 2) = (a : ℝ) * (mu ^ 2 - mu) + 2 * (a : ℝ) + (a : ℝ) * ((a : ℝ) * mu + (-2 * (a : ℝ) - (b : ℝ))) / ((a : ℝ) + (b : ℝ) + (c : ℝ)) - (a : ℝ) * ((a : ℝ) * mu + (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ))) / ((a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) + ((a : ℝ) + (b : ℝ) + (c : ℝ))))
    (P003 : (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) + ((a : ℝ) + (b : ℝ) + (c : ℝ)) = (c : ℝ))
    (P004 : (a : ℝ) * (lam ^ 2 - lam) + (a : ℝ) * (mu ^ 2 - mu) = (b : ℝ) + (b : ℝ) ^ 2 / (a : ℝ) - 2 * (c : ℝ))
    (P005 : (a : ℝ) * ((a : ℝ) * lam + (b : ℝ)) / (c : ℝ) - (a : ℝ) * ((a : ℝ) * mu - (a : ℝ) - (b : ℝ)) / (c : ℝ) = (a : ℝ) * (b : ℝ) / (c : ℝ))
    (P006 : -(a : ℝ) * ((a : ℝ) * lam + (a : ℝ) + (b : ℝ)) / ((a : ℝ) + (b : ℝ) + (c : ℝ)) + (a : ℝ) * ((a : ℝ) * mu - 2 * (a : ℝ) - (b : ℝ)) / ((a : ℝ) + (b : ℝ) + (c : ℝ)) = -(a : ℝ) * (2 * (a : ℝ) + (b : ℝ)) / ((a : ℝ) + (b : ℝ) + (c : ℝ)))
    : (a : ℝ) * lam * (lam - 1) * (1 + 1 / lam ^ 2 + 1 / (lam - 1) ^ 2) + (a : ℝ) * mu * (mu - 1) * (1 + 1 / mu ^ 2 + 1 / (mu - 1) ^ 2) = 4 * (a : ℝ) + (b : ℝ) + (b : ℝ) ^ 2 / (a : ℝ) + (a : ℝ) * (b : ℝ) / (c : ℝ) - 2 * (c : ℝ) - (a : ℝ) * (2 * (a : ℝ) + (b : ℝ)) / ((a : ℝ) + (b : ℝ) + (c : ℝ)) := by
  exact P1662ConcreteSemanticGraph.edge_h_goal (a := a) (b := b) (c := c) (lam := lam) (mu := mu) P001 P002 P003 P004 P005 P006

end ConcreteGraphTypeBridge_p1662_binary_quadratic_form_volume_identity

end Rollout_p1662_binary_quadratic_form_volume_identity

namespace Rollout_p1722_hirzebruch_jung_large_entries_at_most_two

-- graph_id: p1722_hirzebruch_jung_large_entries_at_most_two
-- topology_sha256: 68ed2744cdb1d7035722b828fa61040478e1c5ad3b5b31aff3bcf59ad48149a7
/- accepted add_to_file helper 1 -/

def hjCont : List ℤ → ℤ × ℤ
  | [] => (1, 0)
  | x :: xs =>
      let y := hjCont xs
      (x * y.1 - y.2, y.1)

lemma hjCont_bounds (xs : List ℤ) (h : ∀ x ∈ xs, 2 ≤ x) :
    0 < (hjCont xs).1 ∧
    0 ≤ (hjCont xs).2 ∧
    (hjCont xs).2 ≤ (hjCont xs).1 ∧
    (xs.map fun x => x - 1).prod ≤ (hjCont xs).1 := by
  induction xs with
  | nil => simp [hjCont]
  | cons x xs ih =>
      have hx : 2 ≤ x := h x (by simp)
      have hxs : ∀ y ∈ xs, 2 ≤ y := fun y hy => h y (by simp [hy])
      rcases ih hxs with ⟨hu_pos, hv_nonneg, hvu, hprod⟩
      set u := (hjCont xs).1
      set v := (hjCont xs).2
      have hu_nonneg : 0 ≤ u := le_of_lt hu_pos
      have hxu : 2 * u ≤ x * u := mul_le_mul_of_nonneg_right hx hu_nonneg
      have hxm1_nonneg : 0 ≤ x - 1 := by linarith
      have hmul : (x - 1) * (xs.map fun y => y - 1).prod ≤ (x - 1) * u :=
        mul_le_mul_of_nonneg_left hprod hxm1_nonneg
      have hstep : (x - 1) * u ≤ x * u - v := by nlinarith
      simp [hjCont]
      constructor
      · nlinarith
      constructor
      · exact hu_nonneg
      constructor
      · nlinarith
      · exact le_trans hmul hstep

lemma hjCont_snd_pos_of_ne_nil (xs : List ℤ) (h : ∀ x ∈ xs, 2 ≤ x) (hne : xs ≠ []) :
    0 < (hjCont xs).2 := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
      simp [hjCont]
      exact (hjCont_bounds xs (fun y hy => h y (by simp [hy]))).1

lemma hjCont_gcd (xs : List ℤ) :
    (hjCont xs).1.gcd (hjCont xs).2 = 1 := by
  induction xs with
  | nil => simp [hjCont]
  | cons x xs ih =>
      simp [hjCont]
      rw [Int.gcd_comm]
      exact ih

lemma hj_fold_eq_div (xs : List ℤ) (h : ∀ x ∈ xs, 2 ≤ x) :
    (xs.map fun x : ℤ => (x : ℚ)).foldr (fun x r => x - 1 / r) 0 =
      ((hjCont xs).1 : ℚ) / ((hjCont xs).2 : ℚ) := by
  induction xs with
  | nil => simp [hjCont]
  | cons x xs ih =>
      have hxs : ∀ y ∈ xs, 2 ≤ y := fun y hy => h y (by simp [hy])
      have hb := hjCont_bounds xs hxs
      have hN : ((hjCont xs).1 : ℚ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hb.1)
      rw [List.map_cons, List.foldr_cons, ih hxs]
      simp [hjCont]
      field_simp [hN]

lemma triple_tail_sum_le_prod_add_two (x y z : ℤ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (t : List ℤ) (ht : ∀ w ∈ t, 1 ≤ w) :
    5 * (x + y + z + t.sum) ≤
      (x + 2) * (y + 2) * (z + 2) * (t.map fun u => u + 2).prod := by
  induction t with
  | nil =>
      simp
      nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy),
        mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hz),
        mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr hz)]
  | cons w t ih =>
      have hw : 1 ≤ w := ht w (by simp)
      have ht' : ∀ u ∈ t, 1 ≤ u := by
        intro u hu
        exact ht u (by simp [hu])
      have hS : 3 ≤ x + y + z + t.sum := by
        have hnon : 0 ≤ t.sum := List.sum_nonneg (by
          intro u hu
          exact le_trans (by norm_num : (0:ℤ) ≤ 1) (ht' u hu))
        nlinarith
      have hP := ih ht'
      simp [List.sum_cons, List.map_cons, List.prod_cons]
      nlinarith

lemma list_sum_le_prod_add_two (xs : List ℤ)
    (hpos : ∀ x ∈ xs, 1 ≤ x) (hlen : 3 ≤ xs.length) :
    5 * xs.sum ≤ (xs.map fun x => x + 2).prod := by
  have hne : xs ≠ [] := by
    intro h
    rw [h] at hlen
    norm_num at hlen
  rcases List.exists_cons_of_ne_nil hne with ⟨x, xs₁, rfl⟩
  have hlen₁ : 2 ≤ xs₁.length := by
    simpa using hlen
  have hne₁ : xs₁ ≠ [] := by
    intro h
    rw [h] at hlen₁
    norm_num at hlen₁
  rcases List.exists_cons_of_ne_nil hne₁ with ⟨y, xs₂, rfl⟩
  have hlen₂ : 1 ≤ xs₂.length := by
    simpa using hlen₁
  have hne₂ : xs₂ ≠ [] := by
    intro h
    rw [h] at hlen₂
    norm_num at hlen₂
  rcases List.exists_cons_of_ne_nil hne₂ with ⟨z, t, rfl⟩
  have hx : 1 ≤ x := hpos x (by simp)
  have hy : 1 ≤ y := hpos y (by simp)
  have hz : 1 ≤ z := hpos z (by simp)
  have ht : ∀ w ∈ t, 1 ≤ w := by
    intro w hw
    exact hpos w (by simp [hw])
  have h := triple_tail_sum_le_prod_add_two x y z hx hy hz t ht
  simpa [List.sum_cons, List.map_cons, List.prod_cons, add_assoc, add_comm, add_left_comm,
    mul_assoc] using h

lemma finset_five_sum_excess_le_prod_sub_one {n : ℕ} (a : Fin n → ℤ)
    (ha : ∀ i, 2 ≤ a i)
    (F : Finset (Fin n)) (hF : F ⊆ Finset.univ.filter (fun i => 3 < a i))
    (hcard : 3 ≤ F.card) :
    5 * ∑ i ∈ F, (a i - 3) ≤ ∏ i ∈ Finset.univ, (a i - 1) := by
  let xs := F.toList.map (fun i => a i - 3)
  have hpos : ∀ x ∈ xs, 1 ≤ x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
    have hiF : i ∈ F := by
      simpa using hi
    have hbig : 3 < a i := by
      have hiu : i ∈ Finset.univ.filter (fun j => 3 < a j) := hF hiF
      simpa using hiu
    linarith
  have hlen : 3 ≤ xs.length := by
    simp [xs, hcard]
  have hlist := list_sum_le_prod_add_two xs hpos hlen
  have hsum : xs.sum = ∑ i ∈ F, (a i - 3) := by
    simp [xs]
  have hprodF : (xs.map fun x => x + 2).prod = ∏ i ∈ F, (a i - 1) := by
    simp [xs]
    apply Finset.prod_congr rfl
    intro i hi
    ring
  have hFprod : 5 * ∑ i ∈ F, (a i - 3) ≤ ∏ i ∈ F, (a i - 1) := by
    simpa [hsum, hprodF] using hlist
  have hsubset : (∏ i ∈ F, (a i - 1)) ≤ ∏ i ∈ Finset.univ, (a i - 1) := by
    apply Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ F)
    · intro i hi
      have := ha i
      linarith
    · intro i hi hnot
      have := ha i
      linarith
  exact le_trans hFprod hsubset

/- verified submission -/
theorem hirzebruch_jung_large_entries_at_most_two
    (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℤ)
    (ha : ∀ i, 2 ≤ a i)
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q)
    (hfrac : (List.ofFn fun i => (a i : ℚ)).foldr
      (fun x r => x - 1 / r) 0 = (p : ℚ) / (q : ℚ))
    (hS : (2 * (p : ℚ)) / 9 <
      ∑ i ∈ Finset.univ.filter (fun i => 3 < a i), ((a i - 3 : ℤ) : ℚ)) :
    (Finset.univ.filter (fun i => 3 < a i)).card ≤ 2 := by
  by_contra hcardle
  have hcard3 : 3 ≤ (Finset.univ.filter (fun i => 3 < a i)).card := by
    omega
  let L : List ℤ := List.ofFn a
  have hL : ∀ x ∈ L, 2 ≤ x := by
    intro x hx
    rw [List.mem_ofFn] at hx
    rcases hx with ⟨i, rfl⟩
    exact ha i
  have hcomb := finset_five_sum_excess_le_prod_sub_one a ha
    (Finset.univ.filter (fun i => 3 < a i)) (fun i hi => hi) hcard3
  have hb := hjCont_bounds L hL
  have hprod_eq : (L.map fun x : ℤ => x - 1).prod = ∏ i ∈ Finset.univ, (a i - 1) := by
    simp [L, List.map_ofFn]
    rw [List.prod_ofFn]
    rfl
  have hSN : 5 * ∑ i ∈ Finset.univ.filter (fun i => 3 < a i), (a i - 3) ≤ (hjCont L).1 := by
    exact le_trans (by simpa [hprod_eq] using hcomb) hb.2.2.2
  have hcf : (List.ofFn fun i => (a i : ℚ)).foldr (fun x r => x - 1 / r) 0 =
      ((hjCont L).1 : ℚ) / ((hjCont L).2 : ℚ) := by
    simpa [L] using hj_fold_eq_div L hL
  have hLne : L ≠ [] := by
    intro hnil
    have hlen : L.length = n := by simp [L]
    have hzero : L.length = 0 := by simp [hnil]
    omega
  have hDpos : 0 < (hjCont L).2 := hjCont_snd_pos_of_ne_nil L hL hLne
  have hgcd : (hjCont L).1.gcd (hjCont L).2 = 1 := hjCont_gcd L
  have hco : (hjCont L).1.natAbs.Coprime (hjCont L).2.natAbs := by
    rw [Nat.coprime_iff_gcd_eq_one]
    simpa [Int.gcd] using hgcd
  have hNnum : (((hjCont L).1 : ℚ) / ((hjCont L).2 : ℚ)).num = (hjCont L).1 :=
    Rat.num_div_eq_of_coprime hDpos hco
  have hpqInt : ((p : ℤ).natAbs).Coprime ((q : ℤ).natAbs) := by
    simpa using hpq
  have hpnum : ((p : ℚ) / (q : ℚ)).num = (p : ℤ) := by
    have h := Rat.num_div_eq_of_coprime (show (0 : ℤ) < (q : ℤ) by exact_mod_cast hq) hpqInt
    simpa using h
  have hNp : (hjCont L).1 = (p : ℤ) := by
    calc
      (hjCont L).1 = (((hjCont L).1 : ℚ) / ((hjCont L).2 : ℚ)).num := hNnum.symm
      _ = ((p : ℚ) / (q : ℚ)).num := by
        congr 1
        exact hcf.symm.trans hfrac
      _ = (p : ℤ) := hpnum
  rw [hNp] at hSN
  let S : ℤ := ∑ i ∈ Finset.univ.filter (fun i => 3 < a i), (a i - 3)
  have hSNp : (5 : ℤ) * S ≤ (p : ℤ) := by
    simpa [S] using hSN
  have hSNq : (5 : ℚ) * (S : ℚ) ≤ (p : ℚ) := by
    exact_mod_cast hSNp
  have hsumq : (∑ i ∈ Finset.univ.filter (fun i => 3 < a i), ((a i - 3 : ℤ) : ℚ)) = (S : ℚ) := by
    simp [S]
  have hSq : (2 * (p : ℚ)) / 9 < (S : ℚ) := by
    rw [← hsumq]
    exact hS
  have hpqpos : 0 < (p : ℚ) := by
    exact_mod_cast hp
  nlinarith

end Rollout_p1722_hirzebruch_jung_large_entries_at_most_two

#check_dependency_graph "Rollout_p1722_hirzebruch_jung_large_entries_at_most_two.hirzebruch_jung_large_entries_at_most_two" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"{i | 3 < a i}.card ≤ 2\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hn\",\"statement\":\"1 ≤ n\"},{\"name\":\"ha\",\"statement\":\"∀ (i : Fin n), 2 ≤ a i\"},{\"name\":\"hp\",\"statement\":\"0 < p\"},{\"name\":\"hq\",\"statement\":\"0 < q\"},{\"name\":\"hpq\",\"statement\":\"p.Coprime q\"},{\"name\":\"hfrac\",\"statement\":\"List.foldr (fun x r => x - 1 / r) 0 (List.ofFn fun i => ↑(a i)) = ↑p / ↑q\"},{\"name\":\"hS\",\"statement\":\"2 * ↑p / 9 < ∑ i with 3 < a i, ↑(a i - 3)\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1722_hirzebruch_jung_large_entries_at_most_two\",\"reconstructedProofSha256\":\"a53b118b316b0c237f4fe8c3638b0137ad1475c8d729d90af9cb23d5b8d10a2d\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1722_hirzebruch_jung_large_entries_at_most_two.hirzebruch_jung_large_entries_at_most_two\",\"topologySha256\":\"68ed2744cdb1d7035722b828fa61040478e1c5ad3b5b31aff3bcf59ad48149a7\"}"

namespace Rollout_p1744_euler_congruence_for_counted_reduced_resid

-- graph_id: p1744_euler_congruence_for_counted_reduced_resid
-- topology_sha256: 28dc7b12bcf67d899a4a1555e8b39cf898bb49fb686730674b97db4492424394
/- verified submission -/
theorem euler_congruence_for_counted_reduced_residues
    (N x n : ℕ) (hN : 0 < N) (hx : 0 < x)
    (hcoprime : Nat.Coprime x N)
    (hn : n = ((Finset.Ico 1 N).filter fun a => Nat.Coprime a N).card) :
    Nat.ModEq N (x ^ n) 1 := by
  by_cases hN1 : N = 1
  · subst N
    exact Nat.modEq_one
  · have hNgt : 1 < N := by omega
    have hsets :
        ((Finset.Ico 1 N).filter fun a => Nat.Coprime a N) =
          {a ∈ Finset.Ico 1 (1 + N) | N.Coprime a} := by
      ext a
      constructor
      · intro ha
        simp only [Finset.mem_filter, Finset.mem_Ico] at ha ⊢
        exact ⟨⟨ha.1.1, by omega⟩, ha.2.symm⟩
      · intro ha
        simp only [Finset.mem_filter, Finset.mem_Ico] at ha ⊢
        have ha_ne_N : a ≠ N := by
          intro h
          subst a
          have : N = 1 := (Nat.coprime_self N).mp ha.2
          omega
        exact ⟨⟨ha.1.1, by omega⟩, ha.2.symm⟩
    have hcard :
        ((Finset.Ico 1 N).filter fun a => Nat.Coprime a N).card = N.totient := by
      rw [hsets]
      exact Nat.filter_coprime_Ico_eq_totient N 1
    rw [hn, hcard]
    exact Nat.ModEq.pow_totient hcoprime

end Rollout_p1744_euler_congruence_for_counted_reduced_resid

#check_dependency_graph "Rollout_p1744_euler_congruence_for_counted_reduced_resid.euler_congruence_for_counted_reduced_residues" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"x ^ n ≡ 1 [MOD N]\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hN\",\"statement\":\"0 < N\"},{\"name\":\"hcoprime\",\"statement\":\"x.Coprime N\"},{\"name\":\"hn\",\"statement\":\"n = {a ∈ Finset.Ico 1 N | a.Coprime N}.card\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1744_euler_congruence_for_counted_reduced_resid\",\"reconstructedProofSha256\":\"1fab907a4efa03c9aa258ec39f0faa5dc83e0c7859b990645fa94f15b921edf4\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1744_euler_congruence_for_counted_reduced_resid.euler_congruence_for_counted_reduced_residues\",\"topologySha256\":\"28dc7b12bcf67d899a4a1555e8b39cf898bb49fb686730674b97db4492424394\"}"

namespace Rollout_p1747_parbelos_area_and_vertex_parallelogram

-- graph_id: p1747_parbelos_area_and_vertex_parallelogram
-- topology_sha256: 37863b4fd33cabcaee6b1186d21487043328016f8acaea5ea618c19db6ea265c
/- accepted add_to_file helper 1 -/

open MeasureTheory Set

noncomputable def parbelosParallelogramMap (u w : ℝ × ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  (LinearMap.fst ℝ ℝ ℝ).smulRight u + (LinearMap.snd ℝ ℝ ℝ).smulRight w

noncomputable def parbelosParallelogramAffineMap (C u w : ℝ × ℝ) : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) :=
  AffineMap.const ℝ (ℝ × ℝ) C + (parbelosParallelogramMap u w).toAffineMap

lemma parbelosParallelogramMap_det (u w : ℝ × ℝ) :
    LinearMap.det (parbelosParallelogramMap u w) = u.1 * w.2 - w.1 * u.2 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ)]
  rw [Matrix.det_fin_two]
  simp [parbelosParallelogramMap, LinearMap.toMatrix_apply, Module.Basis.finTwoProd_zero,
    Module.Basis.finTwoProd_one]

lemma parbelos_unit_square_hull_eq_Icc :
    convexHull ℝ ({(0 : ℝ × ℝ), (1, 0), (1, 1), (0, 1)} : Set (ℝ × ℝ)) =
      Set.Icc (0, 0) (1, 1) := by
  have hprod :
      ({(0 : ℝ × ℝ), (1, 0), (1, 1), (0, 1)} : Set (ℝ × ℝ)) =
        ({(0 : ℝ), (1 : ℝ)} : Set ℝ) ×ˢ ({(0 : ℝ), (1 : ℝ)} : Set ℝ) := by
    ext p
    constructor
    · intro hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp
    · intro hp
      rcases hp with ⟨hp1, hp2⟩
      simp at hp1 hp2
      rcases hp1 with h1 | h1 <;> rcases hp2 with h2 | h2
      · left; ext <;> simp [h1, h2]
      · right; right; right; ext <;> simp [h1, h2]
      · right; left; ext <;> simp [h1, h2]
      · right; right; left; ext <;> simp [h1, h2]
  rw [hprod, convexHull_prod, convexHull_pair,
    segment_eq_Icc (zero_le_one : (0 : ℝ) ≤ 1), Set.Icc_prod_Icc]

lemma parbelos_volume_unit_square_hull :
    volume (convexHull ℝ ({(0 : ℝ × ℝ), (1, 0), (1, 1), (0, 1)} : Set (ℝ × ℝ))) = 1 := by
  rw [parbelos_unit_square_hull_eq_Icc]
  rw [← Set.Icc_prod_Icc]
  rw [Measure.volume_eq_prod]
  rw [Measure.prod_prod]
  simp [Real.volume_Icc]

lemma parbelosParallelogramAffineMap_image_hull (C u w : ℝ × ℝ) :
    parbelosParallelogramAffineMap C u w ''
      convexHull ℝ ({(0 : ℝ × ℝ), (1, 0), (1, 1), (0, 1)} : Set (ℝ × ℝ)) =
      convexHull ℝ ({C, C + u, C + u + w, C + w} : Set (ℝ × ℝ)) := by
  rw [AffineMap.image_convexHull]
  congr 1
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases hq with rfl | rfl | rfl | rfl <;>
      simp [parbelosParallelogramAffineMap, parbelosParallelogramMap, add_assoc]
  · intro hp
    rcases hp with rfl | rfl | rfl | rfl
    · refine ⟨(0, 0), by simp, ?_⟩
      simp [parbelosParallelogramAffineMap, parbelosParallelogramMap]
    · refine ⟨(1, 0), by simp, ?_⟩
      simp [parbelosParallelogramAffineMap, parbelosParallelogramMap]
    · refine ⟨(1, 1), by simp, ?_⟩
      simp [parbelosParallelogramAffineMap, parbelosParallelogramMap, add_assoc]
    · refine ⟨(0, 1), by simp, ?_⟩
      simp [parbelosParallelogramAffineMap, parbelosParallelogramMap]

lemma parbelos_volume_hull_parallelogram (C u w : ℝ × ℝ) :
    volume (convexHull ℝ ({C, C + u, C + u + w, C + w} : Set (ℝ × ℝ))) =
      ENNReal.ofReal |u.1 * w.2 - w.1 * u.2| := by
  let Q : Set (ℝ × ℝ) :=
    convexHull ℝ ({(0 : ℝ × ℝ), (1, 0), (1, 1), (0, 1)} : Set (ℝ × ℝ))
  let A : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) := parbelosParallelogramMap u w
  have hset : convexHull ℝ ({C, C + u, C + u + w, C + w} : Set (ℝ × ℝ)) =
      (AffineMap.const ℝ (ℝ × ℝ) C + A.toAffineMap) '' Q := by
    symm
    exact parbelosParallelogramAffineMap_image_hull C u w
  rw [hset]
  have hcomp :
      (AffineMap.const ℝ (ℝ × ℝ) C + A.toAffineMap) '' Q =
        (fun p => C + p) '' (A '' Q) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨A q, ⟨q, hq, rfl⟩, by rfl⟩
    · rintro ⟨q, ⟨r, hr, rfl⟩, rfl⟩
      exact ⟨r, hr, by rfl⟩
  rw [hcomp]
  have htrans : volume ((fun p : ℝ × ℝ => C + p) '' (A '' Q)) = volume (A '' Q) := by
    have h := measure_preimage_add (μ := volume) C ((fun p : ℝ × ℝ => C + p) '' (A '' Q))
    have hpre : (fun p : ℝ × ℝ => C + p) ⁻¹'
        ((fun p : ℝ × ℝ => C + p) '' (A '' Q)) = A '' Q := by
      exact Set.preimage_image_eq _ (add_right_injective C)
    rw [hpre] at h
    exact h.symm
  rw [htrans]
  rw [Measure.addHaar_image_linearMap]
  have hA : LinearMap.det A = u.1 * w.2 - w.1 * u.2 := by
    exact parbelosParallelogramMap_det u w
  have hQ : volume Q = 1 := by
    exact parbelos_volume_unit_square_hull
  rw [hA, hQ]
  simp

lemma parbelos_volume_between_Icc
    {l u : ℝ} (hlu : l ≤ u) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x ∈ Set.Icc l u, f x ≤ g x) :
    volume {p : ℝ × ℝ | l ≤ p.1 ∧ p.1 ≤ u ∧ f p.1 ≤ p.2 ∧ p.2 ≤ g p.1} =
      ENNReal.ofReal (∫ x in l..u, g x - f x) := by
  let S : Set (ℝ × ℝ) := {p | l ≤ p.1 ∧ p.1 ≤ u ∧ f p.1 ≤ p.2 ∧ p.2 ≤ g p.1}
  have hS : MeasurableSet S := by
    dsimp [S]
    measurability
  change volume S = ENNReal.ofReal (∫ x in l..u, g x - f x)
  rw [Measure.volume_eq_prod]
  rw [Measure.prod_apply hS]
  have hsec : ∀ x : ℝ,
      volume (Prod.mk x ⁻¹' S) =
        (Set.Icc l u).indicator (fun x => ENNReal.ofReal (g x - f x)) x := by
    intro x
    by_cases hx : x ∈ Set.Icc l u
    · have hpre : Prod.mk x ⁻¹' S = Set.Icc (f x) (g x) := by
        ext y
        constructor
        · intro hy
          exact hy.2.2
        · intro hy
          exact ⟨hx.1, hx.2, hy⟩
      rw [hpre, Set.indicator_of_mem hx, Real.volume_Icc]
    · have hpre : Prod.mk x ⁻¹' S = (∅ : Set ℝ) := by
        ext y
        constructor
        · intro hy
          exact (hx ⟨hy.1, hy.2.1⟩).elim
        · intro hy
          cases hy
      rw [hpre, Set.indicator_of_notMem hx]
      simp
  rw [lintegral_congr hsec]
  rw [lintegral_indicator measurableSet_Icc]
  have hfi : Integrable (fun x => g x - f x) (volume.restrict (Set.Icc l u)) := by
    exact (hg.sub hf).integrableOn_Icc
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc l u)] fun x => g x - f x := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact sub_nonneg.mpr (hfg x hx)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfi hnn]
  congr 1
  have hintegral :
      (∫ x, g x - f x ∂(volume.restrict (Set.Icc l u))) =
        ∫ x in l..u, g x - f x := by
    calc
      (∫ x, g x - f x ∂(volume.restrict (Set.Icc l u))) =
          ∫ x in Set.Icc l u, g x - f x := by rfl
      _ = ∫ x in Set.Ioc l u, g x - f x := by
        exact integral_Icc_eq_integral_Ioc' (μ := volume) (by simp)
      _ = ∫ x in l..u, g x - f x := by
        exact (intervalIntegral.integral_of_le hlu).symm
  exact hintegral

/- accepted add_to_file helper 2 -/
lemma parbelos_region_volume_explicit
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b < 2 * a) :
    volume {p : ℝ × ℝ |
      (0 ≤ p.1 ∧ p.1 ≤ 2 * b ∧
        b / 2 - (p.1 - b) ^ 2 / (2 * b) ≤ p.2 ∧
        p.2 ≤ a - (p.1 - 2 * a) ^ 2 / (4 * a)) ∨
      (2 * b ≤ p.1 ∧ p.1 ≤ 4 * a ∧
        (2 * a - b) / 2 - (p.1 - (2 * a + b)) ^ 2 / (2 * (2 * a - b)) ≤ p.2 ∧
        p.2 ≤ a - (p.1 - 2 * a) ^ 2 / (4 * a))} =
      ENNReal.ofReal (4 * b * (2 * a - b) / 3) := by
  let U : ℝ → ℝ := fun x => a - (x - 2 * a) ^ 2 / (4 * a)
  let L : ℝ → ℝ := fun x => b / 2 - (x - b) ^ 2 / (2 * b)
  let R : ℝ → ℝ := fun x =>
    (2 * a - b) / 2 - (x - (2 * a + b)) ^ 2 / (2 * (2 * a - b))
  let P₁ : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 2 * b ∧ L p.1 ≤ p.2 ∧ p.2 ≤ U p.1}
  let P₂ : Set (ℝ × ℝ) :=
    {p | 2 * b ≤ p.1 ∧ p.1 ≤ 4 * a ∧ R p.1 ≤ p.2 ∧ p.2 ≤ U p.1}
  set c : ℝ := 2 * a - b
  have hcpos : 0 < c := by
    dsimp [c]
    exact sub_pos.mpr hba
  have hc : c ≠ 0 := ne_of_gt hcpos
  have hcdef : c = 2 * a - b := rfl
  have hUcont : Continuous U := by
    dsimp [U]
    continuity
  have hLcont : Continuous L := by
    dsimp [L]
    continuity
  have hRcont : Continuous R := by
    dsimp [R]
    continuity
  have hUL : ∀ x : ℝ, U x - L x = (c / (4 * a * b)) * x ^ 2 := by
    intro x
    dsimp [U, L]
    field_simp [ha.ne', hb.ne']
    rw [hcdef]
    ring
  have hUR : ∀ x : ℝ, U x - R x = (b / (4 * a * c)) * (4 * a - x) ^ 2 := by
    intro x
    dsimp [U, R]
    rw [← hcdef]
    field_simp [ha.ne', hc]
    rw [hcdef]
    ring
  have hUL_nonneg : ∀ x : ℝ, 0 ≤ U x - L x := by
    intro x
    rw [hUL x]
    positivity
  have hUR_nonneg : ∀ x : ℝ, 0 ≤ U x - R x := by
    intro x
    rw [hUR x]
    positivity
  have hI₁ : ∫ x in (0 : ℝ)..(2 * b), U x - L x = 2 * b ^ 2 * c / (3 * a) := by
    calc
      ∫ x in (0 : ℝ)..(2 * b), U x - L x
          = ∫ x in (0 : ℝ)..(2 * b), (c / (4 * a * b)) * x ^ 2 := by
            apply intervalIntegral.integral_congr
            intro x hx
            exact hUL x
      _ = 2 * b ^ 2 * c / (3 * a) := by
            rw [intervalIntegral.integral_const_mul, integral_pow]
            field_simp [ha.ne', hb.ne']
            ring
  have hI₂ : ∫ x in (2 * b)..(4 * a), U x - R x = 2 * b * c ^ 2 / (3 * a) := by
    calc
      ∫ x in (2 * b)..(4 * a), U x - R x
          = ∫ x in (2 * b)..(4 * a), (b / (4 * a * c)) * (4 * a - x) ^ 2 := by
            apply intervalIntegral.integral_congr
            intro x hx
            exact hUR x
      _ = ∫ x in (0 : ℝ)..(4 * a - 2 * b), (b / (4 * a * c)) * x ^ 2 := by
            have hsub :=
              intervalIntegral.integral_comp_sub_left
                (a := 2 * b) (b := 4 * a)
                (f := fun x : ℝ => (b / (4 * a * c)) * x ^ 2) (d := 4 * a)
            convert hsub using 2 <;> ring
      _ = 2 * b * c ^ 2 / (3 * a) := by
            rw [intervalIntegral.integral_const_mul, integral_pow]
            field_simp [ha.ne', hc]
            rw [hcdef]
            ring
  have hP₁vol : volume P₁ = ENNReal.ofReal (∫ x in (0 : ℝ)..(2 * b), U x - L x) := by
    apply parbelos_volume_between_Icc
    · positivity
    · exact hLcont
    · exact hUcont
    · intro x hx
      exact sub_nonneg.mp (hUL_nonneg x)
  have hP₂vol : volume P₂ = ENNReal.ofReal (∫ x in (2 * b)..(4 * a), U x - R x) := by
    apply parbelos_volume_between_Icc
    · nlinarith
    · exact hRcont
    · exact hUcont
    · intro x hx
      exact sub_nonneg.mp (hUR_nonneg x)
  have hP₂meas : MeasurableSet P₂ := by
    dsimp [P₂, U, R]
    measurability
  have hline : volume ({p : ℝ × ℝ | p.1 = 2 * b}) = 0 := by
    have hset : ({p : ℝ × ℝ | p.1 = 2 * b}) = ({2 * b} : Set ℝ) ×ˢ Set.univ := by
      ext p
      simp
    rw [hset, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hinter : volume (P₁ ∩ P₂) = 0 := by
    apply measure_mono_null _ hline
    intro p hp
    exact le_antisymm hp.1.2.1 hp.2.1
  have hPunion : volume (P₁ ∪ P₂) = volume P₁ + volume P₂ := by
    have h := measure_union_add_inter (μ := volume) P₁ hP₂meas
    rw [hinter, add_zero] at h
    exact h
  change volume (P₁ ∪ P₂) = ENNReal.ofReal (4 * b * (2 * a - b) / 3)
  rw [hPunion, hP₁vol, hP₂vol, hI₁, hI₂]
  have hI₁_nonneg : 0 ≤ 2 * b ^ 2 * c / (3 * a) := by positivity
  have hI₂_nonneg : 0 ≤ 2 * b * c ^ 2 / (3 * a) := by positivity
  rw [← ENNReal.ofReal_add hI₁_nonneg hI₂_nonneg]
  congr 1
  rw [hcdef]
  field_simp [ha.ne']
  ring

/- verified submission -/
theorem parbelos_area_and_vertex_parallelogram
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b < 2 * a) :
    let C₁ : ℝ × ℝ := (0, 0)
    let C₂ : ℝ × ℝ := (2 * b, 0)
    let C₃ : ℝ × ℝ := (4 * a, 0)
    let U : ℝ → ℝ := fun x => a - (x - 2 * a) ^ 2 / (4 * a)
    let L : ℝ → ℝ := fun x => b / 2 - (x - b) ^ 2 / (2 * b)
    let R : ℝ → ℝ := fun x => (2 * a - b) / 2 - (x - (2 * a + b)) ^ 2 / (2 * (2 * a - b))
    let P : Set (ℝ × ℝ) := {p | (0 ≤ p.1 ∧ p.1 ≤ 2 * b ∧ L p.1 ≤ p.2 ∧ p.2 ≤ U p.1) ∨
      (2 * b ≤ p.1 ∧ p.1 ≤ 4 * a ∧ R p.1 ≤ p.2 ∧ p.2 ≤ U p.1)}
    let V₁ : ℝ × ℝ := (b, b / 2)
    let V₂ : ℝ × ℝ := (2 * a, a)
    let V₃ : ℝ × ℝ := (2 * a + b, a - b / 2)
    (V₁ - C₂ = V₂ - V₃ ∧ V₂ - V₁ = V₃ - C₂) ∧
      MeasureTheory.volume P = (4 / 3 : ENNReal) * MeasureTheory.volume (convexHull ℝ ({C₂, V₁, V₂, V₃} : Set (ℝ × ℝ))) := by
  dsimp
  constructor
  · constructor
    · ext <;> ring
    · ext <;> ring
  · rw [parbelos_region_volume_explicit a b ha hb hba]
    let C : ℝ × ℝ := (2 * b, 0)
    let u : ℝ × ℝ := (2 * a + b, a - b / 2) - (2 * b, 0)
    let w : ℝ × ℝ := (b, b / 2) - (2 * b, 0)
    have hpoints :
        ({(2 * b, 0), (b, b / 2), (2 * a, a), (2 * a + b, a - b / 2)} : Set (ℝ × ℝ)) =
          ({C, C + u, C + u + w, C + w} : Set (ℝ × ℝ)) := by
      ext p
      simp [C, u, w]
      constructor
      · intro hp
        rcases hp with rfl | rfl | rfl | rfl
        · left; rfl
        · right; right; right; ext <;> ring
        · right; right; left; ext <;> ring
        · right; left; ext <;> ring
      · intro hp
        rcases hp with rfl | rfl | rfl | rfl
        · left; rfl
        · right; right; right; ext <;> ring
        · right; right; left; ext <;> ring
        · right; left; ext <;> ring
    rw [hpoints, parbelos_volume_hull_parallelogram C u w]
    have hc : 0 ≤ b * (2 * a - b) := by
      have hcpos : 0 ≤ 2 * a - b := le_of_lt (sub_pos.mpr hba)
      exact mul_nonneg (le_of_lt hb) hcpos
    have hdet : u.1 * w.2 - w.1 * u.2 = b * (2 * a - b) := by
      dsimp [u, w]
      ring
    rw [hdet, abs_of_nonneg hc]
    have h43 : (4 / 3 : ENNReal) = ENNReal.ofReal ((4 / 3 : ℝ)) := by
      rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 3 by norm_num)]
      norm_num
    rw [h43, (ENNReal.ofReal_mul (show (0 : ℝ) ≤ (4 / 3) by norm_num)).symm]
    congr 1
    ring

end Rollout_p1747_parbelos_area_and_vertex_parallelogram

#check_dependency_graph "Rollout_p1747_parbelos_area_and_vertex_parallelogram.parbelos_area_and_vertex_parallelogram" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let C₁ := (0, 0); let C₂ := (2 * b, 0); let C₃ := (4 * a, 0); let U := fun x => a - (x - 2 * a) ^ 2 / (4 * a); let L := fun x => b / 2 - (x - b) ^ 2 / (2 * b); let R := fun x => (2 * a - b) / 2 - (x - (2 * a + b)) ^ 2 / (2 * (2 * a - b)); let P := {p | 0 ≤ p.1 ∧ p.1 ≤ 2 * b ∧ L p.1 ≤ p.2 ∧ p.2 ≤ U p.1 ∨ 2 * b ≤ p.1 ∧ p.1 ≤ 4 * a ∧ R p.1 ≤ p.2 ∧ p.2 ≤ U p.1}; let V₁ := (b, b / 2); let V₂ := (2 * a, a); let V₃ := (2 * a + b, a - b / 2); (V₁ - C₂ = V₂ - V₃ ∧ V₂ - V₁ = V₃ - C₂) ∧ MeasureTheory.volume P = 4 / 3 * MeasureTheory.volume ((convexHull ℝ) {C₂, V₁, V₂, V₃})\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"ha\",\"statement\":\"0 < a\"},{\"name\":\"hb\",\"statement\":\"0 < b\"},{\"name\":\"hba\",\"statement\":\"b < 2 * a\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1747_parbelos_area_and_vertex_parallelogram\",\"reconstructedProofSha256\":\"fb64baee342f6ca6046425f908f95376c7ec5e66a944a656042694d75f63beed\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1747_parbelos_area_and_vertex_parallelogram.parbelos_area_and_vertex_parallelogram\",\"topologySha256\":\"37863b4fd33cabcaee6b1186d21487043328016f8acaea5ea618c19db6ea265c\"}"

namespace Rollout_p1776_subgroup_isup_eq_boolean_isup

-- graph_id: p1776_subgroup_isup_eq_boolean_isup
-- topology_sha256: fb662cf9564d5c688def1900e978d2b19b77ef282febb3dedb4a33e5a1159239
/- accepted add_to_file helper 1 -/
def booleanCoeffRank (n : ℤ) : ℕ := (2 * n - 1).natAbs

lemma booleanCoeffRank_reflect (n : ℤ) (hn : ¬ (n = 0 ∨ n = 1)) :
    booleanCoeffRank (if 2 ≤ n then 2 - n else -n) < booleanCoeffRank n := by
  by_cases h : 2 ≤ n
  · simp [booleanCoeffRank, h]
    have hl : ((2 * (2 - n) - 1).natAbs : ℤ) = -(2 * (2 - n) - 1) := by
      have hnon : 0 ≤ -(2 * (2 - n) - 1) := by omega
      have habs := Int.natAbs_of_nonneg hnon
      rwa [Int.natAbs_neg] at habs
    have hr : ((2 * n - 1).natAbs : ℤ) = 2 * n - 1 := by
      exact Int.natAbs_of_nonneg (by omega)
    omega
  · simp [booleanCoeffRank, h]
    have hnlt : n < 0 := by omega
    have hl : ((2 * -n - 1).natAbs : ℤ) = 2 * -n - 1 := by
      exact Int.natAbs_of_nonneg (by omega)
    have hr : ((2 * n - 1).natAbs : ℤ) = -(2 * n - 1) := by
      have hnon : 0 ≤ -(2 * n - 1) := by omega
      have habs := Int.natAbs_of_nonneg hnon
      rwa [Int.natAbs_neg] at habs
    omega

lemma subgroup_le_sup_of_set_prod {U A : Type*} [Group U] [AddCommGroup A]
    (W : A → Subgroup U)
    (hprod : ∀ x y : A,
      (W x : Set U) ⊆ Set.image2 (fun g h : U => g * h) (W y : Set U)
        (W (2 • y - x) : Set U))
    (x y : A) :
    W x ≤ W y ⊔ W (2 • y - x) := by
  rw [← SetLike.coe_subset_coe]
  intro g hg
  rcases hprod x y hg with ⟨g₁, hg₁, g₂, hg₂, rfl⟩
  exact Subgroup.mul_mem _
    (SetLike.le_def.mp le_sup_left hg₁)
    (SetLike.le_def.mp le_sup_right hg₂)

/- accepted add_to_file helper 2 -/
lemma subgroup_le_boolean_iSup_of_int_coeffs {U A : Type*} [Group U] [AddCommGroup A]
    {m : ℕ} (a : Fin m → A) (W : A → Subgroup U)
    (hprod : ∀ x y : A,
      (W x : Set U) ⊆ Set.image2 (fun g h : U => g * h) (W y : Set U)
        (W (2 • y - x) : Set U))
    (n : Fin m → ℤ) :
    W (∑ i, n i • a i) ≤ ⨆ s : Finset (Fin m), W (∑ i ∈ s, a i) := by
  let rank : (Fin m → ℤ) → ℕ := fun c => ∑ i, booleanCoeffRank (c i)
  refine (InvImage.wf rank Nat.lt_wfRel.wf).fix
    (C := fun c : Fin m → ℤ =>
      W (∑ i, c i • a i) ≤ ⨆ s : Finset (Fin m), W (∑ i ∈ s, a i))
    (fun n ih => ?_) n
  have base_of_boolean : ∀ c : Fin m → ℤ, (∀ i, c i = 0 ∨ c i = 1) →
      W (∑ i, c i • a i) ≤ ⨆ s : Finset (Fin m), W (∑ i ∈ s, a i) := by
    intro c hc
    have hsum : (∑ i, c i • a i) =
        ∑ i ∈ Finset.univ.filter (fun i => c i = 1), a i := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      rcases hc i with h | h <;> simp [h]
    rw [hsum]
    exact le_iSup (fun s : Finset (Fin m) => W (∑ i ∈ s, a i))
      (Finset.univ.filter fun i => c i = 1)
  by_cases hb : ∀ i, n i = 0 ∨ n i = 1
  · exact base_of_boolean n hb
  · push_neg at hb
    rcases hb with ⟨j, hj⟩
    have hjnot : ¬ (n j = 0 ∨ n j = 1) := by
      intro h
      rcases h with h | h
      · exact hj.1 h
      · exact hj.2 h
    let b : Fin m → ℤ := fun i =>
      if h : n i = 0 ∨ n i = 1 then n i else if 2 ≤ n i then 1 else 0
    let n' : Fin m → ℤ := fun i => 2 * b i - n i
    have hb01 : ∀ i, b i = 0 ∨ b i = 1 := by
      intro i
      by_cases hgood : n i = 0 ∨ n i = 1
      · simpa [b, hgood] using hgood
      · by_cases htwo : 2 ≤ n i
        · simp [b, hgood, htwo]
        · simp [b, hgood, htwo]
    have hcoord_le : ∀ i, booleanCoeffRank (n' i) ≤ booleanCoeffRank (n i) := by
      intro i
      by_cases hgood : n i = 0 ∨ n i = 1
      · have hn'i : n' i = n i := by
          simp [n', b, hgood]
          ring
        rw [hn'i]
      · have hlt := booleanCoeffRank_reflect (n i) hgood
        by_cases htwo : 2 ≤ n i
        · have hn'i : n' i = 2 - n i := by
            simp [n', b, hgood, htwo]
          rw [hn'i]
          simpa [htwo] using le_of_lt hlt
        · have hn'i : n' i = -n i := by
            simp [n', b, hgood, htwo]
          rw [hn'i]
          simpa [htwo] using le_of_lt hlt
    have hcoord_j : booleanCoeffRank (n' j) < booleanCoeffRank (n j) := by
      have hlt := booleanCoeffRank_reflect (n j) hjnot
      by_cases htwo : 2 ≤ n j
      · have hn'j : n' j = 2 - n j := by
          simp [n', b, hjnot, htwo]
        rw [hn'j]
        simpa [htwo] using hlt
      · have hn'j : n' j = -n j := by
          simp [n', b, hjnot, htwo]
        rw [hn'j]
        simpa [htwo] using hlt
    have hrank : rank n' < rank n := by
      dsimp [rank]
      exact Finset.sum_lt_sum (fun i hi => hcoord_le i) ⟨j, Finset.mem_univ j, hcoord_j⟩
    have hz : W (∑ i, n' i • a i) ≤ ⨆ s : Finset (Fin m), W (∑ i ∈ s, a i) :=
      ih n' hrank
    have hy : W (∑ i, b i • a i) ≤ ⨆ s : Finset (Fin m), W (∑ i ∈ s, a i) :=
      base_of_boolean b hb01
    have hlin : (∑ i, n' i • a i) =
        2 • (∑ i, b i • a i) - ∑ i, n i • a i := by
      trans ∑ i, ((2 * b i) • a i - n i • a i)
      · apply Finset.sum_congr rfl
        intro i hi
        rw [sub_smul]
      · rw [Finset.sum_sub_distrib]
        congr 1
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [show 2 * b i = b i + b i by ring, add_smul, two_nsmul]
    have hx_sup := subgroup_le_sup_of_set_prod W hprod
      (∑ i, n i • a i) (∑ i, b i • a i)
    rw [← hlin] at hx_sup
    exact hx_sup.trans (sup_le hy hz)

/- verified submission -/
theorem subgroup_iSup_eq_boolean_iSup
    {U A : Type*} [Group U] [AddCommGroup A] {m : ℕ}
    (a : Fin m → A) (W : A → Subgroup U)
    (hgen : AddSubgroup.closure (Set.range a) = ⊤)
    (hcomm : ∀ x : A, commutator U ≤ W x)
    (hprod : ∀ x y : A,
      (W x : Set U) ⊆ Set.image2 (fun g h : U => g * h) (W y : Set U)
        (W (2 • y - x) : Set U)) :
    (⨆ x : A, W x) = ⨆ s : Finset (Fin m), W (∑ i ∈ s, a i) := by
  apply le_antisymm
  · apply iSup_le
    intro x
    have hx : x ∈ AddSubgroup.closure (Set.range a) := by
      rw [hgen]
      trivial
    rcases AddSubgroup.mem_closure_range_iff.mp hx with ⟨c, hc⟩
    rw [Finsupp.sum_zsmul] at hc
    rw [hc]
    exact subgroup_le_boolean_iSup_of_int_coeffs a W hprod c
  · apply iSup_le
    intro s
    exact le_iSup (fun x : A => W x) (∑ i ∈ s, a i)

end Rollout_p1776_subgroup_isup_eq_boolean_isup

#check_dependency_graph "Rollout_p1776_subgroup_isup_eq_boolean_isup.subgroup_iSup_eq_boolean_iSup" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"⨆ x, W x = ⨆ s, W (∑ i ∈ s, a i)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hgen\",\"statement\":\"AddSubgroup.closure (Set.range a) = ⊤\"},{\"name\":\"hprod\",\"statement\":\"∀ (x y : A), ↑(W x) ⊆ Set.image2 (fun g h => g * h) ↑(W y) ↑(W (2 • y - x))\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1776_subgroup_isup_eq_boolean_isup\",\"reconstructedProofSha256\":\"d06b8896b7fced31f655f2cff254896f322a38af68ef9b4156b5e6a60c7f2dcc\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1776_subgroup_isup_eq_boolean_isup.subgroup_iSup_eq_boolean_iSup\",\"topologySha256\":\"fb662cf9564d5c688def1900e978d2b19b77ef282febb3dedb4a33e5a1159239\"}"

namespace Rollout_p1808_uniform_excision_implies_coarse_excision

-- graph_id: p1808_uniform_excision_implies_coarse_excision
-- topology_sha256: 9943d8a4477aad14cf2e09eabf976b18caee95156b6751314b607bb9d2607bee
/- accepted add_to_file helper 1 -/
def ueRelPow {X : Type*} (W : SetRel X X) : ℕ → SetRel X X
  | 0 => SetRel.id
  | n + 1 => (ueRelPow W n).comp W

lemma ueRel_comp_mono {X : Type*} {R₁ R₂ S₁ S₂ : SetRel X X}
    (hR : R₁ ⊆ R₂) (hS : S₁ ⊆ S₂) : R₁.comp S₁ ⊆ R₂.comp S₂ := by
  intro p hp
  rcases hp with ⟨x, hpR, hpS⟩
  exact ⟨x, hR hpR, hS hpS⟩

lemma ueRel_inv_subset {X : Type*} {R S : SetRel X X} (h : R ⊆ S) : R.inv ⊆ S.inv := by
  intro p hp
  exact h hp

lemma ueRel_image_subset {X : Type*} {R S : SetRel X X} (h : R ⊆ S) (A : Set X) :
    R.image A ⊆ S.image A := by
  intro x hx
  rcases hx with ⟨a, haA, hax⟩
  exact ⟨a, haA, h hax⟩

lemma ueRelPow_id_subset {X : Type*} {W : SetRel X X} (hW : SetRel.id ⊆ W) :
    ∀ n : ℕ, SetRel.id ⊆ ueRelPow W n
  | 0 => by intro p hp; exact hp
  | n + 1 => by
      intro p hp
      have hp1 : p ∈ ueRelPow W n := ueRelPow_id_subset hW n hp
      rcases p with ⟨x, y⟩
      exact ⟨y, hp1, hW (by rfl : (y, y) ∈ SetRel.id)⟩

lemma ueRelPow_subset_succ {X : Type*} {W : SetRel X X} (hW : SetRel.id ⊆ W) (n : ℕ) :
    ueRelPow W n ⊆ ueRelPow W (n + 1) := by
  intro p hp
  rcases p with ⟨x, y⟩
  exact ⟨y, hp, hW (by rfl : (y, y) ∈ SetRel.id)⟩

lemma ueRelPow_mono {X : Type*} {W : SetRel X X} (hW : SetRel.id ⊆ W) :
    ∀ {m n : ℕ}, m ≤ n → ueRelPow W m ⊆ ueRelPow W n := by
  intro m n hmn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hadd : ∀ k : ℕ, ueRelPow W m ⊆ ueRelPow W (m + k) := by
    intro k
    induction k with
    | zero => intro p hp; exact hp
    | succ k ih =>
        intro p hp
        exact ueRelPow_subset_succ hW (m + k) (ih hp)
  exact hadd k

lemma ueRelPow_comp_subset {X : Type*} (W : SetRel X X) :
    ∀ m n : ℕ, (ueRelPow W m).comp (ueRelPow W n) ⊆ ueRelPow W (m + n) := by
  intro m n
  induction n with
  | zero =>
      intro p hp
      simpa [ueRelPow] using hp
  | succ n ih =>
      intro p hp
      have hp' : p ∈ ((ueRelPow W m).comp (ueRelPow W n)).comp W := by
        simpa [ueRelPow, SetRel.comp_assoc] using hp
      rcases hp' with ⟨y, hy₁, hy₂⟩
      exact ⟨y, ih hy₁, hy₂⟩

lemma ueRelPow_left_subset {X : Type*} (W : SetRel X X) :
    ∀ n : ℕ, W.comp (ueRelPow W n) ⊆ ueRelPow W (n + 1) := by
  intro n
  induction n with
  | zero =>
      intro p hp
      rcases hp with ⟨y, hyW, hyid⟩
      rcases p with ⟨x, z⟩
      change y = z at hyid
      subst z
      exact ⟨x, by rfl, hyW⟩
  | succ n ih =>
      intro p hp
      have hp' : p ∈ (W.comp (ueRelPow W n)).comp W := by
        simpa [ueRelPow, SetRel.comp_assoc] using hp
      rcases hp' with ⟨y, hy₁, hy₂⟩
      exact ⟨y, ih hy₁, hy₂⟩

lemma ueRelPow_inv_subset {X : Type*} {W : SetRel X X} (hW : W.inv ⊆ W) :
    ∀ n : ℕ, (ueRelPow W n).inv ⊆ ueRelPow W n := by
  intro n
  induction n with
  | zero =>
      intro p hp
      rcases p with ⟨x, y⟩
      change (y, x) ∈ SetRel.id at hp
      change y = x at hp
      subst x
      exact by rfl
  | succ n ih =>
      intro p hp
      have hp' : p ∈ W.inv.comp (ueRelPow W n).inv := by
        simpa [ueRelPow, SetRel.inv_comp] using hp
      have hp'' : p ∈ W.comp (ueRelPow W n) :=
        (ueRel_comp_mono hW ih) hp'
      exact ueRelPow_left_subset W n hp''

lemma ue_boundary {X : Type*} {A B : Set X} {W K : SetRel X X}
    (hAB : A ∪ B = Set.univ) (hrefl : SetRel.id ⊆ W)
    (hex : W.image A ∩ W.image B ⊆ K.image (A ∩ B)) :
    ∀ (n : ℕ) {a b : X}, a ∈ A → b ∈ B → (a, b) ∈ ueRelPow W n →
      b ∈ (K.comp (ueRelPow W n)).image (A ∩ B) := by
  intro n
  induction n with
  | zero =>
      intro a b ha hb hab
      change a = b at hab
      subst b
      have haW : a ∈ W.image A := ⟨a, ha, hrefl (by rfl : (a, a) ∈ SetRel.id)⟩
      have hbW : a ∈ W.image B := ⟨a, hb, hrefl (by rfl : (a, a) ∈ SetRel.id)⟩
      have hK : a ∈ K.image (A ∩ B) := hex ⟨haW, hbW⟩
      simpa [ueRelPow, SetRel.comp_id] using hK
  | succ n ih =>
      intro a b ha hb hab
      rcases hab with ⟨y, hay, hyb⟩
      have hyAB : y ∈ A ∪ B := by
        have : y ∈ (Set.univ : Set X) := Set.mem_univ y
        simpa [hAB] using this
      rcases hyAB with hyA | hyB
      · have hbWA : b ∈ W.image A := ⟨y, hyA, hyb⟩
        have hbWB : b ∈ W.image B := ⟨b, hb, hrefl (by rfl : (b, b) ∈ SetRel.id)⟩
        have hbK : b ∈ K.image (A ∩ B) := hex ⟨hbWA, hbWB⟩
        rcases hbK with ⟨c, hcAB, hcb⟩
        refine ⟨c, hcAB, ?_⟩
        exact ⟨b, hcb, ueRelPow_id_subset hrefl (n + 1) (by rfl : (b, b) ∈ SetRel.id)⟩
      · have hy : y ∈ (K.comp (ueRelPow W n)).image (A ∩ B) :=
          ih ha hyB hay
        rcases hy with ⟨c, hcAB, hcy⟩
        refine ⟨c, hcAB, ?_⟩
        have hcb : (c, b) ∈ (K.comp (ueRelPow W n)).comp W := ⟨y, hcy, hyb⟩
        simpa [ueRelPow, SetRel.comp_assoc] using hcb

def coarseGenerated {X : Type*} (R : SetRel X X) : Set (SetRel X X) :=
  {E | ∀ 𝒞 : Set (SetRel X X),
    R ∈ 𝒞 →
    SetRel.id ∈ 𝒞 →
    (∀ ⦃S T : SetRel X X⦄, S ∈ 𝒞 → T ⊆ S → T ∈ 𝒞) →
    (∀ ⦃S T : SetRel X X⦄, S ∈ 𝒞 → T ∈ 𝒞 → S ∪ T ∈ 𝒞) →
    (∀ ⦃S : SetRel X X⦄, S ∈ 𝒞 → S.inv ∈ 𝒞) →
    (∀ ⦃S T : SetRel X X⦄, S ∈ 𝒞 → T ∈ 𝒞 → S.comp T ∈ 𝒞) →
    E ∈ 𝒞}

def uniformCoarse (X : Type*) [UniformSpace X] : Set (SetRel X X) :=
  {E | ∀ R ∈ uniformity X, E ∈ coarseGenerated R}

lemma uniformCoarse_id {X : Type*} [UniformSpace X] :
    SetRel.id ∈ uniformCoarse X := by
  intro R hR 𝒞 hgen hid hsub hunion hinv hcomp
  exact hid

lemma uniformCoarse_subset {X : Type*} [UniformSpace X] {S T : SetRel X X}
    (hS : S ∈ uniformCoarse X) (hTS : T ⊆ S) : T ∈ uniformCoarse X := by
  intro R hR 𝒞 hgen hid hsub hunion hinv hcomp
  exact hsub (hS R hR 𝒞 hgen hid hsub hunion hinv hcomp) hTS

lemma uniformCoarse_comp {X : Type*} [UniformSpace X] {S T : SetRel X X}
    (hS : S ∈ uniformCoarse X) (hT : T ∈ uniformCoarse X) :
    S.comp T ∈ uniformCoarse X := by
  intro R hR 𝒞 hgen hid hsub hunion hinv hcomp
  exact hcomp (hS R hR 𝒞 hgen hid hsub hunion hinv hcomp)
    (hT R hR 𝒞 hgen hid hsub hunion hinv hcomp)

lemma coarseGenerated_relPow_bound {X : Type*} {V W : SetRel X X}
    (hrefl : SetRel.id ⊆ W) (hsymm : W.inv ⊆ W)
    (hV : V ∈ coarseGenerated W) :
    ∃ n : ℕ, V ⊆ ueRelPow W n := by
  refine hV {E : SetRel X X | ∃ n : ℕ, E ⊆ ueRelPow W n} ?_ ?_ ?_ ?_ ?_ ?_
  · exact ⟨1, by simpa [ueRelPow, SetRel.id_comp]⟩
  · exact ⟨0, by intro p hp; exact hp⟩
  · intro S T hS hTS
    rcases hS with ⟨n, hSn⟩
    exact ⟨n, hTS.trans hSn⟩
  · intro S T hS hT
    rcases hS with ⟨m, hSm⟩
    rcases hT with ⟨n, hTn⟩
    refine ⟨max m n, ?_⟩
    intro p hp
    rcases hp with hp | hp
    · exact ueRelPow_mono hrefl (Nat.le_max_left m n) (hSm hp)
    · exact ueRelPow_mono hrefl (Nat.le_max_right m n) (hTn hp)
  · intro S hS
    rcases hS with ⟨n, hSn⟩
    refine ⟨n, ?_⟩
    intro p hp
    exact ueRelPow_inv_subset hsymm n (ueRel_inv_subset hSn hp)
  · intro S T hS hT
    rcases hS with ⟨m, hSm⟩
    rcases hT with ⟨n, hTn⟩
    refine ⟨m + n, ?_⟩
    exact (ueRel_comp_mono hSm hTn).trans (ueRelPow_comp_subset W m n)

lemma ueSymmetrize_inv_subset {X : Type*} (R : SetRel X X) :
    R.symmetrize.inv ⊆ R.symmetrize := by
  intro p hp
  exact ⟨hp.2, hp.1⟩

/- verified submission -/
theorem uniform_excision_implies_coarse_excision
    {X : Type*} [UniformSpace X] (A B : Set X) :
    let generated : SetRel X X → Set (SetRel X X) := fun R =>
      {E | ∀ 𝒞 : Set (SetRel X X),
        R ∈ 𝒞 →
        SetRel.id ∈ 𝒞 →
        (∀ ⦃S T : SetRel X X⦄, S ∈ 𝒞 → T ⊆ S → T ∈ 𝒞) →
        (∀ ⦃S T : SetRel X X⦄, S ∈ 𝒞 → T ∈ 𝒞 → S ∪ T ∈ 𝒞) →
        (∀ ⦃S : SetRel X X⦄, S ∈ 𝒞 → S.inv ∈ 𝒞) →
        (∀ ⦃S T : SetRel X X⦄, S ∈ 𝒞 → T ∈ 𝒞 → S.comp T ∈ 𝒞) →
        E ∈ 𝒞}
    let coarse : Set (SetRel X X) :=
      {E | ∀ R ∈ uniformity X, E ∈ generated R}
    A ∪ B = Set.univ →
    (∃ E ∈ uniformity X, E ∈ coarse) →
    (∃ U ∈ uniformity X,
      ∃ κ : OrderDual {W : SetRel X X // W ⊆ U} → OrderDual (SetRel X X),
        Monotone κ ∧
        (∀ V ∈ uniformity X,
          ∃ W : {W : SetRel X X // W ⊆ U},
            W.1 ∈ uniformity X ∧
              OrderDual.ofDual (κ (OrderDual.toDual W)) ⊆ V) ∧
        (∀ W : {W : SetRel X X // W ⊆ U},
          W.1.image A ∩ W.1.image B ⊆
            (OrderDual.ofDual (κ (OrderDual.toDual W))).image (A ∩ B))) →
    ∀ V ∈ coarse, ∃ T ∈ coarse,
      V.image A ∩ V.image B ⊆ T.image (A ∩ B) := by
  intro generated coarse hAB hcompat hex V hV
  change V ∈ uniformCoarse X at hV
  change ∃ T ∈ uniformCoarse X, V.image A ∩ V.image B ⊆ T.image (A ∩ B)
  rcases hcompat with ⟨E, hEuniform, hEcoarse⟩
  change E ∈ uniformCoarse X at hEcoarse
  rcases hex with ⟨U, hUuniform, κ, hκmono, hκapprox, hκexc⟩
  rcases hκapprox E hEuniform with ⟨WE, hWEuniform, hκWE⟩
  let D : SetRel X X := WE.1 ∩ U ∩ E
  have hDuniform : D ∈ uniformity X := by
    exact Filter.inter_mem (Filter.inter_mem hWEuniform hUuniform) hEuniform
  let W : SetRel X X := D.symmetrize
  have hWuniform : W ∈ uniformity X := by
    exact symmetrize_mem_uniformity hDuniform
  have hW_subset_U : W ⊆ U := by
    intro p hp
    exact hp.1.1.2
  have hW_subset_E : W ⊆ E := by
    intro p hp
    exact hp.1.2
  have hW_subset_WE : W ⊆ WE.1 := by
    intro p hp
    exact hp.1.1.1
  let WU : {S : SetRel X X // S ⊆ U} := ⟨W, hW_subset_U⟩
  have hWrefl : SetRel.id ⊆ W := refl_le_uniformity hWuniform
  have hWsymm : W.inv ⊆ W := by
    exact ueSymmetrize_inv_subset D
  have hWcoarse : W ∈ uniformCoarse X :=
    uniformCoarse_subset hEcoarse hW_subset_E
  let K : SetRel X X := OrderDual.ofDual (κ (OrderDual.toDual WU))
  have hK_subset_E : K ⊆ E := by
    have hle : OrderDual.toDual WE ≤ OrderDual.toDual WU := by
      exact hW_subset_WE
    have hKWE : K ⊆ OrderDual.ofDual (κ (OrderDual.toDual WE)) := by
      exact hκmono hle
    exact hKWE.trans hκWE
  have hKcoarse : K ∈ uniformCoarse X :=
    uniformCoarse_subset hEcoarse hK_subset_E
  have hWexc : W.image A ∩ W.image B ⊆ K.image (A ∩ B) := by
    exact hκexc WU
  have hV_generated_W : V ∈ coarseGenerated W := hV W hWuniform
  rcases coarseGenerated_relPow_bound hWrefl hWsymm hV_generated_W with ⟨n, hVn⟩
  have hPowCoarse : ∀ m : ℕ, ueRelPow W m ∈ uniformCoarse X := by
    intro m
    induction m with
    | zero => exact uniformCoarse_id
    | succ m ih => exact uniformCoarse_comp ih hWcoarse
  refine ⟨K.comp (ueRelPow W (n + n + n)), ?_, ?_⟩
  · exact uniformCoarse_comp hKcoarse (hPowCoarse (n + n + n))
  · intro x hx
    have hxA : x ∈ (ueRelPow W n).image A := ueRel_image_subset hVn A hx.1
    have hxB : x ∈ (ueRelPow W n).image B := ueRel_image_subset hVn B hx.2
    rcases hxA with ⟨a, haA, hax⟩
    rcases hxB with ⟨b, hbB, hbx⟩
    have hxb : (x, b) ∈ ueRelPow W n :=
      ueRelPow_inv_subset hWsymm n hbx
    have hab₂ : (a, b) ∈ (ueRelPow W n).comp (ueRelPow W n) := ⟨x, hax, hxb⟩
    have habN : (a, b) ∈ ueRelPow W (n + n) :=
      ueRelPow_comp_subset W n n hab₂
    have hb_boundary : b ∈ (K.comp (ueRelPow W (n + n))).image (A ∩ B) :=
      ue_boundary hAB hWrefl hWexc (n + n) haA hbB habN
    rcases hb_boundary with ⟨c, hcAB, hcb⟩
    refine ⟨c, hcAB, ?_⟩
    have hcx₁ : (c, x) ∈ (K.comp (ueRelPow W (n + n))).comp (ueRelPow W n) :=
      ⟨b, hcb, hbx⟩
    have hcx₂ : (c, x) ∈ K.comp ((ueRelPow W (n + n)).comp (ueRelPow W n)) := by
      simpa [SetRel.comp_assoc] using hcx₁
    have htail : (ueRelPow W (n + n)).comp (ueRelPow W n) ⊆
        ueRelPow W (n + n + n) := by
      exact ueRelPow_comp_subset W (n + n) n
    exact (ueRel_comp_mono (by intro p hp; exact hp) htail) hcx₂

end Rollout_p1808_uniform_excision_implies_coarse_excision

#check_dependency_graph "Rollout_p1808_uniform_excision_implies_coarse_excision.uniform_excision_implies_coarse_excision" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∃ T ∈ coarse, V.image A ∩ V.image B ⊆ T.image (A ∩ B)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hAB\",\"statement\":\"A ∪ B = Set.univ\"},{\"name\":\"hcompat\",\"statement\":\"∃ E ∈ uniformity X, E ∈ coarse\"},{\"name\":\"hex\",\"statement\":\"∃ U ∈ uniformity X, ∃ κ, Monotone κ ∧ (∀ V ∈ uniformity X, ∃ W, ↑W ∈ uniformity X ∧ OrderDual.ofDual (κ (OrderDual.toDual W)) ⊆ V) ∧ ∀ (W : { W // W ⊆ U }), (↑W).image A ∩ (↑W).image B ⊆ (OrderDual.ofDual (κ (OrderDual.toDual W))).image (A ∩ B)\"},{\"name\":\"hV\",\"statement\":\"V ∈ coarse\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1808_uniform_excision_implies_coarse_excision\",\"reconstructedProofSha256\":\"d215f2341b37da00e5ff6c0cb09a9729d7bec00a177b96d336fa9f91c2d8c547\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1808_uniform_excision_implies_coarse_excision.uniform_excision_implies_coarse_excision\",\"topologySha256\":\"9943d8a4477aad14cf2e09eabf976b18caee95156b6751314b607bb9d2607bee\"}"

namespace Rollout_p1874_proposition_4_9

-- graph_id: p1874_proposition_4_9
-- topology_sha256: bcec890446f03ce91c83154fc3473ac279905ed22afa855c356ec184c9c9a442
/- accepted add_to_file helper 1 -/
lemma proposition_4_9_ordConnected_abs_sub_le
    (x : Set.Icc (0 : ℝ) 1) (r : ℝ) :
    ({y : Set.Icc (0 : ℝ) 1 | |(x : ℝ) - (y : ℝ)| ≤ r}).OrdConnected := by
  refine Set.OrdConnected.mk ?_
  intro y hy z hz w hw
  change |(x : ℝ) - (y : ℝ)| ≤ r at hy
  change |(x : ℝ) - (z : ℝ)| ≤ r at hz
  have hy' := abs_le.mp hy
  have hz' := abs_le.mp hz
  have hwy : (y : ℝ) ≤ w := hw.1
  have hwz : (w : ℝ) ≤ z := hw.2
  change |(x : ℝ) - (w : ℝ)| ≤ r
  apply abs_le.mpr
  constructor
  · nlinarith
  · nlinarith

lemma proposition_4_9_diam_abs_sub_le
    (x : Set.Icc (0 : ℝ) 1) (n : ℕ) :
    Metric.diam {y : Set.Icc (0 : ℝ) 1 |
      |(x : ℝ) - (y : ℝ)| ≤ (2 : ℝ) ^ (-(n + 1 : ℝ))} ≤
      (2 : ℝ) ^ (-(n : ℝ)) := by
  apply Metric.diam_le_of_forall_dist_le
  · positivity
  · intro y hy z hz
    change |(x : ℝ) - (y : ℝ)| ≤ (2 : ℝ) ^ (-(n + 1 : ℝ)) at hy
    change |(x : ℝ) - (z : ℝ)| ≤ (2 : ℝ) ^ (-(n + 1 : ℝ)) at hz
    calc
      dist y z = |(y : ℝ) - (z : ℝ)| := by
        rw [Subtype.dist_eq, Real.dist_eq]
      _ ≤ |(y : ℝ) - (x : ℝ)| + |(x : ℝ) - (z : ℝ)| := by
        exact abs_sub_le _ _ _
      _ = |(x : ℝ) - (y : ℝ)| + |(x : ℝ) - (z : ℝ)| := by
        rw [abs_sub_comm]
      _ ≤ (2 : ℝ) ^ (-(n + 1 : ℝ)) + (2 : ℝ) ^ (-(n + 1 : ℝ)) :=
        add_le_add hy hz
      _ = (2 : ℝ) ^ (-(n : ℝ)) := by
        rw [← two_mul]
        symm
        rw [show (-(n : ℝ)) = (-(n + 1 : ℝ)) + 1 by ring]
        rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        rw [Real.rpow_one]
        ring

/- accepted add_to_file helper 2 -/
lemma proposition_4_9_ball_le
    (α : ℝ) (f : ℕ → ℕ)
    (μ : MeasureTheory.Measure (Set.Icc (0 : ℝ) 1))
    (hμ : ∀ n : ℕ, ∀ A : Set (Set.Icc (0 : ℝ) 1),
      A.OrdConnected →
      Metric.diam A ≤ Real.rpow 2 (-(n : ℝ)) →
      μ A ≤ ENNReal.ofReal (Real.rpow 2 (-(α * (n : ℝ) + (f n : ℝ)))))
    (x : Set.Icc (0 : ℝ) 1) (n : ℕ) :
    μ {y : Set.Icc (0 : ℝ) 1 |
      |(x : ℝ) - (y : ℝ)| ≤ (2 : ℝ) ^ (-(n + 1 : ℝ))} ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-(α * (n : ℝ) + (f n : ℝ)))) := by
  exact hμ n _ (proposition_4_9_ordConnected_abs_sub_le x _)
    (proposition_4_9_diam_abs_sub_le x n)

/- accepted add_to_file helper 3 -/
lemma proposition_4_9_diam_univ_le_one :
    Metric.diam (Set.univ : Set (Set.Icc (0 : ℝ) 1)) ≤ 1 := by
  apply Metric.diam_le_of_forall_dist_le zero_le_one
  intro x _ y _
  rw [Subtype.dist_eq, Real.dist_eq]
  have hx0 : (0:ℝ) ≤ x := x.property.1
  have hx1 : (x:ℝ) ≤ 1 := x.property.2
  have hy0 : (0:ℝ) ≤ y := y.property.1
  have hy1 : (y:ℝ) ≤ 1 := y.property.2
  apply abs_le.mpr
  constructor <;> nlinarith

/- accepted add_to_file helper 4 -/
lemma proposition_4_9_measure_univ_finite
    (α : ℝ) (f : ℕ → ℕ)
    (μ : MeasureTheory.Measure (Set.Icc (0 : ℝ) 1))
    (hμ : ∀ n : ℕ, ∀ A : Set (Set.Icc (0 : ℝ) 1),
      A.OrdConnected →
      Metric.diam A ≤ Real.rpow 2 (-(n : ℝ)) →
      μ A ≤ ENNReal.ofReal (Real.rpow 2 (-(α * (n : ℝ) + (f n : ℝ))))) :
    μ Set.univ < ⊤ := by
  have hb := hμ 0 Set.univ Set.ordConnected_univ
    (by simpa using proposition_4_9_diam_univ_le_one)
  have hr : Real.rpow (2 : ℝ) (-(α * ((0 : ℕ) : ℝ) + (f 0 : ℝ))) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1:ℝ) ≤ 2)
    have hnonneg : 0 ≤ α * ((0 : ℕ) : ℝ) + (f 0 : ℝ) := by simp
    linarith
  exact lt_of_le_of_lt hb (lt_of_le_of_lt (ENNReal.ofReal_le_one.mpr hr) ENNReal.one_lt_top)

/- accepted add_to_file helper 5 -/
lemma proposition_4_9_measure_singleton_eq_zero
    (α : ℝ) (hα : 0 ≤ α) (f : ℕ → ℕ)
    (hf : Summable (fun n : ℕ => Real.rpow 2 (-(f n : ℝ))))
    (μ : MeasureTheory.Measure (Set.Icc (0 : ℝ) 1))
    (hμ : ∀ n : ℕ, ∀ A : Set (Set.Icc (0 : ℝ) 1),
      A.OrdConnected →
      Metric.diam A ≤ Real.rpow 2 (-(n : ℝ)) →
      μ A ≤ ENNReal.ofReal (Real.rpow 2 (-(α * (n : ℝ) + (f n : ℝ)))))
    (x : Set.Icc (0 : ℝ) 1) :
    μ {x} = 0 := by
  have ht : Filter.Tendsto
      (fun n : ℕ => ENNReal.ofReal (Real.rpow 2 (-(f n : ℝ))))
      Filter.atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hf.tendsto_atTop_zero
  have hbound : ∀ n : ℕ, μ {x} ≤ ENNReal.ofReal (Real.rpow 2 (-(f n : ℝ))) := by
    intro n
    have hs := hμ n {x} Set.ordConnected_singleton (by
      rw [Metric.diam_singleton]
      exact Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
    have hr : Real.rpow (2 : ℝ) (-(α * (n : ℝ) + (f n : ℝ))) ≤
        Real.rpow (2 : ℝ) (-(f n : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      have hn : (0:ℝ) ≤ n := by positivity
      nlinarith
    exact le_trans hs (ENNReal.ofReal_le_ofReal hr)
  have hle : μ {x} ≤ 0 := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hev := (ENNReal.tendsto_nhds_zero.mp ht) (ε : ENNReal) (by exact_mod_cast hε)
    rcases hev.exists with ⟨n, hn⟩
    exact le_trans (hbound n) (le_trans hn (by simp))
  exact nonpos_iff_eq_zero.mp hle

/- accepted add_to_file helper 6 -/
lemma proposition_4_9_measurable_abs_sub
    (x : Set.Icc (0 : ℝ) 1) :
    Measurable (fun y : Set.Icc (0 : ℝ) 1 => |(x : ℝ) - (y : ℝ)|) := by
  exact (measurable_const.sub measurable_subtype_coe).abs

def proposition_4_9_shell (x : Set.Icc (0 : ℝ) 1) (n : ℕ) :
    Set (Set.Icc (0 : ℝ) 1) :=
  {y | (2 : ℝ) ^ (-(n + 2 : ℝ)) < |(x : ℝ) - (y : ℝ)| ∧
    |(x : ℝ) - (y : ℝ)| ≤ (2 : ℝ) ^ (-(n + 1 : ℝ))}

def proposition_4_9_far (x : Set.Icc (0 : ℝ) 1) :
    Set (Set.Icc (0 : ℝ) 1) :=
  {y | (1 / 2 : ℝ) < |(x : ℝ) - (y : ℝ)|}

lemma proposition_4_9_measurable_shell
    (x : Set.Icc (0 : ℝ) 1) (n : ℕ) :
    MeasurableSet (proposition_4_9_shell x n) := by
  unfold proposition_4_9_shell
  exact (measurableSet_lt measurable_const (proposition_4_9_measurable_abs_sub x)).inter
    (measurableSet_le (proposition_4_9_measurable_abs_sub x) measurable_const)

lemma proposition_4_9_measurable_far
    (x : Set.Icc (0 : ℝ) 1) :
    MeasurableSet (proposition_4_9_far x) := by
  unfold proposition_4_9_far
  exact measurableSet_lt measurable_const (proposition_4_9_measurable_abs_sub x)

/- accepted add_to_file helper 7 -/
lemma proposition_4_9_half_pow (n : ℕ) :
    ((1 / 2 : ℝ) ^ n) = (2 : ℝ) ^ (-(n : ℝ)) := by
  rw [one_div, inv_pow, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]

lemma proposition_4_9_energy_le_of_dist_ge
    {α d a : ℝ} (hα : 0 ≤ α) (ha : 0 < a) (had : a ≤ d) :
    (1 / ENNReal.ofReal d) ^ α ≤ ENNReal.ofReal ((1 / a) ^ α) := by
  have hd : 0 < d := lt_of_lt_of_le ha had
  have hbase : 1 / ENNReal.ofReal d ≤ ENNReal.ofReal (1 / a) := by
    have hdiv := ENNReal.ofReal_div_of_pos (x := (1 : ℝ)) (y := d) hd
    rw [ENNReal.ofReal_one] at hdiv
    rw [← hdiv]
    exact ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le ha had)
  calc
    (1 / ENNReal.ofReal d) ^ α ≤ (ENNReal.ofReal (1 / a)) ^ α :=
      ENNReal.rpow_le_rpow hbase hα
    _ = ENNReal.ofReal ((1 / a) ^ α) := by
      rw [ENNReal.ofReal_rpow_of_pos (one_div_pos.2 ha)]

/- accepted add_to_file helper 8 -/
lemma proposition_4_9_abs_sub_le_one
    (x y : Set.Icc (0 : ℝ) 1) :
    |(x : ℝ) - (y : ℝ)| ≤ 1 := by
  have hx0 : (0:ℝ) ≤ x := x.property.1
  have hx1 : (x:ℝ) ≤ 1 := x.property.2
  have hy0 : (0:ℝ) ≤ y := y.property.1
  have hy1 : (y:ℝ) ≤ 1 := y.property.2
  apply abs_le.mpr
  constructor <;> nlinarith

/- accepted add_to_file helper 9 -/
lemma proposition_4_9_energy_pointwise_le
    {α : ℝ} (hα : 0 ≤ α)
    (x y : Set.Icc (0 : ℝ) 1) (hxy : y ≠ x) :
    (1 / ENNReal.ofReal |(x : ℝ) - (y : ℝ)|) ^ α ≤
      ENNReal.ofReal ((2 : ℝ) ^ α) *
          (proposition_4_9_far x).indicator (fun _ => (1 : ENNReal)) y +
        ∑' n : ℕ,
          ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) ^ α) *
            (proposition_4_9_shell x n).indicator (fun _ => (1 : ENNReal)) y := by
  by_cases hfar : y ∈ proposition_4_9_far x
  · have hd : (1 / 2 : ℝ) ≤ |(x : ℝ) - (y : ℝ)| := le_of_lt hfar
    have hE := proposition_4_9_energy_le_of_dist_ge hα (by norm_num : (0:ℝ) < 1 / 2) hd
    have h2 : ((1 / (1 / 2 : ℝ)) ^ α) = (2 : ℝ) ^ α := by norm_num
    rw [h2] at hE
    calc
      (1 / ENNReal.ofReal |(x : ℝ) - (y : ℝ)|) ^ α ≤ ENNReal.ofReal ((2 : ℝ) ^ α) := hE
      _ = ENNReal.ofReal ((2 : ℝ) ^ α) *
          (proposition_4_9_far x).indicator (fun _ => (1 : ENNReal)) y := by
        simp [hfar]
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ α) *
            (proposition_4_9_far x).indicator (fun _ => (1 : ENNReal)) y +
          ∑' n : ℕ,
            ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) ^ α) *
              (proposition_4_9_shell x n).indicator (fun _ => (1 : ENNReal)) y :=
        le_add_of_nonneg_right (zero_le _)
  · have hdle_half : |(x : ℝ) - (y : ℝ)| ≤ 1 / 2 := by
      exact le_of_not_gt hfar
    have hcoord : (x : ℝ) ≠ y := by
      intro h
      apply hxy
      exact Subtype.ext h.symm
    have hdpos : 0 < |(x : ℝ) - (y : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr hcoord)
    rcases exists_nat_pow_near_of_lt_one hdpos (proposition_4_9_abs_sub_le_one x y)
        (by norm_num : (0:ℝ) < 1 / 2) (by norm_num : (1:ℝ) / 2 < 1) with
      ⟨m, hm_lower, hm_upper⟩
    have hm_ne : m ≠ 0 := by
      intro hm0
      subst m
      rw [pow_zero] at hm_upper
      rw [pow_one] at hm_lower
      exact hfar (by exact hm_lower)
    rcases Nat.exists_eq_succ_of_ne_zero hm_ne with ⟨n, rfl⟩
    have hm_lower' : ((1 / 2 : ℝ) ^ (n + 2)) < |(x : ℝ) - (y : ℝ)| := by
      simpa [Nat.succ_eq_add_one, add_assoc] using hm_lower
    have hm_upper' : |(x : ℝ) - (y : ℝ)| ≤ ((1 / 2 : ℝ) ^ (n + 1)) := by
      simpa [Nat.succ_eq_add_one] using hm_upper
    have hshell : y ∈ proposition_4_9_shell x n := by
      constructor
      · have h := hm_lower'
        rw [proposition_4_9_half_pow (n + 2)] at h
        convert h using 2
        norm_num [Nat.cast_add]
      · have h := hm_upper'
        rw [proposition_4_9_half_pow (n + 1)] at h
        convert h using 2
        norm_num [Nat.cast_add]
    have hE := proposition_4_9_energy_le_of_dist_ge hα
      (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _) hshell.1.le
    have hterm :
        ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) ^ α) ≤
          ∑' k : ℕ,
            ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(k + 2 : ℝ)))) ^ α) *
              (proposition_4_9_shell x k).indicator (fun _ => (1 : ENNReal)) y := by
      convert ENNReal.le_tsum (f := fun k : ℕ =>
          ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(k + 2 : ℝ)))) ^ α) *
            (proposition_4_9_shell x k).indicator (fun _ => (1 : ENNReal)) y) n using 2
      simp [hshell]
    calc
      (1 / ENNReal.ofReal |(x : ℝ) - (y : ℝ)|) ^ α ≤
          ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) ^ α) := hE
      _ ≤ ∑' k : ℕ,
            ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(k + 2 : ℝ)))) ^ α) *
              (proposition_4_9_shell x k).indicator (fun _ => (1 : ENNReal)) y := hterm
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ α) *
            (proposition_4_9_far x).indicator (fun _ => (1 : ENNReal)) y +
          ∑' k : ℕ,
            ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(k + 2 : ℝ)))) ^ α) *
              (proposition_4_9_shell x k).indicator (fun _ => (1 : ENNReal)) y :=
        le_add_of_nonneg_left (zero_le _)

/- accepted add_to_file helper 10 -/
lemma proposition_4_9_shell_weight_mul
    (α : ℝ) (f : ℕ → ℕ) (n : ℕ) :
    ((1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) ^ α) *
        (2 : ℝ) ^ (-(α * (n : ℝ) + (f n : ℝ))) =
      (2 : ℝ) ^ (2 * α) * (2 : ℝ) ^ (-(f n : ℝ)) := by
  have hA : (1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) ^ α =
      (2 : ℝ) ^ (α * ((n : ℝ) + 2)) := by
    have hbase : 1 / ((2 : ℝ) ^ (-(n + 2 : ℝ))) = (2 : ℝ) ^ ((n : ℝ) + 2) := by
      rw [one_div, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      ring_nf
    rw [hbase]
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    ring_nf
  rw [hA]
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  congr 1
  ring

/- accepted add_to_file helper 11 -/
lemma proposition_4_9_shell_bound_eq
    (α : ℝ) (f : ℕ → ℕ) (n : ℕ) :
    ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) ^ α) *
        ENNReal.ofReal ((2 : ℝ) ^ (-(α * (n : ℝ) + (f n : ℝ)))) =
      ENNReal.ofReal ((2 : ℝ) ^ (2 * α)) *
        ENNReal.ofReal ((2 : ℝ) ^ (-(f n : ℝ))) := by
  rw [← ENNReal.ofReal_mul
    (p := (1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) ^ α)
    (Real.rpow_nonneg (by positivity : 0 ≤ 1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) _)]
  rw [proposition_4_9_shell_weight_mul]
  rw [ENNReal.ofReal_mul (p := (2 : ℝ) ^ (2 * α))
    (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)]

/- accepted add_to_file helper 12 -/
lemma proposition_4_9_energy_le_of_dist_ge'
    {α d a : ℝ} (hα : 0 ≤ α) (ha : 0 < a) (had : a ≤ d) :
    1 / (ENNReal.ofReal d) ^ α ≤ ENNReal.ofReal ((1 / a) ^ α) := by
  simpa [ENNReal.inv_rpow] using
    (proposition_4_9_energy_le_of_dist_ge hα ha had)

/- accepted add_to_file helper 13 -/
lemma proposition_4_9_energy_pointwise_le'
    {α : ℝ} (hα : 0 ≤ α)
    (x y : Set.Icc (0 : ℝ) 1) (hxy : y ≠ x) :
    1 / (ENNReal.ofReal |(x : ℝ) - (y : ℝ)|) ^ α ≤
      ENNReal.ofReal ((2 : ℝ) ^ α) *
          (proposition_4_9_far x).indicator (fun _ => (1 : ENNReal)) y +
        ∑' n : ℕ,
          ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) ^ α) *
            (proposition_4_9_shell x n).indicator (fun _ => (1 : ENNReal)) y := by
  by_cases hfar : y ∈ proposition_4_9_far x
  · have hd : (1 / 2 : ℝ) ≤ |(x : ℝ) - (y : ℝ)| := le_of_lt hfar
    have hE := proposition_4_9_energy_le_of_dist_ge' hα (by norm_num : (0:ℝ) < 1 / 2) hd
    have h2 : ((1 / (1 / 2 : ℝ)) ^ α) = (2 : ℝ) ^ α := by norm_num
    rw [h2] at hE
    calc
      1 / (ENNReal.ofReal |(x : ℝ) - (y : ℝ)|) ^ α ≤ ENNReal.ofReal ((2 : ℝ) ^ α) := hE
      _ = ENNReal.ofReal ((2 : ℝ) ^ α) *
          (proposition_4_9_far x).indicator (fun _ => (1 : ENNReal)) y := by
        simp [hfar]
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ α) *
            (proposition_4_9_far x).indicator (fun _ => (1 : ENNReal)) y +
          ∑' n : ℕ,
            ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) ^ α) *
              (proposition_4_9_shell x n).indicator (fun _ => (1 : ENNReal)) y :=
        le_add_of_nonneg_right (zero_le _)
  · have hdle_half : |(x : ℝ) - (y : ℝ)| ≤ 1 / 2 := by
      exact le_of_not_gt hfar
    have hcoord : (x : ℝ) ≠ y := by
      intro h
      apply hxy
      exact Subtype.ext h.symm
    have hdpos : 0 < |(x : ℝ) - (y : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr hcoord)
    rcases exists_nat_pow_near_of_lt_one hdpos (proposition_4_9_abs_sub_le_one x y)
        (by norm_num : (0:ℝ) < 1 / 2) (by norm_num : (1:ℝ) / 2 < 1) with
      ⟨m, hm_lower, hm_upper⟩
    have hm_ne : m ≠ 0 := by
      intro hm0
      subst m
      rw [pow_zero] at hm_upper
      rw [pow_one] at hm_lower
      exact hfar (by exact hm_lower)
    rcases Nat.exists_eq_succ_of_ne_zero hm_ne with ⟨n, rfl⟩
    have hm_lower' : ((1 / 2 : ℝ) ^ (n + 2)) < |(x : ℝ) - (y : ℝ)| := by
      simpa [Nat.succ_eq_add_one, add_assoc] using hm_lower
    have hm_upper' : |(x : ℝ) - (y : ℝ)| ≤ ((1 / 2 : ℝ) ^ (n + 1)) := by
      simpa [Nat.succ_eq_add_one] using hm_upper
    have hshell : y ∈ proposition_4_9_shell x n := by
      constructor
      · have h := hm_lower'
        rw [proposition_4_9_half_pow (n + 2)] at h
        convert h using 2
        norm_num [Nat.cast_add]
      · have h := hm_upper'
        rw [proposition_4_9_half_pow (n + 1)] at h
        convert h using 2
        norm_num [Nat.cast_add]
    have hE := proposition_4_9_energy_le_of_dist_ge' hα
      (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _) hshell.1.le
    have hterm :
        ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) ^ α) ≤
          ∑' k : ℕ,
            ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(k + 2 : ℝ)))) ^ α) *
              (proposition_4_9_shell x k).indicator (fun _ => (1 : ENNReal)) y := by
      convert ENNReal.le_tsum (f := fun k : ℕ =>
          ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(k + 2 : ℝ)))) ^ α) *
            (proposition_4_9_shell x k).indicator (fun _ => (1 : ENNReal)) y) n using 2
      simp [hshell]
    calc
      1 / (ENNReal.ofReal |(x : ℝ) - (y : ℝ)|) ^ α ≤
          ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) ^ α) := hE
      _ ≤ ∑' k : ℕ,
            ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(k + 2 : ℝ)))) ^ α) *
              (proposition_4_9_shell x k).indicator (fun _ => (1 : ENNReal)) y := hterm
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ α) *
            (proposition_4_9_far x).indicator (fun _ => (1 : ENNReal)) y +
          ∑' k : ℕ,
            ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(k + 2 : ℝ)))) ^ α) *
              (proposition_4_9_shell x k).indicator (fun _ => (1 : ENNReal)) y :=
        le_add_of_nonneg_left (zero_le _)

/- accepted add_to_file helper 14 -/
lemma proposition_4_9_inner_energy_le
    (α : ℝ) (hα : 0 ≤ α) (f : ℕ → ℕ)
    (hf : Summable (fun n : ℕ => Real.rpow 2 (-(f n : ℝ))))
    (μ : MeasureTheory.Measure (Set.Icc (0 : ℝ) 1))
    (hμ : ∀ n : ℕ, ∀ A : Set (Set.Icc (0 : ℝ) 1),
      A.OrdConnected →
      Metric.diam A ≤ Real.rpow 2 (-(n : ℝ)) →
      μ A ≤ ENNReal.ofReal (Real.rpow 2 (-(α * (n : ℝ) + (f n : ℝ)))))
    (x : Set.Icc (0 : ℝ) 1) :
    (∫⁻ y : Set.Icc (0 : ℝ) 1,
      1 / (ENNReal.ofReal |(x : ℝ) - (y : ℝ)|) ^ α ∂μ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ α) * μ Set.univ +
        ENNReal.ofReal ((2 : ℝ) ^ (2 * α)) *
          ∑' n : ℕ, ENNReal.ofReal (Real.rpow 2 (-(f n : ℝ))) := by
  let C0 : ENNReal := ENNReal.ofReal ((2 : ℝ) ^ α)
  let C : ℕ → ENNReal := fun n =>
    ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) ^ α)
  have hmeas0 : Measurable (fun y : Set.Icc (0 : ℝ) 1 =>
      C0 * (proposition_4_9_far x).indicator (fun _ => (1 : ENNReal)) y) := by
    exact (measurable_const.indicator (proposition_4_9_measurable_far x)).const_mul C0
  have hmeass : ∀ n : ℕ, Measurable (fun y : Set.Icc (0 : ℝ) 1 =>
      C n * (proposition_4_9_shell x n).indicator (fun _ => (1 : ENNReal)) y) := by
    intro n
    exact (measurable_const.indicator (proposition_4_9_measurable_shell x n)).const_mul (C n)
  have hAEne : ∀ᵐ y : Set.Icc (0 : ℝ) 1 ∂μ, y ≠ x := by
    rw [MeasureTheory.ae_iff]
    have hset : {y : Set.Icc (0 : ℝ) 1 | ¬ y ≠ x} = {x} := by
      ext y
      simp [eq_comm]
    rw [hset]
    exact proposition_4_9_measure_singleton_eq_zero α hα f hf μ hμ x
  have hAE : ∀ᵐ y : Set.Icc (0 : ℝ) 1 ∂μ,
      1 / (ENNReal.ofReal |(x : ℝ) - (y : ℝ)|) ^ α ≤
        C0 * (proposition_4_9_far x).indicator (fun _ => (1 : ENNReal)) y +
          ∑' n : ℕ, C n *
            (proposition_4_9_shell x n).indicator (fun _ => (1 : ENNReal)) y := by
    filter_upwards [hAEne] with y hy
    simpa [C0, C] using proposition_4_9_energy_pointwise_le' hα x y hy
  have hFint :
      (∫⁻ y : Set.Icc (0 : ℝ) 1,
        C0 * (proposition_4_9_far x).indicator (fun _ => (1 : ENNReal)) y +
          ∑' n : ℕ, C n *
            (proposition_4_9_shell x n).indicator (fun _ => (1 : ENNReal)) y ∂μ) =
      C0 * μ (proposition_4_9_far x) +
        ∑' n : ℕ, C n * μ (proposition_4_9_shell x n) := by
    rw [MeasureTheory.lintegral_add_left hmeas0]
    congr 1
    · rw [MeasureTheory.lintegral_const_mul C0
        (measurable_const.indicator (proposition_4_9_measurable_far x))]
      rw [MeasureTheory.lintegral_indicator_const (proposition_4_9_measurable_far x) 1]
      simp
    · rw [MeasureTheory.lintegral_tsum (fun n => (hmeass n).aemeasurable)]
      congr 1
      funext n
      rw [MeasureTheory.lintegral_const_mul (C n)
        (measurable_const.indicator (proposition_4_9_measurable_shell x n))]
      rw [MeasureTheory.lintegral_indicator_const (proposition_4_9_measurable_shell x n) 1]
      simp
  calc
    (∫⁻ y : Set.Icc (0 : ℝ) 1,
        1 / (ENNReal.ofReal |(x : ℝ) - (y : ℝ)|) ^ α ∂μ)
        ≤ ∫⁻ y : Set.Icc (0 : ℝ) 1,
          C0 * (proposition_4_9_far x).indicator (fun _ => (1 : ENNReal)) y +
            ∑' n : ℕ, C n *
              (proposition_4_9_shell x n).indicator (fun _ => (1 : ENNReal)) y ∂μ :=
      MeasureTheory.lintegral_mono_ae hAE
    _ = C0 * μ (proposition_4_9_far x) +
        ∑' n : ℕ, C n * μ (proposition_4_9_shell x n) := hFint
    _ ≤ C0 * μ Set.univ +
        ENNReal.ofReal ((2 : ℝ) ^ (2 * α)) *
          ∑' n : ℕ, ENNReal.ofReal (Real.rpow 2 (-(f n : ℝ))) := by
      apply add_le_add
      · exact mul_le_mul_left' (MeasureTheory.measure_mono (Set.subset_univ _)) C0
      · calc
          (∑' n : ℕ, C n * μ (proposition_4_9_shell x n))
              ≤ ∑' n : ℕ, C n *
                ENNReal.ofReal (Real.rpow 2 (-(α * (n : ℝ) + (f n : ℝ)))) := by
            apply ENNReal.tsum_le_tsum
            intro n
            apply mul_le_mul_left'
            exact le_trans
              (MeasureTheory.measure_mono (by
                intro y hy
                exact hy.2))
              (proposition_4_9_ball_le α f μ hμ x n)
          _ = ∑' n : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (2 * α)) *
              ENNReal.ofReal (Real.rpow 2 (-(f n : ℝ))) := by
            congr 1
            funext n
            simpa [C] using proposition_4_9_shell_bound_eq α f n
          _ = ENNReal.ofReal ((2 : ℝ) ^ (2 * α)) *
              ∑' n : ℕ, ENNReal.ofReal (Real.rpow 2 (-(f n : ℝ))) := by
            rw [ENNReal.tsum_mul_left]

/- verified submission -/
theorem proposition_4_9
    (α : ℝ) (hα : 0 ≤ α) (f : ℕ → ℕ)
    (hf : Summable (fun n : ℕ => Real.rpow 2 (-(f n : ℝ))))
    (μ : MeasureTheory.Measure (Set.Icc (0 : ℝ) 1))
    (hμ : ∀ n : ℕ, ∀ A : Set (Set.Icc (0 : ℝ) 1),
      A.OrdConnected →
      Metric.diam A ≤ Real.rpow 2 (-(n : ℝ)) →
      μ A ≤ ENNReal.ofReal (Real.rpow 2 (-(α * (n : ℝ) + (f n : ℝ))))) :
    (∫⁻ x, ∫⁻ y,
      1 / (ENNReal.ofReal |(x : ℝ) - (y : ℝ)|) ^ α ∂μ ∂μ) < ⊤ := by
  have hμu : μ Set.univ < ⊤ := proposition_4_9_measure_univ_finite α f μ hμ
  have htsum : (∑' n : ℕ, ENNReal.ofReal (Real.rpow 2 (-(f n : ℝ)))) < ⊤ := by
    have htsumEq := ENNReal.ofReal_tsum_of_nonneg
      (f := fun n : ℕ => Real.rpow 2 (-(f n : ℝ)))
      (fun n => Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _) hf
    rw [← htsumEq]
    exact ENNReal.ofReal_lt_top
  let K : ENNReal := ENNReal.ofReal ((2 : ℝ) ^ α) * μ Set.univ +
    ENNReal.ofReal ((2 : ℝ) ^ (2 * α)) *
      ∑' n : ℕ, ENNReal.ofReal (Real.rpow 2 (-(f n : ℝ)))
  have hK : K < ⊤ := by
    apply ENNReal.add_lt_top.mpr
    constructor
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμu
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top htsum
  calc
    (∫⁻ x, ∫⁻ y,
        1 / (ENNReal.ofReal |(x : ℝ) - (y : ℝ)|) ^ α ∂μ ∂μ)
        ≤ ∫⁻ x : Set.Icc (0 : ℝ) 1, K ∂μ := by
      apply MeasureTheory.lintegral_mono
      intro x
      exact proposition_4_9_inner_energy_le α hα f hf μ hμ x
    _ = K * μ Set.univ := MeasureTheory.lintegral_const K
    _ < ⊤ := ENNReal.mul_lt_top hK hμu

end Rollout_p1874_proposition_4_9

#check_dependency_graph "Rollout_p1874_proposition_4_9.proposition_4_9" against "{\"edges\":[{\"conclusion\":{\"name\":\"hμu\",\"statement\":\"μ Set.univ < ⊤\"},\"graphEdgeId\":\"h_001_h_u\",\"premises\":[{\"name\":\"hμ\",\"statement\":\"∀ (n : ℕ) (A : Set ↑(Set.Icc 0 1)), A.OrdConnected → Metric.diam A ≤ Real.rpow 2 (-↑n) → μ A ≤ ENNReal.ofReal (Real.rpow 2 (-(α * ↑n + ↑(f n))))\"}],\"rawEdgeId\":\"telescope_6\"},{\"conclusion\":{\"name\":\"htsum\",\"statement\":\"∑' (n : ℕ), ENNReal.ofReal (Real.rpow 2 (-↑(f n))) < ⊤\"},\"graphEdgeId\":\"h_002_htsum\",\"premises\":[{\"name\":\"hf\",\"statement\":\"Summable fun n => Real.rpow 2 (-↑(f n))\"}],\"rawEdgeId\":\"telescope_7\"},{\"conclusion\":{\"name\":\"hK\",\"statement\":\"K < ⊤\"},\"graphEdgeId\":\"h_003_hk\",\"premises\":[{\"name\":\"hμu\",\"statement\":\"μ Set.univ < ⊤\"},{\"name\":\"htsum\",\"statement\":\"∑' (n : ℕ), ENNReal.ofReal (Real.rpow 2 (-↑(f n))) < ⊤\"}],\"rawEdgeId\":\"telescope_9\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∫⁻ (x : ↑(Set.Icc 0 1)), ∫⁻ (y : ↑(Set.Icc 0 1)), 1 / ENNReal.ofReal |↑x - ↑y| ^ α ∂μ ∂μ < ⊤\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hα\",\"statement\":\"0 ≤ α\"},{\"name\":\"hf\",\"statement\":\"Summable fun n => Real.rpow 2 (-↑(f n))\"},{\"name\":\"hμ\",\"statement\":\"∀ (n : ℕ) (A : Set ↑(Set.Icc 0 1)), A.OrdConnected → Metric.diam A ≤ Real.rpow 2 (-↑n) → μ A ≤ ENNReal.ofReal (Real.rpow 2 (-(α * ↑n + ↑(f n))))\"},{\"name\":\"hμu\",\"statement\":\"μ Set.univ < ⊤\"},{\"name\":\"hK\",\"statement\":\"K < ⊤\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1874_proposition_4_9\",\"reconstructedProofSha256\":\"70ea3923053fc75d4d7037c8dd77fad511e7cdf193bc054056681aa2d1cc5cfd\",\"selectedEdgeCount\":4,\"theoremName\":\"Rollout_p1874_proposition_4_9.proposition_4_9\",\"topologySha256\":\"bcec890446f03ce91c83154fc3473ac279905ed22afa855c356ec184c9c9a442\"}"
