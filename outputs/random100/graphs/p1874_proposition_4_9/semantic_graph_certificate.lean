import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1874_proposition_4_9
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: bcec890446f03ce91c83154fc3473ac279905ed22afa855c356ec184c9c9a442
-- reconstructed_proof_sha256: 70ea3923053fc75d4d7037c8dd77fad511e7cdf193bc054056681aa2d1cc5cfd
-- selected_edge_count: 4

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


#check_dependency_graph "proposition_4_9" against "{\"edges\":[{\"conclusion\":{\"name\":\"hμu\",\"statement\":\"μ Set.univ < ⊤\"},\"graphEdgeId\":\"h_001_h_u\",\"premises\":[{\"name\":\"hμ\",\"statement\":\"∀ (n : ℕ) (A : Set ↑(Set.Icc 0 1)), A.OrdConnected → Metric.diam A ≤ Real.rpow 2 (-↑n) → μ A ≤ ENNReal.ofReal (Real.rpow 2 (-(α * ↑n + ↑(f n))))\"}],\"rawEdgeId\":\"telescope_6\"},{\"conclusion\":{\"name\":\"htsum\",\"statement\":\"∑' (n : ℕ), ENNReal.ofReal (Real.rpow 2 (-↑(f n))) < ⊤\"},\"graphEdgeId\":\"h_002_htsum\",\"premises\":[{\"name\":\"hf\",\"statement\":\"Summable fun n => Real.rpow 2 (-↑(f n))\"}],\"rawEdgeId\":\"telescope_7\"},{\"conclusion\":{\"name\":\"hK\",\"statement\":\"K < ⊤\"},\"graphEdgeId\":\"h_003_hk\",\"premises\":[{\"name\":\"hμu\",\"statement\":\"μ Set.univ < ⊤\"},{\"name\":\"htsum\",\"statement\":\"∑' (n : ℕ), ENNReal.ofReal (Real.rpow 2 (-↑(f n))) < ⊤\"}],\"rawEdgeId\":\"telescope_9\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∫⁻ (x : ↑(Set.Icc 0 1)), ∫⁻ (y : ↑(Set.Icc 0 1)), 1 / ENNReal.ofReal |↑x - ↑y| ^ α ∂μ ∂μ < ⊤\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hα\",\"statement\":\"0 ≤ α\"},{\"name\":\"hf\",\"statement\":\"Summable fun n => Real.rpow 2 (-↑(f n))\"},{\"name\":\"hμ\",\"statement\":\"∀ (n : ℕ) (A : Set ↑(Set.Icc 0 1)), A.OrdConnected → Metric.diam A ≤ Real.rpow 2 (-↑n) → μ A ≤ ENNReal.ofReal (Real.rpow 2 (-(α * ↑n + ↑(f n))))\"},{\"name\":\"hμu\",\"statement\":\"μ Set.univ < ⊤\"},{\"name\":\"hK\",\"statement\":\"K < ⊤\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1874_proposition_4_9\",\"reconstructedProofSha256\":\"70ea3923053fc75d4d7037c8dd77fad511e7cdf193bc054056681aa2d1cc5cfd\",\"selectedEdgeCount\":4,\"theoremName\":\"proposition_4_9\",\"topologySha256\":\"bcec890446f03ce91c83154fc3473ac279905ed22afa855c356ec184c9c9a442\"}"
