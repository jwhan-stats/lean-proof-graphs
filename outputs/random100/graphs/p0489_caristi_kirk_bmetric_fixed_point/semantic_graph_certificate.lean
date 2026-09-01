import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p0489_caristi_kirk_bmetric_fixed_point
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: e3c506562155440bc52f1df77609cd5aa3e4eb91c6122edfd93871c94b5cd418
-- reconstructed_proof_sha256: fb7c2ed30a2457a3fe100abbf439e471d2a98f12fac28c3d6456b7c379bc0e0f
-- selected_edge_count: 2

/- accepted add_to_file helper 1 -/
lemma caristi_iterate_phi_bound
    (X : Type*) (d : X × X → NNReal) (Φ : X → NNReal) (f : X → X) (A : ℝ)
    (hA : 1 < A)
    (hcaristi : ∀ x : X,
      (d (x, f x) : ℝ) ≤ (Φ x : ℝ) - A * (Φ (f x) : ℝ))
    (x₀ : X) (n : ℕ) :
    (Φ ((f^[n]) x₀) : ℝ) ≤ (Φ x₀ : ℝ) * (A⁻¹) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      let x := (f^[n]) x₀
      have hcar := hcaristi x
      have hdnonneg : (0:ℝ) ≤ d (x, f x) := NNReal.coe_nonneg _
      have hmul : A * (Φ (f x) : ℝ) ≤ (Φ x : ℝ) := by linarith
      have hnext : (Φ (f x) : ℝ) ≤ (Φ x : ℝ) / A := by
        rw [le_div_iff₀ (by linarith : 0 < A)]
        simpa [mul_comm] using hmul
      have hrw : (f^[n+1]) x₀ = f x := by
        simpa [x] using (Function.iterate_succ_apply' f n x₀)
      rw [hrw]
      calc
        (Φ (f x) : ℝ) ≤ (Φ x : ℝ) / A := hnext
        _ ≤ ((Φ x₀ : ℝ) * A⁻¹ ^ n) / A := by
          gcongr
        _ = (Φ x₀ : ℝ) * A⁻¹ ^ (n+1) := by
          ring_nf

lemma tendsto_dist_pair_atTop_prod_zero_of_summable
    {X : Type*} [PseudoMetricSpace X] (x : ℕ → X) (a : ℕ → ℝ)
    (ha0 : ∀ n, 0 ≤ a n)
    (hadj : ∀ n, dist (x n) (x (n + 1)) ≤ a n)
    (hsum : Summable a) :
    Filter.Tendsto (fun p : ℕ × ℕ => dist (x p.1) (x p.2))
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
  have htail_summ : ∀ m : ℕ, Summable fun k : ℕ => a (m + k) := by
    intro m
    have h := (summable_nat_add_iff m).2 hsum
    simpa [Nat.add_comm] using h
  have htail_tendsto : Filter.Tendsto (fun m : ℕ => ∑' k : ℕ, a (m + k))
      Filter.atTop (nhds 0) := by
    simpa [Nat.add_comm] using tendsto_sum_nat_add a
  have hpair_le : ∀ {m n : ℕ}, m ≤ n →
      dist (x m) (x n) ≤ ∑' k : ℕ, a (m + k) := by
    intro m n hmn
    calc
      dist (x m) (x n) ≤ ∑ k ∈ Finset.Ico m n, a k :=
        dist_le_Ico_sum_of_dist_le hmn (fun {_} _ _ => hadj _)
      _ = ∑ k ∈ Finset.range (n - m), a (m + k) :=
        Finset.sum_Ico_eq_sum_range a m n
      _ ≤ ∑' k : ℕ, a (m + k) := by
        exact (htail_summ m).sum_le_tsum (Finset.range (n - m))
          (fun k hk => ha0 (m + k))
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop).1 htail_tendsto ε hε
  have hrect : {p : ℕ × ℕ | N ≤ p.1 ∧ N ≤ p.2} ∈ Filter.atTop ×ˢ Filter.atTop := by
    exact Filter.prod_mem_prod
      (Filter.mem_atTop_sets.2 ⟨N, fun b hb => hb⟩ : Set.Ici N ∈ (Filter.atTop : Filter ℕ))
      (Filter.mem_atTop_sets.2 ⟨N, fun b hb => hb⟩ : Set.Ici N ∈ (Filter.atTop : Filter ℕ))
  exact Filter.Eventually.mono hrect (by
    intro p hp
    have htail_nonneg : ∀ m, 0 ≤ ∑' k : ℕ, a (m + k) := by
      intro m
      exact tsum_nonneg (fun k => ha0 (m + k))
    have htail_lt1 : ∑' k : ℕ, a (p.1 + k) < ε := by
      have hdist := hN p.1 hp.1
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (htail_nonneg p.1)] at hdist
      exact hdist
    have htail_lt2 : ∑' k : ℕ, a (p.2 + k) < ε := by
      have hdist := hN p.2 hp.2
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (htail_nonneg p.2)] at hdist
      exact hdist
    have hdist_nonneg : 0 ≤ dist (x p.1) (x p.2) := dist_nonneg
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hdist_nonneg]
    rcases le_total p.1 p.2 with hle | hle
    · exact lt_of_le_of_lt (hpair_le hle) htail_lt1
    · rw [dist_comm]
      exact lt_of_le_of_lt (hpair_le hle) htail_lt2)

/- accepted add_to_file helper 2 -/
lemma bmetric_predist_four_max
    (X : Type*) (s : ℝ) (d : X × X → NNReal)
    (hs : 1 ≤ s)
    (hd_triangle : ∀ x y z : X,
      (d (x, y) : ℝ) ≤ s * ((d (x, z) : ℝ) + (d (z, y) : ℝ)))
    {N : ℕ} (hN : 0 < N)
    (hpow : (s + 2 * s ^ 2) ^ ((N : ℝ)⁻¹) ≤ 2)
    (x₁ x₂ x₃ x₄ : X) :
    (d (x₁, x₄) : NNReal) ^ ((N : ℝ)⁻¹) ≤
      2 * max ((d (x₁, x₂) : NNReal) ^ ((N : ℝ)⁻¹))
        (max ((d (x₂, x₃) : NNReal) ^ ((N : ℝ)⁻¹))
          ((d (x₃, x₄) : NNReal) ^ ((N : ℝ)⁻¹))) := by
  let p : ℝ := (N : ℝ)⁻¹
  let D : X × X → ℝ := fun xy => (d xy : ℝ)
  let M : ℝ := max (D (x₁, x₂)) (max (D (x₂, x₃)) (D (x₃, x₄)))
  have hs0 : 0 ≤ s := by linarith
  have hM0 : 0 ≤ M := by
    exact le_trans (NNReal.coe_nonneg _) (le_max_left _ _)
  have h12 : D (x₁, x₂) ≤ M := by exact le_max_left _ _
  have h23 : D (x₂, x₃) ≤ M := by
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have h34 : D (x₃, x₄) ≤ M := by
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have h24 : D (x₂, x₄) ≤ 2 * s * M := by
    have ht := hd_triangle x₂ x₄ x₃
    calc
      D (x₂, x₄) ≤ s * (D (x₂, x₃) + D (x₃, x₄)) := by simpa [D] using ht
      _ ≤ s * (M + M) := by gcongr
      _ = 2 * s * M := by ring
  have h14 : D (x₁, x₄) ≤ (s + 2 * s ^ 2) * M := by
    have ht := hd_triangle x₁ x₄ x₂
    calc
      D (x₁, x₄) ≤ s * (D (x₁, x₂) + D (x₂, x₄)) := by simpa [D] using ht
      _ ≤ s * (M + 2 * s * M) := by gcongr
      _ = (s + 2 * s ^ 2) * M := by ring
  have hp0 : 0 ≤ p := by positivity
  have hK0 : 0 ≤ s + 2 * s ^ 2 := by positivity
  have hreal :
      D (x₁, x₄) ^ p ≤
        2 * max (D (x₁, x₂) ^ p)
          (max (D (x₂, x₃) ^ p) (D (x₃, x₄) ^ p)) := by
    calc
      D (x₁, x₄) ^ p ≤ ((s + 2 * s ^ 2) * M) ^ p :=
        Real.rpow_le_rpow (NNReal.coe_nonneg _) h14 hp0
      _ = (s + 2 * s ^ 2) ^ p * M ^ p := Real.mul_rpow hK0 hM0
      _ ≤ 2 * M ^ p := by
        gcongr
      _ = 2 * max (D (x₁, x₂) ^ p)
          (max (D (x₂, x₃) ^ p) (D (x₃, x₄) ^ p)) := by
        dsimp [M, D]
        rw [Real.rpow_max (NNReal.coe_nonneg _)
          (by
            exact le_trans (NNReal.coe_nonneg _) (le_max_left _ _)) hp0]
        rw [Real.rpow_max (NNReal.coe_nonneg _) (NNReal.coe_nonneg _) hp0]
  exact_mod_cast (by simpa [p, D] using hreal)

/- accepted add_to_file helper 3 -/
lemma caristi_orbit_tendsto_pair
    (X : Type*) (s : ℝ) (d : X × X → NNReal) (Φ : X → NNReal)
    (f : X → X) (A : ℝ)
    (hs : 1 ≤ s)
    (hd_zero : ∀ x y : X, d (x, y) = 0 ↔ x = y)
    (hd_symm : ∀ x y : X, d (x, y) = d (y, x))
    (hd_triangle : ∀ x y z : X,
      (d (x, y) : ℝ) ≤ s * ((d (x, z) : ℝ) + (d (z, y) : ℝ)))
    (hA : 1 < A)
    (hcaristi : ∀ x : X,
      (d (x, f x) : ℝ) ≤ (Φ x : ℝ) - A * (Φ (f x) : ℝ))
    (x₀ : X) :
    Filter.Tendsto (fun p : ℕ × ℕ => d ((f^[p.1]) x₀, (f^[p.2]) x₀))
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
  let x : ℕ → X := fun n => (f^[n]) x₀
  let K : ℝ := s + 2 * s ^ 2
  obtain ⟨N, hNgt⟩ := exists_nat_gt K
  have hKpos : 0 < K := by
    dsimp [K]
    positivity
  have hNpos : 0 < N := by
    have hNR : (0:ℝ) < N := lt_trans hKpos hNgt
    exact_mod_cast hNR
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hNpos
  let p : ℝ := (N : ℝ)⁻¹
  have hp0 : 0 ≤ p := by positivity
  have hpne : p ≠ 0 := by positivity
  have hK0 : 0 ≤ K := le_of_lt hKpos
  have hbase : K ≤ (2 ^ N : ℝ) := by
    have hNpow : (N : ℝ) < (2 ^ N : ℝ) := by
      exact_mod_cast (Nat.lt_two_pow_self : N < 2 ^ N)
    linarith
  have hpow : K ^ p ≤ 2 := by
    calc
      K ^ p ≤ ((2 ^ N : ℝ) ^ p) := Real.rpow_le_rpow hK0 hbase hp0
      _ = 2 := by
        dsimp [p]
        rw [← Real.rpow_natCast (2 : ℝ) N]
        rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        field_simp [hN0]
        norm_num
  let q : X → X → NNReal := fun u v => (d (u, v) : NNReal) ^ p
  have hq_self : ∀ u : X, q u u = 0 := by
    intro u
    have hduu : d (u, u) = 0 := (hd_zero u u).2 rfl
    simp [q, hduu, hpne]
  have hq_comm : ∀ u v : X, q u v = q v u := by
    intro u v
    simp [q, hd_symm u v]
  have hq_four : ∀ x₁ x₂ x₃ x₄ : X,
      q x₁ x₄ ≤ 2 * max (q x₁ x₂) (max (q x₂ x₃) (q x₃ x₄)) := by
    intro x₁ x₂ x₃ x₄
    simpa [q, p, K] using
      bmetric_predist_four_max X s d hs hd_triangle hNpos (by simpa [K, p] using hpow)
        x₁ x₂ x₃ x₄
  letI P : PseudoMetricSpace X := PseudoMetricSpace.ofPreNNDist q hq_self hq_comm
  have hphi : ∀ n : ℕ, (Φ (x n) : ℝ) ≤ (Φ x₀ : ℝ) * A⁻¹ ^ n := by
    intro n
    simpa [x] using caristi_iterate_phi_bound X d Φ f A hA hcaristi x₀ n
  have hstep_phi : ∀ n : ℕ, (d (x n, x (n + 1)) : ℝ) ≤ (Φ (x n) : ℝ) := by
    intro n
    have hcar := hcaristi (x n)
    have hrw : x (n + 1) = f (x n) := by
      simpa [x] using (Function.iterate_succ_apply' f n x₀)
    have hdnonneg : (0:ℝ) ≤ d (x n, f (x n)) := NNReal.coe_nonneg _
    have hAphi : (0:ℝ) ≤ A * (Φ (f (x n)) : ℝ) := by positivity
    rw [hrw]
    linarith
  let C : ℝ := (Φ x₀ : ℝ) ^ p
  let r : ℝ := A⁻¹ ^ p
  have hqstep_bound : ∀ n : ℕ,
      ((q (x n) (x (n + 1)) : NNReal) : ℝ) ≤ C * r ^ n := by
    intro n
    have hpow_exch : ((A⁻¹ : ℝ) ^ n) ^ p = (A⁻¹ ^ p) ^ n := by
      rw [← Real.rpow_natCast (A⁻¹ : ℝ) n, ← Real.rpow_natCast ((A⁻¹ : ℝ) ^ p) n]
      rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ A⁻¹)]
      rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ A⁻¹)]
      congr 1
      ring
    calc
      (((q (x n) (x (n + 1)) : NNReal) : ℝ)) = (d (x n, x (n + 1)) : ℝ) ^ p := by
        simp [q, NNReal.coe_rpow]
      _ ≤ (Φ (x n) : ℝ) ^ p :=
        Real.rpow_le_rpow (NNReal.coe_nonneg _) (hstep_phi n) hp0
      _ ≤ ((Φ x₀ : ℝ) * A⁻¹ ^ n) ^ p :=
        Real.rpow_le_rpow (NNReal.coe_nonneg _) (hphi n) hp0
      _ = C * r ^ n := by
        dsimp [C, r]
        rw [Real.mul_rpow (NNReal.coe_nonneg _) (by positivity : (0:ℝ) ≤ A⁻¹ ^ n)]
        rw [hpow_exch]
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact Real.rpow_nonneg (by positivity : (0:ℝ) ≤ A⁻¹) p
  have hr1 : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one (by positivity : (0:ℝ) ≤ A⁻¹)
      (inv_lt_one_of_one_lt₀ hA) (by positivity : 0 < p)
  have hqstep_summable : Summable fun n : ℕ =>
      ((q (x n) (x (n + 1)) : NNReal) : ℝ) := by
    have hgeom : Summable fun n : ℕ => r ^ n := summable_geometric_of_lt_one hr0 hr1
    exact Summable.of_nonneg_of_le (fun n => NNReal.coe_nonneg _)
      hqstep_bound (hgeom.mul_left C)
  have hrho_tendsto :
      Filter.Tendsto (fun pair : ℕ × ℕ => dist (x pair.1) (x pair.2))
        (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
    exact tendsto_dist_pair_atTop_prod_zero_of_summable x
      (fun n => ((q (x n) (x (n + 1)) : NNReal) : ℝ))
      (fun n => NNReal.coe_nonneg _)
      (fun n => PseudoMetricSpace.dist_ofPreNNDist_le q hq_self hq_comm (x n) (x (n + 1)))
      hqstep_summable
  have hq_lower : ∀ pair : ℕ × ℕ,
      ((q (x pair.1) (x pair.2) : NNReal) : ℝ) ≤ 2 * dist (x pair.1) (x pair.2) := by
    intro pair
    exact PseudoMetricSpace.le_two_mul_dist_ofPreNNDist q hq_self hq_comm hq_four
      (x pair.1) (x pair.2)
  have hq_tendsto :
      Filter.Tendsto (fun pair : ℕ × ℕ =>
          ((q (x pair.1) (x pair.2) : NNReal) : ℝ))
        (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using hrho_tendsto.const_mul (2 : ℝ))
      (fun pair => NNReal.coe_nonneg _) hq_lower
  have hpow_tendsto :
      Filter.Tendsto (fun pair : ℕ × ℕ =>
          (((q (x pair.1) (x pair.2) : NNReal) : ℝ)) ^ N)
        (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
    have h := hq_tendsto.pow N
    simpa [hNpos.ne'] using h
  have hpow_eq :
      (fun pair : ℕ × ℕ => (((q (x pair.1) (x pair.2) : NNReal) : ℝ)) ^ N) =
        fun pair : ℕ × ℕ => (d (x pair.1, x pair.2) : ℝ) := by
    funext pair
    simp [q, p, NNReal.coe_rpow,
      Real.rpow_inv_natCast_pow (NNReal.coe_nonneg (d (x pair.1, x pair.2))) hNpos.ne']
  rw [hpow_eq] at hpow_tendsto
  exact (NNReal.tendsto_coe).1 (by simpa [x] using hpow_tendsto)

/- verified submission -/
theorem caristi_kirk_bMetric_fixed_point
    (X : Type*) [Nonempty X]
    (s : ℝ) (d : X × X → NNReal) (Φ : X → NNReal) (f : X → X) (A : ℝ)
    (hs : 1 ≤ s)
    (hd_zero : ∀ x y : X, d (x, y) = 0 ↔ x = y)
    (hd_symm : ∀ x y : X, d (x, y) = d (y, x))
    (hd_triangle : ∀ x y z : X,
      (d (x, y) : ℝ) ≤ s * ((d (x, z) : ℝ) + (d (z, y) : ℝ)))
    (hcomplete : ∀ x : ℕ → X,
      Filter.Tendsto (fun p : ℕ × ℕ => d (x p.1, x p.2))
        (Filter.atTop ×ˢ Filter.atTop) (nhds 0) →
      ∃ u : X, Filter.Tendsto (fun n : ℕ => d (x n, u)) Filter.atTop (nhds 0))
    (hA : 1 < A)
    (hf_continuous : ∀ (x : ℕ → X) (u : X),
      Filter.Tendsto (fun n : ℕ => d (x n, u)) Filter.atTop (nhds 0) →
      Filter.Tendsto (fun n : ℕ => d (f (x n), f u)) Filter.atTop (nhds 0))
    (hcaristi : ∀ x : X,
      (d (x, f x) : ℝ) ≤ (Φ x : ℝ) - A * (Φ (f x) : ℝ)) :
    ∀ x₀ : X, ∃ u : X, f u = u ∧
      Filter.Tendsto (fun n : ℕ => d ((f^[n]) x₀, u)) Filter.atTop (nhds 0) := by
  intro x₀
  let x : ℕ → X := fun n => (f^[n]) x₀
  have hcauchy :
      Filter.Tendsto (fun p : ℕ × ℕ => d (x p.1, x p.2))
        (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
    simpa [x] using caristi_orbit_tendsto_pair X s d Φ f A hs hd_zero hd_symm
      hd_triangle hA hcaristi x₀
  obtain ⟨u, hu⟩ := hcomplete x hcauchy
  have hfx : Filter.Tendsto (fun n : ℕ => d (f (x n), f u)) Filter.atTop (nhds 0) :=
    hf_continuous x u hu
  have hshift : Filter.Tendsto (fun n : ℕ => d (x (n + 1), u)) Filter.atTop (nhds 0) := by
    simpa [Function.comp_def, Nat.add_comm] using
      hu.comp (Filter.tendsto_add_atTop_nat 1)
  have hupper_tendsto : Filter.Tendsto
      (fun n : ℕ => s * ((d (f (x n), f u) : ℝ) + (d (x (n + 1), u) : ℝ)))
      Filter.atTop (nhds 0) := by
    have hfxR : Filter.Tendsto (fun n : ℕ => (d (f (x n), f u) : ℝ))
        Filter.atTop (nhds 0) := (NNReal.tendsto_coe).2 hfx
    have hshiftR : Filter.Tendsto (fun n : ℕ => (d (x (n + 1), u) : ℝ))
        Filter.atTop (nhds 0) := (NNReal.tendsto_coe).2 hshift
    simpa using (hfxR.add hshiftR).const_mul s
  have hineq : ∀ n : ℕ,
      (d (f u, u) : ℝ) ≤
        s * ((d (f (x n), f u) : ℝ) + (d (x (n + 1), u) : ℝ)) := by
    intro n
    have ht := hd_triangle (f u) u (f (x n))
    have hsymm1 : (d (f u, f (x n)) : ℝ) = (d (f (x n), f u) : ℝ) := by
      exact congrArg NNReal.toReal (hd_symm (f u) (f (x n)))
    have hrw : x (n + 1) = f (x n) := by
      simpa [x] using (Function.iterate_succ_apply' f n x₀)
    calc
      (d (f u, u) : ℝ) ≤ s * ((d (f u, f (x n)) : ℝ) + (d (f (x n), u) : ℝ)) := ht
      _ = s * ((d (f (x n), f u) : ℝ) + (d (x (n + 1), u) : ℝ)) := by
        rw [hsymm1, ← hrw]
  have hconst_tendsto_real : Filter.Tendsto (fun _ : ℕ => (d (f u, u) : ℝ))
      Filter.atTop (nhds 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper_tendsto
      (fun _ => NNReal.coe_nonneg _) hineq
  have hconst_tendsto : Filter.Tendsto (fun _ : ℕ => d (f u, u))
      Filter.atTop (nhds 0) := (NNReal.tendsto_coe).1 hconst_tendsto_real
  have hzero : d (f u, u) = 0 := by
    have h := tendsto_nhds_unique hconst_tendsto tendsto_const_nhds
    exact h.symm
  have hfixed : f u = u := (hd_zero (f u) u).1 hzero
  exact ⟨u, hfixed, by simpa [x] using hu⟩


#check_dependency_graph "caristi_kirk_bMetric_fixed_point" against "{\"edges\":[{\"conclusion\":{\"name\":\"hcauchy\",\"statement\":\"Filter.Tendsto (fun p => d (x p.1, x p.2)) (Filter.atTop ×ˢ Filter.atTop) (nhds 0)\"},\"graphEdgeId\":\"h_001_hcauchy\",\"premises\":[{\"name\":\"hs\",\"statement\":\"1 ≤ s\"},{\"name\":\"hd_zero\",\"statement\":\"∀ (x y : X), d (x, y) = 0 ↔ x = y\"},{\"name\":\"hd_symm\",\"statement\":\"∀ (x y : X), d (x, y) = d (y, x)\"},{\"name\":\"hd_triangle\",\"statement\":\"∀ (x y z : X), ↑(d (x, y)) ≤ s * (↑(d (x, z)) + ↑(d (z, y)))\"},{\"name\":\"hA\",\"statement\":\"1 < A\"},{\"name\":\"hcaristi\",\"statement\":\"∀ (x : X), ↑(d (x, f x)) ≤ ↑(Φ x) - A * ↑(Φ (f x))\"}],\"rawEdgeId\":\"telescope_17\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∃ u, f u = u ∧ Filter.Tendsto (fun n => d (f^[n] x₀, u)) Filter.atTop (nhds 0)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hd_zero\",\"statement\":\"∀ (x y : X), d (x, y) = 0 ↔ x = y\"},{\"name\":\"hd_symm\",\"statement\":\"∀ (x y : X), d (x, y) = d (y, x)\"},{\"name\":\"hd_triangle\",\"statement\":\"∀ (x y z : X), ↑(d (x, y)) ≤ s * (↑(d (x, z)) + ↑(d (z, y)))\"},{\"name\":\"hcomplete\",\"statement\":\"∀ (x : ℕ → X), Filter.Tendsto (fun p => d (x p.1, x p.2)) (Filter.atTop ×ˢ Filter.atTop) (nhds 0) → ∃ u, Filter.Tendsto (fun n => d (x n, u)) Filter.atTop (nhds 0)\"},{\"name\":\"hf_continuous\",\"statement\":\"∀ (x : ℕ → X) (u : X), Filter.Tendsto (fun n => d (x n, u)) Filter.atTop (nhds 0) → Filter.Tendsto (fun n => d (f (x n), f u)) Filter.atTop (nhds 0)\"},{\"name\":\"hcauchy\",\"statement\":\"Filter.Tendsto (fun p => d (x p.1, x p.2)) (Filter.atTop ×ˢ Filter.atTop) (nhds 0)\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0489_caristi_kirk_bmetric_fixed_point\",\"reconstructedProofSha256\":\"fb7c2ed30a2457a3fe100abbf439e471d2a98f12fac28c3d6456b7c379bc0e0f\",\"selectedEdgeCount\":2,\"theoremName\":\"caristi_kirk_bMetric_fixed_point\",\"topologySha256\":\"e3c506562155440bc52f1df77609cd5aa3e4eb91c6122edfd93871c94b5cd418\"}"
