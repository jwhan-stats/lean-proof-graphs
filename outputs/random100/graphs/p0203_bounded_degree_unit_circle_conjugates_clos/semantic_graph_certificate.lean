import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p0203_bounded_degree_unit_circle_conjugates_clos
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 0d3ed57d531cecb968ecb1c17477c7cc833bca9b3dff39bd1ddde5a273c210da
-- reconstructed_proof_sha256: 3f4b66458cca99b3424a1e5e891e895af9d70123ff9756984be2e507410ea525
-- selected_edge_count: 1

/- accepted add_to_file helper 1 -/
lemma finite_algebraic_integer_of_bounded_conjugates_inter_Icc
    (N : ℕ) (a b : ℝ) :
    ({x : ℝ | 1 < x ∧
        IsIntegral ℤ x ∧
        (minpoly ℚ x).natDegree ≤ N ∧
        (∀ z : ℂ,
          ((minpoly ℚ x).map (algebraMap ℚ ℂ)).IsRoot z →
          z ≠ (x : ℂ) → ‖z‖ ≤ 1)} ∩ Set.Icc a b).Finite := by
  let R : ℝ := max |a| |b|
  let M : ℝ := max R 1 ^ N * ↑(N.choose (N / 2))
  let K : ℤ := (⌈M⌉₊ : ℤ)
  let U : Set ℤ := Set.Icc (-K) K
  have hU : U.Finite := by
    dsimp [U]
    exact Set.finite_Icc (-K) K
  have hroots_finite :
      (⋃ f : Polynomial ℤ,
        ⋃ (_ : f.natDegree ≤ N ∧ ∀ i : ℕ, f.coeff i ∈ U),
          ↑((Polynomial.map (algebraMap ℤ ℝ) f).roots.toFinset : Set ℝ)).Finite := by
    exact Polynomial.bUnion_roots_finite (algebraMap ℤ ℝ) N hU
  refine hroots_finite.subset ?_
  intro x hx
  rcases hx with ⟨hxS, hxIcc⟩
  rcases hxS with ⟨hxgt, hZ, hdeg, hconj⟩
  let q : Polynomial ℤ := minpoly ℤ x
  have hQ : IsIntegral ℚ x := IsIntegral.tower_top hZ
  have hqmonic : q.Monic := minpoly.monic hZ
  have hpmonic : (minpoly ℚ x).Monic := minpoly.monic hQ
  have hmin : minpoly ℚ x = q.map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hZ
  have hmaps : (minpoly ℚ x).map (algebraMap ℚ ℂ) = q.map (algebraMap ℤ ℂ) := by
    rw [hmin, Polynomial.map_map]
    congr 1
  have hqdeg : q.natDegree ≤ N := by
    have hdegmap : (q.map (algebraMap ℤ ℚ)).natDegree = q.natDegree :=
      Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective ℤ ℚ) q
    have hpq : (minpoly ℚ x).natDegree = q.natDegree := by
      rw [hmin, hdegmap]
    exact hpq ▸ hdeg
  have hx_abs : |x| ≤ R := by
    have haR : |a| ≤ R := le_max_left |a| |b|
    have hbR : |b| ≤ R := le_max_right |a| |b|
    apply abs_le.mpr
    constructor
    · have hnega : -R ≤ a := by
        have h1 : -|a| ≤ a := neg_abs_le a
        have h2 : -R ≤ -|a| := by linarith
        linarith
      linarith [hxIcc.1]
    · have hble : b ≤ R := le_trans (le_abs_self b) hbR
      linarith [hxIcc.2]
  have hrootbound : ∀ z ∈ (q.map (algebraMap ℤ ℂ)).roots, ‖z‖ ≤ max R 1 := by
    intro z hz
    rw [← hmaps] at hz
    have hzroot : ((minpoly ℚ x).map (algebraMap ℚ ℂ)).IsRoot z :=
      (Polynomial.mem_roots (hpmonic.map _).ne_zero).mp hz
    by_cases hzx : z = (x : ℂ)
    · subst z
      calc
        ‖(x : ℂ)‖ = |x| := by simp
        _ ≤ R := hx_abs
        _ ≤ max R 1 := le_max_left R 1
    · exact (hconj z hzroot hzx).trans (le_max_right R 1)
  have hcoeffU : ∀ i : ℕ, q.coeff i ∈ U := by
    intro i
    have hc' := Polynomial.coeff_bdd_of_roots_le (algebraMap ℤ ℂ) hqmonic
      (IsAlgClosed.splits _) hqdeg hrootbound i
    have hmax : max (max R 1) 1 = max R 1 := max_eq_left (le_max_right R 1)
    have hc : ‖((q.map (algebraMap ℤ ℂ)).coeff i)‖ ≤ M := by
      simpa [M, hmax] using hc'
    rw [Polynomial.coeff_map] at hc
    change ‖((q.coeff i : ℤ) : ℂ)‖ ≤ M at hc
    rw [Complex.norm_intCast] at hc
    have hreal : |(q.coeff i : ℝ)| ≤ (⌈M⌉₊ : ℝ) := hc.trans (Nat.le_ceil M)
    have hzint : |q.coeff i| ≤ (⌈M⌉₊ : ℤ) := by exact_mod_cast hreal
    dsimp [U, K]
    exact abs_le.mp hzint
  have hxroot : (q.map (algebraMap ℤ ℝ)).IsRoot x := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap, minpoly.aeval]
  have hxmemroots : x ∈ ((q.map (algebraMap ℤ ℝ)).roots.toFinset : Finset ℝ) := by
    exact Multiset.mem_toFinset.mpr
      ((Polynomial.mem_roots (hqmonic.map _).ne_zero).mpr hxroot)
  refine Set.mem_iUnion.mpr ⟨q, ?_⟩
  refine Set.mem_iUnion.mpr ⟨⟨hqdeg, hcoeffU⟩, ?_⟩
  exact hxmemroots

/- accepted add_to_file helper 2 -/
lemma closed_and_isolated_of_finite_inter_Icc_one
    (S : Set ℝ)
    (hfin : ∀ x : ℝ, (S ∩ Set.Icc (x - 1) (x + 1)).Finite) :
    IsClosed S ∧
      ∀ x ∈ S, ∃ ε > 0, S ∩ Set.Ioo (x - ε) (x + ε) = {x} := by
  constructor
  · rw [← isOpen_compl_iff, Metric.isOpen_iff]
    intro x hx
    let T : Set ℝ := S ∩ Set.Icc (x - 1) (x + 1)
    have hT : T.Finite := hfin x
    have hxnotT : x ∉ T := by
      intro hxT
      exact hx hxT.1
    have hTopen : IsOpen Tᶜ := hT.isClosed.isOpen_compl
    obtain ⟨δ, hδpos, hδball⟩ := (Metric.isOpen_iff.mp hTopen) x hxnotT
    refine ⟨min δ 1, lt_min hδpos zero_lt_one, ?_⟩
    intro y hy hyS
    have hyδ : y ∈ Metric.ball x δ := (Metric.ball_subset_ball (min_le_left δ 1)) hy
    have hyTcomp : y ∉ T := hδball hyδ
    have hyIcc : y ∈ Set.Icc (x - 1) (x + 1) := by
      have hyone : y ∈ Metric.ball x 1 := (Metric.ball_subset_ball (min_le_right δ 1)) hy
      rw [Metric.mem_ball, Real.dist_eq] at hyone
      have hxy : |y - x| < 1 := by
        linarith [abs_sub_comm x y]
      constructor
      · linarith [neg_lt_of_abs_lt hxy]
      · linarith [lt_of_abs_lt hxy]
    exact hyTcomp ⟨hyS, hyIcc⟩
  · intro x hxS
    let T : Set ℝ := S ∩ Set.Icc (x - 1) (x + 1)
    have hT : T.Finite := hfin x
    have hxT : x ∈ T := by
      constructor
      · exact hxS
      · constructor <;> linarith
    obtain ⟨δ, hδpos, hδball⟩ :=
      Metric.exists_ball_inter_eq_singleton_of_mem_discrete hT.isDiscrete hxT
    refine ⟨min δ 1, lt_min hδpos zero_lt_one, ?_⟩
    ext y
    constructor
    · intro hy
      have hyδ : y ∈ Metric.ball x δ := by
        apply (Metric.ball_subset_ball (min_le_left δ 1))
        rw [Metric.mem_ball, Real.dist_eq]
        have hxy : |y - x| < min δ 1 := by
          apply abs_sub_lt_iff.mpr
          constructor <;> linarith [hy.2.1, hy.2.2]
        linarith [abs_sub_comm x y]
      have hyIcc : y ∈ Set.Icc (x - 1) (x + 1) := by
        have hlo : x - min δ 1 < y := hy.2.1
        have hhi : y < x + min δ 1 := hy.2.2
        constructor <;> linarith [min_le_right δ 1]
      have hyT : y ∈ T := ⟨hy.1, hyIcc⟩
      have : y ∈ Metric.ball x δ ∩ T := ⟨hyδ, hyT⟩
      rw [hδball] at this
      simpa using this
    · intro hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      constructor
      · exact hxS
      · constructor <;> linarith [lt_min hδpos zero_lt_one]

/- verified submission -/
theorem bounded_degree_unit_circle_conjugates_closed_discrete
    (B : ℝ) (hB : 0 < B) :
    let S_B : Set ℝ :=
      {x | 1 < x ∧
        IsIntegral ℤ x ∧
        ((minpoly ℚ x).natDegree : ℝ) ≤ B ∧
        (∀ z : ℂ,
          ((minpoly ℚ x).map (algebraMap ℚ ℂ)).IsRoot z →
          z ≠ (x : ℂ) → ‖z‖ ≤ 1) ∧
        (∃ z : ℂ,
          ((minpoly ℚ x).map (algebraMap ℚ ℂ)).IsRoot z ∧
          z ≠ (x : ℂ) ∧ ‖z‖ = 1)};
    IsClosed S_B ∧
      ∀ x ∈ S_B, ∃ ε > 0, S_B ∩ Set.Ioo (x - ε) (x + ε) = {x} := by
  let S_B : Set ℝ :=
      {x | 1 < x ∧
        IsIntegral ℤ x ∧
        ((minpoly ℚ x).natDegree : ℝ) ≤ B ∧
        (∀ z : ℂ,
          ((minpoly ℚ x).map (algebraMap ℚ ℂ)).IsRoot z →
          z ≠ (x : ℂ) → ‖z‖ ≤ 1) ∧
        (∃ z : ℂ,
          ((minpoly ℚ x).map (algebraMap ℚ ℂ)).IsRoot z ∧
          z ≠ (x : ℂ) ∧ ‖z‖ = 1)}
  change IsClosed S_B ∧
      ∀ x ∈ S_B, ∃ ε > 0, S_B ∩ Set.Ioo (x - ε) (x + ε) = {x}
  have hfin : ∀ x : ℝ, (S_B ∩ Set.Icc (x - 1) (x + 1)).Finite := by
    intro x
    refine (finite_algebraic_integer_of_bounded_conjugates_inter_Icc
      ⌊B⌋₊ (x - 1) (x + 1)).subset ?_
    intro y hy
    rcases hy with ⟨hyS, hyIcc⟩
    rcases hyS with ⟨hygt, hyint, hydeg, hyroots, hyunit⟩
    constructor
    · exact ⟨hygt, hyint, Nat.le_floor hydeg, hyroots⟩
    · exact hyIcc
  exact closed_and_isolated_of_finite_inter_Icc_one S_B hfin


#check_dependency_graph "bounded_degree_unit_circle_conjugates_closed_discrete" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let S_B := {x | 1 < x ∧ IsIntegral ℤ x ∧ ↑(minpoly ℚ x).natDegree ≤ B ∧ (∀ (z : ℂ), (Polynomial.map (algebraMap ℚ ℂ) (minpoly ℚ x)).IsRoot z → z ≠ ↑x → ‖z‖ ≤ 1) ∧ ∃ z, (Polynomial.map (algebraMap ℚ ℂ) (minpoly ℚ x)).IsRoot z ∧ z ≠ ↑x ∧ ‖z‖ = 1}; IsClosed S_B ∧ ∀ x ∈ S_B, ∃ ε > 0, S_B ∩ Set.Ioo (x - ε) (x + ε) = {x}\"},\"graphEdgeId\":\"h_goal\",\"premises\":[],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0203_bounded_degree_unit_circle_conjugates_clos\",\"reconstructedProofSha256\":\"3f4b66458cca99b3424a1e5e891e895af9d70123ff9756984be2e507410ea525\",\"selectedEdgeCount\":1,\"theoremName\":\"bounded_degree_unit_circle_conjugates_closed_discrete\",\"topologySha256\":\"0d3ed57d531cecb968ecb1c17477c7cc833bca9b3dff39bd1ddde5a273c210da\"}"
