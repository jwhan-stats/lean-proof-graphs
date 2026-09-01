import Init

/- Generated batch: one abstract topology theorem per selected graph. -/

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0019_unique_diagonal_perfect_matching_iff_no_al
-- topology_sha256: a1634d7f40419c801a109035bdeb7fe0590e91296c79e9c810f08e9363381342
namespace TopologyCertificate_p0019_unique_diagonal_perfect_matching_iff_no_al

-- N001 = hdiag: ∀ (i : Fin n), G.Adj (x i) (y i)
-- N002 = hunmixed: ∀ (C : Set V), Minimal G.IsVertexCover C → C.ncard = n
-- N003 = hxy: Function.Bijective (Sum.elim x y)
-- N004 = hY: Maximal G.IsIndepSet (Set.range y)
-- N005 = hBC: B ↔ C
-- N006 = goal: ((∃ M, M.IsPerfectMatching ∧ (∀ (u v : V), M.Adj u v ↔ ∃ i, u = x i ∧ v = y i ∨ u = y i ∧ v = x i) ∧ ∀ (M' : G.Subgraph), M'.IsPerfectMatching → M' = M) ↔ ∀ (i j : Fin n), i < j → ¬(G.Adj (x i) (y i) ∧ G.Adj (y i) (x j) ∧ G.Adj (x j) (y j) ∧ G.Adj (y j) (x i))) ∧ ((∀ (i j : Fin n), i < j → ¬(G.Adj (x i) (y i) ∧ G.Adj (y i) (x j) ∧ G.Adj (x j) (y j) ∧ G.Adj (y j) (x i))) ↔ ∀ (r : ℕ) (i : Fin (r + 2) → Fin n), Function.Injective i → ¬∀ (s : Fin (r + 2)), G.Adj (x (i s)) (y (i s)) ∧ G.Adj (y (i s)) (x (i (s + 1))))

-- E001 represents h_001_hbc
-- E002 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N003 → N004 → N001 → N002 → N005)
    (E002 : N003 → N004 → N001 → N005 → N006)
    : N006 := by
  have H_N005 : N005 := E001 B003 B004 B001 B002
  have H_N006 : N006 := E002 B003 B004 B001 H_N005
  exact H_N006

end TopologyCertificate_p0019_unique_diagonal_perfect_matching_iff_no_al

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0043_independentdominationnumber_eq_dominationn
-- topology_sha256: c61f4a83bcbad58f8e02ac4870c2a4154fb38a1c4798a2c300e2500f89251222
namespace TopologyCertificate_p0043_independentdominationnumber_eq_dominationn

-- N001 = hhigh: G.IsIndepSet {v | 2 < (G.neighborSet v).ncard}
-- N002 = goal: sInf {n | ∃ D, D.card = n ∧ G.IsIndepSet ↑D ∧ ∀ v ∉ D, ∃ w ∈ D, G.Adj v w} = sInf {n | ∃ D, D.card = n ∧ ∀ v ∉ D, ∃ w ∈ D, G.Adj v w}

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    : N002 := by
  have H_N002 : N002 := E001 B001
  exact H_N002

end TopologyCertificate_p0043_independentdominationnumber_eq_dominationn

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0109_exists_atomic_puiseux_monoid_without_singl
-- topology_sha256: 1f8eb1a2dee6809ed1a7bee3e31417e9eae1d070ed67756f049a7393ee1739f4
namespace TopologyCertificate_p0109_exists_atomic_puiseux_monoid_without_singl

-- N001 = goal: ∃ M, (∀ (x : ↥M), ∃ l, (∀ a ∈ l, AddIrreducible a) ∧ l.sum = x) ∧ ∀ (x : ↥M), {n | ∃ l, l.length = n ∧ (∀ a ∈ l, AddIrreducible a) ∧ l.sum = x} ≠ {2}

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p0109_exists_atomic_puiseux_monoid_without_singl

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0130_affinesemigroup_normal_equiv
-- topology_sha256: b6e0b51344ee410e1677d05af1a57204e4ffb055c0a46ace81c966c822d992e2
namespace TopologyCertificate_p0130_affinesemigroup_normal_equiv

-- N001 = haLI: LinearIndependent ℝ fun i j => ↑(a i j)
-- N002 = haS: ∀ (i : Fin d), a i ∈ S
-- N003 = hcone: ∀ (x : Fin d → ℝ), x ∈ ConvexCone.hull ℝ ((fun u j => ↑(u j)) '' ↑S) ↔ ∃ c, (∀ (i : Fin d), 0 ≤ c i) ∧ x = ∑ i, c i • fun j => ↑(a i j)
-- N004 = hd: 1 ≤ d
-- N005 = goal: let natToInt := fun u j => ↑(u j); let natToReal := fun u j => ↑(u j); let intToReal := fun u j => ↑(u j); let C := {x | ∃ c, (∀ (i : Fin d), 0 ≤ c i) ∧ x = ∑ i, c i • fun j => ↑(a i j)}; let relintC := {x | ∃ c, (∀ (i : Fin d), 0 < c i) ∧ x = ∑ i, c i • fun j => ↑(a i j)}; let fundamentalParallelepiped := {x | ∃ c, (∀ (i : Fin d), 0 ≤ c i ∧ c i < 1) ∧ x = ∑ i, c i • fun j => ↑(a i j)}; let apery := {w | w ∈ S ∧ ∀ (i : Fin d), ¬∃ s ∈ S, w = s + a i}; let leS := fun u v => ∃ s ∈ S, v = u + s; let maximalApery := fun m => m ∈ apery ∧ ∀ w ∈ apery, leS m w → leS w m; let QF := {f | ∃ m, maximalApery m ∧ f = natToInt m - ∑ i, natToInt (a i)}; let G := {z | ∃ u ∈ S, ∃ v ∈ S, z = natToInt u - natToInt v}; let normal := natToInt '' ↑S = G ∩ {z | intToReal z ∈ C}; let condition2 := ∀ f ∈ QF, -f ∈ natToInt '' ↑S ∧ intToReal (-f) ∈ relintC; let condition3 := ∀ f ∈ QF, intToReal (-f) ∈ relintC; let condition4 := ∀ w ∈ apery, natToReal w ∈ fundamentalParallelepiped; (normal ↔ condition2) ∧ (normal ↔ condition3) ∧ (normal ↔ condition4)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N004 → N002 → N001 → N003 → N005)
    : N005 := by
  have H_N005 : N005 := E001 B004 B002 B001 B003
  exact H_N005

end TopologyCertificate_p0130_affinesemigroup_normal_equiv

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0194_seifert_chi_div_e_lt_one
-- topology_sha256: 470b34ed7bca3de6884d3a0c03c78e97958a03ba5b950199a12ad928a6fa2baf
namespace TopologyCertificate_p0194_seifert_chi_div_e_lt_one

-- N001 = hcases: t = 3 ∧ (4 ≤ d ∨ d = 3 ∧ q 1 = 1 ∨ d = 2 ∧ q 1 = 1 ∧ q 2 = 1) ∨ t = 4 ∧ 3 ≤ d ∧ q 1 = 1 ∧ q 2 = 1 ∧ q 3 = 1
-- N002 = hcoprime: ∀ (i : ℕ), 1 ≤ i → i ≤ t → (n i).Coprime (q i)
-- N003 = he: 0 < ↑d - ∑ i ∈ Finset.Icc 1 t, ↑(q i) / ↑(n i)
-- N004 = hn: ∀ (i : ℕ), 1 ≤ i → i ≤ t → 2 ≤ n i
-- N005 = hq_lt: ∀ (i : ℕ), 1 ≤ i → i ≤ t → q i < n i
-- N006 = hq_pos: ∀ (i : ℕ), 1 ≤ i → i ≤ t → 1 ≤ q i
-- N007 = goal: let e := ↑d - ∑ i ∈ Finset.Icc 1 t, ↑(q i) / ↑(n i); let χ := -2 + ∑ i ∈ Finset.Icc 1 t, (1 - 1 / ↑(n i)); χ / e < 1

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (E001 : N004 → N006 → N005 → N002 → N003 → N001 → N007)
    : N007 := by
  have H_N007 : N007 := E001 B004 B006 B005 B002 B003 B001
  exact H_N007

end TopologyCertificate_p0194_seifert_chi_div_e_lt_one

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0203_bounded_degree_unit_circle_conjugates_clos
-- topology_sha256: 0d3ed57d531cecb968ecb1c17477c7cc833bca9b3dff39bd1ddde5a273c210da
namespace TopologyCertificate_p0203_bounded_degree_unit_circle_conjugates_clos

-- N001 = goal: let S_B := {x | 1 < x ∧ IsIntegral ℤ x ∧ ↑(minpoly ℚ x).natDegree ≤ B ∧ (∀ (z : ℂ), (Polynomial.map (algebraMap ℚ ℂ) (minpoly ℚ x)).IsRoot z → z ≠ ↑x → ‖z‖ ≤ 1) ∧ ∃ z, (Polynomial.map (algebraMap ℚ ℂ) (minpoly ℚ x)).IsRoot z ∧ z ≠ ↑x ∧ ‖z‖ = 1}; IsClosed S_B ∧ ∀ x ∈ S_B, ∃ ε > 0, S_B ∩ Set.Ioo (x - ε) (x + ε) = {x}

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p0203_bounded_degree_unit_circle_conjugates_clos

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0229_euclidean_decomposition_bound
-- topology_sha256: 60d8d4e289aa2948542a900b0644473c2588737e01bfa65a0a429d00fc12a92b
namespace TopologyCertificate_p0229_euclidean_decomposition_bound

-- N001 = hep: e ≤ p + 1
-- N002 = hp: Nat.Prime p
-- N003 = hsize: 4 * p ^ 2 ≤ n + 2
-- N004 = hp0: 0 < p
-- N005 = hp2: 2 ≤ p
-- N006 = goal: ∃ d, ∃ f < p, n + 2 = p * d + f + e ∧ d ≥ e + f + (2 * p - 2)

-- E001 represents h_001_hp0
-- E002 represents h_002_hp2
-- E003 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N002 → N004)
    (E002 : N002 → N005)
    (E003 : N002 → N003 → N001 → N004 → N005 → N006)
    : N006 := by
  have H_N004 : N004 := E001 B002
  have H_N005 : N005 := E002 B002
  have H_N006 : N006 := E003 B002 B003 B001 H_N004 H_N005
  exact H_N006

end TopologyCertificate_p0229_euclidean_decomposition_bound

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0246_formalpowerseries_automorphism_exact_seque
-- topology_sha256: 8fca2d9d47864411a13fe5cf51fc66dc9cb51f610c367e248277ea0507cb00dc
namespace TopologyCertificate_p0246_formalpowerseries_automorphism_exact_seque

-- N001 = hN: 2 ≤ N
-- N002 = hNpos: 0 < N
-- N003 = goal: ∃ Aut AutN, (∀ (ρ : PowerSeries ℂ ≃ₐ[ℂ] PowerSeries ℂ), ρ ∈ Aut ↔ Continuous ⇑ρ ∧ Continuous ⇑ρ.symm) ∧ (∀ (ρ : PowerSeries ℂ ≃ₐ[ℂ] PowerSeries ℂ), ρ ∈ AutN ↔ Continuous ⇑ρ ∧ Continuous ⇑ρ.symm ∧ ⇑ρ '' Set.range ⇑(PowerSeries.expand N ⋯) = Set.range ⇑(PowerSeries.expand N ⋯)) ∧ ∃ ι μ, (∀ (ρ : ↥AutN) (f : PowerSeries ℂ), (PowerSeries.expand N ⋯) (↑(μ ρ) f) = ↑ρ ((PowerSeries.expand N ⋯) f)) ∧ (∀ (ρ : ↥AutN), (PowerSeries.expand N ⋯) (↑(μ ρ) PowerSeries.X) = ↑ρ PowerSeries.X ^ N) ∧ (∀ (ε : ↥(rootsOfUnity N ℂ)), ↑(ι ε) PowerSeries.X = (algebraMap ℂ (PowerSeries ℂ)) ↑↑ε * PowerSeries.X) ∧ Function.Injective ⇑ι ∧ Function.Surjective ⇑μ ∧ ι.range = μ.ker ∧ ι.range ≤ Subgroup.center ↥AutN

-- E001 represents h_001_hnpos
-- E002 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    (E002 : N001 → N002 → N003)
    : N003 := by
  have H_N002 : N002 := E001 B001
  have H_N003 : N003 := E002 B001 H_N002
  exact H_N003

end TopologyCertificate_p0246_formalpowerseries_automorphism_exact_seque

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0252_reciprocal_eq_neg_one_pow_of_roots_abs_one
-- topology_sha256: 8135949077b0fb96d1c6fae3bccdb4227c53b9d315b1129708d80ccc0e0481f7
namespace TopologyCertificate_p0252_reciprocal_eq_neg_one_pow_of_roots_abs_one

-- N001 = hf: f ≠ 0
-- N002 = hn: Polynomial.rootMultiplicity 1 f = n
-- N003 = hroots: ∀ (z : ℂ), (Polynomial.map (algebraMap ℝ ℂ) f).IsRoot z → ‖z‖ = 1
-- N004 = hdvd: A ^ n ∣ f
-- N005 = goal: f.reverse = (-1) ^ n • f

-- E001 represents h_001_hdvd
-- E002 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N002 → N004)
    (E002 : N001 → N003 → N002 → N004 → N005)
    : N005 := by
  have H_N004 : N004 := E001 B002
  have H_N005 : N005 := E002 B001 B003 B002 H_N004
  exact H_N005

end TopologyCertificate_p0252_reciprocal_eq_neg_one_pow_of_roots_abs_one

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0256_marking_equivalence
-- topology_sha256: acea382a18f4676772634e4c125bc3b8781d6f109529629ba6e047944a7af310
namespace TopologyCertificate_p0256_marking_equivalence

-- N001 = hμ: irreducible μ
-- N002 = hν: irreducible ν
-- N003 = hn: 0 < n
-- N004 = goal: Relation.ReflTransGen Move μ ν

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N003 → N001 → N002 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B003 B001 B002
  exact H_N004

end TopologyCertificate_p0256_marking_equivalence

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0273_weighted_one_dimensional_dirichlet_lower_b
-- topology_sha256: 85a9ca16859e3f43eb966e57535a3693c8d641cc05d9875fedaae5db579da175
namespace TopologyCertificate_p0273_weighted_one_dimensional_dirichlet_lower_b

-- N001 = hθ0: 0 < θ₀
-- N002 = hθ1: θ₀ < 2 * Real.pi
-- N003 = hφac: AbsolutelyContinuousOnInterval φ 0 (2 * Real.pi)
-- N004 = hφderivL2: MeasureTheory.MemLp (deriv φ) 2 (MeasureTheory.volume.restrict (Set.Icc 0 (2 * Real.pi)))
-- N005 = hφend: φ (2 * Real.pi) - φ 0 = 2 * Real.pi
-- N006 = hαmeas: AEMeasurable α (MeasureTheory.volume.restrict (Set.Icc 0 (2 * Real.pi)))
-- N007 = hαmeasure: (MeasureTheory.volume.restrict (Set.Icc 0 (2 * Real.pi))) {θ | α θ = b ^ 2} = ENNReal.ofReal θ₀
-- N008 = hαvalues: ∀ᵐ (θ : ℝ) ∂MeasureTheory.volume.restrict (Set.Icc 0 (2 * Real.pi)), α θ ∈ {b ^ 2, 1}
-- N009 = hb0: 0 < b
-- N010 = hb1: b < 1
-- N011 = h0le: 0 ≤ 2 * Real.pi
-- N012 = hcs: L ^ 2 ≤ C * D
-- N013 = hD: D = 2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1)
-- N014 = hLnonneg: 0 ≤ L
-- N015 = hb2lt1: b ^ 2 < 1
-- N016 = hinterval_to_restrict: ∀ (f : ℝ → ℝ), ∫ (θ : ℝ) in 0..2 * Real.pi, f θ = ∫ (θ : ℝ), f θ ∂μ
-- N017 = hinv_gt_one: 1 < (b ^ 2)⁻¹
-- N018 = hIntg: ∫ (θ : ℝ), deriv φ θ ∂μ = 2 * Real.pi
-- N019 = hdenpos: 0 < 2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1)
-- N020 = hCeq: ∫ (θ : ℝ) in 0..2 * Real.pi, α θ * |deriv φ θ| ^ 2 = C
-- N021 = hLlower: 2 * Real.pi ≤ L
-- N022 = hTsq_le_Lsq: (2 * Real.pi) ^ 2 ≤ L ^ 2
-- N023 = hmain: 2 * Real.pi ^ 2 / (2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1)) ≤ 1 / 2 * C
-- N024 = goal: 1 / 2 * ∫ (θ : ℝ) in 0..2 * Real.pi, α θ * |deriv φ θ| ^ 2 ≥ 2 * Real.pi ^ 2 / (2 * Real.pi + θ₀ * ((b ^ 2)⁻¹ - 1))

-- E001 represents h_001_h0le
-- E002 represents h_003_hcs
-- E003 represents h_004_hd
-- E004 represents h_007_hlnonneg
-- E005 represents h_010_hb2lt1
-- E006 represents h_002_hinterval_to_restrict
-- E007 represents h_011_hinv_gt_one
-- E008 represents h_005_hintg
-- E009 represents h_012_hdenpos
-- E010 represents h_014_hceq
-- E011 represents h_006_hllower
-- E012 represents h_008_htsq_le_lsq
-- E013 represents h_013_hmain
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
    (E001 : N011)
    (E002 : N009 → N010 → N006 → N008 → N004 → N012)
    (E003 : N009 → N010 → N001 → N002 → N006 → N008 → N007 → N013)
    (E004 : N014)
    (E005 : N009 → N010 → N015)
    (E006 : N011 → N016)
    (E007 : N009 → N015 → N017)
    (E008 : N003 → N005 → N016 → N018)
    (E009 : N009 → N010 → N001 → N002 → N017 → N019)
    (E010 : N016 → N020)
    (E011 : N011 → N018 → N021)
    (E012 : N011 → N021 → N014 → N022)
    (E013 : N012 → N013 → N022 → N019 → N023)
    (E014 : N023 → N020 → N024)
    : N024 := by
  have H_N011 : N011 := E001
  have H_N012 : N012 := E002 B009 B010 B006 B008 B004
  have H_N013 : N013 := E003 B009 B010 B001 B002 B006 B008 B007
  have H_N014 : N014 := E004
  have H_N015 : N015 := E005 B009 B010
  have H_N016 : N016 := E006 H_N011
  have H_N017 : N017 := E007 B009 H_N015
  have H_N018 : N018 := E008 B003 B005 H_N016
  have H_N019 : N019 := E009 B009 B010 B001 B002 H_N017
  have H_N020 : N020 := E010 H_N016
  have H_N021 : N021 := E011 H_N011 H_N018
  have H_N022 : N022 := E012 H_N011 H_N021 H_N014
  have H_N023 : N023 := E013 H_N012 H_N013 H_N022 H_N019
  have H_N024 : N024 := E014 H_N023 H_N020
  exact H_N024

end TopologyCertificate_p0273_weighted_one_dimensional_dirichlet_lower_b

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0292_two_positive_roots_of_mu
-- topology_sha256: 50cc4749c4529bb764e87d2981f6c706ea22d32a28e9d891791887fe92f80b47
namespace TopologyCertificate_p0292_two_positive_roots_of_mu

-- N001 = hΛ: 0 < Λ
-- N002 = hM: 0 < M
-- N003 = hn: 4 ≤ n
-- N004 = goal: let lam := 2 * Λ / ((↑n - 2) * (↑n - 1)); let mu := fun r => 1 - 2 * M / r ^ (n - 3) - lam * r ^ 2; M ^ 2 * lam ^ (n - 3) < (↑n - 3) ^ (n - 3) / (↑n - 1) ^ (n - 1) → ∃ r_minus r_plus, 0 < r_minus ∧ r_minus < r_plus ∧ mu r_minus = 0 ∧ mu r_plus = 0 ∧ ∀ (r : ℝ), 0 < r → mu r = 0 → r = r_minus ∨ r = r_plus

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N003 → N002 → N001 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B003 B002 B001
  exact H_N004

end TopologyCertificate_p0292_two_positive_roots_of_mu

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0332_weighted_pointwise_inequality_on_circle
-- topology_sha256: 6f4bae9a03feda456d41ac3f456a5cbcdd29e3ad1446d5e45fe53e4ab70acc24
namespace TopologyCertificate_p0332_weighted_pointwise_inequality_on_circle

-- N001 = goal: ∃ C, 0 < C ∧ ∀ (f : ℝ → ℝ), Function.Periodic f (2 * Real.pi) → AbsolutelyContinuousOnInterval f (-Real.pi) Real.pi → f 0 = 0 → MeasureTheory.IntegrableOn (fun x => |deriv f x| ^ 2 / Real.sin (x / 2) ^ 2) (Set.Icc (-Real.pi) Real.pi) MeasureTheory.volume → essSup (fun x => |f x| / |Real.sin (x / 2)|) (MeasureTheory.volume.restrict (Set.Icc (-Real.pi) Real.pi)) ≤ C * √(∫ (x : ℝ) in Set.Icc (-Real.pi) Real.pi, |deriv f x| ^ 2 / Real.sin (x / 2) ^ 2)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p0332_weighted_pointwise_inequality_on_circle

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0367_weakhomotopyequivalence_of_iunion_open_res
-- topology_sha256: d8054a5027501cba618538efb0a26a4cda17a805880f39cd49477c4e14fe5b91
namespace TopologyCertificate_p0367_weakhomotopyequivalence_of_iunion_open_res

-- N001 = hf: ∀ (n : { n // 1 ≤ n }), let g := { toFun := fun x => f ↑x, continuous_toFun := ⋯ }; Function.Bijective (Quotient.map ⇑g ⋯) ∧ ∀ (k : ℕ) (x : ↑(U n)), Function.Bijective (Quotient.map (fun p => ⟨g.comp ↑p, ⋯⟩) ⋯)
-- N002 = hU_cover: ⋃ n, U n = Set.univ
-- N003 = hU_mono: Monotone U
-- N004 = hU_open: ∀ (n : { n // 1 ≤ n }), IsOpen (U n)
-- N005 = goal: Function.Bijective (Quotient.map ⇑f ⋯) ∧ ∀ (k : ℕ) (x : X), Function.Bijective (Quotient.map (fun p => ⟨f.comp ↑p, ⋯⟩) ⋯)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N004 → N003 → N002 → N001 → N005)
    : N005 := by
  have H_N005 : N005 := E001 B004 B003 B002 B001
  exact H_N005

end TopologyCertificate_p0367_weakhomotopyequivalence_of_iunion_open_res

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0378_finite_g_set_subcategory_contains_all_mono
-- topology_sha256: c7aa6e819654a31c1b25326607ad68d547a4afb2514a948524abcfdf1173b344
namespace TopologyCertificate_p0378_finite_g_set_subcategory_contains_all_mono

-- N001 = hD_coproduct: D.IsStableUnderFiniteCoproducts
-- N002 = hD_empty: D (CategoryTheory.Limits.initial.to (⊤_ Action FintypeCat G))
-- N003 = hD_id: ∀ {X Y : Action FintypeCat G} (f : X ⟶ Y), D f → D (CategoryTheory.CategoryStruct.id X) ∧ D (CategoryTheory.CategoryStruct.id Y)
-- N004 = hD_pullback: D.IsStableUnderBaseChange
-- N005 = hf: CategoryTheory.MorphismProperty.monomorphisms (Action FintypeCat G) f
-- N006 = inst._@.proofs.1466848982._hygCtx._hyg.6: Finite G
-- N007 = htruth: D (Rollout_p0378_finite_g_set_subcategory_contains_all_mono.FiniteGSetProof.truthU G)
-- N008 = goal: D f

-- E001 represents h_001_htruth
-- E002 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (N008 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (E001 : N006 → N003 → N004 → N001 → N002 → N007)
    (E002 : N004 → N005 → N007 → N008)
    : N008 := by
  have H_N007 : N007 := E001 B006 B003 B004 B001 B002
  have H_N008 : N008 := E002 B004 B005 H_N007
  exact H_N008

end TopologyCertificate_p0378_finite_g_set_subcategory_contains_all_mono

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0412_almosttrivial_and_almostfinite_of_shortexa
-- topology_sha256: 9cb15c8d2be7ea66532caeaf9ddd881b9b97f2e4113556f5d73c0e7fcd4dc7c6
namespace TopologyCertificate_p0412_almosttrivial_and_almostfinite_of_shortexa

-- N001 = hf: Function.Injective ⇑f
-- N002 = hfg: Function.Exact ⇑f ⇑g
-- N003 = hg: Function.Surjective ⇑g
-- N004 = inst._@.proofs.1734391863._hygCtx._hyg.6: IsDomain R
-- N005 = goal: ((∃ r, r ≠ 0 ∧ ∀ (m : M₁), r • m = 0) ↔ (∃ r, r ≠ 0 ∧ ∀ (m : M₀), r • m = 0) ∧ ∃ r, r ≠ 0 ∧ ∀ (m : M₂), r • m = 0) ∧ (IsNoetherianRing R → ((∃ r, r ≠ 0 ∧ ∀ (m : ↥(Submodule.torsion R M₁)), r • m = 0) ∧ Module.Finite R (M₁ ⧸ Submodule.torsion R M₁) ↔ ((∃ r, r ≠ 0 ∧ ∀ (m : ↥(Submodule.torsion R M₀)), r • m = 0) ∧ Module.Finite R (M₀ ⧸ Submodule.torsion R M₀)) ∧ (∃ r, r ≠ 0 ∧ ∀ (m : ↥(Submodule.torsion R M₂)), r • m = 0) ∧ Module.Finite R (M₂ ⧸ Submodule.torsion R M₂)))

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N004 → N001 → N002 → N003 → N005)
    : N005 := by
  have H_N005 : N005 := E001 B004 B001 B002 B003
  exact H_N005

end TopologyCertificate_p0412_almosttrivial_and_almostfinite_of_shortexa

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0414_veronese_affineindependent
-- topology_sha256: f61763d7c3c5fc654d7efba8545fcae2b44416562e2f20714ee9fb6cc89e5284
namespace TopologyCertificate_p0414_veronese_affineindependent

-- N001 = hrp: r ≤ p + 1
-- N002 = hx: Function.Injective x
-- N003 = goal: let I := { ab // (ab.1.sum fun x n => n) ≤ p ∧ (ab.2.sum fun x n => n) ≤ q }; let v := fun z ab => ((↑ab).1.prod fun i n => z i ^ n) * (↑ab).2.prod fun i n => (starRingEnd ℂ) (z i) ^ n; AffineIndependent ℝ fun j => v (x j)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (B001 : N001)
    (B002 : N002)
    (E001 : N001 → N002 → N003)
    : N003 := by
  have H_N003 : N003 := E001 B001 B002
  exact H_N003

end TopologyCertificate_p0414_veronese_affineindependent

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0489_caristi_kirk_bmetric_fixed_point
-- topology_sha256: e3c506562155440bc52f1df77609cd5aa3e4eb91c6122edfd93871c94b5cd418
namespace TopologyCertificate_p0489_caristi_kirk_bmetric_fixed_point

-- N001 = hA: 1 < A
-- N002 = hcaristi: ∀ (x : X), ↑(d (x, f x)) ≤ ↑(Φ x) - A * ↑(Φ (f x))
-- N003 = hcomplete: ∀ (x : ℕ → X), Filter.Tendsto (fun p => d (x p.1, x p.2)) (Filter.atTop ×ˢ Filter.atTop) (nhds 0) → ∃ u, Filter.Tendsto (fun n => d (x n, u)) Filter.atTop (nhds 0)
-- N004 = hd_symm: ∀ (x y : X), d (x, y) = d (y, x)
-- N005 = hd_triangle: ∀ (x y z : X), ↑(d (x, y)) ≤ s * (↑(d (x, z)) + ↑(d (z, y)))
-- N006 = hd_zero: ∀ (x y : X), d (x, y) = 0 ↔ x = y
-- N007 = hf_continuous: ∀ (x : ℕ → X) (u : X), Filter.Tendsto (fun n => d (x n, u)) Filter.atTop (nhds 0) → Filter.Tendsto (fun n => d (f (x n), f u)) Filter.atTop (nhds 0)
-- N008 = hs: 1 ≤ s
-- N009 = hcauchy: Filter.Tendsto (fun p => d (x p.1, x p.2)) (Filter.atTop ×ˢ Filter.atTop) (nhds 0)
-- N010 = goal: ∃ u, f u = u ∧ Filter.Tendsto (fun n => d (f^[n] x₀, u)) Filter.atTop (nhds 0)

-- E001 represents h_001_hcauchy
-- E002 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (B007 : N007)
    (B008 : N008)
    (E001 : N008 → N006 → N004 → N005 → N001 → N002 → N009)
    (E002 : N006 → N004 → N005 → N003 → N007 → N009 → N010)
    : N010 := by
  have H_N009 : N009 := E001 B008 B006 B004 B005 B001 B002
  have H_N010 : N010 := E002 B006 B004 B005 B003 B007 H_N009
  exact H_N010

end TopologyCertificate_p0489_caristi_kirk_bmetric_fixed_point

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0496_normalized_modified_kbessel_nonincreasing_
-- topology_sha256: 76e85da9bebe4ed58125c383835dd52ecbe6599bc93f9169392c1b938160e0ad
namespace TopologyCertificate_p0496_normalized_modified_kbessel_nonincreasing

-- N001 = hk: 0 < k
-- N002 = hx: 0 < x
-- N003 = goal: let Γk := fun z => k ^ (z / k - 1) * Real.Gamma (z / k); let 𝓘 := fun ν => ∑' (r : ℕ), Γk (ν + k) / (Γk (↑r * k + ν + k) * 4 ^ r * ↑r.factorial) * x ^ (2 * r); (∀ ⦃ν μ : ℝ⦄, -k < ν → ν ≤ μ → 𝓘 μ ≤ 𝓘 ν) ∧ ∀ ⦃ν₁ ν₂ α : ℝ⦄, -k < ν₁ → -k < ν₂ → 0 ≤ α → α ≤ 1 → 𝓘 (α * ν₁ + (1 - α) * ν₂) ≤ 𝓘 ν₁ ^ α * 𝓘 ν₂ ^ (1 - α)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (B001 : N001)
    (B002 : N002)
    (E001 : N001 → N002 → N003)
    : N003 := by
  have H_N003 : N003 := E001 B001 B002
  exact H_N003

end TopologyCertificate_p0496_normalized_modified_kbessel_nonincreasing

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0613_chromaticnumber_cartesianpower
-- topology_sha256: ae22701a4b328287dc620e363fc049b384035cf483673f85fda6131a05a68d18
namespace TopologyCertificate_p0613_chromaticnumber_cartesianpower

-- N001 = hk: 1 ≤ k
-- N002 = hn: 0 < n
-- N003 = hcG: G.Colorable q
-- N004 = hq: q ≠ 0
-- N005 = htop: G.chromaticNumber ≠ ⊤
-- N006 = hcolor: (SimpleGraph.fromRel fun x y => ∃ i, G.Adj (x i) (y i) ∧ ∀ (j : Fin k), j ≠ i → x j = y j).Colorable q
-- N007 = upper: (SimpleGraph.fromRel fun x y => ∃ i, G.Adj (x i) (y i) ∧ ∀ (j : Fin k), j ≠ i → x j = y j).chromaticNumber ≤ G.chromaticNumber
-- N008 = goal: (SimpleGraph.fromRel fun x y => ∃ i, G.Adj (x i) (y i) ∧ ∀ (j : Fin k), j ≠ i → x j = y j).chromaticNumber = G.chromaticNumber

-- E001 represents h_001_hcg
-- E002 represents h_002_hq
-- E003 represents h_004_htop
-- E004 represents h_003_hcolor
-- E005 represents h_005_upper
-- E006 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (N008 : Prop)
    (B001 : N001)
    (B002 : N002)
    (E001 : N003)
    (E002 : N002 → N003 → N004)
    (E003 : N003 → N005)
    (E004 : N003 → N004 → N006)
    (E005 : N006 → N005 → N007)
    (E006 : N002 → N001 → N007 → N008)
    : N008 := by
  have H_N003 : N003 := E001
  have H_N004 : N004 := E002 B002 H_N003
  have H_N005 : N005 := E003 H_N003
  have H_N006 : N006 := E004 H_N003 H_N004
  have H_N007 : N007 := E005 H_N006 H_N005
  have H_N008 : N008 := E006 B002 B001 H_N007
  exact H_N008

end TopologyCertificate_p0613_chromaticnumber_cartesianpower

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0617_sqrt_two_weighted_sum_lt
-- topology_sha256: 85963c6ebe640ec9f2bbd8441d5657b918440f84f595b189f386721059f5c9f8
namespace TopologyCertificate_p0617_sqrt_two_weighted_sum_lt

-- N001 = goal: ∑ j ∈ Finset.range (i + 1), ↑(i - j) * √2 ^ j < (4 + 3 * √2) * √2 ^ i

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p0617_sqrt_two_weighted_sum_lt

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0644_collapse_set_partialorder_iff_ordconnected
-- topology_sha256: ffa7fbe65112bd88a8747c3d228b9e112409eaf0464d453ac16f226471a79af6
namespace TopologyCertificate_p0644_collapse_set_partialorder_iff_ordconnected

-- N001 = hB: B.Nonempty
-- N002 = goal: let Q := { x // x ∉ B } ⊕ Unit; let r := fun x y => match x, y with | Sum.inr val, Sum.inr val_1 => True | Sum.inr val, Sum.inl y => ∃ b ∈ B, b ≤ ↑y | Sum.inl x, Sum.inr val => ∃ b ∈ B, ↑x ≤ b | Sum.inl x, Sum.inl y => ↑x ≤ ↑y ∨ ∃ b ∈ B, ∃ b' ∈ B, ↑x ≤ b ∧ b' ≤ ↑y; IsPartialOrder Q r ↔ B.OrdConnected

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    : N002 := by
  have H_N002 : N002 := E001 B001
  exact H_N002

end TopologyCertificate_p0644_collapse_set_partialorder_iff_ordconnected

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0786_projective_iff_projective_in_thick_subcate
-- topology_sha256: 0e507526b3dc3c2fe382547187da09f38ad1d12154a2fa062539f87c58d855eb
namespace TopologyCertificate_p0786_projective_iff_projective_in_thick_subcate

-- N001 = hproj: ∀ (P : C), CategoryTheory.Projective P → S P
-- N002 = hQ: S Q
-- N003 = hS: ∀ (T : CategoryTheory.ShortComplex C), T.ShortExact → (S T.X₁ ∧ S T.X₂ → S T.X₃) ∧ (S T.X₁ ∧ S T.X₃ → S T.X₂) ∧ (S T.X₂ ∧ S T.X₃ → S T.X₁)
-- N004 = inst._@.proofs.968698635._hygCtx._hyg.9: CategoryTheory.EnoughProjectives C
-- N005 = goal: CategoryTheory.Projective Q ↔ ∀ (T : CategoryTheory.ShortComplex C), T.X₃ = Q → S T.X₁ → S T.X₂ → T.ShortExact → CategoryTheory.IsSplitEpi T.g

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N004 → N003 → N001 → N002 → N005)
    : N005 := by
  have H_N005 : N005 := E001 B004 B003 B001 B002
  exact H_N005

end TopologyCertificate_p0786_projective_iff_projective_in_thick_subcate

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0824_finite_category_mobius_zero
-- topology_sha256: fc0062b16cdb74302d0b069d001d3a9330b4878c76acd8c358807a4adc79c636
namespace TopologyCertificate_p0824_finite_category_mobius_zero

-- N001 = hμζ: ∀ (a c : A), ∑ b, μ a b * ↑(Fintype.card (b ⟶ c)) = if a = c then 1 else 0
-- N002 = hζμ: ∀ (a c : A), ∑ b, ↑(Fintype.card (a ⟶ b)) * μ b c = if a = c then 1 else 0
-- N003 = hab: IsEmpty (a ⟶ b)
-- N004 = hMZ: M * ζ = 1
-- N005 = hZM: ζ * M = 1
-- N006 = hζtri: ζ.BlockTriangular label
-- N007 = hbcard: Fintype.card (b ⟶ b) ≠ 0
-- N008 = hμtri: ζ⁻¹.BlockTriangular label
-- N009 = hinv: ζ⁻¹ = M
-- N010 = hlt: label b < label a
-- N011 = hzero: ζ⁻¹ a b = 0
-- N012 = this: M a b = 0
-- N013 = goal: M a b = 0

-- E001 represents h_001_hmz
-- E002 represents h_002_hzm
-- E003 represents h_003_h_tri
-- E004 represents h_006_hbcard
-- E005 represents h_004_h_tri
-- E006 represents h_005_hinv
-- E007 represents h_007_hlt
-- E008 represents h_008_hzero
-- E009 represents h_009_this
-- E010 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N001 → N004)
    (E002 : N002 → N005)
    (E003 : N006)
    (E004 : N007)
    (E005 : N005 → N006 → N008)
    (E006 : N004 → N009)
    (E007 : N003 → N007 → N010)
    (E008 : N008 → N010 → N011)
    (E009 : N009 → N011 → N012)
    (E010 : N012 → N013)
    : N013 := by
  have H_N004 : N004 := E001 B001
  have H_N005 : N005 := E002 B002
  have H_N006 : N006 := E003
  have H_N007 : N007 := E004
  have H_N008 : N008 := E005 H_N005 H_N006
  have H_N009 : N009 := E006 H_N004
  have H_N010 : N010 := E007 B003 H_N007
  have H_N011 : N011 := E008 H_N008 H_N010
  have H_N012 : N012 := E009 H_N009 H_N011
  have H_N013 : N013 := E010 H_N012
  exact H_N013

end TopologyCertificate_p0824_finite_category_mobius_zero

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0912_catlin_vertical_curve_is_geodesic
-- topology_sha256: ff55e243bcb013b3bb1fe2d4b53943a217b77c71844ab85c4d3c84a7f12cdfd5
namespace TopologyCertificate_p0912_catlin_vertical_curve_is_geodesic

-- N001 = ha: 0 < a
-- N002 = hfront: (z₀, w₀) ∈ frontier Ω
-- N003 = hreal: ∀ (z : ℂ), (evalAt z p).im = 0
-- N004 = heval: evalAt = Rollout_p0912_catlin_vertical_curve_is_geodesic.evalDiag
-- N005 = hr: r = Rollout_p0912_catlin_vertical_curve_is_geodesic.catlinR p
-- N006 = hM: M = Rollout_p0912_catlin_vertical_curve_is_geodesic.catlinM m p
-- N007 = hPC: PiecewiseC1 = Rollout_p0912_catlin_vertical_curve_is_geodesic.PiecewiseC1Curve
-- N008 = hrealG: ∀ (z : ℂ), (Rollout_p0912_catlin_vertical_curve_is_geodesic.evalDiag z p).im = 0
-- N009 = hΩdef: Ω = {q | Rollout_p0912_catlin_vertical_curve_is_geodesic.catlinR p q < 0}
-- N010 = hb: Rollout_p0912_catlin_vertical_curve_is_geodesic.catlinR p (z₀, w₀) = 0
-- N011 = goal: (∀ (t : ℝ), σ t ∈ Ω) ∧ ∀ (s t : ℝ), d (σ s) (σ t) = |s - t|

-- E001 represents h_001_heval
-- E002 represents h_006_hr
-- E003 represents h_007_hm
-- E004 represents h_008_hpc
-- E005 represents h_009_hrealg
-- E006 represents h_010_h_def
-- E007 represents h_011_hb
-- E008 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N004)
    (E002 : N005)
    (E003 : N006)
    (E004 : N007)
    (E005 : N003 → N004 → N008)
    (E006 : N005 → N009)
    (E007 : N002 → N009 → N010)
    (E008 : N001 → N006 → N007 → N008 → N009 → N010 → N011)
    : N011 := by
  have H_N004 : N004 := E001
  have H_N005 : N005 := E002
  have H_N006 : N006 := E003
  have H_N007 : N007 := E004
  have H_N008 : N008 := E005 B003 H_N004
  have H_N009 : N009 := E006 H_N005
  have H_N010 : N010 := E007 B002 H_N009
  have H_N011 : N011 := E008 B001 H_N006 H_N007 H_N008 H_N009 H_N010
  exact H_N011

end TopologyCertificate_p0912_catlin_vertical_curve_is_geodesic

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0968_unique_nonzero_zero_of_exponential_factori
-- topology_sha256: d4ca74383152f0bfeefc3bc82eda301a06f7f3b5f660876d151afe5a084e3479
namespace TopologyCertificate_p0968_unique_nonzero_zero_of_exponential_factori

-- N001 = hk₂: k ≤ n - 1
-- N002 = hk₁: 1 ≤ k
-- N003 = hn: 2 ≤ n
-- N004 = goal: let h := fun x => Real.exp (2 * ↑k * x) * ∑ j ∈ Finset.range (n + 1), (-1) ^ (n - j) * (↑n.factorial / ↑j.factorial) * (↑n + ↑k) ^ (↑j - 1) * (↑n + ↑k - ↑j) * x ^ j - ∑ j ∈ Finset.range (n + 1), (-1) ^ (n - j) * (↑n.factorial / ↑j.factorial) * (↑n - ↑k) ^ (↑j - 1) * (↑n - ↑k - ↑j) * x ^ j; ∃ c, -1 < c ∧ c < 0 ∧ h c = 0 ∧ ∀ (x : ℝ), h x = 0 ↔ x = 0 ∨ x = c

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N003 → N002 → N001 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B003 B002 B001
  exact H_N004

end TopologyCertificate_p0968_unique_nonzero_zero_of_exponential_factori

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0971_derivwithin_neg_of_positive_solution
-- topology_sha256: 253a8736d821304a70bd1dc324f603e5e16229c1ee25c0de4161930c7617de03
namespace TopologyCertificate_p0971_derivwithin_neg_of_positive_solution

-- N001 = hΦ: ContDiffOn ℝ 1 Φ (Set.Icc 0 β)
-- N002 = hβ: 0 < β
-- N003 = hf0: f 0 = 0
-- N004 = hfpos: ∀ t ∈ Set.Ioc 0 β, 0 < f t
-- N005 = hlam: 0 < lam
-- N006 = hn: 2 ≤ n
-- N007 = hODE: ∀ t ∈ Set.Ioo 0 β, deriv Φ t + lam * f t ^ (n - 1) * ψ (T t) = 0
-- N008 = ht: t ∈ Set.Ioc 0 β
-- N009 = hTpos: ∀ t ∈ Set.Ioo 0 β, 0 < T t
-- N010 = hψneg_iff: ∀ (s : ℝ), ψ s < 0 ↔ s < 0
-- N011 = hψpos_iff: ∀ (s : ℝ), 0 < ψ s ↔ 0 < s
-- N012 = hn1: n - 1 ≠ 0
-- N013 = htpos: 0 < t
-- N014 = htβ: t ≤ β
-- N015 = hmem0: 0 ∈ Set.Icc 0 β
-- N016 = hderivneg: ∀ t ∈ interior (Set.Icc 0 β), deriv Φ t < 0
-- N017 = hΦ0: Φ 0 = 0
-- N018 = hmemt: t ∈ Set.Icc 0 β
-- N019 = hf_t: 0 < f t
-- N020 = hanti: StrictAntiOn Φ (Set.Icc 0 β)
-- N021 = hpow: 0 < f t ^ (n - 1)
-- N022 = hΦt_neg: Φ t < 0
-- N023 = hprod_neg: f t ^ (n - 1) * ψ (derivWithin T (Set.Icc 0 β) t) < 0
-- N024 = hψderiv_neg: ψ (derivWithin T (Set.Icc 0 β) t) < 0
-- N025 = goal: derivWithin T (Set.Icc 0 β) t < 0

-- E001 represents h_001_h_neg_iff
-- E002 represents h_002_h_pos_iff
-- E003 represents h_005_hn1
-- E004 represents h_007_htpos
-- E005 represents h_008_ht
-- E006 represents h_009_hmem0
-- E007 represents h_003_hderivneg
-- E008 represents h_006_h_0
-- E009 represents h_010_hmemt
-- E010 represents h_013_hf_t
-- E011 represents h_004_hanti
-- E012 represents h_014_hpow
-- E013 represents h_011_h_t_neg
-- E014 represents h_012_hprod_neg
-- E015 represents h_015_h_deriv_neg
-- E016 represents h_goal

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
    (N025 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (B007 : N007)
    (B008 : N008)
    (B009 : N009)
    (E001 : N010)
    (E002 : N011)
    (E003 : N006 → N012)
    (E004 : N008 → N013)
    (E005 : N008 → N014)
    (E006 : N002 → N015)
    (E007 : N005 → N004 → N007 → N009 → N011 → N016)
    (E008 : N003 → N012 → N017)
    (E009 : N013 → N014 → N018)
    (E010 : N004 → N013 → N014 → N019)
    (E011 : N001 → N016 → N020)
    (E012 : N019 → N021)
    (E013 : N020 → N017 → N013 → N015 → N018 → N022)
    (E014 : N022 → N023)
    (E015 : N023 → N021 → N024)
    (E016 : N010 → N024 → N025)
    : N025 := by
  have H_N010 : N010 := E001
  have H_N011 : N011 := E002
  have H_N012 : N012 := E003 B006
  have H_N013 : N013 := E004 B008
  have H_N014 : N014 := E005 B008
  have H_N015 : N015 := E006 B002
  have H_N016 : N016 := E007 B005 B004 B007 B009 H_N011
  have H_N017 : N017 := E008 B003 H_N012
  have H_N018 : N018 := E009 H_N013 H_N014
  have H_N019 : N019 := E010 B004 H_N013 H_N014
  have H_N020 : N020 := E011 B001 H_N016
  have H_N021 : N021 := E012 H_N019
  have H_N022 : N022 := E013 H_N020 H_N017 H_N013 H_N015 H_N018
  have H_N023 : N023 := E014 H_N022
  have H_N024 : N024 := E015 H_N023 H_N021
  have H_N025 : N025 := E016 H_N010 H_N024
  exact H_N025

end TopologyCertificate_p0971_derivwithin_neg_of_positive_solution

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1067_complex_exp_modulus_bounds
-- topology_sha256: ae0775c9de803f41c6b91d674b58b5dd7eeb7343638294ca094a3b916b2a3aff
namespace TopologyCertificate_p1067_complex_exp_modulus_bounds

-- N001 = hz: -z.re ≥ ‖z‖ / 2 ∧ -z.re ≥ 3
-- N002 = hexp: 4 * -z.re + 2 ≤ Real.exp (-z.re)
-- N003 = hnormexp: ‖Complex.exp (-z)‖ = Real.exp (-z.re)
-- N004 = hz1: ‖z + 1‖ ≤ 1 / 2 * Real.exp (-z.re)
-- N005 = hlower_core: 1 / 2 * Real.exp (-z.re) ≤ ‖z + 1 + Complex.exp (-z)‖
-- N006 = hupper_core: ‖z + 1 + Complex.exp (-z)‖ ≤ 2 * Real.exp (-z.re)
-- N007 = goal: 1 / 2 * Real.exp (-z.re) ≤ ‖f z‖ ∧ ‖f z‖ ≤ 2 * Real.exp (-z.re)

-- E001 represents h_003_hexp
-- E002 represents h_005_hnormexp
-- E003 represents h_004_hz1
-- E004 represents h_006_hlower_core
-- E005 represents h_007_hupper_core
-- E006 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    (E002 : N003)
    (E003 : N001 → N002 → N004)
    (E004 : N004 → N003 → N005)
    (E005 : N001 → N002 → N004 → N003 → N006)
    (E006 : N005 → N006 → N007)
    : N007 := by
  have H_N002 : N002 := E001 B001
  have H_N003 : N003 := E002
  have H_N004 : N004 := E003 B001 H_N002
  have H_N005 : N005 := E004 H_N004 H_N003
  have H_N006 : N006 := E005 B001 H_N002 H_N004 H_N003
  have H_N007 : N007 := E006 H_N005 H_N006
  exact H_N007

end TopologyCertificate_p1067_complex_exp_modulus_bounds

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1078_khexpansive_iff_separating_and_isopen_fixe
-- topology_sha256: 1d21a2c271cc6d89ca8dd8b3bb2cfd8d6957cb59c12c94472e01d3e82f68c8b9
namespace TopologyCertificate_p1078_khexpansive_iff_separating_and_isopen_fixe

-- N001 = hadd: ∀ (t u : ℝ) (x : Λ), φ (t + u, x) = φ (t, φ (u, x))
-- N002 = hcont: Continuous φ
-- N003 = hzero: ∀ (x : Λ), φ (0, x) = x
-- N004 = inst._@.proofs.3640889310._hygCtx._hyg.6: CompactSpace Λ
-- N005 = goal: (∃ δ, 0 < δ ∧ ∀ (x y : Λ) (s : ℝ → ℝ), Continuous s → s 0 = 0 → ((∀ (t : ℝ), dist (φ (t, x)) (φ (s t, x)) < δ) ∧ ∀ (t : ℝ), dist (φ (t, x)) (φ (s t, y)) < δ) → y ∈ Set.range fun t => φ (t, x)) ↔ (∃ α, 0 < α ∧ ∀ (x y : Λ), (∀ (t : ℝ), dist (φ (t, x)) (φ (t, y)) < α) → y ∈ Set.range fun t => φ (t, x)) ∧ IsOpen {x | ∀ (t : ℝ), φ (t, x) = x}

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N004 → N002 → N003 → N001 → N005)
    : N005 := by
  have H_N005 : N005 := E001 B004 B002 B003 B001
  exact H_N005

end TopologyCertificate_p1078_khexpansive_iff_separating_and_isopen_fixe

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

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1136_entropy_number_approximation
-- topology_sha256: 35962ed6d9b2ce9c224f8534f09d23127dfd835d3adaae568e40c6c6429a2704
namespace TopologyCertificate_p1136_entropy_number_approximation

-- N001 = hn: 0 < n
-- N002 = goal: let e := fun k T => ⨅ ε, ⨅ (_ : 0 < ε), ⨅ (_ : Metric.externalCoveringNumber ε (⇑T '' Metric.closedBall 0 1) ≤ 2 ^ (k - 1)), ↑ε; e (n + Nat.log 2 (Fintype.card Γ) + 1) V ≤ (⨆ γ, e n (Vγ γ)) + ⨆ x, ⨆ (_ : ‖x‖ ≤ 1), ⨅ γ, ENNReal.ofReal ‖V x - (Vγ γ) x‖

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    : N002 := by
  have H_N002 : N002 := E001 B001
  exact H_N002

end TopologyCertificate_p1136_entropy_number_approximation

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1151_strict_convex_modular_fixed_point
-- topology_sha256: d75903c07f3cb6dafb1d31aa074ca2f36785d75d8e5ad8a06a5b6745d6002ea8
namespace TopologyCertificate_p1151_strict_convex_modular_fixed_point

-- N001 = hcomplete: ∀ (x : ℕ → { x // ∃ l, 0 < l ∧ w l x b < ⊤ }) (l : NNReal), 0 < l → Filter.Tendsto (fun p => w l ↑(x p.1) ↑(x p.2)) (Filter.atTop ×ˢ Filter.atTop) (nhds 0) → ∃ y, Filter.Tendsto (fun n => w l ↑(x n) ↑y) Filter.atTop (nhds 0)
-- N002 = hcontractive: ∃ k L, 0 < k ∧ k < 1 ∧ 0 < L ∧ ∀ (x y : { x // ∃ l, 0 < l ∧ w l x b < ⊤ }) (l : NNReal), 0 < l → l ≤ L → w (k * l) ↑(T x) ↑(T y) ≤ w l ↑x ↑y
-- N003 = hconv: ∀ (l m : NNReal), 0 < l → 0 < m → ∀ (x y z : X), w (l + m) x y ≤ ↑l / (↑l + ↑m) * w l x z + ↑m / (↑l + ↑m) * w m y z
-- N004 = hself: ∀ (l : NNReal), 0 < l → ∀ (x : X), w l x x = 0
-- N005 = hstrict: ∀ (x y : X), (∃ l, 0 < l ∧ w l x y = 0) → x = y
-- N006 = hsymm: ∀ (l : NNReal), 0 < l → ∀ (x y : X), w l x y = w l y x
-- N007 = goal: ((∀ (l : NNReal), 0 < l → ∃ x, w l ↑x ↑(T x) < ⊤) → ∃ x, T x = x) ∧ ((∀ (l : NNReal), 0 < l → ∀ (x y : { x // ∃ m, 0 < m ∧ w m x b < ⊤ }), w l ↑x ↑y < ⊤) → ∃ xstar, T xstar = xstar ∧ (∀ (y : { x // ∃ l, 0 < l ∧ w l x b < ⊤ }), T y = y → y = xstar) ∧ ∀ (x : { x // ∃ l, 0 < l ∧ w l x b < ⊤ }), ∃ l, 0 < l ∧ Filter.Tendsto (fun n => w l ↑(T^[n] x) ↑xstar) Filter.atTop (nhds 0))

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (E001 : N004 → N006 → N005 → N003 → N001 → N002 → N007)
    : N007 := by
  have H_N007 : N007 := E001 B004 B006 B005 B003 B001 B002
  exact H_N007

end TopologyCertificate_p1151_strict_convex_modular_fixed_point

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1180_inversealong_units
-- topology_sha256: 14da5c37624322edd95e16aea21e85ecc3ac5185160255fc6420240c3d494907
namespace TopologyCertificate_p1180_inversealong_units

-- N001 = h_inner: b * a * b = b
-- N002 = h_left: (Set.range fun y => y * b) = Set.range fun y => y * d
-- N003 = h_right: (Set.range fun y => b * y) = Set.range fun y => d * y
-- N004 = goal: ↑r * b * ↑s⁻¹ * (↑s * a * ↑r⁻¹) * (↑r * b * ↑s⁻¹) = ↑r * b * ↑s⁻¹ ∧ ((Set.range fun y => ↑r * b * ↑s⁻¹ * y) = Set.range fun y => ↑r * d * ↑s⁻¹ * y) ∧ (Set.range fun y => y * (↑r * b * ↑s⁻¹)) = Set.range fun y => y * (↑r * d * ↑s⁻¹)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N001 → N003 → N002 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B001 B003 B002
  exact H_N004

end TopologyCertificate_p1180_inversealong_units

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1193_parseval_frame_spans_orthogonal
-- topology_sha256: 186c22b947cae8b637db1e4cb4152e1e644df8cfea430cf772137e20a4e64fdf
namespace TopologyCertificate_p1193_parseval_frame_spans_orthogonal

-- N001 = hdisjoint: Submodule.span ℝ (φ '' I) ⊓ Submodule.span ℝ (φ '' Iᶜ) = ⊥
-- N002 = hParseval: ∀ (x : EuclideanSpace ℝ (Fin M)), ∑ i, inner ℝ x (φ i) ^ 2 = ‖x‖ ^ 2
-- N003 = hu: u ∈ Submodule.span ℝ (φ '' I)
-- N004 = hv: v ∈ Submodule.span ℝ (φ '' Iᶜ)
-- N005 = hframe: Rollout_p1193_parseval_frame_spans_orthogonal.partialFrame φ Set.univ = LinearMap.id
-- N006 = hSIu_A: SI u ∈ A
-- N007 = hSCu_B: SC u ∈ B
-- N008 = hdecomp: ∀ (x : E), SI x + SC x = x
-- N009 = hSI_zero_on_B: ∀ v ∈ B, SI v = 0
-- N010 = hSCu_A: SC u ∈ A
-- N011 = hSCu_zero: SC u = 0
-- N012 = hSIv: SI v = 0
-- N013 = hSIu: SI u = u
-- N014 = goal: inner ℝ u v = 0

-- E001 represents h_001_hframe
-- E002 represents h_004_hsiu_a
-- E003 represents h_005_hscu_b
-- E004 represents h_002_hdecomp
-- E005 represents h_003_hsi_zero_on_b
-- E006 represents h_006_hscu_a
-- E007 represents h_007_hscu_zero
-- E008 represents h_009_hsiv
-- E009 represents h_008_hsiu
-- E010 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N002 → N005)
    (E002 : N006)
    (E003 : N007)
    (E004 : N005 → N008)
    (E005 : N001 → N008 → N009)
    (E006 : N008 → N003 → N006 → N010)
    (E007 : N001 → N007 → N010 → N011)
    (E008 : N009 → N004 → N012)
    (E009 : N008 → N011 → N013)
    (E010 : N013 → N012 → N014)
    : N014 := by
  have H_N005 : N005 := E001 B002
  have H_N006 : N006 := E002
  have H_N007 : N007 := E003
  have H_N008 : N008 := E004 H_N005
  have H_N009 : N009 := E005 B001 H_N008
  have H_N010 : N010 := E006 H_N008 B003 H_N006
  have H_N011 : N011 := E007 B001 H_N007 H_N010
  have H_N012 : N012 := E008 H_N009 B004
  have H_N013 : N013 := E009 H_N008 H_N011
  have H_N014 : N014 := E010 H_N013 H_N012
  exact H_N014

end TopologyCertificate_p1193_parseval_frame_spans_orthogonal

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1226_continuous_quadratic_form_delta_semidefini
-- topology_sha256: fcee227336671d974a9daef65058f17ab415ea536aaf240335313305cad50f04
namespace TopologyCertificate_p1226_continuous_quadratic_form_delta_semidefini

-- N001 = hTq: ∀ (x : X), q x = (T x) x
-- N002 = hTsymm: ∀ (x y : X), (T x) y = (T y) x
-- N003 = inst._@.proofs.3283946215._hygCtx._hyg.12: CompleteSpace X
-- N004 = goal: ((∃ q₁ q₂, (∃ b₁, ∀ (x : X), q₁ x = (b₁ x) x) ∧ (∃ b₂, ∀ (x : X), q₂ x = (b₂ x) x) ∧ (∀ (x : X), 0 ≤ q₁ x) ∧ (∀ (x : X), 0 ≤ q₂ x) ∧ ∀ (x : X), q x = q₁ x - q₂ x) ↔ ∃ p, (∃ bp, ∀ (x : X), p x = (bp x) x) ∧ ∀ (x : X), |q x| ≤ p x) ∧ ((∃ p, (∃ bp, ∀ (x : X), p x = (bp x) x) ∧ ∀ (x : X), |q x| ≤ p x) ↔ ∃ H x x_1, ∃ (_ : CompleteSpace H), ∃ A B, T = B.comp A)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N003 → N001 → N002 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B003 B001 B002
  exact H_N004

end TopologyCertificate_p1226_continuous_quadratic_form_delta_semidefini

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1227_discrete_add_subgroup_covering
-- topology_sha256: 37dc515db3c9a5abba24bc857578d4649ea4d16bcd42ddc2a2cc4e5fe39fc62d
namespace TopologyCertificate_p1227_discrete_add_subgroup_covering

-- N001 = hε₀_lt_one: ε₀ < 1
-- N002 = hε₀_pos: 0 < ε₀
-- N003 = hcover: K ⊆ Set.image2 (fun x1 x2 => x1 + x2) (↑L) ((fun x => ε₀ • x) '' K)
-- N004 = hK_nhds: 0 ∈ interior K
-- N005 = hK_star: StarConvex ℝ 0 K
-- N006 = goal: let ε₁ := ↑(⌊ε₀ / (1 - ε₀)⌋ + 1) * ε₀; Set.univ = Set.image2 (fun x1 x2 => x1 + x2) (↑L) ((fun x => ε₁ • x) '' K)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (E001 : N004 → N005 → N002 → N001 → N003 → N006)
    : N006 := by
  have H_N006 : N006 := E001 B004 B005 B002 B001 B003
  exact H_N006

end TopologyCertificate_p1227_discrete_add_subgroup_covering

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1232_diagonal_homogeneous_polynomial_norm_bound
-- topology_sha256: 910854e5c1c89e9dea383bc8c54c2f4098dc9bdd1ead6751c521e969dbe06da9
namespace TopologyCertificate_p1232_diagonal_homogeneous_polynomial_norm_bound

-- N001 = hφ: ∀ (α : Fin k → 𝕂), (A * if p = ⊤ then ‖α‖ else (∑ j, ‖α j‖.rpow p.toReal).rpow (1 / p.toReal)) ≤ ‖∑ j, α j • φ j‖ ∧ ‖∑ j, α j • φ j‖ ≤ B * if p = ⊤ then ‖α‖ else (∑ j, ‖α j‖.rpow p.toReal).rpow (1 / p.toReal)
-- N002 = hA: 0 < A
-- N003 = hB: 0 < B
-- N004 = hk: 1 ≤ k
-- N005 = hn: 1 ≤ n
-- N006 = hnq: p.conjExponent ≤ ↑n
-- N007 = hp: 1 < p
-- N008 = hpoint: ∀ y ∈ S, y ≤ B ^ n * ‖α‖
-- N009 = hnonempty: S.Nonempty
-- N010 = hBdd: BddAbove S
-- N011 = hupper: sSup S ≤ B ^ n * ‖α‖
-- N012 = goal: A ^ n * ‖α‖ ≤ sSup (Set.range fun x => ‖∑ j, α j * (φ j) ↑x ^ n‖) ∧ sSup (Set.range fun x => ‖∑ j, α j * (φ j) ↑x ^ n‖) ≤ B ^ n * ‖α‖

-- E001 represents h_001_hpoint
-- E002 represents h_003_hnonempty
-- E003 represents h_002_hbdd
-- E004 represents h_004_hupper
-- E005 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (B007 : N007)
    (E001 : N004 → N003 → N007 → N001 → N005 → N006 → N008)
    (E002 : N005 → N009)
    (E003 : N008 → N010)
    (E004 : N008 → N010 → N009 → N011)
    (E005 : N004 → N002 → N007 → N001 → N005 → N010 → N011 → N012)
    : N012 := by
  have H_N008 : N008 := E001 B004 B003 B007 B001 B005 B006
  have H_N009 : N009 := E002 B005
  have H_N010 : N010 := E003 H_N008
  have H_N011 : N011 := E004 H_N008 H_N010 H_N009
  have H_N012 : N012 := E005 B004 B002 B007 B001 B005 H_N010 H_N011
  exact H_N012

end TopologyCertificate_p1232_diagonal_homogeneous_polynomial_norm_bound

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1268_flower_graph_equitable_coloring_moments
-- topology_sha256: 62fc5d51e2f8984904db07fbb0ba470440156ede0fd07187201aad0c3ef5f3f5
namespace TopologyCertificate_p1268_flower_graph_equitable_coloring_moments

-- N001 = heq: ∀ (i j : Fin k), (f.colorClass i).ncard.dist (f.colorClass j).ncard ≤ 1
-- N002 = hmin: ∀ ℓ < k, ¬∃ g, Function.Surjective ⇑g ∧ ∀ (i j : Fin ℓ), (g.colorClass i).ncard.dist (g.colorClass j).ncard ≤ 1
-- N003 = hn: 3 ≤ n
-- N004 = hsort: ∀ (i j : Fin k), i ≤ j → (f.colorClass j).ncard ≤ (f.colorClass i).ncard
-- N005 = hsurj: Function.Surjective ⇑f
-- N006 = h2n: 2 ≤ n
-- N007 = hk_lower: n + 1 ≤ k
-- N008 = hk_upper: k ≤ n + 1
-- N009 = hk: k = n + 1
-- N010 = goal: let X := fun x => ↑(↑(f x) + 1); let μ := (PMF.uniformOfFintype V).toMeasure; MeasureTheory.integral μ X = (↑n + 1) ^ 2 / (2 * ↑n + 1) ∧ ProbabilityTheory.variance X μ = (↑n ^ 4 + 2 * ↑n ^ 3 + 2 * ↑n ^ 2 + ↑n) / (3 * (2 * ↑n + 1) ^ 2)

-- E001 represents h_001_h2n
-- E002 represents h_002_hk_lower
-- E003 represents h_003_hk_upper
-- E004 represents h_004_hk
-- E005 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (E001 : N003 → N006)
    (E002 : N005 → N001 → N007)
    (E003 : N002 → N006 → N008)
    (E004 : N007 → N008 → N009)
    (E005 : N005 → N001 → N002 → N004 → N007 → N008 → N009 → N010)
    : N010 := by
  have H_N006 : N006 := E001 B003
  have H_N007 : N007 := E002 B005 B001
  have H_N008 : N008 := E003 B002 H_N006
  have H_N009 : N009 := E004 H_N007 H_N008
  have H_N010 : N010 := E005 B005 B001 B002 B004 H_N007 H_N008 H_N009
  exact H_N010

end TopologyCertificate_p1268_flower_graph_equitable_coloring_moments

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1286_lebesgue_integral_modified_salem
-- topology_sha256: c173f2fd3f41805f05c416c106daa252296564e158ccbe52222c879356552a75
namespace TopologyCertificate_p1286_lebesgue_integral_modified_salem

-- N001 = hp₀: p₀ ∈ Set.Ioo 0 1
-- N002 = hp₁: p₁ ∈ Set.Ioo 0 1
-- N003 = hp₂: p₂ ∈ Set.Ioo 0 1
-- N004 = hsum: p₀ + p₁ + p₂ = 1
-- N005 = goal: let p := ![p₀, p₁, p₂]; let β := ![0, p₀, p₀ + p₁]; let E := fun i => ∑' (k : ℕ), β (i k) * ∏ r ∈ Finset.range k, p (i r); let canonical := fun x => Classical.epsilon fun i => E i = x ∧ ((∃ j, E j = x ∧ j ≠ i) → ∃ N, ∀ (k : ℕ), N ≤ k → i k = 0); let θ := ![0, 2, 1]; let f := fun x => E fun k => θ (canonical x k); MeasureTheory.IntegrableOn f (Set.Icc 0 1) MeasureTheory.volume ∧ ∫ (x : ℝ) in 0..1, f x = (p₁ ^ 2 + p₀ * p₁ + p₀ * p₂) / (1 - p₀ ^ 2 - 2 * p₁ * p₂)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N001 → N002 → N003 → N004 → N005)
    : N005 := by
  have H_N005 : N005 := E001 B001 B002 B003 B004
  exact H_N005

end TopologyCertificate_p1286_lebesgue_integral_modified_salem

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1299_convexpolytope_trace_latticeembedding
-- topology_sha256: 05c80beeafdb73c7eb8a5d1fdb49b2806e9f9882af8cd90b50f37d0303868e47
namespace TopologyCertificate_p1299_convexpolytope_trace_latticeembedding

-- N001 = hextreme: ∀ (x : L), Set.extremePoints F (φ x) ⊆ Ω
-- N002 = hinj: Function.Injective φ
-- N003 = hjoin: ∀ (x y : L), φ (x ⊔ y) = (convexHull F) (φ x ∪ φ y)
-- N004 = hmeet: ∀ (x y : L), φ (x ⊓ y) = φ x ∩ φ y
-- N005 = hpoly: ∀ (x : L), ∃ A, A.Finite ∧ (convexHull F) A = φ x
-- N006 = inst._@.proofs.3608069470._hygCtx._hyg.11: IsStrictOrderedRing F
-- N007 = hconv: ∀ (x : L), (convexHull F) (ψ x) = φ x
-- N008 = hψinj: Function.Injective ψ
-- N009 = goal: (Function.Injective fun x => φ x ∩ Ω) ∧ (∀ (x : L), Ω ∩ (convexHull F) ((fun x => φ x ∩ Ω) x) = (fun x => φ x ∩ Ω) x) ∧ (∀ (x y : L), (fun x => φ x ∩ Ω) (x ⊓ y) = (fun x => φ x ∩ Ω) x ∩ (fun x => φ x ∩ Ω) y) ∧ (∀ (x y : L), (fun x => φ x ∩ Ω) (x ⊔ y) = Ω ∩ (convexHull F) ((fun x => φ x ∩ Ω) x ∪ (fun x => φ x ∩ Ω) y)) ∧ ∀ (x : L), (convexHull F) ((fun x => φ x ∩ Ω) x) = φ x

-- E001 represents h_001_hconv
-- E002 represents h_002_h_inj
-- E003 represents h_goal

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
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (E001 : N006 → N005 → N001 → N007)
    (E002 : N002 → N007 → N008)
    (E003 : N004 → N003 → N007 → N008 → N009)
    : N009 := by
  have H_N007 : N007 := E001 B006 B005 B001
  have H_N008 : N008 := E002 B002 H_N007
  have H_N009 : N009 := E003 B004 B003 H_N007 H_N008
  exact H_N009

end TopologyCertificate_p1299_convexpolytope_trace_latticeembedding

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1335_quarter_stratifiable_diagonal_isgdelta_and
-- topology_sha256: f6d5f2b5cdd3ab71e8e47d685829467cee1447f2787f921b97cf0a3b7dda70a0
namespace TopologyCertificate_p1335_quarter_stratifiable_diagonal_isgdelta_and

-- N001 = hg_converges: ∀ (x : X) (a : ℕ → X), (∀ (n : ℕ), x ∈ g n (a n)) → Filter.Tendsto a Filter.atTop (nhds x)
-- N002 = hg_cover: ∀ (n : ℕ), ⋃ a, g n a = Set.univ
-- N003 = hg_open: ∀ (n : ℕ) (a : X), IsOpen (g n a)
-- N004 = inst._@.proofs.1599378177._hygCtx._hyg.6: T2Space X
-- N005 = goal: (∃ G, (∀ (n : ℕ), IsOpen (G n)) ∧ Set.diagonal X = ⋂ n, G n) ∧ ∀ (x : X), ∃ V, (∀ (n : ℕ), IsOpen (V n) ∧ x ∈ V n) ∧ ⋂ n, V n = {x}

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N004 → N003 → N002 → N001 → N005)
    : N005 := by
  have H_N005 : N005 := E001 B004 B003 B002 B001
  exact H_N005

end TopologyCertificate_p1335_quarter_stratifiable_diagonal_isgdelta_and

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1355_locallycontinuousmeasurableonecocycle_iff_
-- topology_sha256: eab7bd635f5869034ed81523c6751d4339c777d86cff6e90df03171b19b7338b
namespace TopologyCertificate_p1355_locallycontinuousmeasurableonecocycle_iff

-- N001 = inst._@.proofs.1843747912._hygCtx._hyg.10: IsTopologicalGroup G
-- N002 = inst._@.proofs.1843747912._hygCtx._hyg.26: ContinuousSMul G A
-- N003 = inst._@.proofs.1843747912._hygCtx._hyg.39: BorelSpace A
-- N004 = inst._@.proofs.1843747912._hygCtx._hyg.19: IsTopologicalAddGroup A
-- N005 = inst._@.proofs.1843747912._hygCtx._hyg.33: BorelSpace G
-- N006 = goal: (Measurable c ∧ (∀ (s t : G), c (s * t) = c s + s • c t) ∧ ∃ U, IsOpen U ∧ 1 ∈ U ∧ ContinuousOn c U) ↔ Continuous c ∧ ∀ (s t : G), c (s * t) = c s + s • c t

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (E001 : N001 → N004 → N002 → N005 → N003 → N006)
    : N006 := by
  have H_N006 : N006 := E001 B001 B004 B002 B005 B003
  exact H_N006

end TopologyCertificate_p1355_locallycontinuousmeasurableonecocycle_iff

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1362_common_coincidence_point_of_ordered_metric
-- topology_sha256: 78e4ae4bf05249dce38e5d4dbc12c701bc55911baceeacadef29b6de62e91336
namespace TopologyCertificate_p1362_common_coincidence_point_of_ordered_metric

-- N001 = hβ_lt_one: ∀ (t : NNReal), β t < 1
-- N002 = hβ_zero: ∀ (t : ℕ → NNReal), Filter.Tendsto (fun n => β (t n)) Filter.atTop (nhds 1) → Filter.Tendsto t Filter.atTop (nhds 0)
-- N003 = hcontract: ∀ (x y : X), H x ≤ H y ∨ H y ≤ H x → nndist (f x) (g y) ≤ β (nndist (H x) (H y)) * nndist (H x) (H y)
-- N004 = hf_range: Set.range f ⊆ Set.range H
-- N005 = hfg_inc: ∀ (x y : X), H y = f x → f x ≤ g y
-- N006 = hH_closed: IsClosed (Set.range H)
-- N007 = hregular: ∀ (z : ℕ → X) (a : X), Monotone z → Filter.Tendsto z Filter.atTop (nhds a) → ∀ (n : ℕ), z n ≤ a
-- N008 = inst._@.proofs.697528154._hygCtx._hyg.12: CompleteSpace X
-- N009 = inst._@.proofs.697528154._hygCtx._hyg.3: Nonempty X
-- N010 = hf_eq_g: ∀ (x : X), f x = g x
-- N011 = goal: ∃ u, f u = g u ∧ g u = H u

-- E001 represents h_001_hf_eq_g
-- E002 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (B007 : N007)
    (B008 : N008)
    (B009 : N009)
    (E001 : N003 → N010)
    (E002 : N009 → N008 → N007 → N004 → N006 → N005 → N001 → N002 → N003 → N010 → N011)
    : N011 := by
  have H_N010 : N010 := E001 B003
  have H_N011 : N011 := E002 B009 B008 B007 B004 B006 B005 B001 B002 B003 H_N010
  exact H_N011

end TopologyCertificate_p1362_common_coincidence_point_of_ordered_metric

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1371_decktransformation_eq_id_of_fixed_point
-- topology_sha256: 49b9b585e041fe141c9e7bf83d6fcded9c12a63a2cdd4f73c72e7081daaf95bf
namespace TopologyCertificate_p1371_decktransformation_eq_id_of_fixed_point

-- N001 = arc_lifting: ∀ (f : C(↑(Set.Icc 0 1), B)) (t₀ : ↑(Set.Icc 0 1)) (e₀ : E), p e₀ = f t₀ → ∃! g, (∀ (t : ↑(Set.Icc 0 1)), p (g t) = f t) ∧ g t₀ = e₀
-- N002 = hdeck: p ∘ ⇑h = p
-- N003 = he: h e = e
-- N004 = hp: Continuous p
-- N005 = inst._@.proofs.4209456836._hygCtx._hyg.10: PathConnectedSpace E
-- N006 = goal: h = Homeomorph.refl E

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (E001 : N005 → N004 → N001 → N002 → N003 → N006)
    : N006 := by
  have H_N006 : N006 := E001 B005 B004 B001 B002 B003
  exact H_N006

end TopologyCertificate_p1371_decktransformation_eq_id_of_fixed_point

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1384_scale_prod
-- topology_sha256: 1da667801e740c52d6105a512b20eae005a2c477a38b9219361ad9b071c19e8b
namespace TopologyCertificate_p1384_scale_prod

-- N001 = inst._@.proofs.3934748685._hygCtx._hyg.10: IsTopologicalGroup G
-- N002 = inst._@.proofs.3934748685._hygCtx._hyg.28: LocallyCompactSpace H
-- N003 = inst._@.proofs.3934748685._hygCtx._hyg.31: TotallyDisconnectedSpace H
-- N004 = inst._@.proofs.3934748685._hygCtx._hyg.25: IsTopologicalGroup H
-- N005 = inst._@.proofs.3934748685._hygCtx._hyg.16: TotallyDisconnectedSpace G
-- N006 = inst._@.proofs.3934748685._hygCtx._hyg.13: LocallyCompactSpace G
-- N007 = hPne: SP.Nonempty
-- N008 = hGne: SG.Nonempty
-- N009 = hHne: SH.Nonempty
-- N010 = goal: sInf {n | ∃ U, IsCompact ↑U ∧ IsOpen ↑U ∧ n = U.relIndex (Subgroup.map (φ.toMonoidHom.prodMap ψ.toMonoidHom) U)} = sInf {n | ∃ V, IsCompact ↑V ∧ IsOpen ↑V ∧ n = V.relIndex (Subgroup.map φ.toMonoidHom V)} * sInf {n | ∃ W, IsCompact ↑W ∧ IsOpen ↑W ∧ n = W.relIndex (Subgroup.map ψ.toMonoidHom W)}

-- E001 represents h_001_hpne
-- E002 represents h_002_hgne
-- E003 represents h_003_hhne
-- E004 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (E001 : N001 → N006 → N005 → N004 → N002 → N003 → N007)
    (E002 : N001 → N006 → N005 → N008)
    (E003 : N004 → N002 → N003 → N009)
    (E004 : N001 → N006 → N005 → N004 → N002 → N003 → N007 → N008 → N009 → N010)
    : N010 := by
  have H_N007 : N007 := E001 B001 B006 B005 B004 B002 B003
  have H_N008 : N008 := E002 B001 B006 B005
  have H_N009 : N009 := E003 B004 B002 B003
  have H_N010 : N010 := E004 B001 B006 B005 B004 B002 B003 H_N007 H_N008 H_N009
  exact H_N010

end TopologyCertificate_p1384_scale_prod

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1461_directed_closure_singleton_iff_chain_closu
-- topology_sha256: 802c35783f6009a5c5c37cffb5c7f6daf1d69d7d6c18bf81c1aa855e0a067907
namespace TopologyCertificate_p1461_directed_closure_singleton_iff_chain_closu

-- N001 = inst._@.proof.2120908755._hygCtx._hyg.6: T0Space X
-- N002 = goal: (∀ (D : Set X), D.Nonempty → DirectedOn LE.le D → ∃! x, closure D = closure {x}) ↔ ∀ (C : Set X), C.Nonempty → IsChain LE.le C → ∃! x, closure C = closure {x}

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    : N002 := by
  have H_N002 : N002 := E001 B001
  exact H_N002

end TopologyCertificate_p1461_directed_closure_singleton_iff_chain_closu

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1462_locallycompact_prod_ascoli
-- topology_sha256: 2ae746cbc6be46666faafa2b65013d41608ef6d88274e4b722e55de0f80ebd1f
namespace TopologyCertificate_p1462_locallycompact_prod_ascoli

-- N001 = hK: IsCompact K
-- N002 = hX: ∀ (K : Set C(X, ℝ)), IsCompact K → Continuous fun p => ↑p.1 p.2
-- N003 = inst._@.proofs.2729584061._hygCtx._hyg.10: LocallyCompactSpace Z
-- N004 = hΦ: Continuous Φ
-- N005 = goal: Continuous fun p => ↑p.1 p.2

-- E001 represents h_001_h
-- E002 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N003 → N004)
    (E002 : N003 → N002 → N001 → N004 → N005)
    : N005 := by
  have H_N004 : N004 := E001 B003
  have H_N005 : N005 := E002 B003 B002 B001 H_N004
  exact H_N005

end TopologyCertificate_p1462_locallycompact_prod_ascoli

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1479_completion_preserves_finite_one_point_exte
-- topology_sha256: 39b1009545f4bff0a670c51396fb742561c861c05ae85f94cd168a4c403d40dc
namespace TopologyCertificate_p1479_completion_preserves_finite_one_point_exte

-- N001 = hdiam: Metric.diam Set.univ = 1
-- N002 = hext: ∀ (F : Set A), F.Finite → ∀ (f : ↑F → ↑(Set.Icc 0 1)), (∀ (x y : ↑F), |↑(f x) - ↑(f y)| ≤ dist ↑x ↑y ∧ dist ↑x ↑y ≤ ↑(f x) + ↑(f y)) → ∃ z, ∀ (x : ↑F), dist z ↑x = ↑(f x)
-- N003 = hdiamX: Metric.diam Set.univ = 1
-- N004 = goal: Metric.diam Set.univ = 1 ∧ ∀ (F : Set (UniformSpace.Completion A)), F.Finite → ∀ (f : ↑F → ↑(Set.Icc 0 1)), (∀ (x y : ↑F), |↑(f x) - ↑(f y)| ≤ dist ↑x ↑y ∧ dist ↑x ↑y ≤ ↑(f x) + ↑(f y)) → ∃ z, ∀ (x : ↑F), dist z ↑x = ↑(f x)

-- E001 represents h_001_hdiamx
-- E002 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (E001 : N001 → N003)
    (E002 : N002 → N003 → N004)
    : N004 := by
  have H_N003 : N003 := E001 B001
  have H_N004 : N004 := E002 B002 H_N003
  exact H_N004

end TopologyCertificate_p1479_completion_preserves_finite_one_point_exte

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1494_p_adic_solenoid_only_periodic_point
-- topology_sha256: 3f89eab81a87f5fb87faadc8e5b9321d877ac94dd5afae1efdb5824852a46a7d
namespace TopologyCertificate_p1494_p_adic_solenoid_only_periodic_point

-- N001 = hk: 2 ≤ k
-- N002 = hP_recurrent: ∀ (q : ℕ), Nat.Prime q → ∀ (N : ℕ), ∃ n, N ≤ n ∧ P n = q
-- N003 = hz: (∀ (n : ℕ), ‖z n‖ = 1) ∧ ∀ (n : ℕ), z n = z (n + 1) ^ P n
-- N004 = goal: (∃ m, 0 < m ∧ Function.IsPeriodicPt (fun w n => w n ^ k) m z) ↔ z = fun x => 1

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N002 → N001 → N003 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B002 B001 B003
  exact H_N004

end TopologyCertificate_p1494_p_adic_solenoid_only_periodic_point

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1499_countablytight_iff_prod_firstcountable
-- topology_sha256: 6d791668e76419bbfe9379e31a02f72cf68e3d1b1e9e38d859c818bd9a9bb10a
namespace TopologyCertificate_p1499_countablytight_iff_prod_firstcountable

-- N001 = goal: (∀ (A : Set X), ∀ x ∈ closure A, ∃ B ⊆ A, B.Countable ∧ x ∈ closure B) ↔ ∀ (Y : Type v) [inst : TopologicalSpace Y] [FirstCountableTopology Y] (A : Set (X × Y)), ∀ p ∈ closure A, ∃ B ⊆ A, B.Countable ∧ p ∈ closure B

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p1499_countablytight_iff_prod_firstcountable

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1521_orbit_contained_free_action_restrict_measu
-- topology_sha256: 471b6781f1c3079dd6b581fa595b17e813a968fe878903ea9c3212fb04a978f3
namespace TopologyCertificate_p1521_orbit_contained_free_action_restrict_measu

-- N001 = hB: MeasurableSet B
-- N002 = hc_free: ∀ (y : Y), MulAction.stabilizer Γ y = ⊥
-- N003 = horbit: ∀ (δ : Δ) (y : Y), ∃ γ, δ • y = γ • y
-- N004 = inst._@.proofs.2709197330._hygCtx._hyg.35: MeasurableConstSMul Δ Y
-- N005 = inst._@.proofs.2709197330._hygCtx._hyg.20: StandardBorelSpace Y
-- N006 = inst._@.proofs.2709197330._hygCtx._hyg.11: Countable Γ
-- N007 = inst._@.proofs.2709197330._hygCtx._hyg.31: MeasurableConstSMul Γ Y
-- N008 = inst._@.proofs.2709197330._hygCtx._hyg.119: MeasureTheory.SMulInvariantMeasure Γ Y μ
-- N009 = hS_meas: ∀ (γ : Γ), MeasurableSet (S γ)
-- N010 = hB_eq: B = ⋃ γ, B ∩ S γ
-- N011 = hC_disjoint: Pairwise (Function.onFun Disjoint fun γ => B ∩ S γ)
-- N012 = himage_eq: (fun y => δ • y) '' B = ⋃ γ, γ • (B ∩ S γ)
-- N013 = hT_disjoint: Pairwise (Function.onFun Disjoint fun γ => γ • (B ∩ S γ))
-- N014 = hC_meas: ∀ (γ : Γ), MeasurableSet (B ∩ S γ)
-- N015 = hT_meas: ∀ (γ : Γ), MeasurableSet (γ • (B ∩ S γ))
-- N016 = goal: μ ((fun y => δ • y) '' B) = μ B

-- E001 represents h_001_hs_meas
-- E002 represents h_002_hb_eq
-- E003 represents h_004_hc_disjoint
-- E004 represents h_005_himage_eq
-- E005 represents h_007_ht_disjoint
-- E006 represents h_003_hc_meas
-- E007 represents h_006_ht_meas
-- E008 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (B007 : N007)
    (B008 : N008)
    (E001 : N005 → N007 → N004 → N009)
    (E002 : N003 → N010)
    (E003 : N002 → N011)
    (E004 : N003 → N012)
    (E005 : N002 → N013)
    (E006 : N001 → N009 → N014)
    (E007 : N007 → N014 → N015)
    (E008 : N006 → N008 → N010 → N014 → N011 → N012 → N015 → N013 → N016)
    : N016 := by
  have H_N009 : N009 := E001 B005 B007 B004
  have H_N010 : N010 := E002 B003
  have H_N011 : N011 := E003 B002
  have H_N012 : N012 := E004 B003
  have H_N013 : N013 := E005 B002
  have H_N014 : N014 := E006 B001 H_N009
  have H_N015 : N015 := E007 B007 H_N014
  have H_N016 : N016 := E008 B006 B008 H_N010 H_N014 H_N011 H_N012 H_N015 H_N013
  exact H_N016

end TopologyCertificate_p1521_orbit_contained_free_action_restrict_measu

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1530_inverse_along_mem_bicommutant
-- topology_sha256: b46fcaa3152d6c46b1095bf53141771c7e60801a5c82e999fd8954042fb790bd
namespace TopologyCertificate_p1530_inverse_along_mem_bicommutant

-- N001 = hbad: b * a * d = d
-- N002 = hbd: ∃ x y, b = d * x ∧ b = y * d
-- N003 = hdab: d * a * b = d
-- N004 = goal: ∀ (c : S), c * a = a * c → c * d = d * c → c * b = b * c

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N001 → N003 → N002 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B001 B003 B002
  exact H_N004

end TopologyCertificate_p1530_inverse_along_mem_bicommutant

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1552_index_two_infinite_cyclic_classification
-- topology_sha256: b970c05a80a45b5cb42281387b00efc48d0120f20aec20b1b700ceda483f090b
namespace TopologyCertificate_p1552_index_two_infinite_cyclic_classification

-- N001 = hgen: Subgroup.closure {v, t} = ⊤
-- N002 = hindex: (Subgroup.zpowers t).index = 2
-- N003 = htinf: Infinite ↥(Subgroup.zpowers t)
-- N004 = htors: ∃ x, x ≠ 1 ∧ IsOfFinOrder x
-- N005 = htinj: Function.Injective fun k => t ^ k
-- N006 = hvH: v ∉ Subgroup.zpowers t
-- N007 = hv2mem: v * v ∈ Subgroup.zpowers t
-- N008 = goal: (∃ n e, e (PresentedGroup.of 0) = v ∧ e (PresentedGroup.of 1) = t ∧ Nonempty (K ≃* Multiplicative ℤ × Multiplicative (ZMod 2))) ∨ ∃ e, e (PresentedGroup.of 0) = v ∧ e (PresentedGroup.of 1) = t ∧ Nonempty (K ≃* Monoid.Coprod (Multiplicative (ZMod 2)) (Multiplicative (ZMod 2)))

-- E001 represents h_001_htinj
-- E002 represents h_002_hvh
-- E003 represents h_003_hv2mem
-- E004 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (N008 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N003 → N005)
    (E002 : N001 → N002 → N006)
    (E003 : N002 → N007)
    (E004 : N001 → N002 → N004 → N005 → N006 → N007 → N008)
    : N008 := by
  have H_N005 : N005 := E001 B003
  have H_N006 : N006 := E002 B001 B002
  have H_N007 : N007 := E003 B002
  have H_N008 : N008 := E004 B001 B002 B004 H_N005 H_N006 H_N007
  exact H_N008

end TopologyCertificate_p1552_index_two_infinite_cyclic_classification

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1639_relative_commuting_probability_le
-- topology_sha256: 238ee4d8a7cc5f36548c7db5590c508e76736bd9d1fa902a5b8e58d80fd2b1f5
namespace TopologyCertificate_p1639_relative_commuting_probability_le

-- N001 = inst._@.proofs.3607020331._hygCtx._hyg.13: N.Normal
-- N002 = inst._@.proofs.3607020331._hygCtx._hyg.6: Finite G
-- N003 = hnat: A ≤ B * C
-- N004 = hK: Nat.card ↥I * Nat.card ↥Kbar = Nat.card ↥K
-- N005 = hG: Nat.card (G ⧸ N) * Nat.card ↥N = Nat.card G
-- N006 = hnonneg: 0 ≤ ↑(Nat.card ↥K) * ↑(Nat.card G)
-- N007 = hden: ↑(Nat.card ↥K) * ↑(Nat.card G) = ↑(Nat.card ↥Kbar) * ↑(Nat.card (G ⧸ N)) * (↑(Nat.card ↥I) * ↑(Nat.card ↥N))
-- N008 = hnum: ↑A ≤ ↑(B * C)
-- N009 = hfactor: ↑B / (↑(Nat.card ↥Kbar) * ↑(Nat.card (G ⧸ N))) * (↑C / (↑(Nat.card ↥I) * ↑(Nat.card ↥N))) = ↑(B * C) / (↑(Nat.card ↥K) * ↑(Nat.card G))
-- N010 = goal: ↑A / (↑(Nat.card ↥K) * ↑(Nat.card G)) ≤ ↑(Nat.card { p // Commute (↑p.1) p.2 }) / (↑(Nat.card ↥Kbar) * ↑(Nat.card (G ⧸ N))) * (↑(Nat.card { p // Commute (↑p.1) p.2 }) / (↑(Nat.card ↥(Subgroup.comap N.subtype K)) * ↑(Nat.card ↥N)))

-- E001 represents h_001_hnat
-- E002 represents h_002_hk
-- E003 represents h_003_hg
-- E004 represents h_006_hnonneg
-- E005 represents h_004_hden
-- E006 represents h_005_hnum
-- E007 represents h_007_hfactor
-- E008 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (E001 : N002 → N001 → N003)
    (E002 : N002 → N001 → N004)
    (E003 : N005)
    (E004 : N006)
    (E005 : N001 → N004 → N005 → N007)
    (E006 : N003 → N008)
    (E007 : N001 → N007 → N009)
    (E008 : N001 → N008 → N006 → N009 → N010)
    : N010 := by
  have H_N003 : N003 := E001 B002 B001
  have H_N004 : N004 := E002 B002 B001
  have H_N005 : N005 := E003
  have H_N006 : N006 := E004
  have H_N007 : N007 := E005 B001 H_N004 H_N005
  have H_N008 : N008 := E006 H_N003
  have H_N009 : N009 := E007 B001 H_N007
  have H_N010 : N010 := E008 B001 H_N008 H_N006 H_N009
  exact H_N010

end TopologyCertificate_p1639_relative_commuting_probability_le

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1662_binary_quadratic_form_volume_identity
-- topology_sha256: 36740eb1859b61cc84e98c0fba8102c8ee8ee7c1504f40a8dff4ff09d88d2761
namespace TopologyCertificate_p1662_binary_quadratic_form_volume_identity

-- N001 = ha: 0 < a
-- N002 = hc: c < 0
-- N003 = hlampos: 0 < lam
-- N004 = hlamroot: ↑a * lam ^ 2 + ↑b * lam + ↑c = 0
-- N005 = hmupos: 0 < mu
-- N006 = hmuroot: ↑a * mu ^ 2 + ↑(-2 * a - b) * mu + ↑(a + b + c) = 0
-- N007 = hmuunique: ∀ (x : ℝ), 0 < x → ↑a * x ^ 2 + ↑(-2 * a - b) * x + ↑(a + b + c) = 0 → x = mu
-- N008 = hsum: a + b + c < 0
-- N009 = hA: 0 < ↑a
-- N010 = hC: ↑c < 0
-- N011 = hsumR: ↑a + ↑b + ↑c < 0
-- N012 = hmurootR: ↑a * mu ^ 2 + (-2 * ↑a - ↑b) * mu + (↑a + ↑b + ↑c) = 0
-- N013 = hmuunique': ∀ (x : ℝ), 0 < x → ↑a * x ^ 2 + (-2 * ↑a - ↑b) * x + (↑a + ↑b + ↑c) = 0 → x = mu
-- N014 = hlamne: lam ≠ 0
-- N015 = hfmu: ↑a + (-2 * ↑a - ↑b) + (↑a + ↑b + ↑c) = ↑c
-- N016 = hlamgt: 1 < lam
-- N017 = hmu_at_one: ↑a + (-2 * ↑a - ↑b) + (↑a + ↑b + ↑c) < 0
-- N018 = hrel: 1 - ↑c / (↑a * lam) = mu
-- N019 = hAne: ↑a ≠ 0
-- N020 = hCne: ↑c ≠ 0
-- N021 = hsumne: ↑a + ↑b + ↑c ≠ 0
-- N022 = hmu_gt: 1 < mu
-- N023 = hcdiv: ↑c / (↑a * lam) = -(↑b / ↑a) - lam
-- N024 = hVlam: ↑a * lam * (lam - 1) * (1 + 1 / lam ^ 2 + 1 / (lam - 1) ^ 2) = ↑a * (lam ^ 2 - lam) + 2 * ↑a + ↑a * (↑a * lam + ↑b) / ↑c - ↑a * (↑a * lam + ↑a + ↑b) / (↑a + ↑b + ↑c)
-- N025 = hmlin: mu = lam + 1 + ↑b / ↑a
-- N026 = hVmu: ↑a * mu * (mu - 1) * (1 + 1 / mu ^ 2 + 1 / (mu - 1) ^ 2) = ↑a * (mu ^ 2 - mu) + 2 * ↑a + ↑a * (↑a * mu + (-2 * ↑a - ↑b)) / (↑a + ↑b + ↑c) - ↑a * (↑a * mu + ↑a + (-2 * ↑a - ↑b)) / (↑a + (-2 * ↑a - ↑b) + (↑a + ↑b + ↑c))
-- N027 = hquad: ↑a * (lam ^ 2 - lam) + ↑a * (mu ^ 2 - mu) = ↑b + ↑b ^ 2 / ↑a - 2 * ↑c
-- N028 = hrC: ↑a * (↑a * lam + ↑b) / ↑c - ↑a * (↑a * mu - ↑a - ↑b) / ↑c = ↑a * ↑b / ↑c
-- N029 = hrD: -↑a * (↑a * lam + ↑a + ↑b) / (↑a + ↑b + ↑c) + ↑a * (↑a * mu - 2 * ↑a - ↑b) / (↑a + ↑b + ↑c) = -↑a * (2 * ↑a + ↑b) / (↑a + ↑b + ↑c)
-- N030 = goal: ↑a * lam * (lam - 1) * (1 + 1 / lam ^ 2 + 1 / (lam - 1) ^ 2) + ↑a * mu * (mu - 1) * (1 + 1 / mu ^ 2 + 1 / (mu - 1) ^ 2) = 4 * ↑a + ↑b + ↑b ^ 2 / ↑a + ↑a * ↑b / ↑c - 2 * ↑c - ↑a * (2 * ↑a + ↑b) / (↑a + ↑b + ↑c)

-- E001 represents h_001_ha
-- E002 represents h_002_hc
-- E003 represents h_003_hsumr
-- E004 represents h_005_hmurootr
-- E005 represents h_008_hmuunique
-- E006 represents h_011_hlamne
-- E007 represents h_018_hfmu
-- E008 represents h_004_hlamgt
-- E009 represents h_006_hmu_at_one
-- E010 represents h_009_hrel
-- E011 represents h_010_hane
-- E012 represents h_012_hcne
-- E013 represents h_013_hsumne
-- E014 represents h_007_hmu_gt
-- E015 represents h_014_hcdiv
-- E016 represents h_016_hvlam
-- E017 represents h_015_hmlin
-- E018 represents h_017_hvmu
-- E019 represents h_019_hquad
-- E020 represents h_020_hrc
-- E021 represents h_021_hrd
-- E022 represents h_goal

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
    (N025 : Prop)
    (N026 : Prop)
    (N027 : Prop)
    (N028 : Prop)
    (N029 : Prop)
    (N030 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (B007 : N007)
    (B008 : N008)
    (E001 : N001 → N009)
    (E002 : N002 → N010)
    (E003 : N008 → N011)
    (E004 : N006 → N012)
    (E005 : N007 → N013)
    (E006 : N003 → N014)
    (E007 : N015)
    (E008 : N004 → N003 → N009 → N010 → N011 → N016)
    (E009 : N010 → N017)
    (E010 : N004 → N003 → N009 → N010 → N013 → N018)
    (E011 : N009 → N019)
    (E012 : N010 → N020)
    (E013 : N011 → N021)
    (E014 : N005 → N009 → N011 → N012 → N017 → N022)
    (E015 : N004 → N019 → N014 → N023)
    (E016 : N004 → N003 → N009 → N010 → N011 → N016 → N024)
    (E017 : N018 → N023 → N025)
    (E018 : N005 → N009 → N011 → N012 → N017 → N022 → N026)
    (E019 : N004 → N019 → N025 → N027)
    (E020 : N019 → N020 → N025 → N028)
    (E021 : N019 → N021 → N025 → N029)
    (E022 : N024 → N026 → N015 → N027 → N028 → N029 → N030)
    : N030 := by
  have H_N009 : N009 := E001 B001
  have H_N010 : N010 := E002 B002
  have H_N011 : N011 := E003 B008
  have H_N012 : N012 := E004 B006
  have H_N013 : N013 := E005 B007
  have H_N014 : N014 := E006 B003
  have H_N015 : N015 := E007
  have H_N016 : N016 := E008 B004 B003 H_N009 H_N010 H_N011
  have H_N017 : N017 := E009 H_N010
  have H_N018 : N018 := E010 B004 B003 H_N009 H_N010 H_N013
  have H_N019 : N019 := E011 H_N009
  have H_N020 : N020 := E012 H_N010
  have H_N021 : N021 := E013 H_N011
  have H_N022 : N022 := E014 B005 H_N009 H_N011 H_N012 H_N017
  have H_N023 : N023 := E015 B004 H_N019 H_N014
  have H_N024 : N024 := E016 B004 B003 H_N009 H_N010 H_N011 H_N016
  have H_N025 : N025 := E017 H_N018 H_N023
  have H_N026 : N026 := E018 B005 H_N009 H_N011 H_N012 H_N017 H_N022
  have H_N027 : N027 := E019 B004 H_N019 H_N025
  have H_N028 : N028 := E020 H_N019 H_N020 H_N025
  have H_N029 : N029 := E021 H_N019 H_N021 H_N025
  have H_N030 : N030 := E022 H_N024 H_N026 H_N015 H_N027 H_N028 H_N029
  exact H_N030

end TopologyCertificate_p1662_binary_quadratic_form_volume_identity

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1722_hirzebruch_jung_large_entries_at_most_two
-- topology_sha256: 68ed2744cdb1d7035722b828fa61040478e1c5ad3b5b31aff3bcf59ad48149a7
namespace TopologyCertificate_p1722_hirzebruch_jung_large_entries_at_most_two

-- N001 = ha: ∀ (i : Fin n), 2 ≤ a i
-- N002 = hfrac: List.foldr (fun x r => x - 1 / r) 0 (List.ofFn fun i => ↑(a i)) = ↑p / ↑q
-- N003 = hn: 1 ≤ n
-- N004 = hp: 0 < p
-- N005 = hpq: p.Coprime q
-- N006 = hq: 0 < q
-- N007 = hS: 2 * ↑p / 9 < ∑ i with 3 < a i, ↑(a i - 3)
-- N008 = goal: {i | 3 < a i}.card ≤ 2

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (N008 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (B007 : N007)
    (E001 : N003 → N001 → N004 → N006 → N005 → N002 → N007 → N008)
    : N008 := by
  have H_N008 : N008 := E001 B003 B001 B004 B006 B005 B002 B007
  exact H_N008

end TopologyCertificate_p1722_hirzebruch_jung_large_entries_at_most_two

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1744_euler_congruence_for_counted_reduced_resid
-- topology_sha256: 28dc7b12bcf67d899a4a1555e8b39cf898bb49fb686730674b97db4492424394
namespace TopologyCertificate_p1744_euler_congruence_for_counted_reduced_resid

-- N001 = hcoprime: x.Coprime N
-- N002 = hn: n = {a ∈ Finset.Ico 1 N | a.Coprime N}.card
-- N003 = hN: 0 < N
-- N004 = goal: x ^ n ≡ 1 [MOD N]

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N003 → N001 → N002 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B003 B001 B002
  exact H_N004

end TopologyCertificate_p1744_euler_congruence_for_counted_reduced_resid

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1747_parbelos_area_and_vertex_parallelogram
-- topology_sha256: 37863b4fd33cabcaee6b1186d21487043328016f8acaea5ea618c19db6ea265c
namespace TopologyCertificate_p1747_parbelos_area_and_vertex_parallelogram

-- N001 = ha: 0 < a
-- N002 = hb: 0 < b
-- N003 = hba: b < 2 * a
-- N004 = goal: let C₁ := (0, 0); let C₂ := (2 * b, 0); let C₃ := (4 * a, 0); let U := fun x => a - (x - 2 * a) ^ 2 / (4 * a); let L := fun x => b / 2 - (x - b) ^ 2 / (2 * b); let R := fun x => (2 * a - b) / 2 - (x - (2 * a + b)) ^ 2 / (2 * (2 * a - b)); let P := {p | 0 ≤ p.1 ∧ p.1 ≤ 2 * b ∧ L p.1 ≤ p.2 ∧ p.2 ≤ U p.1 ∨ 2 * b ≤ p.1 ∧ p.1 ≤ 4 * a ∧ R p.1 ≤ p.2 ∧ p.2 ≤ U p.1}; let V₁ := (b, b / 2); let V₂ := (2 * a, a); let V₃ := (2 * a + b, a - b / 2); (V₁ - C₂ = V₂ - V₃ ∧ V₂ - V₁ = V₃ - C₂) ∧ MeasureTheory.volume P = 4 / 3 * MeasureTheory.volume ((convexHull ℝ) {C₂, V₁, V₂, V₃})

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N001 → N002 → N003 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B001 B002 B003
  exact H_N004

end TopologyCertificate_p1747_parbelos_area_and_vertex_parallelogram

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1776_subgroup_isup_eq_boolean_isup
-- topology_sha256: fb662cf9564d5c688def1900e978d2b19b77ef282febb3dedb4a33e5a1159239
namespace TopologyCertificate_p1776_subgroup_isup_eq_boolean_isup

-- N001 = hgen: AddSubgroup.closure (Set.range a) = ⊤
-- N002 = hprod: ∀ (x y : A), ↑(W x) ⊆ Set.image2 (fun g h => g * h) ↑(W y) ↑(W (2 • y - x))
-- N003 = goal: ⨆ x, W x = ⨆ s, W (∑ i ∈ s, a i)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (B001 : N001)
    (B002 : N002)
    (E001 : N001 → N002 → N003)
    : N003 := by
  have H_N003 : N003 := E001 B001 B002
  exact H_N003

end TopologyCertificate_p1776_subgroup_isup_eq_boolean_isup

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1808_uniform_excision_implies_coarse_excision
-- topology_sha256: 9943d8a4477aad14cf2e09eabf976b18caee95156b6751314b607bb9d2607bee
namespace TopologyCertificate_p1808_uniform_excision_implies_coarse_excision

-- N001 = hAB: A ∪ B = Set.univ
-- N002 = hcompat: ∃ E ∈ uniformity X, E ∈ coarse
-- N003 = hex: ∃ U ∈ uniformity X, ∃ κ, Monotone κ ∧ (∀ V ∈ uniformity X, ∃ W, ↑W ∈ uniformity X ∧ OrderDual.ofDual (κ (OrderDual.toDual W)) ⊆ V) ∧ ∀ (W : { W // W ⊆ U }), (↑W).image A ∩ (↑W).image B ⊆ (OrderDual.ofDual (κ (OrderDual.toDual W))).image (A ∩ B)
-- N004 = hV: V ∈ coarse
-- N005 = goal: ∃ T ∈ coarse, V.image A ∩ V.image B ⊆ T.image (A ∩ B)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N001 → N002 → N003 → N004 → N005)
    : N005 := by
  have H_N005 : N005 := E001 B001 B002 B003 B004
  exact H_N005

end TopologyCertificate_p1808_uniform_excision_implies_coarse_excision

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1874_proposition_4_9
-- topology_sha256: bcec890446f03ce91c83154fc3473ac279905ed22afa855c356ec184c9c9a442
namespace TopologyCertificate_p1874_proposition_4_9

-- N001 = hμ: ∀ (n : ℕ) (A : Set ↑(Set.Icc 0 1)), A.OrdConnected → Metric.diam A ≤ Real.rpow 2 (-↑n) → μ A ≤ ENNReal.ofReal (Real.rpow 2 (-(α * ↑n + ↑(f n))))
-- N002 = hα: 0 ≤ α
-- N003 = hf: Summable fun n => Real.rpow 2 (-↑(f n))
-- N004 = hμu: μ Set.univ < ⊤
-- N005 = htsum: ∑' (n : ℕ), ENNReal.ofReal (Real.rpow 2 (-↑(f n))) < ⊤
-- N006 = hK: K < ⊤
-- N007 = goal: ∫⁻ (x : ↑(Set.Icc 0 1)), ∫⁻ (y : ↑(Set.Icc 0 1)), 1 / ENNReal.ofReal |↑x - ↑y| ^ α ∂μ ∂μ < ⊤

-- E001 represents h_001_h_u
-- E002 represents h_002_htsum
-- E003 represents h_003_hk
-- E004 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N001 → N004)
    (E002 : N003 → N005)
    (E003 : N004 → N005 → N006)
    (E004 : N002 → N003 → N001 → N004 → N006 → N007)
    : N007 := by
  have H_N004 : N004 := E001 B001
  have H_N005 : N005 := E002 B003
  have H_N006 : N006 := E003 H_N004 H_N005
  have H_N007 : N007 := E004 B002 B003 B001 H_N004 H_N006
  exact H_N007

end TopologyCertificate_p1874_proposition_4_9

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1918_correspondence_of_induced_probability_assi
-- topology_sha256: 904ffa87e9965ebbd17e6fd553aa5ec27a654b9b759f39bd4bd300ddc3f04112
namespace TopologyCertificate_p1918_correspondence_of_induced_probability_assi

-- N001 = hPconj: ∀ (φ ψ : Formula), P (conj φ ψ) = P φ ∩ P ψ
-- N002 = hPneg: ∀ (φ : Formula), P (neg φ) = N φ
-- N003 = inst._@.proofs.4233523538._hygCtx._hyg.23: MeasureTheory.IsProbabilityMeasure μ
-- N004 = goal: T41 q = p ∧ T14 p = q

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N003 → N002 → N001 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B003 B002 B001
  exact H_N004

end TopologyCertificate_p1918_correspondence_of_induced_probability_assi

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1971_finite_diversity_induces_metric
-- topology_sha256: c03a45d7a39d855d98881c8e2d73689fa54da6b90960483569ca3b857b3d8a26
namespace TopologyCertificate_p1971_finite_diversity_induces_metric

-- N001 = h_triangle: ∀ (A B C : { A // A.Finite }), (↑B).Nonempty → δ ⟨↑A ∪ ↑C, ⋯⟩ ≤ δ ⟨↑A ∪ ↑B, ⋯⟩ + δ ⟨↑B ∪ ↑C, ⋯⟩
-- N002 = h_zero: ∀ (A : { A // A.Finite }), δ A = 0 ↔ (↑A).Subsingleton
-- N003 = goal: (∃ m, ∀ (x y : X), dist x y = δ ⟨{x, y}, ⋯⟩) ∧ (∀ (A B : { A // A.Finite }), ↑A ⊆ ↑B → δ A ≤ δ B) ∧ ∀ (A B : { A // A.Finite }), (↑A ∩ ↑B).Nonempty → δ ⟨↑A ∪ ↑B, ⋯⟩ ≤ δ A + δ B

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (B001 : N001)
    (B002 : N002)
    (E001 : N002 → N001 → N003)
    : N003 := by
  have H_N003 : N003 := E001 B002 B001
  exact H_N003

end TopologyCertificate_p1971_finite_diversity_induces_metric

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1994_quantitative_equivalence_of_plumpness_and_
-- topology_sha256: a3bfaebfa10bc5c7babc922f77d3b381fa73f1340b54a9db20a291da7b6fa59f
namespace TopologyCertificate_p1994_quantitative_equivalence_of_plumpness_and

-- N001 = goal: (∀ (R b : ℝ), 0 < R → 0 < b → b < 1 → (∀ y ∈ E, ∀ (r : ℝ), 0 < r → r ≤ R → ∃ z, Metric.ball z (b * r) ⊆ Metric.ball y r ∩ E) → ∀ (δ : ℝ) (m : ℤ) (b₀ B₀ : ℝ), 0 < δ → δ < 1 → 0 < b₀ → b₀ ≤ B₀ → b₀ / B₀ ≤ b → B₀ * δ ^ m ≤ R → ∀ y ∈ E, ∀ (k : ℤ), m ≤ k → ∃ z, Metric.ball z (b₀ * δ ^ k) ⊆ Metric.ball y (B₀ * δ ^ k) ∩ E) ∧ ∀ (δ : ℝ) (m : ℤ) (b₀ B₀ : ℝ), 0 < δ → δ < 1 → 0 < b₀ → b₀ ≤ B₀ → (∀ y ∈ E, ∀ (k : ℤ), m ≤ k → ∃ z, Metric.ball z (b₀ * δ ^ k) ⊆ Metric.ball y (B₀ * δ ^ k) ∩ E) → ∀ (R b : ℝ), 0 < R → 0 < b → b < 1 → b ≤ δ * b₀ / B₀ → R ≤ B₀ * δ ^ (m - 1) → ∀ y ∈ E, ∀ (r : ℝ), 0 < r → r ≤ R → ∃ z, Metric.ball z (b * r) ⊆ Metric.ball y r ∩ E

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p1994_quantitative_equivalence_of_plumpness_and

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2049_scaling_implies_a_cone_distance
-- topology_sha256: 5e7d1222eab3158d1cbc4ea284d43f37ff4452b5d3b0f9afe6796516f43e5058
namespace TopologyCertificate_p2049_scaling_implies_a_cone_distance

-- N001 = hbound: ∀ (x₀ x₁ : X), x₀ ≠ x₁ → 0 < dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ∧ dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ≤ 4
-- N002 = hscale: ∀ (x₀ x₁ : X) (r₀ r₁ : NNReal), dist (q (x₀, r₀)) (q (x₁, r₁)) ^ 2 = ↑r₀ * ↑r₁ * dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 + (↑r₀ - ↑r₁) ^ 2
-- N003 = goal: let d_X := fun p => Real.arccos (1 - dist (q (p.1, 1)) (q (p.2, 1)) ^ 2 / 2); (∀ (x₀ x₁ : X), d_X (x₀, x₁) ∈ Set.Icc 0 Real.pi) ∧ (∃ m, ∀ (x₀ x₁ : X), dist x₀ x₁ = d_X (x₀, x₁)) ∧ ∀ (x₀ x₁ : X) (r₀ r₁ : NNReal), dist (q (x₀, r₀)) (q (x₁, r₁)) ^ 2 = ↑r₀ ^ 2 + ↑r₁ ^ 2 - 2 * ↑r₀ * ↑r₁ * Real.cos (d_X (x₀, x₁))

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (B001 : N001)
    (B002 : N002)
    (E001 : N002 → N001 → N003)
    : N003 := by
  have H_N003 : N003 := E001 B002 B001
  exact H_N003

end TopologyCertificate_p2049_scaling_implies_a_cone_distance

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2075_metric_amalgamation
-- topology_sha256: deb664ff2993b355db8b0a33e35ab9f9f0aae3ff5569326fe1891b0dcff1b2ed
namespace TopologyCertificate_p2075_metric_amalgamation

-- N001 = hB_clopen: ∀ (i : I), IsClopen (B i)
-- N002 = hB_cover: ⋃ i, B i = Set.univ
-- N003 = hB_disjoint: Set.univ.PairwiseDisjoint B
-- N004 = he_top: ∀ (i : I), PseudoMetricSpace.toUniformSpace.toTopologicalSpace = inferInstance
-- N005 = goal: ∃ mD, (∀ (i : I) (x y : ↑(B i)), dist ↑x ↑y = dist x y) ∧ (∀ (i j : I), i ≠ j → ∀ (x : ↑(B i)) (y : ↑(B j)), dist ↑x ↑y = dist x (p i) + dist ↑(p i) ↑(p j) + dist (p j) y) ∧ PseudoMetricSpace.toUniformSpace.toTopologicalSpace = inferInstance ∧ ∀ (ε : ℝ), 0 ≤ ε → ((∀ (i : I), Metric.ediam (B i) ≤ ENNReal.ofReal ε) ∧ ∀ (i : I), Metric.ediam Set.univ ≤ ENNReal.ofReal ε) → sSup (Set.range fun q => |dist q.1 q.2 - dist q.1 q.2|) ≤ 4 * ε

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N003 → N001 → N002 → N004 → N005)
    : N005 := by
  have H_N005 : N005 := E001 B003 B001 B002 B004
  exact H_N005

end TopologyCertificate_p2075_metric_amalgamation

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2109_stable_equivalence_empty_subfield_points_i
-- topology_sha256: 83c1f3429a819d27d51092c231154faa95c7febde4ce81a49b36cda28c209492
namespace TopologyCertificate_p2109_stable_equivalence_empty_subfield_points_i

-- N001 = hstable: Relation.EqvGen (fun X Y => (∃ k d S T, X = ⟨k, S⟩ ∧ Y = ⟨k + d, T⟩ ∧ ∃ r s φ ψ, (∀ v ∈ S, ∃ v', Fin.append v v' ∈ T) ∧ ∀ (v : Fin k → ℝ) (v' : Fin d → ℝ), Fin.append v v' ∈ T ↔ v ∈ S ∧ (∀ (i : Fin r), ∑ j, MvPolynomial.eval₂ (Int.castRingHom ℝ) v (φ i j) * v' j > 0) ∧ ∀ (i : Fin s), ∑ j, MvPolynomial.eval₂ (Int.castRingHom ℝ) v (ψ i j) * v' j = 0) ∨ ∃ k l S T, X = ⟨k, S⟩ ∧ Y = ⟨l, T⟩ ∧ ∃ h, (∀ (i : Fin l), ∃ p q, ∀ (v : ↑S), MvPolynomial.eval₂ (Rat.castHom ℝ) (↑v) q ≠ 0 ∧ ↑(h v) i = MvPolynomial.eval₂ (Rat.castHom ℝ) (↑v) p / MvPolynomial.eval₂ (Rat.castHom ℝ) (↑v) q) ∧ ∀ (i : Fin k), ∃ p q, ∀ (w : ↑T), MvPolynomial.eval₂ (Rat.castHom ℝ) (↑w) q ≠ 0 ∧ ↑(h.symm w) i = MvPolynomial.eval₂ (Rat.castHom ℝ) (↑w) p / MvPolynomial.eval₂ (Rat.castHom ℝ) (↑w) q) ⟨n, V⟩ ⟨m, W⟩
-- N002 = hpoints: Rollout_p2109_stable_equivalence_empty_subfield_points_i.HasSubfieldPoint A ⟨n, V⟩ ↔ Rollout_p2109_stable_equivalence_empty_subfield_points_i.HasSubfieldPoint A ⟨m, W⟩
-- N003 = goal: (¬∃ v, (fun i => ↑(v i)) ∈ V) ↔ ¬∃ w, (fun i => ↑(w i)) ∈ W

-- E001 represents h_001_hpoints
-- E002 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    (E002 : N002 → N003)
    : N003 := by
  have H_N002 : N002 := E001 B001
  have H_N003 : N003 := E002 H_N002
  exact H_N003

end TopologyCertificate_p2109_stable_equivalence_empty_subfield_points_i

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2112_diagonal_nonnegative_part_difference
-- topology_sha256: 541c0b3df8342957f6a05dab1b135f216666e01e3c4308e0074bef9b58f6652e
namespace TopologyCertificate_p2112_diagonal_nonnegative_part_difference

-- N001 = hω: ∀ (i : Fin n), 0 ≤ ω i ∧ ω i ≤ 1 ∧ (if 0 ≤ x i then 1 else 0) * x i - (if 0 ≤ y i then 1 else 0) * y i = ω i * (x i - y i)
-- N002 = goal: ∃ ω, (∀ (i : Fin n), 0 ≤ ω i ∧ ω i ≤ 1) ∧ ((fun z => Matrix.diagonal fun i => if 0 ≤ z i then 1 else 0) x).mulVec x - ((fun z => Matrix.diagonal fun i => if 0 ≤ z i then 1 else 0) y).mulVec y = (Matrix.diagonal ω).mulVec (x - y)

-- E001 represents h_001_h
-- E002 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (E001 : N001)
    (E002 : N001 → N002)
    : N002 := by
  have H_N001 : N001 := E001
  have H_N002 : N002 := E002 H_N001
  exact H_N002

end TopologyCertificate_p2112_diagonal_nonnegative_part_difference

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2116_pendant_branch_laplacian_eigenvector_decay
-- topology_sha256: 6def72b531159d4e71e5ba8bebbb09ad9dc81baad6b3138a095ddbee09f704e8
namespace TopologyCertificate_p2116_pendant_branch_laplacian_eigenvector_decay

-- N001 = hbranch: ∀ (a b : Fin k), G.Adj (i a) (i b) ↔ ↑a + 1 = ↑b ∨ ↑b + 1 = ↑a
-- N002 = heigen: (SimpleGraph.lapMatrix ℝ G).mulVec φ = lam • φ
-- N003 = hexternal: ∃ x ∉ Set.range i, G.Adj (i ⟨0, hk⟩) x ∧ ∀ (a : Fin k), ∀ v ∉ Set.range i, G.Adj (i a) v → a = ⟨0, hk⟩ ∧ v = x
-- N004 = hi: Function.Injective i
-- N005 = hk: 1 ≤ k
-- N006 = hlam: 4 < lam
-- N007 = goal: let γ := 2 / (lam - 2); 0 < γ ∧ γ < 1 ∧ (∀ (j : Fin k) (hj : ↑j + 1 < k), |φ (i ⟨↑j + 1, hj⟩)| ≤ γ * |φ (i j)|) ∧ ∀ (j : Fin k), |φ (i j)| ≤ γ ^ ↑j * |φ (i ⟨0, hk⟩)|

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (E001 : N005 → N004 → N001 → N003 → N006 → N002 → N007)
    : N007 := by
  have H_N007 : N007 := E001 B005 B004 B001 B003 B006 B002
  exact H_N007

end TopologyCertificate_p2116_pendant_branch_laplacian_eigenvector_decay

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2161_cell_entropy_inequality_for_semidiscrete_f
-- topology_sha256: 914bb69b48bd25703fb73fec441a26a5ec4704a2b1e65300ddb0beca72209839
namespace TopologyCertificate_p2161_cell_entropy_inequality_for_semidiscrete_f

-- N001 = hδ: ∀ r ∈ N, 0 < δ r
-- N002 = hε: ∀ r ∈ N, 0 ≤ ε r
-- N003 = hA: ∀ r ∈ N, 0 ≤ A r
-- N004 = hd: dρSdt = 1 / V * ∑ r ∈ N, A r * (-D r + g r + entropyProduction r)
-- N005 = hH: ∀ r ∈ N, (H r).PosSemidef
-- N006 = hT: 0 < T
-- N007 = hV: 0 < V
-- N008 = hprod: ∀ r ∈ N, 0 ≤ entropyProduction r
-- N009 = hsum: ∑ r ∈ N, A r * (-D r + g r + entropyProduction r) = -∑ r ∈ N, A r * D r + ∑ r ∈ N, A r * g r + ∑ r ∈ N, A r * entropyProduction r
-- N010 = goal: dρSdt + 1 / V * ∑ r ∈ N, A r * D r - 1 / V * ∑ r ∈ N, A r * g r ≥ 0

-- E001 represents h_001_hprod
-- E002 represents h_002_hsum
-- E003 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (B007 : N007)
    (E001 : N001 → N002 → N006 → N005 → N008)
    (E002 : N009)
    (E003 : N007 → N003 → N004 → N008 → N009 → N010)
    : N010 := by
  have H_N008 : N008 := E001 B001 B002 B006 B005
  have H_N009 : N009 := E002
  have H_N010 : N010 := E003 B007 B003 B004 H_N008 H_N009
  exact H_N010

end TopologyCertificate_p2161_cell_entropy_inequality_for_semidiscrete_f

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2227_strongmetricenvelopeofheight
-- topology_sha256: 0c7a7e1ae1d7e6f1a427f32a3d41f791bd3bd2dbc65bf4ed5fae4de7739626f6
namespace TopologyCertificate_p2227_strongmetricenvelopeofheight

-- N001 = hρ_inv: ∀ (α : G), ρ α⁻¹ = ρ α
-- N002 = hρ_lower: ∀ (α : G), 1 ≤ ρ α
-- N003 = hρ_one: ρ 1 = 1
-- N004 = goal: ((∀ (α : G), 1 ≤ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ α) ∧ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ 1 = 1 ∧ (∀ (α : G), (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ α⁻¹ = (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ α) ∧ ∀ (α β : G), (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ (α * β) ≤ max ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ α) ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ β)) ∧ (∀ (α : G), (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ α ≤ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ ∏ᶠ (n : ℕ+), f (a n) = r}) ρ α) ∧ (∀ (σ : G → ℝ), ((∀ (α : G), 1 ≤ σ α) ∧ σ 1 = 1 ∧ (∀ (α : G), σ α⁻¹ = σ α) ∧ ∀ (α β : G), σ (α * β) ≤ max (σ α) (σ β)) → (∀ (α : G), σ α ≤ ρ α) → ∀ (α : G), σ α ≤ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ α) ∧ (ρ = (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ ↔ (∀ (α : G), 1 ≤ ρ α) ∧ ρ 1 = 1 ∧ (∀ (α : G), ρ α⁻¹ = ρ α) ∧ ∀ (α β : G), ρ (α * β) ≤ max (ρ α) (ρ β)) ∧ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ = (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ ∏ᶠ (n : ℕ+), f (a n) = r}) ρ) ∧ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ ∏ᶠ (n : ℕ+), f (a n) = r}) ρ) = (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ ∏ᶠ (n : ℕ+), f (a n) = r}) ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ) ∧ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ ∏ᶠ (n : ℕ+), f (a n) = r}) ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ) = (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N002 → N003 → N001 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B002 B003 B001
  exact H_N004

end TopologyCertificate_p2227_strongmetricenvelopeofheight

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2247_sylow_rank_two_index_prime_subgroups
-- topology_sha256: 1c6ca46bbda1eeac93fb6cf04404be324d1119b830fc90bfd6f96fc2ea3164f9
namespace TopologyCertificate_p2247_sylow_rank_two_index_prime_subgroups

-- N001 = hind: Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥
-- N002 = hp: Nat.Prime p
-- N003 = hspan: Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤
-- N004 = hu: 0 < u
-- N005 = huv: v ≤ u
-- N006 = hv: 0 < v
-- N007 = hx: orderOf x = p ^ u
-- N008 = hy: orderOf y = p ^ v
-- N009 = inst._@.proofs.4000124397._hygCtx._hyg.6: Finite A
-- N010 = hE: E = Subgroup.zpowers (x ^ p ^ (u - 1)) ⊔ Subgroup.zpowers (y ^ p ^ (v - 1))
-- N011 = goal: E = Subgroup.zpowers (x ^ p ^ (u - 1)) ⊔ Subgroup.zpowers (y ^ p ^ (v - 1)) ∧ (u = 1 ∧ v = 1 → ∀ (U : Subgroup ↥↑P), U.index = p ↔ U ≤ E ∧ Nat.card ↥U = p) ∧ (v = 1 ∧ 1 < u → N.index = p ∧ E ≤ N ∧ (∀ (U : Subgroup ↥↑P), U.index = p → E ≤ U → U = N) ∧ Nonempty (↥N ≃* Multiplicative (ZMod (p ^ (u - 1))) × Multiplicative (ZMod p)) ∧ Nat.card { U // U.index = p ∧ U ≠ N } = p ∧ ∀ (U : Subgroup ↥↑P), U.index = p → U ≠ N → IsCyclic ↥U ∧ Nat.card ↥U = p ^ u ∧ U ⊓ E = Subgroup.zpowers (x ^ p ^ (u - 1))) ∧ (1 < v → ∀ (U : Subgroup ↥↑P), U.index = p → E ≤ U)

-- E001 represents h_001_he
-- E002 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (B007 : N007)
    (B008 : N008)
    (B009 : N009)
    (E001 : N002 → N004 → N006 → N007 → N008 → N003 → N001 → N010)
    (E002 : N009 → N002 → N004 → N006 → N005 → N007 → N008 → N003 → N001 → N010 → N011)
    : N011 := by
  have H_N010 : N010 := E001 B002 B004 B006 B007 B008 B003 B001
  have H_N011 : N011 := E002 B009 B002 B004 B006 B005 B007 B008 B003 B001 H_N010
  exact H_N011

end TopologyCertificate_p2247_sylow_rank_two_index_prime_subgroups

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2272_proposition_4_2
-- topology_sha256: 600b198cacdc3ae08bbac9a54879a718992687cf4b769380a7ffaa2e3faaa668
namespace TopologyCertificate_p2272_proposition_4_2

-- N001 = hγe₁e₁: ↑γ (Sum.inl 0) (Sum.inl 0) = 1
-- N002 = hγe₁e₂: ↑γ (Sum.inl 1) (Sum.inl 0) = 1
-- N003 = hγe₁f₁: ↑γ (Sum.inr 0) (Sum.inl 0) = 0
-- N004 = hγe₁f₂: ↑γ (Sum.inr 1) (Sum.inl 0) = 0
-- N005 = hγGSp: ∃ μ, (↑γ).transpose * Matrix.J (Fin 2) ℤ_[p] * ↑γ = ↑μ • Matrix.J (Fin 2) ℤ_[p]
-- N006 = inst._@.proofs.1926733331._hygCtx._hyg.8: Fact (Nat.Prime p)
-- N007 = goal: {h | (∃ A B, (↑A).det = (↑B).det ∧ h = Matrix.fromBlocks (Matrix.diagonal ![↑A 0 0, ↑B 0 0]) (Matrix.diagonal ![↑A 0 1, ↑B 0 1]) (Matrix.diagonal ![↑A 1 0, ↑B 1 0]) (Matrix.diagonal ![↑A 1 1, ↑B 1 1])) ∧ ∃ k, (∃ μ, (↑k).transpose * Matrix.J (Fin 2) ℤ_[p] * ↑k = ↑μ • Matrix.J (Fin 2) ℤ_[p]) ∧ (∀ (i : Fin 2 ⊕ Fin 2), i ≠ Sum.inl 0 → ↑p ^ m ∣ ↑k i (Sum.inl 0)) ∧ h = (↑(γ * k * γ⁻¹)).map ⇑(algebraMap ℤ_[p] ℚ_[p])} = {h | ∃ A B, (↑A).det = (↑B).det ∧ ↑p ^ m ∣ ↑A 1 0 ∧ ↑p ^ m ∣ ↑B 1 0 ∧ ↑p ^ m ∣ ↑A 0 0 - ↑B 0 0 ∧ h = (Matrix.fromBlocks (Matrix.diagonal ![↑A 0 0, ↑B 0 0]) (Matrix.diagonal ![↑A 0 1, ↑B 0 1]) (Matrix.diagonal ![↑A 1 0, ↑B 1 0]) (Matrix.diagonal ![↑A 1 1, ↑B 1 1])).map ⇑(algebraMap ℤ_[p] ℚ_[p])}

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (E001 : N006 → N005 → N001 → N002 → N003 → N004 → N007)
    : N007 := by
  have H_N007 : N007 := E001 B006 B005 B001 B002 B003 B004
  exact H_N007

end TopologyCertificate_p2272_proposition_4_2

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2331_reverse_cauchy_schwarz_with_three_term_min
-- topology_sha256: fec88aa8a97a4f2c48e2051cbfc90e6f8d3639b75ec1d7298bc969f8cf03b91b
namespace TopologyCertificate_p2331_reverse_cauchy_schwarz_with_three_term_min

-- N001 = ha: 0 < a
-- N002 = haA: a ≤ A
-- N003 = hb: 0 < b
-- N004 = hbB: b ≤ B
-- N005 = hx: ∀ (i : Fin n), a ≤ x i ∧ x i ≤ A
-- N006 = hy: ∀ (i : Fin n), b ≤ y i ∧ y i ≤ B
-- N007 = goal: (∑ i, x i ^ 2) * ∑ i, y i ^ 2 - (∑ i, x i * y i) ^ 2 ≤ (A * B - a * b) ^ 2 / 4 * min ((∑ i, x i ^ 2) ^ 2 / (A ^ 2 * a ^ 2)) (min ((∑ i, y i ^ 2) ^ 2 / (B ^ 2 * b ^ 2)) ((∑ i, x i * y i) ^ 2 / (a * b * A * B))) ∧ ∀ (k : Fin 3), ∃ m a' A' b' B' x' y', 1 ≤ m ∧ 0 < a' ∧ a' ≤ A' ∧ 0 < b' ∧ b' ≤ B' ∧ (∀ (i : Fin m), a' ≤ x' i ∧ x' i ≤ A') ∧ (∀ (i : Fin m), b' ≤ y' i ∧ y' i ≤ B') ∧ let t := ![(∑ i, x' i ^ 2) ^ 2 / (A' ^ 2 * a' ^ 2), (∑ i, y' i ^ 2) ^ 2 / (B' ^ 2 * b' ^ 2), (∑ i, x' i * y' i) ^ 2 / (a' * b' * A' * B')]; ∀ (j : Fin 3), j ≠ k → t k < t j

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (E001 : N001 → N002 → N003 → N004 → N005 → N006 → N007)
    : N007 := by
  have H_N007 : N007 := E001 B001 B002 B003 B004 B005 B006
  exact H_N007

end TopologyCertificate_p2331_reverse_cauchy_schwarz_with_three_term_min

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2332_matrix_kronecker_injective_iff_linearindep
-- topology_sha256: 812999549bfeac040effa04a22a8ad38d1e8fe269f6948bb066701c2a4298133
namespace TopologyCertificate_p2332_matrix_kronecker_injective_iff_linearindep

-- N001 = goal: ((∀ (n : ℕ), 0 < n → ∀ (X : Fin g → Matrix (Fin n) (Fin n) ℂ), ∑ j, (A j).kronecker (X j) = 0 → ∀ (j : Fin g), X j = 0) ↔ ∀ (z : Fin g → ℂ), ∑ j, z j • A j = 0 → ∀ (j : Fin g), z j = 0) ∧ ((∀ (z : Fin g → ℂ), ∑ j, z j • A j = 0 → ∀ (j : Fin g), z j = 0) ↔ LinearIndependent ℂ A)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p2332_matrix_kronecker_injective_iff_linearindep

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2342_c0singlezero_apply
-- topology_sha256: 21795638089805f2200533f25659a7f89ca729fc135727d8148dab9b2ca30161
namespace TopologyCertificate_p2342_c0singlezero_apply

-- N001 = goal: (Rollout_p2342_c0singlezero_apply.c0SingleZero x) n = (Rollout_p2342_c0singlezero_apply.c0SingleZero x) n

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p2342_c0singlezero_apply

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2468_average_projection_positive_definite
-- topology_sha256: fcffa0d1dce110e47494d5dc1748590683433e407aeda54d2ca9aeab626ab31f
namespace TopologyCertificate_p2468_average_projection_positive_definite

-- N001 = hadm: ∀ (x : EuclideanSpace ℝ (Fin n)), x ≠ 0 → μ {ω | x ∈ (∑ i ∈ J ω, C i)ᗮ} < 1
-- N002 = hproj: Measurable fun ω => (∑ i ∈ J ω, C i).starProjection
-- N003 = hx: x ≠ 0
-- N004 = inst._@.proofs.1509888941._hygCtx._hyg.17: MeasureTheory.IsProbabilityMeasure μ
-- N005 = hPint: MeasureTheory.Integrable (fun ω => (K ω).starProjection) μ
-- N006 = hfmeas: Measurable fun ω => inner ℝ x ((K ω).starProjection x)
-- N007 = hnonneg: 0 ≤ fun ω => inner ℝ x ((K ω).starProjection x)
-- N008 = hnormsq: ∀ (ω : Ω), inner ℝ x ((K ω).starProjection x) = ‖(K ω).orthogonalProjection x‖ ^ 2
-- N009 = hφint: MeasureTheory.Integrable (fun ω => (K ω).starProjection x) μ
-- N010 = hsupp: (Function.support fun ω => inner ℝ x ((K ω).starProjection x)) = {ω | x ∈ (K ω)ᗮ}ᶜ
-- N011 = hfint: MeasureTheory.Integrable (fun ω => inner ℝ x ((K ω).starProjection x)) μ
-- N012 = hbad_meas: MeasurableSet {ω | x ∈ (K ω)ᗮ}
-- N013 = hsupp_pos: 0 < μ (Function.support fun ω => inner ℝ x ((K ω).starProjection x))
-- N014 = hintpos: 0 < ∫ (ω : Ω), inner ℝ x ((K ω).starProjection x) ∂μ
-- N015 = goal: 0 < inner ℝ x ((∫ (ω : Ω), (K ω).starProjection ∂μ) x)

-- E001 represents h_001_hpint
-- E002 represents h_004_hfmeas
-- E003 represents h_005_hnonneg
-- E004 represents h_006_hnormsq
-- E005 represents h_002_h_int
-- E006 represents h_007_hsupp
-- E007 represents h_003_hfint
-- E008 represents h_008_hbad_meas
-- E009 represents h_009_hsupp_pos
-- E010 represents h_010_hintpos
-- E011 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N004 → N002 → N005)
    (E002 : N002 → N006)
    (E003 : N007)
    (E004 : N008)
    (E005 : N005 → N009)
    (E006 : N008 → N010)
    (E007 : N009 → N011)
    (E008 : N006 → N010 → N012)
    (E009 : N004 → N001 → N003 → N010 → N012 → N013)
    (E010 : N011 → N007 → N013 → N014)
    (E011 : N005 → N009 → N014 → N015)
    : N015 := by
  have H_N005 : N005 := E001 B004 B002
  have H_N006 : N006 := E002 B002
  have H_N007 : N007 := E003
  have H_N008 : N008 := E004
  have H_N009 : N009 := E005 H_N005
  have H_N010 : N010 := E006 H_N008
  have H_N011 : N011 := E007 H_N009
  have H_N012 : N012 := E008 H_N006 H_N010
  have H_N013 : N013 := E009 B004 B001 B003 H_N010 H_N012
  have H_N014 : N014 := E010 H_N011 H_N007 H_N013
  have H_N015 : N015 := E011 H_N005 H_N009 H_N014
  exact H_N015

end TopologyCertificate_p2468_average_projection_positive_definite

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

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2581_looptree_height_bound
-- topology_sha256: b7ec0112d20e1e455666de77441337e930d042a56ef4ed9c1c4be27d8ce7cc77
namespace TopologyCertificate_p2581_looptree_height_bound

-- N001 = hchildren: ∀ v ∈ τ, ∀ (m : ℕ), v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v
-- N002 = hij: i < j
-- N003 = hlex: ∀ (a b : Fin N), a < b ↔ List.Lex (fun x y => x < y) ↑(u a) ↑(u b)
-- N004 = hpre: ↑(u i) <+: ↑(u j)
-- N005 = hprefix: ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ
-- N006 = hroot: [] ∈ τ
-- N007 = hWstep: ∀ (r : Fin N), W r.succ = W r.castSucc + ↑(k ↑(u r)) - 1
-- N008 = hreach: Loop.Reachable (u i) (u j)
-- N009 = hdist: ↑(Loop.dist (u i) (u j)) ≤ W j.castSucc - W i.castSucc + ↑(H j) - ↑(H i)
-- N010 = hcomm: Loop.dist (u j) (u i) = Loop.dist (u i) (u j)
-- N011 = hdist_i: Loop.dist (u i) ⟨[], hroot⟩ = Loop.dist ⟨[], hroot⟩ (u i)
-- N012 = hdist_j: Loop.dist (u j) ⟨[], hroot⟩ = Loop.dist ⟨[], hroot⟩ (u j)
-- N013 = htri_i: Loop.dist (u i) ⟨[], hroot⟩ ≤ Loop.dist (u i) (u j) + Loop.dist (u j) ⟨[], hroot⟩
-- N014 = htri_j: Loop.dist (u j) ⟨[], hroot⟩ ≤ Loop.dist (u j) (u i) + Loop.dist (u i) ⟨[], hroot⟩
-- N015 = htri_iZ: ↑(Loop.dist (u i) ⟨[], hroot⟩) ≤ ↑(Loop.dist (u i) (u j)) + ↑(Loop.dist (u j) ⟨[], hroot⟩)
-- N016 = htri_jZ: ↑(Loop.dist (u j) ⟨[], hroot⟩) ≤ ↑(Loop.dist (u i) (u j)) + ↑(Loop.dist (u i) ⟨[], hroot⟩)
-- N017 = goal: |↑(Hb i) - ↑(Hb j)| ≤ W j.castSucc - W i.castSucc + ↑(H j) - ↑(H i)

-- E001 represents h_001_hreach
-- E002 represents h_002_hdist
-- E003 represents h_005_hcomm
-- E004 represents h_008_hdist_i
-- E005 represents h_009_hdist_j
-- E006 represents h_003_htri_i
-- E007 represents h_004_htri_j
-- E008 represents h_006_htri_iz
-- E009 represents h_007_htri_jz
-- E010 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (B007 : N007)
    (E001 : N005 → N001 → N004 → N008)
    (E002 : N005 → N001 → N003 → N007 → N002 → N004 → N009)
    (E003 : N010)
    (E004 : N006 → N011)
    (E005 : N006 → N012)
    (E006 : N006 → N008 → N013)
    (E007 : N006 → N008 → N014)
    (E008 : N006 → N013 → N015)
    (E009 : N006 → N014 → N010 → N016)
    (E010 : N006 → N009 → N015 → N016 → N011 → N012 → N017)
    : N017 := by
  have H_N008 : N008 := E001 B005 B001 B004
  have H_N009 : N009 := E002 B005 B001 B003 B007 B002 B004
  have H_N010 : N010 := E003
  have H_N011 : N011 := E004 B006
  have H_N012 : N012 := E005 B006
  have H_N013 : N013 := E006 B006 H_N008
  have H_N014 : N014 := E007 B006 H_N008
  have H_N015 : N015 := E008 B006 H_N013
  have H_N016 : N016 := E009 B006 H_N014 H_N010
  have H_N017 : N017 := E010 B006 H_N009 H_N015 H_N016 H_N011 H_N012
  exact H_N017

end TopologyCertificate_p2581_looptree_height_bound

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2604_diagonal_convergence_of_sequences
-- topology_sha256: 0ff276ec76b1c7c532c4ef3a31097c406441d22822053baef5f3bd4ccd2808d6
namespace TopologyCertificate_p2604_diagonal_convergence_of_sequences

-- N001 = ha: ∀ (m : ℕ), Filter.Tendsto (a m) Filter.atTop (nhds (aInf m))
-- N002 = hInf: Filter.Tendsto aInf Filter.atTop (nhds aInfInf)
-- N003 = goal: ∃ b, Monotone b ∧ Filter.Tendsto b Filter.atTop Filter.atTop ∧ Filter.Tendsto (fun n => a (b n) n) Filter.atTop (nhds aInfInf)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (B001 : N001)
    (B002 : N002)
    (E001 : N001 → N002 → N003)
    : N003 := by
  have H_N003 : N003 := E001 B001 B002
  exact H_N003

end TopologyCertificate_p2604_diagonal_convergence_of_sequences

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2625_probability_measure_open_unit_interval_uni
-- topology_sha256: dfdaca984d8be8d649400da403019345f48213505b8a9db6b531bfc4b03b4ea3
namespace TopologyCertificate_p2625_probability_measure_open_unit_interval_uni

-- N001 = inst._@.proofs.1292248354._hygCtx._hyg.13: MeasureTheory.IsProbabilityMeasure μ
-- N002 = hcontIcc: ContinuousOn F (Set.Icc (1 / 4) 1)
-- N003 = hF14: F (1 / 4) < 1
-- N004 = hF1: 1 < F 1
-- N005 = h1mem: 1 ∈ Set.Ioo (F (1 / 4)) (F 1)
-- N006 = himage: 1 ∈ F '' Set.Ioo (1 / 4) 1
-- N007 = goal: ∃ s, 0 < s ∧ s < 1 ∧ ∫ (x : ↑(Set.Ioo 0 1)), (Real.exp (s * (1 - ↑x)) - 1) / (1 - ↑x) ∂μ = 1 ∧ ∀ (t : ℝ), 0 < t → ∫ (x : ↑(Set.Ioo 0 1)), (Real.exp (t * (1 - ↑x)) - 1) / (1 - ↑x) ∂μ = 1 → t = s

-- E001 represents h_001_hconticc
-- E002 represents h_002_hf14
-- E003 represents h_003_hf1
-- E004 represents h_004_h1mem
-- E005 represents h_005_himage
-- E006 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    (E002 : N001 → N003)
    (E003 : N001 → N004)
    (E004 : N003 → N004 → N005)
    (E005 : N002 → N005 → N006)
    (E006 : N001 → N006 → N007)
    : N007 := by
  have H_N002 : N002 := E001 B001
  have H_N003 : N003 := E002 B001
  have H_N004 : N004 := E003 B001
  have H_N005 : N005 := E004 H_N003 H_N004
  have H_N006 : N006 := E005 H_N002 H_N005
  have H_N007 : N007 := E006 B001 H_N006
  exact H_N007

end TopologyCertificate_p2625_probability_measure_open_unit_interval_uni

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2674_graded_dual_rational_map_mem_completion
-- topology_sha256: ee96ffed4839bb111b30a81d1b3d00b895a201f2c741ddc0e91de1722bd55d11
namespace TopologyCertificate_p2674_graded_dual_rational_map_mem_completion

-- N001 = hcleared: ∀ (w' : DirectSum ℂ fun a => Module.Dual ℂ (W a)), ∃ P, (∀ (α : Fin n →₀ ℕ), MvPolynomial.coeff α P = (DirectSum.toModule ℂ ℂ ℂ fun a => (Module.Dual.eval ℂ (W a)) (g α a)) w') ∧ ∀ (z : { z // Function.Injective z }), (∏ i, ∏ j ∈ Finset.Ioi i, (↑z i - ↑z j) ^ p i j) * (f z) w' = (MvPolynomial.eval ↑z) P
-- N002 = hfinite_g: ∀ (a : ℂ), {α | g α a ≠ 0}.Finite
-- N003 = hD: D ≠ 0
-- N004 = hcomponent: ∀ (a : ℂ) (l : Module.Dual ℂ (W a)), (f z) ((DirectSum.lof ℂ ℂ (fun c => Module.Dual ℂ (W c)) a) l) = l (b a)
-- N005 = goal: ∃ b, f z = DirectSum.toModule ℂ ℂ ℂ fun a => (Module.Dual.eval ℂ (W a)) (b a)

-- E001 represents h_001_hfinite_g
-- E002 represents h_002_hd
-- E003 represents h_003_hcomponent
-- E004 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    (E002 : N003)
    (E003 : N001 → N002 → N003 → N004)
    (E004 : N004 → N005)
    : N005 := by
  have H_N002 : N002 := E001 B001
  have H_N003 : N003 := E002
  have H_N004 : N004 := E003 B001 H_N002 H_N003
  have H_N005 : N005 := E004 H_N004
  exact H_N005

end TopologyCertificate_p2674_graded_dual_rational_map_mem_completion

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2692_hodge_operator_on_two_forms
-- topology_sha256: f78a667584570d9c4fb9b59661d293e0d2173c9926ebeb29901dc26023276f9e
namespace TopologyCertificate_p2692_hodge_operator_on_two_forms

-- N001 = h: star e_ab = -e_ab + (2 * μ) • e_bd ∧ star e_ac = e_ac ∧ star e_ad = (1 / (1 + q ^ 2)) • (2 • e_bc - (q ^ 2 * μ) • e_ad) ∧ star e_bc = (q ^ 2 / (1 + q ^ 2)) • (2 • e_ad + μ • e_bc) ∧ star e_bd = e_bd ∧ star e_cd = -e_cd
-- N002 = hq0: q ≠ 0
-- N003 = hq_neg_one: q ^ 2 ≠ -1
-- N004 = goal: star ∘ₗ star = LinearMap.id ∧ (star - LinearMap.id).ker = Submodule.span ℂ {e_bd, e_ac, e_ad + e_bc} ∧ (star + LinearMap.id).ker = Submodule.span ℂ {e_cd, e_ab - μ • e_bd, e_ad - (q ^ 2)⁻¹ • e_bc} ∧ Module.finrank ℂ ↥(star - LinearMap.id).ker = 3 ∧ Module.finrank ℂ ↥(star + LinearMap.id).ker = 3

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N002 → N003 → N001 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B002 B003 B001
  exact H_N004

end TopologyCertificate_p2692_hodge_operator_on_two_forms

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2697_finite_field_normalized_one_cocycle_iff
-- topology_sha256: 4688cecc6caa9aaae7cb3c31292c9b97c22cc81698adb4908adfe5a123c9c151
namespace TopologyCertificate_p2697_finite_field_normalized_one_cocycle_iff

-- N001 = hα: α ≠ 0
-- N002 = hν: orderOf ν = q
-- N003 = inst._@.proofs.2502934680._hygCtx._hyg.11: Fact (Nat.Prime q)
-- N004 = inst._@.proofs.2502934680._hygCtx._hyg.8: Fact (Nat.Prime p)
-- N005 = goal: (α 0 = 0 ∧ ∀ (x y : ZMod q), α (x + y) = α x + (algebraMap (ZMod p) (GaloisField p 2)) ↑ν ^ x.val * α y) ↔ ∃ r, r ≠ 0 ∧ α 0 = 0 ∧ ∀ (x : ZMod q), x ≠ 0 → α x = r * ∑ j ∈ Finset.range x.val, (algebraMap (ZMod p) (GaloisField p 2)) ↑ν ^ j

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N004 → N003 → N002 → N001 → N005)
    : N005 := by
  have H_N005 : N005 := E001 B004 B003 B002 B001
  exact H_N005

end TopologyCertificate_p2697_finite_field_normalized_one_cocycle_iff

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2732_exteriorsquare_surjective_commutatorquotie
-- topology_sha256: 4c76e8035e3fa2c06ceb6be0f2951f8fb779a8602cf5b04a5536a790c7d79b17
namespace TopologyCertificate_p2732_exteriorsquare_surjective_commutatorquotie

-- N001 = hH: commutator G ≤ H
-- N002 = hmap: ∀ (a b : G), f (Multiplicative.ofAdd ((exteriorPower.ιMulti ℤ 2) ![Additive.ofMul ((QuotientGroup.mk' K) a), Additive.ofMul ((QuotientGroup.mk' K) b)])) = (QuotientGroup.mk' D) ⟨⁅a, b⁆, ⋯⟩
-- N003 = goal: ∃ f, Function.Surjective ⇑f ∧ ∀ (a b : G), f (Multiplicative.ofAdd ((exteriorPower.ιMulti ℤ 2) ![Additive.ofMul ((QuotientGroup.mk' K) a), Additive.ofMul ((QuotientGroup.mk' K) b)])) = (QuotientGroup.mk' D) ⟨⁅a, b⁆, ⋯⟩

-- E001 represents h_001_hmap
-- E002 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    (E002 : N001 → N002 → N003)
    : N003 := by
  have H_N002 : N002 := E001 B001
  have H_N003 : N003 := E002 B001 H_N002
  exact H_N003

end TopologyCertificate_p2732_exteriorsquare_surjective_commutatorquotie

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2753_planeposet_union_islinearorder
-- topology_sha256: 3912a60a684387b05d5689bb47a7924195b241da766a67af7244fb7d2a9fd397
namespace TopologyCertificate_p2753_planeposet_union_islinearorder

-- N001 = hcompat: ∀ {x y : P}, x ≠ y → (leH x y ∨ leH y x ↔ ¬(leR x y ∨ leR y x))
-- N002 = hH: IsPartialOrder P leH
-- N003 = hR: IsPartialOrder P leR
-- N004 = goal: IsLinearOrder P fun x y => leH x y ∨ leR x y

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N002 → N003 → N001 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B002 B003 B001
  exact H_N004

end TopologyCertificate_p2753_planeposet_union_islinearorder

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2763_graded_simple_mul_nonzero
-- topology_sha256: 98405581fdf2d54215726224b23b9ab12382ea5a6b9e50d5bcb9beb5d4539aa7
namespace TopologyCertificate_p2763_graded_simple_mul_nonzero

-- N001 = h_direct: iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤
-- N002 = h_mul: ∀ {g h : G} {x y : A}, x ∈ 𝒜 g → y ∈ 𝒜 h → x * y ∈ 𝒜 (g * h)
-- N003 = h_nonzero_mul: ∃ x y, x * y ≠ 0
-- N004 = h_simple: ∀ (I : Submodule K A), (∀ (r : A) {x : A}, x ∈ I → r * x ∈ I) → (∀ (r : A) {x : A}, x ∈ I → x * r ∈ I) → ⨆ g, 𝒜 g ⊓ I = I → I = ⊥ ∨ I = ⊤
-- N005 = ha0: a ≠ 0
-- N006 = ha: a ∈ 𝒜 g
-- N007 = hb0: b ≠ 0
-- N008 = inst._@.proofs.1850184048._hygCtx._hyg.18: IsScalarTower K A A
-- N009 = inst._@.proofs.1850184048._hygCtx._hyg.23: SMulCommClass K A A
-- N010 = goal: ∃ k, ∃ x ∈ 𝒜 k, a * x * b ≠ 0

-- E001 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (B007 : N007)
    (B008 : N008)
    (B009 : N009)
    (E001 : N008 → N009 → N001 → N002 → N003 → N004 → N006 → N005 → N007 → N010)
    : N010 := by
  have H_N010 : N010 := E001 B008 B009 B001 B002 B003 B004 B006 B005 B007
  exact H_N010

end TopologyCertificate_p2763_graded_simple_mul_nonzero

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2771_pbw_filtered_quadratic_relations_unique
-- topology_sha256: 777fa7833f8e565a5d771438cc1a0f128e4aa716361332d85c3e8108d8326c4c
namespace TopologyCertificate_p2771_pbw_filtered_quadratic_relations_unique

-- N001 = hP₂: P ⊆ ⨆ i, ↑(𝒯 ↑i)
-- N002 = hPI: TwoSidedIdeal.span P = I
-- N003 = hPpbw: ∀ (n : ℕ), ∀ x ∈ 𝒯 n, x ∈ TwoSidedIdeal.span (⇑(GradedAlgebra.proj 𝒯 2) '' P) ↔ ∃ y ∈ I, x - y ∈ ⨆ i, 𝒯 ↑i
-- N004 = hQ₂: Q ⊆ ⨆ i, ↑(𝒯 ↑i)
-- N005 = hQI: TwoSidedIdeal.span Q = I
-- N006 = hQpbw: ∀ (n : ℕ), ∀ x ∈ 𝒯 n, x ∈ TwoSidedIdeal.span (⇑(GradedAlgebra.proj 𝒯 2) '' Q) ↔ ∃ y ∈ I, x - y ∈ ⨆ i, 𝒯 ↑i
-- N007 = hPsub: P ⊆ ↑B
-- N008 = hQsub: Q ⊆ ↑A
-- N009 = hAleB: A ≤ B
-- N010 = hBleA: B ≤ A
-- N011 = hAB: A = B
-- N012 = goal: AddSubgroup.closure {x | ∃ a ∈ 𝒯 0, ∃ p ∈ P, ∃ b ∈ 𝒯 0, x = a * p * b} = AddSubgroup.closure {x | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b} ∧ (((∃ M, ↑M = P ∧ (∀ (a : ↥(𝒯 0)), ∀ x ∈ M, ↑a * x ∈ M) ∧ ∀ (a : ↥(𝒯 0)), ∀ x ∈ M, x * ↑a ∈ M) ∧ ∃ N, ↑N = Q ∧ (∀ (a : ↥(𝒯 0)), ∀ x ∈ N, ↑a * x ∈ N) ∧ ∀ (a : ↥(𝒯 0)), ∀ x ∈ N, x * ↑a ∈ N) → P = Q)

-- E001 represents h_001_hpsub
-- E002 represents h_002_hqsub
-- E003 represents h_003_haleb
-- E004 represents h_004_hblea
-- E005 represents h_005_hab
-- E006 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (E001 : N001 → N004 → N002 → N005 → N003 → N006 → N007)
    (E002 : N001 → N004 → N002 → N005 → N003 → N006 → N008)
    (E003 : N007 → N009)
    (E004 : N008 → N010)
    (E005 : N009 → N010 → N011)
    (E006 : N011 → N012)
    : N012 := by
  have H_N007 : N007 := E001 B001 B004 B002 B005 B003 B006
  have H_N008 : N008 := E002 B001 B004 B002 B005 B003 B006
  have H_N009 : N009 := E003 H_N007
  have H_N010 : N010 := E004 H_N008
  have H_N011 : N011 := E005 H_N009 H_N010
  have H_N012 : N012 := E006 H_N011
  exact H_N012

end TopologyCertificate_p2771_pbw_filtered_quadratic_relations_unique

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2823_two_local_inner_derivation_matrix_is_inner
-- topology_sha256: 1b9699c61657e610aa8a7c31dc7526a9ba513097385778c64a2cc219bdef2544
namespace TopologyCertificate_p2823_two_local_inner_derivation_matrix_is_inner

-- N001 = hΔ: ∀ (X Y : Matrix (Fin n) (Fin n) R), ∃ A, Δ X = A * X - X * A ∧ Δ Y = A * Y - Y * A
-- N002 = goal: ∃ B, ∀ (X : Matrix (Fin n) (Fin n) R), Δ X = B * X - X * B

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    : N002 := by
  have H_N002 : N002 := E001 B001
  exact H_N002

end TopologyCertificate_p2823_two_local_inner_derivation_matrix_is_inner

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2889_newton_sum_identity
-- topology_sha256: 86a1e5f723ab4767e2f23767e35423d77febdd24a773f42fe5a06af671650480
namespace TopologyCertificate_p2889_newton_sum_identity

-- N001 = hξ: Set.InjOn ξ (Set.Icc 0 d)
-- N002 = goal: ∑ i ∈ Finset.range (d + 1), (∏ j ∈ Finset.range i, (Polynomial.X - Polynomial.C (ξ j))) * Polynomial.C (∏ j ∈ Finset.Icc 1 i, (ξ 0 - ξ j))⁻¹ = (∏ j ∈ Finset.Icc 1 d, (Polynomial.X - Polynomial.C (ξ j))) * Polynomial.C (∏ j ∈ Finset.Icc 1 d, (ξ 0 - ξ j))⁻¹

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    : N002 := by
  have H_N002 : N002 := E001 B001
  exact H_N002

end TopologyCertificate_p2889_newton_sum_identity

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2920_proposition_3_8
-- topology_sha256: 072a6258b8a4599f09053e96ae1c5d3b4f28aeefb6ed9495f914f7e8c63fff72
namespace TopologyCertificate_p2920_proposition_3_8

-- N001 = goal: let κ := fun x ρ => if ρ.parts.Nodup then (-Polynomial.X) ^ ρ.parts.toFinset.card else 0; let ε := fun a => ∑ s, if h : ∑ i, ↑(s i) = a then ∑ p, ∏ i, κ (↑(s i)) (p i) else 0; let pp := fun a => ∑ s, if h : ∑ i, ↑(s i) = a then ∑ ρ, (1 - Polynomial.X) ^ ∑ i, (ρ i).parts.toFinset.card else 0; let ε₁ := fun a => Polynomial.eval 1 (ε a); ε k = ∑ r ∈ Finset.range (k + 1), Polynomial.C (ε₁ r) * pp (k - r)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p2920_proposition_3_8

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2937_coinvariants_addmonoidalgebra_eq_range
-- topology_sha256: efb7339bd7ad37f7add4d6ffea20ff5f7f3340ddaf8769ccd6fecd3d777912c5
namespace TopologyCertificate_p2937_coinvariants_addmonoidalgebra_eq_range

-- N001 = hφ: Function.Injective ⇑φ
-- N002 = hc: ∀ (m : ↥S), c (AddMonoidAlgebra.single m 1) = AddMonoidAlgebra.single (ψ ↑m) 1 ⊗ₜ[R] AddMonoidAlgebra.single m 1
-- N003 = hexact: Function.Exact ⇑φ ⇑ψ
-- N004 = goal: AlgHom.equalizer c Algebra.TensorProduct.includeRight = (AddMonoidAlgebra.mapDomainAlgHom R R (φ.addSubmonoidComap S)).range

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N001 → N003 → N002 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B001 B003 B002
  exact H_N004

end TopologyCertificate_p2937_coinvariants_addmonoidalgebra_eq_range

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p3013_finite_compatible_shrinking_lemma
-- topology_sha256: 8b9aca9fc832e636b74f6b231361ef29e13d563e12637c3874475ffa894fc31d
namespace TopologyCertificate_p3013_finite_compatible_shrinking_lemma

-- N001 = hO: IsOpen O
-- N002 = hW: ∀ (K : Set (Fin N)), K.Nonempty → IsOpen (W K) ∧ W K ⊆ O ∧ W K ∩ Z = ⋂ i ∈ K, Zi i
-- N003 = hZclosed: IsClosed (Subtype.val ⁻¹' Z)
-- N004 = hZi_open: ∀ (i : Fin N), IsOpen (Subtype.val ⁻¹' Zi i)
-- N005 = hZi_subset: ∀ (i : Fin N), Zi i ⊆ Z
-- N006 = hZO: Z ⊆ O
-- N007 = goal: ∃ U, (∀ (K : Set (Fin N)), K.Nonempty → IsOpen (U K) ∧ U K ⊆ W K ∧ U K ∩ Z = ⋂ i ∈ K, Zi i) ∧ ∀ (J K : Set (Fin N)), J.Nonempty → K.Nonempty → U J ∩ U K = U (J ∪ K)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (E001 : N001 → N006 → N003 → N005 → N004 → N002 → N007)
    : N007 := by
  have H_N007 : N007 := E001 B001 B006 B003 B005 B004 B002
  exact H_N007

end TopologyCertificate_p3013_finite_compatible_shrinking_lemma

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p3019_laurent_circulant_kernel
-- topology_sha256: 63d6015b119f90a9baba38749e4205742c89b29c8136c262b83a135dc804b604
namespace TopologyCertificate_p3019_laurent_circulant_kernel

-- N001 = ha: 0 < a
-- N002 = hab: a < b
-- N003 = hab_coprime: a.Coprime b
-- N004 = hv: B.mulVec v = 0
-- N005 = hNe: NeZero (a + b)
-- N006 = hcop: a.Coprime (a + b)
-- N007 = hv': (Rollout_p3019_laurent_circulant_kernel.laurentCirculantB a b ε).mulVec v = 0
-- N008 = ht: t ^ (a + b) ≠ (-1) ^ (a + b)
-- N009 = hrec: ∀ (r : ZMod (a + b)), x r + t * x (r + 1) = 0
-- N010 = hx: ∀ (r : ZMod (a + b)), x r = 0
-- N011 = hwinv: ∀ (r : ZMod (a + b)), w r = w (r - ↑a)
-- N012 = hweq: ∀ (i j : ZMod (a + b)), w i = w j
-- N013 = hvinv: ∀ (r : ZMod (a + b)), v r = v (r - ↑a)
-- N014 = goal: v i = v j

-- E001 represents h_001_hne
-- E002 represents h_006_hcop
-- E003 represents h_002_hv
-- E004 represents h_004_ht
-- E005 represents h_003_hrec
-- E006 represents h_005_hx
-- E007 represents h_007_hwinv
-- E008 represents h_008_hweq
-- E009 represents h_009_hvinv
-- E010 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N001 → N005)
    (E002 : N003 → N006)
    (E003 : N005 → N004 → N007)
    (E004 : N005 → N008)
    (E005 : N001 → N002 → N005 → N007 → N009)
    (E006 : N005 → N009 → N008 → N010)
    (E007 : N010 → N011)
    (E008 : N005 → N006 → N011 → N012)
    (E009 : N001 → N005 → N012 → N013)
    (E010 : N005 → N006 → N013 → N014)
    : N014 := by
  have H_N005 : N005 := E001 B001
  have H_N006 : N006 := E002 B003
  have H_N007 : N007 := E003 H_N005 B004
  have H_N008 : N008 := E004 H_N005
  have H_N009 : N009 := E005 B001 B002 H_N005 H_N007
  have H_N010 : N010 := E006 H_N005 H_N009 H_N008
  have H_N011 : N011 := E007 H_N010
  have H_N012 : N012 := E008 H_N005 H_N006 H_N011
  have H_N013 : N013 := E009 B001 H_N005 H_N012
  have H_N014 : N014 := E010 H_N005 H_N006 H_N013
  exact H_N014

end TopologyCertificate_p3019_laurent_circulant_kernel

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p3094_finite_multiplicative_ratio_sums
-- topology_sha256: 0f727dd412e7486054192c1914622fb71cd63ecb637578f20f992a8d2ee24e80
namespace TopologyCertificate_p3094_finite_multiplicative_ratio_sums

-- N001 = hr_mul: ∀ (e d b : I), r (e, d) = r (e, b) * r (b, d)
-- N002 = hr_pos: ∀ (e d : I), 0 < r (e, d)
-- N003 = inst._@.proofs.1328577087._hygCtx._hyg.6: Nonempty I
-- N004 = hdiag: ∀ (e : I), r (e, e) = 1
-- N005 = hsum_pos: ∀ (e : I), 0 < ∑ d, r (d, e)
-- N006 = hinv: ∀ (e d : I), (r (e, d))⁻¹ = r (d, e)
-- N007 = hsum_ne: ∀ (e : I), ∑ d, r (d, e) ≠ 0
-- N008 = hA: ∑ e, (∑ d, r (d, e))⁻¹ = 1
-- N009 = hB: (∑ e, r (b, e)) / ∑ d, (r (d, b))⁻¹ = 1
-- N010 = hC: (∑ e, r (e, b)) / ∑ d, r (d, b) = 1
-- N011 = goal: ∑ e, (∑ d, r (d, e))⁻¹ = (∑ e, r (b, e)) / ∑ d, (r (d, b))⁻¹ ∧ (∑ e, r (b, e)) / ∑ d, (r (d, b))⁻¹ = (∑ e, r (e, b)) / ∑ d, r (d, b) ∧ (∑ e, r (e, b)) / ∑ d, r (d, b) = 1

-- E001 represents h_001_hdiag
-- E002 represents h_003_hsum_pos
-- E003 represents h_002_hinv
-- E004 represents h_004_hsum_ne
-- E005 represents h_005_ha
-- E006 represents h_006_hb
-- E007 represents h_007_hc
-- E008 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N002 → N001 → N004)
    (E002 : N003 → N002 → N005)
    (E003 : N001 → N004 → N006)
    (E004 : N005 → N007)
    (E005 : N001 → N006 → N007 → N008)
    (E006 : N003 → N002 → N006 → N009)
    (E007 : N007 → N010)
    (E008 : N008 → N009 → N010 → N011)
    : N011 := by
  have H_N004 : N004 := E001 B002 B001
  have H_N005 : N005 := E002 B003 B002
  have H_N006 : N006 := E003 B001 H_N004
  have H_N007 : N007 := E004 H_N005
  have H_N008 : N008 := E005 B001 H_N006 H_N007
  have H_N009 : N009 := E006 B003 B002 H_N006
  have H_N010 : N010 := E007 H_N007
  have H_N011 : N011 := E008 H_N008 H_N009 H_N010
  exact H_N011

end TopologyCertificate_p3094_finite_multiplicative_ratio_sums

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p3112_connected_nodal_domain_of_leading_eigenvec
-- topology_sha256: c39b7c8c6116dc2fd9aec5c5f12c8be8cfbb66665a78d6ee1e6b4f19fc34ca34
namespace TopologyCertificate_p3112_connected_nodal_domain_of_leading_eigenvec

-- N001 = hσ: 0 < σ
-- N002 = hA_nonneg: ∀ (i j : Fin n), 0 ≤ A i j
-- N003 = hA_symm: A.IsSymm
-- N004 = hG_conn: (SimpleGraph.fromRel fun i j => 0 < A i j).Connected
-- N005 = hl_largest: ∀ (μ : ℝ), (∃ u, u ≠ 0 ∧ (A + W).mulVec u = μ • u) → μ ≤ l
-- N006 = hm_largest: ∀ (μ : ℝ), (∃ u, u ≠ 0 ∧ (A + W - σ • Matrix.vecMulVec v v).mulVec u = μ • u) → μ ≤ m
-- N007 = hn: 1 ≤ n
-- N008 = hv_nonneg: ∀ (i : Fin n), 0 ≤ v i
-- N009 = hv_nonzero: v ≠ 0
-- N010 = hW_diag: W.IsDiag
-- N011 = hx_eigen: (A + W - σ • Matrix.vecMulVec v v).mulVec x = m • x
-- N012 = hx_nonzero: x ≠ 0
-- N013 = hx_sign: 0 ≤ v ⬝ᵥ x
-- N014 = hy_eigen: (A + W).mulVec y = l • y
-- N015 = hy_pos: ∀ (i : Fin n), 0 < y i
-- N016 = hB_symm: B.IsSymm
-- N017 = hnormx: 0 < x ⬝ᵥ x
-- N018 = hMx: M.mulVec x = B.mulVec x - (σ * d) • v
-- N019 = hBx: B.mulVec x = m • x + (σ * d) • v
-- N020 = hBupper: x ⬝ᵥ B.mulVec x ≤ l * x ⬝ᵥ x
-- N021 = hqBx: x ⬝ᵥ B.mulVec x = m * x ⬝ᵥ x + σ * d ^ 2
-- N022 = hml: m ≤ l
-- N023 = goal: ∀ (ε : ℝ), 0 ≤ ε → (SimpleGraph.induce {i | 0 ≤ x i + ε * y i} (SimpleGraph.fromRel fun i j => 0 < A i j)).Connected

-- E001 represents h_002_hb_symm
-- E002 represents h_004_hnormx
-- E003 represents h_005_hmx
-- E004 represents h_006_hbx
-- E005 represents h_008_hbupper
-- E006 represents h_007_hqbx
-- E007 represents h_009_hml
-- E008 represents h_goal

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
    (B011 : N011)
    (B012 : N012)
    (B013 : N013)
    (B014 : N014)
    (B015 : N015)
    (E001 : N003 → N010 → N016)
    (E002 : N012 → N017)
    (E003 : N018)
    (E004 : N011 → N018 → N019)
    (E005 : N005 → N016 → N020)
    (E006 : N019 → N021)
    (E007 : N001 → N017 → N021 → N020 → N022)
    (E008 : N007 → N003 → N002 → N004 → N010 → N009 → N008 → N001 → N012 → N011 → N006 → N013 → N015 → N014 → N005 → N016 → N019 → N021 → N020 → N022 → N023)
    : N023 := by
  have H_N016 : N016 := E001 B003 B010
  have H_N017 : N017 := E002 B012
  have H_N018 : N018 := E003
  have H_N019 : N019 := E004 B011 H_N018
  have H_N020 : N020 := E005 B005 H_N016
  have H_N021 : N021 := E006 H_N019
  have H_N022 : N022 := E007 B001 H_N017 H_N021 H_N020
  have H_N023 : N023 := E008 B007 B003 B002 B004 B010 B009 B008 B001 B012 B011 B006 B013 B015 B014 B005 H_N016 H_N019 H_N021 H_N020 H_N022
  exact H_N023

end TopologyCertificate_p3112_connected_nodal_domain_of_leading_eigenvec

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p3114_dimension_three_evaluation_of_asymptotic_c
-- topology_sha256: f3ac9afe8a0768f21a7fcd2874352f2bb2ead0abe5b84fdd5a46b71d0f19fc12
namespace TopologyCertificate_p3114_dimension_three_evaluation_of_asymptotic_c

-- N001 = goal: let H := fun a => if a < 0 then 0 else if a = 0 then 1 / 2 else 1; let arccot := fun a => Real.pi / 2 - Real.arctan a; let κ := fun a => 1 / (4 * Real.pi) * ((-(1 / (2 * Real.pi)) * ∫ (η : ℝ) in -1..1, if a = 0 ∧ η = 0 then 0 else (1 - η ^ 2) * a / (a ^ 2 + η ^ 2)) - 1 / 4 + H a * (1 + a ^ 2)); ∀ (a : ℝ), κ a = 1 / (4 * Real.pi) * (-1 / 4 - (1 + a ^ 2) * arccot a / Real.pi + (1 + a ^ 2) + a / Real.pi)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p3114_dimension_three_evaluation_of_asymptotic_c

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p3184_levykhintchine_increment_bound
-- topology_sha256: 23545fecef4f1ff04645c5d928169ac23e01358909956c9b1a0cd1de6e02c090
namespace TopologyCertificate_p3184_levykhintchine_increment_bound

-- N001 = hσ2: 0 ≤ σ2
-- N002 = hΔ: 0 ≤ Δ
-- N003 = hn2: MeasureTheory.Integrable (fun x => x ^ 2 * ↑(n x)) MeasureTheory.volume
-- N004 = goal: (∀ (u : ℝ), ‖(fun u => Complex.exp (↑Δ * (Complex.I * ↑u * ↑b - ↑σ2 * ↑u ^ 2 / 2 + ∫ (x : ℝ), (Complex.exp (Complex.I * ↑u * ↑x) - 1 - Complex.I * ↑u * ↑x) * ↑↑(n x)))) u - 1‖ ≤ Δ * |u| * ((fun u => |b| + ∫ (v : ℝ) in Set.Icc (min 0 u) (max 0 u), ‖(fun v => ∫ (x : ℝ), Complex.exp (Complex.I * ↑v * ↑x) * (fun x => ↑(x ^ 2 * ↑(n x))) x) v‖) u + σ2 * |u|)) ∧ (MeasureTheory.Integrable (fun v => ∫ (x : ℝ), Complex.exp (Complex.I * ↑v * ↑x) * (fun x => ↑(x ^ 2 * ↑(n x))) x) MeasureTheory.volume → ∀ (u : ℝ), ‖(fun u => Complex.exp (↑Δ * (Complex.I * ↑u * ↑b - ↑σ2 * ↑u ^ 2 / 2 + ∫ (x : ℝ), (Complex.exp (Complex.I * ↑u * ↑x) - 1 - Complex.I * ↑u * ↑x) * ↑↑(n x)))) u - 1‖ ≤ Δ * |u| * ((|b| + ∫ (v : ℝ), ‖(fun v => ∫ (x : ℝ), Complex.exp (Complex.I * ↑v * ↑x) * (fun x => ↑(x ^ 2 * ↑(n x))) x) v‖) + σ2 * |u|))

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N001 → N002 → N003 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B001 B002 B003
  exact H_N004

end TopologyCertificate_p3184_levykhintchine_increment_bound

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

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p3255_horseshoelikepenalty_strictconcave
-- topology_sha256: 35d8c5ea9a37d2b8ec8b339d43d5d2f09b426f320a12ddbb467aa4c09e83f31b
namespace TopologyCertificate_p3255_horseshoelikepenalty_strictconcave

-- N001 = ha: 0 < a
-- N002 = goal: let pen_a := fun x => -Real.log (Real.log (1 + a / x ^ 2)); ∀ (x y t : ℝ), x ≠ y → 0 < x ∧ 0 < y ∨ x < 0 ∧ y < 0 → 0 < t → t < 1 → pen_a (t * x + (1 - t) * y) > t * pen_a x + (1 - t) * pen_a y

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    : N002 := by
  have H_N002 : N002 := E001 B001
  exact H_N002

end TopologyCertificate_p3255_horseshoelikepenalty_strictconcave
