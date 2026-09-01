import Init

/- Generated batch: one abstract topology theorem per selected graph. -/

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0381_two_minimal_missing_faces_deletion
-- topology_sha256: 05d1d90c7d2ac7843a9bc9fde3759270e612281999887e2da50afe8bd3dbe0bf
namespace TopologyCertificate_p0381_two_minimal_missing_faces_deletion

-- N001 = hmissing: ∀ (S : Set ℕ), Minimal (fun T => T ⊆ Set.Icc 1 m ∧ T ∉ K) S ↔ S = I ∨ S = J
-- N002 = hS: S ⊆ Set.Icc 1 m \ {w}
-- N003 = hw: w ∈ I ∩ J
-- N004 = goal: S ∈ K

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

end TopologyCertificate_p0381_two_minimal_missing_faces_deletion

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0390_linfty_eq_erosion_distance
-- topology_sha256: 7169e0ab7d33b8a0fb0a4a39cd644007ca5765397d525bbf754de2f861f69f8d
namespace TopologyCertificate_p0390_linfty_eq_erosion_distance

-- N001 = goal: ⨆ x, ENNReal.ofReal |f x - g x| = sInf {d | ∃ ε, d = ↑ε ∧ ∀ (a b : ℝ), a < b → g ⁻¹' Set.Icc a b ⊆ f ⁻¹' Set.Icc (a - ↑ε) (b + ↑ε) ∧ f ⁻¹' Set.Icc a b ⊆ g ⁻¹' Set.Icc (a - ↑ε) (b + ↑ε)}

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p0390_linfty_eq_erosion_distance

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0411_finite_product_grid_cell_properties
-- topology_sha256: 0432853c1183bcd36cea3e1bb024047f35166319b34df2e909ba2c44786a23f2
namespace TopologyCertificate_p0411_finite_product_grid_cell_properties

-- N001 = goal: let P := (i : Fin n) → T i; let grid := {q | ∀ (i : Fin n), q i ∈ Q i}; let upper := {x | ∃ q ∈ grid, q ≤ x}; let cell := fun y => {x | x ∈ upper ∧ ∀ (i : Fin n), IsGreatest {a | a ∈ Q i ∧ a ≤ x i} (y i)}; (∀ ⦃x y y' : P⦄, x ∈ cell y → y' ∈ grid → y ≤ y' → y' ⊔ x ∈ cell y' ∧ ∃ x' ∈ cell y', x ≤ x') ∧ ∀ y ∈ grid, IsSublattice (cell y)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p0411_finite_product_grid_cell_properties

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0770_two_bilinear_products_associative_iff
-- topology_sha256: 03737d53c077ded934bac5dc575473f2664b4ae966ca594aa2a3036fff53279b
namespace TopologyCertificate_p0770_two_bilinear_products_associative_iff

-- N001 = goal: let dot := fun x x_1 => match x with | (a, b) => match x_1 with | (c, d) => ((mul₁ a) c + (mul₂ a) d, (mul₂ b) d + (mul₁ b) c); let diamond := fun x x_1 => match x with | (a, b) => match x_1 with | (c, d) => ((mul₁ a) c + (mul₂ b) c, (mul₂ b) d + (mul₁ a) d); let compatibility := (Std.Associative fun x y => (mul₁ x) y) ∧ (Std.Associative fun x y => (mul₂ x) y) ∧ (∀ (x y z : A), (mul₂ ((mul₁ x) y)) z = (mul₁ x) ((mul₂ y) z)) ∧ ∀ (x y z : A), (mul₁ ((mul₂ x) y)) z = (mul₂ x) ((mul₁ y) z); (compatibility ↔ Std.Associative dot) ∧ (Std.Associative dot ↔ Std.Associative diamond)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p0770_two_bilinear_products_associative_iff

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0818_intertwining_orbit_cocycle
-- topology_sha256: 7c24cee0092f3df02efea7f89fb4a675db6848999deb567605152a521cf9f3f3
namespace TopologyCertificate_p0818_intertwining_orbit_cocycle

-- N001 = hc₂: ∀ (g : Γ) (i : Fin n), c g 1 i = 1
-- N002 = hc'₁: ∀ (g : Γ) (i' : Fin n'), c' 1 g i' = 1
-- N003 = hc'₂: ∀ (g : Γ) (i' : Fin n'), c' g 1 i' = 1
-- N004 = hc₁: ∀ (g : Γ) (i : Fin n), c 1 g i = 1
-- N005 = hcob': ∀ (g h k : Γ) (i' : Fin n'), c' h k ((ρ' g)⁻¹ i') * (c' (g * h) k i')⁻¹ * c' g (h * k) i' * (c' g h i')⁻¹ = Additive.toMul (β' (α g h k) i')
-- N006 = hcob: ∀ (g h k : Γ) (i : Fin n), c h k ((ρ g)⁻¹ i) * (c (g * h) k i)⁻¹ * c g (h * k) i * (c g h i)⁻¹ = Additive.toMul (β (α g h k) i)
-- N007 = hintertwine: ∀ p ∈ O, ∀ (u : A), β' u p.1 = β u p.2
-- N008 = goal: let z := fun g h p => c' g h (↑p).1 * (c g h (↑p).2)⁻¹; (∀ (g : Γ) (p : ↑O), z 1 g p = 1 ∧ z g 1 p = 1) ∧ (∀ (g h k : Γ) (p : ↑O), c' h k ((ρ' g)⁻¹ (↑p).1) * (c h k ((ρ g)⁻¹ (↑p).2))⁻¹ * (z (g * h) k p)⁻¹ * z g (h * k) p * (z g h p)⁻¹ = 1) ∧ ∀ (x : Γ → Fin n → ℂˣ) (x' : Γ → Fin n' → ℂˣ), (∀ (i : Fin n), x 1 i = 1) → (∀ (i' : Fin n'), x' 1 i' = 1) → let δx := fun g h i => x h ((ρ g)⁻¹ i) * (x (g * h) i)⁻¹ * x g i; let δx' := fun g h i' => x' h ((ρ' g)⁻¹ i') * (x' (g * h) i')⁻¹ * x' g i'; let y := fun g p => x' g (↑p).1 * (x g (↑p).2)⁻¹; ∀ (g h : Γ) (p : ↑O), c' g h (↑p).1 * δx' g h (↑p).1 * (c g h (↑p).2 * δx g h (↑p).2)⁻¹ = z g h p * (x' h ((ρ' g)⁻¹ (↑p).1) * (x h ((ρ g)⁻¹ (↑p).2))⁻¹ * (y (g * h) p)⁻¹ * y g p)

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
    (E001 : N004 → N001 → N002 → N003 → N006 → N005 → N007 → N008)
    : N008 := by
  have H_N008 : N008 := E001 B004 B001 B002 B003 B006 B005 B007
  exact H_N008

end TopologyCertificate_p0818_intertwining_orbit_cocycle

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0925_tanh_ge_one_sub_exp_neg
-- topology_sha256: c31c7ef38ac30d758d597727d77d1f890e731380163812056eec74da2d1acdf6
namespace TopologyCertificate_p0925_tanh_ge_one_sub_exp_neg

-- N001 = hx: 0 ≤ x
-- N002 = goal: Real.tanh x ≥ 1 - Real.exp (-x)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    : N002 := by
  have H_N002 : N002 := E001 B001
  exact H_N002

end TopologyCertificate_p0925_tanh_ge_one_sub_exp_neg

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0960_antitone_monotone_power_sum_inequality
-- topology_sha256: e4cd917d0aebd07d32c97b0a51e0e5210516236764cf68793d96a95ef4c7844f
namespace TopologyCertificate_p0960_antitone_monotone_power_sum_inequality

-- N001 = ha: ∀ (i : Fin k), 0 ≤ a i
-- N002 = ha_antitone: Antitone a
-- N003 = hb: ∀ (i : Fin k), 0 ≤ b i
-- N004 = hb_monotone: Monotone b
-- N005 = hs: 1 ≤ s
-- N006 = hWnonneg: ∀ (i j : Fin k), 0 ≤ W i j
-- N007 = hU: ∑ i, ∑ j, U i j = C * D
-- N008 = hV: ∑ i, ∑ j, V i j = A * B
-- N009 = hsumW: 0 ≤ ∑ i, ∑ j, W i j
-- N010 = hUs: ∑ i, ∑ j, U j i = C * D
-- N011 = hVs: ∑ i, ∑ j, V j i = A * B
-- N012 = hsumEq: ∑ i, ∑ j, W i j = 2 * (C * D - A * B)
-- N013 = hdiff: 0 ≤ C * D - A * B
-- N014 = hle: A * B ≤ C * D
-- N015 = goal: (∑ i, (a i).rpow s) * ∑ i, a i ^ 2 * b i ≤ (∑ i, (a i).rpow (s + 1)) * ∑ i, a i * b i

-- E001 represents h_001_hwnonneg
-- E002 represents h_003_hu
-- E003 represents h_005_hv
-- E004 represents h_002_hsumw
-- E005 represents h_004_hus
-- E006 represents h_006_hvs
-- E007 represents h_007_hsumeq
-- E008 represents h_008_hdiff
-- E009 represents h_009_hle
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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (E001 : N005 → N001 → N003 → N002 → N004 → N006)
    (E002 : N007)
    (E003 : N008)
    (E004 : N006 → N009)
    (E005 : N007 → N010)
    (E006 : N008 → N011)
    (E007 : N007 → N010 → N008 → N011 → N012)
    (E008 : N009 → N012 → N013)
    (E009 : N013 → N014)
    (E010 : N014 → N015)
    : N015 := by
  have H_N006 : N006 := E001 B005 B001 B003 B002 B004
  have H_N007 : N007 := E002
  have H_N008 : N008 := E003
  have H_N009 : N009 := E004 H_N006
  have H_N010 : N010 := E005 H_N007
  have H_N011 : N011 := E006 H_N008
  have H_N012 : N012 := E007 H_N007 H_N010 H_N008 H_N011
  have H_N013 : N013 := E008 H_N009 H_N012
  have H_N014 : N014 := E009 H_N013
  have H_N015 : N015 := E010 H_N014
  exact H_N015

end TopologyCertificate_p0960_antitone_monotone_power_sum_inequality

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1242_finite_support_derivation
-- topology_sha256: bc281170dffb87d8109f2c024ade7a9d553845452e30202f67d3936dd79f381c
namespace TopologyCertificate_p1242_finite_support_derivation

-- N001 = hD: ∀ (S : Set W) (x : W), x ∈ D S ↔ ∃ F, F.Finite ∧ F ⊆ S ∧ x ∈ D F
-- N002 = hn: 1 ≤ n
-- N003 = hP: P ∈ D^[n] A
-- N004 = hsub: {P} ⊆ D^[n] A
-- N005 = goal: ∃ S, (∀ k < n, (S k).Finite) ∧ (∀ k < n, S k ⊆ D^[k] A) ∧ P ∈ D (S (n - 1)) ∧ ∀ (k : ℕ), k + 1 < n → S (k + 1) ⊆ D (S k)

-- E001 represents h_001_hsub
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
    (E002 : N001 → N002 → N004 → N005)
    : N005 := by
  have H_N004 : N004 := E001 B003
  have H_N005 : N005 := E002 B001 B002 H_N004
  exact H_N005

end TopologyCertificate_p1242_finite_support_derivation

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1318_sequence_triangular_formula
-- topology_sha256: e12f68c590d052a3252704376bcc8420bd334abba0895d8d9e6f14d69b56ebc6
namespace TopologyCertificate_p1318_sequence_triangular_formula

-- N001 = hc₁: c 1 = 2
-- N002 = hc: ∀ (k : ℕ), 0 < k → c (2 * k) = 2 * (k + 1) ^ 2 ∧ c (2 * k + 1) = 2 * (k + 1) ^ 2
-- N003 = hn: 0 < n
-- N004 = goal: let m := (n + 2) / 2; let t := fun r => r * (r + 1) / 2; c n = 2 * m ^ 2 ∧ 2 * m ^ 2 = 2 * (t (m - 1) + t m)

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

end TopologyCertificate_p1318_sequence_triangular_formula

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
-- graph_id: p1489_slope_composition_equivalent
-- topology_sha256: 7a474cd4744979179ba1711124439a6e82dead9ccc91bf25655d868fb3d61174
namespace TopologyCertificate_p1489_slope_composition_equivalent

-- N001 = hββ': (Set.range fun n => β n - β' n).Finite
-- N002 = hα': (Set.range fun p => α' (p.1 + p.2) - α' p.1 - α' p.2).Finite
-- N003 = hβ': (Set.range fun p => β' (p.1 + p.2) - β' p.1 - β' p.2).Finite
-- N004 = hα: (Set.range fun p => α (p.1 + p.2) - α p.1 - α p.2).Finite
-- N005 = hβ: (Set.range fun p => β (p.1 + p.2) - β p.1 - β p.2).Finite
-- N006 = hαα': (Set.range fun n => α n - α' n).Finite
-- N007 = goal: (Set.range fun p => α (β (p.1 + p.2)) - α (β p.1) - α (β p.2)).Finite ∧ (Set.range fun p => α' (β' (p.1 + p.2)) - α' (β' p.1) - α' (β' p.2)).Finite ∧ (Set.range fun n => α (β n) - α' (β' n)).Finite

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
    (E001 : N004 → N002 → N005 → N003 → N006 → N001 → N007)
    : N007 := by
  have H_N007 : N007 := E001 B004 B002 B005 B003 B006 B001
  exact H_N007

end TopologyCertificate_p1489_slope_composition_equivalent

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1572_not_biorderable_of_product_conjugates_eq_o
-- topology_sha256: 5ada9e25b8527e7bb3ae0d80bab4d4a3d543f5311c77d5c36a9536ad537bc67f
namespace TopologyCertificate_p1572_not_biorderable_of_product_conjugates_eq_o

-- N001 = a._@._internal.0.proofs.1064056188._hygCtx._hyg.161: ∃ r, IsStrictTotalOrder G r ∧ (∀ (a b c : G), r a b ↔ r (c * a) (c * b)) ∧ ∀ (a b c : G), r a b ↔ r (a * c) (b * c)
-- N002 = h: ∃ g k x, g ≠ 1 ∧ 1 ≤ k ∧ (List.ofFn fun i => (x i)⁻¹ * g * x i).prod = 1
-- N003 = goal: False

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

end TopologyCertificate_p1572_not_biorderable_of_product_conjugates_eq_o

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1664_paired_complex_tuple_set_convex
-- topology_sha256: b4be8d3735c355ac6e653e0f9dd5a2845135be269c517bc5360bd2601e64ce1b
namespace TopologyCertificate_p1664_paired_complex_tuple_set_convex

-- N001 = hζ: ζ ∈ {ζ | (∀ (i : Fin (l + m)), ζ i = ζ (σ i)) ∧ (∀ (i : Fin (l + m)), 0 < (ζ i).re) ∧ (∀ (i : ℕ), 1 ≤ i → i < l → 0 < (∑ k with ↑k < i, ζ k).im) ∧ (∀ (j : ℕ), 1 ≤ j → j < m → (∑ k with l ≤ ↑k ∧ ↑k < l + j, ζ k).im < 0) ∧ ∑ k with ↑k < l, ζ k = ∑ k with l ≤ ↑k, ζ k}
-- N002 = hη: η ∈ {ζ | (∀ (i : Fin (l + m)), ζ i = ζ (σ i)) ∧ (∀ (i : Fin (l + m)), 0 < (ζ i).re) ∧ (∀ (i : ℕ), 1 ≤ i → i < l → 0 < (∑ k with ↑k < i, ζ k).im) ∧ (∀ (j : ℕ), 1 ≤ j → j < m → (∑ k with l ≤ ↑k ∧ ↑k < l + j, ζ k).im < 0) ∧ ∑ k with ↑k < l, ζ k = ∑ k with l ≤ ↑k, ζ k}
-- N003 = ha: 0 ≤ a
-- N004 = hab: a + b = 1
-- N005 = hb: 0 ≤ b
-- N006 = goal: (∀ (i : Fin (l + m)), (a • ζ + b • η) i = (a • ζ + b • η) (σ i)) ∧ (∀ (i : Fin (l + m)), 0 < ((a • ζ + b • η) i).re) ∧ (∀ (i : ℕ), 1 ≤ i → i < l → 0 < (∑ k with ↑k < i, (a • ζ + b • η) k).im) ∧ (∀ (j : ℕ), 1 ≤ j → j < m → (∑ k with l ≤ ↑k ∧ ↑k < l + j, (a • ζ + b • η) k).im < 0) ∧ ∑ k with ↑k < l, (a • ζ + b • η) k = ∑ k with l ≤ ↑k, (a • ζ + b • η) k

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
    (E001 : N001 → N002 → N003 → N005 → N004 → N006)
    : N006 := by
  have H_N006 : N006 := E001 B001 B002 B003 B005 B004
  exact H_N006

end TopologyCertificate_p1664_paired_complex_tuple_set_convex

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1763_basel_series
-- topology_sha256: 2f0bedcf54f8c11e6853d12d594dd879fa3f5a8a0457c32c42442f518da051ce
namespace TopologyCertificate_p1763_basel_series

-- N001 = h: HasSum (fun n => 1 / ↑(n + 1) ^ 2) (Real.pi ^ 2 / 6)
-- N002 = goal: HasSum (fun n => 1 / ↑(n + 1) ^ 2) (Real.pi ^ 2 / 6)

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

end TopologyCertificate_p1763_basel_series

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1789_seminormal_reesquotient_iff_radical
-- topology_sha256: ba053d0b8197efdea1b134528fc3518ef2231a2339087641ccb0f7b7557bbc6b
namespace TopologyCertificate_p1789_seminormal_reesquotient_iff_radical

-- N001 = hA: (∀ (a b : A), a ^ 2 = b ^ 2 → a ^ 3 = b ^ 3 → a = b) ∧ ∀ (x y : A), x ^ 3 = y ^ 2 → ∃ z, x = z ^ 2 ∧ y = z ^ 3
-- N002 = hI_zero: 0 ∈ I
-- N003 = hq_fiber: ∀ (a b : A), q a = q b ↔ a = b ∨ a ∈ I ∧ b ∈ I
-- N004 = hq_surjective: Function.Surjective ⇑q
-- N005 = qzero: ∀ (a : A), q a = 0 ↔ a ∈ I
-- N006 = goal: ((∀ (a b : B), a ^ 2 = b ^ 2 → a ^ 3 = b ^ 3 → a = b) ∧ ∀ (x y : B), x ^ 3 = y ^ 2 → ∃ z, x = z ^ 2 ∧ y = z ^ 3) ↔ ∀ (a : A), (∃ n, 1 ≤ n ∧ a ^ n ∈ I) → a ∈ I

-- E001 represents h_001_qzero
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
    (E001 : N002 → N003 → N005)
    (E002 : N001 → N004 → N003 → N005 → N006)
    : N006 := by
  have H_N005 : N005 := E001 B002 B003
  have H_N006 : N006 := E002 B001 B004 B003 H_N005
  exact H_N006

end TopologyCertificate_p1789_seminormal_reesquotient_iff_radical

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1925_exists_coloring_increasing_pairs
-- topology_sha256: 3f6427c70203b3e4c6d2749063d02e365dd26f2c1c125c6c882c4d8315e787fc
namespace TopologyCertificate_p1925_exists_coloring_increasing_pairs

-- N001 = goal: ∃ c, (∀ (n m : ℕ), n < m → c (n, m) < m) ∧ ∀ (n k : ℕ) (B : Set ℕ), B.Infinite → ∃ m ∈ B, n < m ∧ k ≤ c (n, m)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p1925_exists_coloring_increasing_pairs

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2061_fixed_disc_of_contractivity
-- topology_sha256: cdaf7feb9a824a85005a206c49841c05ff511f246426e3bdb3992b5cb809e336
namespace TopologyCertificate_p2061_fixed_disc_of_contractivity

-- N001 = hc₁: c < 1
-- N002 = hcontractive: ∀ (x : X), dist (T x) x ≤ c * dist (T x) x₀
-- N003 = goal: let ρ := sInf {r | ∃ x, T x ≠ x ∧ r = dist x (T x)}; (∀ (x : X), dist x x₀ ≤ ρ → x ≠ x₀ → 0 < dist (T x) x₀ ∧ dist (T x) x₀ ≤ ρ) → ∀ (x : X), dist x x₀ ≤ ρ → T x = x

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

end TopologyCertificate_p2061_fixed_disc_of_contractivity

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2404_abelian_surjective_add_id_star_commute
-- topology_sha256: 69f2cf3836ce8fc06e2967a6e32e72fdd62ebbb926a939b0967eab84873aa4af
namespace TopologyCertificate_p2404_abelian_surjective_add_id_star_commute

-- N001 = goal: (Function.Commute ⇑φ fun a => φ a + a) ∧ ∀ (x y : A), (fun a => φ a + a) x = φ y → ∃! z, φ z = x ∧ (fun a => φ a + a) z = y

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p2404_abelian_surjective_add_id_star_commute

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p3210_substochastic_row_update_product
-- topology_sha256: db50fe190604d05227612447bcc66f9ea76bc24aec9dacd3acf69bb671db2c27
namespace TopologyCertificate_p3210_substochastic_row_update_product

-- N001 = hC_nonneg: ∀ (i j : Fin N), 0 ≤ C i j
-- N002 = hQ: Q = (List.ofFn fun i => Matrix.updateRow 1 i (C i)).reverse.prod
-- N003 = hr: IsGreatest (Set.range fun i => ∑ j, C i j) r
-- N004 = hr_lt_one: r < 1
-- N005 = hinvariant: (∀ (x : Fin N), ∑ j, (List.map (fun a => Matrix.updateRow 1 a (C a)) idx.reverse).prod x j ≤ 1) ∧ ∀ i ∈ idx.reverse, ∑ j, (List.map (fun a => Matrix.updateRow 1 a (C a)) idx.reverse).prod i j ≤ r
-- N006 = hi_idx: i ∈ idx
-- N007 = hi: i ∈ idx.reverse
-- N008 = hbound: ∑ j, (List.map (fun a => Matrix.updateRow 1 a (C a)) idx.reverse).prod i j ≤ r
-- N009 = goal: ∑ j, Q i j ≤ r

-- E001 represents h_001_hinvariant
-- E002 represents h_002_hi_idx
-- E003 represents h_003_hi
-- E004 represents h_004_hbound
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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N001 → N003 → N004 → N005)
    (E002 : N006)
    (E003 : N006 → N007)
    (E004 : N005 → N007 → N008)
    (E005 : N002 → N008 → N009)
    : N009 := by
  have H_N005 : N005 := E001 B001 B003 B004
  have H_N006 : N006 := E002
  have H_N007 : N007 := E003 H_N006
  have H_N008 : N008 := E004 H_N005 H_N007
  have H_N009 : N009 := E005 B002 H_N008
  exact H_N009

end TopologyCertificate_p3210_substochastic_row_update_product

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p3260_group_symmetrization_lipschitz
-- topology_sha256: 98cc2ec8af7eb795746b45890d773629394f9177fe3dbdba47ff1373fbbd3200
namespace TopologyCertificate_p3260_group_symmetrization_lipschitz

-- N001 = hact: ∀ (g : G) (x y : ↑X), ‖↑(g • x) - ↑(g • y)‖ ≤ ‖↑x - ↑y‖
-- N002 = hf: ∀ (x y : ↑X), |f x - f y| ≤ L * ‖↑x - ↑y‖
-- N003 = hL: 0 ≤ L
-- N004 = hCpos: 0 < C
-- N005 = hterm: ∀ (g : G), |f (g • x) - f (g • y)| ≤ L * ‖↑x - ↑y‖
-- N006 = hsum: |∑ g, f (g • x) - ∑ g, f (g • y)| ≤ C * (L * ‖↑x - ↑y‖)
-- N007 = hdiv: |(∑ g, f (g • x)) / C - (∑ g, f (g • y)) / C| ≤ L * ‖↑x - ↑y‖
-- N008 = goal: |(∑ g, f (g • x)) / C - (∑ g, f (g • y)) / C| ≤ L * ‖↑x - ↑y‖

-- E001 represents h_001_hcpos
-- E002 represents h_002_hterm
-- E003 represents h_003_hsum
-- E004 represents h_004_hdiv
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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N004)
    (E002 : N001 → N003 → N002 → N005)
    (E003 : N005 → N006)
    (E004 : N004 → N006 → N007)
    (E005 : N007 → N008)
    : N008 := by
  have H_N004 : N004 := E001
  have H_N005 : N005 := E002 B001 B003 B002
  have H_N006 : N006 := E003 H_N005
  have H_N007 : N007 := E004 H_N004 H_N006
  have H_N008 : N008 := E005 H_N007
  exact H_N008

end TopologyCertificate_p3260_group_symmetrization_lipschitz
