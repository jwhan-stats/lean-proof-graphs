import Init

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
