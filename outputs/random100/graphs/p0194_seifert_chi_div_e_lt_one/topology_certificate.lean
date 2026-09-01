import Init

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
