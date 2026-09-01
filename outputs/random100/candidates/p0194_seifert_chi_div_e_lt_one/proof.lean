import Mathlib

/- verified submission -/
lemma seifert_nat_div_lt_one_rat {a b : ℕ} (h : a < b) :
    (a : ℚ) / (b : ℚ) < 1 := by
  have hb : 0 < (b : ℚ) := by
    exact_mod_cast Nat.zero_lt_of_lt h
  exact (div_lt_one hb).mpr (by exact_mod_cast h)

lemma seifert_nat_inv_pos_rat {b : ℕ} (hb : 2 ≤ b) :
    0 < (b : ℚ)⁻¹ := by
  have hb0 : 0 < (b : ℚ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hb)
  exact inv_pos.mpr hb0

theorem seifert_chi_div_e_lt_one
    (t d : ℕ) (n q : ℕ → ℕ)
    (hn : ∀ i, 1 ≤ i → i ≤ t → 2 ≤ n i)
    (hq_pos : ∀ i, 1 ≤ i → i ≤ t → 1 ≤ q i)
    (hq_lt : ∀ i, 1 ≤ i → i ≤ t → q i < n i)
    (hcoprime : ∀ i, 1 ≤ i → i ≤ t → Nat.Coprime (n i) (q i))
    (he : 0 < (d : ℚ) - ∑ i ∈ Finset.Icc 1 t, (q i : ℚ) / (n i : ℚ))
    (hcases :
      (t = 3 ∧
        (4 ≤ d ∨
          (d = 3 ∧ q 1 = 1) ∨
          (d = 2 ∧ q 1 = 1 ∧ q 2 = 1))) ∨
      (t = 4 ∧ 3 ≤ d ∧ q 1 = 1 ∧ q 2 = 1 ∧ q 3 = 1)) :
    let e : ℚ := (d : ℚ) - ∑ i ∈ Finset.Icc 1 t, (q i : ℚ) / (n i : ℚ)
    let χ : ℚ := -2 + ∑ i ∈ Finset.Icc 1 t, (1 - 1 / (n i : ℚ))
    χ / e < 1 := by
  rw [div_lt_one he]
  rcases hcases with h3 | h4
  · rcases h3 with ⟨ht, hc⟩
    subst t
    rcases hc with hd | hd | hd
    · have hdQ : (4 : ℚ) ≤ d := by exact_mod_cast hd
      have hq1 : (q 1 : ℚ) / (n 1 : ℚ) < 1 :=
        seifert_nat_div_lt_one_rat (hq_lt 1 (by norm_num) (by norm_num))
      have hq2 : (q 2 : ℚ) / (n 2 : ℚ) < 1 :=
        seifert_nat_div_lt_one_rat (hq_lt 2 (by norm_num) (by norm_num))
      have hq3 : (q 3 : ℚ) / (n 3 : ℚ) < 1 :=
        seifert_nat_div_lt_one_rat (hq_lt 3 (by norm_num) (by norm_num))
      have hn1 : 0 < (n 1 : ℚ)⁻¹ :=
        seifert_nat_inv_pos_rat (hn 1 (by norm_num) (by norm_num))
      have hn2 : 0 < (n 2 : ℚ)⁻¹ :=
        seifert_nat_inv_pos_rat (hn 2 (by norm_num) (by norm_num))
      have hn3 : 0 < (n 3 : ℚ)⁻¹ :=
        seifert_nat_inv_pos_rat (hn 3 (by norm_num) (by norm_num))
      have hsumq : ∑ i ∈ Finset.Icc 1 3, (q i : ℚ) / (n i : ℚ) < 3 := by
        norm_num [Finset.sum_Icc_succ_top]
        nlinarith
      have hsuminv_exp :
          0 < (n 1 : ℚ)⁻¹ + (n 2 : ℚ)⁻¹ + (n 3 : ℚ)⁻¹ :=
        add_pos (add_pos hn1 hn2) hn3
      have hchi : -2 + ∑ i ∈ Finset.Icc 1 3, (1 - 1 / (n i : ℚ)) < 1 := by
        norm_num [Finset.sum_Icc_succ_top]
        linarith
      have he1 : 1 < (d : ℚ) - ∑ i ∈ Finset.Icc 1 3, (q i : ℚ) / (n i : ℚ) := by
        nlinarith
      exact lt_trans hchi he1
    · rcases hd with ⟨hd, hq1nat⟩
      subst d
      have hq2 : (q 2 : ℚ) / (n 2 : ℚ) < 1 :=
        seifert_nat_div_lt_one_rat (hq_lt 2 (by norm_num) (by norm_num))
      have hq3 : (q 3 : ℚ) / (n 3 : ℚ) < 1 :=
        seifert_nat_div_lt_one_rat (hq_lt 3 (by norm_num) (by norm_num))
      have hn2 : 0 < (n 2 : ℚ)⁻¹ :=
        seifert_nat_inv_pos_rat (hn 2 (by norm_num) (by norm_num))
      have hn3 : 0 < (n 3 : ℚ)⁻¹ :=
        seifert_nat_inv_pos_rat (hn 3 (by norm_num) (by norm_num))
      norm_num [Finset.sum_Icc_succ_top, hq1nat]
      nlinarith
    · rcases hd with ⟨hd, hq1nat, hq2nat⟩
      subst d
      have hq3 : (q 3 : ℚ) / (n 3 : ℚ) < 1 :=
        seifert_nat_div_lt_one_rat (hq_lt 3 (by norm_num) (by norm_num))
      have hn3 : 0 < (n 3 : ℚ)⁻¹ :=
        seifert_nat_inv_pos_rat (hn 3 (by norm_num) (by norm_num))
      norm_num [Finset.sum_Icc_succ_top, hq1nat, hq2nat]
      nlinarith
  · rcases h4 with ⟨ht, hd, hq1nat, hq2nat, hq3nat⟩
    subst t
    have hdQ : (3 : ℚ) ≤ d := by exact_mod_cast hd
    have hq4 : (q 4 : ℚ) / (n 4 : ℚ) < 1 :=
      seifert_nat_div_lt_one_rat (hq_lt 4 (by norm_num) (by norm_num))
    have hn4 : 0 < (n 4 : ℚ)⁻¹ :=
      seifert_nat_inv_pos_rat (hn 4 (by norm_num) (by norm_num))
    norm_num [Finset.sum_Icc_succ_top, hq1nat, hq2nat, hq3nat]
    nlinarith
