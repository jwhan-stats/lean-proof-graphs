import Mathlib

/- accepted add_to_file helper 1 -/
lemma triangular_pair (m : ℕ) :
    2 * m ^ 2 = 2 * ((m - 1) * m / 2 + m * (m + 1) / 2) := by
  have hsum :
      2 * m ^ 2 = (m - 1) * m + m * (m + 1) := by
    cases m with
    | zero => norm_num
    | succ a =>
        simp
        ring
  have hA : 2 ∣ (m - 1) * m := by
    rw [Nat.mul_comm]
    exact Nat.two_dvd_mul_sub_one m
  have hB : 2 ∣ m * (m + 1) := Nat.two_dvd_mul_add_one m
  have hAback : 2 * ((m - 1) * m / 2) = (m - 1) * m := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel hA
  have hBback : 2 * (m * (m + 1) / 2) = m * (m + 1) := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel hB
  have hdouble :
      2 * ((m - 1) * m / 2 + m * (m + 1) / 2)
        = (m - 1) * m + m * (m + 1) := by
    rw [Nat.mul_add, hAback, hBback]
  exact hsum.trans hdouble.symm

/- verified submission -/
theorem sequence_triangular_formula
    (c : ℕ → ℕ)
    (hc₁ : c 1 = 2)
    (hc : ∀ k : ℕ, 0 < k →
      c (2 * k) = 2 * (k + 1) ^ 2 ∧
      c (2 * k + 1) = 2 * (k + 1) ^ 2) :
    ∀ n : ℕ, 0 < n →
      let m := (n + 2) / 2
      let t : ℕ → ℕ := fun r => r * (r + 1) / 2
      c n = 2 * m ^ 2 ∧ 2 * m ^ 2 = 2 * (t (m - 1) + t m) := by
  intro n hn
  by_cases h1 : n = 1
  · subst n
    simp [hc₁]
  · let k := n / 2
    have hk : 0 < k := by
      omega
    have hrec := hc k hk
    have hmod := Nat.mod_two_eq_zero_or_one n
    rcases hmod with heven | hodd
    · have hn_eq : n = 2 * k := by
        omega
      have hm : (n + 2) / 2 = k + 1 := by
        omega
      have hcn : c n = 2 * (k + 1) ^ 2 := by
        rw [hn_eq]
        exact hrec.1
      dsimp
      constructor
      · rw [hm]
        exact hcn
      · rw [hm]
        exact triangular_pair (k + 1)
    · have hn_eq : n = 2 * k + 1 := by
        omega
      have hm : (n + 2) / 2 = k + 1 := by
        omega
      have hcn : c n = 2 * (k + 1) ^ 2 := by
        rw [hn_eq]
        exact hrec.2
      dsimp
      constructor
      · rw [hm]
        exact hcn
      · rw [hm]
        exact triangular_pair (k + 1)
