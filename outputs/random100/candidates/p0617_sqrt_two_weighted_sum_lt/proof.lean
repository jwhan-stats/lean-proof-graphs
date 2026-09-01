import Mathlib

/- accepted add_to_file helper 1 -/
import Mathlib

open Finset Real

noncomputable section

def wsum (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), ((n - j : ℕ) : ℝ) * (Real.sqrt 2) ^ j

lemma wsum_succ (n : ℕ) :
    wsum (n + 1) = wsum n + ∑ j ∈ Finset.range (n + 1), (Real.sqrt 2) ^ j := by
  unfold wsum
  rw [Finset.sum_range_succ]
  have hlast : ((n + 1 - (n + 1) : ℕ) : ℝ) * (Real.sqrt 2) ^ (n + 1) = 0 := by simp
  rw [hlast, add_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hnat : n + 1 - j = n - j + 1 := by omega
  rw [hnat]
  norm_num [pow_succ, add_mul, one_mul]

lemma wsum_eq (n : ℕ) :
    wsum n =
      ((Real.sqrt 2) ^ (n + 1) + (n : ℝ) - ((n + 1 : ℕ) : ℝ) * Real.sqrt 2) *
        (Real.sqrt 2 + 1) ^ 2 := by
  induction n with
  | zero =>
      simp [wsum]
  | succ n ih =>
      rw [wsum_succ n, geom_sum_eq, ih]
      · rw [div_eq_mul_inv, Real.inv_sqrt_two_sub_one]
        have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        have h3 : (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 := by
          rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, h2]
        have h4 : (Real.sqrt 2) ^ 4 = 4 := by
          rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, h2]
          norm_num
        ring_nf
        simp only [h2, h3, h4]
        push_cast
        ring
      · exact Real.one_lt_sqrt_two.ne'

/- verified submission -/
theorem sqrt_two_weighted_sum_lt (i : ℕ) :
    (∑ j ∈ Finset.range (i + 1), ((i - j : ℕ) : ℝ) * (Real.sqrt 2) ^ j) <
      (4 + 3 * Real.sqrt 2) * (Real.sqrt 2) ^ i := by
  change wsum i < (4 + 3 * Real.sqrt 2) * (Real.sqrt 2) ^ i
  let r : ℝ := Real.sqrt 2
  let q : ℝ := (r + 1) ^ 2
  let b : ℝ := ((i + 1 : ℕ) : ℝ) * r - (i : ℝ)
  have hr_gt_one : 1 < r := by
    dsimp [r]
    exact Real.one_lt_sqrt_two
  have hr_pos : 0 < r := lt_trans zero_lt_one hr_gt_one
  have hsq : r ^ 2 = 2 := by
    dsimp [r]
    exact Real.sq_sqrt (by norm_num)
  have hcube : r ^ 3 = 2 * r := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, hsq]
  have htarget : (4 + 3 * r) * r ^ i = r ^ (i + 1) * q := by
    have hrq : r * q = 4 + 3 * r := by
      dsimp [q]
      ring_nf
      rw [hcube, hsq]
      ring
    calc
      (4 + 3 * r) * r ^ i = (r * q) * r ^ i := by rw [hrq]
      _ = r ^ (i + 1) * q := by
        rw [pow_succ]
        ring
  have hdiff : (4 + 3 * r) * r ^ i - wsum i = b * q := by
    rw [wsum_eq i]
    dsimp [r, q, b]
    rw [htarget]
    dsimp [r, q]
    push_cast
    ring
  have hb : 0 < b := by
    have hnonneg : 0 ≤ (i : ℝ) * (r - 1) := by
      exact mul_nonneg (Nat.cast_nonneg i) (sub_nonneg.mpr hr_gt_one.le)
    have hsumpos : 0 < (i : ℝ) * (r - 1) + r :=
      add_pos_of_nonneg_of_pos hnonneg hr_pos
    have hb_eq : b = (i : ℝ) * (r - 1) + r := by
      dsimp [b]
      push_cast
      ring
    rw [hb_eq]
    exact hsumpos
  have hq : 0 < q := by
    dsimp [q]
    exact sq_pos_of_pos (add_pos hr_pos zero_lt_one)
  have hdiff_pos : 0 < (4 + 3 * r) * r ^ i - wsum i := by
    rw [hdiff]
    exact mul_pos hb hq
  dsimp [r] at hdiff_pos
  linarith
