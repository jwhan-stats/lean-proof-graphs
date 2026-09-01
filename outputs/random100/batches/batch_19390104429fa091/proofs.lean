import Mathlib

/- Generated only to amortize Mathlib loading during graph export. -/

namespace Rollout_p1286_lebesgue_integral_modified_salem

/- accepted add_to_file helper 1 -/

noncomputable section

def msP (p₀ p₁ p₂ : ℝ) : Fin 3 → ℝ := ![p₀, p₁, p₂]

def msB (p₀ p₁ p₂ : ℝ) : Fin 3 → ℝ := ![0, p₀, p₀ + p₁]

def msE (p₀ p₁ p₂ : ℝ) (i : ℕ → Fin 3) : ℝ :=
  ∑' k : ℕ, msB p₀ p₁ p₂ (i k) * ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i r)

def msTheta : Fin 3 → Fin 3 := ![0, 2, 1]

lemma msP_pos {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1) (j : Fin 3) :
    0 < msP p₀ p₁ p₂ j := by
  fin_cases j <;> simp [msP, hp₀.1, hp₁.1, hp₂.1]

lemma msP_lt_one {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1) (j : Fin 3) :
    msP p₀ p₁ p₂ j < 1 := by
  fin_cases j <;> simp [msP, hp₀.2, hp₁.2, hp₂.2]

lemma msP_nonneg {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1) (j : Fin 3) :
    0 ≤ msP p₀ p₁ p₂ j :=
  (msP_pos hp₀ hp₁ hp₂ j).le

lemma msB_nonneg {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1) (j : Fin 3) :
    0 ≤ msB p₀ p₁ p₂ j := by
  fin_cases j <;> simp [msB, hp₀.1.le, add_nonneg hp₀.1.le hp₁.1.le]

lemma msB_add_msP_le_one {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (j : Fin 3) :
    msB p₀ p₁ p₂ j + msP p₀ p₁ p₂ j ≤ 1 := by
  fin_cases j <;> simp [msB, msP]
  · exact hp₀.2.le
  · have : p₀ + p₁ < 1 := by
      rw [← hsum]
      linarith [hp₂.1]
    exact this.le
  · exact hsum.le

lemma msB_le_one {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (j : Fin 3) :
    msB p₀ p₁ p₂ j ≤ 1 := by
  have h := msB_add_msP_le_one hp₀ hp₁ hp₂ hsum j
  have hp := msP_nonneg hp₀ hp₁ hp₂ j
  linarith

end

/- accepted add_to_file helper 2 -/
noncomputable section

lemma msE_term_nonneg {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (i : ℕ → Fin 3) (k : ℕ) :
    0 ≤ msB p₀ p₁ p₂ (i k) * ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i r) := by
  exact mul_nonneg (msB_nonneg hp₀ hp₁ _)
    (Finset.prod_nonneg fun r _ => msP_nonneg hp₀ hp₁ hp₂ _)

lemma msE_summable {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (i : ℕ → Fin 3) :
    Summable fun k : ℕ =>
      msB p₀ p₁ p₂ (i k) * ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i r) := by
  let q := max p₀ (max p₁ p₂)
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact le_trans hp₀.1.le (le_max_left _ _)
  have hq_lt_one : q < 1 := by
    dsimp [q]
    exact max_lt hp₀.2 (max_lt hp₁.2 hp₂.2)
  refine Summable.of_nonneg_of_le
    (fun k => msE_term_nonneg hp₀ hp₁ hp₂ i k) ?_ (summable_geometric_of_lt_one hq_nonneg hq_lt_one)
  intro k
  have hp_le_q : ∀ r ∈ Finset.range k, msP p₀ p₁ p₂ (i r) ≤ q := by
    intro r hr
    generalize hj : i r = j
    fin_cases j <;> simp [msP, q]
  have hprod : (∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i r)) ≤ q ^ k := by
    calc
      (∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i r)) ≤
          ∏ r ∈ Finset.range k, q :=
        Finset.prod_le_prod
          (fun r _ => msP_nonneg hp₀ hp₁ hp₂ _)
          (fun r hr => hp_le_q r hr)
      _ = q ^ k := by simp
  calc
    msB p₀ p₁ p₂ (i k) * ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i r)
        ≤ 1 * q ^ k := by
          exact mul_le_mul (msB_le_one hp₀ hp₁ hp₂ hsum _) hprod
            (Finset.prod_nonneg fun r _ => msP_nonneg hp₀ hp₁ hp₂ _) zero_le_one
    _ = q ^ k := one_mul _

end

/- accepted add_to_file helper 3 -/
noncomputable section

lemma msE_eq_beta_add_mul_tail {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (i : ℕ → Fin 3) :
    msE p₀ p₁ p₂ i =
      msB p₀ p₁ p₂ (i 0) + msP p₀ p₁ p₂ (i 0) * msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) := by
  let term : (ℕ → Fin 3) → ℕ → ℝ := fun j k ↦
    msB p₀ p₁ p₂ (j k) * ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (j r)
  have hsplit : msE p₀ p₁ p₂ i = term i 0 + ∑' k : ℕ, term i (k + 1) := by
    dsimp [msE, term]
    exact (msE_summable hp₀ hp₁ hp₂ hsum i).tsum_eq_zero_add
  rw [hsplit]
  have hshift : (∑' k : ℕ, term i (k + 1)) =
      msP p₀ p₁ p₂ (i 0) * msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) := by
    calc
      (∑' k : ℕ, term i (k + 1)) =
          ∑' k : ℕ, msP p₀ p₁ p₂ (i 0) * term (fun n ↦ i (n + 1)) k := by
            congr 1
            ext k
            dsimp [term]
            rw [Finset.prod_range_succ']
            ring
      _ = msP p₀ p₁ p₂ (i 0) * msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) := by
            rw [tsum_mul_left]
            rfl
  rw [hshift]
  dsimp [term]
  simp

end

/- accepted add_to_file helper 4 -/
noncomputable section

lemma msE_partial_succ {p₀ p₁ p₂ : ℝ} (i : ℕ → Fin 3) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
        msB p₀ p₁ p₂ (i k) * ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i r)) =
      msB p₀ p₁ p₂ (i 0) + msP p₀ p₁ p₂ (i 0) *
        (∑ k ∈ Finset.range n,
          msB p₀ p₁ p₂ (i (k + 1)) *
            ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i (r + 1))) := by
  calc
    (∑ k ∈ Finset.range (n + 1),
        msB p₀ p₁ p₂ (i k) * ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i r))
        = msB p₀ p₁ p₂ (i 0) +
          ∑ k ∈ Finset.range n,
            msB p₀ p₁ p₂ (i (k + 1)) *
              ∏ r ∈ Finset.range (k + 1), msP p₀ p₁ p₂ (i r) := by
            rw [Finset.sum_range_succ']
            rw [add_comm]
            simp
    _ = msB p₀ p₁ p₂ (i 0) + msP p₀ p₁ p₂ (i 0) *
          (∑ k ∈ Finset.range n,
            msB p₀ p₁ p₂ (i (k + 1)) *
              ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i (r + 1))) := by
          rw [Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [Finset.prod_range_succ']
          ring

lemma msE_partial_le_one {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) :
    ∀ n : ℕ, ∀ i : ℕ → Fin 3,
      (∑ k ∈ Finset.range n,
        msB p₀ p₁ p₂ (i k) * ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i r)) ≤ 1 := by
  intro n
  induction n with
  | zero =>
      intro i
      simp
  | succ n ih =>
      intro i
      rw [msE_partial_succ]
      have hpnonneg := msP_nonneg hp₀ hp₁ hp₂ (i 0)
      have htail := ih (fun k ↦ i (k + 1))
      have hbound := msB_add_msP_le_one hp₀ hp₁ hp₂ hsum (i 0)
      calc
        msB p₀ p₁ p₂ (i 0) + msP p₀ p₁ p₂ (i 0) *
            (∑ k ∈ Finset.range n,
              msB p₀ p₁ p₂ (i (k + 1)) *
                ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i (r + 1)))
            ≤ msB p₀ p₁ p₂ (i 0) + msP p₀ p₁ p₂ (i 0) * 1 := by
              exact add_le_add_right (mul_le_mul_of_nonneg_left htail hpnonneg) _
        _ = msB p₀ p₁ p₂ (i 0) + msP p₀ p₁ p₂ (i 0) := by ring
        _ ≤ 1 := hbound

lemma msE_nonneg {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1) (i : ℕ → Fin 3) :
    0 ≤ msE p₀ p₁ p₂ i := by
  dsimp [msE]
  exact tsum_nonneg (msE_term_nonneg hp₀ hp₁ hp₂ i)

lemma msE_le_one {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (i : ℕ → Fin 3) :
    msE p₀ p₁ p₂ i ≤ 1 := by
  have hs := msE_summable hp₀ hp₁ hp₂ hsum i
  exact le_of_tendsto hs.hasSum.tendsto_sum_nat
    (Filter.Eventually.of_forall fun n ↦ msE_partial_le_one hp₀ hp₁ hp₂ hsum n i)

lemma msE_mem_Icc {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (i : ℕ → Fin 3) :
    msE p₀ p₁ p₂ i ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨msE_nonneg hp₀ hp₁ hp₂ i, msE_le_one hp₀ hp₁ hp₂ hsum i⟩

end

/- accepted add_to_file helper 5 -/
noncomputable section

lemma msE_eq_one_head {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) {i : ℕ → Fin 3}
    (hi : msE p₀ p₁ p₂ i = 1) :
    i 0 = 2 := by
  have hrec := msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum i
  have htail := msE_le_one hp₀ hp₁ hp₂ hsum (fun k ↦ i (k + 1))
  generalize hj : i 0 = j
  fin_cases j
  · have hE : msE p₀ p₁ p₂ i = p₀ * msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) := by
      rw [hrec, hj]
      simp [msB, msP]
    have hle : msE p₀ p₁ p₂ i ≤ p₀ := by
      rw [hE]
      calc
        p₀ * msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) ≤ p₀ * 1 :=
          mul_le_mul_of_nonneg_left htail hp₀.1.le
        _ = p₀ := by ring
    have hp1 : (1 : ℝ) ≤ p₀ := by
      rw [← hi]
      exact hle
    linarith [hp₀.2]
  · have hp01 : p₀ + p₁ < 1 := by
      rw [← hsum]
      linarith [hp₂.1]
    have hE : msE p₀ p₁ p₂ i = p₀ + p₁ * msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) := by
      rw [hrec, hj]
      simp [msB, msP]
    have hle : msE p₀ p₁ p₂ i ≤ p₀ + p₁ := by
      rw [hE]
      calc
        p₀ + p₁ * msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) ≤ p₀ + p₁ * 1 :=
          add_le_add_right (mul_le_mul_of_nonneg_left htail hp₁.1.le) _
        _ = p₀ + p₁ := by ring
    have hp1 : (1 : ℝ) ≤ p₀ + p₁ := by
      rw [← hi]
      exact hle
    linarith
  · rfl

lemma msE_eq_one_tail {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) {i : ℕ → Fin 3}
    (hi : msE p₀ p₁ p₂ i = 1) :
    msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) = 1 := by
  have hhead := msE_eq_one_head hp₀ hp₁ hp₂ hsum hi
  have hrec := msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum i
  rw [hhead] at hrec
  simp [msB, msP] at hrec
  have hmul : p₂ * (msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) - 1) = 0 := by
    linarith
  have hfactor := mul_eq_zero.mp hmul
  rcases hfactor with hp | ht
  · linarith [hp₂.1]
  · linarith

lemma msE_eq_one_apply {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) :
    ∀ k : ℕ, ∀ i : ℕ → Fin 3, msE p₀ p₁ p₂ i = 1 → i k = 2 := by
  intro k
  induction k with
  | zero =>
      intro i hi
      exact msE_eq_one_head hp₀ hp₁ hp₂ hsum hi
  | succ k ih =>
      intro i hi
      exact ih (fun n ↦ i (n + 1))
        (msE_eq_one_tail hp₀ hp₁ hp₂ hsum hi)

lemma msE_eq_zero_head {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) {i : ℕ → Fin 3}
    (hi : msE p₀ p₁ p₂ i = 0) :
    i 0 = 0 := by
  have hrec := msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum i
  have htail_nonneg := msE_nonneg hp₀ hp₁ hp₂ (fun k ↦ i (k + 1))
  generalize hj : i 0 = j
  fin_cases j
  · rfl
  · have hE : msE p₀ p₁ p₂ i = p₀ + p₁ * msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) := by
      rw [hrec, hj]
      simp [msB, msP]
    have hnonneg : 0 ≤ p₁ * msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) :=
      mul_nonneg hp₁.1.le htail_nonneg
    rw [hE] at hi
    linarith [hp₀.1]
  · have hE : msE p₀ p₁ p₂ i = p₀ + p₁ + p₂ * msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) := by
      rw [hrec, hj]
      simp [msB, msP]
    have hnonneg : 0 ≤ p₂ * msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) :=
      mul_nonneg hp₂.1.le htail_nonneg
    have hp01 : 0 < p₀ + p₁ := add_pos hp₀.1 hp₁.1
    rw [hE] at hi
    linarith

lemma msE_eq_zero_tail {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) {i : ℕ → Fin 3}
    (hi : msE p₀ p₁ p₂ i = 0) :
    msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) = 0 := by
  have hhead := msE_eq_zero_head hp₀ hp₁ hp₂ hsum hi
  have hrec := msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum i
  rw [hhead] at hrec
  simp [msB, msP] at hrec
  have hmul : p₀ * msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) = 0 := by linarith
  have hfactor := mul_eq_zero.mp hmul
  rcases hfactor with hp | ht
  · linarith [hp₀.1]
  · exact ht

lemma msE_eq_zero_apply {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) :
    ∀ k : ℕ, ∀ i : ℕ → Fin 3, msE p₀ p₁ p₂ i = 0 → i k = 0 := by
  intro k
  induction k with
  | zero =>
      intro i hi
      exact msE_eq_zero_head hp₀ hp₁ hp₂ hsum hi
  | succ k ih =>
      intro i hi
      exact ih (fun n ↦ i (n + 1))
        (msE_eq_zero_tail hp₀ hp₁ hp₂ hsum hi)

end

/- accepted add_to_file helper 6 -/
noncomputable section

def msEventuallyZero (i : ℕ → Fin 3) : Prop :=
  ∃ N : ℕ, ∀ k : ℕ, N ≤ k → i k = 0

lemma msEventuallyZero.tail {i : ℕ → Fin 3} (hi : msEventuallyZero i) :
    msEventuallyZero (fun k ↦ i (k + 1)) := by
  rcases hi with ⟨N, hN⟩
  cases N with
  | zero =>
      refine ⟨0, ?_⟩
      intro k hk
      exact hN (k + 1) (Nat.zero_le _)
  | succ N =>
      refine ⟨N, ?_⟩
      intro k hk
      exact hN (k + 1) (Nat.succ_le_succ hk)

lemma msE_head_lower {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (i : ℕ → Fin 3) :
    msB p₀ p₁ p₂ (i 0) ≤ msE p₀ p₁ p₂ i := by
  rw [msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum i]
  have h := mul_nonneg (msP_nonneg hp₀ hp₁ hp₂ (i 0))
    (msE_nonneg hp₀ hp₁ hp₂ (fun k ↦ i (k + 1)))
  linarith

lemma msE_head_upper {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (i : ℕ → Fin 3) :
    msE p₀ p₁ p₂ i ≤
      msB p₀ p₁ p₂ (i 0) + msP p₀ p₁ p₂ (i 0) := by
  rw [msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum i]
  have htail := msE_le_one hp₀ hp₁ hp₂ hsum (fun k ↦ i (k + 1))
  have hmul := mul_le_mul_of_nonneg_left htail (msP_nonneg hp₀ hp₁ hp₂ (i 0))
  rw [mul_one] at hmul
  exact add_le_add_right hmul _

end

/- accepted add_to_file helper 7 -/
noncomputable section

lemma msE_eq_one_not_eventuallyZero {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) {i : ℕ → Fin 3}
    (hi : msE p₀ p₁ p₂ i = 1) :
    ¬ msEventuallyZero i := by
  rintro ⟨N, hN⟩
  have htwo := msE_eq_one_apply hp₀ hp₁ hp₂ hsum N i hi
  have hzero := hN N le_rfl
  rw [hzero] at htwo
  exact (by decide : (0 : Fin 3) ≠ 2) htwo

lemma msE_eventuallyZero_head_eq {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) {i j : ℕ → Fin 3}
    (hEq : msE p₀ p₁ p₂ i = msE p₀ p₁ p₂ j)
    (hi_zero : msEventuallyZero i) (hj_zero : msEventuallyZero j) :
    i 0 = j 0 := by
  have cross01 : ∀ {a b : ℕ → Fin 3},
      msE p₀ p₁ p₂ a = msE p₀ p₁ p₂ b →
      msEventuallyZero a → a 0 = 0 → b 0 = 1 → False := by
    intro a b hab ha_zero ha0 hb1
    have ha_tail_zero := ha_zero.tail
    have hEa : msE p₀ p₁ p₂ a = p₀ * msE p₀ p₁ p₂ (fun k ↦ a (k + 1)) := by
      rw [msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum a, ha0]
      simp [msB, msP]
    have hEb : msE p₀ p₁ p₂ b = p₀ + p₁ * msE p₀ p₁ p₂ (fun k ↦ b (k + 1)) := by
      rw [msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum b, hb1]
      simp [msB, msP]
    have ha_upper : msE p₀ p₁ p₂ a ≤ p₀ := by
      rw [hEa]
      have htail := msE_le_one hp₀ hp₁ hp₂ hsum (fun k ↦ a (k + 1))
      calc
        p₀ * msE p₀ p₁ p₂ (fun k ↦ a (k + 1)) ≤ p₀ * 1 :=
          mul_le_mul_of_nonneg_left htail hp₀.1.le
        _ = p₀ := by ring
    have hb_lower : p₀ ≤ msE p₀ p₁ p₂ b := by
      rw [hEb]
      have htail := msE_nonneg hp₀ hp₁ hp₂ (fun k ↦ b (k + 1))
      have hmul := mul_nonneg hp₁.1.le htail
      linarith
    have ha_eq : msE p₀ p₁ p₂ a = p₀ := le_antisymm ha_upper (by linarith)
    have hb_eq : msE p₀ p₁ p₂ b = p₀ := le_antisymm (by linarith) hb_lower
    have htail_one : msE p₀ p₁ p₂ (fun k ↦ a (k + 1)) = 1 := by
      have hmul : p₀ * msE p₀ p₁ p₂ (fun k ↦ a (k + 1)) = p₀ * 1 := by
        rw [← hEa, ha_eq]
        ring
      exact mul_left_cancel₀ (ne_of_gt hp₀.1) hmul
    exact msE_eq_one_not_eventuallyZero hp₀ hp₁ hp₂ hsum htail_one ha_tail_zero
  have cross12 : ∀ {a b : ℕ → Fin 3},
      msE p₀ p₁ p₂ a = msE p₀ p₁ p₂ b →
      msEventuallyZero a → a 0 = 1 → b 0 = 2 → False := by
    intro a b hab ha_zero ha1 hb2
    have ha_tail_zero := ha_zero.tail
    have hEa : msE p₀ p₁ p₂ a = p₀ + p₁ * msE p₀ p₁ p₂ (fun k ↦ a (k + 1)) := by
      rw [msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum a, ha1]
      simp [msB, msP]
    have hEb : msE p₀ p₁ p₂ b = p₀ + p₁ + p₂ * msE p₀ p₁ p₂ (fun k ↦ b (k + 1)) := by
      rw [msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum b, hb2]
      simp [msB, msP]
    have ha_upper : msE p₀ p₁ p₂ a ≤ p₀ + p₁ := by
      rw [hEa]
      have htail := msE_le_one hp₀ hp₁ hp₂ hsum (fun k ↦ a (k + 1))
      calc
        p₀ + p₁ * msE p₀ p₁ p₂ (fun k ↦ a (k + 1)) ≤ p₀ + p₁ * 1 :=
          add_le_add_right (mul_le_mul_of_nonneg_left htail hp₁.1.le) _
        _ = p₀ + p₁ := by ring
    have hb_lower : p₀ + p₁ ≤ msE p₀ p₁ p₂ b := by
      rw [hEb]
      have htail := msE_nonneg hp₀ hp₁ hp₂ (fun k ↦ b (k + 1))
      have hmul := mul_nonneg hp₂.1.le htail
      linarith
    have ha_eq : msE p₀ p₁ p₂ a = p₀ + p₁ := le_antisymm ha_upper (by linarith)
    have hb_eq : msE p₀ p₁ p₂ b = p₀ + p₁ := le_antisymm (by linarith) hb_lower
    have htail_one : msE p₀ p₁ p₂ (fun k ↦ a (k + 1)) = 1 := by
      have hmul : p₁ * msE p₀ p₁ p₂ (fun k ↦ a (k + 1)) = p₁ * 1 := by
        have : p₀ + p₁ * msE p₀ p₁ p₂ (fun k ↦ a (k + 1)) = p₀ + p₁ := by
          rw [← hEa, ha_eq]
        linarith
      exact mul_left_cancel₀ (ne_of_gt hp₁.1) hmul
    exact msE_eq_one_not_eventuallyZero hp₀ hp₁ hp₂ hsum htail_one ha_tail_zero
  have cross02 : ∀ {a b : ℕ → Fin 3},
      msE p₀ p₁ p₂ a = msE p₀ p₁ p₂ b → a 0 = 0 → b 0 = 2 → False := by
    intro a b hab ha0 hb2
    have ha_upper : msE p₀ p₁ p₂ a ≤ p₀ := by
      have h := msE_head_upper hp₀ hp₁ hp₂ hsum a
      rw [ha0] at h
      simpa [msB, msP] using h
    have hb_lower : p₀ + p₁ ≤ msE p₀ p₁ p₂ b := by
      have h := msE_head_lower hp₀ hp₁ hp₂ hsum b
      rw [hb2] at h
      simpa [msB, msP] using h
    linarith [hp₁.1]
  generalize hi0 : i 0 = a
  generalize hj0 : j 0 = b
  fin_cases a <;> fin_cases b
  · rfl
  · exact False.elim (cross01 hEq hi_zero hi0 hj0)
  · exact False.elim (cross02 hEq hi0 hj0)
  · exact False.elim ((by decide : (0 : Fin 3) ≠ 1)
      (False.elim (cross01 hEq.symm hj_zero hj0 hi0)))
  · rfl
  · exact False.elim (cross12 hEq hi_zero hi0 hj0)
  · exact False.elim ((by decide : (0 : Fin 3) ≠ 2)
      (False.elim (cross02 hEq.symm hj0 hi0)))
  · exact False.elim ((by decide : (1 : Fin 3) ≠ 2)
      (False.elim (cross12 hEq.symm hj_zero hj0 hi0)))
  · rfl

end

/- accepted add_to_file helper 8 -/
noncomputable section

lemma msE_eventuallyZero_tail_eq {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) {i j : ℕ → Fin 3}
    (hEq : msE p₀ p₁ p₂ i = msE p₀ p₁ p₂ j)
    (hi_zero : msEventuallyZero i) (hj_zero : msEventuallyZero j) :
    msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) =
      msE p₀ p₁ p₂ (fun k ↦ j (k + 1)) := by
  have hhead := msE_eventuallyZero_head_eq hp₀ hp₁ hp₂ hsum hEq hi_zero hj_zero
  have hrec_i := msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum i
  have hrec_j := msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum j
  rw [hhead] at hrec_i
  have hpos := msP_pos hp₀ hp₁ hp₂ (j 0)
  have hmul :
      msP p₀ p₁ p₂ (j 0) * msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) =
        msP p₀ p₁ p₂ (j 0) * msE p₀ p₁ p₂ (fun k ↦ j (k + 1)) := by
    linarith
  exact mul_left_cancel₀ (ne_of_gt hpos) hmul

lemma msE_eventuallyZero_injective {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) :
    ∀ k : ℕ, ∀ i j : ℕ → Fin 3,
      msE p₀ p₁ p₂ i = msE p₀ p₁ p₂ j →
      msEventuallyZero i → msEventuallyZero j → i k = j k := by
  intro k
  induction k with
  | zero =>
      intro i j hEq hi hj
      exact msE_eventuallyZero_head_eq hp₀ hp₁ hp₂ hsum hEq hi hj
  | succ k ih =>
      intro i j hEq hi hj
      exact ih (fun n ↦ i (n + 1)) (fun n ↦ j (n + 1))
        (msE_eventuallyZero_tail_eq hp₀ hp₁ hp₂ hsum hEq hi hj)
        hi.tail hj.tail

end

/- accepted add_to_file helper 9 -/
noncomputable section

def msDigit (p₀ p₁ : ℝ) (x : ℝ) : Fin 3 :=
  if x < p₀ then 0 else if x < p₀ + p₁ then 1 else 2

def msTail (p₀ p₁ p₂ : ℝ) (x : ℝ) : ℝ :=
  (x - msB p₀ p₁ p₂ (msDigit p₀ p₁ x)) /
    msP p₀ p₁ p₂ (msDigit p₀ p₁ x)

def msTailIter (p₀ p₁ p₂ : ℝ) : ℕ → ℝ → ℝ
  | 0, x => x
  | n + 1, x => msTailIter p₀ p₁ p₂ n (msTail p₀ p₁ p₂ x)

def msSeq (p₀ p₁ p₂ : ℝ) (x : ℝ) (n : ℕ) : Fin 3 :=
  msDigit p₀ p₁ (msTailIter p₀ p₁ p₂ n x)

lemma msSeq_zero (p₀ p₁ p₂ : ℝ) (x : ℝ) :
    msSeq p₀ p₁ p₂ x 0 = msDigit p₀ p₁ x := rfl

lemma msSeq_succ (p₀ p₁ p₂ : ℝ) (x : ℝ) (n : ℕ) :
    msSeq p₀ p₁ p₂ x (n + 1) = msSeq p₀ p₁ p₂ (msTail p₀ p₁ p₂ x) n := rfl

lemma msTailIter_succ (p₀ p₁ p₂ : ℝ) (x : ℝ) (n : ℕ) :
    msTailIter p₀ p₁ p₂ (n + 1) x =
      msTailIter p₀ p₁ p₂ n (msTail p₀ p₁ p₂ x) := rfl

lemma msTail_mem_Icc {p₀ p₁ p₂ x : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    msTail p₀ p₁ p₂ x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold msTail msDigit
  by_cases h0 : x < p₀
  · simp [h0, msB, msP]
    constructor
    · exact div_nonneg hx.1 hp₀.1.le
    · rw [div_le_one hp₀.1]
      exact h0.le
  · by_cases h1 : x < p₀ + p₁
    · simp [h0, h1, msB, msP]
      constructor
      · exact div_nonneg (sub_nonneg.mpr (le_of_not_gt h0)) hp₁.1.le
      · rw [div_le_one hp₁.1]
        linarith
    · simp [h0, h1, msB, msP]
      constructor
      · exact div_nonneg (sub_nonneg.mpr (le_of_not_gt h1)) hp₂.1.le
      · rw [div_le_one hp₂.1]
        have hx1 : x ≤ p₀ + p₁ + p₂ := by
          rw [hsum]
          exact hx.2
        linarith

lemma msTailIter_mem_Icc {p₀ p₁ p₂ x : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ n : ℕ, msTailIter p₀ p₁ p₂ n x ∈ Set.Icc (0 : ℝ) 1 := by
  intro n
  induction n generalizing x with
  | zero => exact hx
  | succ n ih =>
      exact ih (msTail_mem_Icc hp₀ hp₁ hp₂ hsum hx)

lemma ms_eq_beta_add_mul_tail {p₀ p₁ p₂ x : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1) :
    x = msB p₀ p₁ p₂ (msDigit p₀ p₁ x) +
      msP p₀ p₁ p₂ (msDigit p₀ p₁ x) * msTail p₀ p₁ p₂ x := by
  unfold msTail
  have hp : msP p₀ p₁ p₂ (msDigit p₀ p₁ x) ≠ 0 :=
    ne_of_gt (msP_pos hp₀ hp₁ hp₂ _)
  field_simp [hp]
  ring

end

/- accepted add_to_file helper 10 -/
noncomputable section

lemma ms_expansion {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) :
    ∀ n : ℕ, ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
      x = (∑ k ∈ Finset.range n,
          msB p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k) *
            ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x r)) +
        (∏ k ∈ Finset.range n, msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k)) *
          msTailIter p₀ p₁ p₂ n x := by
  intro n
  induction n with
  | zero =>
      intro x hx
      simp
      rfl
  | succ n ih =>
      intro x hx
      have htx : msTail p₀ p₁ p₂ x ∈ Set.Icc (0 : ℝ) 1 :=
        msTail_mem_Icc hp₀ hp₁ hp₂ hsum hx
      have htail := ih (msTail p₀ p₁ p₂ x) htx
      have hxeq := ms_eq_beta_add_mul_tail hp₀ hp₁ hp₂ (x := x)
      let S : ℝ := ∑ k ∈ Finset.range n,
        msB p₀ p₁ p₂ (msSeq p₀ p₁ p₂ (msTail p₀ p₁ p₂ x) k) *
          ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ (msTail p₀ p₁ p₂ x) r)
      let Q : ℝ := ∏ k ∈ Finset.range n,
        msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ (msTail p₀ p₁ p₂ x) k)
      have hsumshift :
          (∑ k ∈ Finset.range (n + 1),
            msB p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k) *
              ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x r)) =
            msB p₀ p₁ p₂ (msDigit p₀ p₁ x) +
              msP p₀ p₁ p₂ (msDigit p₀ p₁ x) * S := by
        dsimp [S]
        rw [msE_partial_succ (msSeq p₀ p₁ p₂ x) n]
        simp [msSeq_zero, msSeq_succ]
      have hprodshift :
          (∏ k ∈ Finset.range (n + 1),
            msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k)) =
            Q * msP p₀ p₁ p₂ (msDigit p₀ p₁ x) := by
        dsimp [Q]
        rw [Finset.prod_range_succ']
        simp [msSeq_zero, msSeq_succ]
      calc
        x = msB p₀ p₁ p₂ (msDigit p₀ p₁ x) +
            msP p₀ p₁ p₂ (msDigit p₀ p₁ x) * msTail p₀ p₁ p₂ x := hxeq
        _ = msB p₀ p₁ p₂ (msDigit p₀ p₁ x) +
            msP p₀ p₁ p₂ (msDigit p₀ p₁ x) *
              (S + Q * msTailIter p₀ p₁ p₂ n (msTail p₀ p₁ p₂ x)) := by
              dsimp [S, Q]
              nth_rewrite 1 [htail]
              rfl
        _ = (∑ k ∈ Finset.range (n + 1),
              msB p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k) *
                ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x r)) +
            (∏ k ∈ Finset.range (n + 1),
                msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k)) *
              msTailIter p₀ p₁ p₂ (n + 1) x := by
              rw [hsumshift, hprodshift]
              simp [msTailIter_succ]
              ring

end

/- accepted add_to_file helper 11 -/
noncomputable section

lemma msSeq_eval {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    msE p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x) = x := by
  let term : ℕ → ℝ := fun k ↦
    msB p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k) *
      ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x r)
  let rem : ℕ → ℝ := fun n ↦
    (∏ k ∈ Finset.range n, msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k)) *
      msTailIter p₀ p₁ p₂ n x
  let q := max p₀ (max p₁ p₂)
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact le_trans hp₀.1.le (le_max_left _ _)
  have hq_lt_one : q < 1 := by
    dsimp [q]
    exact max_lt hp₀.2 (max_lt hp₁.2 hp₂.2)
  have hp_le_q : ∀ n k : ℕ, k ∈ Finset.range n →
      msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k) ≤ q := by
    intro n k hk
    generalize hj : msSeq p₀ p₁ p₂ x k = j
    fin_cases j <;> simp [msP, q]
  have hrem_bound : ∀ n : ℕ, ‖rem n‖ ≤ q ^ n := by
    intro n
    have hprod_nonneg : 0 ≤ ∏ k ∈ Finset.range n,
        msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k) :=
      Finset.prod_nonneg fun k _ => msP_nonneg hp₀ hp₁ hp₂ _
    have hprod_le : (∏ k ∈ Finset.range n,
        msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k)) ≤ q ^ n := by
      calc
        (∏ k ∈ Finset.range n, msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k)) ≤
            ∏ k ∈ Finset.range n, q :=
          Finset.prod_le_prod
            (fun k _ => msP_nonneg hp₀ hp₁ hp₂ _)
            (fun k hk => hp_le_q n k hk)
        _ = q ^ n := by simp
    have hiter_abs : |msTailIter p₀ p₁ p₂ n x| ≤ 1 := by
      have hmem := msTailIter_mem_Icc hp₀ hp₁ hp₂ hsum hx n
      exact abs_le.mpr ⟨by linarith [hmem.1], hmem.2⟩
    calc
      ‖rem n‖ = |(∏ k ∈ Finset.range n,
          msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k)) *
        msTailIter p₀ p₁ p₂ n x| := by rfl
      _ = |(∏ k ∈ Finset.range n,
          msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k))| *
          |msTailIter p₀ p₁ p₂ n x| := abs_mul _ _
      _ = (∏ k ∈ Finset.range n,
          msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k)) *
          |msTailIter p₀ p₁ p₂ n x| := by rw [abs_of_nonneg hprod_nonneg]
      _ ≤ q ^ n * 1 := mul_le_mul hprod_le hiter_abs (abs_nonneg _) (pow_nonneg hq_nonneg _)
      _ = q ^ n := by ring
  have hrem_tendsto : Filter.Tendsto rem Filter.atTop (nhds 0) :=
    squeeze_zero_norm hrem_bound (tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt_one)
  have hpartial_tendsto : Filter.Tendsto
      (fun n ↦ ∑ k ∈ Finset.range n, term k) Filter.atTop (nhds x) := by
    have hsub := (tendsto_const_nhds (x := x)).sub hrem_tendsto
    have hfun : (fun n ↦ ∑ k ∈ Finset.range n, term k) = fun n ↦ x - rem n := by
      funext n
      have hexp := ms_expansion hp₀ hp₁ hp₂ hsum n x hx
      dsimp [term, rem]
      linarith
    rw [hfun]
    simpa using hsub
  have hE_tendsto : Filter.Tendsto
      (fun n ↦ ∑ k ∈ Finset.range n, term k) Filter.atTop
      (nhds (msE p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x))) := by
    have hs := msE_summable hp₀ hp₁ hp₂ hsum (msSeq p₀ p₁ p₂ x)
    exact hs.hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique hE_tendsto hpartial_tendsto

end

/- accepted add_to_file helper 12 -/
noncomputable section

def msSuffix (i : ℕ → Fin 3) (k n : ℕ) : Fin 3 := i (k + n)

lemma msSuffix_zero (i : ℕ → Fin 3) : msSuffix i 0 = i := by
  funext n
  simp [msSuffix]

lemma msE_decompose {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) :
    ∀ k : ℕ, ∀ i : ℕ → Fin 3,
      msE p₀ p₁ p₂ i =
        (∑ r ∈ Finset.range k,
          msB p₀ p₁ p₂ (i r) * ∏ s ∈ Finset.range r, msP p₀ p₁ p₂ (i s)) +
        (∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i r)) *
          msE p₀ p₁ p₂ (msSuffix i k) := by
  intro k
  induction k with
  | zero =>
      intro i
      simp
      rw [msSuffix_zero]
  | succ k ih =>
      intro i
      have hrec := msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum i
      have htail := ih (fun n ↦ i (n + 1))
      have hsuffix : msSuffix (fun n ↦ i (n + 1)) k = msSuffix i (k + 1) := by
        funext n
        dsimp [msSuffix]
        congr 1
        omega
      rw [hrec, htail, hsuffix]
      rw [msE_partial_succ i k]
      rw [Finset.prod_range_succ']
      ring

end

/- accepted add_to_file helper 13 -/
noncomputable section

lemma msE_suffix_eq_of_prefix {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) {i j : ℕ → Fin 3} {k : ℕ}
    (hEq : msE p₀ p₁ p₂ i = msE p₀ p₁ p₂ j)
    (hprefix : ∀ r : ℕ, r < k → i r = j r) :
    msE p₀ p₁ p₂ (msSuffix i k) = msE p₀ p₁ p₂ (msSuffix j k) := by
  have hpartial :
      (∑ r ∈ Finset.range k,
        msB p₀ p₁ p₂ (i r) * ∏ s ∈ Finset.range r, msP p₀ p₁ p₂ (i s)) =
      ∑ r ∈ Finset.range k,
        msB p₀ p₁ p₂ (j r) * ∏ s ∈ Finset.range r, msP p₀ p₁ p₂ (j s) := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    have hrr : r < k := Finset.mem_range.mp hr
    have hprod_inner :
        (∏ s ∈ Finset.range r, msP p₀ p₁ p₂ (i s)) =
          ∏ s ∈ Finset.range r, msP p₀ p₁ p₂ (j s) := by
      refine Finset.prod_congr rfl ?_
      intro s hs
      exact congrArg (msP p₀ p₁ p₂)
        (hprefix s (lt_trans (Finset.mem_range.mp hs) hrr))
    rw [hprefix r hrr, hprod_inner]
  have hprod :
      (∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i r)) =
        ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (j r) := by
    refine Finset.prod_congr rfl ?_
    intro r hr
    exact congrArg (msP p₀ p₁ p₂) (hprefix r (Finset.mem_range.mp hr))
  have hdec_i := msE_decompose hp₀ hp₁ hp₂ hsum k i
  have hdec_j := msE_decompose hp₀ hp₁ hp₂ hsum k j
  have hdec_i' :
      msE p₀ p₁ p₂ i =
        (∑ r ∈ Finset.range k,
          msB p₀ p₁ p₂ (j r) * ∏ s ∈ Finset.range r, msP p₀ p₁ p₂ (j s)) +
        (∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (j r)) *
          msE p₀ p₁ p₂ (msSuffix i k) := by
    rw [hdec_i, hpartial, hprod]
  have hPpos : 0 < ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (j r) :=
    Finset.prod_pos fun r _ => msP_pos hp₀ hp₁ hp₂ _
  have hmul :
      (∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (j r)) *
          msE p₀ p₁ p₂ (msSuffix i k) =
        (∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (j r)) *
          msE p₀ p₁ p₂ (msSuffix j k) := by
    linarith
  exact mul_left_cancel₀ (ne_of_gt hPpos) hmul

end

/- accepted add_to_file helper 14 -/
noncomputable section

lemma msTailIter_add (p₀ p₁ p₂ : ℝ) (k n : ℕ) (x : ℝ) :
    msTailIter p₀ p₁ p₂ (k + n) x =
      msTailIter p₀ p₁ p₂ n (msTailIter p₀ p₁ p₂ k x) := by
  induction k generalizing x with
  | zero =>
      simp [msTailIter]
  | succ k ih =>
      calc
        msTailIter p₀ p₁ p₂ (k + 1 + n) x
            = msTailIter p₀ p₁ p₂ (k + n + 1) x := by rw [Nat.succ_add]
        _ = msTailIter p₀ p₁ p₂ (k + n) (msTail p₀ p₁ p₂ x) := rfl
        _ = msTailIter p₀ p₁ p₂ n
              (msTailIter p₀ p₁ p₂ k (msTail p₀ p₁ p₂ x)) := ih _
        _ = msTailIter p₀ p₁ p₂ n
              (msTailIter p₀ p₁ p₂ (k + 1) x) := rfl

lemma msDigit_eq_zero_imp_lt {p₀ p₁ x : ℝ}
    (h : msDigit p₀ p₁ x = 0) : x < p₀ := by
  unfold msDigit at h
  by_cases h0 : x < p₀
  · exact h0
  · by_cases h1 : x < p₀ + p₁
    · simp [h0, h1] at h
    · simp [h0, h1] at h

lemma msDigit_eq_one_imp {p₀ p₁ x : ℝ}
    (h : msDigit p₀ p₁ x = 1) : p₀ ≤ x ∧ x < p₀ + p₁ := by
  unfold msDigit at h
  by_cases h0 : x < p₀
  · simp [h0] at h
  · by_cases h1 : x < p₀ + p₁
    · exact ⟨le_of_not_gt h0, h1⟩
    · simp [h0, h1] at h

lemma msDigit_eq_two_imp {p₀ p₁ x : ℝ}
    (h : msDigit p₀ p₁ x = 2) : p₀ + p₁ ≤ x := by
  unfold msDigit at h
  by_cases h0 : x < p₀
  · simp [h0] at h
  · by_cases h1 : x < p₀ + p₁
    · simp [h0, h1] at h
    · exact le_of_not_gt h1

end

/- accepted add_to_file helper 15 -/
noncomputable section

lemma msSeq_eventuallyZero_of_head_ne {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) {a b : ℕ → Fin 3} {y : ℝ}
    (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hb : b = msSeq p₀ p₁ p₂ y)
    (hEq : msE p₀ p₁ p₂ a = msE p₀ p₁ p₂ b)
    (hne : a 0 ≠ b 0) :
    msEventuallyZero b := by
  have hEb : msE p₀ p₁ p₂ b = y := by
    rw [hb]
    exact msSeq_eval hp₀ hp₁ hp₂ hsum hy
  have hb0 : b 0 = msDigit p₀ p₁ y := by
    rw [hb]
    rfl
  generalize ha0 : a 0 = A
  generalize hb0v : b 0 = B
  fin_cases B <;> fin_cases A
  · exact False.elim (hne (by rw [ha0, hb0v]))
  · have hdigit : msDigit p₀ p₁ y = 0 := by
      rw [← hb0]
      exact hb0v
    have hyb := msDigit_eq_zero_imp_lt hdigit
    have ha_lower : p₀ ≤ msE p₀ p₁ p₂ a := by
      have h := msE_head_lower hp₀ hp₁ hp₂ hsum a
      rw [ha0] at h
      simpa [msB, msP] using h
    have ha_y : msE p₀ p₁ p₂ a = y := by rw [hEq, hEb]
    linarith
  · have hdigit : msDigit p₀ p₁ y = 0 := by
      rw [← hb0]
      exact hb0v
    have hyb := msDigit_eq_zero_imp_lt hdigit
    have ha_lower : p₀ + p₁ ≤ msE p₀ p₁ p₂ a := by
      have h := msE_head_lower hp₀ hp₁ hp₂ hsum a
      rw [ha0] at h
      simpa [msB, msP] using h
    have ha_y : msE p₀ p₁ p₂ a = y := by rw [hEq, hEb]
    linarith [hp₁.1]
  · have hdigit : msDigit p₀ p₁ y = 1 := by
      rw [← hb0]
      exact hb0v
    have hyb := msDigit_eq_one_imp hdigit
    have ha_upper : msE p₀ p₁ p₂ a ≤ p₀ := by
      have h := msE_head_upper hp₀ hp₁ hp₂ hsum a
      rw [ha0] at h
      simpa [msB, msP] using h
    have hy_eq : y = p₀ := by
      have ha_y : msE p₀ p₁ p₂ a = y := by rw [hEq, hEb]
      linarith [hyb.1]
    have hb_eq : msE p₀ p₁ p₂ b = p₀ := by rw [hEb, hy_eq]
    have hbrec := msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum b
    rw [hb0v] at hbrec
    simp [msB, msP] at hbrec
    rw [hb_eq] at hbrec
    have htail_zero : msE p₀ p₁ p₂ (fun k ↦ b (k + 1)) = 0 := by
      have hmul : p₁ * msE p₀ p₁ p₂ (fun k ↦ b (k + 1)) = 0 := by
        linarith
      rcases mul_eq_zero.mp hmul with hp | ht
      · linarith [hp₁.1]
      · exact ht
    refine ⟨1, ?_⟩
    intro n hn
    cases n with
    | zero => omega
    | succ m =>
        exact msE_eq_zero_apply hp₀ hp₁ hp₂ hsum m
          (fun k ↦ b (k + 1)) htail_zero
  · exact False.elim (hne (by rw [ha0, hb0v]))
  · have hdigit : msDigit p₀ p₁ y = 1 := by
      rw [← hb0]
      exact hb0v
    have hyb := msDigit_eq_one_imp hdigit
    have ha_lower : p₀ + p₁ ≤ msE p₀ p₁ p₂ a := by
      have h := msE_head_lower hp₀ hp₁ hp₂ hsum a
      rw [ha0] at h
      simpa [msB, msP] using h
    have ha_y : msE p₀ p₁ p₂ a = y := by rw [hEq, hEb]
    linarith
  · have hdigit : msDigit p₀ p₁ y = 2 := by
      rw [← hb0]
      exact hb0v
    have hyb := msDigit_eq_two_imp hdigit
    have ha_upper : msE p₀ p₁ p₂ a ≤ p₀ := by
      have h := msE_head_upper hp₀ hp₁ hp₂ hsum a
      rw [ha0] at h
      simpa [msB, msP] using h
    have ha_y : msE p₀ p₁ p₂ a = y := by rw [hEq, hEb]
    linarith [hp₁.1]
  · have hdigit : msDigit p₀ p₁ y = 2 := by
      rw [← hb0]
      exact hb0v
    have hyb := msDigit_eq_two_imp hdigit
    have ha_upper : msE p₀ p₁ p₂ a ≤ p₀ + p₁ := by
      have h := msE_head_upper hp₀ hp₁ hp₂ hsum a
      rw [ha0] at h
      simpa [msB, msP] using h
    have hy_eq : y = p₀ + p₁ := by
      have ha_y : msE p₀ p₁ p₂ a = y := by rw [hEq, hEb]
      linarith [hyb]
    have hb_eq : msE p₀ p₁ p₂ b = p₀ + p₁ := by rw [hEb, hy_eq]
    have hbrec := msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum b
    rw [hb0v] at hbrec
    simp [msB, msP] at hbrec
    rw [hb_eq] at hbrec
    have htail_zero : msE p₀ p₁ p₂ (fun k ↦ b (k + 1)) = 0 := by
      have hmul : p₂ * msE p₀ p₁ p₂ (fun k ↦ b (k + 1)) = 0 := by
        linarith
      rcases mul_eq_zero.mp hmul with hp | ht
      · linarith [hp₂.1]
      · exact ht
    refine ⟨1, ?_⟩
    intro n hn
    cases n with
    | zero => omega
    | succ m =>
        exact msE_eq_zero_apply hp₀ hp₁ hp₂ hsum m
          (fun k ↦ b (k + 1)) htail_zero
  · exact False.elim (hne (by rw [ha0, hb0v]))

end

/- accepted add_to_file helper 16 -/
noncomputable section

lemma msSeq_eventuallyZero_of_exists_ne {p₀ p₁ p₂ x : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {j : ℕ → Fin 3} (hj : msE p₀ p₁ p₂ j = x)
    (hne : j ≠ msSeq p₀ p₁ p₂ x) :
    msEventuallyZero (msSeq p₀ p₁ p₂ x) := by
  let s : ℕ → Fin 3 := msSeq p₀ p₁ p₂ x
  have hs : msE p₀ p₁ p₂ s = x := msSeq_eval hp₀ hp₁ hp₂ hsum hx
  have hex : ∃ k : ℕ, j k ≠ s k := by
    by_contra hnone
    apply hne
    funext k
    by_contra hk
    exact hnone ⟨k, hk⟩
  let k : ℕ := Nat.find hex
  have hk_ne : j k ≠ s k := Nat.find_spec hex
  have hprefix : ∀ r : ℕ, r < k → j r = s r := by
    intro r hr
    have hnot := Nat.find_min hex hr
    by_contra hdiff
    exact hnot hdiff
  have hEq : msE p₀ p₁ p₂ j = msE p₀ p₁ p₂ s := by rw [hj, hs]
  have hsuffix_E :
      msE p₀ p₁ p₂ (msSuffix j k) = msE p₀ p₁ p₂ (msSuffix s k) :=
    msE_suffix_eq_of_prefix hp₀ hp₁ hp₂ hsum hEq hprefix
  let y : ℝ := msTailIter p₀ p₁ p₂ k x
  have hy : y ∈ Set.Icc (0 : ℝ) 1 :=
    msTailIter_mem_Icc hp₀ hp₁ hp₂ hsum hx k
  have hb : msSuffix s k = msSeq p₀ p₁ p₂ y := by
    funext n
    dsimp [msSuffix, s, msSeq, y]
    rw [msTailIter_add]
  have hhead_ne : msSuffix j k 0 ≠ msSuffix s k 0 := by
    dsimp [msSuffix]
    simpa using hk_ne
  have hsuffix_zero := msSeq_eventuallyZero_of_head_ne hp₀ hp₁ hp₂ hsum hy hb
    hsuffix_E hhead_ne
  rcases hsuffix_zero with ⟨N, hN⟩
  refine ⟨k + N, ?_⟩
  intro m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  have h := hN (N + d) (Nat.le_add_right N d)
  dsimp [msSuffix, s] at h
  simpa [Nat.add_assoc] using h

end

/- accepted add_to_file helper 17 -/
noncomputable section

def msCanonical (p₀ p₁ p₂ : ℝ) (x : ℝ) : ℕ → Fin 3 :=
  Classical.epsilon fun i ↦
    msE p₀ p₁ p₂ i = x ∧
      ((∃ j, msE p₀ p₁ p₂ j = x ∧ j ≠ i) → msEventuallyZero i)

lemma msCanonical_spec {p₀ p₁ p₂ x : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    msE p₀ p₁ p₂ (msCanonical p₀ p₁ p₂ x) = x ∧
      ((∃ j, msE p₀ p₁ p₂ j = x ∧ j ≠ msCanonical p₀ p₁ p₂ x) →
        msEventuallyZero (msCanonical p₀ p₁ p₂ x)) := by
  dsimp [msCanonical]
  let P : (ℕ → Fin 3) → Prop := fun i ↦
    msE p₀ p₁ p₂ i = x ∧
      ((∃ j, msE p₀ p₁ p₂ j = x ∧ j ≠ i) → msEventuallyZero i)
  have hex : ∃ i, P i := by
    refine ⟨msSeq p₀ p₁ p₂ x, msSeq_eval hp₀ hp₁ hp₂ hsum hx, ?_⟩
    rintro ⟨j, hj, hjne⟩
    exact msSeq_eventuallyZero_of_exists_ne hp₀ hp₁ hp₂ hsum hx hj hjne
  have h := Classical.epsilon_spec (p := P) hex
  dsimp [P] at h
  exact h

lemma msCanonical_eq_msSeq {p₀ p₁ p₂ x : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    msCanonical p₀ p₁ p₂ x = msSeq p₀ p₁ p₂ x := by
  have hc := msCanonical_spec hp₀ hp₁ hp₂ hsum hx
  have hs : msE p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x) = x :=
    msSeq_eval hp₀ hp₁ hp₂ hsum hx
  by_contra hne
  have hsc : msSeq p₀ p₁ p₂ x ≠ msCanonical p₀ p₁ p₂ x := by
    intro h
    exact hne h.symm
  have hc_zero : msEventuallyZero (msCanonical p₀ p₁ p₂ x) :=
    hc.2 ⟨msSeq p₀ p₁ p₂ x, hs, hsc⟩
  have hs_zero : msEventuallyZero (msSeq p₀ p₁ p₂ x) :=
    msSeq_eventuallyZero_of_exists_ne hp₀ hp₁ hp₂ hsum hx hc.1 hne
  have hcoords : ∀ k : ℕ,
      msCanonical p₀ p₁ p₂ x k = msSeq p₀ p₁ p₂ x k := by
    intro k
    exact msE_eventuallyZero_injective hp₀ hp₁ hp₂ hsum k
      (msCanonical p₀ p₁ p₂ x) (msSeq p₀ p₁ p₂ x)
      (by rw [hc.1, hs]) hc_zero hs_zero
  exact hne (funext hcoords)

end

/- accepted add_to_file helper 18 -/
noncomputable section

lemma measurable_msDigit (p₀ p₁ : ℝ) : Measurable (msDigit p₀ p₁) := by
  unfold msDigit
  refine Measurable.piecewise
    (measurableSet_lt measurable_id measurable_const) measurable_const ?_
  exact Measurable.piecewise
    (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const

lemma measurable_msTail (p₀ p₁ p₂ : ℝ) : Measurable (msTail p₀ p₁ p₂) := by
  have hd := measurable_msDigit p₀ p₁
  have hB : Measurable fun x ↦ msB p₀ p₁ p₂ (msDigit p₀ p₁ x) :=
    (measurable_of_finite (msB p₀ p₁ p₂)).comp hd
  have hP : Measurable fun x ↦ msP p₀ p₁ p₂ (msDigit p₀ p₁ x) :=
    (measurable_of_finite (msP p₀ p₁ p₂)).comp hd
  exact (measurable_id.sub hB).div hP

lemma measurable_msTailIter (p₀ p₁ p₂ : ℝ) (n : ℕ) :
    Measurable fun x ↦ msTailIter p₀ p₁ p₂ n x := by
  induction n with
  | zero =>
      simpa [msTailIter] using measurable_id
  | succ n ih =>
      simpa [msTailIter] using ih.comp (measurable_msTail p₀ p₁ p₂)

lemma measurable_msSeq (p₀ p₁ p₂ : ℝ) (n : ℕ) :
    Measurable fun x ↦ msSeq p₀ p₁ p₂ x n := by
  unfold msSeq
  exact (measurable_msDigit p₀ p₁).comp (measurable_msTailIter p₀ p₁ p₂ n)

def msG (p₀ p₁ p₂ : ℝ) (x : ℝ) : ℝ :=
  msE p₀ p₁ p₂ (fun k ↦ msTheta (msSeq p₀ p₁ p₂ x k))

lemma measurable_msG {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) : Measurable (msG p₀ p₁ p₂) := by
  let term : ℕ → ℝ → ℝ := fun k x ↦
    msB p₀ p₁ p₂ (msTheta (msSeq p₀ p₁ p₂ x k)) *
      ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (msTheta (msSeq p₀ p₁ p₂ x r))
  have hterm : ∀ k : ℕ, Measurable (term k) := by
    intro k
    have hB : Measurable fun x ↦
        msB p₀ p₁ p₂ (msTheta (msSeq p₀ p₁ p₂ x k)) := by
      exact (measurable_of_finite (fun j ↦ msB p₀ p₁ p₂ (msTheta j))).comp
        (measurable_msSeq p₀ p₁ p₂ k)
    have hP : Measurable fun x ↦
        ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (msTheta (msSeq p₀ p₁ p₂ x r)) := by
      refine Finset.measurable_prod (Finset.range k) ?_
      intro r hr
      exact (measurable_of_finite (fun j ↦ msP p₀ p₁ p₂ (msTheta j))).comp
        (measurable_msSeq p₀ p₁ p₂ r)
    exact hB.mul hP
  have hpartial : ∀ n : ℕ,
      Measurable fun x ↦ ∑ k ∈ Finset.range n, term k x := by
    intro n
    exact Finset.measurable_sum (Finset.range n) fun k _ => hterm k
  have hlim : Filter.Tendsto
      (fun n x ↦ ∑ k ∈ Finset.range n, term k x) Filter.atTop
      (nhds (msG p₀ p₁ p₂)) := by
    rw [tendsto_pi_nhds]
    intro x
    have hs : Summable fun k ↦ term k x := by
      dsimp [term]
      exact msE_summable hp₀ hp₁ hp₂ hsum
        (fun k ↦ msTheta (msSeq p₀ p₁ p₂ x k))
    have h := hs.hasSum.tendsto_sum_nat
    dsimp [msG, msE, term]
    exact h
  exact measurable_of_tendsto_metrizable hpartial hlim

end

/- accepted add_to_file helper 19 -/
noncomputable section

lemma msDigit_map0 {p₀ p₁ y : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1) (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    msDigit p₀ p₁ (p₀ * y) = 0 := by
  unfold msDigit
  rw [if_pos (mul_lt_of_lt_one_right hp₀.1 hy.2)]

lemma msTail_map0 {p₀ p₁ p₂ y : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1) (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    msTail p₀ p₁ p₂ (p₀ * y) = y := by
  unfold msTail
  rw [msDigit_map0 hp₀ hy]
  simp [msB, msP]
  field_simp [ne_of_gt hp₀.1]

lemma msDigit_map1 {p₀ p₁ y : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1) (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    msDigit p₀ p₁ (p₀ + p₁ * y) = 1 := by
  have hnot0 : ¬ p₀ + p₁ * y < p₀ := by
    have hnonneg : 0 ≤ p₁ * y := mul_nonneg hp₁.1.le hy.1
    linarith
  have hlt : p₀ + p₁ * y < p₀ + p₁ := by
    have h := mul_lt_of_lt_one_right hp₁.1 hy.2
    linarith
  unfold msDigit
  rw [if_neg hnot0, if_pos hlt]

lemma msTail_map1 {p₀ p₁ p₂ y : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1) (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    msTail p₀ p₁ p₂ (p₀ + p₁ * y) = y := by
  unfold msTail
  rw [msDigit_map1 hp₀ hp₁ hy]
  simp [msB, msP]
  field_simp [ne_of_gt hp₁.1]

lemma msDigit_map2 {p₀ p₁ p₂ y : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    msDigit p₀ p₁ (p₀ + p₁ + p₂ * y) = 2 := by
  have hnot0 : ¬ p₀ + p₁ + p₂ * y < p₀ := by
    have h : p₁ ≤ p₁ + p₂ * y := by
      have hnonneg : 0 ≤ p₂ * y := mul_nonneg hp₂.1.le hy.1
      linarith
    linarith [hp₁.1]
  have hnot1 : ¬ p₀ + p₁ + p₂ * y < p₀ + p₁ := by
    have hnonneg : 0 ≤ p₂ * y := mul_nonneg hp₂.1.le hy.1
    linarith
  unfold msDigit
  rw [if_neg hnot0, if_neg hnot1]

lemma msTail_map2 {p₀ p₁ p₂ y : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    msTail p₀ p₁ p₂ (p₀ + p₁ + p₂ * y) = y := by
  unfold msTail
  rw [msDigit_map2 hp₀ hp₁ hp₂ hsum hy]
  simp [msB, msP]
  field_simp [ne_of_gt hp₂.1]

end

/- accepted add_to_file helper 20 -/
noncomputable section

lemma msG_eq_of_digit_tail {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) {x y : ℝ} {a : Fin 3}
    (hdigit : msDigit p₀ p₁ x = a)
    (htail : msTail p₀ p₁ p₂ x = y) :
    msG p₀ p₁ p₂ x =
      msB p₀ p₁ p₂ (msTheta a) +
        msP p₀ p₁ p₂ (msTheta a) * msG p₀ p₁ p₂ y := by
  unfold msG
  have hrec := msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum
    (fun k ↦ msTheta (msSeq p₀ p₁ p₂ x k))
  have htailseq :
      (fun k ↦ msTheta (msSeq p₀ p₁ p₂ x (k + 1))) =
        fun k ↦ msTheta (msSeq p₀ p₁ p₂ y k) := by
    funext k
    rw [msSeq_succ, htail]
  have hhead : msSeq p₀ p₁ p₂ x 0 = a := by
    rw [msSeq_zero, hdigit]
  rw [hrec, hhead, htailseq]

lemma msG_map0 {p₀ p₁ p₂ y : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    msG p₀ p₁ p₂ (p₀ * y) = p₀ * msG p₀ p₁ p₂ y := by
  have h := msG_eq_of_digit_tail hp₀ hp₁ hp₂ hsum
    (msDigit_map0 hp₀ hy) (msTail_map0 hp₀ hy)
  simpa [msTheta, msB, msP] using h

lemma msG_map1 {p₀ p₁ p₂ y : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    msG p₀ p₁ p₂ (p₀ + p₁ * y) =
      p₀ + p₁ + p₂ * msG p₀ p₁ p₂ y := by
  have h := msG_eq_of_digit_tail hp₀ hp₁ hp₂ hsum
    (msDigit_map1 hp₀ hp₁ hy) (msTail_map1 hp₀ hp₁ hy)
  simpa [msTheta, msB, msP] using h

lemma msG_map2 {p₀ p₁ p₂ y : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    msG p₀ p₁ p₂ (p₀ + p₁ + p₂ * y) =
      p₀ + p₁ * msG p₀ p₁ p₂ y := by
  have h := msG_eq_of_digit_tail hp₀ hp₁ hp₂ hsum
    (msDigit_map2 hp₀ hp₁ hp₂ hsum hy) (msTail_map2 hp₀ hp₁ hp₂ hsum hy)
  simpa [msTheta, msB, msP] using h

end

/- accepted add_to_file helper 21 -/
noncomputable section

lemma msG_mem_Icc {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (x : ℝ) :
    msG p₀ p₁ p₂ x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold msG
  exact msE_mem_Icc hp₀ hp₁ hp₂ hsum _

end

/- accepted add_to_file helper 22 -/
noncomputable section

lemma msG_integrableOn_Icc {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (a b : ℝ) :
    MeasureTheory.IntegrableOn (msG p₀ p₁ p₂) (Set.Icc a b) MeasureTheory.volume := by
  have hmeas : MeasureTheory.AEStronglyMeasurable (msG p₀ p₁ p₂)
      (MeasureTheory.volume.restrict (Set.Icc a b)) :=
    (measurable_msG hp₀ hp₁ hp₂ hsum).aestronglyMeasurable
  have hbound : ∀ᵐ (x : ℝ) ∂(MeasureTheory.volume.restrict (Set.Icc a b)),
      ‖msG p₀ p₁ p₂ x‖ ≤ 1 := by
    refine Filter.Eventually.of_forall fun x ↦ ?_
    have hmem := msG_mem_Icc hp₀ hp₁ hp₂ hsum x
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hmem.1], hmem.2⟩
  exact MeasureTheory.IntegrableOn.of_bound measure_Icc_lt_top hmeas 1 hbound

end

/- accepted add_to_file helper 23 -/
noncomputable section

lemma msG_intervalIntegrable {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (msG p₀ p₁ p₂) MeasureTheory.volume a b := by
  unfold IntervalIntegrable
  constructor
  · exact (msG_integrableOn_Icc hp₀ hp₁ hp₂ hsum a b).mono_set
      Set.Ioc_subset_Icc_self
  · rw [Set.Ioc_eq_empty (not_lt.mpr hab)]
    exact MeasureTheory.integrableOn_empty

end

/- accepted add_to_file helper 24 -/
noncomputable section

lemma msG_integral_segment0 {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) :
    (∫ x in (0 : ℝ)..p₀, msG p₀ p₁ p₂ x) =
      p₀ ^ 2 * ∫ x in (0 : ℝ)..1, msG p₀ p₁ p₂ x := by
  let g := msG p₀ p₁ p₂
  let I0 := ∫ x in (0 : ℝ)..p₀, g x
  let J := ∫ x in (0 : ℝ)..1, g x
  have hcongr : (∫ y in (0 : ℝ)..1, g (p₀ * y)) = p₀ * J := by
    have hae : ∀ᵐ y ∂MeasureTheory.volume,
        y ∈ Set.uIoc (0 : ℝ) 1 → g (p₀ * y) = p₀ * g y := by
      rw [MeasureTheory.ae_iff]
      apply MeasureTheory.measure_mono_null ?_ (Real.volume_singleton (a := (1 : ℝ)))
      intro y hybad
      by_contra hyne
      have hcond : y ∈ Set.uIoc (0 : ℝ) 1 → g (p₀ * y) = p₀ * g y := by
        intro hy
        have hyIoc : y ∈ Set.Ioc (0 : ℝ) 1 := by
          simpa [Set.uIoc_of_le zero_le_one] using hy
        have hyIco : y ∈ Set.Ico (0 : ℝ) 1 :=
          ⟨hyIoc.1.le, lt_of_le_of_ne hyIoc.2 hyne⟩
        exact msG_map0 hp₀ hp₁ hp₂ hsum hyIco
      exact hybad hcond
    have h := intervalIntegral.integral_congr_ae hae
    calc
      (∫ y in (0 : ℝ)..1, g (p₀ * y)) =
          ∫ y in (0 : ℝ)..1, p₀ * g y := h
      _ = p₀ * J := by
          dsimp [J]
          exact intervalIntegral.integral_const_mul p₀ g
  have hsubst : (∫ y in (0 : ℝ)..1, g (p₀ * y)) = p₀⁻¹ * I0 := by
    have h := intervalIntegral.integral_comp_mul_left
      (a := (0 : ℝ)) (b := (1 : ℝ)) (c := p₀) g (ne_of_gt hp₀.1)
    dsimp [I0]
    simpa using h
  have hpne : p₀ ≠ 0 := ne_of_gt hp₀.1
  have hcalc : p₀⁻¹ * I0 = p₀ * J := by
    rw [← hsubst, hcongr]
  calc
    (∫ x in (0 : ℝ)..p₀, msG p₀ p₁ p₂ x) = I0 := rfl
    _ = p₀ * (p₀⁻¹ * I0) := by field_simp [hpne]
    _ = p₀ * (p₀ * J) := by rw [hcalc]
    _ = p₀ ^ 2 * ∫ x in (0 : ℝ)..1, msG p₀ p₁ p₂ x := by
        dsimp [J, g]
        ring

end

/- accepted add_to_file helper 25 -/
noncomputable section

lemma msG_integral_segment1 {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) :
    (∫ x in p₀..(p₀ + p₁), msG p₀ p₁ p₂ x) =
      p₁ * (p₀ + p₁ + p₂ * ∫ x in (0 : ℝ)..1, msG p₀ p₁ p₂ x) := by
  let g := msG p₀ p₁ p₂
  let I1 := ∫ x in p₀..(p₀ + p₁), g x
  let J := ∫ x in (0 : ℝ)..1, g x
  have hcongr : (∫ y in (0 : ℝ)..1, g (p₀ + p₁ * y)) =
      p₀ + p₁ + p₂ * J := by
    have hae : ∀ᵐ y ∂MeasureTheory.volume,
        y ∈ Set.uIoc (0 : ℝ) 1 →
          g (p₀ + p₁ * y) = p₀ + p₁ + p₂ * g y := by
      rw [MeasureTheory.ae_iff]
      apply MeasureTheory.measure_mono_null ?_ (Real.volume_singleton (a := (1 : ℝ)))
      intro y hybad
      by_contra hyne
      have hcond : y ∈ Set.uIoc (0 : ℝ) 1 →
          g (p₀ + p₁ * y) = p₀ + p₁ + p₂ * g y := by
        intro hy
        have hyIoc : y ∈ Set.Ioc (0 : ℝ) 1 := by
          simpa [Set.uIoc_of_le zero_le_one] using hy
        have hyIco : y ∈ Set.Ico (0 : ℝ) 1 :=
          ⟨hyIoc.1.le, lt_of_le_of_ne hyIoc.2 hyne⟩
        exact msG_map1 hp₀ hp₁ hp₂ hsum hyIco
      exact hybad hcond
    have h := intervalIntegral.integral_congr_ae hae
    have hgint := msG_intervalIntegrable hp₀ hp₁ hp₂ hsum (a := (0 : ℝ)) (b := 1)
      zero_le_one
    calc
      (∫ y in (0 : ℝ)..1, g (p₀ + p₁ * y)) =
          ∫ y in (0 : ℝ)..1, (fun _ ↦ p₀ + p₁) y + p₂ * g y := h
      _ = (∫ y in (0 : ℝ)..1, (fun _ ↦ p₀ + p₁) y) +
          ∫ y in (0 : ℝ)..1, p₂ * g y :=
        intervalIntegral.integral_add intervalIntegrable_const (hgint.const_mul p₂)
      _ = p₀ + p₁ + p₂ * J := by
        rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
        dsimp [J]
        simp
  have hsubst : (∫ y in (0 : ℝ)..1, g (p₀ + p₁ * y)) = p₁⁻¹ * I1 := by
    have hmul := intervalIntegral.integral_comp_mul_left
      (a := (0 : ℝ)) (b := (1 : ℝ)) (c := p₁)
      (fun z ↦ g (p₀ + z)) (ne_of_gt hp₁.1)
    have hshift : (∫ z in (0 : ℝ)..p₁, g (p₀ + z)) = I1 := by
      have h := intervalIntegral.integral_comp_add_right
        (a := (0 : ℝ)) (b := p₁) g p₀
      dsimp [I1]
      simpa [add_comm] using h
    calc
      (∫ y in (0 : ℝ)..1, g (p₀ + p₁ * y)) =
          p₁⁻¹ * ∫ z in p₁ * (0 : ℝ)..p₁ * (1 : ℝ), g (p₀ + z) := by
            simpa using hmul
      _ = p₁⁻¹ * I1 := by
            simp [hshift]
  have hpne : p₁ ≠ 0 := ne_of_gt hp₁.1
  have hcalc : p₁⁻¹ * I1 = p₀ + p₁ + p₂ * J := by
    rw [← hsubst, hcongr]
  calc
    (∫ x in p₀..(p₀ + p₁), msG p₀ p₁ p₂ x) = I1 := rfl
    _ = p₁ * (p₁⁻¹ * I1) := by field_simp [hpne]
    _ = p₁ * (p₀ + p₁ + p₂ * J) := by rw [hcalc]
    _ = p₁ * (p₀ + p₁ + p₂ * ∫ x in (0 : ℝ)..1, msG p₀ p₁ p₂ x) := by
        dsimp [J, g]

end

/- accepted add_to_file helper 26 -/
noncomputable section

lemma msG_integral_segment2 {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) :
    (∫ x in (p₀ + p₁)..1, msG p₀ p₁ p₂ x) =
      p₂ * (p₀ + p₁ * ∫ x in (0 : ℝ)..1, msG p₀ p₁ p₂ x) := by
  let g := msG p₀ p₁ p₂
  let I2 := ∫ x in (p₀ + p₁)..1, g x
  let J := ∫ x in (0 : ℝ)..1, g x
  have hcongr : (∫ y in (0 : ℝ)..1, g (p₀ + p₁ + p₂ * y)) =
      p₀ + p₁ * J := by
    have hae : ∀ᵐ y ∂MeasureTheory.volume,
        y ∈ Set.uIoc (0 : ℝ) 1 →
          g (p₀ + p₁ + p₂ * y) = p₀ + p₁ * g y := by
      exact Filter.Eventually.of_forall fun y hy ↦ by
        have hyIoc : y ∈ Set.Ioc (0 : ℝ) 1 := by
          simpa [Set.uIoc_of_le zero_le_one] using hy
        exact msG_map2 hp₀ hp₁ hp₂ hsum ⟨hyIoc.1.le, hyIoc.2⟩
    have h := intervalIntegral.integral_congr_ae hae
    have hgint := msG_intervalIntegrable hp₀ hp₁ hp₂ hsum (a := (0 : ℝ)) (b := 1)
      zero_le_one
    calc
      (∫ y in (0 : ℝ)..1, g (p₀ + p₁ + p₂ * y)) =
          ∫ y in (0 : ℝ)..1, (fun _ ↦ p₀) y + p₁ * g y := h
      _ = (∫ y in (0 : ℝ)..1, (fun _ ↦ p₀) y) +
          ∫ y in (0 : ℝ)..1, p₁ * g y :=
        intervalIntegral.integral_add intervalIntegrable_const (hgint.const_mul p₁)
      _ = p₀ + p₁ * J := by
        rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
        dsimp [J]
        simp
  have hsubst : (∫ y in (0 : ℝ)..1, g (p₀ + p₁ + p₂ * y)) = p₂⁻¹ * I2 := by
    have hmul := intervalIntegral.integral_comp_mul_left
      (a := (0 : ℝ)) (b := (1 : ℝ)) (c := p₂)
      (fun z ↦ g (p₀ + p₁ + z)) (ne_of_gt hp₂.1)
    have hshift : (∫ z in (0 : ℝ)..p₂, g (p₀ + p₁ + z)) = I2 := by
      have h := intervalIntegral.integral_comp_add_right
        (a := (0 : ℝ)) (b := p₂) g (p₀ + p₁)
      dsimp [I2]
      rw [add_comm p₂ (p₀ + p₁)] at h
      have hone : p₀ + p₁ + p₂ = 1 := hsum
      simpa [hone, add_comm, add_left_comm, add_assoc] using h
    calc
      (∫ y in (0 : ℝ)..1, g (p₀ + p₁ + p₂ * y)) =
          p₂⁻¹ * ∫ z in p₂ * (0 : ℝ)..p₂ * (1 : ℝ), g (p₀ + p₁ + z) := by
            simpa [add_assoc] using hmul
      _ = p₂⁻¹ * I2 := by
            simp [hshift]
  have hpne : p₂ ≠ 0 := ne_of_gt hp₂.1
  have hcalc : p₂⁻¹ * I2 = p₀ + p₁ * J := by
    rw [← hsubst, hcongr]
  calc
    (∫ x in (p₀ + p₁)..1, msG p₀ p₁ p₂ x) = I2 := rfl
    _ = p₂ * (p₂⁻¹ * I2) := by field_simp [hpne]
    _ = p₂ * (p₀ + p₁ * J) := by rw [hcalc]
    _ = p₂ * (p₀ + p₁ * ∫ x in (0 : ℝ)..1, msG p₀ p₁ p₂ x) := by
        dsimp [J, g]

end

/- accepted add_to_file helper 27 -/
noncomputable section

lemma msG_integral_eq {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) :
    (∫ x in (0 : ℝ)..1, msG p₀ p₁ p₂ x) =
      (p₁ ^ 2 + p₀ * p₁ + p₀ * p₂) /
        (1 - p₀ ^ 2 - 2 * p₁ * p₂) := by
  let g := msG p₀ p₁ p₂
  let I0 := ∫ x in (0 : ℝ)..p₀, g x
  let I1 := ∫ x in p₀..(p₀ + p₁), g x
  let I2 := ∫ x in (p₀ + p₁)..1, g x
  let J := ∫ x in (0 : ℝ)..1, g x
  have hp0le : (0 : ℝ) ≤ p₀ := hp₀.1.le
  have hp01 : p₀ ≤ p₀ + p₁ := by linarith [hp₁.1]
  have hp01nonneg : (0 : ℝ) ≤ p₀ + p₁ := by linarith [hp₀.1, hp₁.1]
  have hp01le1 : p₀ + p₁ ≤ 1 := by
    rw [← hsum]
    linarith [hp₂.1]
  have hi0 := msG_intervalIntegrable hp₀ hp₁ hp₂ hsum hp0le
  have hi1 := msG_intervalIntegrable hp₀ hp₁ hp₂ hsum hp01
  have hi2 := msG_intervalIntegrable hp₀ hp₁ hp₂ hsum hp01le1
  have hsplit1 : I0 + I1 = ∫ x in (0 : ℝ)..(p₀ + p₁), g x :=
    intervalIntegral.integral_add_adjacent_intervals hi0 hi1
  have hsplit2 : (∫ x in (0 : ℝ)..(p₀ + p₁), g x) + I2 = J :=
    intervalIntegral.integral_add_adjacent_intervals
      (msG_intervalIntegrable hp₀ hp₁ hp₂ hsum hp01nonneg) hi2
  have hsplit : J = I0 + I1 + I2 := by
    rw [← hsplit2, ← hsplit1]
  have hseg0 : I0 = p₀ ^ 2 * J := msG_integral_segment0 hp₀ hp₁ hp₂ hsum
  have hseg1 : I1 = p₁ * (p₀ + p₁ + p₂ * J) :=
    msG_integral_segment1 hp₀ hp₁ hp₂ hsum
  have hseg2 : I2 = p₂ * (p₀ + p₁ * J) :=
    msG_integral_segment2 hp₀ hp₁ hp₂ hsum
  rw [hseg0, hseg1, hseg2] at hsplit
  let D : ℝ := 1 - p₀ ^ 2 - 2 * p₁ * p₂
  let N : ℝ := p₁ ^ 2 + p₀ * p₁ + p₀ * p₂
  have hDfactor :
      D = p₁ * (1 - p₂) + p₂ * (1 - p₁) + p₀ * (p₁ + p₂) := by
    dsimp [D]
    nlinarith [hsum]
  have hDpos : 0 < D := by
    rw [hDfactor]
    have h1 : 0 < p₁ * (1 - p₂) := mul_pos hp₁.1 (sub_pos.mpr hp₂.2)
    have h2 : 0 < p₂ * (1 - p₁) := mul_pos hp₂.1 (sub_pos.mpr hp₁.2)
    have h3 : 0 < p₀ * (p₁ + p₂) := mul_pos hp₀.1 (add_pos hp₁.1 hp₂.1)
    linarith
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hlin : D * J = N := by
    have hleft : D * J = J - p₀ ^ 2 * J - 2 * p₁ * p₂ * J := by
      dsimp [D]
      ring
    rw [hleft]
    dsimp [N]
    linarith
  calc
    (∫ x in (0 : ℝ)..1, msG p₀ p₁ p₂ x) = J := rfl
    _ = D * J / D := by field_simp [hDne]
    _ = N / D := by rw [hlin]
    _ = (p₁ ^ 2 + p₀ * p₁ + p₀ * p₂) /
          (1 - p₀ ^ 2 - 2 * p₁ * p₂) := rfl

end

/- accepted add_to_file helper 28 -/
noncomputable section

lemma msF_eq_msG_on {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) :
    Set.EqOn
      (fun x ↦ msE p₀ p₁ p₂ (fun k ↦ msTheta (msCanonical p₀ p₁ p₂ x k)))
      (msG p₀ p₁ p₂) (Set.Icc (0 : ℝ) 1) := by
  intro x hx
  dsimp [msG]
  rw [msCanonical_eq_msSeq hp₀ hp₁ hp₂ hsum hx]

end

/- verified submission -/
theorem lebesgue_integral_modified_salem
    (p₀ p₁ p₂ : ℝ)
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) :
    let p : Fin 3 → ℝ := ![p₀, p₁, p₂]
    let β : Fin 3 → ℝ := ![0, p₀, p₀ + p₁]
    let E : (ℕ → Fin 3) → ℝ := fun i ↦
      ∑' k : ℕ, β (i k) * ∏ r ∈ Finset.range k, p (i r)
    let canonical : ℝ → (ℕ → Fin 3) := fun x ↦
      Classical.epsilon fun i ↦
        E i = x ∧
          ((∃ j, E j = x ∧ j ≠ i) →
            ∃ N, ∀ k, N ≤ k → i k = 0)
    let θ : Fin 3 → Fin 3 := ![0, 2, 1]
    let f : ℝ → ℝ := fun x ↦ E (fun k ↦ θ (canonical x k))
    MeasureTheory.IntegrableOn f (Set.Icc 0 1) ∧
      (∫ x in (0 : ℝ)..1, f x) =
        (p₁ ^ 2 + p₀ * p₁ + p₀ * p₂) /
          (1 - p₀ ^ 2 - 2 * p₁ * p₂) := by
  dsimp
  constructor
  · refine MeasureTheory.IntegrableOn.congr_fun
      (msG_integrableOn_Icc hp₀ hp₁ hp₂ hsum 0 1) ?_ measurableSet_Icc
    exact fun x hx ↦ (msF_eq_msG_on hp₀ hp₁ hp₂ hsum hx).symm
  · trans ∫ x in (0 : ℝ)..1, msG p₀ p₁ p₂ x
    · apply intervalIntegral.integral_congr_ae
      exact Filter.Eventually.of_forall fun x hx ↦ by
        have hxIoc : x ∈ Set.Ioc (0 : ℝ) 1 := by
          simpa [Set.uIoc_of_le zero_le_one] using hx
        have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hxIoc.1.le, hxIoc.2⟩
        exact msF_eq_msG_on hp₀ hp₁ hp₂ hsum hxIcc
    · exact msG_integral_eq hp₀ hp₁ hp₂ hsum

end Rollout_p1286_lebesgue_integral_modified_salem

namespace Rollout_p0203_bounded_degree_unit_circle_conjugates_clos

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

end Rollout_p0203_bounded_degree_unit_circle_conjugates_clos

namespace Rollout_p2889_newton_sum_identity

/- verified submission -/

lemma newton_nodal_prod_range_succ {K : Type*} [Field K] (ξ : ℕ → K) (n : ℕ) :
    (∏ j ∈ Finset.range (n + 1), (Polynomial.X - Polynomial.C (ξ j))) =
      (Polynomial.X - Polynomial.C (ξ 0)) *
        ∏ j ∈ Finset.Icc 1 n, (Polynomial.X - Polynomial.C (ξ j)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ, ih,
        Finset.prod_Icc_succ_top (by omega : 1 ≤ n + 1)]
      ring

lemma newton_step_core {K : Type*} [Field K] (p : Polynomial K) (D b x0 xn : K)
    (hb : b ≠ 0) (hxb : b = x0 - xn) :
    p * Polynomial.C (D⁻¹) +
        ((Polynomial.X - Polynomial.C x0) * p) * Polynomial.C ((D * b)⁻¹) =
      (p * (Polynomial.X - Polynomial.C xn)) * Polynomial.C ((D * b)⁻¹) := by
  have hbc : Polynomial.C (b⁻¹ : K) * Polynomial.C b = (1 : Polynomial K) := by
    rw [← Polynomial.C_mul, inv_mul_cancel₀ hb, Polynomial.C_1]
  have hA : p * Polynomial.C (D⁻¹ : K) =
      p * Polynomial.C (D⁻¹ : K) * Polynomial.C (b⁻¹ : K) * Polynomial.C b := by
    calc
      p * Polynomial.C (D⁻¹ : K) = p * Polynomial.C (D⁻¹ : K) * 1 := by
        rw [mul_one]
      _ = p * Polynomial.C (D⁻¹ : K) *
            (Polynomial.C (b⁻¹ : K) * Polynomial.C b) := by
        rw [← hbc]
      _ = p * Polynomial.C (D⁻¹ : K) * Polynomial.C (b⁻¹ : K) * Polynomial.C b := by
        ring
  calc
    p * Polynomial.C (D⁻¹) +
          ((Polynomial.X - Polynomial.C x0) * p) * Polynomial.C ((D * b)⁻¹)
        = p * Polynomial.C (D⁻¹) * Polynomial.C (b⁻¹) * Polynomial.C b +
            ((Polynomial.X - Polynomial.C x0) * p) * Polynomial.C ((D * b)⁻¹) := by
          exact congrArg
            (fun z => z + ((Polynomial.X - Polynomial.C x0) * p) * Polynomial.C ((D * b)⁻¹))
            hA
    _ = (p * Polynomial.C (D⁻¹) * Polynomial.C (b⁻¹)) *
          (Polynomial.C b + (Polynomial.X - Polynomial.C x0)) := by
          rw [mul_inv, Polynomial.C_mul]
          ring
    _ = (p * Polynomial.C (D⁻¹) * Polynomial.C (b⁻¹)) *
          (Polynomial.X - Polynomial.C xn) := by
          rw [hxb, Polynomial.C_sub]
          ring
    _ = (p * (Polynomial.X - Polynomial.C xn)) * Polynomial.C ((D * b)⁻¹) := by
          rw [mul_inv, Polynomial.C_mul]
          ring

theorem newton_sum_identity
    {K : Type*} [Field K] (d : ℕ) (ξ : ℕ → K)
    (hξ : Set.InjOn ξ (Set.Icc 0 d)) :
    ∑ i ∈ Finset.range (d + 1),
        (∏ j ∈ Finset.range i, (Polynomial.X - Polynomial.C (ξ j))) *
          Polynomial.C ((∏ j ∈ Finset.Icc 1 i, (ξ 0 - ξ j))⁻¹) =
      (∏ j ∈ Finset.Icc 1 d, (Polynomial.X - Polynomial.C (ξ j))) *
        Polynomial.C ((∏ j ∈ Finset.Icc 1 d, (ξ 0 - ξ j))⁻¹) := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Finset.sum_range_succ]
      have hsubset : Set.Icc 0 d ⊆ Set.Icc 0 (d + 1) := by
        intro x hx
        exact ⟨hx.1, Nat.le_trans hx.2 (Nat.le_succ d)⟩
      rw [ih (Set.InjOn.mono hsubset hξ)]
      rw [newton_nodal_prod_range_succ ξ d]
      rw [Finset.prod_Icc_succ_top (a := 1) (b := d)
        (f := fun j => ξ 0 - ξ j) (by omega : 1 ≤ d + 1)]
      rw [Finset.prod_Icc_succ_top (a := 1) (b := d)
        (f := fun j => Polynomial.X - Polynomial.C (ξ j)) (by omega : 1 ≤ d + 1)]
      have hne : ξ 0 ≠ ξ (d + 1) := by
        exact hξ.ne (by simp) (by simp) (Nat.succ_ne_zero d).symm
      exact newton_step_core
        (∏ j ∈ Finset.Icc 1 d, (Polynomial.X - Polynomial.C (ξ j)))
        (∏ j ∈ Finset.Icc 1 d, (ξ 0 - ξ j))
        (ξ 0 - ξ (d + 1)) (ξ 0) (ξ (d + 1))
        (sub_ne_zero_of_ne hne) rfl

end Rollout_p2889_newton_sum_identity

namespace Rollout_p1193_parseval_frame_spans_orthogonal

/- accepted add_to_file helper 1 -/
lemma rankOneInner_isSymmetric {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] (a : E) :
    (((innerₗ E) a).smulRight a).IsSymmetric := by
  intro x y
  simp [LinearMap.smulRight_apply, innerₗ_apply_apply,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm x a]
  exact mul_comm (inner ℝ x a) (inner ℝ a y)

noncomputable def partialFrame {M N : ℕ}
    (φ : Fin N → EuclideanSpace ℝ (Fin M)) (J : Set (Fin N)) :
    EuclideanSpace ℝ (Fin M) →ₗ[ℝ] EuclideanSpace ℝ (Fin M) := by
  classical
  exact ∑ i ∈ Finset.univ.filter (fun i => i ∈ J),
    (((innerₗ (EuclideanSpace ℝ (Fin M))) (φ i)).smulRight (φ i))

/- accepted add_to_file helper 2 -/
lemma partialFrame_isSymmetric {M N : ℕ}
    (φ : Fin N → EuclideanSpace ℝ (Fin M)) (J : Set (Fin N)) :
    (partialFrame φ J).IsSymmetric := by
  classical
  unfold partialFrame
  apply LinearMap.isSymmetric_sum
  intro i hi
  exact rankOneInner_isSymmetric (φ i)

/- accepted add_to_file helper 3 -/
lemma partialFrame_mem_span {M N : ℕ}
    (φ : Fin N → EuclideanSpace ℝ (Fin M)) (J : Set (Fin N))
    (x : EuclideanSpace ℝ (Fin M)) :
    partialFrame φ J x ∈ Submodule.span ℝ (φ '' J) := by
  classical
  unfold partialFrame
  simp
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨i, by simpa using hi, rfl⟩

/- accepted add_to_file helper 4 -/
lemma symmetric_eq_id_of_inner_map_self {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (T : E →ₗ[ℝ] E)
    (hT : T.IsSymmetric)
    (hdiag : ∀ x : E, inner ℝ (T x) x = inner ℝ x x) :
    T = LinearMap.id := by
  let R : E →ₗ[ℝ] E := T - LinearMap.id
  have hsymm : R.IsSymmetric := hT.sub LinearMap.IsSymmetric.id
  have hdiagR : ∀ z : E, inner ℝ (R z) z = 0 := by
    intro z
    simp only [R, LinearMap.sub_apply, LinearMap.id_apply]
    rw [inner_sub_left, hdiag z, sub_self]
  have hbilin : ∀ x y : E, inner ℝ (R x) y = 0 := by
    intro x y
    have hp := hsymm.inner_map_polarization x y
    rw [hdiagR (x + y), hdiagR (x - y)] at hp
    simpa using hp
  ext x
  have hzero : inner ℝ (R x) (R x) = 0 := hbilin x (R x)
  have hRx : R x = 0 := (inner_self_eq_zero (𝕜 := ℝ) (x := R x)).mp hzero
  have : T x - x = 0 := by
    simpa [R] using hRx
  exact sub_eq_zero.mp this

/- accepted add_to_file helper 5 -/
lemma partialFrame_univ_eq_id_of_parseval {M N : ℕ}
    (φ : Fin N → EuclideanSpace ℝ (Fin M))
    (hParseval : ∀ x : EuclideanSpace ℝ (Fin M),
      (∑ i : Fin N, (inner ℝ x (φ i)) ^ 2) = ‖x‖ ^ 2) :
    partialFrame φ Set.univ = LinearMap.id := by
  classical
  apply symmetric_eq_id_of_inner_map_self
  · exact partialFrame_isSymmetric φ Set.univ
  · intro x
    calc
      inner ℝ (partialFrame φ Set.univ x) x
          = ∑ i : Fin N, (inner ℝ x (φ i)) ^ 2 := by
            unfold partialFrame
            simp [innerₗ_apply_apply, real_inner_comm]
            rw [inner_sum]
            apply Finset.sum_congr rfl
            intro i hi
            rw [real_inner_smul_right]
            ring
      _ = ‖x‖ ^ 2 := hParseval x
      _ = inner ℝ x x := by rw [real_inner_self_eq_norm_sq]

/- accepted add_to_file helper 6 -/
lemma partialFrame_add_compl {M N : ℕ}
    (φ : Fin N → EuclideanSpace ℝ (Fin M)) (J : Set (Fin N)) :
    partialFrame φ J + partialFrame φ Jᶜ = partialFrame φ Set.univ := by
  classical
  ext x
  simp [partialFrame, Finset.sum_filter_add_sum_filter_not]

/- verified submission -/
theorem parseval_frame_spans_orthogonal
    (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (φ : Fin N → EuclideanSpace ℝ (Fin M))
    (hParseval : ∀ x : EuclideanSpace ℝ (Fin M),
      (∑ i : Fin N, (inner ℝ x (φ i)) ^ 2) = ‖x‖ ^ 2)
    (I : Set (Fin N))
    (hdisjoint : Submodule.span ℝ (φ '' I) ⊓
      Submodule.span ℝ (φ '' Iᶜ) = ⊥) :
    ∀ u ∈ Submodule.span ℝ (φ '' I),
      ∀ v ∈ Submodule.span ℝ (φ '' Iᶜ), inner ℝ u v = 0 := by
  classical
  let E := EuclideanSpace ℝ (Fin M)
  let A : Submodule ℝ E := Submodule.span ℝ (φ '' I)
  let B : Submodule ℝ E := Submodule.span ℝ (φ '' Iᶜ)
  let SI : E →ₗ[ℝ] E := partialFrame φ I
  let SC : E →ₗ[ℝ] E := partialFrame φ Iᶜ
  have hframe : partialFrame φ Set.univ = LinearMap.id :=
    partialFrame_univ_eq_id_of_parseval φ hParseval
  have hdecomp : ∀ x : E, SI x + SC x = x := by
    intro x
    have happ := congrArg (fun T : E →ₗ[ℝ] E => T x)
      (partialFrame_add_compl φ I)
    rw [hframe] at happ
    simpa [SI, SC] using happ
  have hSI_zero_on_B : ∀ v ∈ B, SI v = 0 := by
    intro v hv
    have hSIv_A : SI v ∈ A := by
      simpa [SI, A, E] using partialFrame_mem_span φ I v
    have hSCv_B : SC v ∈ B := by
      simpa [SC, B, E] using partialFrame_mem_span φ Iᶜ v
    have hSIv_B : SI v ∈ B := by
      have hEq : SI v = v - SC v := eq_sub_of_add_eq (hdecomp v)
      rw [hEq]
      exact B.sub_mem hv hSCv_B
    have hbot : SI v ∈ (⊥ : Submodule ℝ E) := by
      rw [← hdisjoint]
      change SI v ∈ A ⊓ B
      exact ⟨hSIv_A, hSIv_B⟩
    exact (Submodule.mem_bot ℝ).mp hbot
  intro u hu v hv
  have hSIu_A : SI u ∈ A := by
    simpa [SI, A, E] using partialFrame_mem_span φ I u
  have hSCu_B : SC u ∈ B := by
    simpa [SC, B, E] using partialFrame_mem_span φ Iᶜ u
  have hSCu_A : SC u ∈ A := by
    have hEq : SC u = u - SI u := eq_sub_of_add_eq' (hdecomp u)
    rw [hEq]
    exact A.sub_mem hu hSIu_A
  have hSCu_zero : SC u = 0 := by
    have hbot : SC u ∈ (⊥ : Submodule ℝ E) := by
      rw [← hdisjoint]
      change SC u ∈ A ⊓ B
      exact ⟨hSCu_A, hSCu_B⟩
    exact (Submodule.mem_bot ℝ).mp hbot
  have hSIu : SI u = u := by
    have h := hdecomp u
    rw [hSCu_zero, add_zero] at h
    exact h
  have hSIv : SI v = 0 := hSI_zero_on_B v hv
  calc
    inner ℝ u v = inner ℝ (SI u) v := by rw [hSIu]
    _ = inner ℝ u (SI v) := partialFrame_isSymmetric φ I u v
    _ = inner ℝ u 0 := by rw [hSIv]
    _ = 0 := by rw [inner_zero_right]

end Rollout_p1193_parseval_frame_spans_orthogonal

namespace Rollout_p0109_exists_atomic_puiseux_monoid_without_singl

/- verified submission -/
theorem exists_atomic_puiseux_monoid_without_singleton_two_lengths :
    ∃ M : AddSubmonoid ℚ≥0,
      (∀ x : M, ∃ l : List M,
        (∀ a ∈ l, AddIrreducible a) ∧ l.sum = x) ∧
      (∀ x : M,
        {n : ℕ | ∃ l : List M,
          l.length = n ∧ (∀ a ∈ l, AddIrreducible a) ∧ l.sum = x} ≠ {2}) := by
  refine ⟨⊥, ?_, ?_⟩
  · intro x
    refine ⟨[], ?_, ?_⟩
    · intro a ha
      cases ha
    · change (0 : (⊥ : AddSubmonoid ℚ≥0)) = x
      apply Subtype.ext
      exact (x.property).symm
  · intro x h
    have h0 : 0 ∈ {n : ℕ | ∃ l : List (⊥ : AddSubmonoid ℚ≥0),
        l.length = n ∧ (∀ a ∈ l, AddIrreducible a) ∧ l.sum = x} := by
      refine ⟨[], rfl, ?_, ?_⟩
      · intro a ha
        cases ha
      · change (0 : (⊥ : AddSubmonoid ℚ≥0)) = x
        apply Subtype.ext
        exact (x.property).symm
    rw [h] at h0
    norm_num at h0

end Rollout_p0109_exists_atomic_puiseux_monoid_without_singl

namespace Rollout_p1384_scale_prod

/- accepted add_to_file helper 1 -/
lemma subgroup_map_prodMap {G H : Type*} [Group G] [Group H]
    (P : Subgroup G) (Q : Subgroup H)
    (f : G →* G) (g : H →* H) :
    (P.prod Q).map (f.prodMap g) = (P.map f).prod (Q.map g) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, hfx⟩
    change y ∈ P.prod Q at hy
    rw [Subgroup.mem_prod] at hy
    rw [← hfx]
    change (f y.1, g y.2) ∈ (P.map f).prod (Q.map g)
    rw [Subgroup.mem_prod]
    constructor
    · exact ⟨y.1, hy.1, rfl⟩
    · exact ⟨y.2, hy.2, rfl⟩
  · intro hx
    change x ∈ (P.map f).prod (Q.map g) at hx
    rw [Subgroup.mem_prod] at hx
    rcases hx with ⟨⟨y1, hy1, hf1⟩, ⟨y2, hy2, hf2⟩⟩
    use (y1, y2)
    constructor
    · change (y1, y2) ∈ P.prod Q
      rw [Subgroup.mem_prod]
      exact ⟨hy1, hy2⟩
    · cases x
      simp_all

lemma subgroup_prodEquiv_map {G H : Type*} [Group G] [Group H]
    (P : Subgroup G) (Q : Subgroup H)
    (f : G →* G) (g : H →* H) :
    Subgroup.map (↑(Subgroup.prodEquiv (P.map f) (Q.map g)))
      ((P.prod Q).subgroupOf ((P.map f).prod (Q.map g))) =
      (P.subgroupOf (P.map f)).prod (Q.subgroupOf (Q.map g)) := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨y, hy, hzy⟩
    change y ∈ ((P.prod Q).subgroupOf ((P.map f).prod (Q.map g))) at hy
    rw [← hzy]
    change Subgroup.prodEquiv (P.map f) (Q.map g) y ∈
      (P.subgroupOf (P.map f)).prod (Q.subgroupOf (Q.map g))
    rw [Subgroup.mem_prod]
    rcases y with ⟨⟨p,q⟩, hpq⟩
    rw [Subgroup.mem_prod] at hpq
    constructor
    · exact hy.1
    · exact hy.2
  · intro hz
    change z ∈ (P.subgroupOf (P.map f)).prod (Q.subgroupOf (Q.map g)) at hz
    rw [Subgroup.mem_prod] at hz
    use (Subgroup.prodEquiv (P.map f) (Q.map g)).symm z
    constructor
    · change (Subgroup.prodEquiv (P.map f) (Q.map g)).symm z ∈
        ((P.prod Q).subgroupOf ((P.map f).prod (Q.map g)))
      rcases z with ⟨⟨p,hp⟩,⟨q,hq⟩⟩
      exact hz
    · simp

lemma relIndex_prod_map {G H : Type*} [Group G] [Group H]
    (P : Subgroup G) (Q : Subgroup H)
    (f : G →* G) (g : H →* H) :
    (P.prod Q).relIndex ((P.prod Q).map (f.prodMap g)) =
      P.relIndex (P.map f) * Q.relIndex (Q.map g) := by
  rw [subgroup_map_prodMap]
  unfold Subgroup.relIndex
  rw [← Subgroup.index_map_equiv
    ((P.prod Q).subgroupOf ((P.map f).prod (Q.map g)))
    (Subgroup.prodEquiv (P.map f) (Q.map g)),
    subgroup_prodEquiv_map, Subgroup.index_prod]

lemma exists_compact_open_subgroup_subset {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    {U : Set G} (hU : IsOpen U) (h1U : 1 ∈ U) :
    ∃ S : Subgroup G, IsCompact (S : Set G) ∧ IsOpen (S : Set G) ∧ (S : Set G) ⊆ U := by
  obtain ⟨L, hL, h1L, hLU⟩ := exists_compact_subset hU h1U
  have hclopenbasis := loc_compact_Haus_tot_disc_of_zero_dim (H := G)
  have hLn : interior L ∈ nhds (1 : G) := isOpen_interior.mem_nhds h1L
  rw [hclopenbasis.mem_nhds_iff] at hLn
  rcases hLn with ⟨K, hKclopen, h1K, hKL⟩
  have hKcompact : IsCompact K :=
    hL.of_isClosed_subset hKclopen.isClosed (hKL.trans interior_subset)
  have hKopen : IsOpen K := hKclopen.isOpen
  obtain ⟨D, hDn, hDK⟩ := compact_open_separated_mul_left hKcompact hKopen
    (show K ⊆ K from subset_rfl)
  have hDnint : interior D ∈ nhds (1 : G) := interior_mem_nhds.2 hDn
  have hclopenbasis2 := loc_compact_Haus_tot_disc_of_zero_dim (H := G)
  have hb := (hclopenbasis2.mem_nhds_iff).mp hDnint
  rcases hb with ⟨C0, hC0, h1C0, hC0D⟩
  let C : Set G := C0 ∩ C0⁻¹
  have hCclopen : IsClopen C :=
    hC0.inter ⟨hC0.isClosed.inv, hC0.isOpen.inv⟩
  have h1C : 1 ∈ C := by
    constructor
    · exact h1C0
    · simpa [Set.mem_inv] using h1C0
  have hCD : C ⊆ D := by
    intro c hc
    exact interior_subset (hC0D hc.1)
  have hCinvD : ∀ c ∈ C, c⁻¹ ∈ D := by
    intro c hc
    exact interior_subset (hC0D (by simpa [Set.mem_inv] using hc.2))
  let S : Subgroup G := Subgroup.closure C
  have hSK : (S : Set G) ⊆ K := by
    intro x hx
    induction hx using Subgroup.closure_induction_left with
    | one =>
        exact h1K
    | mul_left c hc y hy hycK =>
        exact hDK (Set.mul_mem_mul (hCD hc) hycK)
    | inv_mul_cancel c hc y hy hycK =>
        exact hDK (Set.mul_mem_mul (hCinvD c hc) hycK)
  have hSopen : IsOpen (S : Set G) := by
    apply Subgroup.isOpen_of_mem_nhds S (g := 1)
    exact Filter.mem_of_superset (hCclopen.isOpen.mem_nhds h1C) Subgroup.subset_closure
  have hScompact : IsCompact (S : Set G) :=
    hKcompact.of_isClosed_subset (S.isClosed_of_isOpen hSopen) hSK
  exact ⟨S, hScompact, hSopen, hSK.trans ((hKL.trans interior_subset).trans hLU)⟩

/- accepted add_to_file helper 2 -/
lemma continuousMulEquiv_image_compact_open {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (φ : G ≃ₜ* G) {U : Subgroup G}
    (hUc : IsCompact (U : Set G)) (hUo : IsOpen (U : Set G)) :
    IsCompact ((U.map φ.toMulEquiv.toMonoidHom : Subgroup G) : Set G) ∧
      IsOpen ((U.map φ.toMulEquiv.toMonoidHom : Subgroup G) : Set G) := by
  constructor
  · rw [Subgroup.coe_map]
    exact hUc.image φ.toHomeomorph.continuous
  · rw [Subgroup.coe_map]
    exact φ.toHomeomorph.isOpenMap _ hUo

lemma relIndex_ne_zero_of_compact_open {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (φ : G ≃ₜ* G) {U : Subgroup G}
    (hUc : IsCompact (U : Set G)) (hUo : IsOpen (U : Set G)) :
    U.relIndex (U.map φ.toMulEquiv.toMonoidHom) ≠ 0 := by
  obtain ⟨hfc, hfo⟩ := continuousMulEquiv_image_compact_open φ hUc hUo
  let K : Subgroup G := U.map φ.toMulEquiv.toMonoidHom
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hfc
  have hsubopen : IsOpen ((U.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
    rw [Subgroup.coe_subgroupOf]
    exact hUo.preimage continuous_subtype_val
  have hfin : Finite (↥K ⧸ U.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen (U.subgroupOf K) hsubopen
  haveI := hfin
  have hfi : (U.subgroupOf K).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hne : (U.subgroupOf K).index ≠ 0 := Subgroup.finiteIndex_iff.mp hfi
  simpa [Subgroup.relIndex, K] using hne

/- accepted add_to_file helper 3 -/
lemma continuousMulEquiv_prod_image_compact_open {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (φ : G ≃ₜ* G) (ψ : H ≃ₜ* H) {U : Subgroup (G × H)}
    (hUc : IsCompact (U : Set (G × H))) (hUo : IsOpen (U : Set (G × H))) :
    IsCompact ((U.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom) :
      Subgroup (G × H)) : Set (G × H)) ∧
    IsOpen ((U.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom) :
      Subgroup (G × H)) : Set (G × H)) := by
  let e : (G × H) ≃ₜ (G × H) := Homeomorph.prodCongr φ.toHomeomorph ψ.toHomeomorph
  have hmap : ((U.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom) :
      Subgroup (G × H)) : Set (G × H)) = e '' (U : Set (G × H)) := by
    rw [Subgroup.coe_map]
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, by ext <;> rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, by ext <;> rfl⟩
  constructor
  · rw [hmap]
    exact hUc.image e.continuous
  · rw [hmap]
    exact e.isOpenMap _ hUo

lemma relIndex_ne_zero_of_compact_open_prod {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (φ : G ≃ₜ* G) (ψ : H ≃ₜ* H) {U : Subgroup (G × H)}
    (hUc : IsCompact (U : Set (G × H))) (hUo : IsOpen (U : Set (G × H))) :
    U.relIndex (U.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom)) ≠ 0 := by
  obtain ⟨hfc, hfo⟩ := continuousMulEquiv_prod_image_compact_open φ ψ hUc hUo
  let K : Subgroup (G × H) :=
    U.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom)
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hfc
  have hsubopen : IsOpen ((U.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
    rw [Subgroup.coe_subgroupOf]
    exact hUo.preimage continuous_subtype_val
  have hfin : Finite (↥K ⧸ U.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen (U.subgroupOf K) hsubopen
  haveI := hfin
  have hfi : (U.subgroupOf K).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hne : (U.subgroupOf K).index ≠ 0 := Subgroup.finiteIndex_iff.mp hfi
  simpa [Subgroup.relIndex, K] using hne

/- accepted add_to_file helper 4 -/
lemma Subgroup.index_eq_map_mul_relIndex_ker {X Y : Type*} [Group X] [Group Y]
    (q : X →* Y) (hsurj : Function.Surjective q) (R : Subgroup X)
    (hkerR : q.ker.relIndex R ≠ 0) :
    R.index = (R.map q).index * R.relIndex q.ker := by
  let K : Subgroup X := q.ker
  let J : Subgroup X := R ⊔ K
  have hmap : (R.map q).index = J.index := by
    have h := Subgroup.index_map R q
    have hrange : q.range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
    rw [hrange, Subgroup.index_top, Nat.mul_one] at h
    simpa [J, K] using h
  have hrel_eq : R.relIndex J = R.relIndex K := by
    have hsup : K.relIndex J = K.relIndex R := by
      simpa [J] using (Subgroup.relIndex_sup_right R K)
    have hinf := Subgroup.relIndex_inf_mul_relIndex R K J
    have hKJ : K ⊓ J = K := by
      exact inf_eq_left.mpr (show K ≤ J from le_sup_right)
    rw [hKJ, hsup] at hinf
    have hchain := Subgroup.relIndex_mul_relIndex (R ⊓ K) R J
      (show R ⊓ K ≤ R from inf_le_left)
      (show R ≤ J from le_sup_left)
    have hI_R : (R ⊓ K).relIndex R = K.relIndex R := by
      rw [inf_comm]
      exact Subgroup.inf_relIndex_right K R
    rw [hI_R] at hchain
    have hcancel : K.relIndex R * R.relIndex K = K.relIndex R * R.relIndex J := by
      calc
        K.relIndex R * R.relIndex K = R.relIndex K * K.relIndex R := Nat.mul_comm _ _
        _ = (R ⊓ K).relIndex J := hinf
        _ = K.relIndex R * R.relIndex J := hchain.symm
    exact (Nat.mul_left_cancel (Nat.pos_of_ne_zero (by simpa [K] using hkerR)) hcancel).symm
  have htrans := Subgroup.relIndex_mul_index (H := R) (K := J) le_sup_left
  rw [hrel_eq, ← hmap, Nat.mul_comm] at htrans
  exact htrans.symm

/- accepted add_to_file helper 5 -/
lemma subgroup_map_fst_compact_open {G H : Type*}
    [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H]
    {U : Subgroup (G × H)}
    (hUc : IsCompact (U : Set (G × H))) (hUo : IsOpen (U : Set (G × H))) :
    IsCompact ((U.map (MonoidHom.fst G H) : Subgroup G) : Set G) ∧
      IsOpen ((U.map (MonoidHom.fst G H) : Subgroup G) : Set G) := by
  constructor
  · rw [Subgroup.coe_map]
    exact hUc.image continuous_fst
  · rw [Subgroup.coe_map]
    exact isOpenMap_fst _ hUo

lemma subgroup_comap_inr_compact_open {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TotallyDisconnectedSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {U : Subgroup (G × H)}
    (hUc : IsCompact (U : Set (G × H))) (hUo : IsOpen (U : Set (G × H))) :
    IsCompact ((U.comap (MonoidHom.inr G H) : Subgroup H) : Set H) ∧
      IsOpen ((U.comap (MonoidHom.inr G H) : Subgroup H) : Set H) := by
  let f : H →ₜ* G × H := ContinuousMonoidHom.inr G H
  have hpre : ((U.comap (MonoidHom.inr G H) : Subgroup H) : Set H) =
      (fun h : H => ((1 : G), h)) ⁻¹' (U : Set (G × H)) := by
    rw [Subgroup.coe_comap]
    rfl
  have hemb : Topology.IsClosedEmbedding (fun h : H => ((1 : G), h)) := by
    refine Topology.IsClosedEmbedding.mk
      (show Topology.IsEmbedding (Prod.mk (1 : G)) from isEmbedding_prodMkRight (1 : G)) ?_
    have hrange : Set.range (fun h : H => ((1 : G), h)) = ({1} : Set G) ×ˢ Set.univ := by
      ext x
      constructor
      · rintro ⟨h, rfl⟩
        exact ⟨rfl, trivial⟩
      · rintro ⟨hx, -⟩
        rcases x with ⟨g,h⟩
        simp at hx
        subst g
        exact ⟨h, rfl⟩
    rw [hrange]
    exact isClosed_singleton.prod isClosed_univ
  constructor
  · rw [hpre]
    exact hemb.isCompact_preimage hUc
  · rw [hpre]
    exact hUo.preimage f.continuous

/- accepted add_to_file helper 6 -/
lemma Subgroup.index_ne_zero_of_isOpen_of_compact {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K : Subgroup G} (hK : IsCompact (K : Set G))
    {R : Subgroup ↥K} (hR : IsOpen (R : Set ↥K)) :
    R.index ≠ 0 := by
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  have hfin : Finite (↥K ⧸ R) := Subgroup.quotient_finite_of_isOpen R hR
  haveI := hfin
  have hfi : R.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.finiteIndex_iff.mp hfi

/- accepted add_to_file helper 7 -/
noncomputable def kernelFstProdEquiv {G H : Type*} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H]
    (φ : G ≃ₜ* G) (ψ : H ≃ₜ* H) (U : Subgroup (G × H)) :
    let F := φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom
    let X := U.map F
    let B := U.comap (MonoidHom.inr G H)
    let Bf := B.map ψ.toMulEquiv.toMonoidHom
    let q0 := (MonoidHom.fst G H).comp X.subtype
    Bf ≃* q0.rangeRestrict.ker := by
  intro F X B Bf q0
  let e : ↥Bf →* ↥q0.rangeRestrict.ker :=
    (((MonoidHom.inr G H).comp (Bf.subtype)).codRestrict X (by
      intro y
      rcases y with ⟨y, hyBf⟩
      rcases hyBf with ⟨b, hbB, hby⟩
      subst y
      have hm : F (1, b) ∈ X := ⟨(1, b), hbB, rfl⟩
      simpa [F] using hm)).codRestrict q0.rangeRestrict.ker (by
        intro y
        rcases y with ⟨y, hyBf⟩
        rcases hyBf with ⟨b, hbB, hby⟩
        subst y
        simp [q0])
  have hinj : Function.Injective e := by
    intro y z hyz
    apply Subtype.ext
    exact congrArg (fun x : ↥q0.rangeRestrict.ker => (x.1.1.2 : H)) hyz
  have hsurj : Function.Surjective e := by
    intro z
    rcases z with ⟨x, hxker⟩
    rcases x with ⟨x, hxX⟩
    have hq : q0.rangeRestrict ⟨x, hxX⟩ = 1 := hxker
    rcases hxX with ⟨u, hu, hux⟩
    subst x
    have hqval : q0 ⟨F u, by exact ⟨u, hu, rfl⟩⟩ = 1 := congrArg Subtype.val hq
    have hφ : φ u.1 = 1 := by
      simpa [q0, F] using hqval
    have hu1 : u.1 = 1 := by
      apply φ.toMulEquiv.injective
      simpa using hφ
    have huj : u = ((1 : G), u.2) := by
      ext
      · exact hu1
      · rfl
    refine ⟨⟨ψ u.2, ⟨u.2, ?_, rfl⟩⟩, ?_⟩
    · change ((1 : G), u.2) ∈ U
      rw [← huj]
      exact hu
    · ext : 2
      exact Prod.ext hφ.symm rfl
  exact MulEquiv.ofBijective e ⟨hinj, hsurj⟩

/- accepted add_to_file helper 8 -/
lemma kernel_fst_prod_equiv_map {G H : Type*} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H]
    (φ : G ≃ₜ* G) (ψ : H ≃ₜ* H) (U : Subgroup (G × H)) :
    let F := φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom
    let X := U.map F
    let B := U.comap (MonoidHom.inr G H)
    let Bf := B.map ψ.toMulEquiv.toMonoidHom
    let q0 := (MonoidHom.fst G H).comp X.subtype
    Subgroup.map (↑(kernelFstProdEquiv φ ψ U))
      ((B.subgroupOf Bf)) =
      ((U.subgroupOf X).subgroupOf q0.rangeRestrict.ker) := by
  intro F X B Bf q0
  let E := kernelFstProdEquiv φ ψ U
  ext z
  constructor
  · intro hz
    rcases hz with ⟨y, hyB, hEy⟩
    change y ∈ B.subgroupOf Bf at hyB
    change y.val ∈ B at hyB
    rw [← hEy]
    change (E y) ∈ (U.subgroupOf X).subgroupOf q0.rangeRestrict.ker
    change ((E y).val.val : G × H) ∈ U
    change (((1 : G), y.val) : G × H) ∈ U
    exact hyB
  · intro hz
    change z ∈ (U.subgroupOf X).subgroupOf q0.rangeRestrict.ker at hz
    change (z.val.val : G × H) ∈ U at hz
    refine ⟨E.symm z, ?_, ?_⟩
    · change (E.symm z).val ∈ B
      have hyval : (E.symm z).val = z.val.val.2 := by
        have h := congrArg (fun w : ↥q0.rangeRestrict.ker => w.val.val.2)
          (MulEquiv.apply_symm_apply E z)
        simpa [E, kernelFstProdEquiv] using h
      rw [hyval]
      have hfst : z.val.val.1 = 1 := by
        have hq := z.property
        change q0.rangeRestrict z.val = 1 at hq
        have hqval : q0 z.val = 1 := congrArg Subtype.val hq
        simpa [q0] using hqval
      have hzval : z.val.val = ((1 : G), z.val.val.2) := by
        ext
        · exact hfst
        · rfl
      change (((1 : G), z.val.val.2) : G × H) ∈ U
      rw [← hzval]
      exact hz
    · exact MulEquiv.apply_symm_apply E z

/- accepted add_to_file helper 9 -/
lemma relIndex_rangeRestrict_ker_fst {G H : Type*} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H]
    (φ : G ≃ₜ* G) (ψ : H ≃ₜ* H) (U : Subgroup (G × H)) :
    let F := φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom
    let X := U.map F
    let B := U.comap (MonoidHom.inr G H)
    let Bf := B.map ψ.toMulEquiv.toMonoidHom
    let q0 := (MonoidHom.fst G H).comp X.subtype
    (U.subgroupOf X).relIndex q0.rangeRestrict.ker = B.relIndex Bf := by
  intro F X B Bf q0
  unfold Subgroup.relIndex
  rw [← Subgroup.index_map_equiv (B.subgroupOf Bf) (kernelFstProdEquiv φ ψ U),
    kernel_fst_prod_equiv_map]

/- accepted add_to_file helper 10 -/
lemma Subgroup.map_index_mul_relIndex_ker_le_index {X Y : Type*} [Group X] [Group Y]
    (q : X →* Y) (hsurj : Function.Surjective q) (R : Subgroup X)
    [Finite (↥(R ⊔ q.ker) ⧸ R.subgroupOf (R ⊔ q.ker))] :
    (R.map q).index * R.relIndex q.ker ≤ R.index := by
  let K : Subgroup X := q.ker
  let J : Subgroup X := R ⊔ K
  have hmap : (R.map q).index = J.index := by
    have h := Subgroup.index_map R q
    have hrange : q.range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
    rw [hrange, Subgroup.index_top, Nat.mul_one] at h
    simpa [J, K] using h
  have htrans := Subgroup.relIndex_mul_index (H := R) (K := J) le_sup_left
  have hle : R.relIndex K ≤ R.relIndex J := by
    let e : ↥K ⧸ R.subgroupOf K ↪ ↥J ⧸ R.subgroupOf J :=
      Subgroup.quotientSubgroupOfEmbeddingOfLE R (show K ≤ J from le_sup_right)
    have hcard := Nat.card_le_card_of_injective e e.injective
    unfold Subgroup.relIndex
    rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
    simpa [J, K] using hcard
  calc
    (R.map q).index * R.relIndex q.ker = J.index * R.relIndex K := by rw [hmap]
    _ ≤ J.index * R.relIndex J := Nat.mul_le_mul_left _ hle
    _ = R.relIndex J * J.index := Nat.mul_comm _ _
    _ = R.index := htrans

/- accepted add_to_file helper 11 -/
lemma scale_prod_lower {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [TotallyDisconnectedSpace H]
    (φ : G ≃ₜ* G) (ψ : H ≃ₜ* H)
    {U : Subgroup (G × H)}
    (hUc : IsCompact (U : Set (G × H))) (hUo : IsOpen (U : Set (G × H))) :
    sInf {n : ℕ | ∃ V : Subgroup G,
      IsCompact (V : Set G) ∧ IsOpen (V : Set G) ∧
        n = V.relIndex (V.map φ.toMulEquiv.toMonoidHom)} *
    sInf {n : ℕ | ∃ W : Subgroup H,
      IsCompact (W : Set H) ∧ IsOpen (W : Set H) ∧
        n = W.relIndex (W.map ψ.toMulEquiv.toMonoidHom)} ≤
    U.relIndex (U.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom)) := by
  let SG : Set ℕ := {n : ℕ | ∃ V : Subgroup G,
    IsCompact (V : Set G) ∧ IsOpen (V : Set G) ∧
      n = V.relIndex (V.map φ.toMulEquiv.toMonoidHom)}
  let SH : Set ℕ := {n : ℕ | ∃ W : Subgroup H,
    IsCompact (W : Set H) ∧ IsOpen (W : Set H) ∧
      n = W.relIndex (W.map ψ.toMulEquiv.toMonoidHom)}
  have hGne : SG.Nonempty := by
    obtain ⟨S,hSc,hSo,-⟩ := exists_compact_open_subgroup_subset (G := G)
      isOpen_univ (Set.mem_univ 1)
    exact ⟨S.relIndex (S.map φ.toMulEquiv.toMonoidHom), S, hSc, hSo, rfl⟩
  have hHne : SH.Nonempty := by
    obtain ⟨S,hSc,hSo,-⟩ := exists_compact_open_subgroup_subset (G := H)
      isOpen_univ (Set.mem_univ 1)
    exact ⟨S.relIndex (S.map ψ.toMulEquiv.toMonoidHom), S, hSc, hSo, rfl⟩
  let F := φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom
  let X : Subgroup (G × H) := U.map F
  let A : Subgroup G := U.map (MonoidHom.fst G H)
  let Af : Subgroup G := A.map φ.toMulEquiv.toMonoidHom
  let B : Subgroup H := U.comap (MonoidHom.inr G H)
  let Bf : Subgroup H := B.map ψ.toMulEquiv.toMonoidHom
  let q0 : ↥X →* G := (MonoidHom.fst G H).comp X.subtype
  let p : ↥X →* ↥q0.range := q0.rangeRestrict
  let R : Subgroup ↥X := U.subgroupOf X
  obtain ⟨hXc,hXo⟩ := continuousMulEquiv_prod_image_compact_open φ ψ hUc hUo
  obtain ⟨hAc,hAo⟩ := subgroup_map_fst_compact_open hUc hUo
  obtain ⟨hAfc,hAfo⟩ := continuousMulEquiv_image_compact_open φ hAc hAo
  obtain ⟨hBc,hBo⟩ := subgroup_comap_inr_compact_open hUc hUo
  obtain ⟨hBfc,hBfo⟩ := continuousMulEquiv_image_compact_open ψ hBc hBo
  have hRopen : IsOpen (R : Set ↥X) := by
    rw [Subgroup.coe_subgroupOf]
    exact hUo.preimage continuous_subtype_val
  have hrange : q0.range = Af := by
    ext a
    constructor
    · rintro ⟨x, hxa⟩
      rcases x with ⟨x, hxX⟩
      rw [← hxa]
      rcases hxX with ⟨u, hu, hux⟩
      subst x
      refine ⟨u.1, ?_, rfl⟩
      exact ⟨u, hu, rfl⟩
    · rintro ⟨v, hv, hva⟩
      rw [← hva]
      rcases hv with ⟨u, hu, hu1⟩
      rw [← hu1]
      refine ⟨⟨(φ u.1, ψ u.2), ?_⟩, ?_⟩
      · exact ⟨u, hu, rfl⟩
      · rfl
  haveI : CompactSpace ↥X := isCompact_iff_compactSpace.mp hXc
  haveI : CompactSpace ↥q0.range := by
    rw [hrange]
    exact isCompact_iff_compactSpace.mp hAfc
  have hq0cont : Continuous q0 := continuous_fst.comp continuous_subtype_val
  have hpcont : Continuous p := by
    exact hq0cont.subtype_mk (fun x => ⟨x, rfl⟩)
  have hpopen : IsOpenMap p :=
    MonoidHom.isOpenMap_of_sigmaCompact p q0.rangeRestrict_surjective hpcont
  have hpRopen : IsOpen ((R.map p : Subgroup ↥q0.range) : Set ↥q0.range) := by
    rw [Subgroup.coe_map]
    exact hpopen _ hRopen
  have hpRfinite : Finite (↥q0.range ⧸ R.map p) :=
    Subgroup.quotient_finite_of_isOpen (R.map p) hpRopen
  haveI := hpRfinite
  have hpRfi : (R.map p).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let eA : ↥Af ≃* ↥q0.range := MulEquiv.subgroupCongr hrange.symm
  let Dq : Subgroup ↥q0.range := (A.subgroupOf Af).map ↑eA
  have hpR_le_Dq : R.map p ≤ Dq := by
    intro z hz
    rcases hz with ⟨r, hrR, hpr⟩
    rw [← hpr]
    refine ⟨eA.symm (p r), ?_, eA.apply_symm_apply _⟩
    change (eA.symm (p r)).val ∈ A
    change (r.val.1 : G) ∈ A
    change r.val ∈ U at hrR
    exact ⟨r.val, hrR, rfl⟩
  have hfirst_index : A.relIndex Af ≤ (R.map p).index := by
    have hD : Dq.index = A.relIndex Af := by
      dsimp [Dq]
      rw [Subgroup.index_map_equiv]
      rfl
    rw [← hD]
    exact Subgroup.index_antitone hpR_le_Dq
  have hsG : sInf SG ≤ A.relIndex Af :=
    Nat.sInf_le ⟨A,hAc,hAo,rfl⟩
  have hsG' : sInf SG ≤ (R.map p).index := hsG.trans hfirst_index
  have hsH : sInf SH ≤ B.relIndex Bf :=
    Nat.sInf_le ⟨B,hBc,hBo,rfl⟩
  have hfactor : R.relIndex p.ker = B.relIndex Bf := by
    simpa [F,X,B,Bf,q0,p,R] using relIndex_rangeRestrict_ker_fst φ ψ U
  have hsH' : sInf SH ≤ R.relIndex p.ker := by
    rw [hfactor]
    exact hsH
  have hJopen : IsOpen ((R ⊔ p.ker : Subgroup ↥X) : Set ↥X) := by
    let RO : OpenSubgroup ↥X := { toSubgroup := R, isOpen' := hRopen }
    exact Subgroup.isOpen_of_openSubgroup (R ⊔ p.ker) (U := RO) le_sup_left
  have hJcompact : IsCompact ((R ⊔ p.ker : Subgroup ↥X) : Set ↥X) := by
    exact isCompact_univ.of_isClosed_subset ((R ⊔ p.ker).isClosed_of_isOpen hJopen)
      (Set.subset_univ _)
  have hRsubJopen : IsOpen ((R.subgroupOf (R ⊔ p.ker) : Subgroup ↥(R ⊔ p.ker)) :
      Set ↥(R ⊔ p.ker)) := by
    rw [Subgroup.coe_subgroupOf]
    exact hRopen.preimage continuous_subtype_val
  have hJfinite : Finite (↥(R ⊔ p.ker) ⧸ R.subgroupOf (R ⊔ p.ker)) := by
    haveI : CompactSpace ↥(R ⊔ p.ker) := isCompact_iff_compactSpace.mp hJcompact
    exact Subgroup.quotient_finite_of_isOpen _ hRsubJopen
  haveI := hJfinite
  have hdecomp := Subgroup.map_index_mul_relIndex_ker_le_index p
    q0.rangeRestrict_surjective R
  rw [hfactor] at hdecomp
  have hdecomp' : (R.map p).index * B.relIndex Bf ≤ U.relIndex X := by
    simpa [Subgroup.relIndex, R] using hdecomp
  have hmul : sInf SG * sInf SH ≤ (R.map p).index * B.relIndex Bf := by
    exact Nat.mul_le_mul hsG' hsH
  exact hmul.trans hdecomp'

/- verified submission -/
theorem scale_prod
    {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [TotallyDisconnectedSpace H]
    (φ : G ≃ₜ* G) (ψ : H ≃ₜ* H) :
    sInf {n : ℕ | ∃ U : Subgroup (G × H),
      IsCompact (U : Set (G × H)) ∧ IsOpen (U : Set (G × H)) ∧
        n = U.relIndex (U.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom))} =
      sInf {n : ℕ | ∃ V : Subgroup G,
        IsCompact (V : Set G) ∧ IsOpen (V : Set G) ∧
          n = V.relIndex (V.map φ.toMulEquiv.toMonoidHom)} *
      sInf {n : ℕ | ∃ W : Subgroup H,
        IsCompact (W : Set H) ∧ IsOpen (W : Set H) ∧
          n = W.relIndex (W.map ψ.toMulEquiv.toMonoidHom)} := by
  let SP : Set ℕ := {n : ℕ | ∃ U : Subgroup (G × H),
    IsCompact (U : Set (G × H)) ∧ IsOpen (U : Set (G × H)) ∧
      n = U.relIndex (U.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom))}
  let SG : Set ℕ := {n : ℕ | ∃ V : Subgroup G,
    IsCompact (V : Set G) ∧ IsOpen (V : Set G) ∧
      n = V.relIndex (V.map φ.toMulEquiv.toMonoidHom)}
  let SH : Set ℕ := {n : ℕ | ∃ W : Subgroup H,
    IsCompact (W : Set H) ∧ IsOpen (W : Set H) ∧
      n = W.relIndex (W.map ψ.toMulEquiv.toMonoidHom)}
  have hPne : SP.Nonempty := by
    obtain ⟨S,hSc,hSo,-⟩ := exists_compact_open_subgroup_subset (G := G × H)
      isOpen_univ (Set.mem_univ 1)
    exact ⟨S.relIndex (S.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom)),
      S, hSc, hSo, rfl⟩
  have hGne : SG.Nonempty := by
    obtain ⟨S,hSc,hSo,-⟩ := exists_compact_open_subgroup_subset (G := G)
      isOpen_univ (Set.mem_univ 1)
    exact ⟨S.relIndex (S.map φ.toMulEquiv.toMonoidHom), S, hSc, hSo, rfl⟩
  have hHne : SH.Nonempty := by
    obtain ⟨S,hSc,hSo,-⟩ := exists_compact_open_subgroup_subset (G := H)
      isOpen_univ (Set.mem_univ 1)
    exact ⟨S.relIndex (S.map ψ.toMulEquiv.toMonoidHom), S, hSc, hSo, rfl⟩
  apply le_antisymm
  · obtain ⟨V,hVc,hVo,hVmin⟩ := Nat.sInf_mem hGne
    obtain ⟨W,hWc,hWo,hWmin⟩ := Nat.sInf_mem hHne
    have hprod_mem : sInf SG * sInf SH ∈ SP := by
      refine ⟨V.prod W, ?_, ?_, ?_⟩
      · rw [Subgroup.coe_prod]
        exact hVc.prod hWc
      · rw [Subgroup.coe_prod]
        exact hVo.prod hWo
      · calc
          sInf SG * sInf SH =
              V.relIndex (V.map φ.toMulEquiv.toMonoidHom) *
                W.relIndex (W.map ψ.toMulEquiv.toMonoidHom) := by
            rw [hVmin, hWmin]
          _ = (V.prod W).relIndex
              ((V.prod W).map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom)) := by
            exact (relIndex_prod_map V W φ.toMulEquiv.toMonoidHom ψ.toMulEquiv.toMonoidHom).symm
    exact Nat.sInf_le hprod_mem
  · apply le_csInf hPne
    intro n hn
    rcases hn with ⟨U,hUc,hUo,hn⟩
    rw [hn]
    exact scale_prod_lower φ ψ hUc hUo

end Rollout_p1384_scale_prod

namespace Rollout_p3019_laurent_circulant_kernel

/- accepted add_to_file helper 1 -/
lemma eq_of_forall_sub_natCast_zmod
    {m a : ℕ} [NeZero m] {α : Type*} {v : ZMod m → α}
    (hcop : Nat.Coprime a m)
    (h : ∀ i : ZMod m, v i = v (i - (a : ZMod m))) :
    ∀ i j : ZMod m, v i = v j := by
  let u : ZMod m := a
  have hu : IsUnit u := by
    dsimp [u]
    exact (ZMod.isUnit_iff_coprime a m).2 hcop
  have hiter : ∀ (c : ℕ) (i : ZMod m), v i = v (i - (c : ZMod m) * u) := by
    intro c
    induction c with
    | zero =>
        intro i
        simp
    | succ c hc =>
        intro i
        calc
          v i = v (i - (c : ZMod m) * u) := hc i
          _ = v ((i - (c : ZMod m) * u) - u) := h _
          _ = v (i - ((c + 1 : ℕ) : ZMod m) * u) := by
            congr 1
            simp [Nat.cast_add, add_mul]
            ring
  intro i j
  let c : ℕ := (((i - j) * u⁻¹).val)
  have hcast : (c : ZMod m) = (i - j) * u⁻¹ := by
    dsimp [c]
    simpa using (ZMod.natCast_val ((i - j) * u⁻¹) : (((i - j) * u⁻¹).val : ZMod m) = ((i - j) * u⁻¹).cast)
  have hcu : (c : ZMod m) * u = i - j := by
    rw [hcast]
    calc
      ((i - j) * u⁻¹) * u = (i - j) * (u⁻¹ * u) := by ring
      _ = i - j := by rw [ZMod.inv_mul_of_unit u hu]; ring
  calc
    v i = v (i - (c : ZMod m) * u) := hiter c i
    _ = v j := by
      rw [hcu]
      congr 1
      abel

/- accepted add_to_file helper 2 -/
noncomputable def laurentCirculantB
    (a b : ℕ) [NeZero (a + b)] (ε : ℤ) :
    Matrix (ZMod (a + b)) (ZMod (a + b)) (LaurentPolynomial ℤ) := fun i j =>
  if i - j = ((-(a : ℤ) : ℤ) : ZMod (a + b)) then
    LaurentPolynomial.C ε * LaurentPolynomial.T 1
  else if i - j ∈ (Finset.Ico 1 a).image
      (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a + b))) then
    1 + LaurentPolynomial.C ε * LaurentPolynomial.T 1
  else if i - j = 0 then
    1 - LaurentPolynomial.C ε * LaurentPolynomial.T 1
  else if i - j ∈ (Finset.Ico 1 a).image
      (fun k : ℕ => (k : ZMod (a + b))) then
    -1 - LaurentPolynomial.C ε * LaurentPolynomial.T 1
  else if i - j = (a : ZMod (a + b)) then
    -1
  else
    0

/- accepted add_to_file helper 3 -/
lemma sum_ite_eq_image_ite
    {ι α R : Type*} [DecidableEq ι] [DecidableEq α] [Semiring R]
    (s : Finset ι) (f : ι → α) (d : α)
    (hinj : Set.InjOn f s) :
    (∑ k ∈ s, (if d = f k then (1 : R) else 0)) =
      if d ∈ s.image f then 1 else 0 := by
  by_cases hd : d ∈ s.image f
  · rw [if_pos hd]
    rcases Finset.mem_image.mp hd with ⟨k, hk, hkd⟩
    rw [Finset.sum_eq_single_of_mem k hk]
    · rw [← hkd]
      simp
    · intro l hl hlk
      have hfl : f l ≠ d := by
        intro hfl
        apply hlk
        apply hinj hl hk
        rw [hfl, hkd]
      rw [if_neg]
      exact ne_comm.mp hfl
  · rw [if_neg hd]
    apply Finset.sum_eq_zero
    intro k hk
    have hne : d ≠ f k := by
      intro h
      exact hd (Finset.mem_image.mpr ⟨k, hk, h.symm⟩)
    rw [if_neg hne]

/- accepted add_to_file helper 4 -/
lemma zmod_natCast_injOn_Ico_one
    {m a : ℕ} [NeZero m] (ham : a < m) :
    Set.InjOn (fun k : ℕ => (k : ZMod m)) (Finset.Ico 1 a) := by
  intro k hk l hl hkl
  have hklt : k < m := lt_trans (Finset.mem_Ico.mp hk).2 ham
  have hllt : l < m := lt_trans (Finset.mem_Ico.mp hl).2 ham
  have hmod : k % m = l % m := (ZMod.natCast_eq_natCast_iff' k l m).mp hkl
  rwa [Nat.mod_eq_of_lt hklt, Nat.mod_eq_of_lt hllt] at hmod

lemma zmod_int_sub_natCast_injOn_Ico_one
    {m a : ℕ} [NeZero m] (ham : a < m) :
    Set.InjOn
      (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod m))
      (Finset.Ico 1 a) := by
  intro k hk l hl hkl
  have hcast : (k : ZMod m) = (l : ZMod m) := by
    have h := congrArg (fun z : ZMod m => z + (a : ZMod m)) hkl
    simpa using h
  exact zmod_natCast_injOn_Ico_one ham hk hl hcast

/- accepted add_to_file helper 5 -/
lemma zmod_intCast_ne_of_abs_sub_lt {m : ℕ} [NeZero m] {x y : ℤ}
    (hdiff : |x - y| < (m : ℤ)) (hxy : x ≠ y) :
    (x : ZMod m) ≠ (y : ZMod m) := by
  intro h
  have hmod : x ≡ y [ZMOD (m : ℤ)] :=
    (ZMod.intCast_eq_intCast_iff x y m).mp h
  have hdvd : (m : ℤ) ∣ y - x := Int.modEq_iff_dvd.mp hmod
  have hzero : y - x = 0 := by
    apply Int.eq_zero_of_abs_lt_dvd hdvd
    rw [abs_sub_comm]
    exact hdiff
  exact hxy (by omega)

/- accepted add_to_file helper 6 -/
lemma zmod_neg_a_not_mem_shift_image
    (a b : ℕ) [NeZero (a+b)] :
    (((-(a : ℤ) : ℤ) : ZMod (a+b)) ∉
      (Finset.Ico 1 a).image (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))) := by
  intro h
  rcases Finset.mem_image.mp h with ⟨k,hk,hka⟩
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have hk2 : k < a := (Finset.mem_Ico.mp hk).2
  have hne := zmod_intCast_ne_of_abs_sub_lt (m:=a+b)
    (x:=-(a:ℤ)) (y:=(k:ℤ)-(a:ℤ)) ?_ ?_
  · exact hne hka.symm
  · have hrewrite : (-(a : ℤ) : ℤ) - ((k : ℤ) - (a : ℤ)) = -(k : ℤ) := by ring
    rw [hrewrite, abs_neg]
    norm_num
    omega
  · omega

lemma zmod_neg_a_ne_zero (a b : ℕ) [NeZero (a+b)] (ha : 0 < a) (hab : a < b) :
    (((-(a : ℤ) : ℤ) : ZMod (a+b)) ≠ 0) := by
  have hneInt : (((-(a : ℤ) : ℤ) : ZMod (a+b)) ≠ ((0 : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b) (x:=-(a:ℤ)) (y:=0)
    · rw [sub_zero, abs_neg]
      norm_num
      omega
    · omega
  simpa using hneInt

lemma zmod_neg_a_not_mem_nat_image
    (a b : ℕ) [NeZero (a+b)] (hab : a < b) :
    (((-(a : ℤ) : ℤ) : ZMod (a+b)) ∉
      (Finset.Ico 1 a).image (fun k : ℕ => (k : ZMod (a+b)))) := by
  intro h
  rcases Finset.mem_image.mp h with ⟨k,hk,hka⟩
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have hk2 : k < a := (Finset.mem_Ico.mp hk).2
  have hneInt : (((-(a : ℤ) : ℤ) : ZMod (a+b)) ≠ (((k : ℤ) : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b) (x:=-(a:ℤ)) (y:=(k:ℤ))
    · have hrewrite : (-(a : ℤ) : ℤ) - (k : ℤ) = -(((a + k : ℕ) : ℤ)) := by
        norm_num
        ring
      rw [hrewrite, abs_neg]
      have hnonneg : 0 ≤ (((a + k : ℕ) : ℤ)) := by positivity
      rw [abs_of_nonneg hnonneg]
      have hlt : a + k < a + b := by omega
      exact_mod_cast hlt
    · omega
  have hne : (((-(a : ℤ) : ℤ) : ZMod (a+b)) ≠ (k : ZMod (a+b))) := by
    simpa using hneInt
  exact hne hka.symm

lemma zmod_neg_a_ne_a (a b : ℕ) [NeZero (a+b)] (ha : 0 < a) (hab : a < b) :
    (((-(a : ℤ) : ℤ) : ZMod (a+b)) ≠ (a : ZMod (a+b))) := by
  have hneInt : (((-(a : ℤ) : ℤ) : ZMod (a+b)) ≠ (((a : ℤ) : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b) (x:=-(a:ℤ)) (y:=(a:ℤ))
    · have hrewrite : (-(a : ℤ) : ℤ) - (a : ℤ) = -(((2 * a : ℕ) : ℤ)) := by
        norm_num
        ring
      rw [hrewrite, abs_neg]
      have hnonneg : 0 ≤ (((2 * a : ℕ) : ℤ)) := by positivity
      rw [abs_of_nonneg hnonneg]
      have hlt : 2 * a < a + b := by omega
      exact_mod_cast hlt
    · omega
  simpa using hneInt

/- accepted add_to_file helper 7 -/
lemma zmod_shift_image_ne_zero
    (a b : ℕ) [NeZero (a+b)] {d : ZMod (a+b)}
    (hd : d ∈ (Finset.Ico 1 a).image
      (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))) :
    d ≠ 0 := by
  rcases Finset.mem_image.mp hd with ⟨k,hk,rfl⟩
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have hk2 : k < a := (Finset.mem_Ico.mp hk).2
  have hneInt : ((((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)) ≠ ((0 : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b)
      (x:=(k:ℤ)-(a:ℤ)) (y:=0)
    · rw [sub_zero]
      have hrewrite : (k : ℤ) - (a : ℤ) = -(((a - k : ℕ) : ℤ)) := by
        omega
      rw [hrewrite, abs_neg]
      have hnonneg : 0 ≤ (((a - k : ℕ) : ℤ)) := by positivity
      rw [abs_of_nonneg hnonneg]
      have hknat : a - k < a + b := by omega
      exact_mod_cast hknat
    · omega
  simpa using hneInt

lemma zmod_shift_image_disjoint_nat_image
    (a b : ℕ) [NeZero (a+b)] (hab : a < b) {d : ZMod (a+b)}
    (hd : d ∈ (Finset.Ico 1 a).image
      (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))) :
    d ∉ (Finset.Ico 1 a).image (fun k : ℕ => (k : ZMod (a+b))) := by
  rcases Finset.mem_image.mp hd with ⟨k,hk,rfl⟩
  intro hP
  rcases Finset.mem_image.mp hP with ⟨l,hl,hkl⟩
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have hk2 : k < a := (Finset.mem_Ico.mp hk).2
  have hl1 : 1 ≤ l := (Finset.mem_Ico.mp hl).1
  have hl2 : l < a := (Finset.mem_Ico.mp hl).2
  have hneInt : ((((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)) ≠ (((l : ℤ) : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b)
      (x:=(k:ℤ)-(a:ℤ)) (y:=(l:ℤ))
    · have hrewrite : ((k : ℤ) - (a : ℤ)) - (l : ℤ) =
          -((((a + l) - k : ℕ) : ℤ)) := by
        omega
      rw [hrewrite, abs_neg]
      have hnonneg : 0 ≤ ((((a + l) - k : ℕ) : ℤ)) := by positivity
      rw [abs_of_nonneg hnonneg]
      have hlt : (a + l) - k < a + b := by omega
      exact_mod_cast hlt
    · omega
  have hne : ((((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)) ≠ (l : ZMod (a+b))) := by
    simpa using hneInt
  exact hne hkl.symm

lemma zmod_shift_image_ne_a
    (a b : ℕ) [NeZero (a+b)] (hab : a < b) {d : ZMod (a+b)}
    (hd : d ∈ (Finset.Ico 1 a).image
      (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))) :
    d ≠ (a : ZMod (a+b)) := by
  rcases Finset.mem_image.mp hd with ⟨k,hk,rfl⟩
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have hk2 : k < a := (Finset.mem_Ico.mp hk).2
  have hneInt : ((((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)) ≠ (((a : ℤ) : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b)
      (x:=(k:ℤ)-(a:ℤ)) (y:=(a:ℤ))
    · have hrewrite : ((k : ℤ) - (a : ℤ)) - (a : ℤ) =
          -(((2 * a - k : ℕ) : ℤ)) := by
        omega
      rw [hrewrite, abs_neg]
      have hnonneg : 0 ≤ (((2 * a - k : ℕ) : ℤ)) := by positivity
      rw [abs_of_nonneg hnonneg]
      have hlt : 2 * a - k < a + b := by omega
      exact_mod_cast hlt
    · omega
  simpa using hneInt

/- accepted add_to_file helper 8 -/
lemma zmod_zero_not_mem_nat_image
    (a b : ℕ) [NeZero (a+b)] :
    (0 : ZMod (a+b)) ∉
      (Finset.Ico 1 a).image (fun k : ℕ => (k : ZMod (a+b))) := by
  intro h
  rcases Finset.mem_image.mp h with ⟨k,hk,hka⟩
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have hk2 : k < a := (Finset.mem_Ico.mp hk).2
  have hneInt : (((0 : ℤ) : ZMod (a+b)) ≠ (((k : ℤ) : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b)
      (x:=0) (y:=(k:ℤ))
    · rw [zero_sub, abs_neg]
      norm_num
      omega
    · omega
  have hne : (0 : ZMod (a+b)) ≠ (k : ZMod (a+b)) := by
    simpa using hneInt
  exact hne hka.symm

lemma zmod_zero_ne_a (a b : ℕ) [NeZero (a+b)] (ha : 0 < a) (hab : a < b) :
    (0 : ZMod (a+b)) ≠ (a : ZMod (a+b)) := by
  have hneInt : (((0 : ℤ) : ZMod (a+b)) ≠ (((a : ℤ) : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b) (x:=0) (y:=(a:ℤ))
    · rw [zero_sub, abs_neg]
      norm_num
      omega
    · omega
  simpa using hneInt

lemma zmod_nat_image_ne_a
    (a b : ℕ) [NeZero (a+b)] {d : ZMod (a+b)}
    (hd : d ∈ (Finset.Ico 1 a).image (fun k : ℕ => (k : ZMod (a+b)))) :
    d ≠ (a : ZMod (a+b)) := by
  rcases Finset.mem_image.mp hd with ⟨k,hk,rfl⟩
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have hk2 : k < a := (Finset.mem_Ico.mp hk).2
  have hneInt : ((((k : ℤ) : ℤ) : ZMod (a+b)) ≠ (((a : ℤ) : ℤ) : ZMod (a+b))) := by
    apply zmod_intCast_ne_of_abs_sub_lt (m:=a+b)
      (x:=(k:ℤ)) (y:=(a:ℤ))
    · have hrewrite : (k : ℤ) - (a : ℤ) = -(((a - k : ℕ) : ℤ)) := by
        omega
      rw [hrewrite, abs_neg]
      have hnonneg : 0 ≤ (((a - k : ℕ) : ℤ)) := by positivity
      rw [abs_of_nonneg hnonneg]
      have hlt : a - k < a + b := by omega
      exact_mod_cast hlt
    · omega
  have hne : ((k : ZMod (a+b)) ≠ (a : ZMod (a+b))) := by
    simpa using hneInt
  exact hne

/- accepted add_to_file helper 9 -/
lemma zmod_a_not_mem_shift_image
    (a b : ℕ) [NeZero (a+b)] (hab : a < b) :
    (a : ZMod (a+b)) ∉
      (Finset.Ico 1 a).image
        (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b))) := by
  intro h
  exact zmod_shift_image_ne_a a b hab h rfl

lemma zmod_a_not_mem_nat_image
    (a b : ℕ) [NeZero (a+b)] :
    (a : ZMod (a+b)) ∉
      (Finset.Ico 1 a).image (fun k : ℕ => (k : ZMod (a+b))) := by
  intro h
  exact zmod_nat_image_ne_a a b h rfl

/- accepted add_to_file helper 10 -/
lemma zmod_zero_not_mem_shift_image
    (a b : ℕ) [NeZero (a+b)] :
    (0 : ZMod (a+b)) ∉
      (Finset.Ico 1 a).image
        (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b))) := by
  intro h
  exact zmod_shift_image_ne_zero a b h rfl

/- accepted add_to_file helper 11 -/
lemma laurentCirculantB_eq_sum
    (a b : ℕ) [NeZero (a + b)] (ha : 0 < a) (hab : a < b) (ε : ℤ) :
    let t : LaurentPolynomial ℤ := LaurentPolynomial.C ε * LaurentPolynomial.T 1
    let D : ZMod (a+b) → Matrix (ZMod (a+b)) (ZMod (a+b)) (LaurentPolynomial ℤ) :=
      fun c i j => if i - j = c then 1 else 0
    laurentCirculantB a b ε =
      t • D (((-(a : ℤ) : ℤ) : ZMod (a+b))) +
      (1 + t) • (∑ k ∈ Finset.Ico 1 a, D (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b))) +
      (1 - t) • D 0 +
      (-1 - t) • (∑ k ∈ Finset.Ico 1 a, D (k : ZMod (a+b))) +
      (-1) • D (a : ZMod (a+b)) := by
  intro t D
  apply Matrix.ext
  intro i j
  have ham : a < a + b := Nat.lt_add_of_pos_right (Nat.lt_trans ha hab)
  simp only [laurentCirculantB, D, Matrix.add_apply, Matrix.smul_apply]
  rw [Matrix.sum_apply i j (Finset.Ico 1 a)
    (fun x => (fun i j => if i - j = (((x : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)) then (1:LaurentPolynomial ℤ) else 0))]
  rw [Matrix.sum_apply i j (Finset.Ico 1 a)
    (fun x => (fun i j => if i - j = (x : ZMod (a+b)) then (1:LaurentPolynomial ℤ) else 0))]
  rw [sum_ite_eq_image_ite (Finset.Ico 1 a)
    (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b))) (i-j)
    (zmod_int_sub_natCast_injOn_Ico_one ham)]
  rw [sum_ite_eq_image_ite (Finset.Ico 1 a)
    (fun k : ℕ => (k : ZMod (a+b))) (i-j)
    (zmod_natCast_injOn_Ico_one ham)]
  by_cases hA : i - j = (((-(a : ℤ) : ℤ) : ZMod (a+b)))
  · have hN := zmod_neg_a_not_mem_shift_image a b
    have hZ := zmod_neg_a_ne_zero a b ha hab
    have hP := zmod_neg_a_not_mem_nat_image a b hab
    have hAp := zmod_neg_a_ne_a a b ha hab
    simp only [hA, hN, hZ, hP, hAp, if_true, if_false, smul_eq_mul, mul_one, mul_zero,
      add_zero, zero_add, neg_mul, one_mul]
    ring
  · by_cases hN : i - j ∈ (Finset.Ico 1 a).image
        (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))
    · have hZ : i - j ≠ 0 := zmod_shift_image_ne_zero a b hN
      have hP : i - j ∉ (Finset.Ico 1 a).image (fun k : ℕ => (k : ZMod (a+b))) :=
        zmod_shift_image_disjoint_nat_image a b hab hN
      have hAp : i - j ≠ (a : ZMod (a+b)) := zmod_shift_image_ne_a a b hab hN
      simp only [hA, hN, hZ, hP, hAp, if_true, if_false, smul_eq_mul, mul_one, mul_zero,
        add_zero, zero_add, neg_mul, one_mul]
      ring
    · by_cases hZ : i - j = 0
      · have hA0 : (0 : ZMod (a+b)) ≠ (((-(a : ℤ) : ℤ) : ZMod (a+b))) :=
          (zmod_neg_a_ne_zero a b ha hab).symm
        have hN0 := zmod_zero_not_mem_shift_image a b
        have hP0 := zmod_zero_not_mem_nat_image a b
        have hAp0 := zmod_zero_ne_a a b ha hab
        simp only [hZ, hA0, hN0, hP0, hAp0, if_true, if_false, smul_eq_mul, mul_one, mul_zero,
          add_zero, zero_add, neg_mul, one_mul]
        ring
      · by_cases hP : i - j ∈ (Finset.Ico 1 a).image (fun k : ℕ => (k : ZMod (a+b)))
        · have hAp : i - j ≠ (a : ZMod (a+b)) := zmod_nat_image_ne_a a b hP
          simp only [hA, hN, hZ, hP, hAp, if_true, if_false, smul_eq_mul, mul_one, mul_zero,
            add_zero, zero_add, neg_mul, one_mul]
          ring
        · by_cases hAp : i - j = (a : ZMod (a+b))
          · have hA' : (a : ZMod (a+b)) ≠ (((-(a : ℤ) : ℤ) : ZMod (a+b))) :=
              (zmod_neg_a_ne_a a b ha hab).symm
            have hN' := zmod_a_not_mem_shift_image a b hab
            have hZ' := (zmod_zero_ne_a a b ha hab).symm
            have hP' := zmod_a_not_mem_nat_image a b
            simp only [hAp, hA', hN', hZ', hP', if_true, if_false, smul_eq_mul, mul_one, mul_zero,
              add_zero, zero_add, neg_mul, one_mul]
            ring
          · simp only [hA, hN, hZ, hP, hAp, if_true, if_false, smul_eq_mul, mul_one, mul_zero,
              add_zero, zero_add, neg_mul, one_mul]
            ring

/- accepted add_to_file helper 12 -/
lemma zmod_diag_mulVec {m : ℕ} [NeZero m] {R : Type*} [Ring R]
    (c : ZMod m) (v : ZMod m → R) (i : ZMod m) :
    Matrix.mulVec ((fun i j : ZMod m => if i - j = c then (1 : R) else 0) :
      Matrix (ZMod m) (ZMod m) R) v i =
      v (i - c) := by
  rw [Matrix.mulVec]
  simp [dotProduct]
  rw [Finset.sum_eq_single (i - c)]
  · simp
  · intro x _ hx
    have hne : i - x ≠ c := by
      intro h
      apply hx
      rw [← h]
      abel
    simp [hne]
  · simp

/- accepted add_to_file helper 13 -/
lemma zmod_shift_interval_sum
    (a b : ℕ) [NeZero (a+b)] (ha : 0 < a)
    (v : ZMod (a+b) → LaurentPolynomial ℤ) (r : ZMod (a+b)) :
    (∑ k ∈ Finset.Ico 1 a,
      v (r - (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))) =
    ∑ j ∈ Finset.range (a-1), v (r + ((j + 1 : ℕ) : ZMod (a+b))) := by
  let m := a - 1
  let g : ℕ → LaurentPolynomial ℤ := fun z => v (r + ((z + 1 : ℕ) : ZMod (a+b)))
  have hpoint :
      (∑ k ∈ Finset.Ico 1 a,
        v (r - (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))) =
      ∑ j ∈ Finset.range m, g (m - 1 - j) := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < a - 1 := Finset.mem_range.mp hj
    dsimp [g, m] at hj ⊢
    have hnat : a - 1 - 1 - j + 1 = a - 1 - j := by omega
    rw [hnat]
    congr 1
    rw [Nat.cast_sub (by omega : j ≤ a - 1)]
    rw [Nat.cast_sub (by omega : 1 ≤ a)]
    push_cast
    abel
  rw [hpoint]
  simpa [g, m] using (Finset.sum_range_reflect g m)

/- accepted add_to_file helper 14 -/
lemma zmod_window_pos_sum
    (a b : ℕ) [NeZero (a+b)]
    (v : ZMod (a+b) → LaurentPolynomial ℤ) (r : ZMod (a+b)) :
    (∑ k ∈ Finset.Ico 1 (a+1),
      v ((r + (a : ZMod (a+b))) - (k : ZMod (a+b)))) =
    ∑ j ∈ Finset.range a, v (r + (j : ZMod (a+b))) := by
  let g : ℕ → LaurentPolynomial ℤ := fun z => v (r + (z : ZMod (a+b)))
  have hpoint :
      (∑ k ∈ Finset.Ico 1 (a+1),
        v ((r + (a : ZMod (a+b))) - (k : ZMod (a+b)))) =
      ∑ j ∈ Finset.range a, g (a - 1 - j) := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < a := Finset.mem_range.mp hj
    dsimp [g]
    congr 1
    rw [Nat.cast_sub (by omega : j ≤ a - 1)]
    rw [Nat.cast_sub (by omega : 1 ≤ a)]
    push_cast
    abel
  rw [hpoint]
  simpa [g] using (Finset.sum_range_reflect g a)

/- accepted add_to_file helper 15 -/
lemma zmod_window_pos_succ_sum
    (a b : ℕ) [NeZero (a+b)]
    (v : ZMod (a+b) → LaurentPolynomial ℤ) (r : ZMod (a+b)) :
    (∑ k ∈ Finset.Ico 1 (a+1),
      v ((r + (a : ZMod (a+b)) + 1) - (k : ZMod (a+b)))) =
    ∑ j ∈ Finset.range a, v (r + ((j + 1 : ℕ) : ZMod (a+b))) := by
  let g : ℕ → LaurentPolynomial ℤ := fun z => v (r + ((z + 1 : ℕ) : ZMod (a+b)))
  have hpoint :
      (∑ k ∈ Finset.Ico 1 (a+1),
        v ((r + (a : ZMod (a+b)) + 1) - (k : ZMod (a+b)))) =
      ∑ j ∈ Finset.range a, g (a - 1 - j) := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt : j < a := Finset.mem_range.mp hj
    dsimp [g]
    have hnat : a - 1 - j + 1 = a - j := by omega
    rw [hnat]
    congr 1
    rw [Nat.cast_sub (by omega : j ≤ a)]
    push_cast
    abel
  rw [hpoint]
  simpa [g] using (Finset.sum_range_reflect g a)

/- accepted add_to_file helper 16 -/
lemma zmod_window_neg_sum
    (a b : ℕ) [NeZero (a+b)]
    (v : ZMod (a+b) → LaurentPolynomial ℤ) (r : ZMod (a+b)) :
    (∑ k ∈ Finset.Ico 1 (a+1), v (r - (k : ZMod (a+b)))) =
      ∑ j ∈ Finset.range a, v (r - ((j + 1 : ℕ) : ZMod (a+b))) := by
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  norm_num [Nat.add_comm]

/- accepted add_to_file helper 17 -/
lemma zmod_window_neg_succ_sum
    (a b : ℕ) [NeZero (a+b)]
    (v : ZMod (a+b) → LaurentPolynomial ℤ) (r : ZMod (a+b)) :
    (∑ k ∈ Finset.Ico 1 (a+1), v ((r + 1) - (k : ZMod (a+b)))) =
      ∑ j ∈ Finset.range a, v (r - (j : ZMod (a+b))) := by
  rw [Finset.sum_Ico_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  push_cast
  abel

/- accepted add_to_file helper 18 -/
lemma laurentCirculantB_mulVec_factor
    (a b : ℕ) [NeZero (a + b)] (ha : 0 < a) (hab : a < b) (ε : ℤ)
    (v : ZMod (a+b) → LaurentPolynomial ℤ) (r : ZMod (a+b)) :
    let t : LaurentPolynomial ℤ := LaurentPolynomial.C ε * LaurentPolynomial.T 1
    let w : ZMod (a+b) → LaurentPolynomial ℤ := fun x =>
      ∑ k ∈ Finset.Ico 1 (a+1), v (x - (k : ZMod (a+b)))
    (laurentCirculantB a b ε).mulVec v r =
      (w (r + (a : ZMod (a+b))) - w r) +
        t * (w (r + (a : ZMod (a+b)) + 1) - w (r + 1)) := by
  intro t w
  have hdirect :
      (laurentCirculantB a b ε).mulVec v r =
      t * v (r - (((-(a : ℤ) : ℤ) : ZMod (a+b)))) +
      (1 + t) * (∑ k ∈ Finset.Ico 1 a,
        v (r - (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))) +
      (1 - t) * v r +
      (-1 - t) * (∑ k ∈ Finset.Ico 1 a,
        v (r - (k : ZMod (a+b)))) +
      (-1) * v (r - (a : ZMod (a+b))) := by
    let D : ZMod (a+b) → Matrix (ZMod (a+b)) (ZMod (a+b)) (LaurentPolynomial ℤ) :=
      fun c i j => if i - j = c then 1 else 0
    have hB := laurentCirculantB_eq_sum a b ha hab ε
    rw [show laurentCirculantB a b ε =
        t • D (((-(a : ℤ) : ℤ) : ZMod (a+b))) +
        (1 + t) • (∑ k ∈ Finset.Ico 1 a, D (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b))) +
        (1 - t) • D 0 +
        (-1 - t) • (∑ k ∈ Finset.Ico 1 a, D (k : ZMod (a+b))) +
        (-1) • D (a : ZMod (a+b)) from hB]
    simp [D, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sum_mulVec, zmod_diag_mulVec]
    rw [Matrix.neg_mulVec]
    change - Matrix.mulVec ((fun i j : ZMod (a+b) => if i - j = (a : ZMod (a+b)) then (1 : LaurentPolynomial ℤ) else 0) :
        Matrix (ZMod (a+b)) (ZMod (a+b)) (LaurentPolynomial ℤ)) v r = -v (r - (a : ZMod (a+b)))
    rw [zmod_diag_mulVec]
  have hNmid :
      (∑ k ∈ Finset.Ico 1 a,
        v (r - (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a+b)))) =
      ∑ j ∈ Finset.range (a-1), v (r + ((j + 1 : ℕ) : ZMod (a+b))) :=
    zmod_shift_interval_sum a b ha v r
  have hPmid :
      (∑ k ∈ Finset.Ico 1 a, v (r - (k : ZMod (a+b)))) =
      ∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b))) := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    norm_num [Nat.add_comm]
  have hS0 :
      (∑ j ∈ Finset.range a, v (r + (j : ZMod (a+b)))) =
      (∑ j ∈ Finset.range (a-1), v (r + ((j + 1 : ℕ) : ZMod (a+b)))) + v r := by
    have ha1 : a = (a - 1) + 1 := by omega
    have hrange : Finset.range a = Finset.range ((a - 1) + 1) := congrArg Finset.range ha1
    calc
      (∑ j ∈ Finset.range a, v (r + (j : ZMod (a+b))))
          = ∑ j ∈ Finset.range ((a - 1) + 1), v (r + (j : ZMod (a+b))) := by rw [hrange]
      _ = (∑ j ∈ Finset.range (a-1), v (r + ((j + 1 : ℕ) : ZMod (a+b)))) + v r := by
          rw [Finset.sum_range_succ']
          simp
  have hS1 :
      (∑ j ∈ Finset.range a, v (r + ((j + 1 : ℕ) : ZMod (a+b)))) =
      (∑ j ∈ Finset.range (a-1), v (r + ((j + 1 : ℕ) : ZMod (a+b)))) +
        v (r + (a : ZMod (a+b))) := by
    have ha1 : a = (a - 1) + 1 := by omega
    have hrange : Finset.range a = Finset.range ((a - 1) + 1) := congrArg Finset.range ha1
    calc
      (∑ j ∈ Finset.range a, v (r + ((j + 1 : ℕ) : ZMod (a+b))))
          = ∑ j ∈ Finset.range ((a - 1) + 1), v (r + ((j + 1 : ℕ) : ZMod (a+b))) := by rw [hrange]
      _ = (∑ j ∈ Finset.range (a-1), v (r + ((j + 1 : ℕ) : ZMod (a+b)))) +
            v (r + (a : ZMod (a+b))) := by
          rw [Finset.sum_range_succ]
          congr 1
          congr 1
          have hnat : a - 1 + 1 = a := by omega
          exact congrArg (fun z : ZMod (a+b) => r + z)
            (congrArg (fun n : ℕ => (n : ZMod (a+b))) hnat)
  have hT0 :
      (∑ j ∈ Finset.range a, v (r - ((j + 1 : ℕ) : ZMod (a+b)))) =
      (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) +
        v (r - (a : ZMod (a+b))) := by
    have ha1 : a = (a - 1) + 1 := by omega
    have hrange : Finset.range a = Finset.range ((a - 1) + 1) := congrArg Finset.range ha1
    calc
      (∑ j ∈ Finset.range a, v (r - ((j + 1 : ℕ) : ZMod (a+b))))
          = ∑ j ∈ Finset.range ((a - 1) + 1), v (r - ((j + 1 : ℕ) : ZMod (a+b))) := by rw [hrange]
      _ = (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) +
            v (r - (a : ZMod (a+b))) := by
          rw [Finset.sum_range_succ]
          congr 1
          congr 1
          have hnat : a - 1 + 1 = a := by omega
          exact congrArg (fun z : ZMod (a+b) => r - z)
            (congrArg (fun n : ℕ => (n : ZMod (a+b))) hnat)
  have hT1 :
      (∑ j ∈ Finset.range a, v (r - (j : ZMod (a+b)))) =
      v r + (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) := by
    have ha1 : a = (a - 1) + 1 := by omega
    have hrange : Finset.range a = Finset.range ((a - 1) + 1) := congrArg Finset.range ha1
    calc
      (∑ j ∈ Finset.range a, v (r - (j : ZMod (a+b))))
          = ∑ j ∈ Finset.range ((a - 1) + 1), v (r - (j : ZMod (a+b))) := by rw [hrange]
      _ = (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) + v r := by
          rw [Finset.sum_range_succ']
          simp
      _ = v r + (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) := by
          rw [add_comm]
  calc
    (laurentCirculantB a b ε).mulVec v r = _ := hdirect
    _ = (w (r + (a : ZMod (a+b))) - w r) +
        t * (w (r + (a : ZMod (a+b)) + 1) - w (r + 1)) := by
      dsimp [w]
      rw [zmod_window_pos_sum, zmod_window_neg_sum,
        zmod_window_pos_succ_sum, zmod_window_neg_succ_sum]
      rw [hS0, hS1, hT0, hT1, hNmid, hPmid]
      have hend : r - (((-(a : ℤ) : ℤ) : ZMod (a+b))) = r + (a : ZMod (a+b)) := by
        push_cast
        ring
      rw [hend]
      ring

/- accepted add_to_file helper 19 -/
lemma zmod_recur_eq_zero
    {m : ℕ} [NeZero m] {R : Type*} [CommRing R] [IsDomain R]
    {t : R} {x : ZMod m → R}
    (h : ∀ r : ZMod m, x r + t * x (r + 1) = 0)
    (ht : t ^ m ≠ (-1 : R) ^ m) :
    ∀ r : ZMod m, x r = 0 := by
  have hiter : ∀ (c : ℕ) (r : ZMod m),
      t ^ c * x (r + (c : ZMod m)) = (-1 : R) ^ c * x r := by
    intro c
    induction c with
    | zero =>
        intro r
        simp
    | succ c hc =>
        intro r
        have hstep : t * x ((r + (c : ZMod m)) + 1) = - x (r + (c : ZMod m)) :=
          eq_neg_of_add_eq_zero_right (h (r + (c : ZMod m)))
        have hindex : r + (((c + 1 : ℕ) : ZMod m)) = (r + (c : ZMod m)) + 1 := by
          simp [Nat.cast_add]
          ring
        calc
          t ^ (c + 1) * x (r + (((c + 1 : ℕ) : ZMod m)))
              = (t ^ c * t) * x ((r + (c : ZMod m)) + 1) := by
                rw [pow_succ, hindex]
          _ = t ^ c * (t * x ((r + (c : ZMod m)) + 1)) := by rw [mul_assoc]
          _ = t ^ c * (- x (r + (c : ZMod m))) := by rw [hstep]
          _ = - (t ^ c * x (r + (c : ZMod m))) := by ring
          _ = - ((-1 : R) ^ c * x r) := by rw [hc r]
          _ = (-1 : R) ^ (c + 1) * x r := by
                rw [pow_succ]
                ring
  intro r
  have hm := hiter m r
  have hcast : ((m : ZMod m) = 0) := by simp
  rw [hcast, add_zero] at hm
  have hprod : (t ^ m - (-1 : R) ^ m) * x r = 0 := by
    rw [sub_mul]
    rw [hm]
    ring
  have hcoeff : t ^ m - (-1 : R) ^ m ≠ 0 := sub_ne_zero.mpr ht
  exact (mul_eq_zero.mp hprod).resolve_left hcoeff

/- accepted add_to_file helper 20 -/
lemma laurent_neg_one_t_pow_ne
    (m n : ℕ) [NeZero m] :
    let t : LaurentPolynomial ℤ := LaurentPolynomial.C ((-1 : ℤ) ^ n) * LaurentPolynomial.T 1
    t ^ m ≠ (-1 : LaurentPolynomial ℤ) ^ m := by
  intro t
  have hε : ((-1 : ℤ) ^ n) ≠ 0 := by norm_num
  have hpow : t ^ m =
      LaurentPolynomial.C (((-1 : ℤ) ^ n) ^ m) * LaurentPolynomial.T (m : ℤ) := by
    dsimp [t]
    rw [mul_pow, map_pow, LaurentPolynomial.T_pow]
    simp
  have hdeg1 : (t ^ m).degree = (m : ℤ) := by
    rw [hpow]
    exact LaurentPolynomial.degree_C_mul_T (m : ℤ) (((-1 : ℤ) ^ n) ^ m)
      (pow_ne_zero m hε)
  have hconst : (-1 : LaurentPolynomial ℤ) ^ m =
      LaurentPolynomial.C (((-1 : ℤ) ^ m)) := by
    simp
  have hdeg2 : ((-1 : LaurentPolynomial ℤ) ^ m).degree = 0 := by
    rw [hconst]
    exact LaurentPolynomial.degree_C (pow_ne_zero m (by norm_num : (-1 : ℤ) ≠ 0))
  intro ht
  have hmdeg : (m : ℤ) = (0 : WithBot ℤ) := by
    calc
      (m : ℤ) = (t ^ m).degree := hdeg1.symm
      _ = ((-1 : LaurentPolynomial ℤ) ^ m).degree := congrArg LaurentPolynomial.degree ht
      _ = 0 := hdeg2
  have hmpos : (0 : WithBot ℤ) < (m : ℤ) := by
    have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    exact_mod_cast hm
  rw [hmdeg] at hmpos
  exact (lt_irrefl (0 : WithBot ℤ)) hmpos

/- accepted add_to_file helper 21 -/
lemma zmod_window_succ_sub
    (a b : ℕ) [NeZero (a+b)] (ha : 0 < a)
    (v : ZMod (a+b) → LaurentPolynomial ℤ) (r : ZMod (a+b)) :
    (∑ k ∈ Finset.Ico 1 (a+1), v ((r + 1) - (k : ZMod (a+b)))) -
      (∑ k ∈ Finset.Ico 1 (a+1), v (r - (k : ZMod (a+b)))) =
    v r - v (r - (a : ZMod (a+b))) := by
  rw [zmod_window_neg_succ_sum, zmod_window_neg_sum]
  have hT0 :
      (∑ j ∈ Finset.range a, v (r - ((j + 1 : ℕ) : ZMod (a+b)))) =
      (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) +
        v (r - (a : ZMod (a+b))) := by
    have ha1 : a = (a - 1) + 1 := by omega
    have hrange : Finset.range a = Finset.range ((a - 1) + 1) := congrArg Finset.range ha1
    calc
      (∑ j ∈ Finset.range a, v (r - ((j + 1 : ℕ) : ZMod (a+b))))
          = ∑ j ∈ Finset.range ((a - 1) + 1), v (r - ((j + 1 : ℕ) : ZMod (a+b))) := by rw [hrange]
      _ = (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) +
            v (r - (a : ZMod (a+b))) := by
          rw [Finset.sum_range_succ]
          congr 1
          congr 1
          have hnat : a - 1 + 1 = a := by omega
          exact congrArg (fun z : ZMod (a+b) => r - z)
            (congrArg (fun n : ℕ => (n : ZMod (a+b))) hnat)
  have hT1 :
      (∑ j ∈ Finset.range a, v (r - (j : ZMod (a+b)))) =
      v r + (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) := by
    have ha1 : a = (a - 1) + 1 := by omega
    have hrange : Finset.range a = Finset.range ((a - 1) + 1) := congrArg Finset.range ha1
    calc
      (∑ j ∈ Finset.range a, v (r - (j : ZMod (a+b))))
          = ∑ j ∈ Finset.range ((a - 1) + 1), v (r - (j : ZMod (a+b))) := by rw [hrange]
      _ = (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) + v r := by
          rw [Finset.sum_range_succ']
          simp
      _ = v r + (∑ j ∈ Finset.range (a-1), v (r - ((j + 1 : ℕ) : ZMod (a+b)))) := by
          rw [add_comm]
  rw [hT0, hT1]
  ring

/- verified submission -/
theorem laurent_circulant_kernel
    (a b n : ℕ) (ha : 0 < a) (hab : a < b) (hab_coprime : Nat.Coprime a b)
    (hn : 3 ≤ n) :
    let _ : NeZero (a + b) := ⟨Nat.ne_of_gt (Nat.add_pos_left ha b)⟩
    let R := LaurentPolynomial ℤ
    let ε : ℤ := (-1) ^ n
    let q : R := LaurentPolynomial.T 1
    let B : Matrix (ZMod (a + b)) (ZMod (a + b)) R := fun i j =>
      if i - j = ((-(a : ℤ) : ℤ) : ZMod (a + b)) then
        LaurentPolynomial.C ε * q
      else if i - j ∈ (Finset.Ico 1 a).image
          (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a + b))) then
        1 + LaurentPolynomial.C ε * q
      else if i - j = 0 then
        1 - LaurentPolynomial.C ε * q
      else if i - j ∈ (Finset.Ico 1 a).image
          (fun k : ℕ => (k : ZMod (a + b))) then
        -1 - LaurentPolynomial.C ε * q
      else if i - j = (a : ZMod (a + b)) then
        -1
      else
        0
    ∀ v : ZMod (a + b) → R, B.mulVec v = 0 → ∀ i j, v i = v j := by
  intro hNe R ε q B v hv i j
  have hv' : (laurentCirculantB a b ε).mulVec v = 0 := by
    change B.mulVec v = 0
    exact hv
  let t : LaurentPolynomial ℤ := LaurentPolynomial.C ε * LaurentPolynomial.T 1
  let w : ZMod (a+b) → LaurentPolynomial ℤ := fun x =>
    ∑ k ∈ Finset.Ico 1 (a+1), v (x - (k : ZMod (a+b)))
  let x : ZMod (a+b) → LaurentPolynomial ℤ := fun r =>
    w (r + (a : ZMod (a+b))) - w r
  have hrec : ∀ r : ZMod (a+b), x r + t * x (r + 1) = 0 := by
    intro r
    have hfac := laurentCirculantB_mulVec_factor a b ha hab ε v r
    have hidx : r + (a : ZMod (a+b)) + 1 = (r + 1) + (a : ZMod (a+b)) := by abel
    calc
      x r + t * x (r + 1) =
          (w (r + (a : ZMod (a+b))) - w r) +
            t * (w (r + (a : ZMod (a+b)) + 1) - w (r + 1)) := by
            show (w (r + (a : ZMod (a+b))) - w r) +
                t * (w ((r + 1) + (a : ZMod (a+b))) - w (r + 1)) =
              (w (r + (a : ZMod (a+b))) - w r) +
                t * (w (r + (a : ZMod (a+b)) + 1) - w (r + 1))
            rw [hidx]
      _ = (laurentCirculantB a b ε).mulVec v r := hfac.symm
      _ = 0 := congrFun hv' r
  have ht : t ^ (a+b) ≠ (-1 : LaurentPolynomial ℤ) ^ (a+b) := by
    simpa [t, ε] using laurent_neg_one_t_pow_ne (a+b) n
  have hx : ∀ r : ZMod (a+b), x r = 0 :=
    zmod_recur_eq_zero hrec ht
  have hcop : Nat.Coprime a (a+b) := by
    exact Nat.coprime_self_add_right.2 hab_coprime
  have hwinv : ∀ r : ZMod (a+b), w r = w (r - (a : ZMod (a+b))) := by
    intro r
    have hxr := hx (r - (a : ZMod (a+b)))
    have h := sub_eq_zero.mp hxr
    have hidx : (r - (a : ZMod (a+b))) + (a : ZMod (a+b)) = r := by abel
    rw [hidx] at h
    exact h
  have hweq : ∀ i j : ZMod (a+b), w i = w j :=
    eq_of_forall_sub_natCast_zmod hcop hwinv
  have hvinv : ∀ r : ZMod (a+b), v r = v (r - (a : ZMod (a+b))) := by
    intro r
    have hdiff : w (r+1) - w r = 0 := sub_eq_zero.mpr (hweq (r+1) r)
    have htel := zmod_window_succ_sub a b ha v r
    have hzero : v r - v (r - (a : ZMod (a+b))) = 0 := by
      calc
        v r - v (r - (a : ZMod (a+b))) = w (r+1) - w r := by
          show v r - v (r - (a : ZMod (a+b))) =
            (∑ k ∈ Finset.Ico 1 (a+1), v ((r + 1) - (k : ZMod (a+b)))) -
              (∑ k ∈ Finset.Ico 1 (a+1), v (r - (k : ZMod (a+b))))
          exact htel.symm
        _ = 0 := hdiff
    exact sub_eq_zero.mp hzero
  exact eq_of_forall_sub_natCast_zmod hcop hvinv i j

end Rollout_p3019_laurent_circulant_kernel

namespace Rollout_p0489_caristi_kirk_bmetric_fixed_point

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

end Rollout_p0489_caristi_kirk_bmetric_fixed_point

namespace Rollout_p0367_weakhomotopyequivalence_of_iunion_open_res

/- accepted add_to_file helper 1 -/
lemma exists_cover_stage_of_isCompact
    {X : Type*} [TopologicalSpace X] {ι : Type*} [Nonempty ι]
    [Preorder ι] [IsDirectedOrder ι]
    {K : Set X} (hK : IsCompact K)
    (U : ι → Set X)
    (hU_open : ∀ n, IsOpen (U n))
    (hU_mono : Monotone U)
    (hU_cover : ⋃ n, U n = Set.univ) :
    ∃ n, K ⊆ U n := by
  refine hK.elim_directed_cover U hU_open ?_ hU_mono.directed_le
  rw [hU_cover]
  exact Set.subset_univ K

/-- Restrict a generalized loop to a subset containing its range. -/
def genLoopRestrict
    {N X : Type*} [TopologicalSpace N] [TopologicalSpace X]
    (s : Set X) {x : X} (hx : x ∈ s)
    (p : GenLoop N X x) (hp : Set.range p.1 ⊆ s) :
    GenLoop N s ⟨x, hx⟩ := by
  refine ⟨⟨fun y => ⟨p.1 y, hp ⟨y, rfl⟩⟩, ?_⟩, ?_⟩
  · exact p.1.continuous.subtype_mk (fun y => hp ⟨y, rfl⟩)
  · intro y hy
    apply Subtype.ext
    exact p.2 y hy

/-- Extend a generalized loop from a subset to the ambient space. -/
def genLoopExtend
    {N X : Type*} [TopologicalSpace N] [TopologicalSpace X]
    (s : Set X) {x : X} (hx : x ∈ s)
    (p : GenLoop N s ⟨x, hx⟩) :
    GenLoop N X x := by
  refine ⟨⟨fun y => p.1 y, continuous_subtype_val.comp p.1.continuous⟩, ?_⟩
  intro y hy
  exact congrArg Subtype.val (p.2 y hy)

/- verified submission -/
theorem weakHomotopyEquivalence_of_iUnion_open_restrictions
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y))
    (U : {n : ℕ // 1 ≤ n} → Set X)
    (hU_open : ∀ n, IsOpen (U n))
    (hU_mono : Monotone U)
    (hU_cover : ⋃ n, U n = Set.univ)
    (hf : ∀ n,
      let g : C(U n, Y) :=
        ⟨fun x => f x.1, f.continuous.comp continuous_subtype_val⟩
      Function.Bijective
          (Quotient.map g (by
            intro a b h
            exact h.map (fun p => p.map g.continuous)) :
            ZerothHomotopy (U n) → ZerothHomotopy Y) ∧
        ∀ (k : ℕ) (x : U n), Function.Bijective
          (Quotient.map
            (fun p : GenLoop (Fin (k + 1)) (U n) x =>
              (⟨g.comp p.1, by
                intro y hy
                rw [ContinuousMap.comp_apply, p.2 y hy]⟩ :
                GenLoop (Fin (k + 1)) Y (g x)))
            (by
              intro p q h
              exact h.map (fun H => H.compContinuousMap g)) :
            HomotopyGroup.Pi (k + 1) (U n) x →
              HomotopyGroup.Pi (k + 1) Y (g x))) :
    Function.Bijective
        (Quotient.map f (by
          intro a b h
          exact h.map (fun p => p.map f.continuous)) :
          ZerothHomotopy X → ZerothHomotopy Y) ∧
      ∀ (k : ℕ) (x : X), Function.Bijective
        (Quotient.map
          (fun p : GenLoop (Fin (k + 1)) X x =>
            (⟨f.comp p.1, by
              intro y hy
              rw [ContinuousMap.comp_apply, p.2 y hy]⟩ :
              GenLoop (Fin (k + 1)) Y (f x)))
          (by
            intro p q h
            exact h.map (fun H => H.compContinuousMap f)) :
          HomotopyGroup.Pi (k + 1) X x → HomotopyGroup.Pi (k + 1) Y (f x)) := by
  constructor
  · constructor
    · intro a b hab
      obtain ⟨x, rfl⟩ := Quotient.exists_rep a
      obtain ⟨y, rfl⟩ := Quotient.exists_rep b
      let K : Set X := {x, y}
      have hK : IsCompact K := by
        simp [K]
      obtain ⟨n, hnK⟩ :=
        exists_cover_stage_of_isCompact hK U hU_open hU_mono hU_cover
      have hx : x ∈ U n := hnK (by simp [K])
      have hy : y ∈ U n := hnK (by simp [K])
      let x' : U n := ⟨x, hx⟩
      let y' : U n := ⟨y, hy⟩
      let g : C(U n, Y) :=
        ⟨fun z => f z.1, f.continuous.comp continuous_subtype_val⟩
      have hlocal :
          (Quotient.map g (by
            intro a b h
            exact h.map (fun p => p.map g.continuous)) :
            ZerothHomotopy (U n) → ZerothHomotopy Y) ⟦x'⟧ =
          (Quotient.map g (by
            intro a b h
            exact h.map (fun p => p.map g.continuous)) :
            ZerothHomotopy (U n) → ZerothHomotopy Y) ⟦y'⟧ := by
        exact hab
      have hxy_local := (hf n).1.1 hlocal
      have hxy : Joined x y := by
        exact (Quotient.eq.mp hxy_local).map
          (fun p => p.map continuous_subtype_val)
      exact Quotient.eq.mpr hxy
    · intro b
      obtain ⟨y, rfl⟩ := Quotient.exists_rep b
      let n : {n : ℕ // 1 ≤ n} := ⟨1, le_rfl⟩
      obtain ⟨a, ha⟩ := (hf n).1.2 (⟦y⟧ : ZerothHomotopy Y)
      obtain ⟨x, rfl⟩ := Quotient.exists_rep a
      use (⟦x.1⟧ : ZerothHomotopy X)
      exact ha
  · intro k x
    constructor
    · intro a b hab
      obtain ⟨p, rfl⟩ := Quotient.exists_rep a
      obtain ⟨q, rfl⟩ := Quotient.exists_rep b
      let K : Set X := Set.range p.1 ∪ Set.range q.1 ∪ {x}
      have hpK : IsCompact (Set.range p.1) := isCompact_range p.1.continuous
      have hqK : IsCompact (Set.range q.1) := isCompact_range q.1.continuous
      have hK : IsCompact K := by
        unfold K
        exact (hpK.union hqK).union isCompact_singleton
      obtain ⟨n, hnK⟩ :=
        exists_cover_stage_of_isCompact hK U hU_open hU_mono hU_cover
      have hx : x ∈ U n := hnK (by simp [K])
      have hp : Set.range p.1 ⊆ U n := by
        intro z hz
        exact hnK (Set.mem_union_left {x}
          (Set.mem_union_left (Set.range q.1) hz))
      have hq : Set.range q.1 ⊆ U n := by
        intro z hz
        exact hnK (Set.mem_union_left {x}
          (Set.mem_union_right (Set.range p.1) hz))
      let x' : U n := ⟨x, hx⟩
      let pU := genLoopRestrict (U n) hx p hp
      let qU := genLoopRestrict (U n) hx q hq
      let g : C(U n, Y) :=
        ⟨fun z => f z.1, f.continuous.comp continuous_subtype_val⟩
      have hlocal :
          (Quotient.map
            (fun r : GenLoop (Fin (k + 1)) (U n) x' =>
              (⟨g.comp r.1, by
                intro y hy
                rw [ContinuousMap.comp_apply, r.2 y hy]⟩ :
                GenLoop (Fin (k + 1)) Y (g x')))
            (by
              intro r s h
              exact h.map (fun H => H.compContinuousMap g)) :
            HomotopyGroup.Pi (k + 1) (U n) x' →
              HomotopyGroup.Pi (k + 1) Y (g x')) ⟦pU⟧ =
          (Quotient.map
            (fun r : GenLoop (Fin (k + 1)) (U n) x' =>
              (⟨g.comp r.1, by
                intro y hy
                rw [ContinuousMap.comp_apply, r.2 y hy]⟩ :
                GenLoop (Fin (k + 1)) Y (g x')))
            (by
              intro r s h
              exact h.map (fun H => H.compContinuousMap g)) :
            HomotopyGroup.Pi (k + 1) (U n) x' →
              HomotopyGroup.Pi (k + 1) Y (g x')) ⟦qU⟧ := by
        exact hab
      have hpq_local := ((hf n).2 k x').1 hlocal
      have hpqX : GenLoop.Homotopic p q := by
        exact (Quotient.eq.mp hpq_local).map (fun H =>
          H.compContinuousMap
            (⟨Subtype.val, continuous_subtype_val⟩ : C(U n, X)))
      exact Quotient.eq.mpr hpqX
    · intro b
      obtain ⟨q, rfl⟩ := Quotient.exists_rep b
      let K : Set X := {x}
      have hK : IsCompact K := by
        simp [K]
      obtain ⟨n, hnK⟩ :=
        exists_cover_stage_of_isCompact hK U hU_open hU_mono hU_cover
      have hx : x ∈ U n := hnK (by simp [K])
      let x' : U n := ⟨x, hx⟩
      obtain ⟨a, ha⟩ :=
        ((hf n).2 k x').2
          (⟦q⟧ : HomotopyGroup.Pi (k + 1) Y (f x))
      obtain ⟨p, rfl⟩ := Quotient.exists_rep a
      use (⟦genLoopExtend (U n) hx p⟧ :
        HomotopyGroup.Pi (k + 1) X x)
      exact ha

end Rollout_p0367_weakhomotopyequivalence_of_iunion_open_res
