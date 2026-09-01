import Mathlib

/- accepted add_to_file helper 1 -/
import Mathlib

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
