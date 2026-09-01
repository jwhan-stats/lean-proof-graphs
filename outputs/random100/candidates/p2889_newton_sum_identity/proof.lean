import Mathlib

/- verified submission -/
import Mathlib

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
