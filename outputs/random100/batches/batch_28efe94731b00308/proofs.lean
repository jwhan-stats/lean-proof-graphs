import Mathlib

/- Generated only to amortize Mathlib loading during graph export. -/

namespace Rollout_p2332_matrix_kronecker_injective_iff_linearindep

/- verified submission -/
theorem matrix_kronecker_injective_iff_linearIndependent
    (g d e : ℕ) (hg : 0 < g) (hd : 0 < d) (he : 0 < e)
    (A : Fin g → Matrix (Fin d) (Fin e) ℂ) :
    let c₁ : Prop := ∀ (n : ℕ), 0 < n → ∀ X : Fin g → Matrix (Fin n) (Fin n) ℂ,
      (∑ j, Matrix.kronecker (A j) (X j)) = 0 → ∀ j, X j = 0
    let c₂ : Prop := ∀ z : Fin g → ℂ,
      (∑ j, z j • A j) = 0 → ∀ j, z j = 0
    let c₃ : Prop := LinearIndependent ℂ A
    (c₁ ↔ c₂) ∧ (c₂ ↔ c₃) := by
  constructor
  · constructor
    · intro h₁ z hz
      let X : Fin g → Matrix (Fin 1) (Fin 1) ℂ :=
        fun j => Matrix.of fun _ _ => z j
      have hsum : (∑ j, Matrix.kronecker (A j) (X j)) = 0 := by
        ext ⟨i, a⟩ ⟨k, b⟩
        have hz' := congrFun (congrFun hz i) k
        simp [Matrix.sum_apply, Matrix.smul_apply, X] at hz' ⊢
        simpa [mul_comm] using hz'
      have hX := h₁ 1 zero_lt_one X hsum
      intro j
      have hj := congrFun (congrFun (hX j) 0) 0
      simpa [X] using hj
    · intro h₂ n hn X hX j
      ext r s
      let z : Fin g → ℂ := fun j => X j r s
      have hzsum : (∑ j, z j • A j) = 0 := by
        ext i k
        have hX' := congrFun (congrFun hX (i, r)) (k, s)
        simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.kronecker, z] at hX' ⊢
        simpa [mul_comm] using hX'
      have hz := h₂ z hzsum j
      simpa [z] using hz
  · constructor
    · intro h₂
      rw [linearIndependent_iff_injective_fintypeLinearCombination]
      intro x y hxy
      have hdiff : (∑ j, (x - y) j • A j) = 0 := by
        have hmap : Fintype.linearCombination ℂ A (x - y) = 0 := by
          rw [map_sub, hxy, sub_self]
        simpa [Fintype.linearCombination_apply] using hmap
      have h := h₂ (x - y) hdiff
      ext j
      have hj := h j
      simpa using sub_eq_zero.mp hj
    · intro h₃ z hz
      rw [linearIndependent_iff_injective_fintypeLinearCombination] at h₃
      have hzlin : Fintype.linearCombination ℂ A z = Fintype.linearCombination ℂ A 0 := by
        rw [Fintype.linearCombination_apply]
        simpa using hz
      have hz0 := h₃ hzlin
      intro j
      exact congrFun hz0 j

end Rollout_p2332_matrix_kronecker_injective_iff_linearindep
