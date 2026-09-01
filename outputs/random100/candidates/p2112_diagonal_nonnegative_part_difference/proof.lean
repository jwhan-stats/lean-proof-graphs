import Mathlib

/- verified submission -/
lemma positive_part_secant_aux (x y : ℝ) :
    ∃ ω : ℝ, 0 ≤ ω ∧ ω ≤ 1 ∧
      (if 0 ≤ x then (1 : ℝ) else 0) * x -
        (if 0 ≤ y then (1 : ℝ) else 0) * y = ω * (x - y) := by
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · refine ⟨1, by norm_num, by norm_num, ?_⟩
      simp [hx, hy]
    · have hy_lt : y < 0 := lt_of_not_ge hy
      have hden : 0 < x - y := sub_pos.mpr (lt_of_lt_of_le hy_lt hx)
      refine ⟨x / (x - y), ?_, ?_, ?_⟩
      · exact div_nonneg hx (le_of_lt hden)
      · rw [div_le_one hden]
        nlinarith
      · simp [hx, hy]
        exact (div_mul_cancel₀ x (ne_of_gt hden)).symm
  · have hx_lt : x < 0 := lt_of_not_ge hx
    by_cases hy : 0 ≤ y
    · have hden : 0 < y - x := sub_pos.mpr (lt_of_lt_of_le hx_lt hy)
      refine ⟨y / (y - x), ?_, ?_, ?_⟩
      · exact div_nonneg hy (le_of_lt hden)
      · rw [div_le_one hden]
        nlinarith
      · simp [hx, hy]
        field_simp [ne_of_gt hden]
        ring
    · refine ⟨0, by norm_num, by norm_num, ?_⟩
      simp [hx, hy]

theorem diagonal_nonnegative_part_difference
    (n : ℕ) (hn : 0 < n) (x y : Fin n → ℝ) :
    let P : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ :=
      fun z => Matrix.diagonal (fun i => if 0 ≤ z i then 1 else 0)
    ∃ ω : Fin n → ℝ,
      (∀ i, 0 ≤ ω i ∧ ω i ≤ 1) ∧
        Matrix.mulVec (P x) x - Matrix.mulVec (P y) y =
          Matrix.mulVec (Matrix.diagonal ω) (x - y) := by
  let P : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ :=
    fun z => Matrix.diagonal (fun i => if 0 ≤ z i then 1 else 0)
  let ω : Fin n → ℝ :=
    fun i => Classical.choose (positive_part_secant_aux (x i) (y i))
  have hω : ∀ i : Fin n,
      0 ≤ ω i ∧ ω i ≤ 1 ∧
        (if 0 ≤ x i then (1 : ℝ) else 0) * x i -
          (if 0 ≤ y i then (1 : ℝ) else 0) * y i = ω i * (x i - y i) := by
    intro i
    dsimp [ω]
    exact Classical.choose_spec (positive_part_secant_aux (x i) (y i))
  refine ⟨ω, ?_, ?_⟩
  · intro i
    exact ⟨(hω i).1, (hω i).2.1⟩
  · funext i
    exact (by
      simpa [P, Matrix.mulVec_diagonal, Pi.sub_apply] using (hω i).2.2 :
        (Matrix.mulVec (P x) x - Matrix.mulVec (P y) y) i =
          (Matrix.mulVec (Matrix.diagonal ω) (x - y)) i)
