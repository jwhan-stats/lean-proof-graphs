import Mathlib

/- accepted add_to_file helper 1 -/
lemma row_update_prod_invariant
    (N : ℕ)
    (C : Matrix (Fin N) (Fin N) ℝ)
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (r : ℝ)
    (hr : IsGreatest (Set.range (fun i : Fin N => ∑ j : Fin N, C i j)) r)
    (hr_lt_one : r < 1)
    (l : List (Fin N)) :
    (∀ x : Fin N,
      (∑ j : Fin N,
        (l.map (fun a : Fin N =>
          Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) a (C a))).prod x j) ≤ 1) ∧
    (∀ i : Fin N, i ∈ l →
      (∑ j : Fin N,
        (l.map (fun a : Fin N =>
          Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) a (C a))).prod i j) ≤ r) := by
  classical
  induction l with
  | nil =>
      constructor
      · intro x
        simp [Matrix.one_apply]
      · intro i hi
        simp at hi
  | cons a t ih =>
      obtain ⟨ih_one, ih_r⟩ := ih
      have hCa : (∑ j : Fin N, C a j) ≤ r := by
        exact hr.2 (by exact ⟨a, rfl⟩)
      have hrow_a :
          (∑ j : Fin N,
            ((Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) a (C a)) *
              (t.map (fun b : Fin N =>
                Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) b (C b))).prod) a j) ≤ r := by
        calc
          (∑ j : Fin N,
            ((Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) a (C a)) *
              (t.map (fun b : Fin N =>
                Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) b (C b))).prod) a j)
              = ∑ k : Fin N, C a k *
                (∑ j : Fin N,
                  (t.map (fun b : Fin N =>
                    Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) b (C b))).prod k j) := by
                rw [Matrix.updateRow_mul, Matrix.one_mul]
                simp [Matrix.vecMul, dotProduct, Finset.mul_sum]
                rw [Finset.sum_comm]
          _ ≤ ∑ k : Fin N, C a k * 1 := by
                exact Finset.sum_le_sum (fun k _ =>
                  mul_le_mul_of_nonneg_left (ih_one k) (hC_nonneg a k))
          _ = ∑ k : Fin N, C a k := by simp
          _ ≤ r := hCa
      constructor
      · intro x
        simp only [List.map_cons, List.prod_cons]
        by_cases hxa : x = a
        · subst x
          exact le_trans hrow_a (le_of_lt hr_lt_one)
        · have hrow_eq :
              (∑ j : Fin N,
                ((Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) a (C a)) *
                  (t.map (fun b : Fin N =>
                    Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) b (C b))).prod) x j)
                = ∑ j : Fin N,
                  (t.map (fun b : Fin N =>
                    Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) b (C b))).prod x j := by
            rw [Matrix.updateRow_mul, Matrix.one_mul]
            simp [Matrix.updateRow_ne hxa]
          rw [hrow_eq]
          exact ih_one x
      · intro i hi
        simp only [List.map_cons, List.prod_cons]
        by_cases hia : i = a
        · subst i
          exact hrow_a
        · have hit : i ∈ t := by
            simp [hia] at hi
            exact hi
          have hrow_eq :
              (∑ j : Fin N,
                ((Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) a (C a)) *
                  (t.map (fun b : Fin N =>
                    Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) b (C b))).prod) i j)
                = ∑ j : Fin N,
                  (t.map (fun b : Fin N =>
                    Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) b (C b))).prod i j := by
            rw [Matrix.updateRow_mul, Matrix.one_mul]
            simp [Matrix.updateRow_ne hia]
          rw [hrow_eq]
          exact ih_r i hit

/- verified submission -/
theorem substochastic_row_update_product
    (N : ℕ) (hN : 1 ≤ N)
    (C : Matrix (Fin N) (Fin N) ℝ)
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hC_diag : ∀ i, C i i = 0)
    (r : ℝ)
    (hr : IsGreatest (Set.range (fun i : Fin N => ∑ j : Fin N, C i j)) r)
    (hr_lt_one : r < 1)
    (Q : Matrix (Fin N) (Fin N) ℝ)
    (hQ : Q = (List.ofFn (fun i : Fin N =>
      Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) i (C i))).reverse.prod) :
    ∀ i : Fin N, (∑ j : Fin N, Q i j) ≤ r := by
  classical
  intro i
  let idx : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hinvariant := row_update_prod_invariant N C hC_nonneg r hr hr_lt_one idx.reverse
  have hi_idx : i ∈ idx := by
    dsimp [idx]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  have hi : i ∈ idx.reverse := by
    exact List.mem_reverse.mpr hi_idx
  have hbound := hinvariant.2 i hi
  rw [hQ]
  simpa [idx, List.map_reverse] using hbound
