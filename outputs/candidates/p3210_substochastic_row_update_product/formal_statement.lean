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
    ∀ i : Fin N, (∑ j : Fin N, Q i j) ≤ r := by sorry
