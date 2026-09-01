import Mathlib

/- verified submission -/
theorem basel_series : HasSum (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) (Real.pi ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (g := Real.pi ^ 2 / 6) 1).mpr (by
    simpa using hasSum_zeta_two)
  simpa using h
