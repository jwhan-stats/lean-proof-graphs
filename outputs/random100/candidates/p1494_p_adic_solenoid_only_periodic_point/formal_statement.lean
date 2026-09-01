theorem p_adic_solenoid_only_periodic_point
    (P : ℕ → ℕ)
    (hP_prime : ∀ n, Nat.Prime (P n))
    (hP_recurrent : ∀ q, Nat.Prime q → ∀ N, ∃ n, N ≤ n ∧ P n = q)
    (k : ℕ) (hk : 2 ≤ k) :
    ∀ z : ℕ → ℂ,
      ((∀ n, ‖z n‖ = 1) ∧
        ∀ n, z n = z (n + 1) ^ P n) →
      ((∃ m, 0 < m ∧
          Function.IsPeriodicPt (fun w : ℕ → ℂ => fun n => w n ^ k) m z) ↔
        z = fun _ => 1) := by sorry
