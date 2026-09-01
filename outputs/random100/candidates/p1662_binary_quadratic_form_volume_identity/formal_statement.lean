theorem binary_quadratic_form_volume_identity
    (D a b c : ℤ) (lam mu : ℝ)
    (hDpos : 0 < D)
    (hDnsq : ¬ IsSquare D)
    (hDmod : D % 4 = 0 ∨ D % 4 = 1)
    (hdisc : b ^ 2 - 4 * a * c = D)
    (ha : 0 < a)
    (hc : c < 0)
    (hsum : a + b + c < 0)
    (hlamroot : (a : ℝ) * lam ^ 2 + (b : ℝ) * lam + (c : ℝ) = 0)
    (hlampos : 0 < lam)
    (hlamunique : ∀ x : ℝ,
      0 < x → (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0 → x = lam)
    (hmuroot :
      (a : ℝ) * mu ^ 2 + ((-2 * a - b : ℤ) : ℝ) * mu +
        ((a + b + c : ℤ) : ℝ) = 0)
    (hmupos : 0 < mu)
    (hmuunique : ∀ x : ℝ,
      0 < x →
        (a : ℝ) * x ^ 2 + ((-2 * a - b : ℤ) : ℝ) * x +
          ((a + b + c : ℤ) : ℝ) = 0 →
        x = mu) :
    (a : ℝ) * lam * (lam - 1) *
          (1 + 1 / lam ^ 2 + 1 / (lam - 1) ^ 2) +
        (a : ℝ) * mu * (mu - 1) *
          (1 + 1 / mu ^ 2 + 1 / (mu - 1) ^ 2) =
      4 * (a : ℝ) + (b : ℝ) + (b : ℝ) ^ 2 / (a : ℝ) +
        (a : ℝ) * (b : ℝ) / (c : ℝ) - 2 * (c : ℝ) -
        (a : ℝ) * (2 * (a : ℝ) + (b : ℝ)) /
          ((a : ℝ) + (b : ℝ) + (c : ℝ)) := by sorry
