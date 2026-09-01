theorem seminormal_reesQuotient_iff_radical
    {A C B : Type*}
    [CommMonoidWithZero A] [CommMonoidWithZero C] [IsCancelMulZero C]
    [CommMonoidWithZero B]
    (J : SemigroupIdeal C)
    (hJ_zero : (0 : C) ∈ J)
    (p : C →*₀ A)
    (hp_surjective : Function.Surjective p)
    (hp_fiber : ∀ c d : C, p c = p d ↔ c = d ∨ (c ∈ J ∧ d ∈ J))
    (hA :
      (∀ a b : A, a ^ 2 = b ^ 2 → a ^ 3 = b ^ 3 → a = b) ∧
      (∀ x y : A, x ^ 3 = y ^ 2 → ∃ z : A, x = z ^ 2 ∧ y = z ^ 3))
    (I : SemigroupIdeal A)
    (hI_zero : (0 : A) ∈ I)
    (q : A →*₀ B)
    (hq_surjective : Function.Surjective q)
    (hq_fiber : ∀ a b : A, q a = q b ↔ a = b ∨ (a ∈ I ∧ b ∈ I)) :
    ((∀ a b : B, a ^ 2 = b ^ 2 → a ^ 3 = b ^ 3 → a = b) ∧
        (∀ x y : B, x ^ 3 = y ^ 2 → ∃ z : B, x = z ^ 2 ∧ y = z ^ 3)) ↔
      ∀ a : A, (∃ n : ℕ, 1 ≤ n ∧ a ^ n ∈ I) → a ∈ I := by sorry
