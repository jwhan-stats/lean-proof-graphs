theorem proposition_4_2
    (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m)
    (γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p])
    (hγGSp : ∃ μ : ℤ_[p]ˣ,
      (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).transpose *
          Matrix.J (Fin 2) ℤ_[p] *
          (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) =
        (μ : ℤ_[p]) • Matrix.J (Fin 2) ℤ_[p])
    (hγe₁e₁ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inl 0) (Sum.inl 0) = 1)
    (hγe₁e₂ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inl 1) (Sum.inl 0) = 1)
    (hγe₁f₁ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inr 0) (Sum.inl 0) = 0)
    (hγe₁f₂ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inr 1) (Sum.inl 0) = 0) :
    {h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ_[p] |
      (∃ A B : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p],
        Matrix.det (A : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
            Matrix.det (B : Matrix (Fin 2) (Fin 2) ℚ_[p]) ∧
        h = Matrix.fromBlocks
          (Matrix.diagonal ![A 0 0, B 0 0])
          (Matrix.diagonal ![A 0 1, B 0 1])
          (Matrix.diagonal ![A 1 0, B 1 0])
          (Matrix.diagonal ![A 1 1, B 1 1])) ∧
      ∃ k : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p],
        (∃ μ : ℤ_[p]ˣ,
          (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).transpose *
              Matrix.J (Fin 2) ℤ_[p] *
              (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) =
            (μ : ℤ_[p]) • Matrix.J (Fin 2) ℤ_[p]) ∧
        (∀ i : Fin 2 ⊕ Fin 2, i ≠ Sum.inl 0 →
          (p : ℤ_[p]) ^ m ∣
            (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) i (Sum.inl 0)) ∧
        h = ((↑(γ * k * γ⁻¹) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
            (algebraMap ℤ_[p] ℚ_[p]))} =
    {h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ_[p] |
      ∃ A B : Matrix.GeneralLinearGroup (Fin 2) ℤ_[p],
        Matrix.det (A : Matrix (Fin 2) (Fin 2) ℤ_[p]) =
            Matrix.det (B : Matrix (Fin 2) (Fin 2) ℤ_[p]) ∧
        (p : ℤ_[p]) ^ m ∣ (A : Matrix (Fin 2) (Fin 2) ℤ_[p]) 1 0 ∧
        (p : ℤ_[p]) ^ m ∣ (B : Matrix (Fin 2) (Fin 2) ℤ_[p]) 1 0 ∧
        (p : ℤ_[p]) ^ m ∣
          ((A : Matrix (Fin 2) (Fin 2) ℤ_[p]) 0 0 -
            (B : Matrix (Fin 2) (Fin 2) ℤ_[p]) 0 0) ∧
        h = (Matrix.fromBlocks
          (Matrix.diagonal ![A 0 0, B 0 0])
          (Matrix.diagonal ![A 0 1, B 0 1])
          (Matrix.diagonal ![A 1 0, B 1 0])
          (Matrix.diagonal ![A 1 1, B 1 1])).map
            (algebraMap ℤ_[p] ℚ_[p])} := by sorry
