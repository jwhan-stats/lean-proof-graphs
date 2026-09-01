theorem diagonal_homogeneous_polynomial_norm_bounds
    {𝕂 E : Type*} [RCLike 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
    [CompleteSpace E] {k : ℕ} (hk : 1 ≤ k) (φ : Fin k → E →L[𝕂] 𝕂)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (p : ENNReal) (hp : 1 < p)
    (hφ : ∀ α : Fin k → 𝕂,
      A * (if p = ⊤ then ‖α‖ else
        Real.rpow (∑ j : Fin k, Real.rpow ‖α j‖ p.toReal) (1 / p.toReal)) ≤
          ‖∑ j : Fin k, α j • φ j‖ ∧
      ‖∑ j : Fin k, α j • φ j‖ ≤
        B * (if p = ⊤ then ‖α‖ else
          Real.rpow (∑ j : Fin k, Real.rpow ‖α j‖ p.toReal) (1 / p.toReal)))
    (n : ℕ) (hn : 1 ≤ n) (hnq : ENNReal.conjExponent p ≤ n) :
    ∀ α : Fin k → 𝕂,
      A ^ n * ‖α‖ ≤
          sSup (Set.range (fun x : {x : E // ‖x‖ ≤ 1} =>
            ‖∑ j : Fin k, α j * (φ j x) ^ n‖)) ∧
      sSup (Set.range (fun x : {x : E // ‖x‖ ≤ 1} =>
            ‖∑ j : Fin k, α j * (φ j x) ^ n‖)) ≤
        B ^ n * ‖α‖ := by sorry
