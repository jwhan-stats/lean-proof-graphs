theorem entropy_number_approximation
    (𝕜 : Type*) [RCLike 𝕜]
    (X Y : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (Γ : Type*) [Fintype Γ] [Nonempty Γ]
    (V : X →ₗ[𝕜] Y) (Vγ : Γ → X →ₗ[𝕜] Y)
    (n : ℕ) (hn : 0 < n) :
    let e : ℕ → (X →ₗ[𝕜] Y) → ENNReal := fun k T ↦
      ⨅ (ε : NNReal) (_ : 0 < ε)
        (_ : Metric.externalCoveringNumber ε (T '' Metric.closedBall (0 : X) 1) ≤
          2 ^ (k - 1)),
        (ε : ENNReal)
    e (n + Nat.log 2 (Fintype.card Γ) + 1) V ≤
      (⨆ γ : Γ, e n (Vγ γ)) +
        (⨆ (x : X) (_ : ‖x‖ ≤ 1),
          ⨅ γ : Γ, ENNReal.ofReal ‖V x - Vγ γ x‖) := by sorry
