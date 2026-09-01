theorem catlin_vertical_curve_is_geodesic
    (m : ℕ) (p : MvPolynomial (Fin 2) ℂ) :
    let evalAt : ℂ → MvPolynomial (Fin 2) ℂ → ℂ :=
      fun z q => MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z else star z) q
    let D : ℕ → ℕ → ℂ → ℂ := fun j k z =>
      evalAt z ((MvPolynomial.pderiv (1 : Fin 2))^[k]
        ((MvPolynomial.pderiv (0 : Fin 2))^[j] p))
    let P : ℂ → ℝ := fun z => (evalAt z p).re
    let Pz : ℂ → ℂ := fun z => D 1 0 z
    let A : ℕ → ℂ → ℝ := fun l z =>
      sSup {u : ℝ | ∃ j k : ℕ, 0 < j ∧ 0 < k ∧ j + k = l ∧ u = ‖D j k z‖}
    let r : ℂ × ℂ → ℝ := fun q => q.2.re + P q.1
    let Ω : Set (ℂ × ℂ) := {q | r q < 0}
    let M : (ℂ × ℂ) → (ℂ × ℂ) → ℝ := fun q v =>
      ‖v.2 + 2 * v.1 * Pz q.1‖ / |r q| +
        ‖v.1‖ * ∑ l ∈ Finset.Icc 2 m,
          Real.rpow (A l q.1 / |r q|) (1 / (l : ℝ))
    let PiecewiseC1 : (ℝ → ℂ × ℂ) → Prop := fun γ =>
      ∃ n : ℕ, ∃ u : Fin (n + 1) → ℝ,
        u 0 = 0 ∧ u ⟨n, Nat.lt_add_one n⟩ = 1 ∧ StrictMono u ∧
          ∀ i : Fin n,
            ContDiffOn ℝ 1 γ (Set.Icc (u i.castSucc) (u i.succ))
    let d : (ℂ × ℂ) → (ℂ × ℂ) → ℝ := fun q₁ q₂ =>
      sInf {L : ℝ | ∃ γ : ℝ → ℂ × ℂ,
        PiecewiseC1 γ ∧
        γ 0 = q₁ ∧ γ 1 = q₂ ∧
        (∀ u ∈ Set.Icc (0 : ℝ) 1, γ u ∈ Ω) ∧
        L = ∫ u in Set.Icc (0 : ℝ) 1, M (γ u) (deriv γ u)}
    2 ≤ m →
    p.totalDegree = m →
    (∀ z : ℂ, (evalAt z p).im = 0) →
    P 0 = 0 →
    (∀ z : ℂ, 0 ≤ (D 1 1 z).re) →
    (∀ j : ℕ, 0 < j → p.coeff (Finsupp.single (0 : Fin 2) j) = 0) →
    (∀ k : ℕ, 0 < k → p.coeff (Finsupp.single (1 : Fin 2) k) = 0) →
    ∀ (z₀ w₀ : ℂ) (a : ℝ),
      0 < a →
      (z₀, w₀) ∈ frontier Ω →
      let σ : ℝ → ℂ × ℂ := fun t =>
        (z₀, w₀ - ((a * Real.exp (-t) : ℝ) : ℂ))
      (∀ t : ℝ, σ t ∈ Ω) ∧
        ∀ s t : ℝ, d (σ s) (σ t) = |s - t| := by sorry
