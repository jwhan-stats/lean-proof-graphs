theorem formalPowerSeries_automorphism_exact_sequence (N : ℕ) (hN : 2 ≤ N) :
  let A := PowerSeries ℂ
  let _ : TopologicalSpace A :=
    PowerSeries.WithPiTopology.instTopologicalSpace ℂ
  let e : A →ₐ[ℂ] A :=
    PowerSeries.expand N (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hN))
  let G := A ≃ₐ[ℂ] A
  let S : Set A := Set.range e
  ∃ (Aut : Subgroup G) (AutN : Subgroup G),
    (∀ ρ : G, ρ ∈ Aut ↔
      Continuous (ρ : A → A) ∧ Continuous (ρ.symm : A → A)) ∧
    (∀ ρ : G, ρ ∈ AutN ↔
      Continuous (ρ : A → A) ∧ Continuous (ρ.symm : A → A) ∧ ρ '' S = S) ∧
    ∃ (ι : rootsOfUnity N ℂ →* AutN) (μ : AutN →* Aut),
      (∀ (ρ : AutN) (f : A), e ((μ ρ : G) f) = (ρ : G) (e f)) ∧
      (∀ ρ : AutN,
        e ((μ ρ : G) PowerSeries.X) = ((ρ : G) PowerSeries.X) ^ N) ∧
      (∀ ε : rootsOfUnity N ℂ,
        (ι ε : G) PowerSeries.X =
          algebraMap ℂ A (((ε : ℂˣ) : ℂ)) * PowerSeries.X) ∧
      Function.Injective ι ∧
      Function.Surjective μ ∧
      ι.range = μ.ker ∧
      ι.range ≤ Subgroup.center AutN := by sorry
