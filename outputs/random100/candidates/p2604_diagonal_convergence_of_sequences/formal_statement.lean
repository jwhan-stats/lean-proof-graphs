theorem diagonal_convergence_of_sequences
    {E : Type*} [MetricSpace E]
    (a : ℕ → ℕ → E) (aInf : ℕ → E) (aInfInf : E)
    (ha : ∀ m : ℕ, Filter.Tendsto (a m) Filter.atTop (nhds (aInf m)))
    (hInf : Filter.Tendsto aInf Filter.atTop (nhds aInfInf)) :
    ∃ b : ℕ → ℕ,
      Monotone b ∧
      Filter.Tendsto b Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun n : ℕ => a (b n) n) Filter.atTop (nhds aInfInf) := by sorry
