theorem independentDominationNumber_eq_dominationNumber
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hhigh : G.IsIndepSet {v : V | 2 < (G.neighborSet v).ncard}) :
    sInf {n : ℕ | ∃ D : Finset V,
      D.card = n ∧ G.IsIndepSet (↑D : Set V) ∧
        ∀ v : V, v ∉ D → ∃ w : V, w ∈ D ∧ G.Adj v w} =
    sInf {n : ℕ | ∃ D : Finset V,
      D.card = n ∧ ∀ v : V, v ∉ D → ∃ w : V, w ∈ D ∧ G.Adj v w} := by sorry
