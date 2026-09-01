theorem unique_diagonal_perfect_matching_iff_no_alternating_cycle
    {V : Type*} [Fintype V] {n : ℕ} (hn : 1 ≤ n)
    (G : SimpleGraph V) (x y : Fin n → V)
    (hxy : Function.Bijective (Sum.elim x y : Fin n ⊕ Fin n → V))
    (h_no_isolated : ∀ v : V, ∃ w : V, G.Adj v w)
    (hX : Minimal G.IsVertexCover (Set.range x))
    (hY : Maximal G.IsIndepSet (Set.range y))
    (hdiag : ∀ i : Fin n, G.Adj (x i) (y i))
    (hunmixed : ∀ C : Set V, Minimal G.IsVertexCover C → C.ncard = n) :
    ((∃ M : G.Subgraph,
        M.IsPerfectMatching ∧
          (∀ u v : V, M.Adj u v ↔
            ∃ i : Fin n,
              (u = x i ∧ v = y i) ∨ (u = y i ∧ v = x i)) ∧
          ∀ M' : G.Subgraph, M'.IsPerfectMatching → M' = M) ↔
      ∀ i j : Fin n, i < j →
        ¬(G.Adj (x i) (y i) ∧ G.Adj (y i) (x j) ∧
          G.Adj (x j) (y j) ∧ G.Adj (y j) (x i))) ∧
    ((∀ i j : Fin n, i < j →
        ¬(G.Adj (x i) (y i) ∧ G.Adj (y i) (x j) ∧
          G.Adj (x j) (y j) ∧ G.Adj (y j) (x i))) ↔
      ∀ (r : ℕ) (i : Fin (r + 2) → Fin n), Function.Injective i →
        ¬(∀ s : Fin (r + 2),
          G.Adj (x (i s)) (y (i s)) ∧
            G.Adj (y (i s)) (x (i (s + 1))))) := by sorry
