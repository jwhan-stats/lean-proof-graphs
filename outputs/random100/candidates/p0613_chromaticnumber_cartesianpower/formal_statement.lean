theorem chromaticNumber_cartesianPower {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) :
    ∀ k : ℕ, 1 ≤ k →
      (SimpleGraph.fromRel (fun x y : Fin k → Fin n =>
        ∃ i : Fin k, G.Adj (x i) (y i) ∧
          ∀ j : Fin k, j ≠ i → x j = y j)).chromaticNumber =
        G.chromaticNumber := by sorry
