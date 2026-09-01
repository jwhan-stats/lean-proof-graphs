theorem looptree_height_bound
    (N : ℕ)
    (τ : Finset (List ℕ))
    (k : List ℕ → ℕ)
    (hroot : [] ∈ τ)
    (hprefix : ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    (u : Fin N ≃ {v : List ℕ // v ∈ τ})
    (hlex : ∀ a b : Fin N, a < b ↔
      List.Lex (fun x y : ℕ => x < y) (u a).1 (u b).1)
    (W : Fin (N + 1) → ℤ)
    (hWzero : W 0 = 0)
    (hWstep : ∀ r : Fin N,
      W r.succ = W r.castSucc + (k (u r).1 : ℤ) - 1) :
    let H : Fin N → ℕ := fun r => (u r).1.length
    let Loop : SimpleGraph {v : List ℕ // v ∈ τ} :=
      SimpleGraph.fromRel fun x y =>
        (∃ (p : List ℕ) (m : ℕ), p ∈ τ ∧ 1 ≤ m ∧ m < k p ∧
          x.1 = p ++ [m] ∧ y.1 = p ++ [m + 1]) ∨
        (0 < k x.1 ∧ (y.1 = x.1 ++ [1] ∨ y.1 = x.1 ++ [k x.1]))
    let Hb : Fin N → ℕ := fun r => Loop.dist ⟨[], hroot⟩ (u r)
    ∀ i j : Fin N, i < j → (u i).1 <+: (u j).1 →
      |(Hb i : ℤ) - (Hb j : ℤ)| ≤
        W j.castSucc - W i.castSucc + (H j : ℤ) - (H i : ℤ) := by sorry
