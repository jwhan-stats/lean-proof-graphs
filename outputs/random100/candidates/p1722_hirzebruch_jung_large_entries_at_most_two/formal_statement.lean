theorem hirzebruch_jung_large_entries_at_most_two
    (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℤ)
    (ha : ∀ i, 2 ≤ a i)
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q)
    (hfrac : (List.ofFn fun i => (a i : ℚ)).foldr
      (fun x r => x - 1 / r) 0 = (p : ℚ) / (q : ℚ))
    (hS : (2 * (p : ℚ)) / 9 <
      ∑ i ∈ Finset.univ.filter (fun i => 3 < a i), ((a i - 3 : ℤ) : ℚ)) :
    (Finset.univ.filter (fun i => 3 < a i)).card ≤ 2 := by sorry
