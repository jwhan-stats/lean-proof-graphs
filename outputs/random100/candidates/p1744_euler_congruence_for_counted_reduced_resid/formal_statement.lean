theorem euler_congruence_for_counted_reduced_residues
    (N x n : ℕ) (hN : 0 < N) (hx : 0 < x)
    (hcoprime : Nat.Coprime x N)
    (hn : n = ((Finset.Ico 1 N).filter fun a => Nat.Coprime a N).card) :
    Nat.ModEq N (x ^ n) 1 := by sorry
