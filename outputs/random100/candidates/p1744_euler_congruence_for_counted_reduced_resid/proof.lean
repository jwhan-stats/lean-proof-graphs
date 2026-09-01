import Mathlib

/- verified submission -/
theorem euler_congruence_for_counted_reduced_residues
    (N x n : ℕ) (hN : 0 < N) (hx : 0 < x)
    (hcoprime : Nat.Coprime x N)
    (hn : n = ((Finset.Ico 1 N).filter fun a => Nat.Coprime a N).card) :
    Nat.ModEq N (x ^ n) 1 := by
  by_cases hN1 : N = 1
  · subst N
    exact Nat.modEq_one
  · have hNgt : 1 < N := by omega
    have hsets :
        ((Finset.Ico 1 N).filter fun a => Nat.Coprime a N) =
          {a ∈ Finset.Ico 1 (1 + N) | N.Coprime a} := by
      ext a
      constructor
      · intro ha
        simp only [Finset.mem_filter, Finset.mem_Ico] at ha ⊢
        exact ⟨⟨ha.1.1, by omega⟩, ha.2.symm⟩
      · intro ha
        simp only [Finset.mem_filter, Finset.mem_Ico] at ha ⊢
        have ha_ne_N : a ≠ N := by
          intro h
          subst a
          have : N = 1 := (Nat.coprime_self N).mp ha.2
          omega
        exact ⟨⟨ha.1.1, by omega⟩, ha.2.symm⟩
    have hcard :
        ((Finset.Ico 1 N).filter fun a => Nat.Coprime a N).card = N.totient := by
      rw [hsets]
      exact Nat.filter_coprime_Ico_eq_totient N 1
    rw [hn, hcard]
    exact Nat.ModEq.pow_totient hcoprime
