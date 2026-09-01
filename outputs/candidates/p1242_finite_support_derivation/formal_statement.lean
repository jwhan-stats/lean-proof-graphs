theorem finite_support_derivation
    {W : Type*} (D : Set W → Set W)
    (hD : ∀ (S : Set W) (x : W),
      x ∈ D S ↔ ∃ F : Set W, F.Finite ∧ F ⊆ S ∧ x ∈ D F)
    (A : Set W) (n : ℕ) (P : W)
    (hn : 1 ≤ n) (hP : P ∈ (D^[n]) A) :
    ∃ S : ℕ → Set W,
      (∀ k < n, (S k).Finite) ∧
      (∀ k < n, S k ⊆ (D^[k]) A) ∧
      P ∈ D (S (n - 1)) ∧
      ∀ k, k + 1 < n → S (k + 1) ⊆ D (S k) := by sorry
