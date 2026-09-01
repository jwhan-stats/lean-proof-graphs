theorem pendant_branch_laplacian_eigenvector_decay
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : 1 ≤ k)
    (i : Fin k → V)
    (hi : Function.Injective i)
    (hbranch : ∀ a b : Fin k,
      G.Adj (i a) (i b) ↔ a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (hexternal : ∃ x : V,
      x ∉ Set.range i ∧
      G.Adj (i ⟨0, hk⟩) x ∧
      ∀ (a : Fin k) (v : V), v ∉ Set.range i → G.Adj (i a) v →
        a = ⟨0, hk⟩ ∧ v = x)
    (lam : ℝ) (hlam : 4 < lam)
    (φ : V → ℝ) (hφ : φ ≠ 0)
    (heigen : (G.lapMatrix ℝ).mulVec φ = lam • φ) :
    let γ : ℝ := 2 / (lam - 2)
    0 < γ ∧ γ < 1 ∧
      (∀ (j : Fin k) (hj : j.val + 1 < k),
        |φ (i ⟨j.val + 1, hj⟩)| ≤ γ * |φ (i j)|) ∧
      ∀ j : Fin k, |φ (i j)| ≤ γ ^ j.val * |φ (i ⟨0, hk⟩)| := by sorry
