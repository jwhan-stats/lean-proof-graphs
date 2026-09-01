theorem graded_dual_rational_map_mem_completion
    {n : ℕ} (hn : 0 < n)
    (W : ℂ → Type*) [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)]
    (f : {z : Fin n → ℂ // Function.Injective z} →
      Module.Dual ℂ (DirectSum ℂ (fun a => Module.Dual ℂ (W a))))
    (p : Fin n → Fin n → ℤ)
    (g : (Fin n →₀ ℕ) → (∀ a, W a))
    (C : ℂ) :
    letI := Classical.decEq ℂ
    (∀ w' : DirectSum ℂ (fun a => Module.Dual ℂ (W a)),
      ∃ (q : Fin n → Fin n → ℕ) (P : MvPolynomial (Fin n) ℂ),
        ∀ z : {z : Fin n → ℂ // Function.Injective z},
          f z w' = MvPolynomial.eval z.1 P /
            (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (z.1 i - z.1 j) ^ q i j)) →
    (∀ w' : DirectSum ℂ (fun a => Module.Dual ℂ (W a)),
      ∃ P : MvPolynomial (Fin n) ℂ,
        (∀ α : Fin n →₀ ℕ,
          MvPolynomial.coeff α P =
            (DirectSum.toModule ℂ ℂ ℂ
              (fun a => (Module.Dual.eval ℂ (W a)) (g α a))) w') ∧
        ∀ z : {z : Fin n → ℂ // Function.Injective z},
          (∏ i : Fin n, ∏ j ∈ Finset.Ioi i,
              (z.1 i - z.1 j) ^ p i j) * f z w' = MvPolynomial.eval z.1 P) →
    (∀ (α : Fin n →₀ ℕ) (a : ℂ),
      a ≠ C + (α.sum fun _ e => e : ℂ) → g α a = 0) →
    ∀ z : {z : Fin n → ℂ // Function.Injective z},
      ∃ b : ∀ a, W a,
        f z = DirectSum.toModule ℂ ℂ ℂ
          (fun a => (Module.Dual.eval ℂ (W a)) (b a)) := by sorry
