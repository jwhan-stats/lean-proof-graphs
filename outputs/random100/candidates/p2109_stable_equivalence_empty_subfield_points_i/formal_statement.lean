theorem stable_equivalence_empty_subfield_points_iff
    (n m : ℕ) (V : Set (Fin n → ℝ)) (W : Set (Fin m → ℝ))
    (A : Subfield ℝ)
    (hA : Algebra.IsAlgebraic ℚ A)
    (hV : V ∈ BooleanSubalgebra.closure
      {s : Set (Fin n → ℝ) |
        ∃ p : MvPolynomial (Fin n) ℝ,
          s = {x | MvPolynomial.eval x p = 0} ∨
          s = {x | MvPolynomial.eval x p > 0}})
    (hW : W ∈ BooleanSubalgebra.closure
      {s : Set (Fin m → ℝ) |
        ∃ p : MvPolynomial (Fin m) ℝ,
          s = {x | MvPolynomial.eval x p = 0} ∨
          s = {x | MvPolynomial.eval x p > 0}})
    (hstable : Relation.EqvGen
      (fun X Y : Σ k : ℕ, Set (Fin k → ℝ) =>
        (∃ (k d : ℕ) (S : Set (Fin k → ℝ)) (T : Set (Fin (k + d) → ℝ)),
          X = ⟨k, S⟩ ∧ Y = ⟨k + d, T⟩ ∧
          ∃ (r s : ℕ)
            (φ : Fin r → Fin d → MvPolynomial (Fin k) ℤ)
            (ψ : Fin s → Fin d → MvPolynomial (Fin k) ℤ),
            (∀ v ∈ S, ∃ v' : Fin d → ℝ, Fin.append v v' ∈ T) ∧
            ∀ (v : Fin k → ℝ) (v' : Fin d → ℝ),
              Fin.append v v' ∈ T ↔
                v ∈ S ∧
                (∀ i : Fin r,
                  ∑ j : Fin d,
                    MvPolynomial.eval₂ (Int.castRingHom ℝ) v (φ i j) * v' j > 0) ∧
                (∀ i : Fin s,
                  ∑ j : Fin d,
                    MvPolynomial.eval₂ (Int.castRingHom ℝ) v (ψ i j) * v' j = 0)) ∨
        (∃ (k l : ℕ) (S : Set (Fin k → ℝ)) (T : Set (Fin l → ℝ)),
          X = ⟨k, S⟩ ∧ Y = ⟨l, T⟩ ∧
          ∃ h : S ≃ₜ T,
            (∀ i : Fin l, ∃ p q : MvPolynomial (Fin k) ℚ,
              ∀ v : S,
                MvPolynomial.eval₂ (Rat.castHom ℝ) (v : Fin k → ℝ) q ≠ 0 ∧
                (h v : Fin l → ℝ) i =
                  MvPolynomial.eval₂ (Rat.castHom ℝ) (v : Fin k → ℝ) p /
                    MvPolynomial.eval₂ (Rat.castHom ℝ) (v : Fin k → ℝ) q) ∧
            (∀ i : Fin k, ∃ p q : MvPolynomial (Fin l) ℚ,
              ∀ w : T,
                MvPolynomial.eval₂ (Rat.castHom ℝ) (w : Fin l → ℝ) q ≠ 0 ∧
                (h.symm w : Fin k → ℝ) i =
                  MvPolynomial.eval₂ (Rat.castHom ℝ) (w : Fin l → ℝ) p /
                    MvPolynomial.eval₂ (Rat.castHom ℝ) (w : Fin l → ℝ) q)))
      ⟨n, V⟩ ⟨m, W⟩) :
    (¬ ∃ v : Fin n → A, (fun i => ((v i : A) : ℝ)) ∈ V) ↔
      (¬ ∃ w : Fin m → A, (fun i => ((w i : A) : ℝ)) ∈ W) := by sorry
