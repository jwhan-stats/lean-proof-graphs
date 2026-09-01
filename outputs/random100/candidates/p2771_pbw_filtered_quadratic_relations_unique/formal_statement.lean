theorem pbw_filtered_quadratic_relations_unique
    (k T : Type*) [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (P Q : Set T) (I : TwoSidedIdeal T)
    (hP₂ : P ⊆ (⨆ i : Fin 3, 𝒯 (i : ℕ)))
    (hQ₂ : Q ⊆ (⨆ i : Fin 3, 𝒯 (i : ℕ)))
    (hPI : TwoSidedIdeal.span P = I)
    (hQI : TwoSidedIdeal.span Q = I)
    (hPpbw : ∀ (n : ℕ) (x : T), x ∈ 𝒯 n →
      (x ∈ TwoSidedIdeal.span ((GradedAlgebra.proj 𝒯 2) '' P) ↔
        ∃ y ∈ I, x - y ∈ (⨆ i : Fin n, 𝒯 (i : ℕ))))
    (hQpbw : ∀ (n : ℕ) (x : T), x ∈ 𝒯 n →
      (x ∈ TwoSidedIdeal.span ((GradedAlgebra.proj 𝒯 2) '' Q) ↔
        ∃ y ∈ I, x - y ∈ (⨆ i : Fin n, 𝒯 (i : ℕ)))) :
    AddSubgroup.closure {x : T | ∃ a ∈ 𝒯 0, ∃ p ∈ P, ∃ b ∈ 𝒯 0, x = a * p * b} =
        AddSubgroup.closure {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b} ∧
      (((∃ M : AddSubgroup T, (M : Set T) = P ∧
          (∀ (a : 𝒯 0) (x : T), x ∈ M → (a : T) * x ∈ M) ∧
          (∀ (a : 𝒯 0) (x : T), x ∈ M → x * (a : T) ∈ M)) ∧
        (∃ N : AddSubgroup T, (N : Set T) = Q ∧
          (∀ (a : 𝒯 0) (x : T), x ∈ N → (a : T) * x ∈ N) ∧
          (∀ (a : 𝒯 0) (x : T), x ∈ N → x * (a : T) ∈ N))) → P = Q) := by sorry
