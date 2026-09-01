theorem finite_diversity_induces_metric
    {X : Type*} (δ : {A : Set X // A.Finite} → ℝ)
    (h_nonneg : ∀ A : {A : Set X // A.Finite}, 0 ≤ δ A)
    (h_zero : ∀ A : {A : Set X // A.Finite}, δ A = 0 ↔ A.1.Subsingleton)
    (h_triangle : ∀ A B C : {A : Set X // A.Finite}, B.1.Nonempty →
      δ ⟨A.1 ∪ C.1, A.2.union C.2⟩ ≤
        δ ⟨A.1 ∪ B.1, A.2.union B.2⟩ + δ ⟨B.1 ∪ C.1, B.2.union C.2⟩) :
    (∃ m : MetricSpace X, ∀ x y : X,
      m.dist x y = δ ⟨{x, y}, (Set.finite_singleton y).insert x⟩) ∧
      (∀ A B : {A : Set X // A.Finite}, A.1 ⊆ B.1 → δ A ≤ δ B) ∧
      (∀ A B : {A : Set X // A.Finite}, (A.1 ∩ B.1).Nonempty →
        δ ⟨A.1 ∪ B.1, A.2.union B.2⟩ ≤ δ A + δ B) := by sorry
