import Mathlib

/- verified submission -/
lemma finite_diversity_singleton_zero
    {X : Type*} (δ : {A : Set X // A.Finite} → ℝ)
    (h_zero : ∀ A : {A : Set X // A.Finite}, δ A = 0 ↔ A.1.Subsingleton)
    (x : X) :
    δ ⟨{x}, Set.finite_singleton x⟩ = 0 := by
  exact (h_zero _).2 Set.subsingleton_singleton

lemma finite_diversity_pair_self
    {X : Type*} (δ : {A : Set X // A.Finite} → ℝ)
    (h_zero : ∀ A : {A : Set X // A.Finite}, δ A = 0 ↔ A.1.Subsingleton)
    (x : X) :
    δ ⟨{x, x}, (Set.finite_singleton x).insert x⟩ = 0 := by
  apply (h_zero _).2
  intro a ha b hb
  simp at ha hb
  subst a
  subst b
  rfl

lemma finite_diversity_pair_comm
    {X : Type*} (δ : {A : Set X // A.Finite} → ℝ)
    (x y : X) :
    δ ⟨{x, y}, (Set.finite_singleton y).insert x⟩ =
      δ ⟨{y, x}, (Set.finite_singleton x).insert y⟩ := by
  exact congrArg δ (Subtype.ext (Set.pair_comm x y))

lemma finite_diversity_pair_eq
    {X : Type*} (δ : {A : Set X // A.Finite} → ℝ)
    (h_zero : ∀ A : {A : Set X // A.Finite}, δ A = 0 ↔ A.1.Subsingleton)
    {x y : X}
    (h : δ ⟨{x, y}, (Set.finite_singleton y).insert x⟩ = 0) : x = y := by
  have hs : ({x, y} : Set X).Subsingleton := (h_zero _).1 h
  exact hs (by simp) (by simp)

lemma finite_diversity_pair_triangle
    {X : Type*} (δ : {A : Set X // A.Finite} → ℝ)
    (h_triangle : ∀ A B C : {A : Set X // A.Finite}, B.1.Nonempty →
      δ ⟨A.1 ∪ C.1, A.2.union C.2⟩ ≤
        δ ⟨A.1 ∪ B.1, A.2.union B.2⟩ + δ ⟨B.1 ∪ C.1, B.2.union C.2⟩)
    (x y z : X) :
    δ ⟨{x, z}, (Set.finite_singleton z).insert x⟩ ≤
      δ ⟨{x, y}, (Set.finite_singleton y).insert x⟩ +
        δ ⟨{y, z}, (Set.finite_singleton z).insert y⟩ := by
  have h := h_triangle ⟨{x}, Set.finite_singleton x⟩
    ⟨{y}, Set.finite_singleton y⟩ ⟨{z}, Set.finite_singleton z⟩
    (Set.singleton_nonempty y)
  simpa [Set.singleton_union, Set.pair_comm] using h

lemma finite_diversity_mono
    {X : Type*} (δ : {A : Set X // A.Finite} → ℝ)
    (h_zero : ∀ A : {A : Set X // A.Finite}, δ A = 0 ↔ A.1.Subsingleton)
    (h_triangle : ∀ A B C : {A : Set X // A.Finite}, B.1.Nonempty →
      δ ⟨A.1 ∪ C.1, A.2.union C.2⟩ ≤
        δ ⟨A.1 ∪ B.1, A.2.union B.2⟩ + δ ⟨B.1 ∪ C.1, B.2.union C.2⟩)
    (A B : {A : Set X // A.Finite}) (hAB : A.1 ⊆ B.1) :
    δ A ≤ δ B := by
  have hkey : ∀ D : Set X, ∀ hD : D.Finite,
      δ A ≤ δ ⟨A.1 ∪ D, A.2.union hD⟩ := by
    intro D hD
    induction D, hD using Set.Finite.induction_on with
    | empty =>
        simp
    | insert ha hs ih =>
        rename_i a s
        have htri := h_triangle ⟨∅, Set.finite_empty⟩ ⟨{a}, Set.finite_singleton a⟩
          ⟨A.1 ∪ s, A.2.union hs⟩ (Set.singleton_nonempty a)
        have hstep :
            δ ⟨A.1 ∪ s, A.2.union hs⟩ ≤
              δ ⟨A.1 ∪ insert a s, A.2.union (hs.insert a)⟩ := by
          have hzero := finite_diversity_singleton_zero δ h_zero a
          simpa [hzero, Set.empty_union, Set.singleton_union, Set.union_assoc,
            Set.union_comm, Set.union_left_comm] using htri
        exact le_trans ih hstep
  have hdiff : (B.1 \ A.1).Finite := B.2.diff
  have h := hkey (B.1 \ A.1) hdiff
  simpa [Set.union_diff_cancel hAB] using h

lemma finite_diversity_union_le
    {X : Type*} (δ : {A : Set X // A.Finite} → ℝ)
    (h_triangle : ∀ A B C : {A : Set X // A.Finite}, B.1.Nonempty →
      δ ⟨A.1 ∪ C.1, A.2.union C.2⟩ ≤
        δ ⟨A.1 ∪ B.1, A.2.union B.2⟩ + δ ⟨B.1 ∪ C.1, B.2.union C.2⟩)
    (A B : {A : Set X // A.Finite}) (hAB : (A.1 ∩ B.1).Nonempty) :
    δ ⟨A.1 ∪ B.1, A.2.union B.2⟩ ≤ δ A + δ B := by
  let I : {A : Set X // A.Finite} :=
    ⟨A.1 ∩ B.1, A.2.subset Set.inter_subset_left⟩
  have htri := h_triangle A I B hAB
  simpa [I, Set.union_eq_left.mpr Set.inter_subset_left,
    Set.union_eq_right.mpr Set.inter_subset_right] using htri

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
        δ ⟨A.1 ∪ B.1, A.2.union B.2⟩ ≤ δ A + δ B) := by
  let d : X → X → ℝ := fun x y =>
    δ ⟨{x, y}, (Set.finite_singleton y).insert x⟩
  letI : Dist X := ⟨d⟩
  let pm : PseudoMetricSpace X := {
    dist_self := by
      intro x
      exact finite_diversity_pair_self δ h_zero x
    dist_comm := by
      intro x y
      exact finite_diversity_pair_comm δ x y
    dist_triangle := by
      intro x y z
      exact finite_diversity_pair_triangle δ h_triangle x y z
  }
  letI : PseudoMetricSpace X := pm
  refine ⟨⟨MetricSpace.mk ?_, ?_⟩, ?_, ?_⟩
  · intro x y hxy
    change δ ⟨{x, y}, (Set.finite_singleton y).insert x⟩ = 0 at hxy
    exact finite_diversity_pair_eq δ h_zero hxy
  · intro x y
    rfl
  · intro A B hAB
    exact finite_diversity_mono δ h_zero h_triangle A B hAB
  · intro A B hAB
    exact finite_diversity_union_le δ h_triangle A B hAB
