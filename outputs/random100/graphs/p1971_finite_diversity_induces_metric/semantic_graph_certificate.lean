import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1971_finite_diversity_induces_metric
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: c03a45d7a39d855d98881c8e2d73689fa54da6b90960483569ca3b857b3d8a26
-- reconstructed_proof_sha256: 7179d6e8b449b6a305f7c375fca32c0b4443aa103b1105432d1b9ff09db445c4
-- selected_edge_count: 1

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


#check_dependency_graph "finite_diversity_induces_metric" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(∃ m, ∀ (x y : X), dist x y = δ ⟨{x, y}, ⋯⟩) ∧ (∀ (A B : { A // A.Finite }), ↑A ⊆ ↑B → δ A ≤ δ B) ∧ ∀ (A B : { A // A.Finite }), (↑A ∩ ↑B).Nonempty → δ ⟨↑A ∪ ↑B, ⋯⟩ ≤ δ A + δ B\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"h_zero\",\"statement\":\"∀ (A : { A // A.Finite }), δ A = 0 ↔ (↑A).Subsingleton\"},{\"name\":\"h_triangle\",\"statement\":\"∀ (A B C : { A // A.Finite }), (↑B).Nonempty → δ ⟨↑A ∪ ↑C, ⋯⟩ ≤ δ ⟨↑A ∪ ↑B, ⋯⟩ + δ ⟨↑B ∪ ↑C, ⋯⟩\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1971_finite_diversity_induces_metric\",\"reconstructedProofSha256\":\"7179d6e8b449b6a305f7c375fca32c0b4443aa103b1105432d1b9ff09db445c4\",\"selectedEdgeCount\":1,\"theoremName\":\"finite_diversity_induces_metric\",\"topologySha256\":\"c03a45d7a39d855d98881c8e2d73689fa54da6b90960483569ca3b857b3d8a26\"}"
