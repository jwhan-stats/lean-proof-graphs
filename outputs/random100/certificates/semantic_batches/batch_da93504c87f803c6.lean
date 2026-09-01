import GraphCertificate
import Mathlib

namespace Rollout_p1918_correspondence_of_induced_probability_assi

-- graph_id: p1918_correspondence_of_induced_probability_assi
-- topology_sha256: 904ffa87e9965ebbd17e6fd553aa5ec27a654b9b759f39bd4bd300ddc3f04112
/- accepted add_to_file helper 1 -/
lemma toReal_measure_sdiff_add_inter
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsFiniteMeasure μ]
    (s t : Set α) (ht : MeasurableSet t) :
    (μ (s \ t)).toReal + (μ (s ∩ t)).toReal = (μ s).toReal := by
  have h := MeasureTheory.measure_diff_add_inter (μ := μ) s ht
  have h' := congrArg ENNReal.toReal h
  rwa [ENNReal.toReal_add (MeasureTheory.measure_ne_top μ _)
    (MeasureTheory.measure_ne_top μ _)] at h'

lemma toReal_measure_univ_diff_union
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
    (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (μ (Set.univ \ (s ∪ t))).toReal =
      1 - (μ s).toReal - (μ t).toReal + (μ (s ∩ t)).toReal := by
  let u : Set α := s ∪ t
  have hd : Disjoint (Set.univ \ u) u := disjoint_sdiff_self_left
  have hcompENN : μ (Set.univ \ u) + μ u = 1 := by
    have h := MeasureTheory.measure_union (μ := μ) hd (hs.union ht)
    have huniv : Set.univ \ u ∪ u = Set.univ := by
      simp [Set.diff_union_self]
    rw [huniv] at h
    simpa using h.symm
  have hcomp := congrArg ENNReal.toReal hcompENN
  rw [ENNReal.toReal_add (MeasureTheory.measure_ne_top μ _)
    (MeasureTheory.measure_ne_top μ _)] at hcomp
  have hunionENN : μ (s ∪ t) + μ (s ∩ t) = μ s + μ t :=
    MeasureTheory.measure_union_add_inter (μ := μ) s ht
  have hunion := congrArg ENNReal.toReal hunionENN
  rw [ENNReal.toReal_add (MeasureTheory.measure_ne_top μ _)
    (MeasureTheory.measure_ne_top μ _),
    ENNReal.toReal_add (MeasureTheory.measure_ne_top μ _)
    (MeasureTheory.measure_ne_top μ _)] at hunion
  dsimp [u] at hcomp
  nlinarith

lemma four_valued_tuple_eq
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    [MeasureTheory.IsProbabilityMeasure μ]
    (s t : Set α) (hs : MeasurableSet s) (ht : MeasurableSet t) :
    ((μ s).toReal - (μ (s ∩ t)).toReal,
      (μ t).toReal - (μ (s ∩ t)).toReal,
      1 - (μ s).toReal - (μ t).toReal + (μ (s ∩ t)).toReal,
      (μ (s ∩ t)).toReal) =
    ((μ (s \ t)).toReal,
      (μ (t \ s)).toReal,
      (μ (Set.univ \ (s ∪ t))).toReal,
      (μ (s ∩ t)).toReal) := by
  have hs_partition : (μ (s \ t)).toReal + (μ (s ∩ t)).toReal = (μ s).toReal :=
    toReal_measure_sdiff_add_inter (μ := μ) s t ht
  have ht_partition : (μ (t \ s)).toReal + (μ (s ∩ t)).toReal = (μ t).toReal := by
    have h := toReal_measure_sdiff_add_inter (μ := μ) t s hs
    rwa [Set.inter_comm] at h
  have hcompl := toReal_measure_univ_diff_union (μ := μ) s t hs ht
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · nlinarith
  · nlinarith
  · rw [hcompl]
  · rfl

/- verified submission -/
theorem correspondence_of_induced_probability_assignments
    {Atom : Type*} [Fintype Atom]
    {State : Type*} [Countable State]
    (vPos vNeg : Atom → Set State)
    (μ : @MeasureTheory.Measure State ⊤)
    [MeasureTheory.IsProbabilityMeasure μ] :
    let formulas : Set Mathlib.Tactic.ITauto.IProp :=
      {φ | ∀ S : Set Mathlib.Tactic.ITauto.IProp,
        (∀ a : Atom,
          Mathlib.Tactic.ITauto.IProp.var (Fintype.equivFin Atom a) ∈ S) →
        (∀ ψ ∈ S, Mathlib.Tactic.ITauto.IProp.not ψ ∈ S) →
        (∀ ψ χ, ψ ∈ S → χ ∈ S → Mathlib.Tactic.ITauto.IProp.and ψ χ ∈ S) →
        φ ∈ S}
    let Formula := ↥formulas
    let atom : Atom → Formula :=
      fun a => ⟨Mathlib.Tactic.ITauto.IProp.var (Fintype.equivFin Atom a),
        fun S hAtom _ _ => hAtom a⟩
    let neg : Formula → Formula :=
      fun φ => ⟨Mathlib.Tactic.ITauto.IProp.not φ.1,
        fun S hAtom hNeg hConj => hNeg φ.1 (φ.2 S hAtom hNeg hConj)⟩
    let conj : Formula → Formula → Formula :=
      fun φ ψ => ⟨Mathlib.Tactic.ITauto.IProp.and φ.1 ψ.1,
        fun S hAtom hNeg hConj =>
          hConj φ.1 ψ.1 (φ.2 S hAtom hNeg hConj) (ψ.2 S hAtom hNeg hConj)⟩
    ∀ (P N : Formula → Set State),
      (∀ a, P (atom a) = vPos a) →
      (∀ a, N (atom a) = vNeg a) →
      (∀ φ, P (neg φ) = N φ) →
      (∀ φ, N (neg φ) = P φ) →
      (∀ φ ψ, P (conj φ ψ) = P φ ∩ P ψ) →
      (∀ φ ψ, N (conj φ ψ) = N φ ∪ N ψ) →
      let p : Formula → ℝ := fun φ => (μ (P φ)).toReal
      let q : Formula → ℝ × (ℝ × (ℝ × ℝ)) :=
        fun φ =>
          ((μ (P φ \ N φ)).toReal,
            (μ (N φ \ P φ)).toReal,
            (μ (Set.univ \ (P φ ∪ N φ))).toReal,
            (μ (P φ ∩ N φ)).toReal)
      let T₄₁ : (Formula → ℝ × (ℝ × (ℝ × ℝ))) → Formula → ℝ :=
        fun r φ => (r φ).1 + (r φ).2.2.2
      let T₁₄ : (Formula → ℝ) → Formula → ℝ × (ℝ × (ℝ × ℝ)) :=
        fun r φ =>
          (r φ - r (conj φ (neg φ)),
            r (neg φ) - r (conj φ (neg φ)),
            1 - r φ - r (neg φ) + r (conj φ (neg φ)),
            r (conj φ (neg φ)))
      T₄₁ q = p ∧ T₁₄ p = q := by
  intro formulas Formula atom neg conj
  intro P N hPatom hNatom hPneg hNneg hPconj hNconj
  intro p q T41 T14
  constructor
  · funext φ
    have hpartition := @toReal_measure_sdiff_add_inter State ⊤ μ _ (P φ) (N φ)
      MeasurableSpace.measurableSet_top
    simp [T41, q, p]
    nlinarith
  · funext φ
    have hmeasP : @MeasurableSet State ⊤ (P φ) := MeasurableSpace.measurableSet_top
    have hmeasN : @MeasurableSet State ⊤ (N φ) := MeasurableSpace.measurableSet_top
    have hneg : P (neg φ) = N φ := hPneg φ
    have hconf : P (conj φ (neg φ)) = P φ ∩ N φ := by
      rw [hPconj, hneg]
    dsimp [T14, p, q]
    rw [hneg, hconf]
    exact @four_valued_tuple_eq State ⊤ μ _ (P φ) (N φ) hmeasP hmeasN

end Rollout_p1918_correspondence_of_induced_probability_assi

#check_dependency_graph "Rollout_p1918_correspondence_of_induced_probability_assi.correspondence_of_induced_probability_assignments" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"T41 q = p ∧ T14 p = q\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"MeasureTheory.IsProbabilityMeasure μ\"},{\"name\":\"hPneg\",\"statement\":\"∀ (φ : Formula), P (neg φ) = N φ\"},{\"name\":\"hPconj\",\"statement\":\"∀ (φ ψ : Formula), P (conj φ ψ) = P φ ∩ P ψ\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1918_correspondence_of_induced_probability_assi\",\"reconstructedProofSha256\":\"d592cb5cf85e2f5ad21a761b1d2d95a800d0e2356541daf5053ba5bd1caa4c20\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1918_correspondence_of_induced_probability_assi.correspondence_of_induced_probability_assignments\",\"topologySha256\":\"904ffa87e9965ebbd17e6fd553aa5ec27a654b9b759f39bd4bd300ddc3f04112\"}"

namespace Rollout_p1971_finite_diversity_induces_metric

-- graph_id: p1971_finite_diversity_induces_metric
-- topology_sha256: c03a45d7a39d855d98881c8e2d73689fa54da6b90960483569ca3b857b3d8a26
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

end Rollout_p1971_finite_diversity_induces_metric

#check_dependency_graph "Rollout_p1971_finite_diversity_induces_metric.finite_diversity_induces_metric" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(∃ m, ∀ (x y : X), dist x y = δ ⟨{x, y}, ⋯⟩) ∧ (∀ (A B : { A // A.Finite }), ↑A ⊆ ↑B → δ A ≤ δ B) ∧ ∀ (A B : { A // A.Finite }), (↑A ∩ ↑B).Nonempty → δ ⟨↑A ∪ ↑B, ⋯⟩ ≤ δ A + δ B\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"h_zero\",\"statement\":\"∀ (A : { A // A.Finite }), δ A = 0 ↔ (↑A).Subsingleton\"},{\"name\":\"h_triangle\",\"statement\":\"∀ (A B C : { A // A.Finite }), (↑B).Nonempty → δ ⟨↑A ∪ ↑C, ⋯⟩ ≤ δ ⟨↑A ∪ ↑B, ⋯⟩ + δ ⟨↑B ∪ ↑C, ⋯⟩\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1971_finite_diversity_induces_metric\",\"reconstructedProofSha256\":\"7179d6e8b449b6a305f7c375fca32c0b4443aa103b1105432d1b9ff09db445c4\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1971_finite_diversity_induces_metric.finite_diversity_induces_metric\",\"topologySha256\":\"c03a45d7a39d855d98881c8e2d73689fa54da6b90960483569ca3b857b3d8a26\"}"

namespace Rollout_p1994_quantitative_equivalence_of_plumpness_and_

-- graph_id: p1994_quantitative_equivalence_of_plumpness_and_
-- topology_sha256: a3bfaebfa10bc5c7babc922f77d3b381fa73f1340b54a9db20a291da7b6fa59f
/- accepted add_to_file helper 1 -/
lemma exists_dyadic_level
    {δ B₀ r : ℝ} (m : ℤ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hB₀ : 0 < B₀) (hr : 0 < r)
    (hrR : r ≤ B₀ * δ ^ (m - 1)) :
    ∃ k : ℤ, m ≤ k ∧ B₀ * δ ^ k ≤ r ∧ r ≤ B₀ * δ ^ (k - 1) := by
  let a : ℝ := δ⁻¹
  have ha : 1 < a := by
    dsimp [a]
    exact (one_lt_inv₀ hδ0).2 hδ1
  have hscale0 : 0 < B₀ * δ ^ (m - 1) := by
    positivity
  have hx : 1 ≤ (B₀ * δ ^ (m - 1)) / r := by
    rw [one_le_div hr]
    exact hrR
  obtain ⟨n, hn₁, hn₂⟩ := exists_nat_pow_near hx ha
  refine ⟨m + n, by omega, ?_, ?_⟩
  · have hn₂' := hn₂
    rw [show a ^ (n + 1) = (δ ^ ((n : ℤ) + 1))⁻¹ by
      have hcast : ((n : ℤ) + 1) = (((n + 1 : ℕ) : ℤ)) := by norm_num
      rw [hcast, zpow_natCast]
      simp [a]] at hn₂'
    have hq : 0 < δ ^ ((n : ℤ) + 1) := by positivity
    have hlt : B₀ * δ ^ (m - 1) * δ ^ ((n : ℤ) + 1) < r := by
      have h1 : B₀ * δ ^ (m - 1) < (δ ^ ((n : ℤ) + 1))⁻¹ * r :=
        (div_lt_iff₀ hr).1 hn₂'
      exact (lt_inv_mul_iff₀' hq).1 h1
    have hprod : δ ^ (m - 1) * δ ^ ((n : ℤ) + 1) = δ ^ (m + n) := by
      rw [← zpow_add₀ hδ0.ne']
      congr 1
      omega
    have hlt' : B₀ * δ ^ (m + n) < r := by
      rw [← hprod]
      nlinarith
    exact hlt'.le
  · have hn₁' := hn₁
    rw [show a ^ n = (δ ^ (n : ℤ))⁻¹ by
      simp [a, zpow_natCast]] at hn₁'
    have hq : 0 < δ ^ (n : ℤ) := by positivity
    have hle0 : (δ ^ (n : ℤ))⁻¹ * r ≤ B₀ * δ ^ (m - 1) :=
      (le_div_iff₀ hr).1 hn₁'
    have hle : r ≤ (B₀ * δ ^ (m - 1)) * δ ^ (n : ℤ) :=
      (inv_mul_le_iff₀' hq).1 hle0
    have hprod : δ ^ (m - 1) * δ ^ (n : ℤ) = δ ^ (m + n - 1) := by
      rw [← zpow_add₀ hδ0.ne']
      congr 1
      omega
    rw [show m + n - 1 = m + (n : ℤ) - 1 by omega] at hprod
    rw [← hprod]
    nlinarith

/- verified submission -/
theorem quantitative_equivalence_of_plumpness_and_dyadic_plumpness
    {X : Type*} [MetricSpace X] (E : Set X) :
    (∀ (R b : ℝ), 0 < R → 0 < b → b < 1 →
      (∀ y ∈ E, ∀ r : ℝ, 0 < r → r ≤ R →
        ∃ z : X, Metric.ball z (b * r) ⊆ Metric.ball y r ∩ E) →
      ∀ (δ : ℝ) (m : ℤ) (b₀ B₀ : ℝ),
        0 < δ → δ < 1 → 0 < b₀ → b₀ ≤ B₀ →
        b₀ / B₀ ≤ b → B₀ * δ ^ m ≤ R →
        ∀ y ∈ E, ∀ k : ℤ, m ≤ k →
          ∃ z : X, Metric.ball z (b₀ * δ ^ k) ⊆
            Metric.ball y (B₀ * δ ^ k) ∩ E) ∧
    (∀ (δ : ℝ) (m : ℤ) (b₀ B₀ : ℝ),
      0 < δ → δ < 1 → 0 < b₀ → b₀ ≤ B₀ →
      (∀ y ∈ E, ∀ k : ℤ, m ≤ k →
        ∃ z : X, Metric.ball z (b₀ * δ ^ k) ⊆
          Metric.ball y (B₀ * δ ^ k) ∩ E) →
      ∀ (R b : ℝ), 0 < R → 0 < b → b < 1 →
        b ≤ δ * b₀ / B₀ → R ≤ B₀ * δ ^ (m - 1) →
        ∀ y ∈ E, ∀ r : ℝ, 0 < r → r ≤ R →
          ∃ z : X, Metric.ball z (b * r) ⊆ Metric.ball y r ∩ E) := by
  constructor
  · intro R b hR hb hb1 hplump δ m b₀ B₀ hδ0 hδ1 hb₀ hb₀B₀ hratio hscale
    intro y hy k hk
    have hB₀ : 0 < B₀ := lt_of_lt_of_le hb₀ hb₀B₀
    have hr : 0 < B₀ * δ ^ k := by positivity
    have hpow : δ ^ k ≤ δ ^ m :=
      zpow_le_zpow_right_of_le_one₀ hδ0 hδ1.le hk
    have hrR : B₀ * δ ^ k ≤ R := by
      have hmul : B₀ * δ ^ k ≤ B₀ * δ ^ m :=
        mul_le_mul_of_nonneg_left hpow hB₀.le
      exact hmul.trans hscale
    obtain ⟨z, hz⟩ := hplump y hy (B₀ * δ ^ k) hr hrR
    refine ⟨z, ?_⟩
    have hbB : b₀ ≤ b * B₀ := by
      have := (div_le_iff₀ hB₀).1 hratio
      nlinarith
    have hb_radius : b₀ * δ ^ k ≤ b * (B₀ * δ ^ k) := by
      have hnonneg : 0 ≤ δ ^ k := by positivity
      have hmul := mul_le_mul_of_nonneg_right hbB hnonneg
      nlinarith
    exact (Metric.ball_subset_ball hb_radius).trans hz
  · intro δ m b₀ B₀ hδ0 hδ1 hb₀ hb₀B₀ hdyadic R b hR hb hb1 hbratio hRscale
    intro y hy r hr hrR
    have hB₀ : 0 < B₀ := lt_of_lt_of_le hb₀ hb₀B₀
    have hrscale : r ≤ B₀ * δ ^ (m - 1) := hrR.trans hRscale
    obtain ⟨k, hk, hk_low, hk_high⟩ :=
      exists_dyadic_level m hδ0 hδ1 hB₀ hr hrscale
    obtain ⟨z, hz⟩ := hdyadic y hy k hk
    refine ⟨z, ?_⟩
    have hbB : b * B₀ ≤ δ * b₀ :=
      (le_div_iff₀ hB₀).1 hbratio
    have hb_radius : b * r ≤ b₀ * δ ^ k := by
      have h1 : b * r ≤ b * (B₀ * δ ^ (k - 1)) :=
        mul_le_mul_of_nonneg_left hk_high hb.le
      have hpow : δ * δ ^ (k - 1) = δ ^ k := by
        nth_rewrite 1 [← zpow_one δ]
        rw [← zpow_add₀ hδ0.ne']
        congr 1
        omega
      have hnonneg : 0 ≤ δ ^ (k - 1) := by positivity
      have h2 : b * (B₀ * δ ^ (k - 1)) ≤ δ * b₀ * δ ^ (k - 1) := by
        have hmul := mul_le_mul_of_nonneg_right hbB hnonneg
        nlinarith
      have h3 : δ * b₀ * δ ^ (k - 1) = b₀ * δ ^ k := by
        calc
          δ * b₀ * δ ^ (k - 1) = b₀ * (δ * δ ^ (k - 1)) := by ring
          _ = b₀ * δ ^ k := by rw [hpow]
      exact h1.trans (h2.trans_eq h3)
    intro x hx
    have hxdy := hz ((Metric.ball_subset_ball hb_radius) hx)
    exact ⟨(Metric.ball_subset_ball hk_low) hxdy.1, hxdy.2⟩

end Rollout_p1994_quantitative_equivalence_of_plumpness_and_

#check_dependency_graph "Rollout_p1994_quantitative_equivalence_of_plumpness_and_.quantitative_equivalence_of_plumpness_and_dyadic_plumpness" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(∀ (R b : ℝ), 0 < R → 0 < b → b < 1 → (∀ y ∈ E, ∀ (r : ℝ), 0 < r → r ≤ R → ∃ z, Metric.ball z (b * r) ⊆ Metric.ball y r ∩ E) → ∀ (δ : ℝ) (m : ℤ) (b₀ B₀ : ℝ), 0 < δ → δ < 1 → 0 < b₀ → b₀ ≤ B₀ → b₀ / B₀ ≤ b → B₀ * δ ^ m ≤ R → ∀ y ∈ E, ∀ (k : ℤ), m ≤ k → ∃ z, Metric.ball z (b₀ * δ ^ k) ⊆ Metric.ball y (B₀ * δ ^ k) ∩ E) ∧ ∀ (δ : ℝ) (m : ℤ) (b₀ B₀ : ℝ), 0 < δ → δ < 1 → 0 < b₀ → b₀ ≤ B₀ → (∀ y ∈ E, ∀ (k : ℤ), m ≤ k → ∃ z, Metric.ball z (b₀ * δ ^ k) ⊆ Metric.ball y (B₀ * δ ^ k) ∩ E) → ∀ (R b : ℝ), 0 < R → 0 < b → b < 1 → b ≤ δ * b₀ / B₀ → R ≤ B₀ * δ ^ (m - 1) → ∀ y ∈ E, ∀ (r : ℝ), 0 < r → r ≤ R → ∃ z, Metric.ball z (b * r) ⊆ Metric.ball y r ∩ E\"},\"graphEdgeId\":\"h_goal\",\"premises\":[],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1994_quantitative_equivalence_of_plumpness_and_\",\"reconstructedProofSha256\":\"f47028aae7c3e54359a4373fa7145f71b660fa9db4c4fc46901c6b62e9e5d6f7\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1994_quantitative_equivalence_of_plumpness_and_.quantitative_equivalence_of_plumpness_and_dyadic_plumpness\",\"topologySha256\":\"a3bfaebfa10bc5c7babc922f77d3b381fa73f1340b54a9db20a291da7b6fa59f\"}"

namespace Rollout_p2049_scaling_implies_a_cone_distance

-- graph_id: p2049_scaling_implies_a_cone_distance
-- topology_sha256: 5e7d1222eab3158d1cbc4ea284d43f37ff4452b5d3b0f9afe6796516f43e5058
/- accepted add_to_file helper 1 -/
section ConeDistanceHelpers

variable {C X : Type*} [MetricSpace C]
variable (q : X × NNReal → C)

lemma cone_unit_dist_sq_mem_Icc
    (hbound : ∀ (x₀ x₁ : X), x₀ ≠ x₁ →
      0 < dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ∧
        dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ≤ 4)
    (x y : X) :
    dist (q (x, 1)) (q (y, 1)) ^ 2 ∈ Set.Icc (0 : ℝ) 4 := by
  by_cases hxy : x = y
  · subst y
    simp
  · exact ⟨(hbound x y hxy).1.le, (hbound x y hxy).2⟩

lemma cone_angle_mem_Icc (x y : X) :
    Real.arccos (1 - dist (q (x, 1)) (q (y, 1)) ^ 2 / 2) ∈
      Set.Icc (0 : ℝ) Real.pi := by
  exact ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

lemma cone_cos_angle
    (hbound : ∀ (x₀ x₁ : X), x₀ ≠ x₁ →
      0 < dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ∧
        dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ≤ 4)
    (x y : X) :
    Real.cos (Real.arccos (1 - dist (q (x, 1)) (q (y, 1)) ^ 2 / 2)) =
      1 - dist (q (x, 1)) (q (y, 1)) ^ 2 / 2 := by
  have h := cone_unit_dist_sq_mem_Icc (C:=C) (X:=X) q hbound x y
  rw [Set.mem_Icc] at h
  apply Real.cos_arccos
  · linarith
  · linarith

lemma cone_angle_self (x : X) :
    Real.arccos (1 - dist (q (x, 1)) (q (x, 1)) ^ 2 / 2) = 0 := by
  simp

lemma cone_angle_comm (x y : X) :
    Real.arccos (1 - dist (q (x, 1)) (q (y, 1)) ^ 2 / 2) =
      Real.arccos (1 - dist (q (y, 1)) (q (x, 1)) ^ 2 / 2) := by
  rw [dist_comm]

lemma cone_angle_eq_zero_iff
    (hbound : ∀ (x₀ x₁ : X), x₀ ≠ x₁ →
      0 < dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ∧
        dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ≤ 4)
    (x y : X) :
    Real.arccos (1 - dist (q (x, 1)) (q (y, 1)) ^ 2 / 2) = 0 ↔ x = y := by
  constructor
  · intro hθ
    by_contra hxy
    have hb := hbound x y hxy
    have hcos := cone_cos_angle (C:=C) (X:=X) q hbound x y
    rw [hθ, Real.cos_zero] at hcos
    nlinarith
  · intro hxy
    subst y
    exact cone_angle_self (C:=C) q x

lemma cone_dist_sq
    (hscale : ∀ (x₀ x₁ : X) (r₀ r₁ : NNReal),
      dist (q (x₀, r₀)) (q (x₁, r₁)) ^ 2 =
        (r₀ : ℝ) * (r₁ : ℝ) * dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 +
          ((r₀ : ℝ) - (r₁ : ℝ)) ^ 2)
    (hbound : ∀ (x₀ x₁ : X), x₀ ≠ x₁ →
      0 < dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ∧
        dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ≤ 4)
    (x y : X) (r s : NNReal) :
    dist (q (x, r)) (q (y, s)) ^ 2 =
      (r : ℝ) ^ 2 + (s : ℝ) ^ 2 -
        2 * (r : ℝ) * (s : ℝ) *
          Real.cos (Real.arccos (1 - dist (q (x, 1)) (q (y, 1)) ^ 2 / 2)) := by
  rw [hscale x y r s, cone_cos_angle (C:=C) (X:=X) q hbound x y]
  ring

end ConeDistanceHelpers

/- accepted add_to_file helper 2 -/
lemma cone_path_sq_eq_aux (A B L M : ℝ)
    (hA : 0 < Real.sin A)
    (hL : L ^ 2 = (Real.sin B / Real.sin A)^2 +
      (Real.sin (A+B)/(2*Real.sin A))^2 -
      2*(Real.sin B / Real.sin A)*(Real.sin (A+B)/(2*Real.sin A))*Real.cos A)
    (hM : M ^ 2 = (Real.sin (A+B)/(2*Real.sin A))^2 + 1 -
      2*(Real.sin (A+B)/(2*Real.sin A))*1*Real.cos B) :
    L ^ 2 = M ^ 2 := by
  rw [hL,hM]
  field_simp [ne_of_gt hA]
  rw [Real.sin_add A B]
  nlinarith [Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B]

lemma cone_path_sum_sq_aux (A B L : ℝ)
    (hA : 0 < Real.sin A)
    (hL : L ^ 2 = (Real.sin B / Real.sin A)^2 +
      (Real.sin (A+B)/(2*Real.sin A))^2 -
      2*(Real.sin B / Real.sin A)*(Real.sin (A+B)/(2*Real.sin A))*Real.cos A) :
    (L + L)^2 = (Real.sin B / Real.sin A)^2 + 1 -
      2*(Real.sin B / Real.sin A)*1*Real.cos (A+B) := by
  rw [Real.sin_add A B] at hL
  field_simp [ne_of_gt hA] at hL
  rw [Real.cos_add A B]
  rw [show (L + L)^2 = 4 * L^2 by ring]
  field_simp [ne_of_gt hA]
  nlinarith [hL, Real.sin_sq_add_cos_sq A, Real.sin_sq_add_cos_sq B]

/- accepted add_to_file helper 3 -/
section ConeDistanceTriangle

variable {C X : Type*} [MetricSpace C]
variable (q : X × NNReal → C)

lemma cone_angle_triangle
    (hscale : ∀ (x₀ x₁ : X) (r₀ r₁ : NNReal),
      dist (q (x₀, r₀)) (q (x₁, r₁)) ^ 2 =
        (r₀ : ℝ) * (r₁ : ℝ) * dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 +
          ((r₀ : ℝ) - (r₁ : ℝ)) ^ 2)
    (hbound : ∀ (x₀ x₁ : X), x₀ ≠ x₁ →
      0 < dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ∧
        dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ≤ 4)
    (x y z : X) :
    Real.arccos (1 - dist (q (x, 1)) (q (z, 1)) ^ 2 / 2) ≤
      Real.arccos (1 - dist (q (x, 1)) (q (y, 1)) ^ 2 / 2) +
        Real.arccos (1 - dist (q (y, 1)) (q (z, 1)) ^ 2 / 2) := by
  by_cases hxy : x = y
  · subst y
    rw [cone_angle_self (C:=C) q x]
    simp
  by_cases hyz : y = z
  · subst z
    rw [cone_angle_self (C:=C) q y]
    simp
  let a := Real.arccos (1 - dist (q (x, 1)) (q (y, 1)) ^ 2 / 2)
  let b := Real.arccos (1 - dist (q (y, 1)) (q (z, 1)) ^ 2 / 2)
  let c := Real.arccos (1 - dist (q (x, 1)) (q (z, 1)) ^ 2 / 2)
  have haI : a ∈ Set.Icc (0 : ℝ) Real.pi := cone_angle_mem_Icc (C:=C) q x y
  have hbI : b ∈ Set.Icc (0 : ℝ) Real.pi := cone_angle_mem_Icc (C:=C) q y z
  have hcI : c ∈ Set.Icc (0 : ℝ) Real.pi := cone_angle_mem_Icc (C:=C) q x z
  rw [Set.mem_Icc] at haI hbI hcI
  have hane : a ≠ 0 := by
    intro ha
    exact hxy ((cone_angle_eq_zero_iff (C:=C) q hbound x y).mp ha)
  have hbne : b ≠ 0 := by
    intro hb
    exact hyz ((cone_angle_eq_zero_iff (C:=C) q hbound y z).mp hb)
  have hapos : 0 < a := lt_of_le_of_ne haI.1 (Ne.symm hane)
  have hbpos : 0 < b := lt_of_le_of_ne hbI.1 (Ne.symm hbne)
  by_cases hsum : Real.pi ≤ a + b
  · exact le_trans hcI.2 hsum
  · have hslt : a + b < Real.pi := lt_of_not_ge hsum
    by_contra hcle
    have hgt : a + b < c := lt_of_not_ge hcle
    have hspos : 0 < a + b := add_pos hapos hbpos
    have halt : a < Real.pi := by nlinarith
    have hblt : b < Real.pi := by nlinarith
    have hsinA : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi hapos halt
    have hsinB : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hbpos hblt
    have hsinS : 0 < Real.sin (a + b) := Real.sin_pos_of_pos_of_lt_pi hspos hslt
    let rv : ℝ := Real.sin b / Real.sin a
    let tv : ℝ := Real.sin (a + b) / (2 * Real.sin a)
    have hrvpos : 0 < rv := div_pos hsinB hsinA
    have htvpos : 0 < tv := div_pos hsinS (by positivity)
    let r : NNReal := ⟨rv, le_of_lt hrvpos⟩
    let t : NNReal := ⟨tv, le_of_lt htvpos⟩
    let D : ℝ := dist (q (x, r)) (q (z, 1))
    let L : ℝ := dist (q (x, r)) (q (y, t))
    let M : ℝ := dist (q (y, t)) (q (z, 1))
    have htri : D ≤ L + M := dist_triangle _ _ _
    have hD : D ^ 2 = rv ^ 2 + (1 : ℝ) ^ 2 -
        2 * rv * (1 : ℝ) * Real.cos c := by
      have h := cone_dist_sq (C:=C) q hscale hbound x z r 1
      change D ^ 2 = (r : ℝ) ^ 2 + ((1 : NNReal) : ℝ) ^ 2 -
        2 * (r : ℝ) * (((1 : NNReal) : ℝ)) * Real.cos c at h
      simpa [rv] using h
    have hL : L ^ 2 = rv ^ 2 + tv ^ 2 -
        2 * rv * tv * Real.cos a := by
      have h := cone_dist_sq (C:=C) q hscale hbound x y r t
      change L ^ 2 = (r : ℝ) ^ 2 + (t : ℝ) ^ 2 -
        2 * (r : ℝ) * (t : ℝ) * Real.cos a at h
      simpa [rv, tv] using h
    have hM : M ^ 2 = tv ^ 2 + (1 : ℝ) ^ 2 -
        2 * tv * (1 : ℝ) * Real.cos b := by
      have h := cone_dist_sq (C:=C) q hscale hbound y z t 1
      change M ^ 2 = (t : ℝ) ^ 2 + ((1 : NNReal) : ℝ) ^ 2 -
        2 * (t : ℝ) * (((1 : NNReal) : ℝ)) * Real.cos b at h
      simpa [tv] using h
    have hL' : L ^ 2 = (Real.sin b / Real.sin a)^2 +
        (Real.sin (a+b)/(2*Real.sin a))^2 -
        2*(Real.sin b / Real.sin a)*(Real.sin (a+b)/(2*Real.sin a))*Real.cos a := by
      simpa [rv, tv] using hL
    have hM' : M ^ 2 = (Real.sin (a+b)/(2*Real.sin a))^2 + 1 -
        2*(Real.sin (a+b)/(2*Real.sin a))*1*Real.cos b := by
      simpa [tv] using hM
    have hsqLM : L ^ 2 = M ^ 2 :=
      cone_path_sq_eq_aux a b L M hsinA hL' hM'
    have hLM : L = M := by
      have habs := (sq_eq_sq_iff_abs_eq_abs L M).mp hsqLM
      rwa [abs_of_nonneg dist_nonneg, abs_of_nonneg dist_nonneg] at habs
    have hsumsq' := cone_path_sum_sq_aux a b L hsinA hL'
    have hsumsq : (L + M) ^ 2 = rv ^ 2 + 1 -
        2 * rv * (1 : ℝ) * Real.cos (a + b) := by
      rw [show M = L from hLM.symm]
      simpa [rv] using hsumsq'
    have htri_sq : D ^ 2 ≤ (L + M) ^ 2 :=
      pow_le_pow_left₀ dist_nonneg htri 2
    rw [hsumsq] at htri_sq
    have hcoss : Real.cos c < Real.cos (a + b) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi (le_of_lt hspos) hcI.2 hgt
    have hDgt : rv ^ 2 + 1 - 2 * rv * (1 : ℝ) * Real.cos (a + b) < D ^ 2 := by
      rw [hD]
      have hmul := mul_lt_mul_of_pos_left hcoss hrvpos
      nlinarith
    nlinarith

end ConeDistanceTriangle

/- verified submission -/
theorem scaling_implies_a_cone_distance
    {C X : Type*} [MetricSpace C]
    (q : X × NNReal → C)
    (hq : Function.Surjective q)
    (hscale : ∀ (x₀ x₁ : X) (r₀ r₁ : NNReal),
      dist (q (x₀, r₀)) (q (x₁, r₁)) ^ 2 =
        (r₀ : ℝ) * (r₁ : ℝ) * dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 +
          ((r₀ : ℝ) - (r₁ : ℝ)) ^ 2)
    (hbound : ∀ (x₀ x₁ : X), x₀ ≠ x₁ →
      0 < dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ∧
        dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ≤ 4) :
    let d_X : X × X → ℝ := fun p =>
      Real.arccos (1 - dist (q (p.1, 1)) (q (p.2, 1)) ^ 2 / 2);
    (∀ x₀ x₁ : X, d_X (x₀, x₁) ∈ Set.Icc (0 : ℝ) Real.pi) ∧
      (∃ m : MetricSpace X, ∀ x₀ x₁ : X,
        @dist X m.toPseudoMetricSpace.toDist x₀ x₁ = d_X (x₀, x₁)) ∧
      ∀ (x₀ x₁ : X) (r₀ r₁ : NNReal),
        dist (q (x₀, r₀)) (q (x₁, r₁)) ^ 2 =
          (r₀ : ℝ) ^ 2 + (r₁ : ℝ) ^ 2 -
            2 * (r₀ : ℝ) * (r₁ : ℝ) * Real.cos (d_X (x₀, x₁)) := by
  let dX : X × X → ℝ := fun p =>
    Real.arccos (1 - dist (q (p.1, 1)) (q (p.2, 1)) ^ 2 / 2)
  change (∀ x₀ x₁ : X, dX (x₀, x₁) ∈ Set.Icc (0 : ℝ) Real.pi) ∧
    (∃ m : MetricSpace X, ∀ x₀ x₁ : X,
      @dist X m.toPseudoMetricSpace.toDist x₀ x₁ = dX (x₀, x₁)) ∧
    ∀ (x₀ x₁ : X) (r₀ r₁ : NNReal),
      dist (q (x₀, r₀)) (q (x₁, r₁)) ^ 2 =
        (r₀ : ℝ) ^ 2 + (r₁ : ℝ) ^ 2 -
          2 * (r₀ : ℝ) * (r₁ : ℝ) * Real.cos (dX (x₀, x₁))
  let θ : X → X → ℝ := fun x y => dX (x, y)
  have hself : ∀ x : X, θ x x = 0 := by
    intro x
    exact cone_angle_self (C:=C) q x
  have hcomm : ∀ x y : X, θ x y = θ y x := by
    intro x y
    exact cone_angle_comm (C:=C) q x y
  have htriangle : ∀ x y z : X, θ x z ≤ θ x y + θ y z := by
    intro x y z
    exact cone_angle_triangle (C:=C) q hscale hbound x y z
  letI dinst : Dist X := ⟨θ⟩
  letI pms : PseudoMetricSpace X := {
    dist_self := hself
    dist_comm := hcomm
    dist_triangle := htriangle
  }
  let ms : MetricSpace X := MetricSpace.mk (by
    intro x y hxy
    exact (cone_angle_eq_zero_iff (C:=C) q hbound x y).mp hxy)
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    exact cone_angle_mem_Icc (C:=C) q x y
  · refine ⟨ms, ?_⟩
    intro x y
    rfl
  · intro x y r s
    exact cone_dist_sq (C:=C) q hscale hbound x y r s

end Rollout_p2049_scaling_implies_a_cone_distance

#check_dependency_graph "Rollout_p2049_scaling_implies_a_cone_distance.scaling_implies_a_cone_distance" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let d_X := fun p => Real.arccos (1 - dist (q (p.1, 1)) (q (p.2, 1)) ^ 2 / 2); (∀ (x₀ x₁ : X), d_X (x₀, x₁) ∈ Set.Icc 0 Real.pi) ∧ (∃ m, ∀ (x₀ x₁ : X), dist x₀ x₁ = d_X (x₀, x₁)) ∧ ∀ (x₀ x₁ : X) (r₀ r₁ : NNReal), dist (q (x₀, r₀)) (q (x₁, r₁)) ^ 2 = ↑r₀ ^ 2 + ↑r₁ ^ 2 - 2 * ↑r₀ * ↑r₁ * Real.cos (d_X (x₀, x₁))\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hscale\",\"statement\":\"∀ (x₀ x₁ : X) (r₀ r₁ : NNReal), dist (q (x₀, r₀)) (q (x₁, r₁)) ^ 2 = ↑r₀ * ↑r₁ * dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 + (↑r₀ - ↑r₁) ^ 2\"},{\"name\":\"hbound\",\"statement\":\"∀ (x₀ x₁ : X), x₀ ≠ x₁ → 0 < dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ∧ dist (q (x₀, 1)) (q (x₁, 1)) ^ 2 ≤ 4\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2049_scaling_implies_a_cone_distance\",\"reconstructedProofSha256\":\"83e661bf29631a62a059e6436706499cd614ac4ff8008fcef03117a510134bc7\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p2049_scaling_implies_a_cone_distance.scaling_implies_a_cone_distance\",\"topologySha256\":\"5e7d1222eab3158d1cbc4ea284d43f37ff4452b5d3b0f9afe6796516f43e5058\"}"

namespace Rollout_p2075_metric_amalgamation

-- graph_id: p2075_metric_amalgamation
-- topology_sha256: deb664ff2993b355db8b0a33e35ab9f9f0aae3ff5569326fe1891b0dcff1b2ed
/- accepted add_to_file helper 1 -/

noncomputable section

namespace MetricAmalgamation

variable {X : Type*} {I : Type*} [MetricSpace X]

def pieceIndex (B : I → Set X) (hB_cover : (⋃ i, B i) = Set.univ) (x : X) : I :=
  Classical.choose (by
    have hx : x ∈ (⋃ i, B i : Set X) := by
      rw [hB_cover]
      exact Set.mem_univ x
    exact Set.mem_iUnion.mp hx)

lemma mem_piece (B : I → Set X) (hB_cover : (⋃ i, B i) = Set.univ) (x : X) :
    x ∈ B (pieceIndex B hB_cover x) :=
  Classical.choose_spec (by
    have hx : x ∈ (⋃ i, B i : Set X) := by
      rw [hB_cover]
      exact Set.mem_univ x
    exact Set.mem_iUnion.mp hx)

lemma pieceIndex_eq_of_mem {B : I → Set X}
    (hB_disjoint : (Set.univ : Set I).PairwiseDisjoint B)
    (hB_cover : (⋃ i, B i) = Set.univ) {x : X} {i : I} (hx : x ∈ B i) :
    pieceIndex B hB_cover x = i := by
  classical
  by_contra hne
  have hd : Disjoint (B (pieceIndex B hB_cover x)) (B i) :=
    hB_disjoint (Set.mem_univ _) (Set.mem_univ _) hne
  exact Set.disjoint_iff_forall_ne.mp hd (mem_piece B hB_cover x) hx rfl

def piecePoint (B : I → Set X) (hB_cover : (⋃ i, B i) = Set.univ) (x : X) :
    B (pieceIndex B hB_cover x) :=
  ⟨x, mem_piece B hB_cover x⟩

def glueDist (B : I → Set X) (hB_cover : (⋃ i, B i) = Set.univ)
    (p : ∀ i, B i) (e : ∀ i, MetricSpace (B i)) (x y : X) : ℝ := by
  classical
  exact if h : pieceIndex B hB_cover x = pieceIndex B hB_cover y then
    @dist (B (pieceIndex B hB_cover x)) (e _).toPseudoMetricSpace.toDist
      (piecePoint B hB_cover x)
      ⟨y, by simpa [h] using mem_piece B hB_cover y⟩
  else
    @dist (B (pieceIndex B hB_cover x)) (e _).toPseudoMetricSpace.toDist
      (piecePoint B hB_cover x) (p _) +
    dist (p (pieceIndex B hB_cover x) : X) (p (pieceIndex B hB_cover y) : X) +
    @dist (B (pieceIndex B hB_cover y)) (e _).toPseudoMetricSpace.toDist
      (p _) (piecePoint B hB_cover y)

end MetricAmalgamation

end

/- accepted add_to_file helper 2 -/
namespace MetricAmalgamation

variable {X : Type*} {I : Type*} [MetricSpace X]
variable {B : I → Set X}
variable {p : ∀ i, B i}
variable {e : ∀ i, MetricSpace (B i)}

lemma glueDist_left_congr {a i : I} (h : a = i) {x : X} (hx : x ∈ B a) :
    @dist (B a) (e a).toPseudoMetricSpace.toDist (⟨x, hx⟩ : B a) (p a) =
      @dist (B i) (e i).toPseudoMetricSpace.toDist
        (⟨x, h ▸ hx⟩ : B i) (p i) := by
  cases h
  rfl

lemma glueDist_right_congr {b j : I} (h : b = j) {y : X} (hy : y ∈ B b) :
    @dist (B b) (e b).toPseudoMetricSpace.toDist (p b) (⟨y, hy⟩ : B b) =
      @dist (B j) (e j).toPseudoMetricSpace.toDist (p j)
        (⟨y, h ▸ hy⟩ : B j) := by
  cases h
  rfl

lemma glueDist_base_congr {a i b j : I} (ha : a = i) (hb : b = j) :
    dist (p a : X) (p b : X) = dist (p i : X) (p j : X) := by
  cases ha
  cases hb
  rfl

variable {hB_disjoint : (Set.univ : Set I).PairwiseDisjoint B}
variable {hB_cover : (⋃ i, B i) = Set.univ}

include hB_disjoint hB_cover in
lemma glueDist_subtype_same (i : I) (x y : B i) :
    glueDist B hB_cover p e (x : X) (y : X) =
      @dist (B i) (e i).toPseudoMetricSpace.toDist x y := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  have hxi := pieceIndex_eq_of_mem (B := B) hB_disjoint hB_cover hx
  have hyi := pieceIndex_eq_of_mem (B := B) hB_disjoint hB_cover hy
  have hi : i = pieceIndex B hB_cover x := hxi.symm
  subst hi
  simp [glueDist, hyi, piecePoint]

include hB_disjoint hB_cover in
lemma glueDist_subtype_ne {i j : I} (hij : i ≠ j) (x : B i) (y : B j) :
    glueDist B hB_cover p e (x : X) (y : X) =
      @dist (B i) (e i).toPseudoMetricSpace.toDist x (p i) +
        dist (p i : X) (p j : X) +
          @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) y := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  have hxi := pieceIndex_eq_of_mem (B := B) hB_disjoint hB_cover hx
  have hyj := pieceIndex_eq_of_mem (B := B) hB_disjoint hB_cover hy
  have hidx : pieceIndex B hB_cover x ≠ pieceIndex B hB_cover y := by
    simpa [hxi, hyj] using hij
  unfold glueDist
  rw [dif_neg hidx]
  simp only [piecePoint]
  rw [glueDist_left_congr (p := p) (e := e) hxi (mem_piece B hB_cover x)]
  rw [glueDist_right_congr (p := p) (e := e) hyj (mem_piece B hB_cover y)]
  rw [glueDist_base_congr (B := B) (p := p) hxi hyj]

end MetricAmalgamation

/- accepted add_to_file helper 3 -/
namespace MetricAmalgamation

variable {X : Type*} {I : Type*} [MetricSpace X]
variable {B : I → Set X}
variable {hB_disjoint : (Set.univ : Set I).PairwiseDisjoint B}
variable {hB_cover : (⋃ i, B i) = Set.univ}
variable {p : ∀ i, B i}
variable {e : ∀ i, MetricSpace (B i)}

include hB_disjoint hB_cover in
lemma glueDist_comm (x y : X) :
    glueDist B hB_cover p e x y = glueDist B hB_cover p e y x := by
  set i := pieceIndex B hB_cover x
  set j := pieceIndex B hB_cover y
  by_cases hij : i = j
  · let xb : B i := piecePoint B hB_cover x
    let yb : B i := ⟨y, by
      have hyj := mem_piece B hB_cover y
      change y ∈ B j at hyj
      simpa [hij] using hyj⟩
    have hxy0 := glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
      (hB_cover := hB_cover) (p := p) (e := e) i xb yb
    have hyx0 := glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
      (hB_cover := hB_cover) (p := p) (e := e) i yb xb
    have hxy : glueDist B hB_cover p e x y =
        @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb := by
      simpa [xb, yb, piecePoint] using hxy0
    have hyx : glueDist B hB_cover p e y x =
        @dist (B i) (e i).toPseudoMetricSpace.toDist yb xb := by
      simpa [xb, yb, piecePoint] using hyx0
    rw [hxy, hyx]
    exact @dist_comm (B i) (e i).toPseudoMetricSpace xb yb
  · let xb : B i := piecePoint B hB_cover x
    let yb : B j := piecePoint B hB_cover y
    have hxy0 := glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
      (hB_cover := hB_cover) (p := p) (e := e) hij xb yb
    have hyx0 := glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
      (hB_cover := hB_cover) (p := p) (e := e) (Ne.symm hij) yb xb
    have hxy : glueDist B hB_cover p e x y =
        @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
          dist (p i : X) (p j : X) +
            @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
      simpa [xb, yb, piecePoint] using hxy0
    have hyx : glueDist B hB_cover p e y x =
        @dist (B j) (e j).toPseudoMetricSpace.toDist yb (p j) +
          dist (p j : X) (p i : X) +
            @dist (B i) (e i).toPseudoMetricSpace.toDist (p i) xb := by
      simpa [xb, yb, piecePoint] using hyx0
    rw [hxy, hyx]
    rw [@dist_comm (B i) (e i).toPseudoMetricSpace xb (p i)]
    rw [dist_comm (p i : X) (p j : X)]
    rw [@dist_comm (B j) (e j).toPseudoMetricSpace (p j) yb]
    ring

include hB_disjoint hB_cover in
lemma glueDist_triangle (x y z : X) :
    glueDist B hB_cover p e x z ≤
      glueDist B hB_cover p e x y + glueDist B hB_cover p e y z := by
  set i := pieceIndex B hB_cover x
  set j := pieceIndex B hB_cover y
  set k := pieceIndex B hB_cover z
  let xb : B i := piecePoint B hB_cover x
  let yb : B j := piecePoint B hB_cover y
  let zb : B k := piecePoint B hB_cover z
  by_cases hik : i = k
  · let zb_i : B i := ⟨z, by
      have hz := mem_piece B hB_cover z
      change z ∈ B k at hz
      simpa [hik] using hz⟩
    by_cases hij : i = j
    · let yb_i : B i := ⟨y, by
        have hy := mem_piece B hB_cover y
        change y ∈ B j at hy
        simpa [hij] using hy⟩
      have hxz : glueDist B hB_cover p e x z =
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb zb_i := by
        simpa [xb, zb_i, piecePoint] using
          glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) i xb zb_i
      have hxy : glueDist B hB_cover p e x y =
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb_i := by
        simpa [xb, yb_i, piecePoint] using
          glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) i xb yb_i
      have hyz : glueDist B hB_cover p e y z =
          @dist (B i) (e i).toPseudoMetricSpace.toDist yb_i zb_i := by
        simpa [yb_i, zb_i, piecePoint] using
          glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) i yb_i zb_i
      rw [hxz, hxy, hyz]
      exact @dist_triangle (B i) (e i).toPseudoMetricSpace xb yb_i zb_i
    · have hxy : glueDist B hB_cover p e x y =
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
            dist (p i : X) (p j : X) +
              @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
        simpa [xb, yb, piecePoint] using
          glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) hij xb yb
      have hyz : glueDist B hB_cover p e y z =
          @dist (B j) (e j).toPseudoMetricSpace.toDist yb (p j) +
            dist (p j : X) (p i : X) +
              @dist (B i) (e i).toPseudoMetricSpace.toDist (p i) zb_i := by
        simpa [yb, zb_i, piecePoint] using
          glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) (Ne.symm hij) yb zb_i
      have hxz : glueDist B hB_cover p e x z =
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb zb_i := by
        simpa [xb, zb_i, piecePoint] using
          glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) i xb zb_i
      rw [hxz, hxy, hyz]
      have htri : @dist (B i) (e i).toPseudoMetricSpace.toDist xb zb_i ≤
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
            @dist (B i) (e i).toPseudoMetricSpace.toDist (p i) zb_i :=
        @dist_triangle (B i) (e i).toPseudoMetricSpace xb (p i) zb_i
      have h₁ : 0 ≤ dist (p i : X) (p j : X) := dist_nonneg
      have h₂ : 0 ≤ @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb :=
        @dist_nonneg (B j) (e j).toPseudoMetricSpace (p j) yb
      have h₃ : 0 ≤ @dist (B j) (e j).toPseudoMetricSpace.toDist yb (p j) :=
        @dist_nonneg (B j) (e j).toPseudoMetricSpace yb (p j)
      have h₄ : 0 ≤ dist (p j : X) (p i : X) := dist_nonneg
      nlinarith
  · by_cases hij : i = j
    · let yb_i : B i := ⟨y, by
        have hy := mem_piece B hB_cover y
        change y ∈ B j at hy
        simpa [hij] using hy⟩
      have hxz : glueDist B hB_cover p e x z =
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
            dist (p i : X) (p k : X) +
              @dist (B k) (e k).toPseudoMetricSpace.toDist (p k) zb := by
        simpa [xb, zb, piecePoint] using
          glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) hik xb zb
      have hxy : glueDist B hB_cover p e x y =
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb_i := by
        simpa [xb, yb_i, piecePoint] using
          glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) i xb yb_i
      have hyz : glueDist B hB_cover p e y z =
          @dist (B i) (e i).toPseudoMetricSpace.toDist yb_i (p i) +
            dist (p i : X) (p k : X) +
              @dist (B k) (e k).toPseudoMetricSpace.toDist (p k) zb := by
        simpa [yb_i, zb, piecePoint] using
          glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) hik yb_i zb
      rw [hxz, hxy, hyz]
      have htri : @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) ≤
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb_i +
            @dist (B i) (e i).toPseudoMetricSpace.toDist yb_i (p i) :=
        @dist_triangle (B i) (e i).toPseudoMetricSpace xb yb_i (p i)
      nlinarith
    · by_cases hjk : j = k
      · let zb_j : B j := ⟨z, by
          have hz := mem_piece B hB_cover z
          change z ∈ B k at hz
          simpa [hjk] using hz⟩
        have hxz : glueDist B hB_cover p e x z =
            @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
              dist (p i : X) (p j : X) +
                @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) zb_j := by
          have hij' : i ≠ j := by
            intro h
            exact hik (h.trans hjk)
          simpa [xb, zb_j, piecePoint] using
            glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
              (hB_cover := hB_cover) (p := p) (e := e) hij' xb zb_j
        have hxy : glueDist B hB_cover p e x y =
            @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
              dist (p i : X) (p j : X) +
                @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
          simpa [xb, yb, piecePoint] using
            glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
              (hB_cover := hB_cover) (p := p) (e := e) hij xb yb
        have hyz : glueDist B hB_cover p e y z =
            @dist (B j) (e j).toPseudoMetricSpace.toDist yb zb_j := by
          simpa [yb, zb_j, piecePoint] using
            glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
              (hB_cover := hB_cover) (p := p) (e := e) j yb zb_j
        rw [hxz, hxy, hyz]
        have htri : @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) zb_j ≤
            @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb +
              @dist (B j) (e j).toPseudoMetricSpace.toDist yb zb_j :=
          @dist_triangle (B j) (e j).toPseudoMetricSpace (p j) yb zb_j
        nlinarith
      · have hxz : glueDist B hB_cover p e x z =
            @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
              dist (p i : X) (p k : X) +
                @dist (B k) (e k).toPseudoMetricSpace.toDist (p k) zb := by
          simpa [xb, zb, piecePoint] using
            glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
              (hB_cover := hB_cover) (p := p) (e := e) hik xb zb
        have hxy : glueDist B hB_cover p e x y =
            @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
              dist (p i : X) (p j : X) +
                @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
          simpa [xb, yb, piecePoint] using
            glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
              (hB_cover := hB_cover) (p := p) (e := e) hij xb yb
        have hyz : glueDist B hB_cover p e y z =
            @dist (B j) (e j).toPseudoMetricSpace.toDist yb (p j) +
              dist (p j : X) (p k : X) +
                @dist (B k) (e k).toPseudoMetricSpace.toDist (p k) zb := by
          simpa [yb, zb, piecePoint] using
            glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
              (hB_cover := hB_cover) (p := p) (e := e) hjk yb zb
        rw [hxz, hxy, hyz]
        have hbase : dist (p i : X) (p k : X) ≤
            dist (p i : X) (p j : X) + dist (p j : X) (p k : X) :=
          dist_triangle (p i : X) (p j : X) (p k : X)
        have h₁ : 0 ≤ @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb :=
          @dist_nonneg (B j) (e j).toPseudoMetricSpace (p j) yb
        have h₂ : 0 ≤ @dist (B j) (e j).toPseudoMetricSpace.toDist yb (p j) :=
          @dist_nonneg (B j) (e j).toPseudoMetricSpace yb (p j)
        nlinarith

end MetricAmalgamation

/- accepted add_to_file helper 4 -/
namespace MetricAmalgamation

variable {X : Type*} {I : Type*} [MetricSpace X]
variable {B : I → Set X}
variable {hB_disjoint : (Set.univ : Set I).PairwiseDisjoint B}
variable {hB_cover : (⋃ i, B i) = Set.univ}
variable {p : ∀ i, B i}
variable {e : ∀ i, MetricSpace (B i)}

lemma glueDist_self (x : X) : glueDist B hB_cover p e x x = 0 := by
  simp [glueDist, piecePoint]

include hB_disjoint hB_cover in
lemma eq_of_glueDist_eq_zero {x y : X}
    (h : glueDist B hB_cover p e x y = 0) : x = y := by
  set i := pieceIndex B hB_cover x
  set j := pieceIndex B hB_cover y
  by_cases hij : i = j
  · let xb : B i := piecePoint B hB_cover x
    let yb : B i := ⟨y, by
      have hyj := mem_piece B hB_cover y
      change y ∈ B j at hyj
      simpa [hij] using hyj⟩
    have hxy : glueDist B hB_cover p e x y =
        @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb := by
      simpa [xb, yb, piecePoint] using
        glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
          (hB_cover := hB_cover) (p := p) (e := e) i xb yb
    rw [hxy] at h
    have hsub : xb = yb := @eq_of_dist_eq_zero (B i) (e i) xb yb h
    have hval : (xb : X) = (yb : X) := congrArg Subtype.val hsub
    simpa [xb, yb, piecePoint] using hval
  · let xb : B i := piecePoint B hB_cover x
    let yb : B j := piecePoint B hB_cover y
    have hxy : glueDist B hB_cover p e x y =
        @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
          dist (p i : X) (p j : X) +
            @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
      simpa [xb, yb, piecePoint] using
        glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
          (hB_cover := hB_cover) (p := p) (e := e) hij xb yb
    rw [hxy] at h
    have ha : 0 ≤ @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) :=
      @dist_nonneg (B i) (e i).toPseudoMetricSpace xb (p i)
    have hb : 0 ≤ @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb :=
      @dist_nonneg (B j) (e j).toPseudoMetricSpace (p j) yb
    have hc0 : dist (p i : X) (p j : X) ≤ 0 := by
      have hc : dist (p i : X) (p j : X) ≤
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
            dist (p i : X) (p j : X) +
              @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
        nlinarith
      rwa [h] at hc
    have hc : dist (p i : X) (p j : X) = 0 := le_antisymm hc0 dist_nonneg
    have hp : (p i : X) = (p j : X) := eq_of_dist_eq_zero hc
    have hd : Disjoint (B i) (B j) :=
      hB_disjoint (Set.mem_univ i) (Set.mem_univ j) hij
    exact False.elim
      (Set.disjoint_iff_forall_ne.mp hd (p i).property (p j).property hp)

end MetricAmalgamation

/- accepted add_to_file helper 5 -/
namespace MetricAmalgamation

variable {X : Type*} {I : Type*} [MetricSpace X]
variable {B : I → Set X}
variable {hB_disjoint : (Set.univ : Set I).PairwiseDisjoint B}
variable {hB_clopen : ∀ i, IsClopen (B i)}
variable {hB_cover : (⋃ i, B i) = Set.univ}
variable {p : ∀ i, B i}
variable {e : ∀ i, MetricSpace (B i)}
variable {he_top : ∀ i,
  (e i).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
    (inferInstance : TopologicalSpace (B i))}

include hB_disjoint hB_clopen hB_cover he_top in
lemma glueDist_topology (s : Set X) :
    IsOpen s ↔ ∀ x ∈ s, ∃ δ > 0, ∀ y,
      glueDist B hB_cover p e x y < δ → y ∈ s := by
  constructor
  · intro hs x hxs
    set i := pieceIndex B hB_cover x
    let xb : B i := piecePoint B hB_cover x
    let t : Set (B i) := Subtype.val ⁻¹' s
    have ht_old : IsOpen t := continuous_subtype_val.isOpen_preimage s hs
    have ht_e : @IsOpen (B i)
        (e i).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace t := by
      rw [he_top i]
      exact ht_old
    have hx_t : xb ∈ t := by
      change (xb : X) ∈ s
      simpa [xb, piecePoint] using hxs
    rcases (@Metric.isOpen_iff (B i) (e i).toPseudoMetricSpace t).mp ht_e xb hx_t with
      ⟨r, hr, hball⟩
    have hBi : IsOpen (B i) := (hB_clopen i).isOpen
    rcases Metric.isOpen_iff.mp hBi (p i : X) (p i).property with ⟨η, hη, hηsub⟩
    refine ⟨min r η, lt_min hr hη, ?_⟩
    intro y hyD
    set j := pieceIndex B hB_cover y
    let yb : B j := piecePoint B hB_cover y
    by_cases hij : i = j
    · let yb_i : B i := ⟨y, by
        have hyj := mem_piece B hB_cover y
        change y ∈ B j at hyj
        simpa [hij] using hyj⟩
      have hD : glueDist B hB_cover p e x y =
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb_i := by
        simpa [xb, yb_i, piecePoint] using
          glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) i xb yb_i
      have her : @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb_i < r := by
        rw [← hD]
        exact lt_of_lt_of_le hyD (min_le_left r η)
      have her' : @dist (B i) (e i).toPseudoMetricSpace.toDist yb_i xb < r := by
        rw [@dist_comm (B i) (e i).toPseudoMetricSpace yb_i xb]
        exact her
      have hyt : yb_i ∈ t := hball
        ((@Metric.mem_ball (B i) (e i).toPseudoMetricSpace xb yb_i r).mpr her')
      change (yb_i : X) ∈ s at hyt
      simpa [yb_i] using hyt
    · have hD : glueDist B hB_cover p e x y =
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
            dist (p i : X) (p j : X) +
              @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
        simpa [xb, yb, piecePoint] using
          glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) hij xb yb
      have ha : 0 ≤ @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) :=
        @dist_nonneg (B i) (e i).toPseudoMetricSpace xb (p i)
      have hb : 0 ≤ @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb :=
        @dist_nonneg (B j) (e j).toPseudoMetricSpace (p j) yb
      have hbase : dist (p i : X) (p j : X) < η := by
        have hle : dist (p i : X) (p j : X) ≤ glueDist B hB_cover p e x y := by
          rw [hD]
          nlinarith
        exact lt_of_le_of_lt hle (lt_of_lt_of_le hyD (min_le_right r η))
      have hbase' : dist (p j : X) (p i : X) < η := by
        rw [dist_comm]
        exact hbase
      have hpji : (p j : X) ∈ B i := hηsub (Metric.mem_ball.mpr hbase')
      have hd : Disjoint (B i) (B j) :=
        hB_disjoint (Set.mem_univ i) (Set.mem_univ j) hij
      exact False.elim
        (Set.disjoint_iff_forall_ne.mp hd hpji (p j).property rfl)
  · intro h
    rw [Metric.isOpen_iff]
    intro x hxs
    rcases h x hxs with ⟨δ, hδ, hδsub⟩
    set i := pieceIndex B hB_cover x
    let xb : B i := piecePoint B hB_cover x
    let t : Set (B i) := @Metric.ball (B i) (e i).toPseudoMetricSpace xb δ
    have ht_e : @IsOpen (B i)
        (e i).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace t := by
      exact @Metric.isOpen_ball (B i) (e i).toPseudoMetricSpace xb δ
    rw [he_top i] at ht_e
    rcases isOpen_induced_iff.mp ht_e with ⟨u, hu, hu_eq⟩
    have hx_dist : @dist (B i) (e i).toPseudoMetricSpace.toDist xb xb < δ := by
      rw [@dist_self (B i) (e i).toPseudoMetricSpace xb]
      exact hδ
    have hx_t : xb ∈ t :=
      (@Metric.mem_ball (B i) (e i).toPseudoMetricSpace xb xb δ).mpr hx_dist
    have hxu : (xb : X) ∈ u := by
      have : xb ∈ Subtype.val ⁻¹' u := by
        rw [hu_eq]
        exact hx_t
      exact this
    rcases Metric.isOpen_iff.mp hu (xb : X) hxu with ⟨ru, hru, hrusub⟩
    have hBi : IsOpen (B i) := (hB_clopen i).isOpen
    have hxBi : (xb : X) ∈ B i := by
      simpa [xb, piecePoint] using mem_piece B hB_cover x
    rcases Metric.isOpen_iff.mp hBi (xb : X) hxBi with ⟨rB, hrB, hrBsub⟩
    refine ⟨min ru rB, lt_min hru hrB, ?_⟩
    intro y hy
    have hyu : y ∈ u := hrusub (Metric.mem_ball.mpr
      (lt_of_lt_of_le hy (min_le_left ru rB)))
    have hyBi : y ∈ B i := hrBsub (Metric.mem_ball.mpr
      (lt_of_lt_of_le hy (min_le_right ru rB)))
    let yb : B i := ⟨y, hyBi⟩
    have hyt : yb ∈ t := by
      have : yb ∈ Subtype.val ⁻¹' u := hyu
      rwa [hu_eq] at this
    have helt : @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb < δ := by
      have hd : @dist (B i) (e i).toPseudoMetricSpace.toDist yb xb < δ :=
        (@Metric.mem_ball (B i) (e i).toPseudoMetricSpace xb yb δ).mp hyt
      rw [@dist_comm (B i) (e i).toPseudoMetricSpace yb xb] at hd
      exact hd
    have hD : glueDist B hB_cover p e x y =
        @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb := by
      simpa [xb, yb, piecePoint] using
        glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
          (hB_cover := hB_cover) (p := p) (e := e) i xb yb
    apply hδsub y
    rw [hD]
    exact helt

end MetricAmalgamation

/- accepted add_to_file helper 6 -/
namespace MetricAmalgamation

variable {X : Type*} {I : Type*} [MetricSpace X]
variable {B : I → Set X}
variable {hB_disjoint : (Set.univ : Set I).PairwiseDisjoint B}
variable {hB_clopen : ∀ i, IsClopen (B i)}
variable {hB_cover : (⋃ i, B i) = Set.univ}
variable {p : ∀ i, B i}
variable {e : ∀ i, MetricSpace (B i)}
variable {he_top : ∀ i,
  (e i).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
    (inferInstance : TopologicalSpace (B i))}

include hB_disjoint hB_clopen hB_cover he_top in
@[implicit_reducible] noncomputable def glueMetricSpace : MetricSpace X :=
  MetricSpace.ofDistTopology (glueDist B hB_cover p e)
    (glueDist_self (B := B) (hB_cover := hB_cover) (p := p) (e := e))
    (glueDist_comm (B := B) (hB_disjoint := hB_disjoint) (hB_cover := hB_cover)
      (p := p) (e := e))
    (glueDist_triangle (B := B) (hB_disjoint := hB_disjoint) (hB_cover := hB_cover)
      (p := p) (e := e))
    (glueDist_topology (B := B) (hB_disjoint := hB_disjoint)
      (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
      (he_top := he_top))
    (fun x y h => eq_of_glueDist_eq_zero (B := B) (hB_disjoint := hB_disjoint)
      (hB_cover := hB_cover) (p := p) (e := e) h)

include hB_disjoint hB_clopen hB_cover he_top in
lemma dist_glueMetricSpace (x y : X) :
    @dist X (glueMetricSpace (B := B) (hB_disjoint := hB_disjoint)
      (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
      (he_top := he_top)).toPseudoMetricSpace.toDist x y =
      glueDist B hB_cover p e x y :=
  rfl

include hB_disjoint hB_clopen hB_cover he_top in
lemma glueMetricSpace_topology :
    (glueMetricSpace (B := B) (hB_disjoint := hB_disjoint)
      (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
      (he_top := he_top)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace X) :=
  rfl

end MetricAmalgamation

/- accepted add_to_file helper 7 -/
namespace MetricAmalgamation

lemma dist_le_of_ediam_le_ofReal {α : Type*} [PseudoMetricSpace α]
    {s : Set α} {ε : ℝ} (hε : 0 ≤ ε)
    (hs : Metric.ediam s ≤ ENNReal.ofReal ε)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) : dist x y ≤ ε := by
  have hed : edist x y ≤ Metric.ediam s := Metric.edist_le_ediam_of_mem hx hy
  have hof : ENNReal.ofReal (dist x y) ≤ ENNReal.ofReal ε := by
    rw [← edist_dist]
    exact hed.trans hs
  exact (ENNReal.ofReal_le_ofReal_iff hε).mp hof

end MetricAmalgamation

/- accepted add_to_file helper 8 -/
namespace MetricAmalgamation

lemma dist_le_of_ediam_le_ofReal_explicit {α : Type*} (m : PseudoMetricSpace α)
    {s : Set α} {ε : ℝ} (hε : 0 ≤ ε)
    (hs : @Metric.ediam α m.toPseudoEMetricSpace s ≤ ENNReal.ofReal ε)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
    @dist α m.toDist x y ≤ ε := by
  have hed : @edist α m.toPseudoEMetricSpace.toEDist x y ≤
      @Metric.ediam α m.toPseudoEMetricSpace s :=
    @Metric.edist_le_ediam_of_mem α s x y m.toPseudoEMetricSpace hx hy
  have hof : ENNReal.ofReal (@dist α m.toDist x y) ≤ ENNReal.ofReal ε := by
    rw [← @edist_dist α m x y]
    exact hed.trans hs
  exact (ENNReal.ofReal_le_ofReal_iff hε).mp hof

end MetricAmalgamation

/- accepted add_to_file helper 9 -/
namespace MetricAmalgamation

variable {X : Type*} {I : Type*} [MetricSpace X]
variable {B : I → Set X}
variable {hB_disjoint : (Set.univ : Set I).PairwiseDisjoint B}
variable {hB_clopen : ∀ i, IsClopen (B i)}
variable {hB_cover : (⋃ i, B i) = Set.univ}
variable {p : ∀ i, B i}
variable {e : ∀ i, MetricSpace (B i)}
variable {he_top : ∀ i,
  (e i).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
    (inferInstance : TopologicalSpace (B i))}

include hB_disjoint hB_clopen hB_cover he_top in
lemma dist_glueMetricSpace_error_le (ε : ℝ) (hε : 0 ≤ ε)
    (hdiam : ∀ i, Metric.ediam (B i) ≤ ENNReal.ofReal ε)
    (hediam : ∀ i,
      @Metric.ediam (B i) (e i).toPseudoMetricSpace.toPseudoEMetricSpace
        Set.univ ≤ ENNReal.ofReal ε)
    (x y : X) :
    |@dist X (glueMetricSpace (B := B) (hB_disjoint := hB_disjoint)
      (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
      (he_top := he_top)).toPseudoMetricSpace.toDist x y - dist x y| ≤
        4 * ε := by
  set i := pieceIndex B hB_cover x
  set j := pieceIndex B hB_cover y
  let xb : B i := piecePoint B hB_cover x
  let yb : B j := piecePoint B hB_cover y
  have hD0 : @dist X (glueMetricSpace (B := B) (hB_disjoint := hB_disjoint)
      (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
      (he_top := he_top)).toPseudoMetricSpace.toDist x y =
      glueDist B hB_cover p e x y :=
    dist_glueMetricSpace (B := B) (hB_disjoint := hB_disjoint)
      (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
      (he_top := he_top) x y
  by_cases hij : i = j
  · let yb_i : B i := ⟨y, by
      have hyj := mem_piece B hB_cover y
      change y ∈ B j at hyj
      simpa [hij] using hyj⟩
    have hD : @dist X (glueMetricSpace (B := B) (hB_disjoint := hB_disjoint)
        (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
        (he_top := he_top)).toPseudoMetricSpace.toDist x y =
        @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb_i := by
      rw [hD0]
      simpa [xb, yb_i, piecePoint] using
        glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
          (hB_cover := hB_cover) (p := p) (e := e) i xb yb_i
    rw [hD]
    have hdxy : dist x y ≤ ε := by
      exact dist_le_of_ediam_le_ofReal (s := B i) hε (hdiam i)
        (by simpa [xb, piecePoint] using mem_piece B hB_cover x)
        (by simpa [yb_i] using yb_i.property)
    have hexy : @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb_i ≤ ε := by
      exact dist_le_of_ediam_le_ofReal_explicit (e i).toPseudoMetricSpace
        (s := Set.univ) hε (hediam i) (Set.mem_univ xb) (Set.mem_univ yb_i)
    have hd0 : 0 ≤ dist x y := dist_nonneg
    have he0 : 0 ≤ @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb_i :=
      @dist_nonneg (B i) (e i).toPseudoMetricSpace xb yb_i
    rw [abs_sub_le_iff]
    constructor <;> nlinarith
  · have hD : @dist X (glueMetricSpace (B := B) (hB_disjoint := hB_disjoint)
        (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
        (he_top := he_top)).toPseudoMetricSpace.toDist x y =
        @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
          dist (p i : X) (p j : X) +
            @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
      rw [hD0]
      simpa [xb, yb, piecePoint] using
        glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
          (hB_cover := hB_cover) (p := p) (e := e) hij xb yb
    rw [hD]
    have hd_xp : dist x (p i : X) ≤ ε :=
      dist_le_of_ediam_le_ofReal (s := B i) hε (hdiam i)
        (by simpa [xb, piecePoint] using mem_piece B hB_cover x) (p i).property
    have hd_py : dist (p j : X) y ≤ ε :=
      dist_le_of_ediam_le_ofReal (s := B j) hε (hdiam j)
        (p j).property (by simpa [yb, piecePoint] using mem_piece B hB_cover y)
    have he_xp : @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) ≤ ε :=
      dist_le_of_ediam_le_ofReal_explicit (e i).toPseudoMetricSpace
        (s := Set.univ) hε (hediam i) (Set.mem_univ xb) (Set.mem_univ (p i))
    have he_py : @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb ≤ ε :=
      dist_le_of_ediam_le_ofReal_explicit (e j).toPseudoMetricSpace
        (s := Set.univ) hε (hediam j) (Set.mem_univ (p j)) (Set.mem_univ yb)
    have hupper : @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
        dist (p i : X) (p j : X) +
          @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb -
            dist x y ≤ 4 * ε := by
      have hc : dist (p i : X) (p j : X) ≤
          dist (p i : X) x + dist x y + dist y (p j : X) := by
        calc
          dist (p i : X) (p j : X) ≤ dist (p i : X) x + dist x (p j : X) :=
            dist_triangle _ _ _
          _ ≤ (dist (p i : X) x + dist x y) + dist y (p j : X) := by
            have := dist_triangle x y (p j : X)
            nlinarith
      have hxpi : dist (p i : X) x ≤ ε := by simpa [dist_comm] using hd_xp
      have hypj : dist y (p j : X) ≤ ε := by simpa [dist_comm] using hd_py
      nlinarith
    have hlower : dist x y -
        (@dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
          dist (p i : X) (p j : X) +
            @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb) ≤
          4 * ε := by
      have hd : dist x y ≤
          dist x (p i : X) + dist (p i : X) (p j : X) + dist (p j : X) y := by
        calc
          dist x y ≤ dist x (p i : X) + dist (p i : X) y := dist_triangle _ _ _
          _ ≤ dist x (p i : X) +
              (dist (p i : X) (p j : X) + dist (p j : X) y) := by
            have := dist_triangle (p i : X) (p j : X) y
            nlinarith
          _ = dist x (p i : X) + dist (p i : X) (p j : X) +
              dist (p j : X) y := by ring
      have hc_nonneg : dist (p i : X) (p j : X) ≤
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
            dist (p i : X) (p j : X) +
              @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
        have h1 := @dist_nonneg (B i) (e i).toPseudoMetricSpace xb (p i)
        have h2 := @dist_nonneg (B j) (e j).toPseudoMetricSpace (p j) yb
        nlinarith
      nlinarith
    exact abs_sub_le_iff.mpr ⟨hupper, hlower⟩

end MetricAmalgamation

/- verified submission -/
theorem metric_amalgamation
    {X : Type*} {I : Type*} [MetricSpace X]
    (B : I → Set X)
    (hB_disjoint : (Set.univ : Set I).PairwiseDisjoint B)
    (hB_clopen : ∀ i, IsClopen (B i))
    (hB_cover : (⋃ i, B i) = Set.univ)
    (p : ∀ i, B i)
    (e : ∀ i, MetricSpace (B i))
    (he_top : ∀ i,
      (e i).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace (B i))) :
    ∃ mD : MetricSpace X,
      (∀ (i : I) (x y : B i),
        @dist X mD.toPseudoMetricSpace.toDist x y =
          @dist (B i) (e i).toPseudoMetricSpace.toDist x y) ∧
      (∀ (i j : I), i ≠ j → ∀ (x : B i) (y : B j),
        @dist X mD.toPseudoMetricSpace.toDist x y =
          @dist (B i) (e i).toPseudoMetricSpace.toDist x (p i) +
            dist (p i : X) (p j : X) +
              @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) y) ∧
      mD.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace X) ∧
      ∀ ε : ℝ, 0 ≤ ε →
        ((∀ i, Metric.ediam (B i) ≤ ENNReal.ofReal ε) ∧
          (∀ i, @Metric.ediam (B i)
            (e i).toPseudoMetricSpace.toPseudoEMetricSpace Set.univ ≤
              ENNReal.ofReal ε)) →
        sSup (Set.range (fun q : X × X =>
          |@dist X mD.toPseudoMetricSpace.toDist q.1 q.2 - dist q.1 q.2|)) ≤
            4 * ε := by
  classical
  refine ⟨MetricAmalgamation.glueMetricSpace (B := B) (hB_disjoint := hB_disjoint)
    (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
    (he_top := he_top), ?_, ?_, ?_, ?_⟩
  · intro i x y
    exact (MetricAmalgamation.dist_glueMetricSpace (B := B)
      (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
      (hB_cover := hB_cover) (p := p) (e := e) (he_top := he_top) x y).trans
      (MetricAmalgamation.glueDist_subtype_same (B := B)
        (hB_disjoint := hB_disjoint) (hB_cover := hB_cover) (p := p) (e := e) i x y)
  · intro i j hij x y
    have hmain := (MetricAmalgamation.dist_glueMetricSpace (B := B)
      (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
      (hB_cover := hB_cover) (p := p) (e := e) (he_top := he_top) x y).trans
      (MetricAmalgamation.glueDist_subtype_ne (B := B)
        (hB_disjoint := hB_disjoint) (hB_cover := hB_cover) (p := p) (e := e)
        hij x y)
    have hpp0 := (MetricAmalgamation.dist_glueMetricSpace (B := B)
      (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
      (hB_cover := hB_cover) (p := p) (e := e) (he_top := he_top)
      (p i) (p j)).trans
      (MetricAmalgamation.glueDist_subtype_ne (B := B)
        (hB_disjoint := hB_disjoint) (hB_cover := hB_cover) (p := p) (e := e)
        hij (p i) (p j))
    have hpp : @dist X (MetricAmalgamation.glueMetricSpace (B := B)
        (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
        (hB_cover := hB_cover) (p := p) (e := e)
        (he_top := he_top)).toPseudoMetricSpace.toDist (p i : X) (p j : X) =
        dist (p i : X) (p j : X) := by
      calc
        @dist X (MetricAmalgamation.glueMetricSpace (B := B)
          (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
          (hB_cover := hB_cover) (p := p) (e := e)
          (he_top := he_top)).toPseudoMetricSpace.toDist (p i : X) (p j : X)
            = @dist (B i) (e i).toPseudoMetricSpace.toDist (p i) (p i) +
              dist (p i : X) (p j : X) +
                @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) (p j) := hpp0
        _ = dist (p i : X) (p j : X) := by
          rw [@dist_self (B i) (e i).toPseudoMetricSpace (p i)]
          rw [@dist_self (B j) (e j).toPseudoMetricSpace (p j)]
          ring
    calc
      @dist X (MetricAmalgamation.glueMetricSpace (B := B)
        (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
        (hB_cover := hB_cover) (p := p) (e := e)
        (he_top := he_top)).toPseudoMetricSpace.toDist x y
          = @dist (B i) (e i).toPseudoMetricSpace.toDist x (p i) +
            dist (p i : X) (p j : X) +
              @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) y := hmain
      _ = @dist (B i) (e i).toPseudoMetricSpace.toDist x (p i) +
          @dist X (MetricAmalgamation.glueMetricSpace (B := B)
            (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
            (hB_cover := hB_cover) (p := p) (e := e)
            (he_top := he_top)).toPseudoMetricSpace.toDist (p i : X) (p j : X) +
          @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) y := by
        rw [hpp]
  · exact MetricAmalgamation.glueMetricSpace_topology (B := B)
      (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
      (hB_cover := hB_cover) (p := p) (e := e) (he_top := he_top)
  · intro ε hε hdiam
    let mD : MetricSpace X := MetricAmalgamation.glueMetricSpace (B := B)
      (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
      (hB_cover := hB_cover) (p := p) (e := e) (he_top := he_top)
    change sSup (Set.range (fun q : X × X =>
      |@dist X mD.toPseudoMetricSpace.toDist q.1 q.2 -
        @dist X mD.toPseudoMetricSpace.toDist q.1 q.2|)) ≤ 4 * ε
    by_cases hX : Nonempty X
    · rcases hX with ⟨x⟩
      apply csSup_le
      · exact ⟨|@dist X mD.toPseudoMetricSpace.toDist x x -
          @dist X mD.toPseudoMetricSpace.toDist x x|, ⟨(x, x), rfl⟩⟩
      · intro b hb
        rcases hb with ⟨q, rfl⟩
        simp
        nlinarith
    · haveI : IsEmpty X := not_nonempty_iff.mp hX
      haveI : IsEmpty (X × X) := inferInstance
      rw [Set.range_eq_empty, Real.sSup_empty]
      nlinarith

end Rollout_p2075_metric_amalgamation

#check_dependency_graph "Rollout_p2075_metric_amalgamation.metric_amalgamation" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∃ mD, (∀ (i : I) (x y : ↑(B i)), dist ↑x ↑y = dist x y) ∧ (∀ (i j : I), i ≠ j → ∀ (x : ↑(B i)) (y : ↑(B j)), dist ↑x ↑y = dist x (p i) + dist ↑(p i) ↑(p j) + dist (p j) y) ∧ PseudoMetricSpace.toUniformSpace.toTopologicalSpace = inferInstance ∧ ∀ (ε : ℝ), 0 ≤ ε → ((∀ (i : I), Metric.ediam (B i) ≤ ENNReal.ofReal ε) ∧ ∀ (i : I), Metric.ediam Set.univ ≤ ENNReal.ofReal ε) → sSup (Set.range fun q => |dist q.1 q.2 - dist q.1 q.2|) ≤ 4 * ε\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hB_disjoint\",\"statement\":\"Set.univ.PairwiseDisjoint B\"},{\"name\":\"hB_clopen\",\"statement\":\"∀ (i : I), IsClopen (B i)\"},{\"name\":\"hB_cover\",\"statement\":\"⋃ i, B i = Set.univ\"},{\"name\":\"he_top\",\"statement\":\"∀ (i : I), PseudoMetricSpace.toUniformSpace.toTopologicalSpace = inferInstance\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2075_metric_amalgamation\",\"reconstructedProofSha256\":\"c109aa5b848ea59227c5b9bee20b75edfcfb1d49357164096500dd0cefcf365d\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p2075_metric_amalgamation.metric_amalgamation\",\"topologySha256\":\"deb664ff2993b355db8b0a33e35ab9f9f0aae3ff5569326fe1891b0dcff1b2ed\"}"

namespace Rollout_p2109_stable_equivalence_empty_subfield_points_i

-- graph_id: p2109_stable_equivalence_empty_subfield_points_i
-- topology_sha256: 83c1f3429a819d27d51092c231154faa95c7febde4ce81a49b36cda28c209492
/- accepted add_to_file helper 1 -/
lemma scalar_tower_subfield_real (A : Subfield ℝ) : IsScalarTower A ℝ ℝ :=
  Subfield.instIsScalarTowerSubtypeMem (K := ℝ) (X := ℝ) (Y := ℝ) A

noncomputable abbrev subfieldTensorPiEquiv (A : Subfield ℝ) (d : ℕ) :
    TensorProduct A ℝ (Fin d → A) ≃ₗ[ℝ] Fin d → ℝ :=
  @TensorProduct.piScalarRight A _ ℝ _ _ ℝ _ _ _ (scalar_tower_subfield_real A) (Fin d) _ _

noncomputable def subfieldLiftLinearMap {d s : ℕ} (A : Subfield ℝ)
    (b : Fin s → Fin d → A) : (Fin d → ℝ) →ₗ[ℝ] Fin s → ℝ where
  toFun x := fun i => ∑ j : Fin d, ((b i j : A) : ℝ) * x j
  map_add' x y := by
    ext i
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' c x := by
    ext i
    dsimp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_left_comm ((b i j : A) : ℝ) c (x j)

lemma subfieldTensorPiEquiv_lTensor {d s : ℕ} (A : Subfield ℝ)
    (b : Fin s → Fin d → A) :
    (subfieldTensorPiEquiv A s).toLinearMap.comp
      ((Matrix.toLin' (Matrix.of fun i j => b i j)).baseChange ℝ) =
      (subfieldLiftLinearMap A b).comp (subfieldTensorPiEquiv A d).toLinearMap := by
  refine LinearMap.ext ?_
  intro t
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · simp
  · intro c y
    ext i
    let fA : (Fin d → A) →ₗ[A] Fin s → A :=
      Matrix.toLin' (Matrix.of fun i j => b i j)
    change ((subfieldTensorPiEquiv A s).toLinearMap (fA.baseChange ℝ (c ⊗ₜ[A] y))) i =
      ((subfieldLiftLinearMap A b).comp (subfieldTensorPiEquiv A d).toLinearMap) (c ⊗ₜ[A] y) i
    rw [LinearMap.baseChange_tmul]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, subfieldTensorPiEquiv]
    rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRight_apply]
    change (fA y i • c) =
      (subfieldLiftLinearMap A b) ((@TensorProduct.piScalarRightHom A _ ℝ _ _ ℝ _ _ _
        (scalar_tower_subfield_real A) (Fin d)) (c ⊗ₜ[A] y)) i
    change (fA y i • c) =
      (subfieldLiftLinearMap A b) (fun j => y j • c) i
    simp [fA, subfieldLiftLinearMap, Matrix.toLin'_apply, Matrix.mulVec,
      dotProduct]
    simp only [Subfield.smul_def, smul_eq_mul]
    change (A.subtype (∑ x, b i x * y x)) * c = ∑ x, ↑(b i x) * (↑(y x) * c)
    rw [map_sum A.subtype, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp
    ring
  · intro u v hu hv
    simp [map_add, hu, hv]

lemma exists_rat_finset_approx
    {ι : Type*} [Fintype ι] (c : ι → ℝ) (U : Set (ι → ℝ))
    (hU : IsOpen U) (hc : c ∈ U) :
    ∃ q : ι → ℚ, (fun i => ((q i : ℚ) : ℝ)) ∈ U := by
  rcases (Metric.isOpen_iff.mp hU) c hc with ⟨ε, hε, hball⟩
  choose q hq using fun i => exists_rat_near (K := ℝ) (c i) hε
  refine ⟨q, hball ?_⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro i
  have h := hq i
  rw [Real.dist_eq, abs_sub_comm]
  simpa [Real.dist_eq] using h

lemma subfield_cast_sum_q_smul_apply {d : ℕ} {ι : Type} [Fintype ι]
    (A : Subfield ℝ) (q : ι → ℚ) (z : ι → Fin d → A) (j : Fin d) :
    (((∑ p : ι, (q p : A) • z p) j : A) : ℝ) =
      ∑ p : ι, ((q p : ℚ) : ℝ) * ((z p j : A) : ℝ) := by
  simp

lemma exists_subfield_linear_solution_from_rep {d r s : ℕ} (A : Subfield ℝ)
    (a : Fin r → Fin d → A) (b : Fin s → Fin d → A) (x : Fin d → ℝ)
    (S : Finset (ℝ × (Matrix.toLin' (Matrix.of fun i j => b i j)).ker))
    (hxrep : x = fun j => ∑ p ∈ S, p.1 * ((p.2.1 j : A) : ℝ))
    (hpos : ∀ i : Fin r, ∑ j : Fin d, ((a i j : A) : ℝ) * x j > 0) :
    ∃ y : Fin d → A,
      (∀ i : Fin r, ∑ j : Fin d, ((a i j : A) : ℝ) * ((y j : A) : ℝ) > 0) ∧
      ∀ i : Fin s, ∑ j : Fin d, ((b i j : A) : ℝ) * ((y j : A) : ℝ) = 0 := by
  let c : S → ℝ := fun p => p.1.1
  have hxrep' : x = fun j => ∑ p : S, c p * ((p.1.2.1 j : A) : ℝ) := by
    rw [hxrep]
    ext j
    rw [← Finset.sum_attach S (fun p => p.1 * ((p.2.1 j : A) : ℝ))]
    rfl
  let F : (S → ℝ) → Fin r → ℝ := fun u i =>
    ∑ j : Fin d, ((a i j : A) : ℝ) *
      ∑ p : S, u p * ((p.1.2.1 j : A) : ℝ)
  let U : Set (S → ℝ) := {u | ∀ i : Fin r, 0 < F u i}
  have hcont : ∀ i : Fin r, Continuous fun u : S → ℝ => F u i := by
    intro i
    dsimp [F]
    apply continuous_finset_sum Finset.univ
    intro j _
    apply Continuous.mul continuous_const
    apply continuous_finset_sum Finset.univ
    intro p _
    exact (continuous_apply p).mul continuous_const
  have hU : IsOpen U := by
    have hset : U = ⋂ i : Fin r, {u : S → ℝ | 0 < F u i} := by
      ext u
      simp [U]
    rw [hset]
    exact isOpen_iInter_of_finite fun i : Fin r => isOpen_Ioi.preimage (hcont i)
  have hc : c ∈ U := by
    intro i
    have hFx : F c i = ∑ j : Fin d, ((a i j : A) : ℝ) * x j := by
      calc
        F c i = ∑ j : Fin d, ((a i j : A) : ℝ) *
            (fun j => ∑ p : S, c p * ((p.1.2.1 j : A) : ℝ)) j := rfl
        _ = ∑ j : Fin d, ((a i j : A) : ℝ) * x j := by
          apply Finset.sum_congr rfl
          intro j _
          change ((a i j : A) : ℝ) *
              (∑ p : S, c p * ((p.1.2.1 j : A) : ℝ)) =
            ((a i j : A) : ℝ) * x j
          rw [← congrFun hxrep' j]
    simpa [U, hFx] using hpos i
  rcases exists_rat_finset_approx c U hU hc with ⟨q, hq⟩
  let y : Fin d → A := ∑ p : S, (q p : A) • p.1.2.1
  refine ⟨y, ?_, ?_⟩
  · intro i
    have hFy : F (fun p : S => ((q p : ℚ) : ℝ)) i =
        ∑ j : Fin d, ((a i j : A) : ℝ) * ((y j : A) : ℝ) := by
      calc
        F (fun p : S => ((q p : ℚ) : ℝ)) i
            = ∑ j : Fin d, ((a i j : A) : ℝ) *
                ∑ p : S, ((q p : ℚ) : ℝ) * ((p.1.2.1 j : A) : ℝ) := rfl
        _ = ∑ j : Fin d, ((a i j : A) : ℝ) * ((y j : A) : ℝ) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [subfield_cast_sum_q_smul_apply A q (fun p : S => p.1.2.1) j]
    rw [← hFy]
    exact hq i
  · have hyE : y ∈ (Matrix.toLin' (Matrix.of fun i j => b i j)).ker := by
      dsimp [y]
      apply Submodule.sum_smul_mem
      intro p hp
      exact p.1.2.property
    have hfy : Matrix.toLin' (Matrix.of fun i j => b i j) y = 0 :=
      LinearMap.mem_ker.mp hyE
    intro i
    have hi := congrFun hfy i
    have hiR := congrArg (fun z : A => (z : ℝ)) hi
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct] using hiR

lemma exists_subfield_linear_solution {d r s : ℕ} (A : Subfield ℝ)
    (a : Fin r → Fin d → A) (b : Fin s → Fin d → A) (x : Fin d → ℝ)
    (hpos : ∀ i : Fin r, ∑ j : Fin d, ((a i j : A) : ℝ) * x j > 0)
    (heq : ∀ i : Fin s, ∑ j : Fin d, ((b i j : A) : ℝ) * x j = 0) :
    ∃ y : Fin d → A,
      (∀ i : Fin r, ∑ j : Fin d, ((a i j : A) : ℝ) * ((y j : A) : ℝ) > 0) ∧
      ∀ i : Fin s, ∑ j : Fin d, ((b i j : A) : ℝ) * ((y j : A) : ℝ) = 0 := by
  let fA : (Fin d → A) →ₗ[A] Fin s → A :=
    Matrix.toLin' (Matrix.of fun i j => b i j)
  let E : Submodule A (Fin d → A) := fA.ker
  letI := fA.ker.module
  have hexact : Function.Exact ⇑E.subtype ⇑fA := by
    intro z
    constructor
    · intro hz
      exact ⟨⟨z, hz⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact z.property
  have hflat : Function.Exact ⇑(LinearMap.lTensor ℝ E.subtype) ⇑(LinearMap.lTensor ℝ fA) :=
    Module.Flat.lTensor_exact (R := A) (M := ℝ) hexact
  let t : TensorProduct A ℝ (Fin d → A) := (subfieldTensorPiEquiv A d).symm x
  have hkernel : LinearMap.lTensor ℝ fA t = 0 := by
    apply (subfieldTensorPiEquiv A s).injective
    have hmap := congrArg (fun F => F t) (subfieldTensorPiEquiv_lTensor A b)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, t] at hmap
    have hxzero : subfieldLiftLinearMap A b x = 0 := by
      ext i
      exact heq i
    change (subfieldTensorPiEquiv A s) (fA.baseChange ℝ t) = (subfieldTensorPiEquiv A s) 0
    change (subfieldTensorPiEquiv A s)
      ((Matrix.toLin' (Matrix.of fun i j => b i j)).baseChange ℝ
        ((subfieldTensorPiEquiv A d).symm x)) = (subfieldTensorPiEquiv A s) 0
    calc
      (subfieldTensorPiEquiv A s)
          ((Matrix.toLin' (Matrix.of fun i j => b i j)).baseChange ℝ
            ((subfieldTensorPiEquiv A d).symm x))
          = ((subfieldLiftLinearMap A b).comp (subfieldTensorPiEquiv A d).toLinearMap)
              ((subfieldTensorPiEquiv A d).symm x) := hmap
      _ = subfieldLiftLinearMap A b x := by simp
      _ = 0 := hxzero
      _ = (subfieldTensorPiEquiv A s) 0 := by simp
  rcases (hflat t).mp hkernel with ⟨zT, hzT⟩
  rcases TensorProduct.exists_finset zT with ⟨S, hS⟩
  have hxrep : x = fun j => ∑ p ∈ S, p.1 * ((p.2.1 j : A) : ℝ) := by
    have hfun : (subfieldTensorPiEquiv A d).toLinearMap (LinearMap.lTensor ℝ E.subtype zT) = x := by
      rw [hzT]
      simp [t]
    have hsum : (subfieldTensorPiEquiv A d).toLinearMap (LinearMap.lTensor ℝ E.subtype zT) =
        fun j => ∑ p ∈ S, p.1 * ((p.2.1 j : A) : ℝ) := by
      rw [hS]
      rw [map_sum (LinearMap.lTensor ℝ E.subtype)]
      rw [map_sum (subfieldTensorPiEquiv A d).toLinearMap]
      ext j
      rw [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro p hp
      rw [LinearMap.lTensor_tmul]
      simp [subfieldTensorPiEquiv, TensorProduct.piScalarRight, Subfield.smul_def,
        smul_eq_mul, mul_comm]
    exact hfun.symm.trans hsum
  exact exists_subfield_linear_solution_from_rep A a b x S hxrep hpos

/- accepted add_to_file helper 2 -/
lemma eval₂_int_subfield_cast {k : ℕ} (A : Subfield ℝ) (v : Fin k → A)
    (p : MvPolynomial (Fin k) ℤ) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) (fun i => ((v i : A) : ℝ)) p =
      ((MvPolynomial.eval₂ (Int.castRingHom A) (fun i => v i) p : A) : ℝ) := by
  symm
  change A.subtype (MvPolynomial.eval₂ (Int.castRingHom A) (fun i => v i) p) = _
  rw [MvPolynomial.eval₂_comp_left A.subtype (Int.castRingHom A) (fun i => v i) p]
  congr 1

/- accepted add_to_file helper 3 -/
lemma eval₂_rat_subfield_cast {k : ℕ} (A : Subfield ℝ) (v : Fin k → A)
    (p : MvPolynomial (Fin k) ℚ) :
    MvPolynomial.eval₂ (Rat.castHom ℝ) (fun i => ((v i : A) : ℝ)) p =
      ((MvPolynomial.eval₂ (Rat.castHom A) (fun i => v i) p : A) : ℝ) := by
  symm
  change A.subtype (MvPolynomial.eval₂ (Rat.castHom A) (fun i => v i) p) = _
  rw [MvPolynomial.eval₂_comp_left A.subtype (Rat.castHom A) (fun i => v i) p]
  congr 1

/- accepted add_to_file helper 4 -/
def HasSubfieldPoint (A : Subfield ℝ) :
    (Σ k : ℕ, Set (Fin k → ℝ)) → Prop
  | ⟨k, S⟩ => ∃ v : Fin k → A, (fun i => ((v i : A) : ℝ)) ∈ S

/- accepted add_to_file helper 5 -/
lemma fin_append_subfield_cast {k d : ℕ} (A : Subfield ℝ)
    (v : Fin k → A) (y : Fin d → A) :
    Fin.append (fun i => ((v i : A) : ℝ)) (fun i => ((y i : A) : ℝ)) =
      fun i => ((Fin.append v y i : A) : ℝ) := by
  funext i
  induction i using Fin.addCases with
  | left i => simp [Fin.append_left]
  | right i => simp [Fin.append_right]

/- accepted add_to_file helper 6 -/
lemma stable_projection_hasSubfieldPoint_iff
    (A : Subfield ℝ) {k d : ℕ}
    (S : Set (Fin k → ℝ)) (T : Set (Fin (k + d) → ℝ))
    (r s : ℕ)
    (φ : Fin r → Fin d → MvPolynomial (Fin k) ℤ)
    (ψ : Fin s → Fin d → MvPolynomial (Fin k) ℤ)
    (hsurj : ∀ v ∈ S, ∃ v' : Fin d → ℝ, Fin.append v v' ∈ T)
    (hchar : ∀ (v : Fin k → ℝ) (v' : Fin d → ℝ),
      Fin.append v v' ∈ T ↔
        v ∈ S ∧
        (∀ i : Fin r,
          ∑ j : Fin d,
            MvPolynomial.eval₂ (Int.castRingHom ℝ) v (φ i j) * v' j > 0) ∧
        (∀ i : Fin s,
          ∑ j : Fin d,
            MvPolynomial.eval₂ (Int.castRingHom ℝ) v (ψ i j) * v' j = 0)) :
    HasSubfieldPoint A ⟨k, S⟩ ↔ HasSubfieldPoint A ⟨k + d, T⟩ := by
  constructor
  · rintro ⟨v, hv⟩
    let vR : Fin k → ℝ := fun i => ((v i : A) : ℝ)
    rcases hsurj vR hv with ⟨x, hx⟩
    rcases (hchar vR x).mp hx with ⟨_, hineq, heq⟩
    let a : Fin r → Fin d → A := fun i j =>
      MvPolynomial.eval₂ (Int.castRingHom A) (fun l => v l) (φ i j)
    let b : Fin s → Fin d → A := fun i j =>
      MvPolynomial.eval₂ (Int.castRingHom A) (fun l => v l) (ψ i j)
    have hineq' : ∀ i : Fin r,
        ∑ j : Fin d, ((a i j : A) : ℝ) * x j > 0 := by
      intro i
      simpa [a, vR, eval₂_int_subfield_cast] using hineq i
    have heq' : ∀ i : Fin s,
        ∑ j : Fin d, ((b i j : A) : ℝ) * x j = 0 := by
      intro i
      simpa [b, vR, eval₂_int_subfield_cast] using heq i
    rcases exists_subfield_linear_solution A a b x hineq' heq' with ⟨y, hypos, hyeq⟩
    refine ⟨Fin.append v y, ?_⟩
    have hyposR : ∀ i : Fin r,
        ∑ j : Fin d,
          MvPolynomial.eval₂ (Int.castRingHom ℝ) vR (φ i j) *
            (((y j : A) : ℝ)) > 0 := by
      intro i
      simpa [a, vR, eval₂_int_subfield_cast] using hypos i
    have hyeqR : ∀ i : Fin s,
        ∑ j : Fin d,
          MvPolynomial.eval₂ (Int.castRingHom ℝ) vR (ψ i j) *
            (((y j : A) : ℝ)) = 0 := by
      intro i
      simpa [b, vR, eval₂_int_subfield_cast] using hyeq i
    have hmem : Fin.append vR (fun i => ((y i : A) : ℝ)) ∈ T := by
      exact (hchar vR (fun i => ((y i : A) : ℝ))).mpr ⟨hv, hyposR, hyeqR⟩
    rwa [fin_append_subfield_cast A v y] at hmem
  · rintro ⟨w, hw⟩
    let v : Fin k → A := fun i => w (Fin.castAdd d i)
    let y : Fin d → A := fun i => w (Fin.natAdd k i)
    let vR : Fin k → ℝ := fun i => ((v i : A) : ℝ)
    let yR : Fin d → ℝ := fun i => ((y i : A) : ℝ)
    have hmem : Fin.append vR yR ∈ T := by
      have hrestrict :=
        @Fin.append_castAdd_natAdd k d ℝ (fun i => ((w i : A) : ℝ))
      rw [hrestrict]
      exact hw
    rcases (hchar vR yR).mp hmem with ⟨hvS, _, _⟩
    exact ⟨v, hvS⟩

/- accepted add_to_file helper 7 -/
lemma stable_rational_hasSubfieldPoint_iff
    (A : Subfield ℝ) {k l : ℕ}
    (S : Set (Fin k → ℝ)) (T : Set (Fin l → ℝ))
    (h : S ≃ₜ T)
    (hfwd : ∀ i : Fin l, ∃ p q : MvPolynomial (Fin k) ℚ,
      ∀ v : S,
        MvPolynomial.eval₂ (Rat.castHom ℝ) (v : Fin k → ℝ) q ≠ 0 ∧
        (h v : Fin l → ℝ) i =
          MvPolynomial.eval₂ (Rat.castHom ℝ) (v : Fin k → ℝ) p /
            MvPolynomial.eval₂ (Rat.castHom ℝ) (v : Fin k → ℝ) q)
    (hinv : ∀ i : Fin k, ∃ p q : MvPolynomial (Fin l) ℚ,
      ∀ w : T,
        MvPolynomial.eval₂ (Rat.castHom ℝ) (w : Fin l → ℝ) q ≠ 0 ∧
        (h.symm w : Fin k → ℝ) i =
          MvPolynomial.eval₂ (Rat.castHom ℝ) (w : Fin l → ℝ) p /
            MvPolynomial.eval₂ (Rat.castHom ℝ) (w : Fin l → ℝ) q) :
    HasSubfieldPoint A ⟨k, S⟩ ↔ HasSubfieldPoint A ⟨l, T⟩ := by
  constructor
  · rintro ⟨v, hv⟩
    let vR : Fin k → ℝ := fun i => ((v i : A) : ℝ)
    let vS : S := ⟨vR, hv⟩
    choose p q hpq using hfwd
    let w : Fin l → A := fun i =>
      MvPolynomial.eval₂ (Rat.castHom A) (fun j => v j) (p i) /
        MvPolynomial.eval₂ (Rat.castHom A) (fun j => v j) (q i)
    refine ⟨w, ?_⟩
    have hcoord : (fun i => ((w i : A) : ℝ)) = (h vS : Fin l → ℝ) := by
      funext i
      rcases hpq i vS with ⟨_, hmap⟩
      rw [hmap]
      dsimp [w, vS, vR]
      norm_num [eval₂_rat_subfield_cast]
    rw [hcoord]
    exact (h vS).property
  · rintro ⟨w, hw⟩
    let wR : Fin l → ℝ := fun i => ((w i : A) : ℝ)
    let wT : T := ⟨wR, hw⟩
    choose p q hpq using hinv
    let v : Fin k → A := fun i =>
      MvPolynomial.eval₂ (Rat.castHom A) (fun j => w j) (p i) /
        MvPolynomial.eval₂ (Rat.castHom A) (fun j => w j) (q i)
    refine ⟨v, ?_⟩
    have hcoord : (fun i => ((v i : A) : ℝ)) = (h.symm wT : Fin k → ℝ) := by
      funext i
      rcases hpq i wT with ⟨_, hmap⟩
      rw [hmap]
      dsimp [v, wT, wR]
      norm_num [eval₂_rat_subfield_cast]
    rw [hcoord]
    exact (h.symm wT).property

/- accepted add_to_file helper 8 -/
lemma stable_elementary_hasSubfieldPoint_iff
    (A : Subfield ℝ) {X Y : Σ k : ℕ, Set (Fin k → ℝ)}
    (h : (∃ (k d : ℕ) (S : Set (Fin k → ℝ)) (T : Set (Fin (k + d) → ℝ)),
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
                    MvPolynomial.eval₂ (Rat.castHom ℝ) (w : Fin l → ℝ) q))) :
    HasSubfieldPoint A X ↔ HasSubfieldPoint A Y := by
  rcases h with hproj | hrat
  · rcases hproj with ⟨k, d, S, T, hX, hY, r, s, φ, ψ, hsurj, hchar⟩
    simpa [hX, hY] using
      stable_projection_hasSubfieldPoint_iff A S T r s φ ψ hsurj hchar
  · rcases hrat with ⟨k, l, S, T, hX, hY, h, hfwd, hinv⟩
    simpa [hX, hY] using
      stable_rational_hasSubfieldPoint_iff A S T h hfwd hinv

/- verified submission -/
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
      (¬ ∃ w : Fin m → A, (fun i => ((w i : A) : ℝ)) ∈ W) := by
  have hpoints : HasSubfieldPoint A ⟨n, V⟩ ↔ HasSubfieldPoint A ⟨m, W⟩ := by
    refine Relation.EqvGen.rec
      (motive := fun x y _ => HasSubfieldPoint A x ↔ HasSubfieldPoint A y)
      ?_ ?_ ?_ ?_ hstable
    · intro x y hxy
      exact stable_elementary_hasSubfieldPoint_iff A hxy
    · intro x
      rfl
    · intro x y hxy ih
      exact ih.symm
    · intro x y z hxy hyz ihxy ihyz
      exact ihxy.trans ihyz
  simpa [HasSubfieldPoint] using not_congr hpoints

end Rollout_p2109_stable_equivalence_empty_subfield_points_i

#check_dependency_graph "Rollout_p2109_stable_equivalence_empty_subfield_points_i.stable_equivalence_empty_subfield_points_iff" against "{\"edges\":[{\"conclusion\":{\"name\":\"hpoints\",\"statement\":\"Rollout_p2109_stable_equivalence_empty_subfield_points_i.HasSubfieldPoint A ⟨n, V⟩ ↔ Rollout_p2109_stable_equivalence_empty_subfield_points_i.HasSubfieldPoint A ⟨m, W⟩\"},\"graphEdgeId\":\"h_001_hpoints\",\"premises\":[{\"name\":\"hstable\",\"statement\":\"Relation.EqvGen (fun X Y => (∃ k d S T, X = ⟨k, S⟩ ∧ Y = ⟨k + d, T⟩ ∧ ∃ r s φ ψ, (∀ v ∈ S, ∃ v', Fin.append v v' ∈ T) ∧ ∀ (v : Fin k → ℝ) (v' : Fin d → ℝ), Fin.append v v' ∈ T ↔ v ∈ S ∧ (∀ (i : Fin r), ∑ j, MvPolynomial.eval₂ (Int.castRingHom ℝ) v (φ i j) * v' j > 0) ∧ ∀ (i : Fin s), ∑ j, MvPolynomial.eval₂ (Int.castRingHom ℝ) v (ψ i j) * v' j = 0) ∨ ∃ k l S T, X = ⟨k, S⟩ ∧ Y = ⟨l, T⟩ ∧ ∃ h, (∀ (i : Fin l), ∃ p q, ∀ (v : ↑S), MvPolynomial.eval₂ (Rat.castHom ℝ) (↑v) q ≠ 0 ∧ ↑(h v) i = MvPolynomial.eval₂ (Rat.castHom ℝ) (↑v) p / MvPolynomial.eval₂ (Rat.castHom ℝ) (↑v) q) ∧ ∀ (i : Fin k), ∃ p q, ∀ (w : ↑T), MvPolynomial.eval₂ (Rat.castHom ℝ) (↑w) q ≠ 0 ∧ ↑(h.symm w) i = MvPolynomial.eval₂ (Rat.castHom ℝ) (↑w) p / MvPolynomial.eval₂ (Rat.castHom ℝ) (↑w) q) ⟨n, V⟩ ⟨m, W⟩\"}],\"rawEdgeId\":\"telescope_9\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(¬∃ v, (fun i => ↑(v i)) ∈ V) ↔ ¬∃ w, (fun i => ↑(w i)) ∈ W\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hpoints\",\"statement\":\"Rollout_p2109_stable_equivalence_empty_subfield_points_i.HasSubfieldPoint A ⟨n, V⟩ ↔ Rollout_p2109_stable_equivalence_empty_subfield_points_i.HasSubfieldPoint A ⟨m, W⟩\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2109_stable_equivalence_empty_subfield_points_i\",\"reconstructedProofSha256\":\"0491507063df14fc42c2ac8996ab55388da578e868a0a8c896a2ea5e42e201c0\",\"selectedEdgeCount\":2,\"theoremName\":\"Rollout_p2109_stable_equivalence_empty_subfield_points_i.stable_equivalence_empty_subfield_points_iff\",\"topologySha256\":\"83c1f3429a819d27d51092c231154faa95c7febde4ce81a49b36cda28c209492\"}"

namespace Rollout_p2112_diagonal_nonnegative_part_difference

-- graph_id: p2112_diagonal_nonnegative_part_difference
-- topology_sha256: 541c0b3df8342957f6a05dab1b135f216666e01e3c4308e0074bef9b58f6652e
/- verified submission -/
lemma positive_part_secant_aux (x y : ℝ) :
    ∃ ω : ℝ, 0 ≤ ω ∧ ω ≤ 1 ∧
      (if 0 ≤ x then (1 : ℝ) else 0) * x -
        (if 0 ≤ y then (1 : ℝ) else 0) * y = ω * (x - y) := by
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · refine ⟨1, by norm_num, by norm_num, ?_⟩
      simp [hx, hy]
    · have hy_lt : y < 0 := lt_of_not_ge hy
      have hden : 0 < x - y := sub_pos.mpr (lt_of_lt_of_le hy_lt hx)
      refine ⟨x / (x - y), ?_, ?_, ?_⟩
      · exact div_nonneg hx (le_of_lt hden)
      · rw [div_le_one hden]
        nlinarith
      · simp [hx, hy]
        exact (div_mul_cancel₀ x (ne_of_gt hden)).symm
  · have hx_lt : x < 0 := lt_of_not_ge hx
    by_cases hy : 0 ≤ y
    · have hden : 0 < y - x := sub_pos.mpr (lt_of_lt_of_le hx_lt hy)
      refine ⟨y / (y - x), ?_, ?_, ?_⟩
      · exact div_nonneg hy (le_of_lt hden)
      · rw [div_le_one hden]
        nlinarith
      · simp [hx, hy]
        field_simp [ne_of_gt hden]
        ring
    · refine ⟨0, by norm_num, by norm_num, ?_⟩
      simp [hx, hy]

theorem diagonal_nonnegative_part_difference
    (n : ℕ) (hn : 0 < n) (x y : Fin n → ℝ) :
    let P : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ :=
      fun z => Matrix.diagonal (fun i => if 0 ≤ z i then 1 else 0)
    ∃ ω : Fin n → ℝ,
      (∀ i, 0 ≤ ω i ∧ ω i ≤ 1) ∧
        Matrix.mulVec (P x) x - Matrix.mulVec (P y) y =
          Matrix.mulVec (Matrix.diagonal ω) (x - y) := by
  let P : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ :=
    fun z => Matrix.diagonal (fun i => if 0 ≤ z i then 1 else 0)
  let ω : Fin n → ℝ :=
    fun i => Classical.choose (positive_part_secant_aux (x i) (y i))
  have hω : ∀ i : Fin n,
      0 ≤ ω i ∧ ω i ≤ 1 ∧
        (if 0 ≤ x i then (1 : ℝ) else 0) * x i -
          (if 0 ≤ y i then (1 : ℝ) else 0) * y i = ω i * (x i - y i) := by
    intro i
    dsimp [ω]
    exact Classical.choose_spec (positive_part_secant_aux (x i) (y i))
  refine ⟨ω, ?_, ?_⟩
  · intro i
    exact ⟨(hω i).1, (hω i).2.1⟩
  · funext i
    exact (by
      simpa [P, Matrix.mulVec_diagonal, Pi.sub_apply] using (hω i).2.2 :
        (Matrix.mulVec (P x) x - Matrix.mulVec (P y) y) i =
          (Matrix.mulVec (Matrix.diagonal ω) (x - y)) i)

end Rollout_p2112_diagonal_nonnegative_part_difference

#check_dependency_graph "Rollout_p2112_diagonal_nonnegative_part_difference.diagonal_nonnegative_part_difference" against "{\"edges\":[{\"conclusion\":{\"name\":\"hω\",\"statement\":\"∀ (i : Fin n), 0 ≤ ω i ∧ ω i ≤ 1 ∧ (if 0 ≤ x i then 1 else 0) * x i - (if 0 ≤ y i then 1 else 0) * y i = ω i * (x i - y i)\"},\"graphEdgeId\":\"h_001_h\",\"premises\":[],\"rawEdgeId\":\"telescope_6\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∃ ω, (∀ (i : Fin n), 0 ≤ ω i ∧ ω i ≤ 1) ∧ ((fun z => Matrix.diagonal fun i => if 0 ≤ z i then 1 else 0) x).mulVec x - ((fun z => Matrix.diagonal fun i => if 0 ≤ z i then 1 else 0) y).mulVec y = (Matrix.diagonal ω).mulVec (x - y)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hω\",\"statement\":\"∀ (i : Fin n), 0 ≤ ω i ∧ ω i ≤ 1 ∧ (if 0 ≤ x i then 1 else 0) * x i - (if 0 ≤ y i then 1 else 0) * y i = ω i * (x i - y i)\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2112_diagonal_nonnegative_part_difference\",\"reconstructedProofSha256\":\"481f7a61e57d2cb5b6e70040a95b27cffd8151229b355b6032698da9b4cbb8bf\",\"selectedEdgeCount\":2,\"theoremName\":\"Rollout_p2112_diagonal_nonnegative_part_difference.diagonal_nonnegative_part_difference\",\"topologySha256\":\"541c0b3df8342957f6a05dab1b135f216666e01e3c4308e0074bef9b58f6652e\"}"

namespace Rollout_p2116_pendant_branch_laplacian_eigenvector_decay

-- graph_id: p2116_pendant_branch_laplacian_eigenvector_decay
-- topology_sha256: 6def72b531159d4e71e5ba8bebbb09ad9dc81baad6b3138a095ddbee09f704e8
/- accepted add_to_file helper 1 -/
lemma pendant_neighborFinset_interior
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 1 ≤ k)
    (i : Fin k → V)
    (hbranch : ∀ a b : Fin k,
      G.Adj (i a) (i b) ↔ a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (hexternal : ∃ x : V,
      x ∉ Set.range i ∧
      G.Adj (i ⟨0, hk⟩) x ∧
      ∀ (a : Fin k) (v : V), v ∉ Set.range i → G.Adj (i a) v →
        a = ⟨0, hk⟩ ∧ v = x)
    (a : Fin k) (ha : 0 < a.val) (hs : a.val + 1 < k) :
    G.neighborFinset (i a) =
      {i ⟨a.val - 1, by omega⟩, i ⟨a.val + 1, hs⟩} := by
  ext v
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hAdj
    by_cases hv : v ∈ Set.range i
    · rcases hv with ⟨b, rfl⟩
      have hb := (hbranch a b).mp hAdj
      rcases hb with h | h
      · right
        have hbv : b.val = a.val + 1 := by omega
        exact congrArg i (Fin.ext hbv)
      · left
        have hbv : b.val = a.val - 1 := by omega
        exact congrArg i (Fin.ext hbv)
    · rcases hexternal with ⟨x, hxrange, hxadj, huniq⟩
      obtain ⟨ha0, hvx⟩ := huniq a v hv hAdj
      have : a.val = 0 := congrArg Fin.val ha0
      omega
  · intro hv
    rcases hv with hv | hv
    · subst v
      have hpred : a.val - 1 + 1 = a.val := by omega
      exact (hbranch a ⟨a.val - 1, by omega⟩).mpr (Or.inr hpred)
    · subst v
      exact (hbranch a ⟨a.val + 1, hs⟩).mpr (Or.inl rfl)

lemma pendant_neighborFinset_last
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 1 ≤ k)
    (i : Fin k → V)
    (hbranch : ∀ a b : Fin k,
      G.Adj (i a) (i b) ↔ a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (hexternal : ∃ x : V,
      x ∉ Set.range i ∧
      G.Adj (i ⟨0, hk⟩) x ∧
      ∀ (a : Fin k) (v : V), v ∉ Set.range i → G.Adj (i a) v →
        a = ⟨0, hk⟩ ∧ v = x)
    (a : Fin k) (ha : 0 < a.val) (hs : a.val + 1 = k) :
    G.neighborFinset (i a) =
      {i ⟨a.val - 1, by omega⟩} := by
  ext v
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hAdj
    by_cases hv : v ∈ Set.range i
    · rcases hv with ⟨b, rfl⟩
      have hb := (hbranch a b).mp hAdj
      rcases hb with h | h
      · have : b.val = k := by omega
        omega
      · have hbv : b.val = a.val - 1 := by omega
        exact congrArg i (Fin.ext hbv)
    · rcases hexternal with ⟨x, hxrange, hxadj, huniq⟩
      obtain ⟨ha0, hvx⟩ := huniq a v hv hAdj
      have : a.val = 0 := congrArg Fin.val ha0
      omega
  · intro hv
    subst v
    have hpred : a.val - 1 + 1 = a.val := by omega
    exact (hbranch a ⟨a.val - 1, by omega⟩).mpr (Or.inr hpred)

/- accepted add_to_file helper 2 -/
theorem pendant_eigen_last
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 1 ≤ k)
    (i : Fin k → V)
    (hbranch : ∀ a b : Fin k,
      G.Adj (i a) (i b) ↔ a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (hexternal : ∃ x : V,
      x ∉ Set.range i ∧
      G.Adj (i ⟨0, hk⟩) x ∧
      ∀ (a : Fin k) (v : V), v ∉ Set.range i → G.Adj (i a) v →
        a = ⟨0, hk⟩ ∧ v = x)
    (lam : ℝ)
    (φ : V → ℝ)
    (heigen : (G.lapMatrix ℝ).mulVec φ = lam • φ)
    (j : Fin k) (hj : j.val + 1 < k)
    (hjd : j.val + 2 = k) :
    φ (i j) = (1 - lam) * φ (i ⟨j.val + 1, hj⟩) := by
  have hpos : 0 < (⟨j.val + 1, hj⟩ : Fin k).val := by
    change 0 < j.val + 1
    omega
  have hlast : (⟨j.val + 1, hj⟩ : Fin k).val + 1 = k := by
    change j.val + 1 + 1 = k
    omega
  have hneigh := pendant_neighborFinset_last G hk i hbranch hexternal
      ⟨j.val + 1, hj⟩ hpos hlast
  have hpred : (⟨(⟨j.val + 1, hj⟩ : Fin k).val - 1, by omega⟩ : Fin k) = j := by
    apply Fin.ext
    change j.val + 1 - 1 = j.val
    omega
  have hcard : (G.neighborFinset (i ⟨j.val + 1, hj⟩)).card = 1 := by
    rw [hneigh]
    simp
  have hdeg : G.degree (i ⟨j.val + 1, hj⟩) = 1 := by
    rw [← G.card_neighborFinset_eq_degree, hcard]
  have hEq := congrFun heigen (i ⟨j.val + 1, hj⟩)
  rw [SimpleGraph.lapMatrix_mulVec_apply] at hEq
  rw [hdeg, hneigh] at hEq
  simp [hpred] at hEq
  linarith

/- accepted add_to_file helper 3 -/
theorem pendant_eigen_interior
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 1 ≤ k)
    (i : Fin k → V)
    (hi : Function.Injective i)
    (hbranch : ∀ a b : Fin k,
      G.Adj (i a) (i b) ↔ a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (hexternal : ∃ x : V,
      x ∉ Set.range i ∧
      G.Adj (i ⟨0, hk⟩) x ∧
      ∀ (a : Fin k) (v : V), v ∉ Set.range i → G.Adj (i a) v →
        a = ⟨0, hk⟩ ∧ v = x)
    (lam : ℝ)
    (φ : V → ℝ)
    (heigen : (G.lapMatrix ℝ).mulVec φ = lam • φ)
    (j : Fin k) (hj : j.val + 1 < k) (hj2 : j.val + 2 < k) :
    φ (i j) + φ (i ⟨j.val + 2, hj2⟩) =
      (2 - lam) * φ (i ⟨j.val + 1, hj⟩) := by
  let s : Fin k := ⟨j.val + 1, hj⟩
  have hsval : s.val = j.val + 1 := rfl
  have hs_pos : 0 < s.val := by
    rw [hsval]
    omega
  have hs_succ : s.val + 1 < k := by
    rw [hsval]
    omega
  have hneigh := pendant_neighborFinset_interior G hk i hbranch hexternal s hs_pos hs_succ
  have hpred : (⟨s.val - 1, by omega⟩ : Fin k) = j := by
    apply Fin.ext
    change s.val - 1 = j.val
    omega
  have hnext : (⟨s.val + 1, hs_succ⟩ : Fin k) = ⟨j.val + 2, hj2⟩ := by
    apply Fin.ext
    change s.val + 1 = j.val + 2
    omega
  have hne : (⟨s.val - 1, by omega⟩ : Fin k) ≠ ⟨s.val + 1, hs_succ⟩ := by
    intro h
    have hv := congrArg Fin.val h
    change s.val - 1 = s.val + 1 at hv
    omega
  have hvne : i ⟨s.val - 1, by omega⟩ ≠ i ⟨s.val + 1, hs_succ⟩ := by
    intro h
    exact hne (hi h)
  have hcard : (G.neighborFinset (i s)).card = 2 := by
    rw [hneigh]
    exact Finset.card_pair hvne
  have hdeg : G.degree (i s) = 2 := by
    rw [← G.card_neighborFinset_eq_degree, hcard]
  have hEq := congrFun heigen (i s)
  rw [SimpleGraph.lapMatrix_mulVec_apply] at hEq
  rw [hdeg, hneigh] at hEq
  rw [Finset.sum_pair hvne] at hEq
  simp [hpred, hnext] at hEq
  linarith

/- accepted add_to_file helper 4 -/
theorem pendant_adjacent_decay
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 1 ≤ k)
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
    (φ : V → ℝ)
    (heigen : (G.lapMatrix ℝ).mulVec φ = lam • φ) :
    ∀ (j : Fin k) (hj : j.val + 1 < k),
      |φ (i ⟨j.val + 1, hj⟩)| ≤
        (2 / (lam - 2)) * |φ (i j)| := by
  let γ : ℝ := 2 / (lam - 2)
  have ht : 0 < lam - 2 := by nlinarith
  have hγpos : 0 < γ := by
    dsimp [γ]
    positivity
  have hγlt : γ < 1 := by
    dsimp [γ]
    rw [div_lt_one ht]
    nlinarith
  have Haux : ∀ d : ℕ, ∀ (j : Fin k) (hj : j.val + 1 < k),
      j.val + d + 2 = k →
      |φ (i ⟨j.val + 1, hj⟩)| ≤ γ * |φ (i j)| := by
    intro d
    induction d with
    | zero =>
        intro j hj hdist
        have hjd : j.val + 2 = k := by omega
        have heq := pendant_eigen_last G hk i hbranch hexternal lam φ heigen j hj hjd
        have hAbs : |φ (i j)| = (lam - 1) * |φ (i ⟨j.val + 1, hj⟩)| := by
          rw [heq]
          rw [abs_mul]
          have hneg : 1 - lam < 0 := by nlinarith
          rw [abs_of_neg hneg]
          ring
        have hcoef : 1 ≤ γ * (lam - 1) := by
          dsimp [γ]
          field_simp [ne_of_gt ht]
          nlinarith
        calc
          |φ (i ⟨j.val + 1, hj⟩)| = 1 * |φ (i ⟨j.val + 1, hj⟩)| := by
            rw [one_mul]
          _ ≤ (γ * (lam - 1)) * |φ (i ⟨j.val + 1, hj⟩)| :=
            mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
          _ = γ * ((lam - 1) * |φ (i ⟨j.val + 1, hj⟩)|) := by ring
          _ = γ * |φ (i j)| := by rw [← hAbs]
    | succ d ih =>
        intro j hj hdist
        have hj2 : j.val + 2 < k := by omega
        let s : Fin k := ⟨j.val + 1, hj⟩
        have hsval : s.val = j.val + 1 := rfl
        have hs : s.val + 1 < k := by
          rw [hsval]
          omega
        have hsdist : s.val + d + 2 = k := by
          rw [hsval]
          omega
        have hnext := ih s hs hsdist
        have hnext' : |φ (i ⟨j.val + 2, hj2⟩)| ≤ γ * |φ (i s)| := by
          simpa [s] using hnext
        have heq := pendant_eigen_interior G hk i hi hbranch hexternal lam φ heigen j hj hj2
        have hAbs : |φ (i j) + φ (i ⟨j.val + 2, hj2⟩)| =
            (lam - 2) * |φ (i s)| := by
          rw [heq]
          rw [abs_mul]
          have hneg : 2 - lam < 0 := by nlinarith
          rw [abs_of_neg hneg]
          have hsdef : s = ⟨j.val + 1, hj⟩ := rfl
          rw [hsdef]
          ring
        have hineq0 : (lam - 2) * |φ (i s)| ≤
            |φ (i j)| + |φ (i ⟨j.val + 2, hj2⟩)| := by
          rw [← hAbs]
          exact abs_add_le _ _
        have hineq : (lam - 2) * |φ (i s)| ≤
            |φ (i j)| + γ * |φ (i s)| := by
          nlinarith
        have hsub : (lam - 2 - γ) * |φ (i s)| ≤ |φ (i j)| := by
          nlinarith
        have hcoef : 1 ≤ γ * (lam - 2 - γ) := by
          dsimp [γ]
          have htgt : 2 < lam - 2 := by nlinarith
          have htsq : 4 < (lam - 2)^2 := by
            nlinarith [mul_lt_mul_of_pos_left htgt ht]
          field_simp [ne_of_gt ht]
          nlinarith
        calc
          |φ (i ⟨j.val + 1, hj⟩)| = 1 * |φ (i ⟨j.val + 1, hj⟩)| := by
            rw [one_mul]
          _ ≤ (γ * (lam - 2 - γ)) * |φ (i ⟨j.val + 1, hj⟩)| :=
            mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
          _ = γ * ((lam - 2 - γ) * |φ (i ⟨j.val + 1, hj⟩)|) := by ring
          _ ≤ γ * |φ (i j)| := by
            have hsub' : (lam - 2 - γ) * |φ (i ⟨j.val + 1, hj⟩)| ≤ |φ (i j)| := by
              simpa [s] using hsub
            exact mul_le_mul_of_nonneg_left hsub' hγpos.le
  intro j hj
  exact Haux (k - (j.val + 2)) j hj (by omega)

/- verified submission -/
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
      ∀ j : Fin k, |φ (i j)| ≤ γ ^ j.val * |φ (i ⟨0, hk⟩)| := by
  dsimp only
  set γ : ℝ := 2 / (lam - 2) with hγdef
  have ht : 0 < lam - 2 := by nlinarith
  have hγpos : 0 < γ := by
    rw [hγdef]
    positivity
  have hγlt : γ < 1 := by
    rw [hγdef, div_lt_one ht]
    nlinarith
  have hadj := pendant_adjacent_decay G hk i hi hbranch hexternal lam hlam φ heigen
  refine ⟨hγpos, hγlt, ?_, ?_⟩
  · intro j hj
    rw [hγdef]
    exact hadj j hj
  · have Hpow_aux : ∀ n : ℕ, ∀ j : Fin k, j.val = n →
        |φ (i j)| ≤ γ ^ j.val * |φ (i ⟨0, hk⟩)| := by
      intro n
      induction n with
      | zero =>
          intro j hjval
          have hzero : j = ⟨0, hk⟩ := Fin.ext (by omega)
          rw [hzero]
          simp
      | succ n ih =>
          intro j hjval
          have hnlt : n < k := by omega
          let p : Fin k := ⟨n, hnlt⟩
          have hsproof : p.val + 1 < k := by
            dsimp [p]
            omega
          have hjp : j = ⟨p.val + 1, hsproof⟩ := by
            apply Fin.ext
            dsimp [p]
            omega
          calc
            |φ (i j)| = |φ (i ⟨p.val + 1, hsproof⟩)| := congrArg (fun v => |φ (i v)|) hjp
            _ ≤ γ * |φ (i p)| := by
              rw [hγdef]
              exact hadj p hsproof
            _ ≤ γ * (γ ^ n * |φ (i ⟨0, hk⟩)|) := by
              have hpval : p.val = n := rfl
              exact mul_le_mul_of_nonneg_left (ih p hpval) hγpos.le
            _ = γ ^ (n + 1) * |φ (i ⟨0, hk⟩)| := by
              rw [pow_succ]
              ring
            _ = γ ^ j.val * |φ (i ⟨0, hk⟩)| := by
              rw [hjval]
    intro j
    exact Hpow_aux j.val j rfl

end Rollout_p2116_pendant_branch_laplacian_eigenvector_decay

#check_dependency_graph "Rollout_p2116_pendant_branch_laplacian_eigenvector_decay.pendant_branch_laplacian_eigenvector_decay" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let γ := 2 / (lam - 2); 0 < γ ∧ γ < 1 ∧ (∀ (j : Fin k) (hj : ↑j + 1 < k), |φ (i ⟨↑j + 1, hj⟩)| ≤ γ * |φ (i j)|) ∧ ∀ (j : Fin k), |φ (i j)| ≤ γ ^ ↑j * |φ (i ⟨0, hk⟩)|\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hk\",\"statement\":\"1 ≤ k\"},{\"name\":\"hi\",\"statement\":\"Function.Injective i\"},{\"name\":\"hbranch\",\"statement\":\"∀ (a b : Fin k), G.Adj (i a) (i b) ↔ ↑a + 1 = ↑b ∨ ↑b + 1 = ↑a\"},{\"name\":\"hexternal\",\"statement\":\"∃ x ∉ Set.range i, G.Adj (i ⟨0, hk⟩) x ∧ ∀ (a : Fin k), ∀ v ∉ Set.range i, G.Adj (i a) v → a = ⟨0, hk⟩ ∧ v = x\"},{\"name\":\"hlam\",\"statement\":\"4 < lam\"},{\"name\":\"heigen\",\"statement\":\"(SimpleGraph.lapMatrix ℝ G).mulVec φ = lam • φ\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2116_pendant_branch_laplacian_eigenvector_decay\",\"reconstructedProofSha256\":\"18416f0080ac0f8e9f254f03f684a1e65ca560311ab67da9cf851b467e2d56cc\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p2116_pendant_branch_laplacian_eigenvector_decay.pendant_branch_laplacian_eigenvector_decay\",\"topologySha256\":\"6def72b531159d4e71e5ba8bebbb09ad9dc81baad6b3138a095ddbee09f704e8\"}"

namespace Rollout_p2161_cell_entropy_inequality_for_semidiscrete_f

-- graph_id: p2161_cell_entropy_inequality_for_semidiscrete_f
-- topology_sha256: 914bb69b48bd25703fb73fec441a26a5ec4704a2b1e65300ddb0beca72209839
/- verified submission -/
theorem cell_entropy_inequality_for_semidiscrete_finite_volume_scheme
    {ι κ : Type*} [DecidableEq ι] [Fintype κ]
    (N : Finset ι)
    (V : ℝ) (hV : 0 < V)
    (A δ ε : ι → ℝ)
    (hA : ∀ r ∈ N, 0 ≤ A r)
    (hδ : ∀ r ∈ N, 0 < δ r)
    (hε : ∀ r ∈ N, 0 ≤ ε r)
    (qNeighbor : ι → κ → ℝ) (q : κ → ℝ)
    (T : ℝ) (hT : 0 < T)
    (H : ι → Matrix κ κ ℝ)
    (hH : ∀ r ∈ N, (H r).PosSemidef)
    (ρSNeighbor : ι → ℝ) (ρS : ℝ)
    (D : ι → ℝ) (dρSdt : ℝ) :
    let Δq : ι → κ → ℝ := fun r => qNeighbor r - q
    let entropyProduction : ι → ℝ := fun r =>
      ε r * dotProduct (Δq r) ((H r).mulVec (Δq r)) / (2 * T * δ r)
    let g : ι → ℝ := fun r => ε r * (ρSNeighbor r - ρS) / δ r
    dρSdt = (1 / V) * ∑ r ∈ N, A r * (-D r + g r + entropyProduction r) →
      dρSdt + (1 / V) * ∑ r ∈ N, A r * D r -
        (1 / V) * ∑ r ∈ N, A r * g r ≥ 0 := by
  intro Δq entropyProduction g hd
  have hprod : ∀ r ∈ N, 0 ≤ entropyProduction r := by
    intro r hr
    have hquad : 0 ≤ dotProduct (Δq r) ((H r).mulVec (Δq r)) := by
      simpa using (hH r hr).dotProduct_mulVec_nonneg (Δq r)
    have hden : 0 < 2 * T * δ r := by
      exact mul_pos (mul_pos (by norm_num) hT) (hδ r hr)
    exact div_nonneg (mul_nonneg (hε r hr) hquad) hden.le
  have hsum :
      ∑ r ∈ N, A r * (-D r + g r + entropyProduction r)
        = -∑ r ∈ N, A r * D r + ∑ r ∈ N, A r * g r +
            ∑ r ∈ N, A r * entropyProduction r := by
    simp_rw [mul_add, mul_neg]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  calc
    dρSdt + (1 / V) * ∑ r ∈ N, A r * D r -
        (1 / V) * ∑ r ∈ N, A r * g r
        = (1 / V) * ∑ r ∈ N, A r * entropyProduction r := by
          rw [hd, hsum]
          ring
    _ ≥ 0 := by
      exact mul_nonneg (one_div_nonneg.mpr hV.le)
        (Finset.sum_nonneg (fun r hr => mul_nonneg (hA r hr) (hprod r hr)))

end Rollout_p2161_cell_entropy_inequality_for_semidiscrete_f

#check_dependency_graph "Rollout_p2161_cell_entropy_inequality_for_semidiscrete_f.cell_entropy_inequality_for_semidiscrete_finite_volume_scheme" against "{\"edges\":[{\"conclusion\":{\"name\":\"hprod\",\"statement\":\"∀ r ∈ N, 0 ≤ entropyProduction r\"},\"graphEdgeId\":\"h_001_hprod\",\"premises\":[{\"name\":\"hδ\",\"statement\":\"∀ r ∈ N, 0 < δ r\"},{\"name\":\"hε\",\"statement\":\"∀ r ∈ N, 0 ≤ ε r\"},{\"name\":\"hT\",\"statement\":\"0 < T\"},{\"name\":\"hH\",\"statement\":\"∀ r ∈ N, (H r).PosSemidef\"}],\"rawEdgeId\":\"telescope_27\"},{\"conclusion\":{\"name\":\"hsum\",\"statement\":\"∑ r ∈ N, A r * (-D r + g r + entropyProduction r) = -∑ r ∈ N, A r * D r + ∑ r ∈ N, A r * g r + ∑ r ∈ N, A r * entropyProduction r\"},\"graphEdgeId\":\"h_002_hsum\",\"premises\":[],\"rawEdgeId\":\"telescope_28\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"dρSdt + 1 / V * ∑ r ∈ N, A r * D r - 1 / V * ∑ r ∈ N, A r * g r ≥ 0\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hV\",\"statement\":\"0 < V\"},{\"name\":\"hA\",\"statement\":\"∀ r ∈ N, 0 ≤ A r\"},{\"name\":\"hd\",\"statement\":\"dρSdt = 1 / V * ∑ r ∈ N, A r * (-D r + g r + entropyProduction r)\"},{\"name\":\"hprod\",\"statement\":\"∀ r ∈ N, 0 ≤ entropyProduction r\"},{\"name\":\"hsum\",\"statement\":\"∑ r ∈ N, A r * (-D r + g r + entropyProduction r) = -∑ r ∈ N, A r * D r + ∑ r ∈ N, A r * g r + ∑ r ∈ N, A r * entropyProduction r\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2161_cell_entropy_inequality_for_semidiscrete_f\",\"reconstructedProofSha256\":\"51d19a450c3431ccfe4246259fec55054226e7b688f918b56dd1693199bf62d5\",\"selectedEdgeCount\":3,\"theoremName\":\"Rollout_p2161_cell_entropy_inequality_for_semidiscrete_f.cell_entropy_inequality_for_semidiscrete_finite_volume_scheme\",\"topologySha256\":\"914bb69b48bd25703fb73fec441a26a5ec4704a2b1e65300ddb0beca72209839\"}"

namespace Rollout_p2227_strongmetricenvelopeofheight

-- graph_id: p2227_strongmetricenvelopeofheight
-- topology_sha256: 0c7a7e1ae1d7e6f1a427f32a3d41f791bd3bd2dbc65bf4ed5fae4de7739626f6
/- accepted add_to_file helper 1 -/
lemma finprod_sum_elim {ι κ M : Type*} [CommMonoid M]
    (f : ι → M) (g : κ → M)
    (hf : Function.HasFiniteMulSupport f)
    (hg : Function.HasFiniteMulSupport g) :
    (∏ᶠ x : ι ⊕ κ, Sum.elim f g x) =
      (∏ᶠ i, f i) * ∏ᶠ j, g j := by
  classical
  let s := hf.toFinset
  let t := hg.toFinset
  have hsub : Function.mulSupport (Sum.elim f g) ⊆ ↑(s.disjSum t) := by
    intro x hx
    cases x with
    | inl i =>
        have hi : i ∈ s := by
          have hi' : i ∈ hf.toFinset := (hf.mem_toFinset).2 hx
          simpa [s] using hi'
        simp [Finset.mem_disjSum, hi]
    | inr j =>
        have hj : j ∈ t := by
          have hj' : j ∈ hg.toFinset := (hg.mem_toFinset).2 hx
          simpa [t] using hj'
        simp [Finset.mem_disjSum, hj]
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  rw [Finset.prod_sumElim]
  rw [finprod_eq_prod_of_mulSupport_subset f (s:=s) (by
    intro i hi
    have hi' : i ∈ hf.toFinset := by simpa [s] using hi
    simpa [s] using (hf.mem_toFinset).1 hi'),
    finprod_eq_prod_of_mulSupport_subset g (s:=t) (by
    intro j hj
    have hj' : j ∈ hg.toFinset := by simpa [t] using hj
    simpa [t] using (hg.mem_toFinset).1 hj')]

noncomputable def pnatInterleaveEquiv : ℕ+ ≃ ℕ+ ⊕ ℕ+ :=
  Equiv.pnatEquivNat.trans
    (Equiv.natSumNatEquivNat.symm.trans
      ((Equiv.pnatEquivNat.symm).sumCongr Equiv.pnatEquivNat.symm))

lemma hasFiniteMulSupport_interleave {M : Type*} [One M]
    {a b : ℕ+ → M}
    (ha : Function.HasFiniteMulSupport a)
    (hb : Function.HasFiniteMulSupport b) :
    Function.HasFiniteMulSupport
      (fun n : ℕ+ ↦ Sum.elim a b (pnatInterleaveEquiv n)) := by
  classical
  have hsum : Function.HasFiniteMulSupport (Sum.elim a b) := by
    apply (Set.Finite.union
      (Set.Finite.image (α:=ℕ+) (s:=Function.mulSupport a) Sum.inl ha)
      (Set.Finite.image (α:=ℕ+) (s:=Function.mulSupport b) Sum.inr hb)).subset
    intro x hx
    cases x with
    | inl i =>
        exact Set.mem_union_left _ ⟨i, (Function.mem_mulSupport).1 hx, rfl⟩
    | inr j =>
        exact Set.mem_union_right _ ⟨j, (Function.mem_mulSupport).1 hx, rfl⟩
  simpa [Function.comp_def] using hsum.fun_comp_of_injective pnatInterleaveEquiv.injective

lemma finprod_interleave {M : Type*} [CommMonoid M]
    {a b : ℕ+ → M}
    (ha : Function.HasFiniteMulSupport a)
    (hb : Function.HasFiniteMulSupport b) :
    (∏ᶠ n : ℕ+, Sum.elim a b (pnatInterleaveEquiv n)) =
      (∏ᶠ n, a n) * ∏ᶠ n, b n := by
  exact (finprod_comp (g := Sum.elim a b) pnatInterleaveEquiv
    pnatInterleaveEquiv.bijective).trans (finprod_sum_elim a b ha hb)

lemma finite_range_apply_of_hasFiniteMulSupport {M : Type*} [One M]
    {a : ℕ+ → M} (ha : Function.HasFiniteMulSupport a) (f : M → ℝ) :
    Set.Finite (Set.range fun n : ℕ+ ↦ f (a n)) := by
  classical
  apply (Set.Finite.union
    (Set.Finite.image (α:=ℕ+) (β:=ℝ) (s:=Function.mulSupport a)
      (fun n : ℕ+ ↦ f (a n)) ha)
    (Set.finite_singleton (f 1))).subset
  rintro y ⟨n, rfl⟩
  by_cases hn : a n = 1
  · exact Set.mem_union_right _ (by simpa [hn])
  · exact Set.mem_union_left _
      (Set.mem_image_of_mem (fun m : ℕ+ ↦ f (a m)) ((Function.mem_mulSupport).2 hn))

lemma bddAbove_range_apply_of_hasFiniteMulSupport {M : Type*} [One M]
    {a : ℕ+ → M} (ha : Function.HasFiniteMulSupport a) (f : M → ℝ) :
    BddAbove (Set.range fun n : ℕ+ ↦ f (a n)) :=
  (finite_range_apply_of_hasFiniteMulSupport ha f).bddAbove

/- accepted add_to_file helper 2 -/
lemma sSup_range_interleave {G : Type*} [One G]
    {a b : ℕ+ → G}
    (ha : Function.HasFiniteMulSupport a)
    (hb : Function.HasFiniteMulSupport b)
    (f : G → ℝ) :
    sSup (Set.range fun n : ℕ+ ↦
        f (Sum.elim a b (pnatInterleaveEquiv n))) =
      max (sSup (Set.range fun n : ℕ+ ↦ f (a n)))
        (sSup (Set.range fun n : ℕ+ ↦ f (b n))) := by
  classical
  let e := pnatInterleaveEquiv
  have hrange :
      Set.range (fun n : ℕ+ ↦ f (Sum.elim a b (e n))) =
        Set.range (fun n : ℕ+ ↦ f (a n)) ∪
          Set.range (fun n : ℕ+ ↦ f (b n)) := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      cases he : e n with
      | inl i =>
          exact Or.inl ⟨i, by simpa [he]⟩
      | inr j =>
          exact Or.inr ⟨j, by simpa [he]⟩
    · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
      · obtain ⟨n, hn⟩ := e.surjective (Sum.inl i)
        exact ⟨n, by simp [hn]⟩
      · obtain ⟨n, hn⟩ := e.surjective (Sum.inr j)
        exact ⟨n, by simp [hn]⟩
  rw [hrange]
  rw [csSup_union
    (bddAbove_range_apply_of_hasFiniteMulSupport ha f)
    (Set.range_nonempty _)
    (bddAbove_range_apply_of_hasFiniteMulSupport hb f)
    (Set.range_nonempty _)]

/- accepted add_to_file helper 3 -/
def pnatSingle {M : Type*} [One M] (x : M) : ℕ+ → M :=
  fun n ↦ if n = 1 then x else 1

lemma hasFiniteMulSupport_pnatSingle {M : Type*} [One M] (x : M) :
    Function.HasFiniteMulSupport (pnatSingle x) := by
  classical
  apply (Set.finite_singleton (1 : ℕ+)).subset
  intro n hn
  by_cases h : n = 1
  · simpa [h]
  · exfalso
    exact hn (by simp [pnatSingle, h])

lemma finprod_pnatSingle {M : Type*} [CommMonoid M] (x : M) :
    (∏ᶠ n : ℕ+, pnatSingle x n) = x := by
  classical
  have hsub : Function.mulSupport (pnatSingle x) ⊆ ↑({1} : Finset ℕ+) := by
    intro n hn
    by_cases h : n = 1
    · simpa [h]
    · exfalso
      exact hn (by simp [pnatSingle, h])
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  simp [pnatSingle]

lemma sSup_range_apply_pnatSingle {G : Type*} [One G]
    (f : G → ℝ) (x : G)
    (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) :
    sSup (Set.range fun n : ℕ+ ↦ f (pnatSingle x n)) = f x := by
  classical
  have hrange : Set.range (fun n : ℕ+ ↦ f (pnatSingle x n)) = {f x, f 1} := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      by_cases h : n = 1
      · simp [pnatSingle, h]
      · simp [pnatSingle, h]
    · rintro (rfl | rfl)
      · exact ⟨1, by simp [pnatSingle]⟩
      · exact ⟨2, by simp [pnatSingle]⟩
  rw [hrange, csSup_pair]
  have h : f 1 ≤ f x := by simpa [hf_one] using hf_lower x
  exact max_eq_left h

/- accepted add_to_file helper 4 -/
noncomputable abbrev heightEnvOne {G : Type*} [CommMonoid G] (f : G → ℝ) (α : G) : ℝ :=
  sInf {r : ℝ | ∃ a : ℕ+ → G,
    Function.HasFiniteMulSupport a ∧
    (∏ᶠ n, a n) = α ∧
    (∏ᶠ n, f (a n)) = r}

noncomputable abbrev heightEnvInf {G : Type*} [CommMonoid G] (f : G → ℝ) (α : G) : ℝ :=
  sInf {r : ℝ | ∃ a : ℕ+ → G,
    Function.HasFiniteMulSupport a ∧
    (∏ᶠ n, a n) = α ∧
    sSup (Set.range fun n : ℕ+ ↦ f (a n)) = r}

lemma one_le_finprod_apply_of_hasFiniteMulSupport {G : Type*} [One G]
    {a : ℕ+ → G} (ha : Function.HasFiniteMulSupport a)
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) :
    1 ≤ ∏ᶠ n : ℕ+, f (a n) := by
  classical
  let s := ha.toFinset
  have hsub : Function.mulSupport (fun n : ℕ+ ↦ f (a n)) ⊆ ↑s := by
    intro n hn
    have hnfa : f (a n) ≠ 1 := (Function.mem_mulSupport).1 hn
    by_contra hns
    have hna : a n = 1 := by
      by_contra hna
      exact hns (by
        have : n ∈ ha.toFinset := (ha.mem_toFinset).2 ((Function.mem_mulSupport).2 hna)
        simpa [s] using this)
    exact hnfa (by simp [hna, hf_one])
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  exact Finset.one_le_prod (fun n _ ↦ hf_lower (a n))

lemma one_le_sSup_range_apply_of_hasFiniteMulSupport {G : Type*} [One G]
    {a : ℕ+ → G} (ha : Function.HasFiniteMulSupport a)
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) :
    1 ≤ sSup (Set.range fun n : ℕ+ ↦ f (a n)) := by
  classical
  obtain ⟨n, hn⟩ := ha.exists_notMem
  have han : a n = 1 := by
    by_contra h
    exact hn ((Function.mem_mulSupport).2 h)
  have hmem : f (a n) ∈ Set.range fun n : ℕ+ ↦ f (a n) := ⟨n, rfl⟩
  have hle := le_csSup (bddAbove_range_apply_of_hasFiniteMulSupport ha f) hmem
  simpa [han, hf_one] using hle

lemma heightEnvOne_nonempty {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    {r : ℝ | ∃ a : ℕ+ → G,
      Function.HasFiniteMulSupport a ∧
      (∏ᶠ n, a n) = α ∧
      (∏ᶠ n, f (a n)) = r}.Nonempty := by
  classical
  refine ⟨f α, pnatSingle α, hasFiniteMulSupport_pnatSingle α,
    finprod_pnatSingle α, ?_⟩
  have hsub : Function.mulSupport (fun n : ℕ+ ↦ f (pnatSingle α n)) ⊆
      ↑({1} : Finset ℕ+) := by
    intro n hn
    by_cases h : n = 1
    · simpa [h]
    · exfalso
      exact (Function.mem_mulSupport).1 hn (by simp [pnatSingle, h, hf_one])
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  simp [pnatSingle]

lemma heightEnvInf_nonempty {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    {r : ℝ | ∃ a : ℕ+ → G,
      Function.HasFiniteMulSupport a ∧
      (∏ᶠ n, a n) = α ∧
      sSup (Set.range fun n : ℕ+ ↦ f (a n)) = r}.Nonempty := by
  exact ⟨f α, pnatSingle α, hasFiniteMulSupport_pnatSingle α,
    finprod_pnatSingle α, sSup_range_apply_pnatSingle f α hf_lower hf_one⟩

/- accepted add_to_file helper 5 -/
lemma heightEnvOne_bddBelow {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    BddBelow {r : ℝ | ∃ a : ℕ+ → G,
      Function.HasFiniteMulSupport a ∧
      (∏ᶠ n, a n) = α ∧
      (∏ᶠ n, f (a n)) = r} := by
  refine ⟨1, ?_⟩
  rintro r ⟨a, ha, -, hprod⟩
  rw [← hprod]
  exact one_le_finprod_apply_of_hasFiniteMulSupport ha f hf_lower hf_one

lemma heightEnvInf_bddBelow {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    BddBelow {r : ℝ | ∃ a : ℕ+ → G,
      Function.HasFiniteMulSupport a ∧
      (∏ᶠ n, a n) = α ∧
      sSup (Set.range fun n : ℕ+ ↦ f (a n)) = r} := by
  refine ⟨1, ?_⟩
  rintro r ⟨a, ha, -, hsup⟩
  rw [← hsup]
  exact one_le_sSup_range_apply_of_hasFiniteMulSupport ha f hf_lower hf_one

lemma one_le_heightEnvInf {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    1 ≤ heightEnvInf f α := by
  apply le_csInf (heightEnvInf_nonempty f hf_lower hf_one α)
  rintro r ⟨a, ha, -, hsup⟩
  rw [← hsup]
  exact one_le_sSup_range_apply_of_hasFiniteMulSupport ha f hf_lower hf_one

lemma heightEnvInf_le_self {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    heightEnvInf f α ≤ f α := by
  apply csInf_le (heightEnvInf_bddBelow f hf_lower hf_one α)
  exact ⟨pnatSingle α, hasFiniteMulSupport_pnatSingle α, finprod_pnatSingle α,
    sSup_range_apply_pnatSingle f α hf_lower hf_one⟩

/- accepted add_to_file helper 6 -/
lemma heightEnvInf_le_inv_of_inv {G : Type*} [CommGroup G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1)
    (hf_inv : ∀ α : G, f α⁻¹ = f α) (α : G) :
    heightEnvInf f α⁻¹ ≤ heightEnvInf f α := by
  apply le_csInf (heightEnvInf_nonempty f hf_lower hf_one α)
  rintro r ⟨a, ha, hprod, hsup⟩
  apply csInf_le (heightEnvInf_bddBelow f hf_lower hf_one α⁻¹)
  refine ⟨a⁻¹, ha.inv, ?_, ?_⟩
  · change (∏ᶠ n : ℕ+, (a n)⁻¹) = α⁻¹
    rw [finprod_inv_distrib, hprod]
  · rw [← hsup]
    congr 1
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, by simp [hf_inv]⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, by simp [hf_inv]⟩

lemma heightEnvInf_inv {G : Type*} [CommGroup G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1)
    (hf_inv : ∀ α : G, f α⁻¹ = f α) (α : G) :
    heightEnvInf f α⁻¹ = heightEnvInf f α := by
  apply le_antisymm
  · exact heightEnvInf_le_inv_of_inv f hf_lower hf_one hf_inv α
  · simpa using heightEnvInf_le_inv_of_inv f hf_lower hf_one hf_inv α⁻¹

lemma heightEnvInf_one {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) :
    heightEnvInf f 1 = 1 := by
  apply le_antisymm
  · simpa [hf_one] using heightEnvInf_le_self f hf_lower hf_one (1 : G)
  · exact one_le_heightEnvInf f hf_lower hf_one 1

/- accepted add_to_file helper 7 -/
lemma heightEnvInf_mul {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1)
    (α β : G) :
    heightEnvInf f (α * β) ≤ max (heightEnvInf f α) (heightEnvInf f β) := by
  classical
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨r, ⟨a, ha, hpa, hsa⟩, hrlt⟩ :=
    exists_lt_of_csInf_lt (heightEnvInf_nonempty f hf_lower hf_one α)
      (lt_add_of_pos_right (heightEnvInf f α) hε)
  obtain ⟨s, ⟨b, hb, hpb, hsb⟩, hslt⟩ :=
    exists_lt_of_csInf_lt (heightEnvInf_nonempty f hf_lower hf_one β)
      (lt_add_of_pos_right (heightEnvInf f β) hε)
  let c : ℕ+ → G := fun n ↦ Sum.elim a b (pnatInterleaveEquiv n)
  have hc : Function.HasFiniteMulSupport c := hasFiniteMulSupport_interleave ha hb
  have hprod : (∏ᶠ n, c n) = α * β := by
    rw [finprod_interleave ha hb, hpa, hpb]
  have hsup : sSup (Set.range fun n : ℕ+ ↦ f (c n)) = max r s := by
    rw [← hsa, ← hsb]
    exact sSup_range_interleave ha hb f
  have hupper : heightEnvInf f (α * β) ≤ max r s := by
    apply csInf_le (heightEnvInf_bddBelow f hf_lower hf_one (α * β))
    exact ⟨c, hc, hprod, hsup⟩
  have hlt : max r s < max (heightEnvInf f α) (heightEnvInf f β) + ε := by
    calc
      max r s < max (heightEnvInf f α + ε) (heightEnvInf f β + ε) :=
        max_lt_max hrlt hslt
      _ = max (heightEnvInf f α) (heightEnvInf f β) + ε := max_add_add_right _ _ _
  exact hupper.trans hlt.le

/- accepted add_to_file helper 8 -/
lemma single_le_finset_prod_of_one_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → ℝ) (hg : ∀ i, 1 ≤ g i)
    {i : ι} (hi : i ∈ s) :
    g i ≤ ∏ j ∈ s, g j := by
  have hrest : 1 ≤ ∏ j ∈ s.erase i, g j :=
    Finset.one_le_prod (fun j _ ↦ hg j)
  have hgi0 : 0 ≤ g i := zero_le_one.trans (hg i)
  calc
    g i ≤ g i * ∏ j ∈ s.erase i, g j := le_mul_of_one_le_right hgi0 hrest
    _ = ∏ j ∈ s, g j := Finset.mul_prod_erase s g hi

lemma sSup_range_apply_le_finprod_apply_of_hasFiniteMulSupport {G : Type*} [One G]
    {a : ℕ+ → G} (ha : Function.HasFiniteMulSupport a)
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) :
    sSup (Set.range fun n : ℕ+ ↦ f (a n)) ≤ ∏ᶠ n : ℕ+, f (a n) := by
  classical
  let s := ha.toFinset
  have hsub : Function.mulSupport (fun n : ℕ+ ↦ f (a n)) ⊆ ↑s := by
    intro n hn
    have hnfa : f (a n) ≠ 1 := (Function.mem_mulSupport).1 hn
    by_contra hns
    have hna : a n = 1 := by
      by_contra hna
      exact hns (by
        have : n ∈ ha.toFinset := (ha.mem_toFinset).2 ((Function.mem_mulSupport).2 hna)
        simpa [s] using this)
    exact hnfa (by simp [hna, hf_one])
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨n, rfl⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  by_cases hn : a n = 1
  · change f (a n) ≤ ∏ i ∈ s, f (a i)
    rw [hn, hf_one]
    exact Finset.one_le_prod (fun m _ ↦ hf_lower (a m))
  · have hns : n ∈ s := by
      have : n ∈ ha.toFinset := (ha.mem_toFinset).2 ((Function.mem_mulSupport).2 hn)
      simpa [s] using this
    exact single_le_finset_prod_of_one_le s (fun m ↦ f (a m))
      (fun m ↦ hf_lower (a m)) hns

lemma heightEnvInf_le_heightEnvOne {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    heightEnvInf f α ≤ heightEnvOne f α := by
  apply le_csInf (heightEnvOne_nonempty f hf_lower hf_one α)
  rintro r ⟨a, ha, hprod, hval⟩
  rw [← hval]
  have hInf_le_sup : heightEnvInf f α ≤ sSup (Set.range fun n : ℕ+ ↦ f (a n)) := by
    apply csInf_le (heightEnvInf_bddBelow f hf_lower hf_one α)
    exact ⟨a, ha, hprod, rfl⟩
  exact hInf_le_sup.trans
    (sSup_range_apply_le_finprod_apply_of_hasFiniteMulSupport ha f hf_lower hf_one)

/- accepted add_to_file helper 9 -/
lemma strong_apply_finprod_le_sSup_range_apply {G : Type*} [CommMonoid G]
    {a : ℕ+ → G} (ha : Function.HasFiniteMulSupport a)
    (σ : G → ℝ) (hσ_lower : ∀ α : G, 1 ≤ σ α) (hσ_one : σ 1 = 1)
    (hσ_mul : ∀ α β : G, σ (α * β) ≤ max (σ α) (σ β)) :
    σ (∏ᶠ n : ℕ+, a n) ≤ sSup (Set.range fun n : ℕ+ ↦ σ (a n)) := by
  classical
  let s := ha.toFinset
  have hsub : Function.mulSupport a ⊆ ↑s := by
    intro n hn
    have : n ∈ ha.toFinset := (ha.mem_toFinset).2 hn
    simpa [s] using this
  rw [finprod_eq_prod_of_mulSupport_subset a hsub]
  have hbdd : BddAbove (Set.range fun n : ℕ+ ↦ σ (a n)) :=
    bddAbove_range_apply_of_hasFiniteMulSupport ha σ
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty]
      obtain ⟨n, hn⟩ := ha.exists_notMem
      have han : a n = 1 := by
        by_contra h
        exact hn ((Function.mem_mulSupport).2 h)
      exact le_csSup hbdd ⟨n, by simp [han]⟩
  | insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (hσ_mul (a i) (∏ x ∈ s, a x)).trans
        (max_le (le_csSup hbdd ⟨i, rfl⟩) ih)

lemma sSup_range_mono {G : Type*} [One G]
    {a : ℕ+ → G} (ha : Function.HasFiniteMulSupport a)
    {σ f : G → ℝ} (hσf : ∀ α : G, σ α ≤ f α) :
    sSup (Set.range fun n : ℕ+ ↦ σ (a n)) ≤
      sSup (Set.range fun n : ℕ+ ↦ f (a n)) := by
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨n, rfl⟩
  exact (hσf (a n)).trans
    (le_csSup (bddAbove_range_apply_of_hasFiniteMulSupport ha f) ⟨n, rfl⟩)

lemma strong_le_heightEnvInf {G : Type*} [CommMonoid G]
    (σ f : G → ℝ)
    (hσ_lower : ∀ α : G, 1 ≤ σ α) (hσ_one : σ 1 = 1)
    (hσ_mul : ∀ α β : G, σ (α * β) ≤ max (σ α) (σ β))
    (hσf : ∀ α : G, σ α ≤ f α)
    (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    σ α ≤ heightEnvInf f α := by
  apply le_csInf (heightEnvInf_nonempty f hf_lower hf_one α)
  rintro r ⟨a, ha, hprod, hsup⟩
  rw [← hsup]
  calc
    σ α = σ (∏ᶠ n : ℕ+, a n) := by rw [hprod]
    _ ≤ sSup (Set.range fun n : ℕ+ ↦ σ (a n)) :=
      strong_apply_finprod_le_sSup_range_apply ha σ hσ_lower hσ_one hσ_mul
    _ ≤ sSup (Set.range fun n : ℕ+ ↦ f (a n)) := sSup_range_mono ha hσf

/- accepted add_to_file helper 10 -/
lemma heightEnvOne_le_self {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    heightEnvOne f α ≤ f α := by
  classical
  apply csInf_le (heightEnvOne_bddBelow f hf_lower hf_one α)
  refine ⟨pnatSingle α, hasFiniteMulSupport_pnatSingle α, finprod_pnatSingle α, ?_⟩
  have hsub : Function.mulSupport (fun n : ℕ+ ↦ f (pnatSingle α n)) ⊆
      ↑({1} : Finset ℕ+) := by
    intro n hn
    by_cases h : n = 1
    · simpa [h]
    · exfalso
      exact (Function.mem_mulSupport).1 hn (by simp [pnatSingle, h, hf_one])
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  simp [pnatSingle]

lemma one_le_heightEnvOne {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    1 ≤ heightEnvOne f α := by
  apply le_csInf (heightEnvOne_nonempty f hf_lower hf_one α)
  rintro r ⟨a, ha, -, hprod⟩
  rw [← hprod]
  exact one_le_finprod_apply_of_hasFiniteMulSupport ha f hf_lower hf_one

lemma heightEnvOne_one {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) :
    heightEnvOne f 1 = 1 := by
  apply le_antisymm
  · simpa [hf_one] using heightEnvOne_le_self f hf_lower hf_one (1 : G)
  · exact one_le_heightEnvOne f hf_lower hf_one 1

lemma heightEnvInf_eq_self_of_strong {G : Type*} [CommMonoid G]
    (f : G → ℝ)
    (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1)
    (hf_mul : ∀ α β : G, f (α * β) ≤ max (f α) (f β)) :
    heightEnvInf f = f := by
  funext α
  apply le_antisymm
  · exact heightEnvInf_le_self f hf_lower hf_one α
  · exact strong_le_heightEnvInf f f hf_lower hf_one hf_mul
      (fun β ↦ le_rfl) hf_lower hf_one α

lemma heightEnvOne_eq_self_of_strong {G : Type*} [CommMonoid G]
    (f : G → ℝ)
    (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1)
    (hf_mul : ∀ α β : G, f (α * β) ≤ max (f α) (f β)) :
    heightEnvOne f = f := by
  funext α
  apply le_antisymm
  · exact heightEnvOne_le_self f hf_lower hf_one α
  · calc
      f α = heightEnvInf f α := by
        rw [heightEnvInf_eq_self_of_strong f hf_lower hf_one hf_mul]
      _ ≤ heightEnvOne f α := heightEnvInf_le_heightEnvOne f hf_lower hf_one α

lemma heightEnvInf_mono {G : Type*} [CommMonoid G]
    {f g : G → ℝ}
    (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1)
    (hg_lower : ∀ α : G, 1 ≤ g α) (hg_one : g 1 = 1)
    (hfg : ∀ α : G, f α ≤ g α) (α : G) :
    heightEnvInf f α ≤ heightEnvInf g α := by
  apply le_csInf (heightEnvInf_nonempty g hg_lower hg_one α)
  rintro r ⟨a, ha, hprod, hsup⟩
  rw [← hsup]
  have hleft : heightEnvInf f α ≤ sSup (Set.range fun n : ℕ+ ↦ f (a n)) := by
    apply csInf_le (heightEnvInf_bddBelow f hf_lower hf_one α)
    exact ⟨a, ha, hprod, rfl⟩
  exact hleft.trans (sSup_range_mono ha hfg)

lemma heightEnvInf_heightEnvOne_eq_heightEnvInf {G : Type*} [CommMonoid G]
    (f : G → ℝ)
    (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) :
    heightEnvInf f = heightEnvInf (heightEnvOne f) := by
  funext α
  apply le_antisymm
  · exact strong_le_heightEnvInf (heightEnvInf f) (heightEnvOne f)
      (one_le_heightEnvInf f hf_lower hf_one)
      (heightEnvInf_one f hf_lower hf_one)
      (heightEnvInf_mul f hf_lower hf_one)
      (heightEnvInf_le_heightEnvOne f hf_lower hf_one)
      (one_le_heightEnvOne f hf_lower hf_one)
      (heightEnvOne_one f hf_lower hf_one)
      α
  · exact heightEnvInf_mono
      (one_le_heightEnvOne f hf_lower hf_one)
      (heightEnvOne_one f hf_lower hf_one)
      hf_lower hf_one
      (heightEnvOne_le_self f hf_lower hf_one) α

/- verified submission -/
theorem strongMetricEnvelopeOfHeight
    {G : Type*} [CommGroup G] (ρ : G → ℝ)
    (hρ_lower : ∀ α : G, 1 ≤ ρ α)
    (hρ_one : ρ 1 = 1)
    (hρ_inv : ∀ α : G, ρ α⁻¹ = ρ α) :
    let envelopeOne : (G → ℝ) → G → ℝ := fun f α ↦
      sInf {r : ℝ | ∃ a : ℕ+ → G,
        Function.HasFiniteMulSupport a ∧
        (∏ᶠ n, a n) = α ∧
        (∏ᶠ n, f (a n)) = r}
    let envelopeInf : (G → ℝ) → G → ℝ := fun f α ↦
      sInf {r : ℝ | ∃ a : ℕ+ → G,
        Function.HasFiniteMulSupport a ∧
        (∏ᶠ n, a n) = α ∧
        sSup (Set.range fun n : ℕ+ ↦ f (a n)) = r}
    ((∀ α : G, 1 ≤ envelopeInf ρ α) ∧
      envelopeInf ρ 1 = 1 ∧
      (∀ α : G, envelopeInf ρ α⁻¹ = envelopeInf ρ α) ∧
      (∀ α β : G,
        envelopeInf ρ (α * β) ≤ max (envelopeInf ρ α) (envelopeInf ρ β))) ∧
    (∀ α : G, envelopeInf ρ α ≤ envelopeOne ρ α) ∧
    (∀ σ : G → ℝ,
      ((∀ α : G, 1 ≤ σ α) ∧
        σ 1 = 1 ∧
        (∀ α : G, σ α⁻¹ = σ α) ∧
        (∀ α β : G, σ (α * β) ≤ max (σ α) (σ β))) →
      (∀ α : G, σ α ≤ ρ α) →
      ∀ α : G, σ α ≤ envelopeInf ρ α) ∧
    (ρ = envelopeInf ρ ↔
      (∀ α : G, 1 ≤ ρ α) ∧
      ρ 1 = 1 ∧
      (∀ α : G, ρ α⁻¹ = ρ α) ∧
      (∀ α β : G, ρ (α * β) ≤ max (ρ α) (ρ β))) ∧
    (envelopeInf ρ = envelopeInf (envelopeOne ρ) ∧
      envelopeInf (envelopeOne ρ) = envelopeOne (envelopeInf ρ) ∧
      envelopeOne (envelopeInf ρ) = envelopeInf (envelopeInf ρ)) := by
  refine ⟨⟨one_le_heightEnvInf ρ hρ_lower hρ_one,
    heightEnvInf_one ρ hρ_lower hρ_one,
    heightEnvInf_inv ρ hρ_lower hρ_one hρ_inv,
    heightEnvInf_mul ρ hρ_lower hρ_one⟩,
    heightEnvInf_le_heightEnvOne ρ hρ_lower hρ_one,
    ?_, ?_, ?_⟩
  · intro σ hσ hσρ α
    rcases hσ with ⟨hσ_lower, hσ_one, -, hσ_mul⟩
    exact strong_le_heightEnvInf σ ρ hσ_lower hσ_one hσ_mul hσρ
      hρ_lower hρ_one α
  · constructor
    · intro h
      refine ⟨hρ_lower, hρ_one, hρ_inv, ?_⟩
      intro α β
      rw [h]
      exact heightEnvInf_mul ρ hρ_lower hρ_one α β
    · rintro ⟨hρ_lower', hρ_one', -, hρ_mul⟩
      exact (heightEnvInf_eq_self_of_strong ρ hρ_lower' hρ_one' hρ_mul).symm
  · refine ⟨heightEnvInf_heightEnvOne_eq_heightEnvInf ρ hρ_lower hρ_one, ?_, ?_⟩
    · have h₁ := heightEnvInf_heightEnvOne_eq_heightEnvInf ρ hρ_lower hρ_one
      have h₂ := heightEnvOne_eq_self_of_strong (heightEnvInf ρ)
        (one_le_heightEnvInf ρ hρ_lower hρ_one)
        (heightEnvInf_one ρ hρ_lower hρ_one)
        (heightEnvInf_mul ρ hρ_lower hρ_one)
      exact h₁.symm.trans h₂.symm
    · have h₁ := heightEnvOne_eq_self_of_strong (heightEnvInf ρ)
        (one_le_heightEnvInf ρ hρ_lower hρ_one)
        (heightEnvInf_one ρ hρ_lower hρ_one)
        (heightEnvInf_mul ρ hρ_lower hρ_one)
      have h₂ := heightEnvInf_eq_self_of_strong (heightEnvInf ρ)
        (one_le_heightEnvInf ρ hρ_lower hρ_one)
        (heightEnvInf_one ρ hρ_lower hρ_one)
        (heightEnvInf_mul ρ hρ_lower hρ_one)
      exact h₁.trans h₂.symm

end Rollout_p2227_strongmetricenvelopeofheight

#check_dependency_graph "Rollout_p2227_strongmetricenvelopeofheight.strongMetricEnvelopeOfHeight" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"((∀ (α : G), 1 ≤ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ α) ∧ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ 1 = 1 ∧ (∀ (α : G), (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ α⁻¹ = (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ α) ∧ ∀ (α β : G), (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ (α * β) ≤ max ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ α) ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ β)) ∧ (∀ (α : G), (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ α ≤ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ ∏ᶠ (n : ℕ+), f (a n) = r}) ρ α) ∧ (∀ (σ : G → ℝ), ((∀ (α : G), 1 ≤ σ α) ∧ σ 1 = 1 ∧ (∀ (α : G), σ α⁻¹ = σ α) ∧ ∀ (α β : G), σ (α * β) ≤ max (σ α) (σ β)) → (∀ (α : G), σ α ≤ ρ α) → ∀ (α : G), σ α ≤ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ α) ∧ (ρ = (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ ↔ (∀ (α : G), 1 ≤ ρ α) ∧ ρ 1 = 1 ∧ (∀ (α : G), ρ α⁻¹ = ρ α) ∧ ∀ (α β : G), ρ (α * β) ≤ max (ρ α) (ρ β)) ∧ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ = (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ ∏ᶠ (n : ℕ+), f (a n) = r}) ρ) ∧ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ ∏ᶠ (n : ℕ+), f (a n) = r}) ρ) = (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ ∏ᶠ (n : ℕ+), f (a n) = r}) ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ) ∧ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ ∏ᶠ (n : ℕ+), f (a n) = r}) ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ) = (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hρ_lower\",\"statement\":\"∀ (α : G), 1 ≤ ρ α\"},{\"name\":\"hρ_one\",\"statement\":\"ρ 1 = 1\"},{\"name\":\"hρ_inv\",\"statement\":\"∀ (α : G), ρ α⁻¹ = ρ α\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2227_strongmetricenvelopeofheight\",\"reconstructedProofSha256\":\"964d5827dbfe76c5223cd0228076320fa62b8063e8b6c94499060e9ec639c56f\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p2227_strongmetricenvelopeofheight.strongMetricEnvelopeOfHeight\",\"topologySha256\":\"0c7a7e1ae1d7e6f1a427f32a3d41f791bd3bd2dbc65bf4ed5fae4de7739626f6\"}"

namespace Rollout_p2247_sylow_rank_two_index_prime_subgroups

-- graph_id: p2247_sylow_rank_two_index_prime_subgroups
-- topology_sha256: 1c6ca46bbda1eeac93fb6cf04404be324d1119b830fc90bfd6f96fc2ea3164f9
/- accepted add_to_file helper 1 -/
lemma comm_isComplement'_of_sup_top_inf_bot {G : Type*} [CommGroup G] {H K : Subgroup G}
    (hs : H ⊔ K = ⊤) (hi : H ⊓ K = ⊥) : H.IsComplement' K := by
  unfold Subgroup.IsComplement'
  constructor
  · intro a b hab
    change ((a.1 : G) * a.2) = ((b.1 : G) * b.2) at hab
    have heq : ((a.1 : G)⁻¹ * b.1) = ((a.2 : G) * (b.2 : G)⁻¹) := by
      calc
        ((a.1 : G)⁻¹ * b.1)
            = ((a.1 : G)⁻¹ * ((b.1 : G) * b.2) * (b.2 : G)⁻¹) := by group
        _ = ((a.1 : G)⁻¹ * ((a.1 : G) * a.2) * (b.2 : G)⁻¹) := by rw [hab]
        _ = ((a.2 : G) * (b.2 : G)⁻¹) := by group
    have hmem : ((a.1 : G)⁻¹ * b.1) ∈ H ⊓ K := by
      rw [Subgroup.mem_inf]
      constructor
      · exact H.mul_mem (H.inv_mem a.1.property) b.1.property
      · rw [heq]
        exact K.mul_mem a.2.property (K.inv_mem b.2.property)
    have hone : ((a.1 : G)⁻¹ * b.1) = 1 := by
      exact (Subgroup.eq_bot_iff_forall (H ⊓ K)).mp hi _ hmem
    have h1 : (a.1 : G) = b.1 := inv_mul_eq_one.mp hone
    have h2 : (a.2 : G) = b.2 := by
      have hone2 : ((a.2 : G) * (b.2 : G)⁻¹) = 1 := by rw [← heq, hone]
      exact mul_inv_eq_one.mp hone2
    ext <;> assumption
  · intro g
    have hg : (g : G) ∈ H ⊔ K := by rw [hs]; exact Subgroup.mem_top g
    rw [Subgroup.mem_sup] at hg
    rcases hg with ⟨h, hh, k, hk, hhk⟩
    exact ⟨⟨⟨h, hh⟩, ⟨k, hk⟩⟩, by simpa using hhk⟩

/- accepted add_to_file helper 2 -/
def commSubgroupProdHom {G : Type*} [CommGroup G] (H K : Subgroup G) :
    H × K →* G where
  toFun p := (p.1 : G) * p.2
  map_one' := by simp
  map_mul' := by
    intro a b
    simp [mul_left_comm, mul_comm]

/- accepted add_to_file helper 3 -/
lemma commSubgroupProdHom_range {G : Type*} [CommGroup G] (H K : Subgroup G) :
    (commSubgroupProdHom H K).range = H ⊔ K := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨p, rfl⟩
    exact Subgroup.mul_mem_sup p.1.property p.2.property
  · intro hz
    rw [Subgroup.mem_sup] at hz
    rcases hz with ⟨h, hh, k, hk, hhk⟩
    exact ⟨⟨⟨h, hh⟩, ⟨k, hk⟩⟩, by simpa [commSubgroupProdHom] using hhk⟩

lemma commSubgroupProdHom_injective {G : Type*} [CommGroup G] {H K : Subgroup G}
    (hi : H ⊓ K = ⊥) : Function.Injective (commSubgroupProdHom H K) := by
  intro a b hab
  change ((a.1 : G) * a.2) = ((b.1 : G) * b.2) at hab
  have heq : ((a.1 : G)⁻¹ * b.1) = ((a.2 : G) * (b.2 : G)⁻¹) := by
    calc
      ((a.1 : G)⁻¹ * b.1)
          = ((a.1 : G)⁻¹ * ((b.1 : G) * b.2) * (b.2 : G)⁻¹) := by group
      _ = ((a.1 : G)⁻¹ * ((a.1 : G) * a.2) * (b.2 : G)⁻¹) := by rw [hab]
      _ = ((a.2 : G) * (b.2 : G)⁻¹) := by group
  have hmem : ((a.1 : G)⁻¹ * b.1) ∈ H ⊓ K := by
    rw [Subgroup.mem_inf]
    constructor
    · exact H.mul_mem (H.inv_mem a.1.property) b.1.property
    · rw [heq]
      exact K.mul_mem a.2.property (K.inv_mem b.2.property)
  have hone : ((a.1 : G)⁻¹ * b.1) = 1 := by
    exact (Subgroup.eq_bot_iff_forall (H ⊓ K)).mp hi _ hmem
  have h1 : (a.1 : G) = b.1 := inv_mul_eq_one.mp hone
  have h2 : (a.2 : G) = b.2 := by
    have hone2 : ((a.2 : G) * (b.2 : G)⁻¹) = 1 := by rw [← heq, hone]
    exact mul_inv_eq_one.mp hone2
  ext <;> assumption

/- accepted add_to_file helper 4 -/
lemma Nat_card_sup_of_inf_bot {G : Type*} [CommGroup G] {H K : Subgroup G}
    (hi : H ⊓ K = ⊥) : Nat.card ↥(H ⊔ K) = Nat.card ↥H * Nat.card ↥K := by
  let f := commSubgroupProdHom H K
  have hinj : Function.Injective f.rangeRestrict := by
    rw [MonoidHom.rangeRestrict_injective_iff]
    exact commSubgroupProdHom_injective hi
  have hbij : Function.Bijective f.rangeRestrict :=
    ⟨hinj, MonoidHom.rangeRestrict_surjective f⟩
  let e : (↥H × ↥K) ≃* f.range := MulEquiv.ofBijective f.rangeRestrict hbij
  calc
    Nat.card ↥(H ⊔ K) = Nat.card ↥f.range := by rw [commSubgroupProdHom_range]
    _ = Nat.card (↥H × ↥K) := (Nat.card_congr e.toEquiv).symm
    _ = Nat.card ↥H * Nat.card ↥K := Nat.card_prod ↥H ↥K

/- accepted add_to_file helper 5 -/
lemma orderOf_prime_pow_pow {G : Type*} [Group G] {p u k : ℕ}
    (hp : p.Prime) {x : G} (hx : orderOf x = p ^ u) (hku : k ≤ u) :
    orderOf (x ^ (p ^ k)) = p ^ (u - k) := by
  have hdvd : p ^ k ∣ orderOf x := by
    rw [hx]
    exact pow_dvd_pow p hku
  rw [orderOf_pow_of_dvd (pow_ne_zero k hp.ne_zero) hdvd, hx]
  exact Nat.pow_div hku hp.pos

/- accepted add_to_file helper 6 -/
lemma zpowers_pow_inf_zpowers_pow_eq_bot {G : Type*} [Group G] {x y : G}
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) (m n : ℕ) :
    Subgroup.zpowers (x ^ m) ⊓ Subgroup.zpowers (y ^ n) = ⊥ := by
  have hxm : Subgroup.zpowers (x ^ m) ≤ Subgroup.zpowers x := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.pow_mem (Subgroup.zpowers x) (Subgroup.mem_zpowers x) m
  have hyn : Subgroup.zpowers (y ^ n) ≤ Subgroup.zpowers y := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.pow_mem (Subgroup.zpowers y) (Subgroup.mem_zpowers y) n
  apply le_antisymm
  · calc
      Subgroup.zpowers (x ^ m) ⊓ Subgroup.zpowers (y ^ n)
          ≤ Subgroup.zpowers x ⊓ Subgroup.zpowers y := inf_le_inf hxm hyn
      _ = ⊥ := hind
  · exact bot_le

/- accepted add_to_file helper 7 -/
lemma product_eq_one_of_inf_bot {G : Type*} [CommGroup G] {H K : Subgroup G}
    (hi : H ⊓ K = ⊥) {a b : G} (ha : a ∈ H) (hb : b ∈ K)
    (h : a * b = 1) : a = 1 ∧ b = 1 := by
  let f := commSubgroupProdHom H K
  have hpair : (⟨⟨a, ha⟩, ⟨b, hb⟩⟩ : H × K) = 1 := by
    apply commSubgroupProdHom_injective hi
    simp [commSubgroupProdHom, h]
  constructor
  · exact congrArg (fun p : H × K => (p.1 : G)) hpair
  · exact congrArg (fun p : H × K => (p.2 : G)) hpair

/- accepted add_to_file helper 8 -/
lemma int_prime_pow_mul_dvd_mul_iff {p u : ℕ} (hp : p.Prime) (hu : 0 < u) {i : ℤ} :
    ((p ^ u : ℕ) : ℤ) ∣ i * p ↔ ((p ^ (u - 1) : ℕ) : ℤ) ∣ i := by
  have hpow : ((p ^ u : ℕ) : ℤ) = (p ^ (u - 1) : ℕ) * p := by
    calc
      ((p ^ u : ℕ) : ℤ) = ((p ^ (u - 1 + 1) : ℕ) : ℤ) := by rw [Nat.sub_add_cancel hu]
      _ = (p ^ (u - 1) : ℕ) * p := by rw [pow_succ, Nat.cast_mul]
  have hpz : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [hpow, Int.mul_dvd_mul_iff_right hpz]

/- accepted add_to_file helper 9 -/
lemma zpow_mem_zpowers_pow_of_dvd {G : Type*} [Group G] (x : G) {n : ℕ} {i : ℤ}
    (hd : (n : ℤ) ∣ i) : x ^ i ∈ Subgroup.zpowers (x ^ n) := by
  rcases hd with ⟨t, rfl⟩
  rw [zpow_mul]
  convert Subgroup.zpow_mem _ (Subgroup.mem_zpowers (x ^ n)) t using 2
  exact zpow_natCast x n

/- accepted add_to_file helper 10 -/
lemma pow_ker_eq_zpowers_sup {G : Type*} [CommGroup G]
    {p u v : ℕ} (hp : p.Prime) (hu : 0 < u) (hv : 0 < v)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p ^ v)
    (hspan : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    (powMonoidHom p : G →* G).ker =
      Subgroup.zpowers (x ^ (p ^ (u - 1))) ⊔
        Subgroup.zpowers (y ^ (p ^ (v - 1))) := by
  ext z
  constructor
  · intro hzker
    have hzpow : z ^ p = 1 := by simpa [powMonoidHom] using hzker
    have htop : z ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
      rw [hspan]
      exact Subgroup.mem_top z
    rw [Subgroup.mem_sup] at htop
    rcases htop with ⟨a, ha, b, hb, hab⟩
    rw [Subgroup.mem_zpowers_iff] at ha hb
    rcases ha with ⟨i, rfl⟩
    rcases hb with ⟨j, rfl⟩
    subst z
    have hzpowprod : x ^ (i * p) * y ^ (j * p) = 1 := by
      calc
        x ^ (i * p) * y ^ (j * p) = (x ^ i * y ^ j) ^ p := by
          calc
            x ^ (i * p) * y ^ (j * p) = (x ^ i * y ^ j) ^ (p : ℤ) := by
              rw [mul_zpow, ← zpow_mul, ← zpow_mul]
            _ = (x ^ i * y ^ j) ^ p := by rw [zpow_natCast]
        _ = 1 := hzpow
    have hone := product_eq_one_of_inf_bot hind
      (Subgroup.zpow_mem (Subgroup.zpowers x) (Subgroup.mem_zpowers x) _)
      (Subgroup.zpow_mem (Subgroup.zpowers y) (Subgroup.mem_zpowers y) _) hzpowprod
    have hdix : (orderOf x : ℤ) ∣ i * p := orderOf_dvd_iff_zpow_eq_one.mpr hone.1
    have hdiy : (orderOf y : ℤ) ∣ j * p := orderOf_dvd_iff_zpow_eq_one.mpr hone.2
    rw [hx] at hdix
    rw [hy] at hdiy
    have hiq : ((p ^ (u - 1) : ℕ) : ℤ) ∣ i := (int_prime_pow_mul_dvd_mul_iff hp hu).mp hdix
    have hjq : ((p ^ (v - 1) : ℕ) : ℤ) ∣ j := (int_prime_pow_mul_dvd_mul_iff hp hv).mp hdiy
    exact Subgroup.mul_mem_sup
      (zpow_mem_zpowers_pow_of_dvd x hiq)
      (zpow_mem_zpowers_pow_of_dvd y hjq)
  · intro hz
    rw [Subgroup.mem_sup] at hz
    rcases hz with ⟨a, ha, b, hb, hab⟩
    subst z
    have hxqord : orderOf (x ^ (p ^ (u - 1))) = p := by
      rw [orderOf_prime_pow_pow hp hx (Nat.sub_le u 1)]
      rw [show u - (u - 1) = 1 by omega, pow_one]
    have hyqord : orderOf (y ^ (p ^ (v - 1))) = p := by
      rw [orderOf_prime_pow_pow hp hy (Nat.sub_le v 1)]
      rw [show v - (v - 1) = 1 by omega, pow_one]
    have hadvd : orderOf a ∣ p := by
      rw [← hxqord]
      exact orderOf_dvd_of_mem_zpowers ha
    have hbdvd : orderOf b ∣ p := by
      rw [← hyqord]
      exact orderOf_dvd_of_mem_zpowers hb
    have hap : a ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp hadvd
    have hbp : b ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp hbdvd
    change (a * b) ^ p = 1
    rw [mul_pow, hap, hbp, one_mul]

/- accepted add_to_file helper 11 -/
lemma Nat_card_pow_ker {G : Type*} [CommGroup G]
    {p u v : ℕ} (hp : p.Prime) (hu : 0 < u) (hv : 0 < v)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p ^ v)
    (hspan : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    Nat.card ↥((powMonoidHom p : G →* G).ker) = p ^ 2 := by
  rw [pow_ker_eq_zpowers_sup hp hu hv hx hy hspan hind]
  rw [Nat_card_sup_of_inf_bot (zpowers_pow_inf_zpowers_pow_eq_bot hind _ _)]
  rw [Nat.card_zpowers, Nat.card_zpowers]
  have hxqord : orderOf (x ^ (p ^ (u - 1))) = p := by
    rw [orderOf_prime_pow_pow hp hx (Nat.sub_le u 1)]
    rw [show u - (u - 1) = 1 by omega, pow_one]
  have hyqord : orderOf (y ^ (p ^ (v - 1))) = p := by
    rw [orderOf_prime_pow_pow hp hy (Nat.sub_le v 1)]
    rw [show v - (v - 1) = 1 by omega, pow_one]
  rw [hxqord, hyqord]
  exact (pow_two p).symm

/- accepted add_to_file helper 12 -/
lemma Nat_card_of_zpowers_sup_top_inf_bot {G : Type*} [CommGroup G] {x y : G}
    (hspan : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    Nat.card G = orderOf x * orderOf y := by
  have hcomp := comm_isComplement'_of_sup_top_inf_bot hspan hind
  calc
    Nat.card G = Nat.card ↥(Subgroup.zpowers x) * Nat.card ↥(Subgroup.zpowers y) :=
      hcomp.card_mul.symm
    _ = orderOf x * orderOf y := by rw [Nat.card_zpowers, Nat.card_zpowers]

/- accepted add_to_file helper 13 -/
lemma subgroup_index_prime_iff_card_prime_of_card_sq {G : Type*} [Group G]
    {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ 2) (U : Subgroup G) :
    U.index = p ↔ Nat.card U = p := by
  have h := U.card_mul_index
  rw [hG, pow_two] at h
  constructor
  · intro hindex
    rw [hindex, mul_comm] at h
    exact Nat.mul_left_cancel hp.pos h
  · intro hcard
    rw [hcard] at h
    exact Nat.mul_left_cancel hp.pos h

/- accepted add_to_file helper 14 -/
lemma pow_mem_subgroup_of_index_eq {G : Type*} [CommGroup G]
    (U : Subgroup G) {p : ℕ} (hindex : U.index = p) (g : G) :
    g ^ p ∈ U := by
  letI := Subgroup.normal_of_comm U
  let q := QuotientGroup.mk' U
  have hqpow : (q g) ^ p = 1 := by
    have h := pow_card_eq_one' (x := q g)
    rwa [← U.index_eq_card, hindex] at h
  have hker : g ^ p ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hqpow
  rwa [QuotientGroup.ker_mk'] at hker

/- accepted add_to_file helper 15 -/
lemma subgroup_index_prime_iff_card_eq_of_card_pow_succ {G : Type*} [Group G]
    {p u : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ (u + 1)) (U : Subgroup G) :
    U.index = p ↔ Nat.card ↥U = p ^ u := by
  have h := U.card_mul_index
  rw [hG, pow_succ] at h
  have hpu : 0 < p ^ u := pow_pos hp.pos u
  constructor
  · intro hindex
    rw [hindex] at h
    exact Nat.mul_right_cancel hp.pos h
  · intro hcard
    rw [hcard] at h
    exact Nat.mul_left_cancel hpu h

/- accepted add_to_file helper 16 -/
lemma zpowers_x_pow_pred_le_zpowers_x_pow {G : Type*} [Group G]
    {p u : ℕ} (hu : 1 < u) (x : G) :
    Subgroup.zpowers (x ^ (p ^ (u - 1))) ≤ Subgroup.zpowers (x ^ p) := by
  rw [Subgroup.zpowers_le]
  rw [show u - 1 = (u - 2) + 1 by omega, pow_succ, mul_comm, pow_mul]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers (x ^ p)) _

/- accepted add_to_file helper 17 -/
lemma N_index_mem_unique_v1 {G : Type*} [CommGroup G] [Finite G]
    {p u v : ℕ} (hp : p.Prime) (hu : 0 < u) (hv : 0 < v)
    (hu1 : 1 < u) (hv1 : v = 1)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p ^ v)
    (hspan : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    let E : Subgroup G := (powMonoidHom p : G →* G).ker
    let N : Subgroup G := Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y
    N.index = p ∧ E ≤ N ∧
      (∀ U : Subgroup G, U.index = p → E ≤ U → U = N) := by
  intro E N
  have hE : E = Subgroup.zpowers (x ^ (p ^ (u - 1))) ⊔
      Subgroup.zpowers (y ^ (p ^ (v - 1))) :=
    pow_ker_eq_zpowers_sup hp hu hv hx hy hspan hind
  have hPcard : Nat.card G = p ^ (u + 1) := by
    rw [Nat_card_of_zpowers_sup_top_inf_bot hspan hind, hx, hy, hv1, pow_one, ← pow_succ]
  have hNcard : Nat.card ↥N = p ^ u := by
    dsimp [N]
    have hNinf : Subgroup.zpowers (x ^ p) ⊓ Subgroup.zpowers y = ⊥ := by
      simpa using zpowers_pow_inf_zpowers_pow_eq_bot hind p 1
    rw [Nat_card_sup_of_inf_bot hNinf]
    rw [Nat.card_zpowers, Nat.card_zpowers]
    have hordxp : orderOf (x ^ p) = p ^ (u - 1) := by
      simpa using orderOf_prime_pow_pow hp hx (k := 1) (by omega : 1 ≤ u)
    rw [hordxp, hy, hv1, pow_one]
    rw [← pow_succ]
    congr 1
    omega
  have hNindex : N.index = p :=
    (subgroup_index_prime_iff_card_eq_of_card_pow_succ hp hPcard N).mpr hNcard
  refine ⟨hNindex, ?_, ?_⟩
  · rw [hE, hv1]
    simp only [Nat.reduceSub, pow_zero, pow_one]
    apply sup_le
    · exact le_trans (zpowers_x_pow_pred_le_zpowers_x_pow hu1 x) le_sup_left
    · exact (le_sup_right : Subgroup.zpowers y ≤
        Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y)
  · intro U hUindex hEU
    have hyE : y ∈ E := by
      rw [hE, hv1]
      simp only [Nat.reduceSub, pow_zero, pow_one]
      exact (le_sup_right : Subgroup.zpowers y ≤
        Subgroup.zpowers (x ^ (p ^ (u - 1))) ⊔ Subgroup.zpowers y) (Subgroup.mem_zpowers y)
    have hyU : y ∈ U := hEU hyE
    have hxpU : x ^ p ∈ U := pow_mem_subgroup_of_index_eq U hUindex x
    have hNU : N ≤ U := by
      dsimp [N]
      apply sup_le
      · rwa [Subgroup.zpowers_le]
      · rwa [Subgroup.zpowers_le]
    have hUcard : Nat.card ↥U = p ^ u :=
      (subgroup_index_prime_iff_card_eq_of_card_pow_succ hp hPcard U).mp hUindex
    apply Eq.symm
    apply Subgroup.eq_of_le_of_card_ge hNU
    rw [hUcard, hNcard]

/- accepted add_to_file helper 18 -/
lemma orderOf_mul_zpow_right_v1 {G : Type*} [CommGroup G] [Finite G]
    {p u : ℕ} (hp : p.Prime) (hu : 0 < u)
    {x y : G} (hx : orderOf x = p ^ u) (hy : orderOf y = p)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) (k : ℤ) :
    orderOf (x * y ^ k) = p ^ u := by
  let z := x * y ^ k
  have hpow_formula : ∀ n : ℕ, z ^ n = x ^ n * y ^ (k * n) := by
    intro n
    calc
      z ^ n = (x * y ^ k) ^ (n : ℤ) := by rw [zpow_natCast]
      _ = x ^ (n : ℤ) * (y ^ k) ^ (n : ℤ) := by rw [mul_zpow]
      _ = x ^ n * y ^ (k * n) := by rw [zpow_natCast, ← zpow_mul]
  have hxupper : x ^ p ^ u = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hyupper : y ^ (k * ((p ^ u : ℕ) : ℤ)) = 1 := by
    have hfac : k * (((p ^ u : ℕ) : ℤ)) = (p : ℤ) * (k * (((p ^ (u - 1) : ℕ) : ℤ))) := by
      have hpow : (((p ^ u : ℕ) : ℤ)) = (p : ℤ) * (((p ^ (u - 1) : ℕ) : ℤ)) := by
        calc
          (((p ^ u : ℕ) : ℤ)) = (((p ^ (u - 1 + 1) : ℕ) : ℤ)) := by rw [Nat.sub_add_cancel hu]
          _ = (p : ℤ) * (((p ^ (u - 1) : ℕ) : ℤ)) := by
            rw [pow_succ, Nat.cast_mul, mul_comm]
      rw [hpow]
      ring
    rw [hfac, zpow_mul]
    have hyp : y ^ (p : ℤ) = 1 := by
      rw [zpow_natCast, ← hy]
      exact pow_orderOf_eq_one y
    rw [hyp, one_zpow]
  have hupper : z ^ p ^ u = 1 := by
    rw [hpow_formula, hxupper, hyupper, one_mul]
  have hle : orderOf z ≤ p ^ u :=
    orderOf_le_of_pow_eq_one (pow_pos hp.pos u) hupper
  have hge : p ^ u ≤ orderOf z := by
    have hzd : z ^ orderOf z = 1 := pow_orderOf_eq_one z
    rw [hpow_formula] at hzd
    have hone := product_eq_one_of_inf_bot hind
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _)
      (Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) _) hzd
    have hdvd : orderOf x ∣ orderOf z := orderOf_dvd_iff_pow_eq_one.mpr hone.1
    rw [hx] at hdvd
    exact Nat.le_of_dvd (orderOf_pos z) hdvd
  exact le_antisymm hle hge

/- accepted add_to_file helper 19 -/
lemma mul_zpow_right_pow_pred_eq_left {G : Type*} [CommGroup G]
    {p u : ℕ} (hu : 1 < u) {x y : G} (hy : orderOf y = p) (k : ℤ) :
    (x * y ^ k) ^ (p ^ (u - 1)) = x ^ (p ^ (u - 1)) := by
  let z := x * y ^ k
  have hpow_formula : ∀ n : ℕ, z ^ n = x ^ n * y ^ (k * n) := by
    intro n
    calc
      z ^ n = (x * y ^ k) ^ (n : ℤ) := by rw [zpow_natCast]
      _ = x ^ (n : ℤ) * (y ^ k) ^ (n : ℤ) := by rw [mul_zpow]
      _ = x ^ n * y ^ (k * n) := by rw [zpow_natCast, ← zpow_mul]
  have hyq : y ^ (k * (((p ^ (u - 1) : ℕ) : ℤ))) = 1 := by
    have hfac : k * (((p ^ (u - 1) : ℕ) : ℤ)) =
        (p : ℤ) * (k * (((p ^ (u - 2) : ℕ) : ℤ))) := by
      have hpow : (((p ^ (u - 1) : ℕ) : ℤ)) =
          (p : ℤ) * (((p ^ (u - 2) : ℕ) : ℤ)) := by
        calc
          (((p ^ (u - 1) : ℕ) : ℤ)) = (((p ^ ((u - 2) + 1) : ℕ) : ℤ)) := by
            congr 2
            omega
          _ = (p : ℤ) * (((p ^ (u - 2) : ℕ) : ℤ)) := by
            rw [pow_succ, Nat.cast_mul, mul_comm]
      rw [hpow]
      ring
    rw [hfac, zpow_mul]
    have hyp : y ^ (p : ℤ) = 1 := by
      rw [zpow_natCast, ← hy]
      exact pow_orderOf_eq_one y
    rw [hyp, one_zpow]
  calc
    (x * y ^ k) ^ (p ^ (u - 1)) = z ^ (p ^ (u - 1)) := rfl
    _ = x ^ (p ^ (u - 1)) * y ^ (k * (((p ^ (u - 1) : ℕ) : ℤ))) := hpow_formula _
    _ = x ^ (p ^ (u - 1)) := by rw [hyq, mul_one]

/- accepted add_to_file helper 20 -/
lemma cyclic_nonN_v1 {G : Type*} [CommGroup G] [Finite G]
    {p u v : ℕ} (hp : p.Prime) (hu : 0 < u) (hv : 0 < v)
    (hu1 : 1 < u) (hv1 : v = 1)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p ^ v)
    (hspan : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥)
    {U : Subgroup G} (hU : U.index = p)
    (hUN : U ≠ Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y) :
    let E : Subgroup G := (powMonoidHom p : G →* G).ker
    IsCyclic U ∧ Nat.card ↥U = p ^ u ∧
      U ⊓ E = Subgroup.zpowers (x ^ (p ^ (u - 1))) := by
  intro E
  let N : Subgroup G := Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y
  have hN := N_index_mem_unique_v1 hp hu hv hu1 hv1 hx hy hspan hind
  change N.index = p ∧ E ≤ N ∧ (∀ V : Subgroup G, V.index = p → E ≤ V → V = N) at hN
  have hE : E = Subgroup.zpowers (x ^ (p ^ (u - 1))) ⊔
      Subgroup.zpowers (y ^ (p ^ (v - 1))) :=
    pow_ker_eq_zpowers_sup hp hu hv hx hy hspan hind
  have hPcard : Nat.card G = p ^ (u + 1) := by
    rw [Nat_card_of_zpowers_sup_top_inf_bot hspan hind, hx, hy, hv1, pow_one, ← pow_succ]
  have hUcard : Nat.card ↥U = p ^ u :=
    (subgroup_index_prime_iff_card_eq_of_card_pow_succ hp hPcard U).mp hU
  have hyU : y ∉ U := by
    intro h
    have hEU : E ≤ U := by
      rw [hE, hv1]
      simp only [Nat.reduceSub, pow_zero, pow_one]
      apply sup_le
      · have hxpU : x ^ p ∈ U := pow_mem_subgroup_of_index_eq U hU x
        exact le_trans (zpowers_x_pow_pred_le_zpowers_x_pow hu1 x)
          ((Subgroup.zpowers_le).mpr hxpU)
      · exact (Subgroup.zpowers_le).mpr h
    exact hUN (hN.2.2 U hU hEU)
  letI : Fact p.Prime := ⟨hp⟩
  letI := Subgroup.normal_of_comm U
  let q : G →* G ⧸ U := QuotientGroup.mk' U
  have hQcard : Nat.card (G ⧸ U) = p := by rw [← U.index_eq_card, hU]
  have hqy : q y ≠ 1 := by
    intro h
    have hyker : y ∈ q.ker := by rw [MonoidHom.mem_ker]; exact h
    rw [QuotientGroup.ker_mk'] at hyker
    exact hyU hyker
  have hqxmem : q x ∈ Subgroup.zpowers (q y) :=
    mem_zpowers_of_prime_card hQcard hqy
  rw [Subgroup.mem_zpowers_iff] at hqxmem
  rcases hqxmem with ⟨i, hiq⟩
  let k : ℤ := -i
  let z : G := x * y ^ k
  have hzq : q z = 1 := by
    change q (x * y ^ (-i)) = 1
    rw [map_mul, map_zpow, ← hiq]
    simp
  have hzU : z ∈ U := by
    have hzker : z ∈ q.ker := by rw [MonoidHom.mem_ker]; exact hzq
    rw [QuotientGroup.ker_mk'] at hzker
    exact hzker
  have hy' : orderOf y = p := by simpa [hv1] using hy
  have hzorder : orderOf z = p ^ u :=
    orderOf_mul_zpow_right_v1 hp hu hx hy' hind k
  have hHzU : Subgroup.zpowers z ≤ U := (Subgroup.zpowers_le).mpr hzU
  have hUeq : U = Subgroup.zpowers z := by
    apply Eq.symm
    apply Subgroup.eq_of_le_of_card_ge hHzU
    rw [hUcard, Nat.card_zpowers, hzorder]
  have hA : Subgroup.zpowers (x ^ (p ^ (u - 1))) ≤ U ⊓ E := by
    apply le_inf
    · rw [hUeq, Subgroup.zpowers_le]
      rw [← mul_zpow_right_pow_pred_eq_left hu1 hy' k]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers z) _
    · rw [hE, hv1]
      simp only [Nat.reduceSub, pow_zero, pow_one]
      exact le_sup_left
  have hinter : U ⊓ E = Subgroup.zpowers (x ^ (p ^ (u - 1))) := by
    apply le_antisymm
    · intro w hw
      have hwU : w ∈ U := hw.1
      have hwE : w ∈ E := hw.2
      rw [hUeq, Subgroup.mem_zpowers_iff] at hwU
      rcases hwU with ⟨t, hwt⟩
      have hwpow : w ^ p = 1 := by simpa [E, powMonoidHom] using hwE
      have hzpowtp : z ^ (t * p) = 1 := by
        calc
          z ^ (t * p) = (z ^ t) ^ (p : ℤ) := by rw [← zpow_mul]
          _ = (z ^ t) ^ p := by rw [zpow_natCast]
          _ = 1 := by rw [hwt]; exact hwpow
      have hdvd : (orderOf z : ℤ) ∣ t * p := orderOf_dvd_iff_zpow_eq_one.mpr hzpowtp
      rw [hzorder] at hdvd
      have hqdt : (((p ^ (u - 1) : ℕ) : ℤ)) ∣ t :=
        (int_prime_pow_mul_dvd_mul_iff hp hu).mp hdvd
      rcases hqdt with ⟨s, rfl⟩
      have hzqpow : z ^ (((p ^ (u - 1) : ℕ) : ℤ)) = x ^ (p ^ (u - 1)) := by
        rw [zpow_natCast]
        exact mul_zpow_right_pow_pred_eq_left hu1 hy' k
      have hweq : w = (x ^ (p ^ (u - 1))) ^ s := by
        calc
          w = z ^ ((((p ^ (u - 1) : ℕ) : ℤ)) * s) := hwt.symm
          _ = (z ^ (((p ^ (u - 1) : ℕ) : ℤ))) ^ s := by rw [zpow_mul]
          _ = (x ^ (p ^ (u - 1))) ^ s := by rw [hzqpow]
      rw [hweq]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers (x ^ (p ^ (u - 1)))) s
    · exact hA
  refine ⟨?_, hUcard, hinter⟩
  rw [hUeq]
  exact Subgroup.isCyclic_zpowers z

/- accepted add_to_file helper 21 -/
lemma H_fin_injective_v1 {G : Type*} [CommGroup G]
    {p u : ℕ} (hp : p.Prime) (hu : 0 < u)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    Function.Injective (fun r : Fin p =>
      Subgroup.zpowers (x * y ^ (r.val : ℕ))) := by
  intro r s hrs
  change Subgroup.zpowers (x * y ^ (r.val : ℕ)) =
    Subgroup.zpowers (x * y ^ (s.val : ℕ)) at hrs
  have hrs_mem : x * y ^ (s.val : ℕ) ∈
      Subgroup.zpowers (x * y ^ (r.val : ℕ)) := by
    rw [hrs]
    exact Subgroup.mem_zpowers _
  rw [Subgroup.mem_zpowers_iff] at hrs_mem
  rcases hrs_mem with ⟨t, ht⟩
  have hformula : ((x * y ^ (r.val : ℕ)) ^ t) =
      x ^ t * y ^ (((r.val : ℤ)) * t) := by
    calc
      ((x * y ^ (r.val : ℕ)) ^ t) = x ^ t * (y ^ (r.val : ℕ)) ^ t := by rw [mul_zpow]
      _ = x ^ t * (y ^ ((r.val : ℤ))) ^ t := by rw [zpow_natCast]
      _ = x ^ t * y ^ (((r.val : ℤ)) * t) := by rw [← zpow_mul]
  rw [hformula] at ht
  let X : Subgroup G := Subgroup.zpowers x
  let Y : Subgroup G := Subgroup.zpowers y
  have hpair :
      (⟨⟨x ^ t, Subgroup.zpow_mem X (Subgroup.mem_zpowers x) t⟩,
        ⟨y ^ (((r.val : ℤ)) * t), Subgroup.zpow_mem Y (Subgroup.mem_zpowers y) _⟩⟩ : X × Y) =
      ⟨⟨x, Subgroup.mem_zpowers x⟩,
        ⟨y ^ (s.val : ℕ), Subgroup.pow_mem Y (Subgroup.mem_zpowers y) _⟩⟩ := by
    apply commSubgroupProdHom_injective hind
    simpa [commSubgroupProdHom] using ht
  have hxt : x ^ t = x := congrArg (fun a : X × Y => (a.1 : G)) hpair
  have hyt : y ^ (((r.val : ℤ)) * t) = y ^ (s.val : ℕ) :=
    congrArg (fun a : X × Y => (a.2 : G)) hpair
  have hxone : x ^ (1 - t) = 1 := by
    calc
      x ^ (1 - t) = x * (x ^ t)⁻¹ := by group
      _ = x * x⁻¹ := by rw [hxt]
      _ = 1 := by simp
  have hyone : y ^ (((s.val : ℤ)) - ((r.val : ℤ)) * t) = 1 := by
    calc
      y ^ (((s.val : ℤ)) - ((r.val : ℤ)) * t)
          = y ^ (s.val : ℕ) * (y ^ (((r.val : ℤ)) * t))⁻¹ := by group
      _ = y ^ (s.val : ℕ) * (y ^ (s.val : ℕ))⁻¹ := by rw [hyt]
      _ = 1 := by simp
  have hdvdx : (orderOf x : ℤ) ∣ 1 - t := orderOf_dvd_iff_zpow_eq_one.mpr hxone
  have hdvdy : (orderOf y : ℤ) ∣ (((s.val : ℤ)) - ((r.val : ℤ)) * t) :=
    orderOf_dvd_iff_zpow_eq_one.mpr hyone
  rw [hx] at hdvdx
  rw [hy] at hdvdy
  have hp_dvd_orderx : (p : ℤ) ∣ ((p ^ u : ℕ) : ℤ) := by
    have hd : p ^ 1 ∣ p ^ u := pow_dvd_pow p (by omega : 1 ≤ u)
    have hdZ : (((p ^ 1 : ℕ) : ℤ)) ∣ (((p ^ u : ℕ) : ℤ)) := by exact_mod_cast hd
    simpa using hdZ
  have hpt : (p : ℤ) ∣ 1 - t := dvd_trans hp_dvd_orderx hdvdx
  rcases hpt with ⟨a, ha⟩
  rcases hdvdy with ⟨b, hb⟩
  have hpsr : (p : ℤ) ∣ (((s.val : ℤ)) - (r.val : ℤ)) := by
    refine ⟨b - (r.val : ℤ) * a, ?_⟩
    have hrewrite : (((s.val : ℤ)) - (r.val : ℤ)) =
        ((((s.val : ℤ)) - ((r.val : ℤ)) * t) - ((r.val : ℤ)) * (1 - t)) := by ring
    rw [hrewrite, hb, ha]
    ring
  have hzmod : (((s.val : ℤ) - (r.val : ℤ) : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (((s.val : ℤ) - (r.val : ℤ))) p).mpr hpsr
  have hzmods : (((s.val : ℤ)) : ZMod p) = (((r.val : ℤ)) : ZMod p) := by
    apply sub_eq_zero.mp
    simpa using hzmod
  have hzmodnat : ((s.val : ZMod p) = (r.val : ZMod p)) := by exact_mod_cast hzmods
  have hnatmod : s.val ≡ r.val [MOD p] :=
    (ZMod.natCast_eq_natCast_iff s.val r.val p).mp hzmodnat
  have hval : s.val = r.val :=
    Nat.ModEq.eq_of_lt_of_lt hnatmod s.isLt r.isLt
  exact Fin.ext hval.symm

/- accepted add_to_file helper 22 -/
lemma H_fin_ne_N_v1 {G : Type*} [CommGroup G]
    {p u : ℕ} (hp : p.Prime) (hu : 0 < u)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) (r : Fin p) :
    Subgroup.zpowers (x * y ^ (r.val : ℕ)) ≠
      Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y := by
  intro hHN
  have hyN : y ∈ Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y :=
    (le_sup_right : Subgroup.zpowers y ≤
      Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y) (Subgroup.mem_zpowers y)
  rw [← hHN] at hyN
  rw [Subgroup.mem_zpowers_iff] at hyN
  rcases hyN with ⟨t, ht⟩
  have hformula : ((x * y ^ (r.val : ℕ)) ^ t) =
      x ^ t * y ^ (((r.val : ℤ)) * t) := by
    calc
      ((x * y ^ (r.val : ℕ)) ^ t) = x ^ t * (y ^ (r.val : ℕ)) ^ t := by rw [mul_zpow]
      _ = x ^ t * (y ^ ((r.val : ℤ))) ^ t := by rw [zpow_natCast]
      _ = x ^ t * y ^ (((r.val : ℤ)) * t) := by rw [← zpow_mul]
  rw [hformula] at ht
  let X : Subgroup G := Subgroup.zpowers x
  let Y : Subgroup G := Subgroup.zpowers y
  have hpair :
      (⟨⟨x ^ t, Subgroup.zpow_mem X (Subgroup.mem_zpowers x) t⟩,
        ⟨y ^ (((r.val : ℤ)) * t), Subgroup.zpow_mem Y (Subgroup.mem_zpowers y) _⟩⟩ : X × Y) =
      ⟨⟨1, X.one_mem⟩, ⟨y, Subgroup.mem_zpowers y⟩⟩ := by
    apply commSubgroupProdHom_injective hind
    simpa [commSubgroupProdHom] using ht
  have hxt : x ^ t = 1 := congrArg (fun a : X × Y => (a.1 : G)) hpair
  have hyt : y ^ (((r.val : ℤ)) * t) = y := congrArg (fun a : X × Y => (a.2 : G)) hpair
  have hyone : y ^ (((r.val : ℤ)) * t - 1) = 1 := by
    calc
      y ^ (((r.val : ℤ)) * t - 1) = y ^ (((r.val : ℤ)) * t) * y⁻¹ := by group
      _ = y * y⁻¹ := by rw [hyt]
      _ = 1 := by simp
  have hdvdx : (orderOf x : ℤ) ∣ t := orderOf_dvd_iff_zpow_eq_one.mpr hxt
  have hdvdy : (orderOf y : ℤ) ∣ (((r.val : ℤ)) * t - 1) :=
    orderOf_dvd_iff_zpow_eq_one.mpr hyone
  rw [hx] at hdvdx
  rw [hy] at hdvdy
  have hp_dvd_orderx : (p : ℤ) ∣ ((p ^ u : ℕ) : ℤ) := by
    have hd : p ^ 1 ∣ p ^ u := pow_dvd_pow p (by omega : 1 ≤ u)
    have hdZ : (((p ^ 1 : ℕ) : ℤ)) ∣ (((p ^ u : ℕ) : ℤ)) := by exact_mod_cast hd
    simpa using hdZ
  have hpt : (p : ℤ) ∣ t := dvd_trans hp_dvd_orderx hdvdx
  have hprt : (p : ℤ) ∣ ((r.val : ℤ)) * t := dvd_mul_of_dvd_right hpt _
  rcases hprt with ⟨b, hb⟩
  rcases hdvdy with ⟨a, ha⟩
  have hdiv1 : (p : ℤ) ∣ 1 := by
    refine ⟨b - a, ?_⟩
    have hsub : (p : ℤ) * b - (p : ℤ) * a = 1 := by
      rw [← hb, ← ha]
      ring
    calc
      1 = (p : ℤ) * b - (p : ℤ) * a := hsub.symm
      _ = (p : ℤ) * (b - a) := by ring
  have hdiv1nat : p ∣ 1 := by exact_mod_cast hdiv1
  exact hp.not_dvd_one hdiv1nat

/- accepted add_to_file helper 23 -/
lemma nonN_eq_H_fin_v1 {G : Type*} [CommGroup G] [Finite G]
    {p u v : ℕ} (hp : p.Prime) (hu : 0 < u) (hv : 0 < v)
    (hu1 : 1 < u) (hv1 : v = 1)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p ^ v)
    (hspan : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥)
    {U : Subgroup G} (hU : U.index = p)
    (hUN : U ≠ Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y) :
    ∃ r : Fin p, U = Subgroup.zpowers (x * y ^ (r.val : ℕ)) := by
  let E : Subgroup G := (powMonoidHom p : G →* G).ker
  let N : Subgroup G := Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y
  have hN := N_index_mem_unique_v1 hp hu hv hu1 hv1 hx hy hspan hind
  change N.index = p ∧ E ≤ N ∧ (∀ V : Subgroup G, V.index = p → E ≤ V → V = N) at hN
  have hE : E = Subgroup.zpowers (x ^ (p ^ (u - 1))) ⊔
      Subgroup.zpowers (y ^ (p ^ (v - 1))) :=
    pow_ker_eq_zpowers_sup hp hu hv hx hy hspan hind
  have hyU : y ∉ U := by
    intro h
    have hEU : E ≤ U := by
      rw [hE, hv1]
      simp only [Nat.reduceSub, pow_zero, pow_one]
      apply sup_le
      · have hxpU : x ^ p ∈ U := pow_mem_subgroup_of_index_eq U hU x
        exact le_trans (zpowers_x_pow_pred_le_zpowers_x_pow hu1 x)
          ((Subgroup.zpowers_le).mpr hxpU)
      · exact (Subgroup.zpowers_le).mpr h
    exact hUN (hN.2.2 U hU hEU)
  letI : Fact p.Prime := ⟨hp⟩
  letI := Subgroup.normal_of_comm U
  let q : G →* G ⧸ U := QuotientGroup.mk' U
  have hQcard : Nat.card (G ⧸ U) = p := by rw [← U.index_eq_card, hU]
  have hqy : q y ≠ 1 := by
    intro h
    have hyker : y ∈ q.ker := by rw [MonoidHom.mem_ker]; exact h
    rw [QuotientGroup.ker_mk'] at hyker
    exact hyU hyker
  have hqxmem : q x ∈ Subgroup.zpowers (q y) :=
    mem_zpowers_of_prime_card hQcard hqy
  rw [Subgroup.mem_zpowers_iff] at hqxmem
  rcases hqxmem with ⟨i, hiq⟩
  let k : ℤ := -i
  let z : G := x * y ^ k
  have hzq : q z = 1 := by
    change q (x * y ^ (-i)) = 1
    rw [map_mul, map_zpow, ← hiq]
    simp
  have hzU : z ∈ U := by
    have hzker : z ∈ q.ker := by rw [MonoidHom.mem_ker]; exact hzq
    rw [QuotientGroup.ker_mk'] at hzker
    exact hzker
  have hPcard : Nat.card G = p ^ (u + 1) := by
    rw [Nat_card_of_zpowers_sup_top_inf_bot hspan hind, hx, hy, hv1, pow_one, ← pow_succ]
  have hUcard : Nat.card ↥U = p ^ u :=
    (subgroup_index_prime_iff_card_eq_of_card_pow_succ hp hPcard U).mp hU
  have hy' : orderOf y = p := by simpa [hv1] using hy
  have hzorder : orderOf z = p ^ u :=
    orderOf_mul_zpow_right_v1 hp hu hx hy' hind k
  have hHzU : Subgroup.zpowers z ≤ U := (Subgroup.zpowers_le).mpr hzU
  have hUeqz : U = Subgroup.zpowers z := by
    apply Eq.symm
    apply Subgroup.eq_of_le_of_card_ge hHzU
    rw [hUcard, Nat.card_zpowers, hzorder]
  have hknonneg : 0 ≤ k % (p : ℤ) :=
    Int.emod_nonneg k (by exact_mod_cast hp.ne_zero)
  have hklt : k % (p : ℤ) < (p : ℤ) :=
    Int.emod_lt_of_pos k (by exact_mod_cast hp.pos)
  let r : Fin p := ⟨(k % (p : ℤ)).toNat, by
    exact (Int.toNat_lt hknonneg).mpr hklt⟩
  have hmod : y ^ (k % ↑(orderOf y)) = y ^ k := zpow_mod_orderOf y k
  rw [hy'] at hmod
  have hrcast : ((r.val : ℤ)) = k % (p : ℤ) := Int.toNat_of_nonneg hknonneg
  have hykr : y ^ k = y ^ (r.val : ℕ) := by
    calc
      y ^ k = y ^ (k % (p : ℤ)) := hmod.symm
      _ = y ^ ((r.val : ℤ)) := by rw [← hrcast]
      _ = y ^ (r.val : ℕ) := by rw [zpow_natCast]
  have hzr : z = x * y ^ (r.val : ℕ) := by
    dsimp [z]
    rw [hykr]
  exact ⟨r, by rw [hUeqz, hzr]⟩

/- accepted add_to_file helper 24 -/
lemma card_nonN_index_prime_v1 {G : Type*} [CommGroup G] [Finite G]
    {p u v : ℕ} (hp : p.Prime) (hu : 0 < u) (hv : 0 < v)
    (hu1 : 1 < u) (hv1 : v = 1)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p ^ v)
    (hspan : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    Nat.card {U : Subgroup G // U.index = p ∧
      U ≠ Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y} = p := by
  let N : Subgroup G := Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y
  let H : Fin p → Subgroup G := fun r =>
    Subgroup.zpowers (x * y ^ (r.val : ℕ))
  have hPcard : Nat.card G = p ^ (u + 1) := by
    rw [Nat_card_of_zpowers_sup_top_inf_bot hspan hind, hx, hy, hv1, pow_one, ← pow_succ]
  have hy' : orderOf y = p := by simpa [hv1] using hy
  have hHindex : ∀ r : Fin p, (H r).index = p := by
    intro r
    have hzorder : orderOf (x * y ^ (r.val : ℕ)) = p ^ u := by
      simpa [zpow_natCast] using
        (orderOf_mul_zpow_right_v1 hp hu hx hy' hind (((r.val : ℤ))))
    have hHcard : Nat.card ↥(H r) = p ^ u := by
      dsimp [H]
      rw [Nat.card_zpowers, hzorder]
    exact (subgroup_index_prime_iff_card_eq_of_card_pow_succ hp hPcard (H r)).mpr hHcard
  have hHne : ∀ r : Fin p, H r ≠ N := by
    intro r
    exact H_fin_ne_N_v1 hp hu hx hy' hind r
  let S := {U : Subgroup G // U.index = p ∧ U ≠ N}
  let f : Fin p → S := fun r => ⟨H r, hHindex r, hHne r⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply H_fin_injective_v1 hp hu hx hy' hind
    exact congrArg Subtype.val hab
  have hsurj : Function.Surjective f := by
    intro UU
    rcases nonN_eq_H_fin_v1 hp hu hv hu1 hv1 hx hy hspan hind UU.2.1 UU.2.2 with ⟨r, hr⟩
    exact ⟨r, Subtype.ext hr.symm⟩
  let e : Fin p ≃ S := Equiv.ofBijective f ⟨hinj, hsurj⟩
  calc
    Nat.card S = Nat.card (Fin p) := (Nat.card_congr e).symm
    _ = p := Nat.card_fin p

/- accepted add_to_file helper 25 -/
lemma pow_pred_mem_subgroup_of_index_eq {G : Type*} [CommGroup G]
    (U : Subgroup G) {p n : ℕ} (hn : 1 < n) (hindex : U.index = p) (x : G) :
    x ^ (p ^ (n - 1)) ∈ U := by
  have h := pow_mem_subgroup_of_index_eq U hindex (x ^ (p ^ (n - 2)))
  convert h using 1
  rw [← pow_mul]
  congr 1
  rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]

/- accepted add_to_file helper 26 -/
lemma N_mulEquiv_v1 {G : Type*} [CommGroup G]
    {p u : ℕ} (hp : p.Prime) (hu : 0 < u)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    let N : Subgroup G := Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y
    Nonempty (N ≃* Multiplicative (ZMod (p ^ (u - 1))) × Multiplicative (ZMod p)) := by
  intro N
  let X : Subgroup G := Subgroup.zpowers (x ^ p)
  let Y : Subgroup G := Subgroup.zpowers y
  have hinf : X ⊓ Y = ⊥ := by
    dsimp [X, Y]
    simpa using zpowers_pow_inf_zpowers_pow_eq_bot hind p 1
  let f := commSubgroupProdHom X Y
  have hrange : f.range = N := by
    dsimp [f, N, X, Y]
    exact commSubgroupProdHom_range (Subgroup.zpowers (x ^ p)) (Subgroup.zpowers y)
  have hinj : Function.Injective f.rangeRestrict := by
    rw [MonoidHom.rangeRestrict_injective_iff]
    dsimp [f]
    exact commSubgroupProdHom_injective hinf
  have hbij : Function.Bijective f.rangeRestrict :=
    ⟨hinj, MonoidHom.rangeRestrict_surjective f⟩
  let eprod : (↥X × ↥Y) ≃* N := by
    let e : (↥X × ↥Y) ≃* f.range := MulEquiv.ofBijective f.rangeRestrict hbij
    rwa [hrange] at e
  have hXcard : Nat.card ↥X = p ^ (u - 1) := by
    dsimp [X]
    rw [Nat.card_zpowers]
    simpa using orderOf_prime_pow_pow hp hx (k := 1) (by omega : 1 ≤ u)
  have hYcard : Nat.card ↥Y = p := by
    dsimp [Y]
    rw [Nat.card_zpowers, hy]
  rcases IsCyclic.exists_generator (α := X) with ⟨gx, hgx⟩
  rcases IsCyclic.exists_generator (α := Y) with ⟨gy, hgy⟩
  let eX : Multiplicative (ZMod (p ^ (u - 1))) ≃* X :=
    zmodMulEquivOfGenerator hgx hXcard
  let eY : Multiplicative (ZMod p) ≃* Y := zmodMulEquivOfGenerator hgy hYcard
  exact ⟨eprod.symm.trans (MulEquiv.prodCongr eX.symm eY.symm)⟩

/- verified submission -/
theorem sylow_rank_two_index_prime_subgroups
    {A : Type*} [CommGroup A] [Finite A]
    {p u v : ℕ} (hp : p.Prime) (hu : 0 < u) (hv : 0 < v) (huv : v ≤ u)
    (P : Sylow p A) (x y : P)
    (hx : orderOf x = p ^ u) (hy : orderOf y = p ^ v)
    (hspan : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    let E : Subgroup P := (powMonoidHom p : P →* P).ker
    let N : Subgroup P := Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y
    E = Subgroup.zpowers (x ^ (p ^ (u - 1))) ⊔
          Subgroup.zpowers (y ^ (p ^ (v - 1))) ∧
    (u = 1 ∧ v = 1 →
      ∀ U : Subgroup P, U.index = p ↔ U ≤ E ∧ Nat.card U = p) ∧
    (v = 1 ∧ 1 < u →
      N.index = p ∧ E ≤ N ∧
      (∀ U : Subgroup P, U.index = p → E ≤ U → U = N) ∧
      Nonempty (N ≃* Multiplicative (ZMod (p ^ (u - 1))) × Multiplicative (ZMod p)) ∧
      Nat.card {U : Subgroup P // U.index = p ∧ U ≠ N} = p ∧
      (∀ U : Subgroup P, U.index = p → U ≠ N →
        IsCyclic U ∧ Nat.card U = p ^ u ∧
          U ⊓ E = Subgroup.zpowers (x ^ (p ^ (u - 1))))) ∧
    (1 < v → ∀ U : Subgroup P, U.index = p → E ≤ U) := by
  intro E N
  have hE : E = Subgroup.zpowers (x ^ (p ^ (u - 1))) ⊔
      Subgroup.zpowers (y ^ (p ^ (v - 1))) :=
    pow_ker_eq_zpowers_sup hp hu hv hx hy hspan hind
  refine ⟨hE, ?_, ?_, ?_⟩
  · rintro ⟨hu1, hv1⟩
    have hPcard : Nat.card P = p ^ 2 := by
      calc
        Nat.card P = orderOf x * orderOf y :=
          Nat_card_of_zpowers_sup_top_inf_bot hspan hind
        _ = p ^ 2 := by rw [hx, hy, hu1, hv1]; simpa using (pow_two p).symm
    have hEcard : Nat.card ↥E = p ^ 2 :=
      Nat_card_pow_ker hp hu hv hx hy hspan hind
    have hEtop : E = ⊤ := Subgroup.eq_top_of_card_eq E (by rw [hEcard, hPcard])
    intro U
    rw [hEtop]
    constructor
    · intro hU
      exact ⟨le_top, (subgroup_index_prime_iff_card_prime_of_card_sq hp hPcard U).mp hU⟩
    · intro hU
      exact (subgroup_index_prime_iff_card_prime_of_card_sq hp hPcard U).mpr hU.2
  · rintro ⟨hv1, hu1⟩
    have hNstruct := N_index_mem_unique_v1 hp hu hv hu1 hv1 hx hy hspan hind
    change N.index = p ∧ E ≤ N ∧
      (∀ U : Subgroup P, U.index = p → E ≤ U → U = N) at hNstruct
    have hy' : orderOf y = p := by simpa [hv1] using hy
    have hNiso : Nonempty (N ≃* Multiplicative (ZMod (p ^ (u - 1))) ×
        Multiplicative (ZMod p)) := by
      exact N_mulEquiv_v1 hp hu hx hy' hind
    have hcount : Nat.card {U : Subgroup P // U.index = p ∧ U ≠ N} = p := by
      exact card_nonN_index_prime_v1 hp hu hv hu1 hv1 hx hy hspan hind
    refine ⟨hNstruct.1, hNstruct.2.1, hNstruct.2.2, hNiso, hcount, ?_⟩
    intro U hU hUN
    exact cyclic_nonN_v1 hp hu hv hu1 hv1 hx hy hspan hind hU hUN
  · intro hv1
    intro U hU
    rw [hE]
    apply sup_le
    · rw [Subgroup.zpowers_le]
      exact pow_pred_mem_subgroup_of_index_eq U (by omega : 1 < u) hU x
    · rw [Subgroup.zpowers_le]
      exact pow_pred_mem_subgroup_of_index_eq U hv1 hU y

end Rollout_p2247_sylow_rank_two_index_prime_subgroups

#check_dependency_graph "Rollout_p2247_sylow_rank_two_index_prime_subgroups.sylow_rank_two_index_prime_subgroups" against "{\"edges\":[{\"conclusion\":{\"name\":\"hE\",\"statement\":\"E = Subgroup.zpowers (x ^ p ^ (u - 1)) ⊔ Subgroup.zpowers (y ^ p ^ (v - 1))\"},\"graphEdgeId\":\"h_001_he\",\"premises\":[{\"name\":\"hp\",\"statement\":\"Nat.Prime p\"},{\"name\":\"hu\",\"statement\":\"0 < u\"},{\"name\":\"hv\",\"statement\":\"0 < v\"},{\"name\":\"hx\",\"statement\":\"orderOf x = p ^ u\"},{\"name\":\"hy\",\"statement\":\"orderOf y = p ^ v\"},{\"name\":\"hspan\",\"statement\":\"Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤\"},{\"name\":\"hind\",\"statement\":\"Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥\"}],\"rawEdgeId\":\"telescope_19\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"E = Subgroup.zpowers (x ^ p ^ (u - 1)) ⊔ Subgroup.zpowers (y ^ p ^ (v - 1)) ∧ (u = 1 ∧ v = 1 → ∀ (U : Subgroup ↥↑P), U.index = p ↔ U ≤ E ∧ Nat.card ↥U = p) ∧ (v = 1 ∧ 1 < u → N.index = p ∧ E ≤ N ∧ (∀ (U : Subgroup ↥↑P), U.index = p → E ≤ U → U = N) ∧ Nonempty (↥N ≃* Multiplicative (ZMod (p ^ (u - 1))) × Multiplicative (ZMod p)) ∧ Nat.card { U // U.index = p ∧ U ≠ N } = p ∧ ∀ (U : Subgroup ↥↑P), U.index = p → U ≠ N → IsCyclic ↥U ∧ Nat.card ↥U = p ^ u ∧ U ⊓ E = Subgroup.zpowers (x ^ p ^ (u - 1))) ∧ (1 < v → ∀ (U : Subgroup ↥↑P), U.index = p → E ≤ U)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"Finite A\"},{\"name\":\"hp\",\"statement\":\"Nat.Prime p\"},{\"name\":\"hu\",\"statement\":\"0 < u\"},{\"name\":\"hv\",\"statement\":\"0 < v\"},{\"name\":\"huv\",\"statement\":\"v ≤ u\"},{\"name\":\"hx\",\"statement\":\"orderOf x = p ^ u\"},{\"name\":\"hy\",\"statement\":\"orderOf y = p ^ v\"},{\"name\":\"hspan\",\"statement\":\"Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤\"},{\"name\":\"hind\",\"statement\":\"Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥\"},{\"name\":\"hE\",\"statement\":\"E = Subgroup.zpowers (x ^ p ^ (u - 1)) ⊔ Subgroup.zpowers (y ^ p ^ (v - 1))\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2247_sylow_rank_two_index_prime_subgroups\",\"reconstructedProofSha256\":\"95be45d03e9821e2b759a62abd02ffbb2f228a34dc84b4acd36cb28361c24923\",\"selectedEdgeCount\":2,\"theoremName\":\"Rollout_p2247_sylow_rank_two_index_prime_subgroups.sylow_rank_two_index_prime_subgroups\",\"topologySha256\":\"1c6ca46bbda1eeac93fb6cf04404be324d1119b830fc90bfd6f96fc2ea3164f9\"}"

namespace Rollout_p2272_proposition_4_2

-- graph_id: p2272_proposition_4_2
-- topology_sha256: 600b198cacdc3ae08bbac9a54879a718992687cf4b769380a7ffaa2e3faaa668
/- accepted add_to_file helper 1 -/
lemma gsp_inv_aux {l : Type*} [DecidableEq l] [Fintype l] {R : Type*} [CommRing R]
    (g : Matrix.GeneralLinearGroup (l ⊕ l) R) {μ : Rˣ}
    (h : (g : Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
        (g : Matrix (l ⊕ l) (l ⊕ l) R) = (μ : R) • Matrix.J l R) :
    ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
        Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
        ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
          Matrix (l ⊕ l) (l ⊕ l) R) =
      ((μ⁻¹ : Rˣ) : R) • Matrix.J l R := by
  have hmul :
      (μ : R) •
        ((((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
            Matrix (l ⊕ l) (l ⊕ l) R).transpose) * Matrix.J l R *
          ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
            Matrix (l ⊕ l) (l ⊕ l) R)) = Matrix.J l R := by
    calc
      (μ : R) •
          ((((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R).transpose) * Matrix.J l R *
            ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R))
          =
          (((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R).transpose) *
            ((μ : R) • Matrix.J l R) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R) := by
            simp [Matrix.mul_smul, mul_assoc]
      _ =
          (((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R).transpose) *
            ((g : Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
              (g : Matrix (l ⊕ l) (l ⊕ l) R)) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R) := by rw [h]
      _ =
          ((((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R).transpose) *
            ((g : Matrix (l ⊕ l) (l ⊕ l) R).transpose)) *
            Matrix.J l R *
            ((g : Matrix (l ⊕ l) (l ⊕ l) R) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R)) := by
            simp [mul_assoc]
      _ = Matrix.J l R := by
            rw [← Matrix.transpose_mul]
            simp
  calc
    (((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
          Matrix (l ⊕ l) (l ⊕ l) R).transpose) * Matrix.J l R *
        ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
          Matrix (l ⊕ l) (l ⊕ l) R)
        = ((μ⁻¹ : Rˣ) : R) •
          ((μ : R) •
            ((((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
                Matrix (l ⊕ l) (l ⊕ l) R).transpose) * Matrix.J l R *
              ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
                Matrix (l ⊕ l) (l ⊕ l) R))) := by
          simp [smul_smul]
    _ = ((μ⁻¹ : Rˣ) : R) • Matrix.J l R := by rw [hmul]

/- accepted add_to_file helper 2 -/
lemma gsp_conj_aux {l : Type*} [DecidableEq l] [Fintype l] {R : Type*} [CommRing R]
    (g x : Matrix.GeneralLinearGroup (l ⊕ l) R)
    {μg μx : Rˣ}
    (hg : (g : Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
        (g : Matrix (l ⊕ l) (l ⊕ l) R) = (μg : R) • Matrix.J l R)
    (hx : (x : Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
        (x : Matrix (l ⊕ l) (l ⊕ l) R) = (μx : R) • Matrix.J l R) :
    ((g⁻¹ * x * g : Matrix.GeneralLinearGroup (l ⊕ l) R) :
        Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
        ((g⁻¹ * x * g : Matrix.GeneralLinearGroup (l ⊕ l) R) :
          Matrix (l ⊕ l) (l ⊕ l) R) =
      (μx : R) • Matrix.J l R := by
  have hgi := gsp_inv_aux g hg
  have hc : ((μg⁻¹ : Rˣ) : R) * ((μx : R) * (μg : R)) = μx := by
    simp [mul_assoc, mul_left_comm]
  calc
    ((g⁻¹ * x * g : Matrix.GeneralLinearGroup (l ⊕ l) R) :
        Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
        ((g⁻¹ * x * g : Matrix.GeneralLinearGroup (l ⊕ l) R) :
          Matrix (l ⊕ l) (l ⊕ l) R)
        =
        (g : Matrix (l ⊕ l) (l ⊕ l) R).transpose *
        ((x : Matrix (l ⊕ l) (l ⊕ l) R).transpose *
          ((((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R).transpose) * Matrix.J l R *
            ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R))) *
        (x : Matrix (l ⊕ l) (l ⊕ l) R) *
        (g : Matrix (l ⊕ l) (l ⊕ l) R) := by
          simp [Matrix.transpose_mul, mul_assoc]
    _ =
        (g : Matrix (l ⊕ l) (l ⊕ l) R).transpose *
        ((x : Matrix (l ⊕ l) (l ⊕ l) R).transpose *
          (((μg⁻¹ : Rˣ) : R) • Matrix.J l R)) *
        (x : Matrix (l ⊕ l) (l ⊕ l) R) *
        (g : Matrix (l ⊕ l) (l ⊕ l) R) := by rw [hgi]
    _ =
        ((μg⁻¹ : Rˣ) : R) •
          ((g : Matrix (l ⊕ l) (l ⊕ l) R).transpose *
          ((x : Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
            (x : Matrix (l ⊕ l) (l ⊕ l) R)) *
          (g : Matrix (l ⊕ l) (l ⊕ l) R)) := by
          simp [Matrix.smul_mul, Matrix.mul_smul, mul_assoc]
    _ =
        ((μg⁻¹ : Rˣ) : R) •
          ((g : Matrix (l ⊕ l) (l ⊕ l) R).transpose *
          ((μx : R) • Matrix.J l R) *
          (g : Matrix (l ⊕ l) (l ⊕ l) R)) := by rw [hx]
    _ =
        (((μg⁻¹ : Rˣ) : R) * (μx : R)) •
          ((g : Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
            (g : Matrix (l ⊕ l) (l ⊕ l) R)) := by
          simp [Matrix.smul_mul, Matrix.mul_smul, mul_assoc, smul_smul]
    _ =
        (((μg⁻¹ : Rˣ) : R) * (μx : R)) •
          ((μg : R) • Matrix.J l R) := by rw [hg]
    _ = (μx : R) • Matrix.J l R := by
          simp only [smul_eq_mul, smul_smul]
          rw [show ((μg⁻¹ : Rˣ) : R) * (μx : R) * (μg : R) = μx by
            simpa [mul_assoc] using hc]

/- accepted add_to_file helper 3 -/
def Hmat {R : Type*} [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
  Matrix.fromBlocks
    (Matrix.diagonal ![A 0 0, B 0 0])
    (Matrix.diagonal ![A 0 1, B 0 1])
    (Matrix.diagonal ![A 1 0, B 1 0])
    (Matrix.diagonal ![A 1 1, B 1 1])

lemma Hmat_det {R : Type*} [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R) :
    (Hmat A B).det = A.det * B.det := by
  have hsub :
      (Hmat A B).submatrix
        (Equiv.swap (Sum.inl (1 : Fin 2)) (Sum.inr (0 : Fin 2)))
        (Equiv.swap (Sum.inl (1 : Fin 2)) (Sum.inr (0 : Fin 2))) =
      Matrix.fromBlocks A 0 0 B := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Hmat, Equiv.swap_apply_of_ne_of_ne]
  have hdet := Matrix.det_submatrix_equiv_self
    (Equiv.swap (Sum.inl (1 : Fin 2)) (Sum.inr (0 : Fin 2))) (Hmat A B)
  rw [hsub] at hdet
  rw [← hdet]
  exact Matrix.det_fromBlocks_zero₁₂ A 0 B

lemma Hmat_gsp {R : Type*} [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R)
    (hd : A.det = B.det) :
    (Hmat A B).transpose * Matrix.J (Fin 2) R * Hmat A B =
      A.det • Matrix.J (Fin 2) R := by
  rw [Matrix.det_fin_two A, Matrix.det_fin_two B] at hd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, Hmat, Matrix.J, Matrix.det_fin_two] <;>
    ring_nf <;> first | linear_combination hd | linear_combination -hd

/- accepted add_to_file helper 4 -/
lemma padic_algebraMap_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (algebraMap ℤ_[p] ℚ_[p]) :=
  IsFractionRing.injective ℤ_[p] ℚ_[p]

/- accepted add_to_file helper 5 -/
lemma conjugate_line_decomp {R : Type*} [CommRing R]
    (γ k : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) {N : R}
    (hγcol :
      Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
        ((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) =
      ((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) +
        ((Pi.single (Sum.inl (1 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)))
    (hk : ∀ i : Fin 2 ⊕ Fin 2, i ≠ Sum.inl (0 : Fin 2) →
      N ∣ (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) i (Sum.inl (0 : Fin 2))) :
    ∃ a : R, ∃ w : (Fin 2 ⊕ Fin 2) → R,
      Matrix.mulVec
        (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
        (((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) +
          ((Pi.single (Sum.inl (1 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R))) =
      a • (((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) +
          ((Pi.single (Sum.inl (1 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R))) +
        N • w := by
  let e : (Fin 2 ⊕ Fin 2) → R :=
    Pi.single (Sum.inl (0 : Fin 2)) (1 : R)
  let x : (Fin 2 ⊕ Fin 2) → R :=
    e + Pi.single (Sum.inl (1 : Fin 2)) (1 : R)
  have hγcol' : Matrix.mulVec
      (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e = x := by
    dsimp [e, x]
    exact hγcol
  let a : R := (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
    (Sum.inl (0 : Fin 2)) (Sum.inl (0 : Fin 2))
  let c : (Fin 2 ⊕ Fin 2) → R := fun i =>
    if hi : i = Sum.inl (0 : Fin 2) then 0 else Classical.choose (hk i hi)
  have hc : ∀ i : Fin 2 ⊕ Fin 2, i ≠ Sum.inl (0 : Fin 2) →
      (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) i (Sum.inl (0 : Fin 2)) =
        N * c i := by
    intro i hi
    simpa [c, hi] using Classical.choose_spec (hk i hi)
  have hkc : Matrix.mulVec (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e =
      a • e + N • c := by
    ext i
    by_cases hi : i = Sum.inl (0 : Fin 2)
    · subst i
      simp [e, a, c, Matrix.mulVec]
    · simp [e, Matrix.mulVec, hi, hc i hi]
  have hginvx :
      Matrix.mulVec
        ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x = e := by
    rw [← hγcol']
    calc
      Matrix.mulVec
          ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
          (Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e)
          =
          Matrix.mulVec
            (((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) *
              (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) e := by
            exact Matrix.mulVec_mulVec e _ _
      _ = e := by simp
  refine ⟨a, Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) c, ?_⟩
  calc
    Matrix.mulVec
        (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x
        =
        Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
          (Matrix.mulVec (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e) := by
          have h1 :
              Matrix.mulVec
                (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                  Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x =
              Matrix.mulVec
                (((γ * k : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                  Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                (Matrix.mulVec
                  ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
                    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x) := by
            calc
              Matrix.mulVec
                  (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x
                  =
                  Matrix.mulVec
                    ((((γ * k : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) *
                    ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
                      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) x := by
                    simp [mul_assoc]
              _ =
                  Matrix.mulVec
                    (((γ * k : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                    (Matrix.mulVec
                      ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
                        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x) := by
                    exact (Matrix.mulVec_mulVec x _ _).symm
          rw [hginvx] at h1
          rw [h1]
          calc
            Matrix.mulVec
                (((γ * k : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                  Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e
                =
                Matrix.mulVec
                  (((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) *
                    (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) e := by simp
            _ =
                Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                  (Matrix.mulVec (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e) := by
                  exact (Matrix.mulVec_mulVec e _ _).symm
    _ =
        Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
          (a • e + N • c) := by rw [hkc]
    _ = a • x + N • Matrix.mulVec
        (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) c := by
          rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hγcol']

/- accepted add_to_file helper 6 -/
def extractA {R : Type*} [CommRing R]
    (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) :
    Matrix (Fin 2) (Fin 2) R :=
  !![G (Sum.inl 0) (Sum.inl 0), G (Sum.inl 0) (Sum.inr 0);
     G (Sum.inr 0) (Sum.inl 0), G (Sum.inr 0) (Sum.inr 0)]

def extractB {R : Type*} [CommRing R]
    (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) :
    Matrix (Fin 2) (Fin 2) R :=
  !![G (Sum.inl 1) (Sum.inl 1), G (Sum.inl 1) (Sum.inr 1);
     G (Sum.inr 1) (Sum.inl 1), G (Sum.inr 1) (Sum.inr 1)]

/- accepted add_to_file helper 7 -/
lemma extractA_map_of_eq {R K : Type*} [CommRing R] [CommRing K] [Algebra R K]
    {h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    {A B : Matrix (Fin 2) (Fin 2) K}
    {G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (hh : h = Hmat A B) (hg : h = G.map (algebraMap R K)) :
    A = (extractA G).map (algebraMap R K) := by
  ext i j
  have heq : Hmat A B = G.map (algebraMap R K) := hh.symm.trans hg
  fin_cases i <;> fin_cases j
  · have eq := congr_fun (congr_fun heq (Sum.inl (0:Fin 2))) (Sum.inl (0:Fin 2))
    simpa [Hmat, extractA] using eq
  · have eq := congr_fun (congr_fun heq (Sum.inl (0:Fin 2))) (Sum.inr (0:Fin 2))
    simpa [Hmat, extractA] using eq
  · have eq := congr_fun (congr_fun heq (Sum.inr (0:Fin 2))) (Sum.inl (0:Fin 2))
    simpa [Hmat, extractA] using eq
  · have eq := congr_fun (congr_fun heq (Sum.inr (0:Fin 2))) (Sum.inr (0:Fin 2))
    simpa [Hmat, extractA] using eq

lemma extractB_map_of_eq {R K : Type*} [CommRing R] [CommRing K] [Algebra R K]
    {h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    {A B : Matrix (Fin 2) (Fin 2) K}
    {G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (hh : h = Hmat A B) (hg : h = G.map (algebraMap R K)) :
    B = (extractB G).map (algebraMap R K) := by
  ext i j
  have heq : Hmat A B = G.map (algebraMap R K) := hh.symm.trans hg
  fin_cases i <;> fin_cases j
  · have eq := congr_fun (congr_fun heq (Sum.inl (1:Fin 2))) (Sum.inl (1:Fin 2))
    simpa [Hmat, extractB] using eq
  · have eq := congr_fun (congr_fun heq (Sum.inl (1:Fin 2))) (Sum.inr (1:Fin 2))
    simpa [Hmat, extractB] using eq
  · have eq := congr_fun (congr_fun heq (Sum.inr (1:Fin 2))) (Sum.inl (1:Fin 2))
    simpa [Hmat, extractB] using eq
  · have eq := congr_fun (congr_fun heq (Sum.inr (1:Fin 2))) (Sum.inr (1:Fin 2))
    simpa [Hmat, extractB] using eq

/- accepted add_to_file helper 8 -/
lemma extract_det_data (p : ℕ) [Fact p.Prime]
    {h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ_[p]}
    {A B : Matrix (Fin 2) (Fin 2) ℚ_[p]}
    {G : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]}
    (hh : h = Hmat A B)
    (hg : h = ((G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
      (algebraMap ℤ_[p] ℚ_[p])))
    (hdetAB : A.det = B.det) :
    IsUnit (extractA (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])).det ∧
      IsUnit (extractB (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])).det ∧
      (extractA (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])).det =
        (extractB (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])).det := by
  let AZ := extractA (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
  let BZ := extractB (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
  have hAmap : A = AZ.map (algebraMap ℤ_[p] ℚ_[p]) := by
    dsimp [AZ]
    exact extractA_map_of_eq hh hg
  have hBmap : B = BZ.map (algebraMap ℤ_[p] ℚ_[p]) := by
    dsimp [BZ]
    exact extractB_map_of_eq hh hg
  have hdetZ : AZ.det = BZ.det := by
    apply padic_algebraMap_injective p
    calc
      algebraMap ℤ_[p] ℚ_[p] AZ.det = (AZ.map (algebraMap ℤ_[p] ℚ_[p])).det := by
        exact RingHom.map_det (algebraMap ℤ_[p] ℚ_[p]) AZ
      _ = A.det := by rw [← hAmap]
      _ = B.det := hdetAB
      _ = (BZ.map (algebraMap ℤ_[p] ℚ_[p])).det := by rw [← hBmap]
      _ = algebraMap ℤ_[p] ℚ_[p] BZ.det := by
        exact (RingHom.map_det (algebraMap ℤ_[p] ℚ_[p]) BZ).symm
  have hGunit : IsUnit ((G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).det) := by
    simpa using (Matrix.GeneralLinearGroup.det G).isUnit
  have hGdet : (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).det =
      AZ.det * BZ.det := by
    apply padic_algebraMap_injective p
    calc
      algebraMap ℤ_[p] ℚ_[p]
          (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).det
          =
          (((G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
            (algebraMap ℤ_[p] ℚ_[p])).det) := by
            exact RingHom.map_det (algebraMap ℤ_[p] ℚ_[p])
              (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
      _ = (Hmat A B).det := by
            have heqmat :
                ((G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
                  (algebraMap ℤ_[p] ℚ_[p])) = Hmat A B := hg.symm.trans hh
            rw [heqmat]
      _ = A.det * B.det := Hmat_det A B
      _ = (AZ.map (algebraMap ℤ_[p] ℚ_[p])).det *
          (BZ.map (algebraMap ℤ_[p] ℚ_[p])).det := by rw [← hAmap, ← hBmap]
      _ = algebraMap ℤ_[p] ℚ_[p] (AZ.det * BZ.det) := by
        rw [RingHom.map_mul,
          RingHom.map_det (algebraMap ℤ_[p] ℚ_[p]) AZ,
          RingHom.map_det (algebraMap ℤ_[p] ℚ_[p]) BZ,
          RingHom.mapMatrix_apply, RingHom.mapMatrix_apply]
  have hprod : IsUnit (AZ.det * BZ.det) := by
    simpa [hGdet] using hGunit
  exact ⟨isUnit_of_mul_isUnit_left hprod, isUnit_of_mul_isUnit_right hprod, hdetZ⟩

/- accepted add_to_file helper 9 -/
lemma extract_congr_data (p m : ℕ) [Fact p.Prime]
    {h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ_[p]}
    {A B : Matrix (Fin 2) (Fin 2) ℚ_[p]}
    (γ k : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p])
    (hγe₁e₁ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inl 0) (Sum.inl 0) = 1)
    (hγe₁e₂ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inl 1) (Sum.inl 0) = 1)
    (hγe₁f₁ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inr 0) (Sum.inl 0) = 0)
    (hγe₁f₂ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inr 1) (Sum.inl 0) = 0)
    (hk : ∀ i : Fin 2 ⊕ Fin 2, i ≠ Sum.inl 0 →
      (p : ℤ_[p]) ^ m ∣
        (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) i (Sum.inl 0))
    (hh : h = Hmat A B)
    (hg : h = (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
      (algebraMap ℤ_[p] ℚ_[p]))) :
    (p : ℤ_[p]) ^ m ∣
      (extractA (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]))) 1 0 ∧
    (p : ℤ_[p]) ^ m ∣
      (extractB (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]))) 1 0 ∧
    (p : ℤ_[p]) ^ m ∣
      ((extractA (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]))) 0 0 -
        (extractB (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]))) 0 0) := by
  let e : (Fin 2 ⊕ Fin 2) → ℤ_[p] := Pi.single (Sum.inl (0 : Fin 2)) 1
  let x : (Fin 2 ⊕ Fin 2) → ℤ_[p] :=
    e + Pi.single (Sum.inl (1 : Fin 2)) 1
  have hγcol : Matrix.mulVec
      (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) e = x := by
    ext i
    fin_cases i <;> simp [e, x, Matrix.mulVec, hγe₁e₁, hγe₁e₂, hγe₁f₁, hγe₁f₂]
  obtain ⟨a, w, hdecomp⟩ := conjugate_line_decomp γ k hγcol hk
  have zero_entry : ∀ r c : Fin 2 ⊕ Fin 2, Hmat A B r c = 0 →
      (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) r c = 0 := by
    intro r c hr
    apply padic_algebraMap_injective p
    calc
      algebraMap ℤ_[p] ℚ_[p]
          ((((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) r c) = h r c := by
        exact (congr_fun (congr_fun hg r) c).symm
      _ = Hmat A B r c := congr_fun (congr_fun hh r) c
      _ = 0 := hr
  have z₁ : ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) *
      (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) *
      ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]))⁻¹)
      (Sum.inl (0:Fin 2)) (Sum.inl (1:Fin 2)) = 0 := by
    simpa using zero_entry _ _ (by simp [Hmat])
  have z₂ : ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) *
      (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) *
      ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]))⁻¹)
      (Sum.inl (1:Fin 2)) (Sum.inl (0:Fin 2)) = 0 := by
    simpa using zero_entry _ _ (by simp [Hmat])
  have z₃ : ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) *
      (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) *
      ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]))⁻¹)
      (Sum.inr (0:Fin 2)) (Sum.inl (1:Fin 2)) = 0 := by
    simpa using zero_entry _ _ (by simp [Hmat])
  have z₄ : ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) *
      (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) *
      ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]))⁻¹)
      (Sum.inr (1:Fin 2)) (Sum.inl (0:Fin 2)) = 0 := by
    simpa using zero_entry _ _ (by simp [Hmat])
  have hA00 : extractA (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) 0 0 =
      a + (p : ℤ_[p]) ^ m * w (Sum.inl (0:Fin 2)) := by
    have e0 := congr_fun hdecomp (Sum.inl (0:Fin 2))
    calc
      extractA (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) 0 0
        =
        Matrix.mulVec (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) x (Sum.inl (0:Fin 2)) := by
        symm
        simp [extractA, e, x, Matrix.mulVec, z₁]
      _ = a • x (Sum.inl (0:Fin 2)) + (p : ℤ_[p]) ^ m • w (Sum.inl (0:Fin 2)) := e0
      _ = a + (p : ℤ_[p]) ^ m * w (Sum.inl (0:Fin 2)) := by simp [e, x]
  have hB00 : extractB (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) 0 0 =
      a + (p : ℤ_[p]) ^ m * w (Sum.inl (1:Fin 2)) := by
    have e1 := congr_fun hdecomp (Sum.inl (1:Fin 2))
    calc
      extractB (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) 0 0
        =
        Matrix.mulVec (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) x (Sum.inl (1:Fin 2)) := by
        symm
        simp [extractB, e, x, Matrix.mulVec, z₂]
      _ = a • x (Sum.inl (1:Fin 2)) + (p : ℤ_[p]) ^ m • w (Sum.inl (1:Fin 2)) := e1
      _ = a + (p : ℤ_[p]) ^ m * w (Sum.inl (1:Fin 2)) := by simp [e, x]
  have hA10 : extractA (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) 1 0 =
      (p : ℤ_[p]) ^ m * w (Sum.inr (0:Fin 2)) := by
    have ef0 := congr_fun hdecomp (Sum.inr (0:Fin 2))
    calc
      extractA (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) 1 0
        =
        Matrix.mulVec (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) x (Sum.inr (0:Fin 2)) := by
        symm
        simp [extractA, e, x, Matrix.mulVec, z₃]
      _ = a • x (Sum.inr (0:Fin 2)) + (p : ℤ_[p]) ^ m • w (Sum.inr (0:Fin 2)) := ef0
      _ = (p : ℤ_[p]) ^ m * w (Sum.inr (0:Fin 2)) := by simp [e, x]
  have hB10 : extractB (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) 1 0 =
      (p : ℤ_[p]) ^ m * w (Sum.inr (1:Fin 2)) := by
    have ef1 := congr_fun hdecomp (Sum.inr (1:Fin 2))
    calc
      extractB (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) 1 0
        =
        Matrix.mulVec (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) x (Sum.inr (1:Fin 2)) := by
        symm
        simp [extractB, e, x, Matrix.mulVec, z₄]
      _ = a • x (Sum.inr (1:Fin 2)) + (p : ℤ_[p]) ^ m • w (Sum.inr (1:Fin 2)) := ef1
      _ = (p : ℤ_[p]) ^ m * w (Sum.inr (1:Fin 2)) := by simp [e, x]
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨w (Sum.inr (0:Fin 2)), hA10⟩
  · exact ⟨w (Sum.inr (1:Fin 2)), hB10⟩
  · refine ⟨w (Sum.inl (0:Fin 2)) - w (Sum.inl (1:Fin 2)), ?_⟩
    rw [hA00, hB00]
    ring

/- accepted add_to_file helper 10 -/
lemma Hmat_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A B : Matrix (Fin 2) (Fin 2) R) :
    Hmat (A.map f) (B.map f) = (Hmat A B).map f := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Hmat]

/- accepted add_to_file helper 11 -/
lemma Hmat_line_decomp {R : Type*} [CommRing R]
    (A B : Matrix (Fin 2) (Fin 2) R) {N : R}
    (hA10 : N ∣ A 1 0) (hB10 : N ∣ B 1 0)
    (hdiff : N ∣ (A 0 0 - B 0 0)) :
    ∃ w : (Fin 2 ⊕ Fin 2) → R,
      Matrix.mulVec (Hmat A B)
        (((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) +
          ((Pi.single (Sum.inl (1 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R))) =
      A 0 0 • (((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) +
          ((Pi.single (Sum.inl (1 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R))) +
        N • w := by
  obtain ⟨ca, hca⟩ := hA10
  obtain ⟨cb, hcb⟩ := hB10
  obtain ⟨cd, hcd⟩ := hdiff
  let w : (Fin 2 ⊕ Fin 2) → R := fun i =>
    if i = Sum.inl (0:Fin 2) then 0 else
    if i = Sum.inl (1:Fin 2) then -cd else
    if i = Sum.inr (0:Fin 2) then ca else cb
  refine ⟨w, ?_⟩
  ext i
  fin_cases i <;> simp [Hmat, Matrix.mulVec, w, hca, hcb, hcd] <;> ring <;>
    try linear_combination -hcd

/- accepted add_to_file helper 12 -/
lemma line_condition_of_decomp {R : Type*} [CommRing R]
    (γ H : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) {N a : R}
    (w : (Fin 2 ⊕ Fin 2) → R)
    (hγcol :
      Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
        ((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) =
      ((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) +
        ((Pi.single (Sum.inl (1 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)))
    (hHx :
      Matrix.mulVec (H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
        (((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) +
          ((Pi.single (Sum.inl (1 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R))) =
      a • (((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) +
          ((Pi.single (Sum.inl (1 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R))) +
        N • w) :
    ∀ i : Fin 2 ⊕ Fin 2, i ≠ Sum.inl (0 : Fin 2) →
      N ∣ (((γ⁻¹ * H * γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) i (Sum.inl (0 : Fin 2)) := by
  let e : (Fin 2 ⊕ Fin 2) → R := Pi.single (Sum.inl (0 : Fin 2)) 1
  let x : (Fin 2 ⊕ Fin 2) → R :=
    e + Pi.single (Sum.inl (1 : Fin 2)) 1
  have hγcol' : Matrix.mulVec
      (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e = x := by
    dsimp [e, x]
    exact hγcol
  have hHx' : Matrix.mulVec
      (H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x = a • x + N • w := by
    dsimp [e, x]
    exact hHx
  have hginvx :
      Matrix.mulVec
        ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x = e := by
    rw [← hγcol']
    calc
      Matrix.mulVec
          ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
          (Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e)
          =
          Matrix.mulVec
            (((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) *
              (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) e := by
            exact Matrix.mulVec_mulVec e _ _
      _ = e := by simp
  have hcol :
      Matrix.mulVec
        (((γ⁻¹ * H * γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) e =
      Matrix.mulVec
        ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
        (a • x + N • w) := by
    calc
      Matrix.mulVec
          (((γ⁻¹ * H * γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) e
          =
          Matrix.mulVec
            ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
            (Matrix.mulVec (H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
              (Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e)) := by
          calc
            Matrix.mulVec
                (((γ⁻¹ * H * γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
                  Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) e
                =
                Matrix.mulVec
                  ((((γ⁻¹ * H : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) *
                  (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) e := by
                  simp [mul_assoc]
            _ =
                Matrix.mulVec
                  (((γ⁻¹ * H : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                  (Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e) := by
                  exact (Matrix.mulVec_mulVec e _ _).symm
            _ =
                Matrix.mulVec
                  ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
                    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                  (Matrix.mulVec (H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                    (Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e)) := by
                  calc
                    Matrix.mulVec
                        (((γ⁻¹ * H : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                        (Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e)
                        =
                        Matrix.mulVec
                          ((((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) *
                          (H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R))
                          (Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e) := by
                          simp
                    _ =
                        Matrix.mulVec
                          ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
                            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                          (Matrix.mulVec (H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                            (Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e)) := by
                          exact (Matrix.mulVec_mulVec _ _ _).symm
      _ =
          Matrix.mulVec
            ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
            (Matrix.mulVec (H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x) := by
            rw [hγcol']
      _ =
          Matrix.mulVec
            ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
            (a • x + N • w) := by rw [hHx']
  intro i hi
  refine ⟨Matrix.mulVec
    ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) w i, ?_⟩
  calc
    (((γ⁻¹ * H * γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) i (Sum.inl (0 : Fin 2))
        =
        Matrix.mulVec
          (((γ⁻¹ * H * γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) e i := by
          simp [e, Matrix.mulVec]
    _ =
        Matrix.mulVec
          ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
          (a • x + N • w) i := by rw [hcol]
    _ = N * Matrix.mulVec
          ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) w i := by
          rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hginvx]
          simp [e, hi]

/- accepted add_to_file helper 13 -/
lemma Hmat_GL_map_eq {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A B : Matrix.GeneralLinearGroup (Fin 2) R) :
    (Hmat (A : Matrix (Fin 2) (Fin 2) R)
      (B : Matrix (Fin 2) (Fin 2) R)).map f =
    Hmat ((Matrix.GeneralLinearGroup.map f A :
      Matrix.GeneralLinearGroup (Fin 2) S) : Matrix (Fin 2) (Fin 2) S)
      ((Matrix.GeneralLinearGroup.map f B :
        Matrix.GeneralLinearGroup (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Hmat, Matrix.GeneralLinearGroup.map_apply]

/- verified submission -/
theorem proposition_4_2
    (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m)
    (γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p])
    (hγGSp : ∃ μ : ℤ_[p]ˣ,
      (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).transpose *
          Matrix.J (Fin 2) ℤ_[p] *
          (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) =
        (μ : ℤ_[p]) • Matrix.J (Fin 2) ℤ_[p])
    (hγe₁e₁ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inl 0) (Sum.inl 0) = 1)
    (hγe₁e₂ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inl 1) (Sum.inl 0) = 1)
    (hγe₁f₁ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inr 0) (Sum.inl 0) = 0)
    (hγe₁f₂ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inr 1) (Sum.inl 0) = 0) :
    {h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ_[p] |
      (∃ A B : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p],
        Matrix.det (A : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
            Matrix.det (B : Matrix (Fin 2) (Fin 2) ℚ_[p]) ∧
        h = Matrix.fromBlocks
          (Matrix.diagonal ![A 0 0, B 0 0])
          (Matrix.diagonal ![A 0 1, B 0 1])
          (Matrix.diagonal ![A 1 0, B 1 0])
          (Matrix.diagonal ![A 1 1, B 1 1])) ∧
      ∃ k : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p],
        (∃ μ : ℤ_[p]ˣ,
          (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).transpose *
              Matrix.J (Fin 2) ℤ_[p] *
              (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) =
            (μ : ℤ_[p]) • Matrix.J (Fin 2) ℤ_[p]) ∧
        (∀ i : Fin 2 ⊕ Fin 2, i ≠ Sum.inl 0 →
          (p : ℤ_[p]) ^ m ∣
            (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) i (Sum.inl 0)) ∧
        h = ((↑(γ * k * γ⁻¹) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
            (algebraMap ℤ_[p] ℚ_[p]))} =
    {h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ_[p] |
      ∃ A B : Matrix.GeneralLinearGroup (Fin 2) ℤ_[p],
        Matrix.det (A : Matrix (Fin 2) (Fin 2) ℤ_[p]) =
            Matrix.det (B : Matrix (Fin 2) (Fin 2) ℤ_[p]) ∧
        (p : ℤ_[p]) ^ m ∣ (A : Matrix (Fin 2) (Fin 2) ℤ_[p]) 1 0 ∧
        (p : ℤ_[p]) ^ m ∣ (B : Matrix (Fin 2) (Fin 2) ℤ_[p]) 1 0 ∧
        (p : ℤ_[p]) ^ m ∣
          ((A : Matrix (Fin 2) (Fin 2) ℤ_[p]) 0 0 -
            (B : Matrix (Fin 2) (Fin 2) ℤ_[p]) 0 0) ∧
        h = (Matrix.fromBlocks
          (Matrix.diagonal ![A 0 0, B 0 0])
          (Matrix.diagonal ![A 0 1, B 0 1])
          (Matrix.diagonal ![A 1 0, B 1 0])
          (Matrix.diagonal ![A 1 1, B 1 1])).map
            (algebraMap ℤ_[p] ℚ_[p])} := by
  ext h
  constructor
  · rintro ⟨⟨A, B, hdet, hH⟩, k, _hkGSp, hk, hconj⟩
    change h = Hmat (A : Matrix (Fin 2) (Fin 2) ℚ_[p])
      (B : Matrix (Fin 2) (Fin 2) ℚ_[p]) at hH
    let G : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p] := γ * k * γ⁻¹
    have hconj' : h = ((G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
      (algebraMap ℤ_[p] ℚ_[p])) := by
      simpa [G] using hconj
    obtain ⟨huA, huB, hdetZ⟩ := extract_det_data p hH hconj' hdet
    let AZ : Matrix (Fin 2) (Fin 2) ℤ_[p] :=
      extractA (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
    let BZ : Matrix (Fin 2) (Fin 2) ℤ_[p] :=
      extractB (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
    let AGL : Matrix.GeneralLinearGroup (Fin 2) ℤ_[p] :=
      Matrix.GeneralLinearGroup.mk'' AZ huA
    let BGL : Matrix.GeneralLinearGroup (Fin 2) ℤ_[p] :=
      Matrix.GeneralLinearGroup.mk'' BZ huB
    obtain ⟨hcA, hcB, hdiff⟩ :=
      extract_congr_data p m γ k hγe₁e₁ hγe₁e₂ hγe₁f₁ hγe₁f₂ hk hH hconj'
    refine ⟨AGL, BGL, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [AGL, BGL, AZ, BZ, Matrix.GeneralLinearGroup.val_mk''] using hdetZ
    · simpa [AGL, AZ, G, Matrix.GeneralLinearGroup.val_mk''] using hcA
    · simpa [BGL, BZ, G, Matrix.GeneralLinearGroup.val_mk''] using hcB
    · simpa [AGL, BGL, AZ, BZ, G, Matrix.GeneralLinearGroup.val_mk''] using hdiff
    · have hAmap : (A : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
          AZ.map (algebraMap ℤ_[p] ℚ_[p]) := by
        dsimp [AZ]
        exact extractA_map_of_eq hH hconj'
      have hBmap : (B : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
          BZ.map (algebraMap ℤ_[p] ℚ_[p]) := by
        dsimp [BZ]
        exact extractB_map_of_eq hH hconj'
      calc
        h = Hmat (A : Matrix (Fin 2) (Fin 2) ℚ_[p])
            (B : Matrix (Fin 2) (Fin 2) ℚ_[p]) := hH
        _ = Hmat (AZ.map (algebraMap ℤ_[p] ℚ_[p]))
            (BZ.map (algebraMap ℤ_[p] ℚ_[p])) := by rw [hAmap, hBmap]
        _ = (Hmat AZ BZ).map (algebraMap ℤ_[p] ℚ_[p]) := Hmat_map _ _ _
        _ = (Hmat (AGL : Matrix (Fin 2) (Fin 2) ℤ_[p])
            (BGL : Matrix (Fin 2) (Fin 2) ℤ_[p])).map
            (algebraMap ℤ_[p] ℚ_[p]) := by
          simp [AGL, BGL, Matrix.GeneralLinearGroup.val_mk'']
  · rintro ⟨A, B, hdet, hcA, hcB, hdiff, hH⟩
    change h = (Hmat (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
      (B : Matrix (Fin 2) (Fin 2) ℤ_[p])).map (algebraMap ℤ_[p] ℚ_[p]) at hH
    let Aq : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p] :=
      Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) A
    let Bq : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p] :=
      Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) B
    have hdetq :
        Matrix.det (Aq : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
          Matrix.det (Bq : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
      rw [Matrix.GeneralLinearGroup.val_map_apply,
        Matrix.GeneralLinearGroup.val_map_apply]
      rw [← RingHom.mapMatrix_apply (algebraMap ℤ_[p] ℚ_[p])
        (A : Matrix (Fin 2) (Fin 2) ℤ_[p]),
        ← RingHom.mapMatrix_apply (algebraMap ℤ_[p] ℚ_[p])
        (B : Matrix (Fin 2) (Fin 2) ℤ_[p])]
      rw [← RingHom.map_det (algebraMap ℤ_[p] ℚ_[p])
        (A : Matrix (Fin 2) (Fin 2) ℤ_[p]),
        ← RingHom.map_det (algebraMap ℤ_[p] ℚ_[p])
        (B : Matrix (Fin 2) (Fin 2) ℤ_[p])]
      rw [hdet]
    have hHq : h = Hmat (Aq : Matrix (Fin 2) (Fin 2) ℚ_[p])
        (Bq : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
      calc
        h = (Hmat (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
            (B : Matrix (Fin 2) (Fin 2) ℤ_[p])).map
            (algebraMap ℤ_[p] ℚ_[p]) := hH
        _ = Hmat (Aq : Matrix (Fin 2) (Fin 2) ℚ_[p])
            (Bq : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
          dsimp [Aq, Bq]
          exact Hmat_GL_map_eq (algebraMap ℤ_[p] ℚ_[p]) A B
    have hUA : IsUnit (A : Matrix (Fin 2) (Fin 2) ℤ_[p]).det := by
      simpa using (Matrix.GeneralLinearGroup.det A).isUnit
    have hUB : IsUnit (B : Matrix (Fin 2) (Fin 2) ℤ_[p]).det := by
      simpa using (Matrix.GeneralLinearGroup.det B).isUnit
    have hunitH : IsUnit (Hmat (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
        (B : Matrix (Fin 2) (Fin 2) ℤ_[p])).det := by
      rw [Hmat_det]
      exact hUA.mul hUB
    let HGL : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p] :=
      Matrix.GeneralLinearGroup.mk''
        (Hmat (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
          (B : Matrix (Fin 2) (Fin 2) ℤ_[p])) hunitH
    let k : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p] := γ⁻¹ * HGL * γ
    have hHGSp :
        (HGL : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).transpose *
            Matrix.J (Fin 2) ℤ_[p] *
          (HGL : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) =
        ((Matrix.GeneralLinearGroup.det A : ℤ_[p]ˣ) : ℤ_[p]) •
          Matrix.J (Fin 2) ℤ_[p] := by
      have base := Hmat_gsp (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
        (B : Matrix (Fin 2) (Fin 2) ℤ_[p]) hdet
      simpa [HGL, Matrix.GeneralLinearGroup.val_mk''] using base
    obtain ⟨μγ, hγeq⟩ := hγGSp
    have hkGSp :
        (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).transpose *
            Matrix.J (Fin 2) ℤ_[p] *
          (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) =
        ((Matrix.GeneralLinearGroup.det A : ℤ_[p]ˣ) : ℤ_[p]) •
          Matrix.J (Fin 2) ℤ_[p] := by
      have conj := gsp_conj_aux γ HGL hγeq hHGSp
      simpa [k] using conj
    let e : (Fin 2 ⊕ Fin 2) → ℤ_[p] := Pi.single (Sum.inl (0 : Fin 2)) 1
    let x : (Fin 2 ⊕ Fin 2) → ℤ_[p] :=
      e + Pi.single (Sum.inl (1 : Fin 2)) 1
    have hγcol : Matrix.mulVec
        (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) e = x := by
      ext i
      fin_cases i <;> simp [e, x, Matrix.mulVec, hγe₁e₁, hγe₁e₂, hγe₁f₁, hγe₁f₂]
    obtain ⟨w, hHx⟩ := Hmat_line_decomp
      (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
      (B : Matrix (Fin 2) (Fin 2) ℤ_[p]) hcA hcB hdiff
    have hHxH :
        Matrix.mulVec (HGL : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
          (((Pi.single (Sum.inl (0 : Fin 2)) (1 : ℤ_[p]) : (Fin 2 ⊕ Fin 2) → ℤ_[p])) +
            ((Pi.single (Sum.inl (1 : Fin 2)) (1 : ℤ_[p]) : (Fin 2 ⊕ Fin 2) → ℤ_[p]))) =
        (A : Matrix (Fin 2) (Fin 2) ℤ_[p]) 0 0 •
          (((Pi.single (Sum.inl (0 : Fin 2)) (1 : ℤ_[p]) : (Fin 2 ⊕ Fin 2) → ℤ_[p])) +
            ((Pi.single (Sum.inl (1 : Fin 2)) (1 : ℤ_[p]) : (Fin 2 ⊕ Fin 2) → ℤ_[p]))) +
          (p : ℤ_[p]) ^ m • w := by
      simpa [HGL, Matrix.GeneralLinearGroup.val_mk''] using hHx
    have hkl : ∀ i : Fin 2 ⊕ Fin 2, i ≠ Sum.inl 0 →
        (p : ℤ_[p]) ^ m ∣
          (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) i (Sum.inl 0) := by
      have line := line_condition_of_decomp γ HGL w hγcol hHxH
      simpa [k] using line
    have hconj : h = ((↑(γ * k * γ⁻¹) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
        (algebraMap ℤ_[p] ℚ_[p])) := by
      have hgroup : γ * k * γ⁻¹ = HGL := by
        dsimp [k]
        group
      calc
        h = (Hmat (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
            (B : Matrix (Fin 2) (Fin 2) ℤ_[p])).map
            (algebraMap ℤ_[p] ℚ_[p]) := hH
        _ = ((HGL : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
            (algebraMap ℤ_[p] ℚ_[p])) := by
          simp [HGL, Matrix.GeneralLinearGroup.val_mk'']
        _ = ((↑(γ * k * γ⁻¹) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
            (algebraMap ℤ_[p] ℚ_[p])) := by rw [hgroup]
    exact ⟨⟨Aq, Bq, hdetq, hHq⟩, k,
      ⟨Matrix.GeneralLinearGroup.det A, hkGSp⟩, hkl, hconj⟩

end Rollout_p2272_proposition_4_2

#check_dependency_graph "Rollout_p2272_proposition_4_2.proposition_4_2" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"{h | (∃ A B, (↑A).det = (↑B).det ∧ h = Matrix.fromBlocks (Matrix.diagonal ![↑A 0 0, ↑B 0 0]) (Matrix.diagonal ![↑A 0 1, ↑B 0 1]) (Matrix.diagonal ![↑A 1 0, ↑B 1 0]) (Matrix.diagonal ![↑A 1 1, ↑B 1 1])) ∧ ∃ k, (∃ μ, (↑k).transpose * Matrix.J (Fin 2) ℤ_[p] * ↑k = ↑μ • Matrix.J (Fin 2) ℤ_[p]) ∧ (∀ (i : Fin 2 ⊕ Fin 2), i ≠ Sum.inl 0 → ↑p ^ m ∣ ↑k i (Sum.inl 0)) ∧ h = (↑(γ * k * γ⁻¹)).map ⇑(algebraMap ℤ_[p] ℚ_[p])} = {h | ∃ A B, (↑A).det = (↑B).det ∧ ↑p ^ m ∣ ↑A 1 0 ∧ ↑p ^ m ∣ ↑B 1 0 ∧ ↑p ^ m ∣ ↑A 0 0 - ↑B 0 0 ∧ h = (Matrix.fromBlocks (Matrix.diagonal ![↑A 0 0, ↑B 0 0]) (Matrix.diagonal ![↑A 0 1, ↑B 0 1]) (Matrix.diagonal ![↑A 1 0, ↑B 1 0]) (Matrix.diagonal ![↑A 1 1, ↑B 1 1])).map ⇑(algebraMap ℤ_[p] ℚ_[p])}\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"Fact (Nat.Prime p)\"},{\"name\":\"hγGSp\",\"statement\":\"∃ μ, (↑γ).transpose * Matrix.J (Fin 2) ℤ_[p] * ↑γ = ↑μ • Matrix.J (Fin 2) ℤ_[p]\"},{\"name\":\"hγe₁e₁\",\"statement\":\"↑γ (Sum.inl 0) (Sum.inl 0) = 1\"},{\"name\":\"hγe₁e₂\",\"statement\":\"↑γ (Sum.inl 1) (Sum.inl 0) = 1\"},{\"name\":\"hγe₁f₁\",\"statement\":\"↑γ (Sum.inr 0) (Sum.inl 0) = 0\"},{\"name\":\"hγe₁f₂\",\"statement\":\"↑γ (Sum.inr 1) (Sum.inl 0) = 0\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2272_proposition_4_2\",\"reconstructedProofSha256\":\"b1141185f1b9f649d68bf75e20f59455a2c82fcca1cb1918e2f4b914ff3fcbe2\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p2272_proposition_4_2.proposition_4_2\",\"topologySha256\":\"600b198cacdc3ae08bbac9a54879a718992687cf4b769380a7ffaa2e3faaa668\"}"

namespace Rollout_p2331_reverse_cauchy_schwarz_with_three_term_min

-- graph_id: p2331_reverse_cauchy_schwarz_with_three_term_min
-- topology_sha256: fec88aa8a97a4f2c48e2051cbfc90e6f8d3639b75ec1d7298bc969f8cf03b91b
/- accepted add_to_file helper 1 -/
lemma weighted_variance_bound {n : ℕ} (p z : Fin n → ℝ) (r R : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hzl : ∀ i, r ≤ z i) (hzu : ∀ i, z i ≤ R) :
    (∑ i, p i) * (∑ i, p i * z i ^ 2) - (∑ i, p i * z i) ^ 2 ≤
      (R - r) ^ 2 / 4 * (∑ i, p i) ^ 2 := by
  let U := ∑ i, p i
  let V := ∑ i, p i * z i ^ 2
  let W := ∑ i, p i * z i
  have hU : 0 ≤ U := by
    exact Finset.sum_nonneg fun i _ => hp i
  have hV : V ≤ (r + R) * W - r * R * U := by
    have hpoint : ∀ i ∈ Finset.univ,
        p i * z i ^ 2 ≤ p i * ((r + R) * z i - r * R) := by
      intro i _
      have hzi : z i ^ 2 ≤ (r + R) * z i - r * R := by
        have hnonneg : 0 ≤ (z i - r) * (R - z i) :=
          mul_nonneg (sub_nonneg.mpr (hzl i)) (sub_nonneg.mpr (hzu i))
        nlinarith
      exact mul_le_mul_of_nonneg_left hzi (hp i)
    calc
      V ≤ ∑ i, p i * ((r + R) * z i - r * R) := Finset.sum_le_sum hpoint
      _ = ∑ i, ((p i * z i) * (r + R) - p i * (r * R)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, (p i * z i) * (r + R)) - ∑ i, p i * (r * R) := by
        rw [Finset.sum_sub_distrib]
      _ = W * (r + R) - U * (r * R) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
      _ = (r + R) * W - r * R * U := by ring
  have hmul : U * V ≤ U * ((r + R) * W - r * R * U) :=
    mul_le_mul_of_nonneg_left hV hU
  have hsq : 0 ≤ (W - (r + R) * U / 2) ^ 2 := sq_nonneg _
  change U * V - W ^ 2 ≤ (R - r) ^ 2 / 4 * U ^ 2
  nlinarith

/- accepted add_to_file helper 2 -/
lemma interval_variance_bound {n : ℕ}
    (a A b B : ℝ)
    (ha : 0 < a) (haA : a ≤ A) (hb : 0 < b) (hbB : b ≤ B)
    (x y : Fin n → ℝ)
    (hx : ∀ i, a ≤ x i ∧ x i ≤ A)
    (hy : ∀ i, b ≤ y i ∧ y i ≤ B) :
    (∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 ≤
      ((A * B - a * b) ^ 2 / 4) *
        ((∑ i, x i ^ 2) ^ 2 / (A ^ 2 * a ^ 2)) := by
  have hA : 0 < A := lt_of_lt_of_le ha haA
  have hB : 0 < B := lt_of_lt_of_le hb hbB
  have hxpos : ∀ i, 0 < x i := fun i => lt_of_lt_of_le ha (hx i).1
  have hypos : ∀ i, 0 < y i := fun i => lt_of_lt_of_le hb (hy i).1
  have hvarx :
      (∑ i, x i ^ 2) * (∑ i, x i ^ 2 * (y i / x i) ^ 2) -
          (∑ i, x i ^ 2 * (y i / x i)) ^ 2 ≤
        (B / a - b / A) ^ 2 / 4 * (∑ i, x i ^ 2) ^ 2 := by
    apply weighted_variance_bound
    · intro i
      exact sq_nonneg (x i)
    · intro i
      apply (div_le_div_iff₀ hA (hxpos i)).mpr
      calc
        b * x i ≤ y i * x i := mul_le_mul_of_nonneg_right (hy i).1 (hxpos i).le
        _ ≤ y i * A := mul_le_mul_of_nonneg_left (hx i).2 (hypos i).le
    · intro i
      apply (div_le_div_iff₀ (hxpos i) ha).mpr
      calc
        y i * a ≤ B * a := mul_le_mul_of_nonneg_right (hy i).2 ha.le
        _ ≤ B * x i := mul_le_mul_of_nonneg_left (hx i).1 hB.le
  have hVeq : (∑ i, x i ^ 2 * (y i / x i) ^ 2) = ∑ i, y i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    have hxi : x i ≠ 0 := ne_of_gt (hxpos i)
    field_simp [hxi]
  have hWeq : (∑ i, x i ^ 2 * (y i / x i)) = ∑ i, x i * y i := by
    apply Finset.sum_congr rfl
    intro i _
    have hxi : x i ≠ 0 := ne_of_gt (hxpos i)
    field_simp [hxi]
  have hxterm :
      (∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 ≤
        (B / a - b / A) ^ 2 / 4 * (∑ i, x i ^ 2) ^ 2 := by
    simpa [hVeq, hWeq] using hvarx
  calc
    (∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 ≤
        (B / a - b / A) ^ 2 / 4 * (∑ i, x i ^ 2) ^ 2 := hxterm
    _ = ((A * B - a * b) ^ 2 / 4) *
          ((∑ i, x i ^ 2) ^ 2 / (A ^ 2 * a ^ 2)) := by
      field_simp [ha.ne', hA.ne']

/- accepted add_to_file helper 3 -/
lemma interval_cross_bound {n : ℕ}
    (a A b B : ℝ)
    (ha : 0 < a) (haA : a ≤ A) (hb : 0 < b) (hbB : b ≤ B)
    (x y : Fin n → ℝ)
    (hx : ∀ i, a ≤ x i ∧ x i ≤ A)
    (hy : ∀ i, b ≤ y i ∧ y i ≤ B) :
    (∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 ≤
      ((A * B - a * b) ^ 2 / 4) *
        ((∑ i, x i * y i) ^ 2 / (a * b * A * B)) := by
  let U := ∑ i, x i ^ 2
  let V := ∑ i, y i ^ 2
  let W := ∑ i, x i * y i
  have hU : 0 ≤ U := Finset.sum_nonneg fun i _ => sq_nonneg (x i)
  have hV : 0 ≤ V := Finset.sum_nonneg fun i _ => sq_nonneg (y i)
  have hlin :
      b * B * U + a * A * V ≤ (A * B + a * b) * W := by
    have hpoint : ∀ i ∈ Finset.univ,
        b * B * x i ^ 2 + a * A * y i ^ 2 ≤
          (A * B + a * b) * (x i * y i) := by
      intro i _
      have hfactor1 : 0 ≤ A * y i - b * x i := by
        apply sub_nonneg.mpr
        calc
          b * x i ≤ y i * x i := by
            exact mul_le_mul_of_nonneg_right (hy i).1
              (lt_of_lt_of_le ha (hx i).1).le
          _ ≤ y i * A := by
            exact mul_le_mul_of_nonneg_left (hx i).2
              (lt_of_lt_of_le hb (hy i).1).le
          _ = A * y i := by ring
      have hfactor2 : 0 ≤ B * x i - a * y i := by
        apply sub_nonneg.mpr
        calc
          a * y i ≤ a * B := by
            exact mul_le_mul_of_nonneg_left (hy i).2 ha.le
          _ = B * a := by ring
          _ ≤ B * x i := by
            exact mul_le_mul_of_nonneg_left (hx i).1 (lt_of_lt_of_le hb hbB).le
      have hprod : 0 ≤ (A * y i - b * x i) * (B * x i - a * y i) :=
        mul_nonneg hfactor1 hfactor2
      nlinarith
    have hsum := Finset.sum_le_sum hpoint
    have hleft :
        (∑ i, (b * B * x i ^ 2 + a * A * y i ^ 2)) =
          b * B * U + a * A * V := by
      calc
        (∑ i, (b * B * x i ^ 2 + a * A * y i ^ 2)) =
            (∑ i, b * B * x i ^ 2) + ∑ i, a * A * y i ^ 2 :=
          Finset.sum_add_distrib
        _ = b * B * (∑ i, x i ^ 2) + a * A * (∑ i, y i ^ 2) := by
          congr 1
          · rw [← Finset.mul_sum]
          · rw [← Finset.mul_sum]
    have hright :
        (∑ i, (A * B + a * b) * (x i * y i)) =
          (A * B + a * b) * W := by
      rw [← Finset.mul_sum]
    rw [hleft, hright] at hsum
    exact hsum
  have hLnonneg : 0 ≤ b * B * U + a * A * V := by
    exact add_nonneg
      (mul_nonneg (mul_pos hb (lt_of_lt_of_le hb hbB)).le hU)
      (mul_nonneg (mul_pos ha (lt_of_lt_of_le ha haA)).le hV)
  have hsq : (b * B * U + a * A * V) ^ 2 ≤ ((A * B + a * b) * W) ^ 2 :=
    pow_le_pow_left₀ hLnonneg hlin 2
  have h4 : 4 * (b * B) * (a * A) * (U * V) ≤
      (b * B * U + a * A * V) ^ 2 := by
    nlinarith [sq_nonneg (b * B * U - a * A * V)]
  have hmain : 4 * (b * B) * (a * A) * (U * V) ≤
      ((A * B + a * b) * W) ^ 2 := le_trans h4 hsq
  have hnum : 4 * (b * B) * (a * A) * (U * V - W ^ 2) ≤
      (A * B - a * b) ^ 2 * W ^ 2 := by
    nlinarith
  have hden : 0 < 4 * (b * B) * (a * A) := by
    have hA : 0 < A := lt_of_lt_of_le ha haA
    have hB : 0 < B := lt_of_lt_of_le hb hbB
    positivity
  have htarget : U * V - W ^ 2 ≤
      ((A * B - a * b) ^ 2 * W ^ 2) / (4 * (b * B) * (a * A)) := by
    exact (le_div_iff₀ hden).mpr (by nlinarith)
  have hA : 0 < A := lt_of_lt_of_le ha haA
  have hB : 0 < B := lt_of_lt_of_le hb hbB
  calc
    (∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 =
        U * V - W ^ 2 := rfl
    _ ≤ ((A * B - a * b) ^ 2 * W ^ 2) / (4 * (b * B) * (a * A)) := htarget
    _ = ((A * B - a * b) ^ 2 / 4) *
          (W ^ 2 / (a * b * A * B)) := by
      field_simp [ha.ne', hA.ne', hb.ne', hB.ne']

/- accepted add_to_file helper 4 -/
lemma three_term_strict_examples :
    ∀ k : Fin 3,
      ∃ (m : ℕ) (a' A' b' B' : ℝ) (x' y' : Fin m → ℝ),
        1 ≤ m ∧
        0 < a' ∧ a' ≤ A' ∧ 0 < b' ∧ b' ≤ B' ∧
        (∀ i, a' ≤ x' i ∧ x' i ≤ A') ∧
        (∀ i, b' ≤ y' i ∧ y' i ≤ B') ∧
        (let t : Fin 3 → ℝ :=
          ![((∑ i, x' i ^ 2) ^ 2 / (A' ^ 2 * a' ^ 2)),
            ((∑ i, y' i ^ 2) ^ 2 / (B' ^ 2 * b' ^ 2)),
            ((∑ i, x' i * y' i) ^ 2 / (a' * b' * A' * B'))]
         ∀ j : Fin 3, j ≠ k → t k < t j) := by
  intro k
  fin_cases k
  · refine ⟨1, 1, 2, 1, 2, fun _ => 1, fun _ => 2, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · intro i
      norm_num
    · intro i
      norm_num
    · dsimp
      intro j hj
      fin_cases j
      · simp at hj
      · norm_num [Fin.sum_univ_one]
      · norm_num [Fin.sum_univ_one]
  · refine ⟨1, 1, 2, 1, 2, fun _ => 2, fun _ => 1, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · intro i
      norm_num
    · intro i
      norm_num
    · dsimp
      intro j hj
      fin_cases j
      · norm_num [Fin.sum_univ_one]
      · simp at hj
      · norm_num [Fin.sum_univ_one]
  · refine ⟨2, 1, 2, 1, 2, ![2, 1], ![1, 2], by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> norm_num
    · intro i
      fin_cases i <;> norm_num
    · dsimp
      intro j hj
      fin_cases j
      · norm_num [Fin.sum_univ_two]
      · norm_num [Fin.sum_univ_two]
      · simp at hj

/- verified submission -/
theorem reverse_cauchy_schwarz_with_three_term_min
    (n : ℕ) (hn : 1 ≤ n)
    (a A b B : ℝ)
    (ha : 0 < a) (haA : a ≤ A) (hb : 0 < b) (hbB : b ≤ B)
    (x y : Fin n → ℝ)
    (hx : ∀ i, a ≤ x i ∧ x i ≤ A)
    (hy : ∀ i, b ≤ y i ∧ y i ≤ B) :
    ((∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 ≤
      ((A * B - a * b) ^ 2 / 4) *
        min ((∑ i, x i ^ 2) ^ 2 / (A ^ 2 * a ^ 2))
          (min ((∑ i, y i ^ 2) ^ 2 / (B ^ 2 * b ^ 2))
            ((∑ i, x i * y i) ^ 2 / (a * b * A * B)))) ∧
    (∀ k : Fin 3,
      ∃ (m : ℕ) (a' A' b' B' : ℝ) (x' y' : Fin m → ℝ),
        1 ≤ m ∧
        0 < a' ∧ a' ≤ A' ∧ 0 < b' ∧ b' ≤ B' ∧
        (∀ i, a' ≤ x' i ∧ x' i ≤ A') ∧
        (∀ i, b' ≤ y' i ∧ y' i ≤ B') ∧
        (let t : Fin 3 → ℝ :=
          ![((∑ i, x' i ^ 2) ^ 2 / (A' ^ 2 * a' ^ 2)),
            ((∑ i, y' i ^ 2) ^ 2 / (B' ^ 2 * b' ^ 2)),
            ((∑ i, x' i * y' i) ^ 2 / (a' * b' * A' * B'))]
         ∀ j : Fin 3, j ≠ k → t k < t j)) := by
  constructor
  · have hxbound :
        (∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 ≤
          ((A * B - a * b) ^ 2 / 4) *
            ((∑ i, x i ^ 2) ^ 2 / (A ^ 2 * a ^ 2)) :=
      interval_variance_bound a A b B ha haA hb hbB x y hx hy
    have hyraw := interval_variance_bound b B a A hb hbB ha haA y x hy hx
    have hybound :
        (∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 ≤
          ((A * B - a * b) ^ 2 / 4) *
            ((∑ i, y i ^ 2) ^ 2 / (B ^ 2 * b ^ 2)) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hyraw
    have hcrossbound :
        (∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 ≤
          ((A * B - a * b) ^ 2 / 4) *
            ((∑ i, x i * y i) ^ 2 / (a * b * A * B)) :=
      interval_cross_bound a A b B ha haA hb hbB x y hx hy
    have hc : 0 ≤ ((A * B - a * b) ^ 2 / 4) := by positivity
    rw [mul_min_of_nonneg _ _ hc, mul_min_of_nonneg _ _ hc]
    exact le_min hxbound (le_min hybound hcrossbound)
  · exact three_term_strict_examples

end Rollout_p2331_reverse_cauchy_schwarz_with_three_term_min

#check_dependency_graph "Rollout_p2331_reverse_cauchy_schwarz_with_three_term_min.reverse_cauchy_schwarz_with_three_term_min" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(∑ i, x i ^ 2) * ∑ i, y i ^ 2 - (∑ i, x i * y i) ^ 2 ≤ (A * B - a * b) ^ 2 / 4 * min ((∑ i, x i ^ 2) ^ 2 / (A ^ 2 * a ^ 2)) (min ((∑ i, y i ^ 2) ^ 2 / (B ^ 2 * b ^ 2)) ((∑ i, x i * y i) ^ 2 / (a * b * A * B))) ∧ ∀ (k : Fin 3), ∃ m a' A' b' B' x' y', 1 ≤ m ∧ 0 < a' ∧ a' ≤ A' ∧ 0 < b' ∧ b' ≤ B' ∧ (∀ (i : Fin m), a' ≤ x' i ∧ x' i ≤ A') ∧ (∀ (i : Fin m), b' ≤ y' i ∧ y' i ≤ B') ∧ let t := ![(∑ i, x' i ^ 2) ^ 2 / (A' ^ 2 * a' ^ 2), (∑ i, y' i ^ 2) ^ 2 / (B' ^ 2 * b' ^ 2), (∑ i, x' i * y' i) ^ 2 / (a' * b' * A' * B')]; ∀ (j : Fin 3), j ≠ k → t k < t j\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"ha\",\"statement\":\"0 < a\"},{\"name\":\"haA\",\"statement\":\"a ≤ A\"},{\"name\":\"hb\",\"statement\":\"0 < b\"},{\"name\":\"hbB\",\"statement\":\"b ≤ B\"},{\"name\":\"hx\",\"statement\":\"∀ (i : Fin n), a ≤ x i ∧ x i ≤ A\"},{\"name\":\"hy\",\"statement\":\"∀ (i : Fin n), b ≤ y i ∧ y i ≤ B\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2331_reverse_cauchy_schwarz_with_three_term_min\",\"reconstructedProofSha256\":\"1142f8fedc1d083beac4a3e89048b5ec6f4ca63f30f7feb9f0e6155df59e3351\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p2331_reverse_cauchy_schwarz_with_three_term_min.reverse_cauchy_schwarz_with_three_term_min\",\"topologySha256\":\"fec88aa8a97a4f2c48e2051cbfc90e6f8d3639b75ec1d7298bc969f8cf03b91b\"}"

namespace Rollout_p2332_matrix_kronecker_injective_iff_linearindep

-- graph_id: p2332_matrix_kronecker_injective_iff_linearindep
-- topology_sha256: 812999549bfeac040effa04a22a8ad38d1e8fe269f6948bb066701c2a4298133
/- verified submission -/
theorem matrix_kronecker_injective_iff_linearIndependent
    (g d e : ℕ) (hg : 0 < g) (hd : 0 < d) (he : 0 < e)
    (A : Fin g → Matrix (Fin d) (Fin e) ℂ) :
    let c₁ : Prop := ∀ (n : ℕ), 0 < n → ∀ X : Fin g → Matrix (Fin n) (Fin n) ℂ,
      (∑ j, Matrix.kronecker (A j) (X j)) = 0 → ∀ j, X j = 0
    let c₂ : Prop := ∀ z : Fin g → ℂ,
      (∑ j, z j • A j) = 0 → ∀ j, z j = 0
    let c₃ : Prop := LinearIndependent ℂ A
    (c₁ ↔ c₂) ∧ (c₂ ↔ c₃) := by
  constructor
  · constructor
    · intro h₁ z hz
      let X : Fin g → Matrix (Fin 1) (Fin 1) ℂ :=
        fun j => Matrix.of fun _ _ => z j
      have hsum : (∑ j, Matrix.kronecker (A j) (X j)) = 0 := by
        ext ⟨i, a⟩ ⟨k, b⟩
        have hz' := congrFun (congrFun hz i) k
        simp [Matrix.sum_apply, Matrix.smul_apply, X] at hz' ⊢
        simpa [mul_comm] using hz'
      have hX := h₁ 1 zero_lt_one X hsum
      intro j
      have hj := congrFun (congrFun (hX j) 0) 0
      simpa [X] using hj
    · intro h₂ n hn X hX j
      ext r s
      let z : Fin g → ℂ := fun j => X j r s
      have hzsum : (∑ j, z j • A j) = 0 := by
        ext i k
        have hX' := congrFun (congrFun hX (i, r)) (k, s)
        simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.kronecker, z] at hX' ⊢
        simpa [mul_comm] using hX'
      have hz := h₂ z hzsum j
      simpa [z] using hz
  · constructor
    · intro h₂
      rw [linearIndependent_iff_injective_fintypeLinearCombination]
      intro x y hxy
      have hdiff : (∑ j, (x - y) j • A j) = 0 := by
        have hmap : Fintype.linearCombination ℂ A (x - y) = 0 := by
          rw [map_sub, hxy, sub_self]
        simpa [Fintype.linearCombination_apply] using hmap
      have h := h₂ (x - y) hdiff
      ext j
      have hj := h j
      simpa using sub_eq_zero.mp hj
    · intro h₃ z hz
      rw [linearIndependent_iff_injective_fintypeLinearCombination] at h₃
      have hzlin : Fintype.linearCombination ℂ A z = Fintype.linearCombination ℂ A 0 := by
        rw [Fintype.linearCombination_apply]
        simpa using hz
      have hz0 := h₃ hzlin
      intro j
      exact congrFun hz0 j

end Rollout_p2332_matrix_kronecker_injective_iff_linearindep

#check_dependency_graph "Rollout_p2332_matrix_kronecker_injective_iff_linearindep.matrix_kronecker_injective_iff_linearIndependent" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"((∀ (n : ℕ), 0 < n → ∀ (X : Fin g → Matrix (Fin n) (Fin n) ℂ), ∑ j, (A j).kronecker (X j) = 0 → ∀ (j : Fin g), X j = 0) ↔ ∀ (z : Fin g → ℂ), ∑ j, z j • A j = 0 → ∀ (j : Fin g), z j = 0) ∧ ((∀ (z : Fin g → ℂ), ∑ j, z j • A j = 0 → ∀ (j : Fin g), z j = 0) ↔ LinearIndependent ℂ A)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2332_matrix_kronecker_injective_iff_linearindep\",\"reconstructedProofSha256\":\"5f6b35e57af2756aa3fc75c8250ca61176fbf4c7dc7229c1560ad8136bf4f472\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p2332_matrix_kronecker_injective_iff_linearindep.matrix_kronecker_injective_iff_linearIndependent\",\"topologySha256\":\"812999549bfeac040effa04a22a8ad38d1e8fe269f6948bb066701c2a4298133\"}"

namespace Rollout_p2342_c0singlezero_apply

-- graph_id: p2342_c0singlezero_apply
-- topology_sha256: 21795638089805f2200533f25659a7f89ca729fc135727d8148dab9b2ca30161
/- verified submission -/
noncomputable def c0SingleZero {E : Type*} [TopologicalSpace E] [Zero E] (x : E) :
    ZeroAtInftyContinuousMap ℕ E where
  toFun n := if n = 0 then x else 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    apply HasCompactSupport.is_zero_at_infty
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_singleton (x := (0 : ℕ)))
    intro n hn
    by_cases h0 : n = 0
    · exact Set.mem_singleton_iff.mpr h0
    · exfalso
      exact hn (by simp [h0])

@[simp] theorem c0SingleZero_apply {E : Type*} [TopologicalSpace E] [Zero E] (x : E) (n : ℕ) :
    c0SingleZero x n = (if n = 0 then x else 0) := rfl

theorem no_implementing_star_hom
    {A : Type*} [CStarAlgebra A] [Nontrivial A]
    (α : A →⋆ₙₐ[ℂ] A)
    (hα : α 1 = 1)
    (hessential : ∀ a : A,
      (∀ x : (⊥ : NonUnitalStarSubalgebra ℂ A).comap α, a * (x : A) = 0) → a = 0) :
    let I := (⊥ : NonUnitalStarSubalgebra ℂ A).comap α
    letI : ContinuousStar I :=
      ⟨(continuous_star.comp continuous_subtype_val).subtype_mk _⟩
    let B := A × ZeroAtInftyContinuousMap ℕ I
    ¬ ∃ β : B →⋆ₙₐ[ℂ] B, ∀ b b' : B,
      (β b * b').1 = α b.1 * b'.1 ∧
      (↑((β b * b').2 0) : A) = α b.1 * ↑(b'.2 0) ∧
      ∀ n : ℕ, (↑((β b * b').2 (n + 1)) : A) =
        (↑(b.2 n) : A) * ↑(b'.2 (n + 1)) := by
  dsimp only
  intro h
  rcases h with ⟨β, hβ⟩
  letI : ContinuousStar ((⊥ : NonUnitalStarSubalgebra ℂ A).comap α) :=
    ⟨(continuous_star.comp continuous_subtype_val).subtype_mk _⟩
  let I := (⊥ : NonUnitalStarSubalgebra ℂ A).comap α
  let b0 : A × ZeroAtInftyContinuousMap ℕ I := (1, 0)
  let d : I := (β b0).2 0
  have hleft : ∀ x : I, ((d : A) * (x : A)) = (x : A) := by
    intro x
    let bx : A × ZeroAtInftyContinuousMap ℕ I := (0, c0SingleZero x)
    have hx := (hβ b0 bx).2.1
    simpa [b0, bx, d, hα] using hx
  have hd_eq : (d : A) = 1 := by
    have hzero : ∀ x : (⊥ : NonUnitalStarSubalgebra ℂ A).comap α,
        (((d : A) - 1) * (x : A)) = 0 := by
      intro x
      rw [sub_mul, one_mul, hleft x, sub_self]
    exact sub_eq_zero.mp (hessential ((d : A) - 1) hzero)
  have hdα : α (d : A) = 0 := by
    have hmem : α (d : A) ∈ (⊥ : NonUnitalStarSubalgebra ℂ A) :=
      (NonUnitalStarSubalgebra.mem_comap (⊥ : NonUnitalStarSubalgebra ℂ A) α (d : A)).mp d.property
    exact NonUnitalStarAlgebra.mem_bot.mp hmem
  have h10 : (1 : A) = 0 := by
    calc
      (1 : A) = α 1 := hα.symm
      _ = α (d : A) := by rw [hd_eq]
      _ = 0 := hdα
  exact one_ne_zero h10

end Rollout_p2342_c0singlezero_apply

#check_dependency_graph "Rollout_p2342_c0singlezero_apply.c0SingleZero_apply" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(Rollout_p2342_c0singlezero_apply.c0SingleZero x) n = (Rollout_p2342_c0singlezero_apply.c0SingleZero x) n\"},\"graphEdgeId\":\"h_goal\",\"premises\":[],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2342_c0singlezero_apply\",\"reconstructedProofSha256\":\"726dfca9dc47d67d031d5dd151cd70f9c0ed149aa4a716b805dca98fa931d81d\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p2342_c0singlezero_apply.c0SingleZero_apply\",\"topologySha256\":\"21795638089805f2200533f25659a7f89ca729fc135727d8148dab9b2ca30161\"}"

namespace Rollout_p2468_average_projection_positive_definite

-- graph_id: p2468_average_projection_positive_definite
-- topology_sha256: fcffa0d1dce110e47494d5dc1748590683433e407aeda54d2ca9aeab626ab31f
/- verified submission -/
theorem average_projection_positive_definite
    {n : ℕ} (hn : 1 ≤ n)
    {ι Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (C : ι → Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hC : ⨆ i, C i = ⊤)
    (J : Ω → Finset ι)
    (hproj : Measurable (fun ω =>
      (∑ i ∈ J ω, C i).starProjection))
    (hadm : ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 →
      μ {ω | x ∈ (∑ i ∈ J ω, C i)ᗮ} < 1) :
    ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 →
      0 < inner ℝ x
        ((∫ ω, (∑ i ∈ J ω, C i).starProjection ∂μ) x) := by
  intro x hx
  let K : Ω → Submodule ℝ (EuclideanSpace ℝ (Fin n)) := fun ω => ∑ i ∈ J ω, C i
  have hPint : MeasureTheory.Integrable (fun ω => (K ω).starProjection) μ := by
    refine MeasureTheory.Integrable.of_bound hproj.aestronglyMeasurable 1 ?_
    filter_upwards with ω
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
    intro v
    simpa using Submodule.norm_starProjection_apply_le (K ω) v
  have hφint : MeasureTheory.Integrable (fun ω => (K ω).starProjection x) μ :=
    hPint.apply_continuousLinearMap x
  have hfint : MeasureTheory.Integrable (fun ω => inner ℝ x ((K ω).starProjection x)) μ :=
    MeasureTheory.Integrable.const_inner x hφint
  have hfmeas : Measurable (fun ω => inner ℝ x ((K ω).starProjection x)) :=
    Measurable.const_inner (hproj.apply_continuousLinearMap x)
  have hnonneg : 0 ≤ fun ω => inner ℝ x ((K ω).starProjection x) := by
    intro ω
    have h := Submodule.re_inner_starProjection_nonneg (K ω) x
    convert h using 1
    rw [real_inner_comm]
    rfl
  have hnormsq (ω : Ω) :
      inner ℝ x ((K ω).starProjection x) = ‖(K ω).orthogonalProjection x‖ ^ 2 := by
    have h := Submodule.re_inner_starProjection_eq_normSq (K ω) x
    convert h using 1
    · rw [real_inner_comm]
      rfl
  have hsupp : Function.support (fun ω => inner ℝ x ((K ω).starProjection x)) =
      {ω | x ∈ (K ω)ᗮ}ᶜ := by
    ext ω
    constructor
    · intro hsupport horth
      have hsne : inner ℝ x ((K ω).starProjection x) ≠ 0 := Function.mem_support.mp hsupport
      have hpzero : (K ω).starProjection x = 0 :=
        (Submodule.starProjection_apply_eq_zero_iff (K ω)).2 horth
      exact hsne (by simp [hpzero])
    · intro hnotorth
      rw [Function.mem_support]
      by_contra hinner
      have hsquarezero : ‖(K ω).orthogonalProjection x‖ ^ 2 = 0 := by
        rw [← hnormsq ω, hinner]
      have hprojzero : (K ω).orthogonalProjection x = 0 := by
        have hnormzero : ‖(K ω).orthogonalProjection x‖ = 0 :=
          eq_zero_of_pow_eq_zero hsquarezero
        exact norm_eq_zero.mp hnormzero
      exact hnotorth ((Submodule.orthogonalProjection_eq_zero_iff).1 hprojzero)
  have hbad_meas : MeasurableSet {ω | x ∈ (K ω)ᗮ} := by
    have h := (measurableSet_support hfmeas).compl
    rwa [hsupp, compl_compl] at h
  have hsupp_pos :
      0 < μ (Function.support (fun ω => inner ℝ x ((K ω).starProjection x))) := by
    have hcomp : 0 < μ {ω | x ∈ (K ω)ᗮ}ᶜ := by
      rw [MeasureTheory.prob_compl_eq_one_sub hbad_meas]
      exact tsub_pos_iff_lt.2 (hadm x hx)
    rwa [hsupp]
  have hintpos : 0 < ∫ ω, inner ℝ x ((K ω).starProjection x) ∂μ :=
    (MeasureTheory.integral_pos_iff_support_of_nonneg hnonneg hfint).2 hsupp_pos
  calc
    0 < ∫ ω, inner ℝ x ((K ω).starProjection x) ∂μ := hintpos
    _ = inner ℝ x (∫ ω, (K ω).starProjection x ∂μ) := integral_inner hφint x
    _ = inner ℝ x ((∫ ω, (K ω).starProjection ∂μ) x) := by
      rw [ContinuousLinearMap.integral_apply hPint x]

end Rollout_p2468_average_projection_positive_definite

#check_dependency_graph "Rollout_p2468_average_projection_positive_definite.average_projection_positive_definite" against "{\"edges\":[{\"conclusion\":{\"name\":\"hPint\",\"statement\":\"MeasureTheory.Integrable (fun ω => (K ω).starProjection) μ\"},\"graphEdgeId\":\"h_001_hpint\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"MeasureTheory.IsProbabilityMeasure μ\"},{\"name\":\"hproj\",\"statement\":\"Measurable fun ω => (∑ i ∈ J ω, C i).starProjection\"}],\"rawEdgeId\":\"telescope_15\"},{\"conclusion\":{\"name\":\"hfmeas\",\"statement\":\"Measurable fun ω => inner ℝ x ((K ω).starProjection x)\"},\"graphEdgeId\":\"h_004_hfmeas\",\"premises\":[{\"name\":\"hproj\",\"statement\":\"Measurable fun ω => (∑ i ∈ J ω, C i).starProjection\"}],\"rawEdgeId\":\"telescope_18\"},{\"conclusion\":{\"name\":\"hnonneg\",\"statement\":\"0 ≤ fun ω => inner ℝ x ((K ω).starProjection x)\"},\"graphEdgeId\":\"h_005_hnonneg\",\"premises\":[],\"rawEdgeId\":\"telescope_19\"},{\"conclusion\":{\"name\":\"hnormsq\",\"statement\":\"∀ (ω : Ω), inner ℝ x ((K ω).starProjection x) = ‖(K ω).orthogonalProjection x‖ ^ 2\"},\"graphEdgeId\":\"h_006_hnormsq\",\"premises\":[],\"rawEdgeId\":\"telescope_20\"},{\"conclusion\":{\"name\":\"hφint\",\"statement\":\"MeasureTheory.Integrable (fun ω => (K ω).starProjection x) μ\"},\"graphEdgeId\":\"h_002_h_int\",\"premises\":[{\"name\":\"hPint\",\"statement\":\"MeasureTheory.Integrable (fun ω => (K ω).starProjection) μ\"}],\"rawEdgeId\":\"telescope_16\"},{\"conclusion\":{\"name\":\"hsupp\",\"statement\":\"(Function.support fun ω => inner ℝ x ((K ω).starProjection x)) = {ω | x ∈ (K ω)ᗮ}ᶜ\"},\"graphEdgeId\":\"h_007_hsupp\",\"premises\":[{\"name\":\"hnormsq\",\"statement\":\"∀ (ω : Ω), inner ℝ x ((K ω).starProjection x) = ‖(K ω).orthogonalProjection x‖ ^ 2\"}],\"rawEdgeId\":\"telescope_21\"},{\"conclusion\":{\"name\":\"hfint\",\"statement\":\"MeasureTheory.Integrable (fun ω => inner ℝ x ((K ω).starProjection x)) μ\"},\"graphEdgeId\":\"h_003_hfint\",\"premises\":[{\"name\":\"hφint\",\"statement\":\"MeasureTheory.Integrable (fun ω => (K ω).starProjection x) μ\"}],\"rawEdgeId\":\"telescope_17\"},{\"conclusion\":{\"name\":\"hbad_meas\",\"statement\":\"MeasurableSet {ω | x ∈ (K ω)ᗮ}\"},\"graphEdgeId\":\"h_008_hbad_meas\",\"premises\":[{\"name\":\"hfmeas\",\"statement\":\"Measurable fun ω => inner ℝ x ((K ω).starProjection x)\"},{\"name\":\"hsupp\",\"statement\":\"(Function.support fun ω => inner ℝ x ((K ω).starProjection x)) = {ω | x ∈ (K ω)ᗮ}ᶜ\"}],\"rawEdgeId\":\"telescope_22\"},{\"conclusion\":{\"name\":\"hsupp_pos\",\"statement\":\"0 < μ (Function.support fun ω => inner ℝ x ((K ω).starProjection x))\"},\"graphEdgeId\":\"h_009_hsupp_pos\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"MeasureTheory.IsProbabilityMeasure μ\"},{\"name\":\"hadm\",\"statement\":\"∀ (x : EuclideanSpace ℝ (Fin n)), x ≠ 0 → μ {ω | x ∈ (∑ i ∈ J ω, C i)ᗮ} < 1\"},{\"name\":\"hx\",\"statement\":\"x ≠ 0\"},{\"name\":\"hsupp\",\"statement\":\"(Function.support fun ω => inner ℝ x ((K ω).starProjection x)) = {ω | x ∈ (K ω)ᗮ}ᶜ\"},{\"name\":\"hbad_meas\",\"statement\":\"MeasurableSet {ω | x ∈ (K ω)ᗮ}\"}],\"rawEdgeId\":\"telescope_23\"},{\"conclusion\":{\"name\":\"hintpos\",\"statement\":\"0 < ∫ (ω : Ω), inner ℝ x ((K ω).starProjection x) ∂μ\"},\"graphEdgeId\":\"h_010_hintpos\",\"premises\":[{\"name\":\"hfint\",\"statement\":\"MeasureTheory.Integrable (fun ω => inner ℝ x ((K ω).starProjection x)) μ\"},{\"name\":\"hnonneg\",\"statement\":\"0 ≤ fun ω => inner ℝ x ((K ω).starProjection x)\"},{\"name\":\"hsupp_pos\",\"statement\":\"0 < μ (Function.support fun ω => inner ℝ x ((K ω).starProjection x))\"}],\"rawEdgeId\":\"telescope_24\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"0 < inner ℝ x ((∫ (ω : Ω), (K ω).starProjection ∂μ) x)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hPint\",\"statement\":\"MeasureTheory.Integrable (fun ω => (K ω).starProjection) μ\"},{\"name\":\"hφint\",\"statement\":\"MeasureTheory.Integrable (fun ω => (K ω).starProjection x) μ\"},{\"name\":\"hintpos\",\"statement\":\"0 < ∫ (ω : Ω), inner ℝ x ((K ω).starProjection x) ∂μ\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2468_average_projection_positive_definite\",\"reconstructedProofSha256\":\"c3c2ee76601932c699ac0058aeec3c0ffcfebd03cf300d82c76c78f06319c2d7\",\"selectedEdgeCount\":11,\"theoremName\":\"Rollout_p2468_average_projection_positive_definite.average_projection_positive_definite\",\"topologySha256\":\"fcffa0d1dce110e47494d5dc1748590683433e407aeda54d2ca9aeab626ab31f\"}"

namespace Rollout_p2476_approximatepointspectrum_subset_closure_sc

-- graph_id: p2476_approximatepointspectrum_subset_closure_sc
-- topology_sha256: 0c595635aee944b581bdaea9c8a2ecb86c55cb527f19e24cd9f57e497d699998
/- accepted add_to_file helper 1 -/
lemma srg_sqrt_sq_add_sq_le_abs_add {u q : ℝ} (hq : 0 ≤ q) :
    Real.sqrt (u ^ 2 + q ^ 2) ≤ |u| + q := by
  apply le_of_sq_le_sq
  · rw [Real.sq_sqrt (by positivity)]
    nlinarith [sq_abs u, abs_nonneg u, hq]
  · positivity

lemma srg_abs_sub_sqrt_sq_add_sq_le {u q : ℝ} (hq : 0 ≤ q) :
    |(|u| - Real.sqrt (u ^ 2 + q ^ 2))| ≤ q := by
  have hupper : Real.sqrt (u ^ 2 + q ^ 2) ≤ |u| + q :=
    srg_sqrt_sq_add_sq_le_abs_add hq
  have hlower : |u| ≤ Real.sqrt (u ^ 2 + q ^ 2) := by
    apply Real.abs_le_sqrt
    nlinarith [sq_nonneg q]
  rw [abs_sub_le_iff]
  constructor
  · nlinarith [Real.sqrt_nonneg (u ^ 2 + q ^ 2)]
  · nlinarith

lemma scaledRelativeGraph_polar_approx
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) {x : H} (hx : ‖x‖ = 1) (w : ℂ) :
    ∃ z : ℂ,
      (let a : ℝ := (inner ℂ (T x) x).re
       let b : ℝ := Real.sqrt (‖T x‖ ^ 2 - a ^ 2)
       z = (a : ℂ) + Complex.I * (b : ℂ) ∨
         z = (a : ℂ) - Complex.I * (b : ℂ)) ∧
      dist w z ≤ 2 * ‖T x - w • x‖ := by
  let α : ℂ := inner ℂ (T x) x
  let c : ℂ := star α
  let y : H := T x - c • x
  let a : ℝ := α.re
  let b : ℝ := Real.sqrt (‖T x‖ ^ 2 - a ^ 2)
  have hyx : inner ℂ y x = 0 := by
    dsimp [y, c, α]
    rw [inner_sub_left, inner_smul_left, inner_self_eq_norm_sq_to_K, hx]
    simp
  have hxy : inner ℂ x y = 0 := (inner_eq_zero_symm).1 hyx
  have hortho : inner ℂ (c • x) y = 0 := by
    rw [inner_smul_left, hxy]
    simp
  have hpyth : ‖c • x + y‖ ^ 2 = ‖c • x‖ ^ 2 + ‖y‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (c • x) y hortho
    nlinarith
  have hTxeq : c • x + y = T x := by
    simp [y]
  rw [hTxeq] at hpyth
  have hc : ‖c • x‖ = ‖c‖ := by
    simp [norm_smul, hx]
  have hcn : ‖c • x‖ ^ 2 = ‖c‖ ^ 2 := by
    rw [hc]
  have hcre : c.re = a := by
    dsimp [c, a, α]
  have hc_sq : ‖c‖ ^ 2 = a ^ 2 + c.im ^ 2 := by
    calc
      ‖c‖ ^ 2 = Complex.normSq c := by
        rw [Complex.normSq_eq_norm_sq]
      _ = c.re * c.re + c.im * c.im := by
        rw [Complex.normSq_apply]
      _ = a ^ 2 + c.im ^ 2 := by
        rw [hcre]
        ring
  have hb_sq : ‖T x‖ ^ 2 - a ^ 2 = c.im ^ 2 + ‖y‖ ^ 2 := by
    nlinarith
  have hb : b = Real.sqrt (c.im ^ 2 + ‖y‖ ^ 2) := by
    dsimp [b]
    rw [hb_sq]
  have horthod : inner ℂ ((c - w) • x) y = 0 := by
    rw [inner_smul_left, hxy]
    simp
  have hdeq : T x - w • x = (c - w) • x + y := by
    rw [sub_smul]
    simp [y]
  have hpythd : ‖(c - w) • x + y‖ ^ 2 = ‖(c - w) • x‖ ^ 2 + ‖y‖ ^ 2 := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero ((c - w) • x) y horthod
    nlinarith
  rw [← hdeq] at hpythd
  have hcwn : ‖(c - w) • x‖ = ‖c - w‖ := by
    simp [norm_smul, hx]
  have hcwnsq : ‖(c - w) • x‖ ^ 2 = ‖c - w‖ ^ 2 := by
    rw [hcwn]
  have hcw_sq : ‖c - w‖ ^ 2 ≤ ‖T x - w • x‖ ^ 2 := by
    nlinarith [sq_nonneg ‖y‖]
  have hy_sq : ‖y‖ ^ 2 ≤ ‖T x - w • x‖ ^ 2 := by
    nlinarith [sq_nonneg ‖c - w‖]
  have hcw_le : ‖c - w‖ ≤ ‖T x - w • x‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hcw_sq
  have hy_le : ‖y‖ ≤ ‖T x - w • x‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hy_sq
  have hsqrt_abs : |(|c.im| - Real.sqrt (c.im ^ 2 + ‖y‖ ^ 2))| ≤ ‖y‖ :=
    srg_abs_sub_sqrt_sq_add_sq_le (norm_nonneg y)
  have hsqrt_abs' : |(|c.im| - b)| ≤ ‖y‖ := by
    simpa [hb] using hsqrt_abs
  by_cases hcim : 0 ≤ c.im
  · refine ⟨a + Complex.I * (b : ℂ), Or.inl rfl, ?_⟩
    have hcdiff :
        c - ((c.re : ℂ) + Complex.I * (b : ℂ)) =
          Complex.I * ((c.im - b : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simp
    have hz : (a : ℂ) + Complex.I * (b : ℂ) =
        (c.re : ℂ) + Complex.I * (b : ℂ) := by
      rw [hcre]
    have hnorm_cz : ‖c - ((a : ℂ) + Complex.I * (b : ℂ))‖ = |c.im - b| := by
      rw [hz, hcdiff]
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have him : |c.im - b| ≤ ‖y‖ := by
      have hcabs : |c.im| = c.im := abs_of_nonneg hcim
      have h := hsqrt_abs'
      rw [hcabs] at h
      exact h
    calc
      dist w ((a : ℂ) + Complex.I * (b : ℂ))
          ≤ dist w c + dist c ((a : ℂ) + Complex.I * (b : ℂ)) :=
        dist_triangle w c _
      _ = ‖w - c‖ + ‖c - ((a : ℂ) + Complex.I * (b : ℂ))‖ := by
        rw [dist_eq_norm, dist_eq_norm]
      _ ≤ ‖T x - w • x‖ + ‖y‖ := by
        gcongr
        · rw [norm_sub_rev]
          exact hcw_le
        · rw [hnorm_cz]
          exact him
      _ ≤ 2 * ‖T x - w • x‖ := by
        nlinarith
  · have hcimneg : c.im < 0 := lt_of_not_ge hcim
    refine ⟨a - Complex.I * (b : ℂ), Or.inr rfl, ?_⟩
    have hcdiff :
        c - ((c.re : ℂ) - Complex.I * (b : ℂ)) =
          Complex.I * ((c.im + b : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · simp
    have hz : (a : ℂ) - Complex.I * (b : ℂ) =
        (c.re : ℂ) - Complex.I * (b : ℂ) := by
      rw [hcre]
    have hnorm_cz : ‖c - ((a : ℂ) - Complex.I * (b : ℂ))‖ = |c.im + b| := by
      rw [hz, hcdiff]
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have him : |c.im + b| ≤ ‖y‖ := by
      have hEq : |c.im + b| = |(|c.im| - b)| := by
        rw [abs_of_neg hcimneg]
        rw [show -c.im - b = -(c.im + b) by ring]
        rw [abs_neg]
      rw [hEq]
      exact hsqrt_abs'
    calc
      dist w ((a : ℂ) - Complex.I * (b : ℂ))
          ≤ dist w c + dist c ((a : ℂ) - Complex.I * (b : ℂ)) :=
        dist_triangle w c _
      _ = ‖w - c‖ + ‖c - ((a : ℂ) - Complex.I * (b : ℂ))‖ := by
        rw [dist_eq_norm, dist_eq_norm]
      _ ≤ ‖T x - w • x‖ + ‖y‖ := by
        gcongr
        · rw [norm_sub_rev]
          exact hcw_le
        · rw [hnorm_cz]
          exact him
      _ ≤ 2 * ‖T x - w • x‖ := by
        nlinarith

/- verified submission -/
theorem approximatePointSpectrum_subset_closure_scaledRelativeGraph_polar
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) :
    {w : ℂ |
        ∃ x : ℕ → H,
          (∀ n : ℕ, ‖x n‖ = 1) ∧
            Filter.Tendsto (fun n : ℕ => ‖T (x n) - w • x n‖)
              Filter.atTop (nhds 0)} ⊆
      closure
        {z : ℂ |
          ∃ x : H, ‖x‖ = 1 ∧
            let a : ℝ := (inner ℂ (T x) x).re
            let b : ℝ := Real.sqrt (‖T x‖ ^ 2 - a ^ 2)
            z = (a : ℂ) + Complex.I * (b : ℂ) ∨
              z = (a : ℂ) - Complex.I * (b : ℂ)} := by
  intro w hw
  rcases hw with ⟨x, hxnorm, hlim⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hδ : 0 < ε / 2 := by positivity
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hlim (ε / 2) hδ
  have hr : ‖T (x N) - w • x N‖ < ε / 2 := by
    have h := hN N le_rfl
    simpa [dist_eq_norm, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using h
  obtain ⟨z, hzgraph, hzdist⟩ :=
    scaledRelativeGraph_polar_approx T (hxnorm N) w
  refine ⟨z, ?_, ?_⟩
  · exact ⟨x N, hxnorm N, hzgraph⟩
  · calc
      dist w z ≤ 2 * ‖T (x N) - w • x N‖ := hzdist
      _ < ε := by nlinarith

end Rollout_p2476_approximatepointspectrum_subset_closure_sc

#check_dependency_graph "Rollout_p2476_approximatepointspectrum_subset_closure_sc.approximatePointSpectrum_subset_closure_scaledRelativeGraph_polar" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"w ∈ closure {z | ∃ x, ‖x‖ = 1 ∧ let a := (inner ℂ (T x) x).re; let b := √(‖T x‖ ^ 2 - a ^ 2); z = ↑a + Complex.I * ↑b ∨ z = ↑a - Complex.I * ↑b}\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hw\",\"statement\":\"w ∈ {w | ∃ x, (∀ (n : ℕ), ‖x n‖ = 1) ∧ Filter.Tendsto (fun n => ‖T (x n) - w • x n‖) Filter.atTop (nhds 0)}\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2476_approximatepointspectrum_subset_closure_sc\",\"reconstructedProofSha256\":\"5d8ea053d9be55b631b620d799cac392ef98ec73b3e2af01ed7eef248a1ede21\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p2476_approximatepointspectrum_subset_closure_sc.approximatePointSpectrum_subset_closure_scaledRelativeGraph_polar\",\"topologySha256\":\"0c595635aee944b581bdaea9c8a2ecb86c55cb527f19e24cd9f57e497d699998\"}"

namespace Rollout_p2581_looptree_height_bound

-- graph_id: p2581_looptree_height_bound
-- topology_sha256: b7ec0112d20e1e455666de77441337e930d042a56ef4ed9c1c4be27d8ce7cc77
/- accepted add_to_file helper 1 -/
noncomputable def treeHeight (τ : Finset (List ℕ)) : ℕ := τ.sup List.length

lemma treeHeight_le {τ : Finset (List ℕ)} {v : List ℕ} (hv : v ∈ τ) :
    v.length ≤ treeHeight τ := by
  exact Finset.le_sup (f := List.length) hv

def subtree (τ : Finset (List ℕ)) (v : List ℕ) : Finset (List ℕ) :=
  τ.filter (fun x => v <+: x)

lemma subtree_eq_insert_biUnion
    (τ : Finset (List ℕ)) (k : List ℕ → ℕ)
    (hprefix : ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    {v : List ℕ} (hv : v ∈ τ) :
    subtree τ v =
      insert v ((Finset.Icc 1 (k v)).biUnion (fun m => subtree τ (v ++ [m]))) := by
  ext x
  constructor
  · intro hx
    have hxτ : x ∈ τ := (Finset.mem_filter.mp hx).1
    have hpre : v <+: x := (Finset.mem_filter.mp hx).2
    rcases hpre with ⟨t, rfl⟩
    cases t with
    | nil =>
        simp
    | cons a rest =>
        have hprefix_child : v ++ [a] <+: v ++ (a :: rest) := by
          refine ⟨rest, ?_⟩
          simp [List.append_assoc]
        have hchildmem : v ++ [a] ∈ τ := hprefix hxτ hprefix_child
        have ha : 1 ≤ a ∧ a ≤ k v := (hchildren v hv a).mp hchildmem
        simp [subtree, Finset.mem_biUnion, ha, hxτ]
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_Icc] at hx
    rcases hx with rfl | ⟨m, hm, hmsub⟩
    · simp [subtree, hv]
    · have hmpre : v <+: v ++ [m] := by
        refine ⟨[m], ?_⟩
        simp
      have hxpre : v ++ [m] <+: x := (Finset.mem_filter.mp hmsub).2
      have hxτ : x ∈ τ := (Finset.mem_filter.mp hmsub).1
      exact Finset.mem_filter.mpr ⟨hxτ, hmpre.trans hxpre⟩

/- accepted add_to_file helper 2 -/
lemma subtree_children_disjoint
    (τ : Finset (List ℕ)) (k : List ℕ → ℕ) (v : List ℕ) :
    (↑(Finset.Icc 1 (k v)) : Set ℕ).PairwiseDisjoint
      (fun m => subtree τ (v ++ [m])) := by
  intro a ha b hb hne
  rw [Function.onFun]
  apply Finset.disjoint_left.mpr
  intro x hxa hxb
  have hpa : v ++ [a] <+: x := (Finset.mem_filter.mp hxa).2
  have hpb : v ++ [b] <+: x := (Finset.mem_filter.mp hxb).2
  have hcomp := List.prefix_or_prefix_of_prefix hpa hpb
  have hlen : (v ++ [a]).length = (v ++ [b]).length := by simp
  have hchild : v ++ [a] = v ++ [b] := by
    rcases hcomp with hp | hp
    · exact hp.eq_of_length hlen
    · exact (hp.eq_of_length hlen.symm).symm
  have hsingle : [a] = [b] := List.append_right_injective v hchild
  have hab : a = b := by simpa using hsingle
  exact hne hab

lemma subtree_parent_not_mem_children_biUnion
    (τ : Finset (List ℕ)) (k : List ℕ → ℕ) (v : List ℕ) :
    v ∉ (Finset.Icc 1 (k v)).biUnion (fun m => subtree τ (v ++ [m])) := by
  intro hv
  simp only [Finset.mem_biUnion, Finset.mem_Icc] at hv
  rcases hv with ⟨m, hm, hmsub⟩
  have hpre : v ++ [m] <+: v := (Finset.mem_filter.mp hmsub).2
  have hlen := hpre.length_le
  simp at hlen

lemma subtree_sum_rec
    (τ : Finset (List ℕ)) (k : List ℕ → ℕ)
    (hprefix : ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    {v : List ℕ} (hv : v ∈ τ)
    (ih : ∀ m : ℕ, 1 ≤ m → m ≤ k v →
      (∑ x ∈ subtree τ (v ++ [m]), ((k x : ℤ) - 1)) = -1) :
    (∑ x ∈ subtree τ v, ((k x : ℤ) - 1)) = -1 := by
  rw [subtree_eq_insert_biUnion τ k hprefix hchildren hv]
  rw [Finset.sum_insert (subtree_parent_not_mem_children_biUnion τ k v)]
  rw [Finset.sum_biUnion (subtree_children_disjoint τ k v)]
  have hsum : (∑ m ∈ Finset.Icc 1 (k v),
      ∑ x ∈ subtree τ (v ++ [m]), ((k x : ℤ) - 1)) =
      ∑ m ∈ Finset.Icc 1 (k v), (-1 : ℤ) := by
    apply Finset.sum_congr rfl
    intro m hm
    have hm' : 1 ≤ m ∧ m ≤ k v := Finset.mem_Icc.mp hm
    exact ih m hm'.1 hm'.2
  rw [hsum]
  simp
  ring

/- accepted add_to_file helper 3 -/
lemma subtree_weight_sum_gap
    (τ : Finset (List ℕ)) (k : List ℕ → ℕ)
    (hprefix : ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v) :
    ∀ n : ℕ, ∀ {v : List ℕ}, v ∈ τ → treeHeight τ - v.length ≤ n →
      (∑ x ∈ subtree τ v, ((k x : ℤ) - 1)) = -1 := by
  intro n
  induction n with
  | zero =>
      intro v hv hgap
      have hk : k v = 0 := by
        by_contra hne
        have hpos : 0 < k v := Nat.pos_of_ne_zero hne
        have hchild : v ++ [1] ∈ τ := (hchildren v hv 1).mpr ⟨le_rfl, hpos⟩
        have hlechild := treeHeight_le hchild
        have hle : treeHeight τ ≤ v.length := by
          have hzero : treeHeight τ - v.length = 0 := Nat.le_zero.mp hgap
          exact (Nat.sub_eq_zero_iff_le).mp hzero
        have hlen : (v ++ [1]).length = v.length + 1 := by simp
        omega
      exact subtree_sum_rec τ k hprefix hchildren hv (by
        intro m hm1 hmk
        omega)
  | succ n ihn =>
      intro v hv hgap
      exact subtree_sum_rec τ k hprefix hchildren hv (by
        intro m hm1 hmk
        have hchild : v ++ [m] ∈ τ := (hchildren v hv m).mpr ⟨hm1, hmk⟩
        have hlechild := treeHeight_le hchild
        have hlen : (v ++ [m]).length = v.length + 1 := by simp
        apply ihn hchild
        omega)

lemma subtree_weight_sum
    (τ : Finset (List ℕ)) (k : List ℕ → ℕ)
    (hprefix : ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    {v : List ℕ} (hv : v ∈ τ) :
    (∑ x ∈ subtree τ v, ((k x : ℤ) - 1)) = -1 := by
  exact subtree_weight_sum_gap τ k hprefix hchildren
    (treeHeight τ - v.length) hv le_rfl

/- accepted add_to_file helper 4 -/
def finPred {N : ℕ} (j : Fin N) (hj : 0 < j.val) : Fin N :=
  ⟨j.val - 1, by
    have hN := j.isLt
    omega⟩

lemma finPred_succ_eq_castSucc {N : ℕ} (j : Fin N) (hj : 0 < j.val) :
    (finPred j hj).succ = j.castSucc := by
  apply Fin.ext
  simp [finPred]
  omega

lemma mem_Icc_finPred_iff {N : ℕ} {i r j : Fin N} (hj : 0 < j.val) :
    r ∈ Finset.Icc i (finPred j hj) ↔ i ≤ r ∧ r < j := by
  simp [finPred]
  intro hir
  show r.val ≤ j.val - 1 ↔ r.val < j.val
  omega

/- accepted add_to_file helper 5 -/
lemma W_diff_eq_sum_interval
    {N : ℕ} {τ : Finset (List ℕ)} {k : List ℕ → ℕ}
    {u : Fin N ≃ {v : List ℕ // v ∈ τ}}
    {W : Fin (N + 1) → ℤ}
    (hWstep : ∀ r : Fin N,
      W r.succ = W r.castSucc + (k (u r).1 : ℤ) - 1)
    {i j : Fin N} (hij : i < j) (hj : 0 < j.val) :
    W j.castSucc - W i.castSucc =
      ∑ r ∈ Finset.Icc i (finPred j hj),
        ((k (u r).1 : ℤ) - 1) := by
  have hle : i ≤ finPred j hj := by
    change i.val ≤ (finPred j hj).val
    simp [finPred]
    have : i.val < j.val := hij
    omega
  have htel := Fin.sum_Icc_sub hle W
  calc
    W j.castSucc - W i.castSucc
        = ∑ r ∈ Finset.Icc i (finPred j hj), (W r.succ - W r.castSucc) := by
            rw [htel, finPred_succ_eq_castSucc]
    _ = ∑ r ∈ Finset.Icc i (finPred j hj),
          ((k (u r).1 : ℤ) - 1) := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [hWstep r]
            ring

/- accepted add_to_file helper 6 -/
lemma lex_sandwich_prefix :
    ∀ {a c x : List ℕ}, a <+: c →
      List.Lex (fun p q : ℕ => p < q) a x →
      List.Lex (fun p q : ℕ => p < q) x c → a <+: x := by
  intro a
  induction a with
  | nil =>
      intro c x hac hax hxc
      exact List.nil_prefix
  | cons a as ih =>
      intro c x hac hax hxc
      rcases hac with ⟨t, rfl⟩
      cases x with
      | nil =>
          cases hax
      | cons b bs =>
          cases hax with
          | rel hab =>
              cases hxc with
              | rel hba => omega
              | cons htail => omega
          | cons htail =>
              have htailxc : List.Lex (fun p q : ℕ => p < q) bs (as ++ t) := by
                cases hxc with
                | rel hba => omega
                | cons h => exact h
              have hprefix_as : as <+: as ++ t := by
                refine ⟨t, rfl⟩
              have hp := ih (c := as ++ t) (x := bs) hprefix_as htail htailxc
              rcases hp with ⟨s, hs⟩
              refine ⟨s, ?_⟩
              simpa using congrArg (fun z => a :: z) hs

lemma lex_append_left_cancel {s x y : List ℕ} :
    List.Lex (fun a b : ℕ => a < b) (s ++ x) (s ++ y) →
    List.Lex (fun a b : ℕ => a < b) x y := by
  induction s generalizing x y with
  | nil =>
      intro h
      exact h
  | cons a s ih =>
      intro h
      have h' : List.Lex (fun p q : ℕ => p < q)
          (a :: (s ++ x)) (a :: (s ++ y)) := by
        simpa using h
      cases h' with
      | rel hrel => omega
      | cons htail => exact ih htail

lemma lex_append_left_iff (s x y : List ℕ) :
    List.Lex (fun a b : ℕ => a < b) (s ++ x) (s ++ y) ↔
      List.Lex (fun a b : ℕ => a < b) x y := by
  constructor
  · exact lex_append_left_cancel
  · intro h
    exact List.Lex.append_left _ h s

lemma lex_interval_image
    {N : ℕ} {τ : Finset (List ℕ)}
    {u : Fin N ≃ {v : List ℕ // v ∈ τ}}
    (hlex : ∀ a b : Fin N, a < b ↔
      List.Lex (fun x y : ℕ => x < y) (u a).1 (u b).1)
    {i j : Fin N} (hj : 0 < j.val) :
    (Finset.Icc i (finPred j hj)).image (fun r => (u r).1) =
      τ.filter (fun x =>
        (x = (u i).1 ∨ List.Lex (fun a b : ℕ => a < b) (u i).1 x) ∧
        List.Lex (fun a b : ℕ => a < b) x (u j).1) := by
  ext x
  constructor
  · intro hx
    simp only [Finset.mem_image] at hx
    rcases hx with ⟨r, hr, rfl⟩
    have hrb := (mem_Icc_finPred_iff (i := i) (r := r) (j := j) hj).mp hr
    have hlower : (u r).1 = (u i).1 ∨
        List.Lex (fun a b : ℕ => a < b) (u i).1 (u r).1 := by
      rcases eq_or_lt_of_le hrb.1 with heq | hlt
      · left
        rw [heq]
      · right
        exact (hlex i r).mp hlt
    have hupper : List.Lex (fun a b : ℕ => a < b) (u r).1 (u j).1 :=
      (hlex r j).mp hrb.2
    exact Finset.mem_filter.mpr ⟨(u r).2, ⟨hlower, hupper⟩⟩
  · intro hx
    have hxτ : x ∈ τ := (Finset.mem_filter.mp hx).1
    have hbounds := (Finset.mem_filter.mp hx).2
    let r : Fin N := u.symm ⟨x, hxτ⟩
    have hur : u r = ⟨x, hxτ⟩ := Equiv.apply_symm_apply u ⟨x, hxτ⟩
    have hurl : (u r).1 = x := congrArg Subtype.val hur
    have hir : i ≤ r := by
      rcases hbounds.1 with heq | hlt
      · have hsub : u i = ⟨x, hxτ⟩ := by
          apply Subtype.ext
          exact heq.symm
        have hfi : i = r := by
          apply u.injective
          rw [hsub, hur]
        rw [hfi]
      · have hlt' : i < r := by
          apply (hlex i r).mpr
          rw [hurl]
          exact hlt
        exact le_of_lt hlt'
    have hrj : r < j := by
      apply (hlex r j).mpr
      rw [hurl]
      exact hbounds.2
    refine Finset.mem_image.mpr ⟨r, ?_, ?_⟩
    · exact (mem_Icc_finPred_iff (i := i) (r := r) (j := j) hj).mpr ⟨hir, hrj⟩
    · exact hurl

/- accepted add_to_file helper 7 -/
lemma lex_interval_parent_child
    (τ : Finset (List ℕ)) (k : List ℕ → ℕ)
    (hprefix : ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    {a : List ℕ} (ha : a ∈ τ) {m : ℕ} (hm : 1 ≤ m ∧ m ≤ k a) :
    τ.filter (fun x =>
        (x = a ∨ List.Lex (fun p q : ℕ => p < q) a x) ∧
        List.Lex (fun p q : ℕ => p < q) x (a ++ [m])) =
      insert a ((Finset.Icc 1 (m - 1)).biUnion
        (fun q => subtree τ (a ++ [q]))) := by
  ext x
  constructor
  · intro hx
    have hxτ : x ∈ τ := (Finset.mem_filter.mp hx).1
    have hb := (Finset.mem_filter.mp hx).2
    rcases hb.1 with heq | hlower
    · simp [heq]
    · have hac : a <+: a ++ [m] := by
        refine ⟨[m], ?_⟩
        simp
      have hpre : a <+: x := lex_sandwich_prefix hac hlower hb.2
      rcases hpre with ⟨t, rfl⟩
      cases t with
      | nil =>
          have haa : List.Lex (fun p q : ℕ => p < q) a a := by
            simpa using hlower
          exact (List.lex_irrefl (fun n : ℕ => lt_irrefl n) a haa).elim
      | cons q rest =>
          have hprefix_child : a ++ [q] <+: a ++ (q :: rest) := by
            refine ⟨rest, ?_⟩
            simp [List.append_assoc]
          have hchildτ : a ++ [q] ∈ τ := hprefix hxτ hprefix_child
          have hqvalid : 1 ≤ q ∧ q ≤ k a := (hchildren a ha q).mp hchildτ
          have hqlex : List.Lex (fun p q : ℕ => p < q) (q :: rest) [m] := by
            apply lex_append_left_cancel
            simpa using hb.2
          have hqm : q < m := by
            cases hqlex with
            | rel h => exact h
            | cons h => cases h
          have hqle : q ≤ m - 1 := by omega
          simp [subtree, Finset.mem_biUnion, hqvalid, hqle, hxτ]
  · intro hx
    simp only [Finset.mem_insert, Finset.mem_biUnion, Finset.mem_Icc] at hx
    rcases hx with heq | ⟨q, hq, hsub⟩
    · rw [heq]
      have hbase : List.Lex (fun p q : ℕ => p < q) [] [m] := List.Lex.nil
      have hupper := List.Lex.append_left _ hbase a
      exact Finset.mem_filter.mpr ⟨ha, ⟨Or.inl rfl, by simpa using hupper⟩⟩
    · have hxτ : x ∈ τ := (Finset.mem_filter.mp hsub).1
      have hchildpre : a ++ [q] <+: x := (Finset.mem_filter.mp hsub).2
      have hqm : q < m := by omega
      have hlower : List.Lex (fun p q : ℕ => p < q) a x := by
        rcases hchildpre with ⟨rest, rfl⟩
        have hbase : List.Lex (fun p q : ℕ => p < q) [] (q :: rest) := List.Lex.nil
        have hlex := List.Lex.append_left _ hbase a
        simpa [List.append_assoc] using hlex
      have hupper : List.Lex (fun p q : ℕ => p < q) x (a ++ [m]) := by
        rcases hchildpre with ⟨rest, rfl⟩
        have htail : List.Lex (fun p q : ℕ => p < q) (q :: rest) [m] :=
          List.Lex.rel hqm
        have hlex := List.Lex.append_left _ htail a
        simpa [List.append_assoc] using hlex
      exact Finset.mem_filter.mpr ⟨hxτ, ⟨Or.inr hlower, hupper⟩⟩

/- accepted add_to_file helper 8 -/
lemma lex_interval_parent_child_weight_sum
    (τ : Finset (List ℕ)) (k : List ℕ → ℕ)
    (hprefix : ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    {a : List ℕ} (ha : a ∈ τ) {m : ℕ} (hm : 1 ≤ m ∧ m ≤ k a) :
    (∑ x ∈ τ.filter (fun x =>
        (x = a ∨ List.Lex (fun p q : ℕ => p < q) a x) ∧
        List.Lex (fun p q : ℕ => p < q) x (a ++ [m])),
      ((k x : ℤ) - 1)) = (k a : ℤ) - m := by
  rw [lex_interval_parent_child τ k hprefix hchildren ha hm]
  have hnotmem : a ∉ (Finset.Icc 1 (m - 1)).biUnion
      (fun q => subtree τ (a ++ [q])) := by
    intro hmem
    have hbig : a ∈ (Finset.Icc 1 (k a)).biUnion
        (fun q => subtree τ (a ++ [q])) := by
      simp only [Finset.mem_biUnion, Finset.mem_Icc] at hmem ⊢
      rcases hmem with ⟨q, hq, hsub⟩
      exact ⟨q, ⟨hq.1, by omega⟩, hsub⟩
    exact subtree_parent_not_mem_children_biUnion τ k a hbig
  have hsub : (↑(Finset.Icc 1 (m - 1)) : Set ℕ) ⊆
      (↑(Finset.Icc 1 (k a)) : Set ℕ) := by
    intro q hq
    simp only [Finset.mem_coe, Finset.mem_Icc] at hq ⊢
    omega
  have hdisj := Set.Pairwise.mono hsub (subtree_children_disjoint τ k a)
  rw [Finset.sum_insert hnotmem]
  rw [Finset.sum_biUnion hdisj]
  have hsum : (∑ q ∈ Finset.Icc 1 (m - 1),
      ∑ x ∈ subtree τ (a ++ [q]), ((k x : ℤ) - 1)) =
      ∑ q ∈ Finset.Icc 1 (m - 1), (-1 : ℤ) := by
    apply Finset.sum_congr rfl
    intro q hq
    have hq' : 1 ≤ q ∧ q ≤ m - 1 := Finset.mem_Icc.mp hq
    have hqle : q ≤ k a := by omega
    have hchild : a ++ [q] ∈ τ := (hchildren a ha q).mpr ⟨hq'.1, hqle⟩
    exact subtree_weight_sum τ k hprefix hchildren hchild
  rw [hsum]
  simp
  have hmcast : (((m - 1 : ℕ) : ℤ) = (m : ℤ) - 1) := by omega
  rw [hmcast]
  ring

/- accepted add_to_file helper 9 -/
lemma W_parent_child_gap
    {N : ℕ} {τ : Finset (List ℕ)} {k : List ℕ → ℕ}
    (hprefix : ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    {u : Fin N ≃ {v : List ℕ // v ∈ τ}}
    (hlex : ∀ a b : Fin N, a < b ↔
      List.Lex (fun x y : ℕ => x < y) (u a).1 (u b).1)
    {W : Fin (N + 1) → ℤ}
    (hWstep : ∀ r : Fin N,
      W r.succ = W r.castSucc + (k (u r).1 : ℤ) - 1)
    {i t : Fin N} (hit : i < t) {m : ℕ}
    (ht : (u t).1 = (u i).1 ++ [m]) :
    W t.castSucc - W i.castSucc = (k (u i).1 : ℤ) - m := by
  have htval : 0 < t.val := by
    have : i.val < t.val := hit
    omega
  have hchildτ : (u i).1 ++ [m] ∈ τ := by
    rw [← ht]
    exact (u t).2
  have hm : 1 ≤ m ∧ m ≤ k (u i).1 :=
    (hchildren (u i).1 (u i).2 m).mp hchildτ
  let s := Finset.Icc i (finPred t htval)
  have hW := W_diff_eq_sum_interval (u := u) hWstep hit htval
  have himage := lex_interval_image (u := u) hlex (i := i) (j := t) htval
  have hinj : Set.InjOn (fun r : Fin N => (u r).1) (↑s : Set (Fin N)) := by
    intro a ha b hb h
    apply u.injective
    apply Subtype.ext
    exact h
  calc
    W t.castSucc - W i.castSucc
        = ∑ r ∈ s, ((k (u r).1 : ℤ) - 1) := hW
    _ = ∑ x ∈ s.image (fun r : Fin N => (u r).1), ((k x : ℤ) - 1) := by
          exact (Finset.sum_image (s := s) (g := fun r : Fin N => (u r).1)
            (f := fun x : List ℕ => (k x : ℤ) - 1) hinj).symm
    _ = ∑ x ∈ τ.filter (fun x =>
          (x = (u i).1 ∨ List.Lex (fun a b : ℕ => a < b) (u i).1 x) ∧
          List.Lex (fun a b : ℕ => a < b) x (u t).1),
          ((k x : ℤ) - 1) := by
          rw [← himage]
    _ = (k (u i).1 : ℤ) - m := by
          rw [ht]
          exact lex_interval_parent_child_weight_sum τ k hprefix hchildren (u i).2 hm

/- accepted add_to_file helper 10 -/
def loopGraph (τ : Finset (List ℕ)) (k : List ℕ → ℕ) :
    SimpleGraph {v : List ℕ // v ∈ τ} :=
  SimpleGraph.fromRel fun x y =>
    (∃ (p : List ℕ) (m : ℕ), p ∈ τ ∧ 1 ≤ m ∧ m < k p ∧
      x.1 = p ++ [m] ∧ y.1 = p ++ [m + 1]) ∨
    (0 < k x.1 ∧ (y.1 = x.1 ++ [1] ∨ y.1 = x.1 ++ [k x.1]))

/- accepted add_to_file helper 11 -/
lemma loop_adj_parent_last
    (τ : Finset (List ℕ)) (k : List ℕ → ℕ)
    {p : List ℕ} (hp : p ∈ τ) (hkp : 0 < k p)
    (hchild : p ++ [k p] ∈ τ) :
    (loopGraph τ k).Adj ⟨p, hp⟩ ⟨p ++ [k p], hchild⟩ := by
  rw [loopGraph, SimpleGraph.fromRel_adj]
  constructor
  · intro h
    have hval : p = p ++ [k p] := congrArg Subtype.val h
    have hlen := congrArg List.length hval
    simp at hlen
  · left
    right
    exact ⟨hkp, Or.inr rfl⟩

lemma loop_adj_sibling
    (τ : Finset (List ℕ)) (k : List ℕ → ℕ)
    {p : List ℕ} (hp : p ∈ τ) {m : ℕ}
    (hm1 : 1 ≤ m) (hmk : m < k p)
    (hmchild : p ++ [m] ∈ τ) (hnextchild : p ++ [m + 1] ∈ τ) :
    (loopGraph τ k).Adj ⟨p ++ [m], hmchild⟩ ⟨p ++ [m + 1], hnextchild⟩ := by
  rw [loopGraph, SimpleGraph.fromRel_adj]
  constructor
  · intro h
    have hval : p ++ [m] = p ++ [m + 1] := congrArg Subtype.val h
    have hsingle : [m] = [m + 1] := List.append_right_injective p hval
    have : m = m + 1 := by simpa using hsingle
    omega
  · left
    left
    exact ⟨p, m, hp, hm1, hmk, rfl, rfl⟩

/- accepted add_to_file helper 12 -/
lemma loop_parent_child_walk_gap
    (τ : Finset (List ℕ)) (k : List ℕ → ℕ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    {p : List ℕ} (hp : p ∈ τ) :
    ∀ d m : ℕ, 1 ≤ m → m ≤ k p → k p - m = d →
      ∃ hchild : p ++ [m] ∈ τ,
        ∃ w : (loopGraph τ k).Walk ⟨p, hp⟩ ⟨p ++ [m], hchild⟩,
          w.length = k p - m + 1 := by
  intro d
  induction d with
  | zero =>
      intro m hm1 hmk hgap
      have hm : m = k p := by omega
      subst m
      have hkp : 0 < k p := by omega
      have hchild : p ++ [k p] ∈ τ :=
        (hchildren p hp (k p)).mpr ⟨hkp, le_rfl⟩
      refine ⟨hchild, SimpleGraph.Walk.cons
        (loop_adj_parent_last τ k hp hkp hchild) SimpleGraph.Walk.nil, ?_⟩
      simp
  | succ d ih =>
      intro m hm1 hmk hgap
      have hmlt : m < k p := by omega
      have hchild : p ++ [m] ∈ τ := (hchildren p hp m).mpr ⟨hm1, hmk⟩
      have hgapnext : k p - (m + 1) = d := by omega
      rcases ih (m + 1) (by omega) (by omega) hgapnext with ⟨hnext, w, hw⟩
      have hadj := (loop_adj_sibling τ k hp hm1 hmlt hchild hnext).symm
      refine ⟨hchild, w.concat hadj, ?_⟩
      rw [SimpleGraph.Walk.length_concat, hw]
      omega

lemma loop_parent_child_walk
    (τ : Finset (List ℕ)) (k : List ℕ → ℕ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    {p : List ℕ} (hp : p ∈ τ) {m : ℕ} (hm1 : 1 ≤ m) (hmk : m ≤ k p) :
    ∃ hchild : p ++ [m] ∈ τ,
      ∃ w : (loopGraph τ k).Walk ⟨p, hp⟩ ⟨p ++ [m], hchild⟩,
        w.length = k p - m + 1 := by
  exact loop_parent_child_walk_gap τ k hchildren hp
    (k p - m) m hm1 hmk rfl

lemma loop_dist_parent_child
    (τ : Finset (List ℕ)) (k : List ℕ → ℕ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    {p : List ℕ} (hp : p ∈ τ) {m : ℕ} (hm1 : 1 ≤ m) (hmk : m ≤ k p)
    (hchild : p ++ [m] ∈ τ) :
    (loopGraph τ k).dist ⟨p, hp⟩ ⟨p ++ [m], hchild⟩ ≤ k p - m + 1 := by
  rcases loop_parent_child_walk τ k hchildren hp hm1 hmk with ⟨hchild', w, hw⟩
  have hdist := SimpleGraph.dist_le w
  rw [hw] at hdist
  exact hdist

/- accepted add_to_file helper 13 -/
lemma loop_dist_le_W_depth_gap
    {N : ℕ} {τ : Finset (List ℕ)} {k : List ℕ → ℕ}
    (hprefix : ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    {u : Fin N ≃ {v : List ℕ // v ∈ τ}}
    (hlex : ∀ a b : Fin N, a < b ↔
      List.Lex (fun x y : ℕ => x < y) (u a).1 (u b).1)
    {W : Fin (N + 1) → ℤ}
    (hWstep : ∀ r : Fin N,
      W r.succ = W r.castSucc + (k (u r).1 : ℤ) - 1) :
    ∀ n : ℕ, ∀ {i j : Fin N}, i ≤ j →
      (u i).1 <+: (u j).1 →
      (u j).1.length - (u i).1.length ≤ n →
      (((loopGraph τ k).dist (u i) (u j) : ℕ) : ℤ) ≤
        W j.castSucc - W i.castSucc +
          ((u j).1.length : ℤ) - ((u i).1.length : ℤ) := by
  intro n
  induction n with
  | zero =>
      intro i j hij hpre hgap
      have hle_len : (u j).1.length ≤ (u i).1.length := by
        have hz : (u j).1.length - (u i).1.length = 0 := Nat.le_zero.mp hgap
        exact (Nat.sub_eq_zero_iff_le).mp hz
      have hge_len : (u i).1.length ≤ (u j).1.length := hpre.length_le
      have hlen : (u i).1.length = (u j).1.length := by omega
      have hlist : (u i).1 = (u j).1 := hpre.eq_of_length hlen
      have hsub : u i = u j := Subtype.ext hlist
      have hfin : i = j := u.injective hsub
      subst j
      simp
  | succ n ihn =>
      intro i j hij hpre hgap
      by_cases hfin : i = j
      · subst j
        simp
      · have hit : i < j := lt_of_le_of_ne hij hfin
        rcases hpre with ⟨tail, htail⟩
        cases tail with
        | nil =>
            have hlist : (u i).1 = (u j).1 := by
              simpa using htail
            have hsub : u i = u j := Subtype.ext hlist
            exact (hfin (u.injective hsub)).elim
        | cons m rest =>
            have huj : (u j).1 = (u i).1 ++ m :: rest := by
              simpa using htail.symm
            let c := (u i).1 ++ [m]
            have hcpre_j : c <+: (u j).1 := by
              rw [huj]
              refine ⟨rest, ?_⟩
              simp [c, List.append_assoc]
            have hc : c ∈ τ := hprefix (u j).2 hcpre_j
            have hm : 1 ≤ m ∧ m ≤ k (u i).1 :=
              (hchildren (u i).1 (u i).2 m).mp hc
            let t : Fin N := u.symm ⟨c, hc⟩
            have hutsub : u t = ⟨c, hc⟩ := Equiv.apply_symm_apply u ⟨c, hc⟩
            have hut : (u t).1 = c := congrArg Subtype.val hutsub
            have hparentlex : List.Lex (fun p q : ℕ => p < q) (u i).1 c := by
              have hbase : List.Lex (fun p q : ℕ => p < q) [] [m] := List.Lex.nil
              have h := List.Lex.append_left _ hbase (u i).1
              simpa [c] using h
            have hit_t : i < t := by
              apply (hlex i t).mpr
              rw [hut]
              exact hparentlex
            have htj : t ≤ j := by
              by_cases hteq : t = j
              · rw [hteq]
              · have hchildlex_j : List.Lex (fun p q : ℕ => p < q) c (u j).1 := by
                  rw [huj]
                  cases rest with
                  | nil =>
                      have hjt : (u j).1 = c := by
                        simp [huj, c]
                      have hjsub : u j = ⟨c, hc⟩ := Subtype.ext hjt
                      have hjtfin : j = t := by
                        apply u.injective
                        rw [hjsub, hutsub]
                      exact (hteq hjtfin.symm).elim
                  | cons q rest2 =>
                      have hbase : List.Lex (fun p q : ℕ => p < q) [] (q :: rest2) := List.Lex.nil
                      have h := List.Lex.append_left _ hbase c
                      simpa [c, List.append_assoc] using h
                have htltj : t < j := by
                  apply (hlex t j).mpr
                  rw [hut]
                  exact hchildlex_j
                exact le_of_lt htltj
            have htpre_j : (u t).1 <+: (u j).1 := by
              rw [hut]
              exact hcpre_j
            have hgap_t : (u j).1.length - (u t).1.length ≤ n := by
              have hlt : (u t).1.length = (u i).1.length + 1 := by
                simp [hut, c]
              omega
            have hrec := ihn (i := t) (j := j) htj htpre_j hgap_t
            have hWgap := W_parent_child_gap hprefix hchildren (u := u) hlex
              (W := W) hWstep hit_t (m := m) hut
            have hlocalNat := loop_dist_parent_child τ k hchildren (u i).2 hm.1 hm.2 hc
            have htarget : ⟨c, hc⟩ = u t := hutsub.symm
            rw [htarget] at hlocalNat
            rcases loop_parent_child_walk τ k hchildren (u i).2 hm.1 hm.2 with ⟨hc', w, hw⟩
            have htarget' : ⟨c, hc'⟩ = u t := by
              apply Subtype.ext
              exact hut.symm
            rw [htarget'] at w
            have hreach := w.reachable
            have htri := hreach.dist_triangle_left (u j)
            have htriZ : (((loopGraph τ k).dist (u i) (u j) : ℕ) : ℤ) ≤
                (((loopGraph τ k).dist (u i) (u t) : ℕ) : ℤ) +
                (((loopGraph τ k).dist (u t) (u j) : ℕ) : ℤ) := by
              exact_mod_cast htri
            have hlocalZ : (((loopGraph τ k).dist (u i) (u t) : ℕ) : ℤ) ≤
                (k (u i).1 : ℤ) - m + 1 := by
              have h0 : (((loopGraph τ k).dist (u i) (u t) : ℕ) : ℤ) ≤
                  (((k (u i).1 - m + 1 : ℕ) : ℤ)) := by
                exact_mod_cast hlocalNat
              have h1 : (((k (u i).1 - m + 1 : ℕ) : ℤ)) =
                  (k (u i).1 : ℤ) - m + 1 := by
                omega
              rwa [h1] at h0
            have hlen_t : ((u t).1.length : ℤ) - ((u i).1.length : ℤ) = 1 := by
              have hlt : (u t).1.length = (u i).1.length + 1 := by
                simp [hut, c]
              rw [hlt]
              norm_num
            linarith

/- accepted add_to_file helper 14 -/
lemma loop_reachable_of_prefix_gap
    {τ : Finset (List ℕ)} {k : List ℕ → ℕ}
    (hprefix : ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v) :
    ∀ n : ℕ, ∀ {a b : {v : List ℕ // v ∈ τ}},
      a.1 <+: b.1 → b.1.length - a.1.length ≤ n →
      (loopGraph τ k).Reachable a b := by
  intro n
  induction n with
  | zero =>
      intro a b hpre hgap
      have hle_len : b.1.length ≤ a.1.length := by
        have hz : b.1.length - a.1.length = 0 := Nat.le_zero.mp hgap
        exact (Nat.sub_eq_zero_iff_le).mp hz
      have hge_len : a.1.length ≤ b.1.length := hpre.length_le
      have hlen : a.1.length = b.1.length := by omega
      have hlist : a.1 = b.1 := hpre.eq_of_length hlen
      have hab : a = b := Subtype.ext hlist
      cases hab
      exact SimpleGraph.Reachable.refl (G := loopGraph τ k) a
  | succ n ihn =>
      intro a b hpre hgap
      rcases hpre with ⟨tail, htail⟩
      cases tail with
      | nil =>
          have hlist : a.1 = b.1 := by simpa using htail
          have hab : a = b := Subtype.ext hlist
          cases hab
          exact SimpleGraph.Reachable.refl (G := loopGraph τ k) a
      | cons m rest =>
          have hb : b.1 = a.1 ++ m :: rest := by
            simpa using htail.symm
          let c := a.1 ++ [m]
          have hcpre_b : c <+: b.1 := by
            rw [hb]
            refine ⟨rest, ?_⟩
            simp [c, List.append_assoc]
          have hc : c ∈ τ := hprefix b.2 hcpre_b
          have hm : 1 ≤ m ∧ m ≤ k a.1 :=
            (hchildren a.1 a.2 m).mp hc
          let cvertex : {v : List ℕ // v ∈ τ} := ⟨c, hc⟩
          have hcpre_b' : cvertex.1 <+: b.1 := hcpre_b
          have hgap_c : b.1.length - cvertex.1.length ≤ n := by
            have hclen : cvertex.1.length = a.1.length + 1 := by
              simp [cvertex, c]
            omega
          have hrec := ihn (a := cvertex) (b := b) hcpre_b' hgap_c
          rcases loop_parent_child_walk τ k hchildren a.2 hm.1 hm.2 with ⟨hc', w, hw⟩
          have htarget : ⟨c, hc'⟩ = cvertex := rfl
          rw [htarget] at w
          exact w.reachable.trans hrec

lemma loop_reachable_of_prefix
    {τ : Finset (List ℕ)} {k : List ℕ → ℕ}
    (hprefix : ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    {a b : {v : List ℕ // v ∈ τ}} (hpre : a.1 <+: b.1) :
    (loopGraph τ k).Reachable a b := by
  exact loop_reachable_of_prefix_gap hprefix hchildren
    (b.1.length - a.1.length) hpre le_rfl

lemma loop_dist_le_W_depth
    {N : ℕ} {τ : Finset (List ℕ)} {k : List ℕ → ℕ}
    (hprefix : ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    {u : Fin N ≃ {v : List ℕ // v ∈ τ}}
    (hlex : ∀ a b : Fin N, a < b ↔
      List.Lex (fun x y : ℕ => x < y) (u a).1 (u b).1)
    {W : Fin (N + 1) → ℤ}
    (hWstep : ∀ r : Fin N,
      W r.succ = W r.castSucc + (k (u r).1 : ℤ) - 1)
    {i j : Fin N} (hij : i ≤ j) (hpre : (u i).1 <+: (u j).1) :
    (((loopGraph τ k).dist (u i) (u j) : ℕ) : ℤ) ≤
      W j.castSucc - W i.castSucc +
        ((u j).1.length : ℤ) - ((u i).1.length : ℤ) := by
  exact loop_dist_le_W_depth_gap hprefix hchildren (u := u) hlex (W := W) hWstep
    ((u j).1.length - (u i).1.length) hij hpre le_rfl

/- verified submission -/
theorem looptree_height_bound
    (N : ℕ)
    (τ : Finset (List ℕ))
    (k : List ℕ → ℕ)
    (hroot : [] ∈ τ)
    (hprefix : ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ)
    (hchildren : ∀ (v : List ℕ), v ∈ τ → ∀ m : ℕ,
      v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v)
    (u : Fin N ≃ {v : List ℕ // v ∈ τ})
    (hlex : ∀ a b : Fin N, a < b ↔
      List.Lex (fun x y : ℕ => x < y) (u a).1 (u b).1)
    (W : Fin (N + 1) → ℤ)
    (hWzero : W 0 = 0)
    (hWstep : ∀ r : Fin N,
      W r.succ = W r.castSucc + (k (u r).1 : ℤ) - 1) :
    let H : Fin N → ℕ := fun r => (u r).1.length
    let Loop : SimpleGraph {v : List ℕ // v ∈ τ} :=
      SimpleGraph.fromRel fun x y =>
        (∃ (p : List ℕ) (m : ℕ), p ∈ τ ∧ 1 ≤ m ∧ m < k p ∧
          x.1 = p ++ [m] ∧ y.1 = p ++ [m + 1]) ∨
        (0 < k x.1 ∧ (y.1 = x.1 ++ [1] ∨ y.1 = x.1 ++ [k x.1]))
    let Hb : Fin N → ℕ := fun r => Loop.dist ⟨[], hroot⟩ (u r)
    ∀ i j : Fin N, i < j → (u i).1 <+: (u j).1 →
      |(Hb i : ℤ) - (Hb j : ℤ)| ≤
        W j.castSucc - W i.castSucc + (H j : ℤ) - (H i : ℤ) := by
  intro H Loop Hb i j hij hpre
  have hreach : Loop.Reachable (u i) (u j) :=
    loop_reachable_of_prefix hprefix hchildren hpre
  have hdist : (((Loop.dist (u i) (u j) : ℕ) : ℤ)) ≤
      W j.castSucc - W i.castSucc + (H j : ℤ) - (H i : ℤ) := by
    exact loop_dist_le_W_depth hprefix hchildren (u := u) hlex
      (W := W) hWstep (le_of_lt hij) hpre
  have htri_i := hreach.dist_triangle_left ⟨[], hroot⟩
  have htri_j := hreach.symm.dist_triangle_left ⟨[], hroot⟩
  have hcomm : Loop.dist (u j) (u i) = Loop.dist (u i) (u j) :=
    SimpleGraph.dist_comm
  have htri_iZ : ((Loop.dist (u i) ⟨[], hroot⟩ : ℕ) : ℤ) ≤
      ((Loop.dist (u i) (u j) : ℕ) : ℤ) +
        ((Loop.dist (u j) ⟨[], hroot⟩ : ℕ) : ℤ) := by
    exact_mod_cast htri_i
  have htri_jZ : ((Loop.dist (u j) ⟨[], hroot⟩ : ℕ) : ℤ) ≤
      ((Loop.dist (u i) (u j) : ℕ) : ℤ) +
        ((Loop.dist (u i) ⟨[], hroot⟩ : ℕ) : ℤ) := by
    have htri_j' : Loop.dist (u j) ⟨[], hroot⟩ ≤
        Loop.dist (u i) (u j) + Loop.dist (u i) ⟨[], hroot⟩ := by
      simpa [hcomm] using htri_j
    exact_mod_cast htri_j'
  have hdist_i : Loop.dist (u i) ⟨[], hroot⟩ = Loop.dist ⟨[], hroot⟩ (u i) :=
    SimpleGraph.dist_comm
  have hdist_j : Loop.dist (u j) ⟨[], hroot⟩ = Loop.dist ⟨[], hroot⟩ (u j) :=
    SimpleGraph.dist_comm
  rw [hdist_i] at htri_iZ
  rw [hdist_j] at htri_jZ
  change |((Loop.dist ⟨[], hroot⟩ (u i) : ℕ) : ℤ) -
      ((Loop.dist ⟨[], hroot⟩ (u j) : ℕ) : ℤ)| ≤
      W j.castSucc - W i.castSucc + (((u j).1.length : ℕ) : ℤ) -
        (((u i).1.length : ℕ) : ℤ)
  rw [abs_le]
  constructor <;> linarith

end Rollout_p2581_looptree_height_bound

#check_dependency_graph "Rollout_p2581_looptree_height_bound.looptree_height_bound" against "{\"edges\":[{\"conclusion\":{\"name\":\"hreach\",\"statement\":\"Loop.Reachable (u i) (u j)\"},\"graphEdgeId\":\"h_001_hreach\",\"premises\":[{\"name\":\"hprefix\",\"statement\":\"∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ\"},{\"name\":\"hchildren\",\"statement\":\"∀ v ∈ τ, ∀ (m : ℕ), v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v\"},{\"name\":\"hpre\",\"statement\":\"↑(u i) <+: ↑(u j)\"}],\"rawEdgeId\":\"telescope_18\"},{\"conclusion\":{\"name\":\"hdist\",\"statement\":\"↑(Loop.dist (u i) (u j)) ≤ W j.castSucc - W i.castSucc + ↑(H j) - ↑(H i)\"},\"graphEdgeId\":\"h_002_hdist\",\"premises\":[{\"name\":\"hprefix\",\"statement\":\"∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ\"},{\"name\":\"hchildren\",\"statement\":\"∀ v ∈ τ, ∀ (m : ℕ), v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v\"},{\"name\":\"hlex\",\"statement\":\"∀ (a b : Fin N), a < b ↔ List.Lex (fun x y => x < y) ↑(u a) ↑(u b)\"},{\"name\":\"hWstep\",\"statement\":\"∀ (r : Fin N), W r.succ = W r.castSucc + ↑(k ↑(u r)) - 1\"},{\"name\":\"hij\",\"statement\":\"i < j\"},{\"name\":\"hpre\",\"statement\":\"↑(u i) <+: ↑(u j)\"}],\"rawEdgeId\":\"telescope_19\"},{\"conclusion\":{\"name\":\"hcomm\",\"statement\":\"Loop.dist (u j) (u i) = Loop.dist (u i) (u j)\"},\"graphEdgeId\":\"h_005_hcomm\",\"premises\":[],\"rawEdgeId\":\"telescope_22\"},{\"conclusion\":{\"name\":\"hdist_i\",\"statement\":\"Loop.dist (u i) ⟨[], hroot⟩ = Loop.dist ⟨[], hroot⟩ (u i)\"},\"graphEdgeId\":\"h_008_hdist_i\",\"premises\":[{\"name\":\"hroot\",\"statement\":\"[] ∈ τ\"}],\"rawEdgeId\":\"telescope_25\"},{\"conclusion\":{\"name\":\"hdist_j\",\"statement\":\"Loop.dist (u j) ⟨[], hroot⟩ = Loop.dist ⟨[], hroot⟩ (u j)\"},\"graphEdgeId\":\"h_009_hdist_j\",\"premises\":[{\"name\":\"hroot\",\"statement\":\"[] ∈ τ\"}],\"rawEdgeId\":\"telescope_26\"},{\"conclusion\":{\"name\":\"htri_i\",\"statement\":\"Loop.dist (u i) ⟨[], hroot⟩ ≤ Loop.dist (u i) (u j) + Loop.dist (u j) ⟨[], hroot⟩\"},\"graphEdgeId\":\"h_003_htri_i\",\"premises\":[{\"name\":\"hroot\",\"statement\":\"[] ∈ τ\"},{\"name\":\"hreach\",\"statement\":\"Loop.Reachable (u i) (u j)\"}],\"rawEdgeId\":\"telescope_20\"},{\"conclusion\":{\"name\":\"htri_j\",\"statement\":\"Loop.dist (u j) ⟨[], hroot⟩ ≤ Loop.dist (u j) (u i) + Loop.dist (u i) ⟨[], hroot⟩\"},\"graphEdgeId\":\"h_004_htri_j\",\"premises\":[{\"name\":\"hroot\",\"statement\":\"[] ∈ τ\"},{\"name\":\"hreach\",\"statement\":\"Loop.Reachable (u i) (u j)\"}],\"rawEdgeId\":\"telescope_21\"},{\"conclusion\":{\"name\":\"htri_iZ\",\"statement\":\"↑(Loop.dist (u i) ⟨[], hroot⟩) ≤ ↑(Loop.dist (u i) (u j)) + ↑(Loop.dist (u j) ⟨[], hroot⟩)\"},\"graphEdgeId\":\"h_006_htri_iz\",\"premises\":[{\"name\":\"hroot\",\"statement\":\"[] ∈ τ\"},{\"name\":\"htri_i\",\"statement\":\"Loop.dist (u i) ⟨[], hroot⟩ ≤ Loop.dist (u i) (u j) + Loop.dist (u j) ⟨[], hroot⟩\"}],\"rawEdgeId\":\"telescope_23\"},{\"conclusion\":{\"name\":\"htri_jZ\",\"statement\":\"↑(Loop.dist (u j) ⟨[], hroot⟩) ≤ ↑(Loop.dist (u i) (u j)) + ↑(Loop.dist (u i) ⟨[], hroot⟩)\"},\"graphEdgeId\":\"h_007_htri_jz\",\"premises\":[{\"name\":\"hroot\",\"statement\":\"[] ∈ τ\"},{\"name\":\"htri_j\",\"statement\":\"Loop.dist (u j) ⟨[], hroot⟩ ≤ Loop.dist (u j) (u i) + Loop.dist (u i) ⟨[], hroot⟩\"},{\"name\":\"hcomm\",\"statement\":\"Loop.dist (u j) (u i) = Loop.dist (u i) (u j)\"}],\"rawEdgeId\":\"telescope_24\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"|↑(Hb i) - ↑(Hb j)| ≤ W j.castSucc - W i.castSucc + ↑(H j) - ↑(H i)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hroot\",\"statement\":\"[] ∈ τ\"},{\"name\":\"hdist\",\"statement\":\"↑(Loop.dist (u i) (u j)) ≤ W j.castSucc - W i.castSucc + ↑(H j) - ↑(H i)\"},{\"name\":\"htri_iZ\",\"statement\":\"↑(Loop.dist (u i) ⟨[], hroot⟩) ≤ ↑(Loop.dist (u i) (u j)) + ↑(Loop.dist (u j) ⟨[], hroot⟩)\"},{\"name\":\"htri_jZ\",\"statement\":\"↑(Loop.dist (u j) ⟨[], hroot⟩) ≤ ↑(Loop.dist (u i) (u j)) + ↑(Loop.dist (u i) ⟨[], hroot⟩)\"},{\"name\":\"hdist_i\",\"statement\":\"Loop.dist (u i) ⟨[], hroot⟩ = Loop.dist ⟨[], hroot⟩ (u i)\"},{\"name\":\"hdist_j\",\"statement\":\"Loop.dist (u j) ⟨[], hroot⟩ = Loop.dist ⟨[], hroot⟩ (u j)\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2581_looptree_height_bound\",\"reconstructedProofSha256\":\"7d45651ca68f6f5c0e534caef335ee8f853c72ebdae9715513b05af7366dc400\",\"selectedEdgeCount\":10,\"theoremName\":\"Rollout_p2581_looptree_height_bound.looptree_height_bound\",\"topologySha256\":\"b7ec0112d20e1e455666de77441337e930d042a56ef4ed9c1c4be27d8ce7cc77\"}"

namespace Rollout_p2604_diagonal_convergence_of_sequences

-- graph_id: p2604_diagonal_convergence_of_sequences
-- topology_sha256: 0ff276ec76b1c7c532c4ef3a31097c406441d22822053baef5f3bd4ccd2808d6
/- verified submission -/

open Filter Topology

theorem diagonal_convergence_of_sequences
    {E : Type*} [MetricSpace E]
    (a : ℕ → ℕ → E) (aInf : ℕ → E) (aInfInf : E)
    (ha : ∀ m : ℕ, Filter.Tendsto (a m) Filter.atTop (nhds (aInf m)))
    (hInf : Filter.Tendsto aInf Filter.atTop (nhds aInfInf)) :
    ∃ b : ℕ → ℕ,
      Monotone b ∧
      Filter.Tendsto b Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun n : ℕ => a (b n) n) Filter.atTop (nhds aInfInf) := by
  choose N hN using fun (m : ℕ) (k : ℕ) =>
    Metric.tendsto_atTop.mp (ha m) (1 / ((k : ℝ) + 1))
      (one_div_pos.mpr (Nat.cast_add_one_pos k))
  let A : ℕ → ℕ := fun m =>
    max m ((Finset.range (m + 1)).sup fun k => N m k)
  let b : ℕ → ℕ := fun n => Nat.findGreatest (fun m => A m ≤ n) n
  have hbmono : Monotone b := by
    intro m n hmn
    dsimp [b]
    calc
      Nat.findGreatest (fun k => A k ≤ m) m
          ≤ Nat.findGreatest (fun k => A k ≤ m) n :=
        Nat.findGreatest_mono_right (fun k => A k ≤ m) hmn
      _ ≤ Nat.findGreatest (fun k => A k ≤ n) n :=
        Nat.findGreatest_mono_left (fun k hk => le_trans hk hmn) n
  have hbtop : Filter.Tendsto b Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop_iff_of_monotone hbmono]
    intro m
    refine ⟨A m, ?_⟩
    dsimp [b]
    exact Nat.le_findGreatest (P := fun k => A k ≤ A m) (le_max_left _ _) le_rfl
  refine ⟨b, hbmono, hbtop, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_one_div_lt (K := ℝ) (show 0 < ε / 2 by positivity)
  obtain ⟨L, hL⟩ := Metric.tendsto_atTop.mp hInf (ε / 2) (by positivity)
  obtain ⟨Nb, hNb⟩ := Filter.tendsto_atTop_atTop.mp hbtop (max K L)
  refine ⟨max (A 0) Nb, ?_⟩
  intro n hn
  have hA0n : A 0 ≤ n := le_trans (le_max_left _ _) hn
  have hAbn : A (b n) ≤ n := by
    dsimp [b]
    exact Nat.findGreatest_spec (P := fun m => A m ≤ n) (Nat.zero_le n) hA0n
  have hbn_ge : max K L ≤ b n := hNb n (le_trans (le_max_right _ _) hn)
  have hKb : K ≤ b n := le_trans (le_max_left _ _) hbn_ge
  have hLb : L ≤ b n := le_trans (le_max_right _ _) hbn_ge
  have hNA : N (b n) (b n) ≤ A (b n) := by
    have hmem : b n ∈ Finset.range (b n + 1) := by simp
    have hs := Finset.le_sup (s := Finset.range (b n + 1))
      (f := fun k => N (b n) k) hmem
    dsimp [A]
    exact le_trans hs (le_max_right _ _)
  have hfirst : dist (a (b n) n) (aInf (b n)) < 1 / ((b n : ℝ) + 1) :=
    hN (b n) (b n) n (le_trans hNA hAbn)
  have hcast : (K : ℝ) + 1 ≤ (b n : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ hKb
  have hrec : 1 / ((b n : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1) :=
    one_div_le_one_div_of_le (Nat.cast_add_one_pos K) hcast
  have hfirst' : dist (a (b n) n) (aInf (b n)) < ε / 2 :=
    lt_trans (lt_of_lt_of_le hfirst hrec) hK
  have hsecond : dist (aInf (b n)) aInfInf < ε / 2 := hL (b n) hLb
  calc
    dist (a (b n) n) aInfInf
        ≤ dist (a (b n) n) (aInf (b n)) + dist (aInf (b n)) aInfInf :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hfirst' hsecond
    _ = ε := by ring

end Rollout_p2604_diagonal_convergence_of_sequences

#check_dependency_graph "Rollout_p2604_diagonal_convergence_of_sequences.diagonal_convergence_of_sequences" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∃ b, Monotone b ∧ Filter.Tendsto b Filter.atTop Filter.atTop ∧ Filter.Tendsto (fun n => a (b n) n) Filter.atTop (nhds aInfInf)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"ha\",\"statement\":\"∀ (m : ℕ), Filter.Tendsto (a m) Filter.atTop (nhds (aInf m))\"},{\"name\":\"hInf\",\"statement\":\"Filter.Tendsto aInf Filter.atTop (nhds aInfInf)\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2604_diagonal_convergence_of_sequences\",\"reconstructedProofSha256\":\"238481b24472d90be60030089453999ede85862b712a588b33658b515764271b\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p2604_diagonal_convergence_of_sequences.diagonal_convergence_of_sequences\",\"topologySha256\":\"0ff276ec76b1c7c532c4ef3a31097c406441d22822053baef5f3bd4ccd2808d6\"}"

namespace Rollout_p2625_probability_measure_open_unit_interval_uni

-- graph_id: p2625_probability_measure_open_unit_interval_uni
-- topology_sha256: dfdaca984d8be8d649400da403019345f48213505b8a9db6b531bfc4b03b4ea3
/- accepted add_to_file helper 1 -/
lemma exp_sub_one_le_mul_exp {z : ℝ} (hz : 0 < z) : Real.exp z - 1 ≤ z * Real.exp z := by
  have hs := convexOn_exp.slope_le_of_hasDerivAt (by simp) (by simp) hz (Real.hasDerivAt_exp z)
  dsimp [slope] at hs
  simp at hs
  have h2 := mul_le_mul_of_nonneg_left hs hz.le
  field_simp [hz.ne'] at h2
  simpa [mul_comm, mul_left_comm, mul_assoc] using h2

lemma kernel_nonneg_and_bound {t y : ℝ} (ht : 0 ≤ t) (hy0 : 0 < y) (hy1 : y ≤ 1) :
    0 ≤ (Real.exp (t * y) - 1) / y ∧
      (Real.exp (t * y) - 1) / y ≤ t * Real.exp t := by
  have hzy : 0 ≤ t * y := mul_nonneg ht hy0.le
  have hnonneg : 0 ≤ (Real.exp (t * y) - 1) / y := by
    exact div_nonneg (sub_nonneg.mpr (Real.one_le_exp hzy)) hy0.le
  refine ⟨hnonneg, ?_⟩
  by_cases hz : t * y = 0
  · rw [hz]
    simp only [Real.exp_zero, sub_self, zero_div]
    exact mul_nonneg ht (Real.exp_nonneg t)
  · have hzpos : 0 < t * y := lt_of_le_of_ne' hzy hz
    have hexp1 := exp_sub_one_le_mul_exp hzpos
    have htle : t * y ≤ t := by
      nth_rewrite 2 [← mul_one t]
      exact mul_le_mul_of_nonneg_left hy1 ht
    have hexp2 : Real.exp (t * y) ≤ Real.exp t := Real.exp_le_exp.mpr htle
    have hnum : Real.exp (t * y) - 1 ≤ (t * y) * Real.exp t := by
      calc
        Real.exp (t * y) - 1 ≤ (t * y) * Real.exp (t * y) := hexp1
        _ ≤ (t * y) * Real.exp t := mul_le_mul_of_nonneg_left hexp2 hzy
    calc
      (Real.exp (t * y) - 1) / y ≤ ((t * y) * Real.exp t) / y :=
        div_le_div_of_nonneg_right hnum hy0.le
      _ = t * Real.exp t := by
        field_simp [hy0.ne']

/- accepted add_to_file helper 2 -/
lemma kernel_integrable
    (μ : MeasureTheory.Measure (Set.Ioo (0 : ℝ) 1)) [MeasureTheory.IsProbabilityMeasure μ]
    {t : ℝ} (ht : 0 ≤ t) :
    MeasureTheory.Integrable
      (fun x : Set.Ioo (0 : ℝ) 1 =>
        (Real.exp (t * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ))) μ := by
  have hcont : Continuous (fun x : Set.Ioo (0 : ℝ) 1 =>
      (Real.exp (t * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ))) := by
    apply Continuous.div
    · continuity
    · continuity
    · intro x
      have hx1 : (x : ℝ) < 1 := x.2.2
      exact sub_ne_zero.mpr (ne_of_gt hx1)
  refine MeasureTheory.Integrable.of_mem_Icc 0 (t * Real.exp t) hcont.aemeasurable ?_
  filter_upwards with x
  have hy0 : 0 < 1 - (x : ℝ) := sub_pos.mpr x.2.2
  have hy1 : 1 - (x : ℝ) ≤ 1 := by
    have hx0 : 0 < (x : ℝ) := x.2.1
    linarith
  exact kernel_nonneg_and_bound ht hy0 hy1

/- accepted add_to_file helper 3 -/
lemma F_continuousOn_Icc
    (μ : MeasureTheory.Measure (Set.Ioo (0 : ℝ) 1)) [MeasureTheory.IsProbabilityMeasure μ] :
    ContinuousOn
      (fun t : ℝ => ∫ x : Set.Ioo (0 : ℝ) 1,
        (Real.exp (t * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ)
      (Set.Icc 0 1) := by
  apply MeasureTheory.continuousOn_of_dominated
      (bound := fun _ : Set.Ioo (0 : ℝ) 1 => Real.exp 1) (s := Set.Icc (0:ℝ) 1)
  · intro t ht
    exact (kernel_integrable μ ht.1).aestronglyMeasurable
  · intro t ht
    filter_upwards with x
    have hy0 : 0 < 1 - (x : ℝ) := sub_pos.mpr x.2.2
    have hy1 : 1 - (x : ℝ) ≤ 1 := by
      have hx0 : 0 < (x : ℝ) := x.2.1
      linarith
    have hb := kernel_nonneg_and_bound ht.1 hy0 hy1
    have htexp : t * Real.exp t ≤ Real.exp 1 := by
      have ht1 : t ≤ 1 := ht.2
      calc
        t * Real.exp t ≤ 1 * Real.exp 1 := by
          exact mul_le_mul ht1 (Real.exp_le_exp.mpr ht1) (Real.exp_nonneg t) zero_le_one
        _ = Real.exp 1 := one_mul _
    rw [Real.norm_of_nonneg hb.1]
    exact le_trans hb.2 htexp
  · exact MeasureTheory.integrable_const (Real.exp 1)
  · filter_upwards with x
    have hx1 : (x : ℝ) < 1 := x.2.2
    have hcont : Continuous fun t : ℝ =>
        (Real.exp (t * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) := by
      apply Continuous.div
      · continuity
      · continuity
      · intro t
        exact sub_ne_zero.mpr (ne_of_gt hx1)
    exact hcont.continuousOn

/- accepted add_to_file helper 4 -/
lemma F_quarter_lt_one
    (μ : MeasureTheory.Measure (Set.Ioo (0 : ℝ) 1)) [MeasureTheory.IsProbabilityMeasure μ] :
    (∫ x : Set.Ioo (0 : ℝ) 1,
      (Real.exp ((1/4 : ℝ) * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ) < 1 := by
  let c : ℝ := (1/4 : ℝ) * Real.exp (1/4 : ℝ)
  have hle : (∫ x : Set.Ioo (0 : ℝ) 1,
      (Real.exp ((1/4 : ℝ) * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ) ≤
      ∫ _x : Set.Ioo (0 : ℝ) 1, c ∂μ := by
    apply MeasureTheory.integral_mono_ae
    · exact kernel_integrable μ (by norm_num)
    · exact MeasureTheory.integrable_const c
    · filter_upwards with x
      have hy0 : 0 < 1 - (x : ℝ) := sub_pos.mpr x.2.2
      have hy1 : 1 - (x : ℝ) ≤ 1 := by
        have hx0 : 0 < (x : ℝ) := x.2.1
        linarith
      exact (kernel_nonneg_and_bound (by norm_num : (0:ℝ) ≤ 1/4) hy0 hy1).2
  have hconst : ∫ _x : Set.Ioo (0 : ℝ) 1, c ∂μ = c := by
    rw [MeasureTheory.integral_const]
    simp [MeasureTheory.Measure.real, MeasureTheory.IsProbabilityMeasure.measure_univ]
  have hc : c < 1 := by
    dsimp [c]
    have hexp : Real.exp (1/4 : ℝ) < 4/3 := by
      have h := Real.exp_bound_div_one_sub_of_interval'
        (by norm_num : (0:ℝ) < 1/4) (by norm_num : (1/4:ℝ) < 1)
      norm_num at h ⊢
      exact h
    nlinarith [Real.exp_nonneg (1/4 : ℝ)]
  exact lt_of_le_of_lt (by simpa [hconst] using hle) hc

/- accepted add_to_file helper 5 -/
lemma F_one_gt_one
    (μ : MeasureTheory.Measure (Set.Ioo (0 : ℝ) 1)) [MeasureTheory.IsProbabilityMeasure μ] :
    1 < (∫ x : Set.Ioo (0 : ℝ) 1,
      (Real.exp ((1 : ℝ) * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ) := by
  let d : Set.Ioo (0 : ℝ) 1 → ℝ := fun x =>
    (Real.exp ((1 : ℝ) * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) - 1
  have hd_pos : ∀ x, 0 < d x := by
    intro x
    dsimp [d]
    have hy : 0 < 1 - (x : ℝ) := sub_pos.mpr x.2.2
    have hexp : 1 - (x : ℝ) + 1 < Real.exp (1 - (x : ℝ)) :=
      Real.add_one_lt_exp (sub_ne_zero.mpr (ne_of_gt x.2.2))
    have hratio : 1 < (Real.exp (1 - (x : ℝ)) - 1) / (1 - (x : ℝ)) := by
      rw [lt_div_iff₀ hy]
      linarith
    simpa [one_mul] using sub_pos.mpr hratio
  have hd_nonneg : 0 ≤ d := fun x => (hd_pos x).le
  have hf1 : MeasureTheory.Integrable
      (fun x : Set.Ioo (0 : ℝ) 1 =>
        (Real.exp ((1 : ℝ) * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ))) μ :=
    kernel_integrable μ zero_le_one
  have hd_int : MeasureTheory.Integrable d μ := by
    dsimp [d]
    exact hf1.sub (MeasureTheory.integrable_const 1)
  have hd_int_pos : 0 < ∫ x : Set.Ioo (0 : ℝ) 1, d x ∂μ := by
    rw [MeasureTheory.integral_pos_iff_support_of_nonneg hd_nonneg hd_int]
    have hsupp : Function.support d = Set.univ := by
      ext x
      simp [Function.support, ne_of_gt (hd_pos x)]
    rw [hsupp, MeasureTheory.IsProbabilityMeasure.measure_univ]
    norm_num
  have hdecomp : (∫ x : Set.Ioo (0 : ℝ) 1, d x ∂μ) =
      (∫ x : Set.Ioo (0 : ℝ) 1,
        (Real.exp ((1 : ℝ) * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ) - 1 := by
    dsimp [d]
    rw [MeasureTheory.integral_sub hf1 (MeasureTheory.integrable_const 1)]
    congr 1
    rw [MeasureTheory.integral_const]
    simp [MeasureTheory.Measure.real, MeasureTheory.IsProbabilityMeasure.measure_univ]
  linarith

/- accepted add_to_file helper 6 -/
lemma F_strictMono_on_nonneg
    (μ : MeasureTheory.Measure (Set.Ioo (0 : ℝ) 1)) [MeasureTheory.IsProbabilityMeasure μ]
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a < b) :
    (∫ x : Set.Ioo (0 : ℝ) 1,
      (Real.exp (a * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ) <
    (∫ x : Set.Ioo (0 : ℝ) 1,
      (Real.exp (b * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ) := by
  let d : Set.Ioo (0 : ℝ) 1 → ℝ := fun x =>
    (Real.exp (b * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) -
      (Real.exp (a * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ))
  have hd_pos : ∀ x, 0 < d x := by
    intro x
    dsimp [d]
    have hy : 0 < 1 - (x : ℝ) := sub_pos.mpr x.2.2
    have harg : a * (1 - (x : ℝ)) < b * (1 - (x : ℝ)) :=
      mul_lt_mul_of_pos_right hab hy
    have hexp : Real.exp (a * (1 - (x : ℝ))) < Real.exp (b * (1 - (x : ℝ))) :=
      Real.exp_lt_exp_of_lt harg
    have hnum : Real.exp (a * (1 - (x : ℝ))) - 1 <
        Real.exp (b * (1 - (x : ℝ))) - 1 := sub_lt_sub_right hexp 1
    exact sub_pos.mpr (div_lt_div_of_pos_right hnum hy)
  have hd_nonneg : 0 ≤ d := fun x => (hd_pos x).le
  have hfa : MeasureTheory.Integrable
      (fun x : Set.Ioo (0 : ℝ) 1 =>
        (Real.exp (a * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ))) μ :=
    kernel_integrable μ ha
  have hfb : MeasureTheory.Integrable
      (fun x : Set.Ioo (0 : ℝ) 1 =>
        (Real.exp (b * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ))) μ :=
    kernel_integrable μ hb
  have hd_int : MeasureTheory.Integrable d μ := by
    dsimp [d]
    exact hfb.sub hfa
  have hd_int_pos : 0 < ∫ x : Set.Ioo (0 : ℝ) 1, d x ∂μ := by
    rw [MeasureTheory.integral_pos_iff_support_of_nonneg hd_nonneg hd_int]
    have hsupp : Function.support d = Set.univ := by
      ext x
      simp [Function.support, ne_of_gt (hd_pos x)]
    rw [hsupp, MeasureTheory.IsProbabilityMeasure.measure_univ]
    norm_num
  have hdecomp : (∫ x : Set.Ioo (0 : ℝ) 1, d x ∂μ) =
      (∫ x : Set.Ioo (0 : ℝ) 1,
        (Real.exp (b * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ) -
      (∫ x : Set.Ioo (0 : ℝ) 1,
        (Real.exp (a * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ) := by
    dsimp [d]
    exact MeasureTheory.integral_sub hfb hfa
  linarith

/- verified submission -/
theorem probability_measure_open_unit_interval_unique_solution
    (μ : MeasureTheory.Measure (Set.Ioo (0 : ℝ) 1)) [MeasureTheory.IsProbabilityMeasure μ] :
    ∃ s : ℝ,
      0 < s ∧
        s < 1 ∧
          (∫ x, (Real.exp (s * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ) = 1 ∧
            ∀ t : ℝ,
              0 < t →
                (∫ x, (Real.exp (t * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ) = 1 →
                  t = s := by
  let F : ℝ → ℝ := fun t : ℝ =>
    ∫ x : Set.Ioo (0 : ℝ) 1,
      (Real.exp (t * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ
  have hcontIcc : ContinuousOn F (Set.Icc (1/4 : ℝ) 1) := by
    have hcont := F_continuousOn_Icc μ
    apply hcont.mono
    intro t ht
    constructor
    · linarith [ht.1]
    · exact ht.2
  have hF14 : F (1/4 : ℝ) < 1 := by
    exact F_quarter_lt_one μ
  have hF1 : 1 < F 1 := by
    exact F_one_gt_one μ
  have h1mem : (1 : ℝ) ∈ Set.Ioo (F (1/4 : ℝ)) (F 1) := ⟨hF14, hF1⟩
  have himage := intermediate_value_Ioo (by norm_num : (1/4 : ℝ) ≤ 1) hcontIcc h1mem
  rcases himage with ⟨s, hsI, hsF⟩
  have hs0 : 0 < s := by linarith [hsI.1]
  have hs1 : s < 1 := hsI.2
  have hs_eq : (∫ x : Set.Ioo (0 : ℝ) 1,
      (Real.exp (s * (1 - (x : ℝ))) - 1) / (1 - (x : ℝ)) ∂μ) = 1 := by
    exact hsF
  refine ⟨s, hs0, hs1, hs_eq, ?_⟩
  intro t ht0 ht_eq
  rcases lt_trichotomy t s with hts | hts | hts
  · have hstrict := F_strictMono_on_nonneg μ ht0.le hs0.le hts
    rw [ht_eq, hs_eq] at hstrict
    exact (lt_irrefl (1 : ℝ) hstrict).elim
  · exact hts
  · have hstrict := F_strictMono_on_nonneg μ hs0.le ht0.le hts
    rw [ht_eq, hs_eq] at hstrict
    exact (lt_irrefl (1 : ℝ) hstrict).elim

end Rollout_p2625_probability_measure_open_unit_interval_uni

#check_dependency_graph "Rollout_p2625_probability_measure_open_unit_interval_uni.probability_measure_open_unit_interval_unique_solution" against "{\"edges\":[{\"conclusion\":{\"name\":\"hcontIcc\",\"statement\":\"ContinuousOn F (Set.Icc (1 / 4) 1)\"},\"graphEdgeId\":\"h_001_hconticc\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"MeasureTheory.IsProbabilityMeasure μ\"}],\"rawEdgeId\":\"telescope_3\"},{\"conclusion\":{\"name\":\"hF14\",\"statement\":\"F (1 / 4) < 1\"},\"graphEdgeId\":\"h_002_hf14\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"MeasureTheory.IsProbabilityMeasure μ\"}],\"rawEdgeId\":\"telescope_4\"},{\"conclusion\":{\"name\":\"hF1\",\"statement\":\"1 < F 1\"},\"graphEdgeId\":\"h_003_hf1\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"MeasureTheory.IsProbabilityMeasure μ\"}],\"rawEdgeId\":\"telescope_5\"},{\"conclusion\":{\"name\":\"h1mem\",\"statement\":\"1 ∈ Set.Ioo (F (1 / 4)) (F 1)\"},\"graphEdgeId\":\"h_004_h1mem\",\"premises\":[{\"name\":\"hF14\",\"statement\":\"F (1 / 4) < 1\"},{\"name\":\"hF1\",\"statement\":\"1 < F 1\"}],\"rawEdgeId\":\"telescope_6\"},{\"conclusion\":{\"name\":\"himage\",\"statement\":\"1 ∈ F '' Set.Ioo (1 / 4) 1\"},\"graphEdgeId\":\"h_005_himage\",\"premises\":[{\"name\":\"hcontIcc\",\"statement\":\"ContinuousOn F (Set.Icc (1 / 4) 1)\"},{\"name\":\"h1mem\",\"statement\":\"1 ∈ Set.Ioo (F (1 / 4)) (F 1)\"}],\"rawEdgeId\":\"telescope_7\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∃ s, 0 < s ∧ s < 1 ∧ ∫ (x : ↑(Set.Ioo 0 1)), (Real.exp (s * (1 - ↑x)) - 1) / (1 - ↑x) ∂μ = 1 ∧ ∀ (t : ℝ), 0 < t → ∫ (x : ↑(Set.Ioo 0 1)), (Real.exp (t * (1 - ↑x)) - 1) / (1 - ↑x) ∂μ = 1 → t = s\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"MeasureTheory.IsProbabilityMeasure μ\"},{\"name\":\"himage\",\"statement\":\"1 ∈ F '' Set.Ioo (1 / 4) 1\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2625_probability_measure_open_unit_interval_uni\",\"reconstructedProofSha256\":\"58c99c42120bd9d9430e6f73b93bcbac31d68498c9cade4f2f554cdb55a1e9da\",\"selectedEdgeCount\":6,\"theoremName\":\"Rollout_p2625_probability_measure_open_unit_interval_uni.probability_measure_open_unit_interval_unique_solution\",\"topologySha256\":\"dfdaca984d8be8d649400da403019345f48213505b8a9db6b531bfc4b03b4ea3\"}"
