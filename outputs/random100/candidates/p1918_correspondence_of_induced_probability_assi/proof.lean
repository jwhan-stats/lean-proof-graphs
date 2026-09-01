import Mathlib

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
