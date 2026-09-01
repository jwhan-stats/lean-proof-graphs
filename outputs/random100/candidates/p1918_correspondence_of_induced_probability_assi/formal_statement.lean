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
      T₄₁ q = p ∧ T₁₄ p = q := by sorry
