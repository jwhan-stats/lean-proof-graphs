theorem locallyContinuousMeasurableOneCocycle_iff_continuousCrossedHomomorphism
    {G A : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [DistribMulAction G A] [ContinuousSMul G A]
    [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace A] [BorelSpace A]
    (c : G → A) :
    (Measurable c ∧
        (∀ s t : G, c (s * t) = c s + s • c t) ∧
        ∃ U : Set G, IsOpen U ∧ (1 : G) ∈ U ∧ ContinuousOn c U) ↔
      (Continuous c ∧ ∀ s t : G, c (s * t) = c s + s • c t) := by sorry
