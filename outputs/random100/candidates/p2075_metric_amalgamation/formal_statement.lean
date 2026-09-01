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
            4 * ε := by sorry
