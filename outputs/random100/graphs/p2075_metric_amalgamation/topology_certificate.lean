import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2075_metric_amalgamation
-- topology_sha256: deb664ff2993b355db8b0a33e35ab9f9f0aae3ff5569326fe1891b0dcff1b2ed
namespace TopologyCertificate_p2075_metric_amalgamation

-- N001 = hB_clopen: ∀ (i : I), IsClopen (B i)
-- N002 = hB_cover: ⋃ i, B i = Set.univ
-- N003 = hB_disjoint: Set.univ.PairwiseDisjoint B
-- N004 = he_top: ∀ (i : I), PseudoMetricSpace.toUniformSpace.toTopologicalSpace = inferInstance
-- N005 = goal: ∃ mD, (∀ (i : I) (x y : ↑(B i)), dist ↑x ↑y = dist x y) ∧ (∀ (i j : I), i ≠ j → ∀ (x : ↑(B i)) (y : ↑(B j)), dist ↑x ↑y = dist x (p i) + dist ↑(p i) ↑(p j) + dist (p j) y) ∧ PseudoMetricSpace.toUniformSpace.toTopologicalSpace = inferInstance ∧ ∀ (ε : ℝ), 0 ≤ ε → ((∀ (i : I), Metric.ediam (B i) ≤ ENNReal.ofReal ε) ∧ ∀ (i : I), Metric.ediam Set.univ ≤ ENNReal.ofReal ε) → sSup (Set.range fun q => |dist q.1 q.2 - dist q.1 q.2|) ≤ 4 * ε

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N003 → N001 → N002 → N004 → N005)
    : N005 := by
  have H_N005 : N005 := E001 B003 B001 B002 B004
  exact H_N005

end TopologyCertificate_p2075_metric_amalgamation
