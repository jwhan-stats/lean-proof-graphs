import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1268_flower_graph_equitable_coloring_moments
-- topology_sha256: 62fc5d51e2f8984904db07fbb0ba470440156ede0fd07187201aad0c3ef5f3f5
namespace TopologyCertificate_p1268_flower_graph_equitable_coloring_moments

-- N001 = heq: ∀ (i j : Fin k), (f.colorClass i).ncard.dist (f.colorClass j).ncard ≤ 1
-- N002 = hmin: ∀ ℓ < k, ¬∃ g, Function.Surjective ⇑g ∧ ∀ (i j : Fin ℓ), (g.colorClass i).ncard.dist (g.colorClass j).ncard ≤ 1
-- N003 = hn: 3 ≤ n
-- N004 = hsort: ∀ (i j : Fin k), i ≤ j → (f.colorClass j).ncard ≤ (f.colorClass i).ncard
-- N005 = hsurj: Function.Surjective ⇑f
-- N006 = h2n: 2 ≤ n
-- N007 = hk_lower: n + 1 ≤ k
-- N008 = hk_upper: k ≤ n + 1
-- N009 = hk: k = n + 1
-- N010 = goal: let X := fun x => ↑(↑(f x) + 1); let μ := (PMF.uniformOfFintype V).toMeasure; MeasureTheory.integral μ X = (↑n + 1) ^ 2 / (2 * ↑n + 1) ∧ ProbabilityTheory.variance X μ = (↑n ^ 4 + 2 * ↑n ^ 3 + 2 * ↑n ^ 2 + ↑n) / (3 * (2 * ↑n + 1) ^ 2)

-- E001 represents h_001_h2n
-- E002 represents h_002_hk_lower
-- E003 represents h_003_hk_upper
-- E004 represents h_004_hk
-- E005 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (N008 : Prop)
    (N009 : Prop)
    (N010 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (E001 : N003 → N006)
    (E002 : N005 → N001 → N007)
    (E003 : N002 → N006 → N008)
    (E004 : N007 → N008 → N009)
    (E005 : N005 → N001 → N002 → N004 → N007 → N008 → N009 → N010)
    : N010 := by
  have H_N006 : N006 := E001 B003
  have H_N007 : N007 := E002 B005 B001
  have H_N008 : N008 := E003 B002 H_N006
  have H_N009 : N009 := E004 H_N007 H_N008
  have H_N010 : N010 := E005 B005 B001 B002 B004 H_N007 H_N008 H_N009
  exact H_N010

end TopologyCertificate_p1268_flower_graph_equitable_coloring_moments
