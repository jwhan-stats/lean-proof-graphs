import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1479_completion_preserves_finite_one_point_exte
-- topology_sha256: 39b1009545f4bff0a670c51396fb742561c861c05ae85f94cd168a4c403d40dc
namespace TopologyCertificate_p1479_completion_preserves_finite_one_point_exte

-- N001 = hdiam: Metric.diam Set.univ = 1
-- N002 = hext: ∀ (F : Set A), F.Finite → ∀ (f : ↑F → ↑(Set.Icc 0 1)), (∀ (x y : ↑F), |↑(f x) - ↑(f y)| ≤ dist ↑x ↑y ∧ dist ↑x ↑y ≤ ↑(f x) + ↑(f y)) → ∃ z, ∀ (x : ↑F), dist z ↑x = ↑(f x)
-- N003 = hdiamX: Metric.diam Set.univ = 1
-- N004 = goal: Metric.diam Set.univ = 1 ∧ ∀ (F : Set (UniformSpace.Completion A)), F.Finite → ∀ (f : ↑F → ↑(Set.Icc 0 1)), (∀ (x y : ↑F), |↑(f x) - ↑(f y)| ≤ dist ↑x ↑y ∧ dist ↑x ↑y ≤ ↑(f x) + ↑(f y)) → ∃ z, ∀ (x : ↑F), dist z ↑x = ↑(f x)

-- E001 represents h_001_hdiamx
-- E002 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (E001 : N001 → N003)
    (E002 : N002 → N003 → N004)
    : N004 := by
  have H_N003 : N003 := E001 B001
  have H_N004 : N004 := E002 B002 H_N003
  exact H_N004

end TopologyCertificate_p1479_completion_preserves_finite_one_point_exte
