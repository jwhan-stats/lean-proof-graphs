import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1747_parbelos_area_and_vertex_parallelogram
-- topology_sha256: 37863b4fd33cabcaee6b1186d21487043328016f8acaea5ea618c19db6ea265c
namespace TopologyCertificate_p1747_parbelos_area_and_vertex_parallelogram

-- N001 = ha: 0 < a
-- N002 = hb: 0 < b
-- N003 = hba: b < 2 * a
-- N004 = goal: let C₁ := (0, 0); let C₂ := (2 * b, 0); let C₃ := (4 * a, 0); let U := fun x => a - (x - 2 * a) ^ 2 / (4 * a); let L := fun x => b / 2 - (x - b) ^ 2 / (2 * b); let R := fun x => (2 * a - b) / 2 - (x - (2 * a + b)) ^ 2 / (2 * (2 * a - b)); let P := {p | 0 ≤ p.1 ∧ p.1 ≤ 2 * b ∧ L p.1 ≤ p.2 ∧ p.2 ≤ U p.1 ∨ 2 * b ≤ p.1 ∧ p.1 ≤ 4 * a ∧ R p.1 ≤ p.2 ∧ p.2 ≤ U p.1}; let V₁ := (b, b / 2); let V₂ := (2 * a, a); let V₃ := (2 * a + b, a - b / 2); (V₁ - C₂ = V₂ - V₃ ∧ V₂ - V₁ = V₃ - C₂) ∧ MeasureTheory.volume P = 4 / 3 * MeasureTheory.volume ((convexHull ℝ) {C₂, V₁, V₂, V₃})

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N001 → N002 → N003 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B001 B002 B003
  exact H_N004

end TopologyCertificate_p1747_parbelos_area_and_vertex_parallelogram
