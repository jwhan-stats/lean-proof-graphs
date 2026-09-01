import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1664_paired_complex_tuple_set_convex
-- topology_sha256: b4be8d3735c355ac6e653e0f9dd5a2845135be269c517bc5360bd2601e64ce1b
namespace TopologyCertificate_p1664_paired_complex_tuple_set_convex

-- N001 = hζ: ζ ∈ {ζ | (∀ (i : Fin (l + m)), ζ i = ζ (σ i)) ∧ (∀ (i : Fin (l + m)), 0 < (ζ i).re) ∧ (∀ (i : ℕ), 1 ≤ i → i < l → 0 < (∑ k with ↑k < i, ζ k).im) ∧ (∀ (j : ℕ), 1 ≤ j → j < m → (∑ k with l ≤ ↑k ∧ ↑k < l + j, ζ k).im < 0) ∧ ∑ k with ↑k < l, ζ k = ∑ k with l ≤ ↑k, ζ k}
-- N002 = hη: η ∈ {ζ | (∀ (i : Fin (l + m)), ζ i = ζ (σ i)) ∧ (∀ (i : Fin (l + m)), 0 < (ζ i).re) ∧ (∀ (i : ℕ), 1 ≤ i → i < l → 0 < (∑ k with ↑k < i, ζ k).im) ∧ (∀ (j : ℕ), 1 ≤ j → j < m → (∑ k with l ≤ ↑k ∧ ↑k < l + j, ζ k).im < 0) ∧ ∑ k with ↑k < l, ζ k = ∑ k with l ≤ ↑k, ζ k}
-- N003 = ha: 0 ≤ a
-- N004 = hab: a + b = 1
-- N005 = hb: 0 ≤ b
-- N006 = goal: (∀ (i : Fin (l + m)), (a • ζ + b • η) i = (a • ζ + b • η) (σ i)) ∧ (∀ (i : Fin (l + m)), 0 < ((a • ζ + b • η) i).re) ∧ (∀ (i : ℕ), 1 ≤ i → i < l → 0 < (∑ k with ↑k < i, (a • ζ + b • η) k).im) ∧ (∀ (j : ℕ), 1 ≤ j → j < m → (∑ k with l ≤ ↑k ∧ ↑k < l + j, (a • ζ + b • η) k).im < 0) ∧ ∑ k with ↑k < l, (a • ζ + b • η) k = ∑ k with l ≤ ↑k, (a • ζ + b • η) k

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (E001 : N001 → N002 → N003 → N005 → N004 → N006)
    : N006 := by
  have H_N006 : N006 := E001 B001 B002 B003 B005 B004
  exact H_N006

end TopologyCertificate_p1664_paired_complex_tuple_set_convex
