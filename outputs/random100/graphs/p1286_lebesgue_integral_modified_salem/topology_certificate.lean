import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1286_lebesgue_integral_modified_salem
-- topology_sha256: c173f2fd3f41805f05c416c106daa252296564e158ccbe52222c879356552a75
namespace TopologyCertificate_p1286_lebesgue_integral_modified_salem

-- N001 = hp₀: p₀ ∈ Set.Ioo 0 1
-- N002 = hp₁: p₁ ∈ Set.Ioo 0 1
-- N003 = hp₂: p₂ ∈ Set.Ioo 0 1
-- N004 = hsum: p₀ + p₁ + p₂ = 1
-- N005 = goal: let p := ![p₀, p₁, p₂]; let β := ![0, p₀, p₀ + p₁]; let E := fun i => ∑' (k : ℕ), β (i k) * ∏ r ∈ Finset.range k, p (i r); let canonical := fun x => Classical.epsilon fun i => E i = x ∧ ((∃ j, E j = x ∧ j ≠ i) → ∃ N, ∀ (k : ℕ), N ≤ k → i k = 0); let θ := ![0, 2, 1]; let f := fun x => E fun k => θ (canonical x k); MeasureTheory.IntegrableOn f (Set.Icc 0 1) MeasureTheory.volume ∧ ∫ (x : ℝ) in 0..1, f x = (p₁ ^ 2 + p₀ * p₁ + p₀ * p₂) / (1 - p₀ ^ 2 - 2 * p₁ * p₂)

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
    (E001 : N001 → N002 → N003 → N004 → N005)
    : N005 := by
  have H_N005 : N005 := E001 B001 B002 B003 B004
  exact H_N005

end TopologyCertificate_p1286_lebesgue_integral_modified_salem
