import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1078_khexpansive_iff_separating_and_isopen_fixe
-- topology_sha256: 1d21a2c271cc6d89ca8dd8b3bb2cfd8d6957cb59c12c94472e01d3e82f68c8b9
namespace TopologyCertificate_p1078_khexpansive_iff_separating_and_isopen_fixe

-- N001 = hadd: ∀ (t u : ℝ) (x : Λ), φ (t + u, x) = φ (t, φ (u, x))
-- N002 = hcont: Continuous φ
-- N003 = hzero: ∀ (x : Λ), φ (0, x) = x
-- N004 = inst._@.proofs.3640889310._hygCtx._hyg.6: CompactSpace Λ
-- N005 = goal: (∃ δ, 0 < δ ∧ ∀ (x y : Λ) (s : ℝ → ℝ), Continuous s → s 0 = 0 → ((∀ (t : ℝ), dist (φ (t, x)) (φ (s t, x)) < δ) ∧ ∀ (t : ℝ), dist (φ (t, x)) (φ (s t, y)) < δ) → y ∈ Set.range fun t => φ (t, x)) ↔ (∃ α, 0 < α ∧ ∀ (x y : Λ), (∀ (t : ℝ), dist (φ (t, x)) (φ (t, y)) < α) → y ∈ Set.range fun t => φ (t, x)) ∧ IsOpen {x | ∀ (t : ℝ), φ (t, x) = x}

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
    (E001 : N004 → N002 → N003 → N001 → N005)
    : N005 := by
  have H_N005 : N005 := E001 B004 B002 B003 B001
  exact H_N005

end TopologyCertificate_p1078_khexpansive_iff_separating_and_isopen_fixe
