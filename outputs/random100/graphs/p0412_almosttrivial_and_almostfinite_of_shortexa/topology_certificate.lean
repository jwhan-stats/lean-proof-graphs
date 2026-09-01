import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0412_almosttrivial_and_almostfinite_of_shortexa
-- topology_sha256: 9cb15c8d2be7ea66532caeaf9ddd881b9b97f2e4113556f5d73c0e7fcd4dc7c6
namespace TopologyCertificate_p0412_almosttrivial_and_almostfinite_of_shortexa

-- N001 = hf: Function.Injective ⇑f
-- N002 = hfg: Function.Exact ⇑f ⇑g
-- N003 = hg: Function.Surjective ⇑g
-- N004 = inst._@.proofs.1734391863._hygCtx._hyg.6: IsDomain R
-- N005 = goal: ((∃ r, r ≠ 0 ∧ ∀ (m : M₁), r • m = 0) ↔ (∃ r, r ≠ 0 ∧ ∀ (m : M₀), r • m = 0) ∧ ∃ r, r ≠ 0 ∧ ∀ (m : M₂), r • m = 0) ∧ (IsNoetherianRing R → ((∃ r, r ≠ 0 ∧ ∀ (m : ↥(Submodule.torsion R M₁)), r • m = 0) ∧ Module.Finite R (M₁ ⧸ Submodule.torsion R M₁) ↔ ((∃ r, r ≠ 0 ∧ ∀ (m : ↥(Submodule.torsion R M₀)), r • m = 0) ∧ Module.Finite R (M₀ ⧸ Submodule.torsion R M₀)) ∧ (∃ r, r ≠ 0 ∧ ∀ (m : ↥(Submodule.torsion R M₂)), r • m = 0) ∧ Module.Finite R (M₂ ⧸ Submodule.torsion R M₂)))

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
    (E001 : N004 → N001 → N002 → N003 → N005)
    : N005 := by
  have H_N005 : N005 := E001 B004 B001 B002 B003
  exact H_N005

end TopologyCertificate_p0412_almosttrivial_and_almostfinite_of_shortexa
