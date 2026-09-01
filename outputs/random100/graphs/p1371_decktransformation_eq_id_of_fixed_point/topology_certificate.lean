import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1371_decktransformation_eq_id_of_fixed_point
-- topology_sha256: 49b9b585e041fe141c9e7bf83d6fcded9c12a63a2cdd4f73c72e7081daaf95bf
namespace TopologyCertificate_p1371_decktransformation_eq_id_of_fixed_point

-- N001 = arc_lifting: ∀ (f : C(↑(Set.Icc 0 1), B)) (t₀ : ↑(Set.Icc 0 1)) (e₀ : E), p e₀ = f t₀ → ∃! g, (∀ (t : ↑(Set.Icc 0 1)), p (g t) = f t) ∧ g t₀ = e₀
-- N002 = hdeck: p ∘ ⇑h = p
-- N003 = he: h e = e
-- N004 = hp: Continuous p
-- N005 = inst._@.proofs.4209456836._hygCtx._hyg.10: PathConnectedSpace E
-- N006 = goal: h = Homeomorph.refl E

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
    (E001 : N005 → N004 → N001 → N002 → N003 → N006)
    : N006 := by
  have H_N006 : N006 := E001 B005 B004 B001 B002 B003
  exact H_N006

end TopologyCertificate_p1371_decktransformation_eq_id_of_fixed_point
