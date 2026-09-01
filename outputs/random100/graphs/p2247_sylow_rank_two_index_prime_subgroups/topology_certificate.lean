import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2247_sylow_rank_two_index_prime_subgroups
-- topology_sha256: 1c6ca46bbda1eeac93fb6cf04404be324d1119b830fc90bfd6f96fc2ea3164f9
namespace TopologyCertificate_p2247_sylow_rank_two_index_prime_subgroups

-- N001 = hind: Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥
-- N002 = hp: Nat.Prime p
-- N003 = hspan: Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤
-- N004 = hu: 0 < u
-- N005 = huv: v ≤ u
-- N006 = hv: 0 < v
-- N007 = hx: orderOf x = p ^ u
-- N008 = hy: orderOf y = p ^ v
-- N009 = inst._@.proofs.4000124397._hygCtx._hyg.6: Finite A
-- N010 = hE: E = Subgroup.zpowers (x ^ p ^ (u - 1)) ⊔ Subgroup.zpowers (y ^ p ^ (v - 1))
-- N011 = goal: E = Subgroup.zpowers (x ^ p ^ (u - 1)) ⊔ Subgroup.zpowers (y ^ p ^ (v - 1)) ∧ (u = 1 ∧ v = 1 → ∀ (U : Subgroup ↥↑P), U.index = p ↔ U ≤ E ∧ Nat.card ↥U = p) ∧ (v = 1 ∧ 1 < u → N.index = p ∧ E ≤ N ∧ (∀ (U : Subgroup ↥↑P), U.index = p → E ≤ U → U = N) ∧ Nonempty (↥N ≃* Multiplicative (ZMod (p ^ (u - 1))) × Multiplicative (ZMod p)) ∧ Nat.card { U // U.index = p ∧ U ≠ N } = p ∧ ∀ (U : Subgroup ↥↑P), U.index = p → U ≠ N → IsCyclic ↥U ∧ Nat.card ↥U = p ^ u ∧ U ⊓ E = Subgroup.zpowers (x ^ p ^ (u - 1))) ∧ (1 < v → ∀ (U : Subgroup ↥↑P), U.index = p → E ≤ U)

-- E001 represents h_001_he
-- E002 represents h_goal

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
    (N011 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (B007 : N007)
    (B008 : N008)
    (B009 : N009)
    (E001 : N002 → N004 → N006 → N007 → N008 → N003 → N001 → N010)
    (E002 : N009 → N002 → N004 → N006 → N005 → N007 → N008 → N003 → N001 → N010 → N011)
    : N011 := by
  have H_N010 : N010 := E001 B002 B004 B006 B007 B008 B003 B001
  have H_N011 : N011 := E002 B009 B002 B004 B006 B005 B007 B008 B003 B001 H_N010
  exact H_N011

end TopologyCertificate_p2247_sylow_rank_two_index_prime_subgroups
