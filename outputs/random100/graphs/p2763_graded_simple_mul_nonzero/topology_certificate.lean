import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2763_graded_simple_mul_nonzero
-- topology_sha256: 98405581fdf2d54215726224b23b9ab12382ea5a6b9e50d5bcb9beb5d4539aa7
namespace TopologyCertificate_p2763_graded_simple_mul_nonzero

-- N001 = h_direct: iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤
-- N002 = h_mul: ∀ {g h : G} {x y : A}, x ∈ 𝒜 g → y ∈ 𝒜 h → x * y ∈ 𝒜 (g * h)
-- N003 = h_nonzero_mul: ∃ x y, x * y ≠ 0
-- N004 = h_simple: ∀ (I : Submodule K A), (∀ (r : A) {x : A}, x ∈ I → r * x ∈ I) → (∀ (r : A) {x : A}, x ∈ I → x * r ∈ I) → ⨆ g, 𝒜 g ⊓ I = I → I = ⊥ ∨ I = ⊤
-- N005 = ha0: a ≠ 0
-- N006 = ha: a ∈ 𝒜 g
-- N007 = hb0: b ≠ 0
-- N008 = inst._@.proofs.1850184048._hygCtx._hyg.18: IsScalarTower K A A
-- N009 = inst._@.proofs.1850184048._hygCtx._hyg.23: SMulCommClass K A A
-- N010 = goal: ∃ k, ∃ x ∈ 𝒜 k, a * x * b ≠ 0

-- E001 represents h_goal

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
    (B006 : N006)
    (B007 : N007)
    (B008 : N008)
    (B009 : N009)
    (E001 : N008 → N009 → N001 → N002 → N003 → N004 → N006 → N005 → N007 → N010)
    : N010 := by
  have H_N010 : N010 := E001 B008 B009 B001 B002 B003 B004 B006 B005 B007
  exact H_N010

end TopologyCertificate_p2763_graded_simple_mul_nonzero
