import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1789_seminormal_reesquotient_iff_radical
-- topology_sha256: ba053d0b8197efdea1b134528fc3518ef2231a2339087641ccb0f7b7557bbc6b
namespace TopologyCertificate_p1789_seminormal_reesquotient_iff_radical

-- N001 = hA: (∀ (a b : A), a ^ 2 = b ^ 2 → a ^ 3 = b ^ 3 → a = b) ∧ ∀ (x y : A), x ^ 3 = y ^ 2 → ∃ z, x = z ^ 2 ∧ y = z ^ 3
-- N002 = hI_zero: 0 ∈ I
-- N003 = hq_fiber: ∀ (a b : A), q a = q b ↔ a = b ∨ a ∈ I ∧ b ∈ I
-- N004 = hq_surjective: Function.Surjective ⇑q
-- N005 = qzero: ∀ (a : A), q a = 0 ↔ a ∈ I
-- N006 = goal: ((∀ (a b : B), a ^ 2 = b ^ 2 → a ^ 3 = b ^ 3 → a = b) ∧ ∀ (x y : B), x ^ 3 = y ^ 2 → ∃ z, x = z ^ 2 ∧ y = z ^ 3) ↔ ∀ (a : A), (∃ n, 1 ≤ n ∧ a ^ n ∈ I) → a ∈ I

-- E001 represents h_001_qzero
-- E002 represents h_goal

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
    (E001 : N002 → N003 → N005)
    (E002 : N001 → N004 → N003 → N005 → N006)
    : N006 := by
  have H_N005 : N005 := E001 B002 B003
  have H_N006 : N006 := E002 B001 B004 B003 H_N005
  exact H_N006

end TopologyCertificate_p1789_seminormal_reesquotient_iff_radical
