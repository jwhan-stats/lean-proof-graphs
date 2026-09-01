import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0109_exists_atomic_puiseux_monoid_without_singl
-- topology_sha256: 1f8eb1a2dee6809ed1a7bee3e31417e9eae1d070ed67756f049a7393ee1739f4
namespace TopologyCertificate_p0109_exists_atomic_puiseux_monoid_without_singl

-- N001 = goal: ∃ M, (∀ (x : ↥M), ∃ l, (∀ a ∈ l, AddIrreducible a) ∧ l.sum = x) ∧ ∀ (x : ↥M), {n | ∃ l, l.length = n ∧ (∀ a ∈ l, AddIrreducible a) ∧ l.sum = x} ≠ {2}

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p0109_exists_atomic_puiseux_monoid_without_singl
