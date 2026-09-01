import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1242_finite_support_derivation
-- topology_sha256: bc281170dffb87d8109f2c024ade7a9d553845452e30202f67d3936dd79f381c
namespace TopologyCertificate_p1242_finite_support_derivation

-- N001 = hD: ∀ (S : Set W) (x : W), x ∈ D S ↔ ∃ F, F.Finite ∧ F ⊆ S ∧ x ∈ D F
-- N002 = hn: 1 ≤ n
-- N003 = hP: P ∈ D^[n] A
-- N004 = hsub: {P} ⊆ D^[n] A
-- N005 = goal: ∃ S, (∀ k < n, (S k).Finite) ∧ (∀ k < n, S k ⊆ D^[k] A) ∧ P ∈ D (S (n - 1)) ∧ ∀ (k : ℕ), k + 1 < n → S (k + 1) ⊆ D (S k)

-- E001 represents h_001_hsub
-- E002 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N003 → N004)
    (E002 : N001 → N002 → N004 → N005)
    : N005 := by
  have H_N004 : N004 := E001 B003
  have H_N005 : N005 := E002 B001 B002 H_N004
  exact H_N005

end TopologyCertificate_p1242_finite_support_derivation
