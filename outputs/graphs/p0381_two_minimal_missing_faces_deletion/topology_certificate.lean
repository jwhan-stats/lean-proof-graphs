import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0381_two_minimal_missing_faces_deletion
-- topology_sha256: 05d1d90c7d2ac7843a9bc9fde3759270e612281999887e2da50afe8bd3dbe0bf
namespace TopologyCertificate_p0381_two_minimal_missing_faces_deletion

-- N001 = hmissing: ∀ (S : Set ℕ), Minimal (fun T => T ⊆ Set.Icc 1 m ∧ T ∉ K) S ↔ S = I ∨ S = J
-- N002 = hS: S ⊆ Set.Icc 1 m \ {w}
-- N003 = hw: w ∈ I ∩ J
-- N004 = goal: S ∈ K

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N001 → N003 → N002 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B001 B003 B002
  exact H_N004

end TopologyCertificate_p0381_two_minimal_missing_faces_deletion
