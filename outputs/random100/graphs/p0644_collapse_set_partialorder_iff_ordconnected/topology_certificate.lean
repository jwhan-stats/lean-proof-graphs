import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0644_collapse_set_partialorder_iff_ordconnected
-- topology_sha256: ffa7fbe65112bd88a8747c3d228b9e112409eaf0464d453ac16f226471a79af6
namespace TopologyCertificate_p0644_collapse_set_partialorder_iff_ordconnected

-- N001 = hB: B.Nonempty
-- N002 = goal: let Q := { x // x ∉ B } ⊕ Unit; let r := fun x y => match x, y with | Sum.inr val, Sum.inr val_1 => True | Sum.inr val, Sum.inl y => ∃ b ∈ B, b ≤ ↑y | Sum.inl x, Sum.inr val => ∃ b ∈ B, ↑x ≤ b | Sum.inl x, Sum.inl y => ↑x ≤ ↑y ∨ ∃ b ∈ B, ∃ b' ∈ B, ↑x ≤ b ∧ b' ≤ ↑y; IsPartialOrder Q r ↔ B.OrdConnected

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    : N002 := by
  have H_N002 : N002 := E001 B001
  exact H_N002

end TopologyCertificate_p0644_collapse_set_partialorder_iff_ordconnected
