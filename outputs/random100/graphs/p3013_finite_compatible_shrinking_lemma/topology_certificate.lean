import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p3013_finite_compatible_shrinking_lemma
-- topology_sha256: 8b9aca9fc832e636b74f6b231361ef29e13d563e12637c3874475ffa894fc31d
namespace TopologyCertificate_p3013_finite_compatible_shrinking_lemma

-- N001 = hO: IsOpen O
-- N002 = hW: ∀ (K : Set (Fin N)), K.Nonempty → IsOpen (W K) ∧ W K ⊆ O ∧ W K ∩ Z = ⋂ i ∈ K, Zi i
-- N003 = hZclosed: IsClosed (Subtype.val ⁻¹' Z)
-- N004 = hZi_open: ∀ (i : Fin N), IsOpen (Subtype.val ⁻¹' Zi i)
-- N005 = hZi_subset: ∀ (i : Fin N), Zi i ⊆ Z
-- N006 = hZO: Z ⊆ O
-- N007 = goal: ∃ U, (∀ (K : Set (Fin N)), K.Nonempty → IsOpen (U K) ∧ U K ⊆ W K ∧ U K ∩ Z = ⋂ i ∈ K, Zi i) ∧ ∀ (J K : Set (Fin N)), J.Nonempty → K.Nonempty → U J ∩ U K = U (J ∪ K)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (E001 : N001 → N006 → N003 → N005 → N004 → N002 → N007)
    : N007 := by
  have H_N007 : N007 := E001 B001 B006 B003 B005 B004 B002
  exact H_N007

end TopologyCertificate_p3013_finite_compatible_shrinking_lemma
