import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1552_index_two_infinite_cyclic_classification
-- topology_sha256: b970c05a80a45b5cb42281387b00efc48d0120f20aec20b1b700ceda483f090b
namespace TopologyCertificate_p1552_index_two_infinite_cyclic_classification

-- N001 = hgen: Subgroup.closure {v, t} = ⊤
-- N002 = hindex: (Subgroup.zpowers t).index = 2
-- N003 = htinf: Infinite ↥(Subgroup.zpowers t)
-- N004 = htors: ∃ x, x ≠ 1 ∧ IsOfFinOrder x
-- N005 = htinj: Function.Injective fun k => t ^ k
-- N006 = hvH: v ∉ Subgroup.zpowers t
-- N007 = hv2mem: v * v ∈ Subgroup.zpowers t
-- N008 = goal: (∃ n e, e (PresentedGroup.of 0) = v ∧ e (PresentedGroup.of 1) = t ∧ Nonempty (K ≃* Multiplicative ℤ × Multiplicative (ZMod 2))) ∨ ∃ e, e (PresentedGroup.of 0) = v ∧ e (PresentedGroup.of 1) = t ∧ Nonempty (K ≃* Monoid.Coprod (Multiplicative (ZMod 2)) (Multiplicative (ZMod 2)))

-- E001 represents h_001_htinj
-- E002 represents h_002_hvh
-- E003 represents h_003_hv2mem
-- E004 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (N008 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N003 → N005)
    (E002 : N001 → N002 → N006)
    (E003 : N002 → N007)
    (E004 : N001 → N002 → N004 → N005 → N006 → N007 → N008)
    : N008 := by
  have H_N005 : N005 := E001 B003
  have H_N006 : N006 := E002 B001 B002
  have H_N007 : N007 := E003 B002
  have H_N008 : N008 := E004 B001 B002 B004 H_N005 H_N006 H_N007
  exact H_N008

end TopologyCertificate_p1552_index_two_infinite_cyclic_classification
