import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1384_scale_prod
-- topology_sha256: 1da667801e740c52d6105a512b20eae005a2c477a38b9219361ad9b071c19e8b
namespace TopologyCertificate_p1384_scale_prod

-- N001 = inst._@.proofs.3934748685._hygCtx._hyg.10: IsTopologicalGroup G
-- N002 = inst._@.proofs.3934748685._hygCtx._hyg.28: LocallyCompactSpace H
-- N003 = inst._@.proofs.3934748685._hygCtx._hyg.31: TotallyDisconnectedSpace H
-- N004 = inst._@.proofs.3934748685._hygCtx._hyg.25: IsTopologicalGroup H
-- N005 = inst._@.proofs.3934748685._hygCtx._hyg.16: TotallyDisconnectedSpace G
-- N006 = inst._@.proofs.3934748685._hygCtx._hyg.13: LocallyCompactSpace G
-- N007 = hPne: SP.Nonempty
-- N008 = hGne: SG.Nonempty
-- N009 = hHne: SH.Nonempty
-- N010 = goal: sInf {n | ∃ U, IsCompact ↑U ∧ IsOpen ↑U ∧ n = U.relIndex (Subgroup.map (φ.toMonoidHom.prodMap ψ.toMonoidHom) U)} = sInf {n | ∃ V, IsCompact ↑V ∧ IsOpen ↑V ∧ n = V.relIndex (Subgroup.map φ.toMonoidHom V)} * sInf {n | ∃ W, IsCompact ↑W ∧ IsOpen ↑W ∧ n = W.relIndex (Subgroup.map ψ.toMonoidHom W)}

-- E001 represents h_001_hpne
-- E002 represents h_002_hgne
-- E003 represents h_003_hhne
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
    (N009 : Prop)
    (N010 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (E001 : N001 → N006 → N005 → N004 → N002 → N003 → N007)
    (E002 : N001 → N006 → N005 → N008)
    (E003 : N004 → N002 → N003 → N009)
    (E004 : N001 → N006 → N005 → N004 → N002 → N003 → N007 → N008 → N009 → N010)
    : N010 := by
  have H_N007 : N007 := E001 B001 B006 B005 B004 B002 B003
  have H_N008 : N008 := E002 B001 B006 B005
  have H_N009 : N009 := E003 B004 B002 B003
  have H_N010 : N010 := E004 B001 B006 B005 B004 B002 B003 H_N007 H_N008 H_N009
  exact H_N010

end TopologyCertificate_p1384_scale_prod
