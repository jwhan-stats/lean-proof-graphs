import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1461_directed_closure_singleton_iff_chain_closu
-- topology_sha256: 802c35783f6009a5c5c37cffb5c7f6daf1d69d7d6c18bf81c1aa855e0a067907
namespace TopologyCertificate_p1461_directed_closure_singleton_iff_chain_closu

-- N001 = inst._@.proof.2120908755._hygCtx._hyg.6: T0Space X
-- N002 = goal: (∀ (D : Set X), D.Nonempty → DirectedOn LE.le D → ∃! x, closure D = closure {x}) ↔ ∀ (C : Set X), C.Nonempty → IsChain LE.le C → ∃! x, closure C = closure {x}

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    : N002 := by
  have H_N002 : N002 := E001 B001
  exact H_N002

end TopologyCertificate_p1461_directed_closure_singleton_iff_chain_closu
