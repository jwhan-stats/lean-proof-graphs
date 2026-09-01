import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p2753_planeposet_union_islinearorder
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 3912a60a684387b05d5689bb47a7924195b241da766a67af7244fb7d2a9fd397
-- reconstructed_proof_sha256: f47032c34e14a483d358cec8af85aa2ceea28ad2a3d4eba066f481c66d572597
-- selected_edge_count: 1

/- verified submission -/
theorem planePoset_union_isLinearOrder
    {P : Type*} [Finite P]
    (leH leR : P → P → Prop)
    (hH : IsPartialOrder P leH)
    (hR : IsPartialOrder P leR)
    (hcompat : ∀ {x y : P}, x ≠ y →
      ((leH x y ∨ leH y x) ↔ ¬ (leR x y ∨ leR y x))) :
    IsLinearOrder P (fun x y => leH x y ∨ leR x y) := by
  let U : P → P → Prop := fun x y => leH x y ∨ leR x y
  change IsLinearOrder P U
  have hreflU : ∀ x : P, U x x := by
    intro x
    exact Or.inl (hH.refl x)
  have htotalU : ∀ x y : P, U x y ∨ U y x := by
    intro x y
    by_cases hxy : x = y
    · subst y
      exact Or.inl (hreflU x)
    · by_cases hr : leR x y ∨ leR y x
      · rcases hr with hrxy | hryx
        · exact Or.inl (Or.inr hrxy)
        · exact Or.inr (Or.inr hryx)
      · have hh : leH x y ∨ leH y x := (hcompat hxy).mpr hr
        rcases hh with hhxy | hhyx
        · exact Or.inl (Or.inl hhxy)
        · exact Or.inr (Or.inl hhyx)
  have hantisymmU : ∀ x y : P, U x y → U y x → x = y := by
    intro x y hxy hyx
    by_cases heq : x = y
    · exact heq
    · rcases hxy with hxyH | hxyR
      · rcases hyx with hyxH | hyxR
        · exact hH.antisymm x y hxyH hyxH
        · have hnoR : ¬ (leR x y ∨ leR y x) :=
            (hcompat heq).mp (Or.inl hxyH)
          exact False.elim (hnoR (Or.inr hyxR))
      · rcases hyx with hyxH | hyxR
        · have hnoR : ¬ (leR x y ∨ leR y x) :=
            (hcompat heq).mp (Or.inr hyxH)
          exact False.elim (hnoR (Or.inl hxyR))
        · exact hR.antisymm x y hxyR hyxR
  have htransU : ∀ x y z : P, U x y → U y z → U x z := by
    intro x y z hxy hyz
    rcases hxy with hxyH | hxyR
    · rcases hyz with hyzH | hyzR
      · exact Or.inl (hH.trans x y z hxyH hyzH)
      · by_cases hxyeq : x = y
        · subst y
          exact Or.inr hyzR
        · by_cases hyzeq : y = z
          · subst z
            exact Or.inl hxyH
          · rcases htotalU x z with hxzU | hzxU
            · exact hxzU
            · rcases hzxU with hzxH | hzxR
              · have hzyH : leH z y := hH.trans z x y hzxH hxyH
                have hnoR : ¬ (leR y z ∨ leR z y) :=
                  (hcompat hyzeq).mp (Or.inr hzyH)
                exact False.elim (hnoR (Or.inl hyzR))
              · have hyxR : leR y x := hR.trans y z x hyzR hzxR
                have hnoR : ¬ (leR x y ∨ leR y x) :=
                  (hcompat hxyeq).mp (Or.inl hxyH)
                exact False.elim (hnoR (Or.inr hyxR))
    · rcases hyz with hyzH | hyzR
      · by_cases hxyeq : x = y
        · subst y
          exact Or.inl hyzH
        · by_cases hyzeq : y = z
          · subst z
            exact Or.inr hxyR
          · rcases htotalU x z with hxzU | hzxU
            · exact hxzU
            · rcases hzxU with hzxH | hzxR
              · have hyxH : leH y x := hH.trans y z x hyzH hzxH
                have hnoR : ¬ (leR x y ∨ leR y x) :=
                  (hcompat hxyeq).mp (Or.inr hyxH)
                exact False.elim (hnoR (Or.inl hxyR))
              · have hzyR : leR z y := hR.trans z x y hzxR hxyR
                have hnoR : ¬ (leR y z ∨ leR z y) :=
                  (hcompat hyzeq).mp (Or.inl hyzH)
                exact False.elim (hnoR (Or.inr hzyR))
      · exact Or.inr (hR.trans x y z hxyR hyzR)
  exact {
    refl := hreflU
    trans := htransU
    antisymm := hantisymmU
    total := htotalU
  }


#check_dependency_graph "planePoset_union_isLinearOrder" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"IsLinearOrder P fun x y => leH x y ∨ leR x y\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hH\",\"statement\":\"IsPartialOrder P leH\"},{\"name\":\"hR\",\"statement\":\"IsPartialOrder P leR\"},{\"name\":\"hcompat\",\"statement\":\"∀ {x y : P}, x ≠ y → (leH x y ∨ leH y x ↔ ¬(leR x y ∨ leR y x))\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2753_planeposet_union_islinearorder\",\"reconstructedProofSha256\":\"f47032c34e14a483d358cec8af85aa2ceea28ad2a3d4eba066f481c66d572597\",\"selectedEdgeCount\":1,\"theoremName\":\"planePoset_union_isLinearOrder\",\"topologySha256\":\"3912a60a684387b05d5689bb47a7924195b241da766a67af7244fb7d2a9fd397\"}"
