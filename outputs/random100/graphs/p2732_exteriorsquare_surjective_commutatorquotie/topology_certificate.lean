import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2732_exteriorsquare_surjective_commutatorquotie
-- topology_sha256: 4c76e8035e3fa2c06ceb6be0f2951f8fb779a8602cf5b04a5536a790c7d79b17
namespace TopologyCertificate_p2732_exteriorsquare_surjective_commutatorquotie

-- N001 = hH: commutator G ≤ H
-- N002 = hmap: ∀ (a b : G), f (Multiplicative.ofAdd ((exteriorPower.ιMulti ℤ 2) ![Additive.ofMul ((QuotientGroup.mk' K) a), Additive.ofMul ((QuotientGroup.mk' K) b)])) = (QuotientGroup.mk' D) ⟨⁅a, b⁆, ⋯⟩
-- N003 = goal: ∃ f, Function.Surjective ⇑f ∧ ∀ (a b : G), f (Multiplicative.ofAdd ((exteriorPower.ιMulti ℤ 2) ![Additive.ofMul ((QuotientGroup.mk' K) a), Additive.ofMul ((QuotientGroup.mk' K) b)])) = (QuotientGroup.mk' D) ⟨⁅a, b⁆, ⋯⟩

-- E001 represents h_001_hmap
-- E002 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    (E002 : N001 → N002 → N003)
    : N003 := by
  have H_N002 : N002 := E001 B001
  have H_N003 : N003 := E002 B001 H_N002
  exact H_N003

end TopologyCertificate_p2732_exteriorsquare_surjective_commutatorquotie
