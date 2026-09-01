import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2937_coinvariants_addmonoidalgebra_eq_range
-- topology_sha256: efb7339bd7ad37f7add4d6ffea20ff5f7f3340ddaf8769ccd6fecd3d777912c5
namespace TopologyCertificate_p2937_coinvariants_addmonoidalgebra_eq_range

-- N001 = hφ: Function.Injective ⇑φ
-- N002 = hc: ∀ (m : ↥S), c (AddMonoidAlgebra.single m 1) = AddMonoidAlgebra.single (ψ ↑m) 1 ⊗ₜ[R] AddMonoidAlgebra.single m 1
-- N003 = hexact: Function.Exact ⇑φ ⇑ψ
-- N004 = goal: AlgHom.equalizer c Algebra.TensorProduct.includeRight = (AddMonoidAlgebra.mapDomainAlgHom R R (φ.addSubmonoidComap S)).range

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

end TopologyCertificate_p2937_coinvariants_addmonoidalgebra_eq_range
