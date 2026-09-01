theorem exteriorSquare_surjective_commutatorQuotient
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let K : Subgroup G := H ⊔ Subgroup.center G
    letI : K.Normal := inferInstance
    let B := G ⧸ K
    letI : CommGroup B :=
      { (inferInstance : Group B) with
        mul_comm := fun a b =>
          ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).mpr
            (hH.trans le_sup_left)).comm a b }
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), ⊤⁆
    let C : Subgroup G := ⁅H, ⊤⁆
    letI : C.Normal := inferInstance
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    ∃ f : Multiplicative ↥(ExteriorAlgebra.exteriorPower ℤ 2 (Additive B)) →* (DG ⧸ D),
      Function.Surjective f ∧
        ∀ a b : G,
          f (Multiplicative.ofAdd
            ((exteriorPower.ιMulti ℤ 2)
              ![Additive.ofMul (QuotientGroup.mk' K a),
                Additive.ofMul (QuotientGroup.mk' K b)])) =
            QuotientGroup.mk' D
              ⟨(@commutatorElement G _).bracket a b,
                Subgroup.commutator_mem_commutator
                  (Subgroup.mem_top a) (Subgroup.mem_top b)⟩ := by sorry
