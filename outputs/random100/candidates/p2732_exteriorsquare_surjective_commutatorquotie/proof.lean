import Mathlib

/- accepted add_to_file helper 1 -/
lemma exteriorSquare_derivedSubgroup_le
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ ≤ H := by
  exact hH

lemma exteriorSquare_derived_commutator_le_comap
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    commutator DG ≤ C.comap DG.subtype := by
  intro DG C
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  change commutator DG ≤ C.comap DG.subtype
  rw [← Subgroup.map_le_iff_le_comap]
  rw [Subgroup.map_subtype_commutator]
  exact Subgroup.commutator_mono (exteriorSquare_derivedSubgroup_le H hH) le_top

def exteriorSquare_quotientCommGroup
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    CommGroup (DG ⧸ D) := by
  intro DG C D
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  exact
    { (inferInstance : Group (DG ⧸ D)) with
      mul_comm := fun a b =>
        ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := D)).mpr
          (exteriorSquare_derived_commutator_le_comap H hH)).comm a b }

lemma exteriorSquare_mk_conj
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    ∀ (a : G) (x : DG),
      QuotientGroup.mk' D
          ⟨a * (x : G) * a⁻¹,
            Subgroup.Normal.conj_mem inferInstance (x : G) x.2 a⟩ =
        QuotientGroup.mk' D x := by
  intro DG C D a x
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  let y : DG := ⟨a * (x : G) * a⁻¹,
    Subgroup.Normal.conj_mem inferInstance (x : G) x.2 a⟩
  rw [show QuotientGroup.mk' D y = QuotientGroup.mk' D x ↔ y⁻¹ * x ∈ D from QuotientGroup.eq]
  change ((y⁻¹ * x : DG) : G) ∈ C
  have hcalc : ((y⁻¹ * x : DG) : G) =
      (@commutatorElement G inferInstance).bracket a (x : G)⁻¹ := by
    change (a * (x : G) * a⁻¹)⁻¹ * (x : G) =
      a * (x : G)⁻¹ * a⁻¹ * ((x : G)⁻¹)⁻¹
    group
  rw [hcalc]
  change (@commutatorElement G inferInstance).bracket a (x : G)⁻¹ ∈
    ⁅H, (⊤ : Subgroup G)⁆
  rw [Subgroup.commutator_comm H (⊤ : Subgroup G)]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a)
    (H.inv_mem ((exteriorSquare_derivedSubgroup_le H hH) x.2))

lemma exteriorSquare_mk_comm_mul_left
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    ∀ a₁ a₂ b : G,
      QuotientGroup.mk' D
          ⟨(@commutatorElement G inferInstance).bracket (a₁ * a₂) b,
            Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ =
        QuotientGroup.mk' D
            ⟨(@commutatorElement G inferInstance).bracket a₁ b,
              Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ *
          QuotientGroup.mk' D
            ⟨(@commutatorElement G inferInstance).bracket a₂ b,
              Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ := by
  intro DG C D a₁ a₂ b
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroup H hH
  let c₁ : DG := ⟨(@commutatorElement G inferInstance).bracket a₁ b,
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩
  let c₂ : DG := ⟨(@commutatorElement G inferInstance).bracket a₂ b,
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩
  let c₂conj : DG := ⟨a₁ * (c₂ : G) * a₁⁻¹,
    Subgroup.Normal.conj_mem inferInstance (c₂ : G) c₂.2 a₁⟩
  have hid : (@commutatorElement G inferInstance).bracket (a₁ * a₂) b =
      ((c₂conj * c₁ : DG) : G) := by
    change a₁ * a₂ * b * (a₁ * a₂)⁻¹ * b⁻¹ =
      a₁ * (a₂ * b * a₂⁻¹ * b⁻¹) * a₁⁻¹ * (a₁ * b * a₁⁻¹ * b⁻¹)
    group
  have hsub : (⟨(@commutatorElement G inferInstance).bracket (a₁ * a₂) b,
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) =
      c₂conj * c₁ := Subtype.ext hid
  change QuotientGroup.mk' D (⟨(@commutatorElement G inferInstance).bracket (a₁ * a₂) b,
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) =
      QuotientGroup.mk' D c₁ * QuotientGroup.mk' D c₂
  rw [hsub]
  rw [map_mul]
  rw [exteriorSquare_mk_conj H hH a₁ c₂]
  exact mul_comm _ _

/- accepted add_to_file helper 2 -/
lemma exteriorSquare_mk_comm_mul_right
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    ∀ a b₁ b₂ : G,
      QuotientGroup.mk' D
          ⟨(@commutatorElement G inferInstance).bracket a (b₁ * b₂),
            Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ =
        QuotientGroup.mk' D
            ⟨(@commutatorElement G inferInstance).bracket a b₁,
              Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ *
          QuotientGroup.mk' D
            ⟨(@commutatorElement G inferInstance).bracket a b₂,
              Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ := by
  intro DG C D a b₁ b₂
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  let c₁ : DG := ⟨(@commutatorElement G inferInstance).bracket a b₁,
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩
  let c₂ : DG := ⟨(@commutatorElement G inferInstance).bracket a b₂,
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩
  let c₂conj : DG := ⟨b₁ * (c₂ : G) * b₁⁻¹,
    Subgroup.Normal.conj_mem inferInstance (c₂ : G) c₂.2 b₁⟩
  have hid : (@commutatorElement G inferInstance).bracket a (b₁ * b₂) =
      ((c₁ * c₂conj : DG) : G) := by
    change a * (b₁ * b₂) * a⁻¹ * (b₁ * b₂)⁻¹ =
      (a * b₁ * a⁻¹ * b₁⁻¹) * (b₁ * (a * b₂ * a⁻¹ * b₂⁻¹) * b₁⁻¹)
    group
  have hsub : (⟨(@commutatorElement G inferInstance).bracket a (b₁ * b₂),
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) =
      c₁ * c₂conj := Subtype.ext hid
  change QuotientGroup.mk' D (⟨(@commutatorElement G inferInstance).bracket a (b₁ * b₂),
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) =
      QuotientGroup.mk' D c₁ * QuotientGroup.mk' D c₂
  rw [hsub]
  rw [map_mul]
  rw [exteriorSquare_mk_conj H hH b₁ c₂]

/- accepted add_to_file helper 3 -/
def exteriorSquare_rawLeftHom
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    G → (G →* (DG ⧸ D)) := by
  intro DG C D b
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  exact
    { toFun := fun a =>
        QuotientGroup.mk' D
          ⟨(@commutatorElement G inferInstance).bracket a b,
            Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩
      map_one' := by
        have hsub : (⟨(@commutatorElement G inferInstance).bracket 1 b,
            Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) = 1 :=
          Subtype.ext (commutatorElement_one_left b)
        change QuotientGroup.mk' D
            (⟨(@commutatorElement G inferInstance).bracket 1 b,
              Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) = 1
        rw [hsub]
        rfl
      map_mul' := by
        intro a₁ a₂
        exact exteriorSquare_mk_comm_mul_left H hH a₁ a₂ b }

/- accepted add_to_file helper 4 -/
lemma exteriorSquare_sup_le_rawLeftHom_ker
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    ∀ b : G,
      H ⊔ Subgroup.center G ≤ (exteriorSquare_rawLeftHom H hH b).ker := by
  intro DG C D b
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  rw [sup_le_iff]
  constructor
  · intro x hx
    rw [MonoidHom.mem_ker]
    let xb : DG := ⟨(@commutatorElement G inferInstance).bracket x b,
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩
    change QuotientGroup.mk' D xb = 1
    apply (QuotientGroup.eq_one_iff xb).mpr
    change (@commutatorElement G inferInstance).bracket x b ∈ C
    change (@commutatorElement G inferInstance).bracket x b ∈ ⁅H, (⊤ : Subgroup G)⁆
    exact Subgroup.commutator_mem_commutator hx (Subgroup.mem_top b)
  · intro z hz
    rw [MonoidHom.mem_ker]
    have hcomm : Commute z b := ((Subgroup.mem_center_iff.mp hz b).symm)
    have hsub : (⟨(@commutatorElement G inferInstance).bracket z b,
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) = 1 :=
      Subtype.ext (Commute.commutator_eq hcomm)
    change QuotientGroup.mk' D
        (⟨(@commutatorElement G inferInstance).bracket z b,
          Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) = 1
    rw [hsub]
    rfl

/- accepted add_to_file helper 5 -/
def exteriorSquare_leftHomB
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let K : Subgroup G := H ⊔ Subgroup.center G
    letI : K.Normal := inferInstance
    let B := G ⧸ K
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    G → (B →* (DG ⧸ D)) := by
  intro K B DG C D b
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : K.Normal := by
    change (H ⊔ Subgroup.center G).Normal
    infer_instance
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  exact QuotientGroup.lift K (exteriorSquare_rawLeftHom H hH b)
    (exteriorSquare_sup_le_rawLeftHom_ker H hH b)

/- accepted add_to_file helper 6 -/
@[reducible]
def exteriorSquare_quotientCommGroupRed
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    CommGroup (DG ⧸ D) := by
  intro DG C D
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  exact
    { (inferInstance : Group (DG ⧸ D)) with
      mul_comm := fun a b =>
        ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := D)).mpr
          (exteriorSquare_derived_commutator_le_comap H hH)).comm a b }

/- accepted add_to_file helper 7 -/
lemma exteriorSquare_leftHomB_mk
    {G : Type*} [Group G] (H : Subgroup G) (hH : commutator G ≤ H) :
    letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
    let K : Subgroup G := H ⊔ Subgroup.center G
    letI : K.Normal := inferInstance
    let B := G ⧸ K
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    ∀ a b : G,
      exteriorSquare_leftHomB H hH b (QuotientGroup.mk' K a) =
        exteriorSquare_rawLeftHom H hH b a := by
  intro K B DG C D a b
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : K.Normal := by
    change (H ⊔ Subgroup.center G).Normal
    infer_instance
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  exact QuotientGroup.lift_mk' K (exteriorSquare_sup_le_rawLeftHom_ker H hH b) a

/- accepted add_to_file helper 8 -/
def exteriorSquare_rawRightAddHom
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
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
    G →* Multiplicative (Additive B →+ Additive (DG ⧸ D)) := by
  intro K B DG C D
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : K.Normal := by
    change (H ⊔ Subgroup.center G).Normal
    infer_instance
  letI : CommGroup B :=
    { (inferInstance : Group B) with
      mul_comm := fun a b =>
        ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).mpr
          (hH.trans le_sup_left)).comm a b }
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
  exact
    { toFun := fun b =>
        Multiplicative.ofAdd
          { toFun := fun x =>
              Additive.ofMul ((exteriorSquare_leftHomB H hH b) (Additive.toMul x))
            map_zero' := by
              change Additive.ofMul ((exteriorSquare_leftHomB H hH b) 1) = 0
              rw [map_one]
              rfl
            map_add' := by
              intro x y
              change Additive.ofMul
                  ((exteriorSquare_leftHomB H hH b)
                    (Additive.toMul x * Additive.toMul y)) =
                Additive.ofMul ((exteriorSquare_leftHomB H hH b) (Additive.toMul x)) +
                  Additive.ofMul ((exteriorSquare_leftHomB H hH b) (Additive.toMul y))
              rw [map_mul]
              rfl }
      map_one' := by
        ext a
        change Additive.ofMul ((exteriorSquare_leftHomB H hH 1) (QuotientGroup.mk' K a)) =
          Additive.ofMul 1
        congr 1
        rw [exteriorSquare_leftHomB_mk]
        change QuotientGroup.mk' D
            ⟨(@commutatorElement G inferInstance).bracket a 1,
              Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ = 1
        have hsub : (⟨(@commutatorElement G inferInstance).bracket a 1,
            Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) = 1 :=
          Subtype.ext (commutatorElement_one_right a)
        change QuotientGroup.mk' D
            (⟨(@commutatorElement G inferInstance).bracket a 1,
              Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) = 1
        rw [hsub]
        rfl
      map_mul' := by
        intro b₁ b₂
        ext a
        change Additive.ofMul
            ((exteriorSquare_leftHomB H hH (b₁ * b₂)) (QuotientGroup.mk' K a)) =
          Additive.ofMul ((exteriorSquare_leftHomB H hH b₁) (QuotientGroup.mk' K a)) +
            Additive.ofMul ((exteriorSquare_leftHomB H hH b₂) (QuotientGroup.mk' K a))
        congr 1
        change (exteriorSquare_leftHomB H hH (b₁ * b₂)) (QuotientGroup.mk' K a) =
          (exteriorSquare_leftHomB H hH b₁) (QuotientGroup.mk' K a) *
            (exteriorSquare_leftHomB H hH b₂) (QuotientGroup.mk' K a)
        rw [exteriorSquare_leftHomB_mk, exteriorSquare_leftHomB_mk, exteriorSquare_leftHomB_mk]
        exact exteriorSquare_mk_comm_mul_right H hH a b₁ b₂ }

/- accepted add_to_file helper 9 -/
lemma exteriorSquare_sup_le_rawRightAddHom_ker
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
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
    K ≤ (exteriorSquare_rawRightAddHom H hH).ker := by
  intro K B DG C D
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : K.Normal := by
    change (H ⊔ Subgroup.center G).Normal
    infer_instance
  letI : CommGroup B :=
    { (inferInstance : Group B) with
      mul_comm := fun a b =>
        ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).mpr
          (hH.trans le_sup_left)).comm a b }
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
  rw [sup_le_iff]
  constructor
  · intro x hx
    rw [MonoidHom.mem_ker]
    ext a
    change Additive.ofMul ((exteriorSquare_leftHomB H hH x) (QuotientGroup.mk' K a)) =
      Additive.ofMul 1
    congr 1
    rw [exteriorSquare_leftHomB_mk]
    let ax : DG := ⟨(@commutatorElement G inferInstance).bracket a x,
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩
    change QuotientGroup.mk' D ax = 1
    apply (QuotientGroup.eq_one_iff ax).mpr
    change (@commutatorElement G inferInstance).bracket a x ∈ C
    change (@commutatorElement G inferInstance).bracket a x ∈ ⁅H, (⊤ : Subgroup G)⁆
    rw [Subgroup.commutator_comm H (⊤ : Subgroup G)]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) hx
  · intro z hz
    rw [MonoidHom.mem_ker]
    ext a
    change Additive.ofMul ((exteriorSquare_leftHomB H hH z) (QuotientGroup.mk' K a)) =
      Additive.ofMul 1
    congr 1
    rw [exteriorSquare_leftHomB_mk]
    have hcomm : Commute a z := Subgroup.mem_center_iff.mp hz a
    change QuotientGroup.mk' D
        ⟨(@commutatorElement G inferInstance).bracket a z,
          Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ = 1
    have hsub : (⟨(@commutatorElement G inferInstance).bracket a z,
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) = 1 :=
      Subtype.ext (Commute.commutator_eq hcomm)
    change QuotientGroup.mk' D
        (⟨(@commutatorElement G inferInstance).bracket a z,
          Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) = 1
    rw [hsub]
    rfl

/- accepted add_to_file helper 10 -/
def exteriorSquare_bilinearHom
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
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
    B →* Multiplicative (Additive B →+ Additive (DG ⧸ D)) := by
  intro K B DG C D
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : K.Normal := by
    change (H ⊔ Subgroup.center G).Normal
    infer_instance
  letI : CommGroup B :=
    { (inferInstance : Group B) with
      mul_comm := fun a b =>
        ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).mpr
          (hH.trans le_sup_left)).comm a b }
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
  exact QuotientGroup.lift K (exteriorSquare_rawRightAddHom H hH)
    (exteriorSquare_sup_le_rawRightAddHom_ker H hH)

lemma exteriorSquare_bilinearHom_mk
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
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
    ∀ b : G,
      exteriorSquare_bilinearHom H hH (QuotientGroup.mk' K b) =
        exteriorSquare_rawRightAddHom H hH b := by
  intro K B DG C D b
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : K.Normal := by
    change (H ⊔ Subgroup.center G).Normal
    infer_instance
  letI : CommGroup B :=
    { (inferInstance : Group B) with
      mul_comm := fun a b =>
        ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).mpr
          (hH.trans le_sup_left)).comm a b }
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
  exact QuotientGroup.lift_mk' K (exteriorSquare_sup_le_rawRightAddHom_ker H hH) b

/- accepted add_to_file helper 11 -/
lemma exteriorSquare_bilinearHom_self
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
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
    ∀ x : Additive B,
      (Multiplicative.toAdd (exteriorSquare_bilinearHom H hH (Additive.toMul x))) x = 0 := by
  intro K B DG C D x
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : K.Normal := by
    change (H ⊔ Subgroup.center G).Normal
    infer_instance
  letI : CommGroup B :=
    { (inferInstance : Group B) with
      mul_comm := fun a b =>
        ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).mpr
          (hH.trans le_sup_left)).comm a b }
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective K (Additive.toMul x)
  change (Multiplicative.toAdd (exteriorSquare_bilinearHom H hH (QuotientGroup.mk' K a)))
      (QuotientGroup.mk' K a) = 0
  rw [exteriorSquare_bilinearHom_mk]
  change Additive.ofMul ((exteriorSquare_leftHomB H hH a) (QuotientGroup.mk' K a)) = 0
  rw [exteriorSquare_leftHomB_mk]
  change Additive.ofMul
      (QuotientGroup.mk' D
        ⟨(@commutatorElement G inferInstance).bracket a a,
          Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩) = 0
  congr 1
  have hsub : (⟨(@commutatorElement G inferInstance).bracket a a,
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) = 1 :=
    Subtype.ext (commutatorElement_self a)
  change QuotientGroup.mk' D
      (⟨(@commutatorElement G inferInstance).bracket a a,
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩ : DG) = 1
  rw [hsub]
  rfl

/- accepted add_to_file helper 12 -/
def exteriorSquare_commutatorAlternatingMap
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
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
    Additive B [⋀^Fin 2]→ₗ[ℤ] Additive (DG ⧸ D) := by
  intro K B DG C D
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : K.Normal := by
    change (H ⊔ Subgroup.center G).Normal
    infer_instance
  letI : CommGroup B :=
    { (inferInstance : Group B) with
      mul_comm := fun a b =>
        ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).mpr
          (hH.trans le_sup_left)).comm a b }
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
  let ψ := exteriorSquare_bilinearHom H hH
  let F : (Fin 2 → Additive B) → Additive (DG ⧸ D) := fun v =>
    (Multiplicative.toAdd (ψ (Additive.toMul (v 1)))) (v 0)
  exact
    { toMultilinearMap :=
        { toFun := F
          map_update_add' := by
            intro _ m i x y
            fin_cases i
            · simp [F]
              exact (Multiplicative.toAdd (ψ (Additive.toMul (m 1)))).map_add x y
            · simp [F]
              exact congrArg (fun z => (Multiplicative.toAdd z) (m 0))
                (map_mul ψ (Additive.toMul x) (Additive.toMul y))
          map_update_smul' := by
            intro _ m i c x
            fin_cases i
            · simp [F]
              exact map_zsmul (Multiplicative.toAdd (ψ (Additive.toMul (m 1)))) c x
            · simp [F]
              exact congrArg (fun z => (Multiplicative.toAdd z) (m 0))
                (map_zpow ψ (Additive.toMul x) c) }
      map_eq_zero_of_eq' := by
        intro v i j hij hne
        fin_cases i <;> fin_cases j
        · exact (hne rfl).elim
        · change v 0 = v 1 at hij
          change (Multiplicative.toAdd (ψ (Additive.toMul (v 1)))) (v 0) = 0
          rw [hij]
          exact exteriorSquare_bilinearHom_self H hH (v 1)
        · change v 1 = v 0 at hij
          change (Multiplicative.toAdd (ψ (Additive.toMul (v 1)))) (v 0) = 0
          rw [hij]
          exact exteriorSquare_bilinearHom_self H hH (v 0)
        · exact (hne rfl).elim }

/- accepted add_to_file helper 13 -/
lemma exteriorSquare_alternatingMap_mk
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
    let DG : Subgroup G := ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆
    let C : Subgroup G := ⁅H, (⊤ : Subgroup G)⁆
    let D : Subgroup DG := C.comap DG.subtype
    letI : D.Normal := inferInstance
    letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
    ∀ a b : G,
      exteriorSquare_commutatorAlternatingMap H hH
          ![Additive.ofMul (QuotientGroup.mk' K a),
            Additive.ofMul (QuotientGroup.mk' K b)] =
        Additive.ofMul
          (QuotientGroup.mk' D
            ⟨(@commutatorElement G _).bracket a b,
              Subgroup.commutator_mem_commutator
                (Subgroup.mem_top a) (Subgroup.mem_top b)⟩) := by
  intro K B DG C D a b
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : K.Normal := by
    change (H ⊔ Subgroup.center G).Normal
    infer_instance
  letI : CommGroup B :=
    { (inferInstance : Group B) with
      mul_comm := fun a b =>
        ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).mpr
          (hH.trans le_sup_left)).comm a b }
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
  simp [exteriorSquare_commutatorAlternatingMap]
  change (Multiplicative.toAdd
      (exteriorSquare_bilinearHom H hH (QuotientGroup.mk' K b)))
      (Additive.ofMul (QuotientGroup.mk' K a)) = _
  rw [exteriorSquare_bilinearHom_mk]
  change Additive.ofMul ((exteriorSquare_leftHomB H hH b) (QuotientGroup.mk' K a)) = _
  rw [exteriorSquare_leftHomB_mk]
  rfl

/- verified submission -/
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
                  (Subgroup.mem_top a) (Subgroup.mem_top b)⟩ := by
  intro K B DG C D
  letI : H.Normal := Subgroup.Normal.of_commutator_le G hH
  letI : K.Normal := by
    change (H ⊔ Subgroup.center G).Normal
    infer_instance
  letI : CommGroup B :=
    { (inferInstance : Group B) with
      mul_comm := fun a b =>
        ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := K)).mpr
          (hH.trans le_sup_left)).comm a b }
  letI : D.Normal := by
    change (C.comap DG.subtype).Normal
    infer_instance
  letI : CommGroup (DG ⧸ D) := exteriorSquare_quotientCommGroupRed H hH
  let A := exteriorSquare_commutatorAlternatingMap H hH
  let L := exteriorPower.alternatingMapLinearEquiv A
  let f : Multiplicative ↥(ExteriorAlgebra.exteriorPower ℤ 2 (Additive B)) →* (DG ⧸ D) :=
    { toFun := fun x => Additive.toMul (L (Multiplicative.toAdd x))
      map_one' := by
        change Additive.toMul (L 0) = 1
        rw [map_zero]
        rfl
      map_mul' := by
        intro x y
        change Additive.toMul (L (Multiplicative.toAdd x + Multiplicative.toAdd y)) =
          Additive.toMul (L (Multiplicative.toAdd x)) * Additive.toMul (L (Multiplicative.toAdd y))
        rw [map_add]
        rfl }
  have hmap : ∀ a b : G,
      f (Multiplicative.ofAdd
        ((exteriorPower.ιMulti ℤ 2)
          ![Additive.ofMul (QuotientGroup.mk' K a),
            Additive.ofMul (QuotientGroup.mk' K b)])) =
        QuotientGroup.mk' D
          ⟨(@commutatorElement G _).bracket a b,
            Subgroup.commutator_mem_commutator
              (Subgroup.mem_top a) (Subgroup.mem_top b)⟩ := by
    intro a b
    change Additive.toMul
        ((exteriorPower.alternatingMapLinearEquiv A)
          ((exteriorPower.ιMulti ℤ 2)
            ![Additive.ofMul (QuotientGroup.mk' K a),
              Additive.ofMul (QuotientGroup.mk' K b)])) = _
    rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    rw [exteriorSquare_alternatingMap_mk]
    rfl
  refine ⟨f, ?_, hmap⟩
  rw [← MonoidHom.range_eq_top]
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective D y
  have hx : x.1 ∈ Subgroup.closure
      {g : G | ∃ g₁ ∈ (⊤ : Subgroup G), ∃ g₂ ∈ (⊤ : Subgroup G),
        (@commutatorElement G inferInstance).bracket g₁ g₂ = g} := by
    have hx' := x.2
    change x.1 ∈ ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ at hx'
    rwa [Subgroup.commutator_def] at hx'
  refine Subgroup.closure_induction
      (p := fun g hg =>
        (QuotientGroup.mk' D ⟨g, hg⟩ : DG ⧸ D) ∈ f.range)
      ?_ ?_ ?_ ?_ hx
  · intro g hg
    rcases hg with ⟨a, -, b, -, rfl⟩
    rw [← hmap a b]
    exact ⟨_, rfl⟩
  · change (QuotientGroup.mk' D (1 : DG)) ∈ f.range
    rw [map_one]
    exact f.range.one_mem
  · intro x y hx hy px py
    change (QuotientGroup.mk' D ((⟨x, hx⟩ : DG) * ⟨y, hy⟩)) ∈ f.range
    rw [map_mul]
    exact f.range.mul_mem px py
  · intro x hx px
    change (QuotientGroup.mk' D (⟨x, hx⟩ : DG)⁻¹) ∈ f.range
    rw [map_inv]
    exact f.range.inv_mem px
