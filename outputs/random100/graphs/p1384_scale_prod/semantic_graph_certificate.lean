import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1384_scale_prod
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 1da667801e740c52d6105a512b20eae005a2c477a38b9219361ad9b071c19e8b
-- reconstructed_proof_sha256: 34199488470e5da349edf7403291821d8cdb498fcc7d7e556d007843922f8486
-- selected_edge_count: 4

/- accepted add_to_file helper 1 -/
lemma subgroup_map_prodMap {G H : Type*} [Group G] [Group H]
    (P : Subgroup G) (Q : Subgroup H)
    (f : G →* G) (g : H →* H) :
    (P.prod Q).map (f.prodMap g) = (P.map f).prod (Q.map g) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, hfx⟩
    change y ∈ P.prod Q at hy
    rw [Subgroup.mem_prod] at hy
    rw [← hfx]
    change (f y.1, g y.2) ∈ (P.map f).prod (Q.map g)
    rw [Subgroup.mem_prod]
    constructor
    · exact ⟨y.1, hy.1, rfl⟩
    · exact ⟨y.2, hy.2, rfl⟩
  · intro hx
    change x ∈ (P.map f).prod (Q.map g) at hx
    rw [Subgroup.mem_prod] at hx
    rcases hx with ⟨⟨y1, hy1, hf1⟩, ⟨y2, hy2, hf2⟩⟩
    use (y1, y2)
    constructor
    · change (y1, y2) ∈ P.prod Q
      rw [Subgroup.mem_prod]
      exact ⟨hy1, hy2⟩
    · cases x
      simp_all

lemma subgroup_prodEquiv_map {G H : Type*} [Group G] [Group H]
    (P : Subgroup G) (Q : Subgroup H)
    (f : G →* G) (g : H →* H) :
    Subgroup.map (↑(Subgroup.prodEquiv (P.map f) (Q.map g)))
      ((P.prod Q).subgroupOf ((P.map f).prod (Q.map g))) =
      (P.subgroupOf (P.map f)).prod (Q.subgroupOf (Q.map g)) := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨y, hy, hzy⟩
    change y ∈ ((P.prod Q).subgroupOf ((P.map f).prod (Q.map g))) at hy
    rw [← hzy]
    change Subgroup.prodEquiv (P.map f) (Q.map g) y ∈
      (P.subgroupOf (P.map f)).prod (Q.subgroupOf (Q.map g))
    rw [Subgroup.mem_prod]
    rcases y with ⟨⟨p,q⟩, hpq⟩
    rw [Subgroup.mem_prod] at hpq
    constructor
    · exact hy.1
    · exact hy.2
  · intro hz
    change z ∈ (P.subgroupOf (P.map f)).prod (Q.subgroupOf (Q.map g)) at hz
    rw [Subgroup.mem_prod] at hz
    use (Subgroup.prodEquiv (P.map f) (Q.map g)).symm z
    constructor
    · change (Subgroup.prodEquiv (P.map f) (Q.map g)).symm z ∈
        ((P.prod Q).subgroupOf ((P.map f).prod (Q.map g)))
      rcases z with ⟨⟨p,hp⟩,⟨q,hq⟩⟩
      exact hz
    · simp

lemma relIndex_prod_map {G H : Type*} [Group G] [Group H]
    (P : Subgroup G) (Q : Subgroup H)
    (f : G →* G) (g : H →* H) :
    (P.prod Q).relIndex ((P.prod Q).map (f.prodMap g)) =
      P.relIndex (P.map f) * Q.relIndex (Q.map g) := by
  rw [subgroup_map_prodMap]
  unfold Subgroup.relIndex
  rw [← Subgroup.index_map_equiv
    ((P.prod Q).subgroupOf ((P.map f).prod (Q.map g)))
    (Subgroup.prodEquiv (P.map f) (Q.map g)),
    subgroup_prodEquiv_map, Subgroup.index_prod]

lemma exists_compact_open_subgroup_subset {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    {U : Set G} (hU : IsOpen U) (h1U : 1 ∈ U) :
    ∃ S : Subgroup G, IsCompact (S : Set G) ∧ IsOpen (S : Set G) ∧ (S : Set G) ⊆ U := by
  obtain ⟨L, hL, h1L, hLU⟩ := exists_compact_subset hU h1U
  have hclopenbasis := loc_compact_Haus_tot_disc_of_zero_dim (H := G)
  have hLn : interior L ∈ nhds (1 : G) := isOpen_interior.mem_nhds h1L
  rw [hclopenbasis.mem_nhds_iff] at hLn
  rcases hLn with ⟨K, hKclopen, h1K, hKL⟩
  have hKcompact : IsCompact K :=
    hL.of_isClosed_subset hKclopen.isClosed (hKL.trans interior_subset)
  have hKopen : IsOpen K := hKclopen.isOpen
  obtain ⟨D, hDn, hDK⟩ := compact_open_separated_mul_left hKcompact hKopen
    (show K ⊆ K from subset_rfl)
  have hDnint : interior D ∈ nhds (1 : G) := interior_mem_nhds.2 hDn
  have hclopenbasis2 := loc_compact_Haus_tot_disc_of_zero_dim (H := G)
  have hb := (hclopenbasis2.mem_nhds_iff).mp hDnint
  rcases hb with ⟨C0, hC0, h1C0, hC0D⟩
  let C : Set G := C0 ∩ C0⁻¹
  have hCclopen : IsClopen C :=
    hC0.inter ⟨hC0.isClosed.inv, hC0.isOpen.inv⟩
  have h1C : 1 ∈ C := by
    constructor
    · exact h1C0
    · simpa [Set.mem_inv] using h1C0
  have hCD : C ⊆ D := by
    intro c hc
    exact interior_subset (hC0D hc.1)
  have hCinvD : ∀ c ∈ C, c⁻¹ ∈ D := by
    intro c hc
    exact interior_subset (hC0D (by simpa [Set.mem_inv] using hc.2))
  let S : Subgroup G := Subgroup.closure C
  have hSK : (S : Set G) ⊆ K := by
    intro x hx
    induction hx using Subgroup.closure_induction_left with
    | one =>
        exact h1K
    | mul_left c hc y hy hycK =>
        exact hDK (Set.mul_mem_mul (hCD hc) hycK)
    | inv_mul_cancel c hc y hy hycK =>
        exact hDK (Set.mul_mem_mul (hCinvD c hc) hycK)
  have hSopen : IsOpen (S : Set G) := by
    apply Subgroup.isOpen_of_mem_nhds S (g := 1)
    exact Filter.mem_of_superset (hCclopen.isOpen.mem_nhds h1C) Subgroup.subset_closure
  have hScompact : IsCompact (S : Set G) :=
    hKcompact.of_isClosed_subset (S.isClosed_of_isOpen hSopen) hSK
  exact ⟨S, hScompact, hSopen, hSK.trans ((hKL.trans interior_subset).trans hLU)⟩

/- accepted add_to_file helper 2 -/
lemma continuousMulEquiv_image_compact_open {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (φ : G ≃ₜ* G) {U : Subgroup G}
    (hUc : IsCompact (U : Set G)) (hUo : IsOpen (U : Set G)) :
    IsCompact ((U.map φ.toMulEquiv.toMonoidHom : Subgroup G) : Set G) ∧
      IsOpen ((U.map φ.toMulEquiv.toMonoidHom : Subgroup G) : Set G) := by
  constructor
  · rw [Subgroup.coe_map]
    exact hUc.image φ.toHomeomorph.continuous
  · rw [Subgroup.coe_map]
    exact φ.toHomeomorph.isOpenMap _ hUo

lemma relIndex_ne_zero_of_compact_open {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (φ : G ≃ₜ* G) {U : Subgroup G}
    (hUc : IsCompact (U : Set G)) (hUo : IsOpen (U : Set G)) :
    U.relIndex (U.map φ.toMulEquiv.toMonoidHom) ≠ 0 := by
  obtain ⟨hfc, hfo⟩ := continuousMulEquiv_image_compact_open φ hUc hUo
  let K : Subgroup G := U.map φ.toMulEquiv.toMonoidHom
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hfc
  have hsubopen : IsOpen ((U.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
    rw [Subgroup.coe_subgroupOf]
    exact hUo.preimage continuous_subtype_val
  have hfin : Finite (↥K ⧸ U.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen (U.subgroupOf K) hsubopen
  haveI := hfin
  have hfi : (U.subgroupOf K).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hne : (U.subgroupOf K).index ≠ 0 := Subgroup.finiteIndex_iff.mp hfi
  simpa [Subgroup.relIndex, K] using hne

/- accepted add_to_file helper 3 -/
lemma continuousMulEquiv_prod_image_compact_open {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (φ : G ≃ₜ* G) (ψ : H ≃ₜ* H) {U : Subgroup (G × H)}
    (hUc : IsCompact (U : Set (G × H))) (hUo : IsOpen (U : Set (G × H))) :
    IsCompact ((U.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom) :
      Subgroup (G × H)) : Set (G × H)) ∧
    IsOpen ((U.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom) :
      Subgroup (G × H)) : Set (G × H)) := by
  let e : (G × H) ≃ₜ (G × H) := Homeomorph.prodCongr φ.toHomeomorph ψ.toHomeomorph
  have hmap : ((U.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom) :
      Subgroup (G × H)) : Set (G × H)) = e '' (U : Set (G × H)) := by
    rw [Subgroup.coe_map]
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, by ext <;> rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, by ext <;> rfl⟩
  constructor
  · rw [hmap]
    exact hUc.image e.continuous
  · rw [hmap]
    exact e.isOpenMap _ hUo

lemma relIndex_ne_zero_of_compact_open_prod {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (φ : G ≃ₜ* G) (ψ : H ≃ₜ* H) {U : Subgroup (G × H)}
    (hUc : IsCompact (U : Set (G × H))) (hUo : IsOpen (U : Set (G × H))) :
    U.relIndex (U.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom)) ≠ 0 := by
  obtain ⟨hfc, hfo⟩ := continuousMulEquiv_prod_image_compact_open φ ψ hUc hUo
  let K : Subgroup (G × H) :=
    U.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom)
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hfc
  have hsubopen : IsOpen ((U.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
    rw [Subgroup.coe_subgroupOf]
    exact hUo.preimage continuous_subtype_val
  have hfin : Finite (↥K ⧸ U.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen (U.subgroupOf K) hsubopen
  haveI := hfin
  have hfi : (U.subgroupOf K).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hne : (U.subgroupOf K).index ≠ 0 := Subgroup.finiteIndex_iff.mp hfi
  simpa [Subgroup.relIndex, K] using hne

/- accepted add_to_file helper 4 -/
lemma Subgroup.index_eq_map_mul_relIndex_ker {X Y : Type*} [Group X] [Group Y]
    (q : X →* Y) (hsurj : Function.Surjective q) (R : Subgroup X)
    (hkerR : q.ker.relIndex R ≠ 0) :
    R.index = (R.map q).index * R.relIndex q.ker := by
  let K : Subgroup X := q.ker
  let J : Subgroup X := R ⊔ K
  have hmap : (R.map q).index = J.index := by
    have h := Subgroup.index_map R q
    have hrange : q.range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
    rw [hrange, Subgroup.index_top, Nat.mul_one] at h
    simpa [J, K] using h
  have hrel_eq : R.relIndex J = R.relIndex K := by
    have hsup : K.relIndex J = K.relIndex R := by
      simpa [J] using (Subgroup.relIndex_sup_right R K)
    have hinf := Subgroup.relIndex_inf_mul_relIndex R K J
    have hKJ : K ⊓ J = K := by
      exact inf_eq_left.mpr (show K ≤ J from le_sup_right)
    rw [hKJ, hsup] at hinf
    have hchain := Subgroup.relIndex_mul_relIndex (R ⊓ K) R J
      (show R ⊓ K ≤ R from inf_le_left)
      (show R ≤ J from le_sup_left)
    have hI_R : (R ⊓ K).relIndex R = K.relIndex R := by
      rw [inf_comm]
      exact Subgroup.inf_relIndex_right K R
    rw [hI_R] at hchain
    have hcancel : K.relIndex R * R.relIndex K = K.relIndex R * R.relIndex J := by
      calc
        K.relIndex R * R.relIndex K = R.relIndex K * K.relIndex R := Nat.mul_comm _ _
        _ = (R ⊓ K).relIndex J := hinf
        _ = K.relIndex R * R.relIndex J := hchain.symm
    exact (Nat.mul_left_cancel (Nat.pos_of_ne_zero (by simpa [K] using hkerR)) hcancel).symm
  have htrans := Subgroup.relIndex_mul_index (H := R) (K := J) le_sup_left
  rw [hrel_eq, ← hmap, Nat.mul_comm] at htrans
  exact htrans.symm

/- accepted add_to_file helper 5 -/
lemma subgroup_map_fst_compact_open {G H : Type*}
    [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H]
    {U : Subgroup (G × H)}
    (hUc : IsCompact (U : Set (G × H))) (hUo : IsOpen (U : Set (G × H))) :
    IsCompact ((U.map (MonoidHom.fst G H) : Subgroup G) : Set G) ∧
      IsOpen ((U.map (MonoidHom.fst G H) : Subgroup G) : Set G) := by
  constructor
  · rw [Subgroup.coe_map]
    exact hUc.image continuous_fst
  · rw [Subgroup.coe_map]
    exact isOpenMap_fst _ hUo

lemma subgroup_comap_inr_compact_open {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [TotallyDisconnectedSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {U : Subgroup (G × H)}
    (hUc : IsCompact (U : Set (G × H))) (hUo : IsOpen (U : Set (G × H))) :
    IsCompact ((U.comap (MonoidHom.inr G H) : Subgroup H) : Set H) ∧
      IsOpen ((U.comap (MonoidHom.inr G H) : Subgroup H) : Set H) := by
  let f : H →ₜ* G × H := ContinuousMonoidHom.inr G H
  have hpre : ((U.comap (MonoidHom.inr G H) : Subgroup H) : Set H) =
      (fun h : H => ((1 : G), h)) ⁻¹' (U : Set (G × H)) := by
    rw [Subgroup.coe_comap]
    rfl
  have hemb : Topology.IsClosedEmbedding (fun h : H => ((1 : G), h)) := by
    refine Topology.IsClosedEmbedding.mk
      (show Topology.IsEmbedding (Prod.mk (1 : G)) from isEmbedding_prodMkRight (1 : G)) ?_
    have hrange : Set.range (fun h : H => ((1 : G), h)) = ({1} : Set G) ×ˢ Set.univ := by
      ext x
      constructor
      · rintro ⟨h, rfl⟩
        exact ⟨rfl, trivial⟩
      · rintro ⟨hx, -⟩
        rcases x with ⟨g,h⟩
        simp at hx
        subst g
        exact ⟨h, rfl⟩
    rw [hrange]
    exact isClosed_singleton.prod isClosed_univ
  constructor
  · rw [hpre]
    exact hemb.isCompact_preimage hUc
  · rw [hpre]
    exact hUo.preimage f.continuous

/- accepted add_to_file helper 6 -/
lemma Subgroup.index_ne_zero_of_isOpen_of_compact {G : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {K : Subgroup G} (hK : IsCompact (K : Set G))
    {R : Subgroup ↥K} (hR : IsOpen (R : Set ↥K)) :
    R.index ≠ 0 := by
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hK
  have hfin : Finite (↥K ⧸ R) := Subgroup.quotient_finite_of_isOpen R hR
  haveI := hfin
  have hfi : R.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.finiteIndex_iff.mp hfi

/- accepted add_to_file helper 7 -/
noncomputable def kernelFstProdEquiv {G H : Type*} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H]
    (φ : G ≃ₜ* G) (ψ : H ≃ₜ* H) (U : Subgroup (G × H)) :
    let F := φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom
    let X := U.map F
    let B := U.comap (MonoidHom.inr G H)
    let Bf := B.map ψ.toMulEquiv.toMonoidHom
    let q0 := (MonoidHom.fst G H).comp X.subtype
    Bf ≃* q0.rangeRestrict.ker := by
  intro F X B Bf q0
  let e : ↥Bf →* ↥q0.rangeRestrict.ker :=
    (((MonoidHom.inr G H).comp (Bf.subtype)).codRestrict X (by
      intro y
      rcases y with ⟨y, hyBf⟩
      rcases hyBf with ⟨b, hbB, hby⟩
      subst y
      have hm : F (1, b) ∈ X := ⟨(1, b), hbB, rfl⟩
      simpa [F] using hm)).codRestrict q0.rangeRestrict.ker (by
        intro y
        rcases y with ⟨y, hyBf⟩
        rcases hyBf with ⟨b, hbB, hby⟩
        subst y
        simp [q0])
  have hinj : Function.Injective e := by
    intro y z hyz
    apply Subtype.ext
    exact congrArg (fun x : ↥q0.rangeRestrict.ker => (x.1.1.2 : H)) hyz
  have hsurj : Function.Surjective e := by
    intro z
    rcases z with ⟨x, hxker⟩
    rcases x with ⟨x, hxX⟩
    have hq : q0.rangeRestrict ⟨x, hxX⟩ = 1 := hxker
    rcases hxX with ⟨u, hu, hux⟩
    subst x
    have hqval : q0 ⟨F u, by exact ⟨u, hu, rfl⟩⟩ = 1 := congrArg Subtype.val hq
    have hφ : φ u.1 = 1 := by
      simpa [q0, F] using hqval
    have hu1 : u.1 = 1 := by
      apply φ.toMulEquiv.injective
      simpa using hφ
    have huj : u = ((1 : G), u.2) := by
      ext
      · exact hu1
      · rfl
    refine ⟨⟨ψ u.2, ⟨u.2, ?_, rfl⟩⟩, ?_⟩
    · change ((1 : G), u.2) ∈ U
      rw [← huj]
      exact hu
    · ext : 2
      exact Prod.ext hφ.symm rfl
  exact MulEquiv.ofBijective e ⟨hinj, hsurj⟩

/- accepted add_to_file helper 8 -/
lemma kernel_fst_prod_equiv_map {G H : Type*} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H]
    (φ : G ≃ₜ* G) (ψ : H ≃ₜ* H) (U : Subgroup (G × H)) :
    let F := φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom
    let X := U.map F
    let B := U.comap (MonoidHom.inr G H)
    let Bf := B.map ψ.toMulEquiv.toMonoidHom
    let q0 := (MonoidHom.fst G H).comp X.subtype
    Subgroup.map (↑(kernelFstProdEquiv φ ψ U))
      ((B.subgroupOf Bf)) =
      ((U.subgroupOf X).subgroupOf q0.rangeRestrict.ker) := by
  intro F X B Bf q0
  let E := kernelFstProdEquiv φ ψ U
  ext z
  constructor
  · intro hz
    rcases hz with ⟨y, hyB, hEy⟩
    change y ∈ B.subgroupOf Bf at hyB
    change y.val ∈ B at hyB
    rw [← hEy]
    change (E y) ∈ (U.subgroupOf X).subgroupOf q0.rangeRestrict.ker
    change ((E y).val.val : G × H) ∈ U
    change (((1 : G), y.val) : G × H) ∈ U
    exact hyB
  · intro hz
    change z ∈ (U.subgroupOf X).subgroupOf q0.rangeRestrict.ker at hz
    change (z.val.val : G × H) ∈ U at hz
    refine ⟨E.symm z, ?_, ?_⟩
    · change (E.symm z).val ∈ B
      have hyval : (E.symm z).val = z.val.val.2 := by
        have h := congrArg (fun w : ↥q0.rangeRestrict.ker => w.val.val.2)
          (MulEquiv.apply_symm_apply E z)
        simpa [E, kernelFstProdEquiv] using h
      rw [hyval]
      have hfst : z.val.val.1 = 1 := by
        have hq := z.property
        change q0.rangeRestrict z.val = 1 at hq
        have hqval : q0 z.val = 1 := congrArg Subtype.val hq
        simpa [q0] using hqval
      have hzval : z.val.val = ((1 : G), z.val.val.2) := by
        ext
        · exact hfst
        · rfl
      change (((1 : G), z.val.val.2) : G × H) ∈ U
      rw [← hzval]
      exact hz
    · exact MulEquiv.apply_symm_apply E z

/- accepted add_to_file helper 9 -/
lemma relIndex_rangeRestrict_ker_fst {G H : Type*} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H]
    (φ : G ≃ₜ* G) (ψ : H ≃ₜ* H) (U : Subgroup (G × H)) :
    let F := φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom
    let X := U.map F
    let B := U.comap (MonoidHom.inr G H)
    let Bf := B.map ψ.toMulEquiv.toMonoidHom
    let q0 := (MonoidHom.fst G H).comp X.subtype
    (U.subgroupOf X).relIndex q0.rangeRestrict.ker = B.relIndex Bf := by
  intro F X B Bf q0
  unfold Subgroup.relIndex
  rw [← Subgroup.index_map_equiv (B.subgroupOf Bf) (kernelFstProdEquiv φ ψ U),
    kernel_fst_prod_equiv_map]

/- accepted add_to_file helper 10 -/
lemma Subgroup.map_index_mul_relIndex_ker_le_index {X Y : Type*} [Group X] [Group Y]
    (q : X →* Y) (hsurj : Function.Surjective q) (R : Subgroup X)
    [Finite (↥(R ⊔ q.ker) ⧸ R.subgroupOf (R ⊔ q.ker))] :
    (R.map q).index * R.relIndex q.ker ≤ R.index := by
  let K : Subgroup X := q.ker
  let J : Subgroup X := R ⊔ K
  have hmap : (R.map q).index = J.index := by
    have h := Subgroup.index_map R q
    have hrange : q.range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
    rw [hrange, Subgroup.index_top, Nat.mul_one] at h
    simpa [J, K] using h
  have htrans := Subgroup.relIndex_mul_index (H := R) (K := J) le_sup_left
  have hle : R.relIndex K ≤ R.relIndex J := by
    let e : ↥K ⧸ R.subgroupOf K ↪ ↥J ⧸ R.subgroupOf J :=
      Subgroup.quotientSubgroupOfEmbeddingOfLE R (show K ≤ J from le_sup_right)
    have hcard := Nat.card_le_card_of_injective e e.injective
    unfold Subgroup.relIndex
    rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
    simpa [J, K] using hcard
  calc
    (R.map q).index * R.relIndex q.ker = J.index * R.relIndex K := by rw [hmap]
    _ ≤ J.index * R.relIndex J := Nat.mul_le_mul_left _ hle
    _ = R.relIndex J * J.index := Nat.mul_comm _ _
    _ = R.index := htrans

/- accepted add_to_file helper 11 -/
lemma scale_prod_lower {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [TotallyDisconnectedSpace H]
    (φ : G ≃ₜ* G) (ψ : H ≃ₜ* H)
    {U : Subgroup (G × H)}
    (hUc : IsCompact (U : Set (G × H))) (hUo : IsOpen (U : Set (G × H))) :
    sInf {n : ℕ | ∃ V : Subgroup G,
      IsCompact (V : Set G) ∧ IsOpen (V : Set G) ∧
        n = V.relIndex (V.map φ.toMulEquiv.toMonoidHom)} *
    sInf {n : ℕ | ∃ W : Subgroup H,
      IsCompact (W : Set H) ∧ IsOpen (W : Set H) ∧
        n = W.relIndex (W.map ψ.toMulEquiv.toMonoidHom)} ≤
    U.relIndex (U.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom)) := by
  let SG : Set ℕ := {n : ℕ | ∃ V : Subgroup G,
    IsCompact (V : Set G) ∧ IsOpen (V : Set G) ∧
      n = V.relIndex (V.map φ.toMulEquiv.toMonoidHom)}
  let SH : Set ℕ := {n : ℕ | ∃ W : Subgroup H,
    IsCompact (W : Set H) ∧ IsOpen (W : Set H) ∧
      n = W.relIndex (W.map ψ.toMulEquiv.toMonoidHom)}
  have hGne : SG.Nonempty := by
    obtain ⟨S,hSc,hSo,-⟩ := exists_compact_open_subgroup_subset (G := G)
      isOpen_univ (Set.mem_univ 1)
    exact ⟨S.relIndex (S.map φ.toMulEquiv.toMonoidHom), S, hSc, hSo, rfl⟩
  have hHne : SH.Nonempty := by
    obtain ⟨S,hSc,hSo,-⟩ := exists_compact_open_subgroup_subset (G := H)
      isOpen_univ (Set.mem_univ 1)
    exact ⟨S.relIndex (S.map ψ.toMulEquiv.toMonoidHom), S, hSc, hSo, rfl⟩
  let F := φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom
  let X : Subgroup (G × H) := U.map F
  let A : Subgroup G := U.map (MonoidHom.fst G H)
  let Af : Subgroup G := A.map φ.toMulEquiv.toMonoidHom
  let B : Subgroup H := U.comap (MonoidHom.inr G H)
  let Bf : Subgroup H := B.map ψ.toMulEquiv.toMonoidHom
  let q0 : ↥X →* G := (MonoidHom.fst G H).comp X.subtype
  let p : ↥X →* ↥q0.range := q0.rangeRestrict
  let R : Subgroup ↥X := U.subgroupOf X
  obtain ⟨hXc,hXo⟩ := continuousMulEquiv_prod_image_compact_open φ ψ hUc hUo
  obtain ⟨hAc,hAo⟩ := subgroup_map_fst_compact_open hUc hUo
  obtain ⟨hAfc,hAfo⟩ := continuousMulEquiv_image_compact_open φ hAc hAo
  obtain ⟨hBc,hBo⟩ := subgroup_comap_inr_compact_open hUc hUo
  obtain ⟨hBfc,hBfo⟩ := continuousMulEquiv_image_compact_open ψ hBc hBo
  have hRopen : IsOpen (R : Set ↥X) := by
    rw [Subgroup.coe_subgroupOf]
    exact hUo.preimage continuous_subtype_val
  have hrange : q0.range = Af := by
    ext a
    constructor
    · rintro ⟨x, hxa⟩
      rcases x with ⟨x, hxX⟩
      rw [← hxa]
      rcases hxX with ⟨u, hu, hux⟩
      subst x
      refine ⟨u.1, ?_, rfl⟩
      exact ⟨u, hu, rfl⟩
    · rintro ⟨v, hv, hva⟩
      rw [← hva]
      rcases hv with ⟨u, hu, hu1⟩
      rw [← hu1]
      refine ⟨⟨(φ u.1, ψ u.2), ?_⟩, ?_⟩
      · exact ⟨u, hu, rfl⟩
      · rfl
  haveI : CompactSpace ↥X := isCompact_iff_compactSpace.mp hXc
  haveI : CompactSpace ↥q0.range := by
    rw [hrange]
    exact isCompact_iff_compactSpace.mp hAfc
  have hq0cont : Continuous q0 := continuous_fst.comp continuous_subtype_val
  have hpcont : Continuous p := by
    exact hq0cont.subtype_mk (fun x => ⟨x, rfl⟩)
  have hpopen : IsOpenMap p :=
    MonoidHom.isOpenMap_of_sigmaCompact p q0.rangeRestrict_surjective hpcont
  have hpRopen : IsOpen ((R.map p : Subgroup ↥q0.range) : Set ↥q0.range) := by
    rw [Subgroup.coe_map]
    exact hpopen _ hRopen
  have hpRfinite : Finite (↥q0.range ⧸ R.map p) :=
    Subgroup.quotient_finite_of_isOpen (R.map p) hpRopen
  haveI := hpRfinite
  have hpRfi : (R.map p).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let eA : ↥Af ≃* ↥q0.range := MulEquiv.subgroupCongr hrange.symm
  let Dq : Subgroup ↥q0.range := (A.subgroupOf Af).map ↑eA
  have hpR_le_Dq : R.map p ≤ Dq := by
    intro z hz
    rcases hz with ⟨r, hrR, hpr⟩
    rw [← hpr]
    refine ⟨eA.symm (p r), ?_, eA.apply_symm_apply _⟩
    change (eA.symm (p r)).val ∈ A
    change (r.val.1 : G) ∈ A
    change r.val ∈ U at hrR
    exact ⟨r.val, hrR, rfl⟩
  have hfirst_index : A.relIndex Af ≤ (R.map p).index := by
    have hD : Dq.index = A.relIndex Af := by
      dsimp [Dq]
      rw [Subgroup.index_map_equiv]
      rfl
    rw [← hD]
    exact Subgroup.index_antitone hpR_le_Dq
  have hsG : sInf SG ≤ A.relIndex Af :=
    Nat.sInf_le ⟨A,hAc,hAo,rfl⟩
  have hsG' : sInf SG ≤ (R.map p).index := hsG.trans hfirst_index
  have hsH : sInf SH ≤ B.relIndex Bf :=
    Nat.sInf_le ⟨B,hBc,hBo,rfl⟩
  have hfactor : R.relIndex p.ker = B.relIndex Bf := by
    simpa [F,X,B,Bf,q0,p,R] using relIndex_rangeRestrict_ker_fst φ ψ U
  have hsH' : sInf SH ≤ R.relIndex p.ker := by
    rw [hfactor]
    exact hsH
  have hJopen : IsOpen ((R ⊔ p.ker : Subgroup ↥X) : Set ↥X) := by
    let RO : OpenSubgroup ↥X := { toSubgroup := R, isOpen' := hRopen }
    exact Subgroup.isOpen_of_openSubgroup (R ⊔ p.ker) (U := RO) le_sup_left
  have hJcompact : IsCompact ((R ⊔ p.ker : Subgroup ↥X) : Set ↥X) := by
    exact isCompact_univ.of_isClosed_subset ((R ⊔ p.ker).isClosed_of_isOpen hJopen)
      (Set.subset_univ _)
  have hRsubJopen : IsOpen ((R.subgroupOf (R ⊔ p.ker) : Subgroup ↥(R ⊔ p.ker)) :
      Set ↥(R ⊔ p.ker)) := by
    rw [Subgroup.coe_subgroupOf]
    exact hRopen.preimage continuous_subtype_val
  have hJfinite : Finite (↥(R ⊔ p.ker) ⧸ R.subgroupOf (R ⊔ p.ker)) := by
    haveI : CompactSpace ↥(R ⊔ p.ker) := isCompact_iff_compactSpace.mp hJcompact
    exact Subgroup.quotient_finite_of_isOpen _ hRsubJopen
  haveI := hJfinite
  have hdecomp := Subgroup.map_index_mul_relIndex_ker_le_index p
    q0.rangeRestrict_surjective R
  rw [hfactor] at hdecomp
  have hdecomp' : (R.map p).index * B.relIndex Bf ≤ U.relIndex X := by
    simpa [Subgroup.relIndex, R] using hdecomp
  have hmul : sInf SG * sInf SH ≤ (R.map p).index * B.relIndex Bf := by
    exact Nat.mul_le_mul hsG' hsH
  exact hmul.trans hdecomp'

/- verified submission -/
theorem scale_prod
    {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [TotallyDisconnectedSpace H]
    (φ : G ≃ₜ* G) (ψ : H ≃ₜ* H) :
    sInf {n : ℕ | ∃ U : Subgroup (G × H),
      IsCompact (U : Set (G × H)) ∧ IsOpen (U : Set (G × H)) ∧
        n = U.relIndex (U.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom))} =
      sInf {n : ℕ | ∃ V : Subgroup G,
        IsCompact (V : Set G) ∧ IsOpen (V : Set G) ∧
          n = V.relIndex (V.map φ.toMulEquiv.toMonoidHom)} *
      sInf {n : ℕ | ∃ W : Subgroup H,
        IsCompact (W : Set H) ∧ IsOpen (W : Set H) ∧
          n = W.relIndex (W.map ψ.toMulEquiv.toMonoidHom)} := by
  let SP : Set ℕ := {n : ℕ | ∃ U : Subgroup (G × H),
    IsCompact (U : Set (G × H)) ∧ IsOpen (U : Set (G × H)) ∧
      n = U.relIndex (U.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom))}
  let SG : Set ℕ := {n : ℕ | ∃ V : Subgroup G,
    IsCompact (V : Set G) ∧ IsOpen (V : Set G) ∧
      n = V.relIndex (V.map φ.toMulEquiv.toMonoidHom)}
  let SH : Set ℕ := {n : ℕ | ∃ W : Subgroup H,
    IsCompact (W : Set H) ∧ IsOpen (W : Set H) ∧
      n = W.relIndex (W.map ψ.toMulEquiv.toMonoidHom)}
  have hPne : SP.Nonempty := by
    obtain ⟨S,hSc,hSo,-⟩ := exists_compact_open_subgroup_subset (G := G × H)
      isOpen_univ (Set.mem_univ 1)
    exact ⟨S.relIndex (S.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom)),
      S, hSc, hSo, rfl⟩
  have hGne : SG.Nonempty := by
    obtain ⟨S,hSc,hSo,-⟩ := exists_compact_open_subgroup_subset (G := G)
      isOpen_univ (Set.mem_univ 1)
    exact ⟨S.relIndex (S.map φ.toMulEquiv.toMonoidHom), S, hSc, hSo, rfl⟩
  have hHne : SH.Nonempty := by
    obtain ⟨S,hSc,hSo,-⟩ := exists_compact_open_subgroup_subset (G := H)
      isOpen_univ (Set.mem_univ 1)
    exact ⟨S.relIndex (S.map ψ.toMulEquiv.toMonoidHom), S, hSc, hSo, rfl⟩
  apply le_antisymm
  · obtain ⟨V,hVc,hVo,hVmin⟩ := Nat.sInf_mem hGne
    obtain ⟨W,hWc,hWo,hWmin⟩ := Nat.sInf_mem hHne
    have hprod_mem : sInf SG * sInf SH ∈ SP := by
      refine ⟨V.prod W, ?_, ?_, ?_⟩
      · rw [Subgroup.coe_prod]
        exact hVc.prod hWc
      · rw [Subgroup.coe_prod]
        exact hVo.prod hWo
      · calc
          sInf SG * sInf SH =
              V.relIndex (V.map φ.toMulEquiv.toMonoidHom) *
                W.relIndex (W.map ψ.toMulEquiv.toMonoidHom) := by
            rw [hVmin, hWmin]
          _ = (V.prod W).relIndex
              ((V.prod W).map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom)) := by
            exact (relIndex_prod_map V W φ.toMulEquiv.toMonoidHom ψ.toMulEquiv.toMonoidHom).symm
    exact Nat.sInf_le hprod_mem
  · apply le_csInf hPne
    intro n hn
    rcases hn with ⟨U,hUc,hUo,hn⟩
    rw [hn]
    exact scale_prod_lower φ ψ hUc hUo


#check_dependency_graph "scale_prod" against "{\"edges\":[{\"conclusion\":{\"name\":\"hPne\",\"statement\":\"SP.Nonempty\"},\"graphEdgeId\":\"h_001_hpne\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"IsTopologicalGroup G\"},{\"name\":\"<generated-instance>\",\"statement\":\"LocallyCompactSpace G\"},{\"name\":\"<generated-instance>\",\"statement\":\"TotallyDisconnectedSpace G\"},{\"name\":\"<generated-instance>\",\"statement\":\"IsTopologicalGroup H\"},{\"name\":\"<generated-instance>\",\"statement\":\"LocallyCompactSpace H\"},{\"name\":\"<generated-instance>\",\"statement\":\"TotallyDisconnectedSpace H\"}],\"rawEdgeId\":\"telescope_17\"},{\"conclusion\":{\"name\":\"hGne\",\"statement\":\"SG.Nonempty\"},\"graphEdgeId\":\"h_002_hgne\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"IsTopologicalGroup G\"},{\"name\":\"<generated-instance>\",\"statement\":\"LocallyCompactSpace G\"},{\"name\":\"<generated-instance>\",\"statement\":\"TotallyDisconnectedSpace G\"}],\"rawEdgeId\":\"telescope_18\"},{\"conclusion\":{\"name\":\"hHne\",\"statement\":\"SH.Nonempty\"},\"graphEdgeId\":\"h_003_hhne\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"IsTopologicalGroup H\"},{\"name\":\"<generated-instance>\",\"statement\":\"LocallyCompactSpace H\"},{\"name\":\"<generated-instance>\",\"statement\":\"TotallyDisconnectedSpace H\"}],\"rawEdgeId\":\"telescope_19\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"sInf {n | ∃ U, IsCompact ↑U ∧ IsOpen ↑U ∧ n = U.relIndex (Subgroup.map (φ.toMonoidHom.prodMap ψ.toMonoidHom) U)} = sInf {n | ∃ V, IsCompact ↑V ∧ IsOpen ↑V ∧ n = V.relIndex (Subgroup.map φ.toMonoidHom V)} * sInf {n | ∃ W, IsCompact ↑W ∧ IsOpen ↑W ∧ n = W.relIndex (Subgroup.map ψ.toMonoidHom W)}\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"IsTopologicalGroup G\"},{\"name\":\"<generated-instance>\",\"statement\":\"LocallyCompactSpace G\"},{\"name\":\"<generated-instance>\",\"statement\":\"TotallyDisconnectedSpace G\"},{\"name\":\"<generated-instance>\",\"statement\":\"IsTopologicalGroup H\"},{\"name\":\"<generated-instance>\",\"statement\":\"LocallyCompactSpace H\"},{\"name\":\"<generated-instance>\",\"statement\":\"TotallyDisconnectedSpace H\"},{\"name\":\"hPne\",\"statement\":\"SP.Nonempty\"},{\"name\":\"hGne\",\"statement\":\"SG.Nonempty\"},{\"name\":\"hHne\",\"statement\":\"SH.Nonempty\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1384_scale_prod\",\"reconstructedProofSha256\":\"34199488470e5da349edf7403291821d8cdb498fcc7d7e556d007843922f8486\",\"selectedEdgeCount\":4,\"theoremName\":\"scale_prod\",\"topologySha256\":\"1da667801e740c52d6105a512b20eae005a2c477a38b9219361ad9b071c19e8b\"}"
