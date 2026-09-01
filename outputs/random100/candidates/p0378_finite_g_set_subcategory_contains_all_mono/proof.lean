import Mathlib

/- accepted add_to_file helper 1 -/
import Mathlib
open CategoryTheory
open CategoryTheory.Limits
namespace FiniteGSetProof
universe u
@[reducible]
def trivialMulAction (G : Type u) [Monoid G] (A : Type) : MulAction G A where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
@[reducible]
def trivialObj (G : Type u) [Monoid G] (A : Type) [Finite A] : Action (FintypeCat.{0}) G := by
  letI : MulAction G A := trivialMulAction G A
  exact Action.FintypeCat.ofMulAction G (FintypeCat.of A)
def actionHomOfEquivariant {G : Type u} [Monoid G] {X Y : Action (FintypeCat.{0}) G}
    (φ : X.V.obj → Y.V.obj)
    (hφ : ∀ g x, φ (ConcreteCategory.hom (X.ρ g) x) = ConcreteCategory.hom (Y.ρ g) (φ x)) : X ⟶ Y where
  hom := FintypeCat.homMk φ
  comm := by intro g; ext x; exact hφ g x
lemma concreteCategoryHom_actionHomOfEquivariant {G : Type u} [Monoid G]
    {X Y : Action (FintypeCat.{0}) G} (φ : X.V.obj → Y.V.obj)
    (hφ : ∀ g x, φ (ConcreteCategory.hom (X.ρ g) x) = ConcreteCategory.hom (Y.ρ g) (φ x)) :
    ConcreteCategory.hom (actionHomOfEquivariant φ hφ : X ⟶ Y) = φ := rfl
noncomputable def toTrivialObj (G : Type u) [Monoid G] (A : Type) [Finite A] [Nonempty A]
    (X : Action (FintypeCat.{0}) G) : X ⟶ trivialObj G A :=
  let a : A := Classical.choice inferInstance
  actionHomOfEquivariant (fun _ => a) (by intro g x; rfl)
def trivialMap (G : Type u) [Monoid G] {A B : Type} [Finite A] [Finite B]
    (φ : A → B) : trivialObj G A ⟶ trivialObj G B :=
  actionHomOfEquivariant φ (by intro g x; rfl)
variable (G : Type u) [Group G]
def oneObj : Action (FintypeCat.{0}) G := trivialObj G PUnit
def twoObj : Action (FintypeCat.{0}) G := trivialObj G Bool
noncomputable def oneMap {X : Action (FintypeCat) G} : X ⟶ oneObj G := toTrivialObj G PUnit X
def truth : oneObj G ⟶ twoObj G := trivialMap G (fun _ => true)
def falsehood : oneObj G ⟶ twoObj G := trivialMap G (fun _ => false)
lemma concreteCategoryHom_truth :
    ⇑(ConcreteCategory.hom (truth G)) = (fun _ : PUnit => true) := rfl
lemma concreteCategoryHom_falsehood :
    ⇑(ConcreteCategory.hom (falsehood G)) = (fun _ : PUnit => false) := rfl
noncomputable instance oneUnique (X : Action (FintypeCat) G) : Unique (X ⟶ oneObj G) where
  default := oneMap G
  uniq f := by apply Action.hom_ext; ext x; cases f x; rfl
noncomputable def oneIsTerminal : Limits.IsTerminal (oneObj G) := Limits.IsTerminal.ofUnique (oneObj G)
noncomputable abbrev initialObj : Action (FintypeCat) G := ⊥_ _
noncomputable def truthSource : Bool → Action (FintypeCat) G
  | false => initialObj G
  | true => oneObj G
def truthTarget : Bool → Action (FintypeCat) G
  | false => oneObj G
  | true => oneObj G
noncomputable def sourceCofan : Cofan (truthSource G) where
  pt := oneObj G
  ι := Discrete.natTrans fun
    | ⟨false⟩ => initial.to (oneObj G)
    | ⟨true⟩ => 𝟙 (oneObj G)
noncomputable def sourceCofanIsColimit : IsColimit (sourceCofan G) := by
  refine IsColimit.mk (fun s => s.ι.app ⟨true⟩) ?_ ?_
  · intro s j
    cases j using Discrete.casesOn with
    | mk a =>
      cases a
      · exact initial.hom_ext _ _
      · exact Category.id_comp _
  · intro s m hm
    simpa [sourceCofan] using hm ⟨true⟩
lemma from_one_apply_action {W : Action (FintypeCat) G} (h : oneObj G ⟶ W) (g : G) :
    h PUnit.unit = ConcreteCategory.hom (W.ρ g) (h PUnit.unit) := by
  have hcomm := congrArg (fun φ : (oneObj G).V ⟶ W.V =>
      ConcreteCategory.hom φ PUnit.unit) (h.comm g)
  simpa using hcomm
noncomputable def targetCofan : Cofan (truthTarget G) where
  pt := twoObj G
  ι := Discrete.natTrans fun
    | ⟨false⟩ => truth G
    | ⟨true⟩ => falsehood G
noncomputable def targetCofanIsColimit : IsColimit (targetCofan G) := by
  let desc (s : Cocone (Discrete.functor (truthTarget G))) : twoObj G ⟶ s.pt :=
    actionHomOfEquivariant
      (fun b : (twoObj G).V.obj =>
        match (show Bool from b) with
        | true => s.ι.app ⟨false⟩ PUnit.unit
        | false => s.ι.app ⟨true⟩ PUnit.unit)
      (by
        intro g b
        cases (show Bool from b)
        · exact from_one_apply_action G (s.ι.app ⟨true⟩) g
        · exact from_one_apply_action G (s.ι.app ⟨false⟩) g)
  refine IsColimit.mk desc ?_ ?_
  · intro s j
    cases j using Discrete.casesOn with
    | mk a =>
      cases a
      · apply ConcreteCategory.ext_apply
        intro x
        cases x
        rw [ConcreteCategory.comp_apply]
        change (ConcreteCategory.hom (desc s)) ((ConcreteCategory.hom (truth G)) PUnit.unit) = _
        rw [concreteCategoryHom_actionHomOfEquivariant, concreteCategoryHom_truth]
        rfl
      · apply ConcreteCategory.ext_apply
        intro x
        cases x
        rw [ConcreteCategory.comp_apply]
        change (ConcreteCategory.hom (desc s)) ((ConcreteCategory.hom (falsehood G)) PUnit.unit) = _
        rw [concreteCategoryHom_actionHomOfEquivariant, concreteCategoryHom_falsehood]
        rfl
  · intro s m hm
    apply ConcreteCategory.ext_apply
    intro b
    cases (show Bool from b)
    · have h := ConcreteCategory.congr_hom (hm ⟨true⟩) PUnit.unit
      rw [ConcreteCategory.comp_apply] at h
      change (ConcreteCategory.hom m) ((ConcreteCategory.hom (falsehood G)) PUnit.unit) = _ at h
      rw [concreteCategoryHom_falsehood] at h
      simp only [] at h
      exact h
    · have h := ConcreteCategory.congr_hom (hm ⟨false⟩) PUnit.unit
      rw [ConcreteCategory.comp_apply] at h
      change (ConcreteCategory.hom m) ((ConcreteCategory.hom (truth G)) PUnit.unit) = _ at h
      rw [concreteCategoryHom_truth] at h
      simp only [] at h
      exact h
end FiniteGSetProof

/- accepted add_to_file helper 2 -/
namespace FiniteGSetProof

variable (G : Type u) [Group G]

noncomputable def targetCofanTrue : Cofan (truthTarget G) where
  pt := twoObj G
  ι := Discrete.natTrans fun
    | ⟨false⟩ => falsehood G
    | ⟨true⟩ => truth G

noncomputable def targetCofanTrueIsColimit : IsColimit (targetCofanTrue G) := by
  let desc (s : Cocone (Discrete.functor (truthTarget G))) : twoObj G ⟶ s.pt :=
    actionHomOfEquivariant
      (fun b : (twoObj G).V.obj =>
        match (show Bool from b) with
        | true => s.ι.app ⟨true⟩ PUnit.unit
        | false => s.ι.app ⟨false⟩ PUnit.unit)
      (by
        intro g b
        cases (show Bool from b)
        · exact from_one_apply_action G (s.ι.app ⟨false⟩) g
        · exact from_one_apply_action G (s.ι.app ⟨true⟩) g)
  refine IsColimit.mk desc ?_ ?_
  · intro s j
    cases j using Discrete.casesOn with
    | mk a =>
      cases a
      · apply ConcreteCategory.ext_apply
        intro x
        cases x
        rw [ConcreteCategory.comp_apply]
        change (ConcreteCategory.hom (desc s)) ((ConcreteCategory.hom (falsehood G)) PUnit.unit) = _
        rw [concreteCategoryHom_actionHomOfEquivariant, concreteCategoryHom_falsehood]
        rfl
      · apply ConcreteCategory.ext_apply
        intro x
        cases x
        rw [ConcreteCategory.comp_apply]
        change (ConcreteCategory.hom (desc s)) ((ConcreteCategory.hom (truth G)) PUnit.unit) = _
        rw [concreteCategoryHom_actionHomOfEquivariant, concreteCategoryHom_truth]
        rfl
  · intro s m hm
    apply ConcreteCategory.ext_apply
    intro b
    cases (show Bool from b)
    · have h := ConcreteCategory.congr_hom (hm ⟨false⟩) PUnit.unit
      rw [ConcreteCategory.comp_apply] at h
      change (ConcreteCategory.hom m) ((ConcreteCategory.hom (falsehood G)) PUnit.unit) = _ at h
      rw [concreteCategoryHom_falsehood] at h
      simp only [] at h
      exact h
    · have h := ConcreteCategory.congr_hom (hm ⟨true⟩) PUnit.unit
      rw [ConcreteCategory.comp_apply] at h
      change (ConcreteCategory.hom m) ((ConcreteCategory.hom (truth G)) PUnit.unit) = _ at h
      rw [concreteCategoryHom_truth] at h
      simp only [] at h
      exact h

end FiniteGSetProof

/- accepted add_to_file helper 3 -/
namespace FiniteGSetProof

variable (G : Type u) [Group G]

noncomputable def truthNat : Discrete.functor (truthSource G) ⟶ Discrete.functor (truthTarget G) :=
  Discrete.natTrans fun
    | ⟨false⟩ => initial.to (oneObj G)
    | ⟨true⟩ => 𝟙 (oneObj G)

lemma truthNat_comm (j : Discrete Bool) :
    (sourceCofan G).ι.app j ≫ truth G =
      (truthNat G).app j ≫ (targetCofanTrue G).ι.app j := by
  cases j using Discrete.casesOn with
  | mk a =>
    cases a
    · exact initial.hom_ext _ _
    · rfl

end FiniteGSetProof

/- accepted add_to_file helper 4 -/
namespace FiniteGSetProof

lemma morphismProperty_truth (G : Type*) [Group G] [Finite G]
    (D : CategoryTheory.MorphismProperty (Action (FintypeCat) G))
    (hD_id : {X Y : Action (FintypeCat) G} → (f : X ⟶ Y) →
      D f → D (CategoryTheory.CategoryStruct.id X) ∧
        D (CategoryTheory.CategoryStruct.id Y))
    (hD_pullback : D.IsStableUnderBaseChange)
    (hD_coproduct : D.IsStableUnderFiniteCoproducts)
    (hD_empty : D (CategoryTheory.Limits.initial.to
      (CategoryTheory.Limits.terminal (Action (FintypeCat) G)))) :
    D (truth G) := by
  classical
  haveI : D.IsStableUnderBaseChange := hD_pullback
  haveI : D.IsStableUnderFiniteCoproducts := hD_coproduct
  haveI : D.RespectsIso := hD_pullback.respectsIso
  let e := terminalIsoIsTerminal (oneIsTerminal G)
  have hInitOne' : D (initial.to (terminal (Action (FintypeCat) G)) ≫ e.hom) :=
    MorphismProperty.RespectsIso.postcomp D e.hom
      (initial.to (terminal (Action (FintypeCat) G))) hD_empty
  have hInitOne : D (initial.to (oneObj G)) := by
    convert hInitOne' using 1
  have hIdOne : D (𝟙 (oneObj G)) := (hD_id (initial.to (oneObj G)) hInitOne).2
  have hcomponents : D.functorCategory (Discrete Bool) (truthNat G) := by
    intro j
    cases j using Discrete.casesOn with
    | mk a =>
      cases a
      · exact hInitOne
      · exact hIdOne
  exact (hD_coproduct.isStableUnderCoproductsOfShape Bool).condition
    (Discrete.functor (truthSource G)) (Discrete.functor (truthTarget G))
    (sourceCofan G) (targetCofanTrue G)
    (sourceCofanIsColimit G) (targetCofanTrueIsColimit G)
    (truthNat G) hcomponents (truth G) (fun j => truthNat_comm G j)

end FiniteGSetProof

/- accepted add_to_file helper 5 -/
namespace FiniteGSetProof

variable (G : Type*) [Group G]

lemma rho_apply (X : Action (FintypeCat) G) (g : G) (x : X.V.obj) :
    ConcreteCategory.hom (X.ρ g) x = g • x := by
  rfl

lemma hom_apply_action {X Y : Action (FintypeCat) G} (f : X ⟶ Y) (g : G) (x : X.V.obj) :
    f (ConcreteCategory.hom (X.ρ g) x) = ConcreteCategory.hom (Y.ρ g) (f x) := by
  have h := congrArg (fun φ : X.V ⟶ Y.V => ConcreteCategory.hom φ x) (f.comm g)
  simpa [ConcreteCategory.comp_apply] using h

lemma hom_apply_smul {X Y : Action (FintypeCat) G} (f : X ⟶ Y) (g : G) (x : X.V.obj) :
    f (g • x) = g • f x := by
  simpa [rho_apply G] using hom_apply_action G f g x

end FiniteGSetProof

/- accepted add_to_file helper 6 -/
namespace FiniteGSetProof

variable (G : Type*) [Group G]

noncomputable def characteristicMap {X Y : Action (FintypeCat) G} (f : X ⟶ Y) :
    Y ⟶ twoObj G := by
  classical
  exact actionHomOfEquivariant
    (fun y => if ∃ x : X.V.obj, f x = y then true else false)
    (by
      intro g y
      change (if ∃ x : X.V.obj, f x = g • y then true else false) =
        (if ∃ x : X.V.obj, f x = y then true else false)
      have hiff : (∃ x : X.V.obj, f x = g • y) ↔ (∃ x : X.V.obj, f x = y) := by
        constructor
        · rintro ⟨x, hx⟩
          refine ⟨g⁻¹ • x, ?_⟩
          calc
            f (g⁻¹ • x) = g⁻¹ • f x := hom_apply_smul G f g⁻¹ x
            _ = g⁻¹ • (g • y) := by rw [hx]
            _ = y := inv_smul_smul g y
        · rintro ⟨x, hx⟩
          refine ⟨g • x, ?_⟩
          calc
            f (g • x) = g • f x := hom_apply_smul G f g x
            _ = g • y := by rw [hx]
      rw [propext hiff])

end FiniteGSetProof

/- accepted add_to_file helper 7 -/
namespace FiniteGSetProof

variable (G : Type*) [Group G]

lemma characteristicMap_apply {X Y : Action (FintypeCat) G} (f : X ⟶ Y) (y : Y.V.obj)
    [Decidable (∃ x : X.V.obj, f x = y)] :
    characteristicMap G f y = (if ∃ x : X.V.obj, f x = y then true else false) := by
  unfold characteristicMap
  rw [concreteCategoryHom_actionHomOfEquivariant]
  congr

end FiniteGSetProof

/- accepted add_to_file helper 8 -/
namespace FiniteGSetProof

variable (G : Type*) [Group G]

lemma oneMap_apply {X : Action (FintypeCat) G} (x : X.V.obj) :
    oneMap G x = PUnit.unit := by
  rfl

noncomputable def characteristicSquare {X Y : Action (FintypeCat) G} (f : X ⟶ Y) :
    Square (Action (FintypeCat) G) := by
  classical
  refine Square.mk (oneMap G) f (truth G) (characteristicMap G f) ?_
  apply ConcreteCategory.ext_apply
  intro x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  rw [oneMap_apply, concreteCategoryHom_truth]
  simp [characteristicMap_apply]

end FiniteGSetProof

/- accepted add_to_file helper 9 -/
namespace FiniteGSetProof

variable (G : Type*) [Group G]

lemma characteristicSquare_isPullback {X Y : Action (FintypeCat) G} (f : X ⟶ Y) [Mono f] :
    (characteristicSquare G f).IsPullback := by
  classical
  have hf_inj : Function.Injective (ConcreteCategory.hom f) :=
    (ConcreteCategory.mono_iff_injective_of_preservesPullback f).mp inferInstance
  let F := Action.forget (FintypeCat) G ⋙ FintypeCat.incl
  have hmap : ((characteristicSquare G f).map F).IsPullback := by
    refine (CategoryTheory.Limits.Types.isPullback_iff _ _ _ _).mpr ⟨?_, ?_, ?_⟩
    · exact ((characteristicSquare G f).map F).fac
    · intro x y h
      exact hf_inj h.2
    · intro p y hp
      cases p
      have hχ : characteristicMap G f y = true := hp.symm
      rw [characteristicMap_apply] at hχ
      split at hχ
      case isTrue hmem =>
        rcases hmem with ⟨x, hx⟩
        exact ⟨x, oneMap_apply G x, hx⟩
      case isFalse hnot =>
        simp at hχ
  exact Square.IsPullback.of_map F hmap

end FiniteGSetProof

/- accepted add_to_file helper 10 -/
namespace FiniteGSetProof

universe u v

@[reducible]
def trivialMulActionU (G : Type u) [Monoid G] (A : Type v) : MulAction G A where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[reducible]
def trivialObjU (G : Type u) [Monoid G] (A : Type v) [Finite A] : Action (FintypeCat.{v}) G := by
  letI : MulAction G A := trivialMulActionU G A
  exact Action.FintypeCat.ofMulAction G (FintypeCat.of A)

def actionHomOfEquivariantU {G : Type u} [Monoid G] {X Y : Action (FintypeCat.{v}) G}
    (φ : X.V.obj → Y.V.obj)
    (hφ : ∀ g x, φ (ConcreteCategory.hom (X.ρ g) x) = ConcreteCategory.hom (Y.ρ g) (φ x)) : X ⟶ Y where
  hom := FintypeCat.homMk φ
  comm := by intro g; ext x; exact hφ g x

lemma concreteCategoryHom_actionHomOfEquivariantU {G : Type u} [Monoid G]
    {X Y : Action (FintypeCat.{v}) G} (φ : X.V.obj → Y.V.obj)
    (hφ : ∀ g x, φ (ConcreteCategory.hom (X.ρ g) x) = ConcreteCategory.hom (Y.ρ g) (φ x)) :
    ConcreteCategory.hom (actionHomOfEquivariantU φ hφ : X ⟶ Y) = φ := rfl

noncomputable def toTrivialObjU (G : Type u) [Monoid G] (A : Type v) [Finite A] [Nonempty A]
    (X : Action (FintypeCat.{v}) G) : X ⟶ trivialObjU G A :=
  let a : A := Classical.choice inferInstance
  actionHomOfEquivariantU (fun _ => a) (by intro g x; rfl)

def trivialMapU (G : Type u) [Monoid G] {A B : Type v} [Finite A] [Finite B]
    (φ : A → B) : trivialObjU G A ⟶ trivialObjU G B :=
  actionHomOfEquivariantU φ (by intro g x; rfl)

variable (G : Type u) [Group G]

@[reducible]
def oneObjU : Action (FintypeCat.{v}) G := trivialObjU G (ULift.{v,0} PUnit.{1})
@[reducible]
def twoObjU : Action (FintypeCat.{v}) G := trivialObjU G (ULift.{v,0} Bool)
noncomputable def oneMapU {X : Action (FintypeCat.{v}) G} : X ⟶ oneObjU G :=
  toTrivialObjU G (ULift.{v,0} PUnit.{1}) X
def truthU : oneObjU G ⟶ twoObjU G :=
  trivialMapU G (fun _ : ULift.{v,0} PUnit.{1} => (ULift.up true : ULift.{v,0} Bool))
def falsehoodU : oneObjU G ⟶ twoObjU G :=
  trivialMapU G (fun _ : ULift.{v,0} PUnit.{1} => (ULift.up false : ULift.{v,0} Bool))

lemma concreteCategoryHom_truthU :
    (⇑(ConcreteCategory.hom (truthU G)) : (ULift.{v,0} PUnit.{1}) → ULift.{v,0} Bool) =
      (fun _ : ULift.{v,0} PUnit.{1} => (ULift.up true : ULift.{v,0} Bool)) := rfl
lemma concreteCategoryHom_falsehoodU :
    (⇑(ConcreteCategory.hom (falsehoodU G)) : (ULift.{v,0} PUnit.{1}) → ULift.{v,0} Bool) =
      (fun _ : ULift.{v,0} PUnit.{1} => (ULift.up false : ULift.{v,0} Bool)) := rfl

noncomputable instance oneUniqueU (X : Action (FintypeCat.{v}) G) : Unique (X ⟶ oneObjU G) where
  default := oneMapU G
  uniq f := by
    apply Action.hom_ext
    ext x
    cases f x with
    | up q =>
      cases q
      rfl

noncomputable def oneIsTerminalU : Limits.IsTerminal (oneObjU (G:=G)) :=
  Limits.IsTerminal.ofUnique _

noncomputable abbrev initialObjU : Action (FintypeCat.{v}) G := ⊥_ _

end FiniteGSetProof

/- accepted add_to_file helper 11 -/
namespace FiniteGSetProof
universe u v
variable (G : Type u) [Group G]

noncomputable def truthSourceU : Bool → Action (FintypeCat.{v}) G
  | false => initialObjU G
  | true => oneObjU G

def truthTargetU : Bool → Action (FintypeCat.{v}) G
  | false => oneObjU G
  | true => oneObjU G

noncomputable def sourceCofanU : Cofan (truthSourceU G) where
  pt := oneObjU G
  ι := Discrete.natTrans fun
    | ⟨false⟩ => initial.to (oneObjU G)
    | ⟨true⟩ => 𝟙 (oneObjU G)

noncomputable def sourceCofanUIsColimit : IsColimit (sourceCofanU G) := by
  refine IsColimit.mk (fun s => s.ι.app ⟨true⟩) ?_ ?_
  · intro s j
    cases j using Discrete.casesOn with
    | mk a =>
      cases a
      · exact initial.hom_ext _ _
      · exact Category.id_comp _
  · intro s m hm
    simpa [sourceCofanU] using hm ⟨true⟩

lemma from_one_apply_actionU {W : Action (FintypeCat.{v}) G} (h : oneObjU G ⟶ W) (g : G) :
    h (ULift.up PUnit.unit) = ConcreteCategory.hom (W.ρ g) (h (ULift.up PUnit.unit)) := by
  have hcomm := congrArg (fun φ : (oneObjU G).V ⟶ W.V =>
      ConcreteCategory.hom φ (ULift.up PUnit.unit)) (h.comm g)
  simpa using hcomm

noncomputable def targetCofanTrueU : Cofan (truthTargetU G) where
  pt := twoObjU G
  ι := Discrete.natTrans fun
    | ⟨false⟩ => falsehoodU G
    | ⟨true⟩ => truthU G

noncomputable def targetCofanTrueUIsColimit : IsColimit (targetCofanTrueU G) := by
  let desc (s : Cocone (Discrete.functor (truthTargetU G))) : twoObjU G ⟶ s.pt :=
    actionHomOfEquivariantU
      (fun b : (twoObjU G).V.obj =>
        if (show ULift.{v,0} Bool from b).down then
          s.ι.app ⟨true⟩ (ULift.up PUnit.unit)
        else
          s.ι.app ⟨false⟩ (ULift.up PUnit.unit))
      (by
        intro g b
        cases b with
        | up q =>
          cases q
          · exact from_one_apply_actionU G (s.ι.app ⟨false⟩) g
          · exact from_one_apply_actionU G (s.ι.app ⟨true⟩) g)
  refine IsColimit.mk desc ?_ ?_
  · intro s j
    cases j using Discrete.casesOn with
    | mk a =>
      cases a
      · apply ConcreteCategory.ext_apply
        intro x
        cases x with
        | up q =>
          cases q
          rw [ConcreteCategory.comp_apply]
          change (ConcreteCategory.hom (desc s)) ((ConcreteCategory.hom (falsehoodU G))
            (ULift.up PUnit.unit)) = _
          rw [concreteCategoryHom_actionHomOfEquivariantU, concreteCategoryHom_falsehoodU]
          rfl
      · apply ConcreteCategory.ext_apply
        intro x
        cases x with
        | up q =>
          cases q
          rw [ConcreteCategory.comp_apply]
          change (ConcreteCategory.hom (desc s)) ((ConcreteCategory.hom (truthU G))
            (ULift.up PUnit.unit)) = _
          rw [concreteCategoryHom_actionHomOfEquivariantU, concreteCategoryHom_truthU]
          rfl
  · intro s m hm
    apply ConcreteCategory.ext_apply
    intro b
    cases b with
    | up q =>
      cases q
      · have h := ConcreteCategory.congr_hom (hm ⟨false⟩) (ULift.up PUnit.unit)
        rw [ConcreteCategory.comp_apply] at h
        change (ConcreteCategory.hom m) ((ConcreteCategory.hom (falsehoodU G))
          (ULift.up PUnit.unit)) = _ at h
        rw [concreteCategoryHom_falsehoodU] at h
        simp only [] at h
        exact h
      · have h := ConcreteCategory.congr_hom (hm ⟨true⟩) (ULift.up PUnit.unit)
        rw [ConcreteCategory.comp_apply] at h
        change (ConcreteCategory.hom m) ((ConcreteCategory.hom (truthU G))
          (ULift.up PUnit.unit)) = _ at h
        rw [concreteCategoryHom_truthU] at h
        simp only [] at h
        exact h

end FiniteGSetProof

/- accepted add_to_file helper 12 -/
namespace FiniteGSetProof
universe u v
variable (G : Type u) [Group G]

noncomputable def truthNatU : Discrete.functor (truthSourceU G) ⟶ Discrete.functor (truthTargetU G) :=
  Discrete.natTrans fun
    | ⟨false⟩ => initial.to (oneObjU G)
    | ⟨true⟩ => 𝟙 (oneObjU G)

lemma truthNatU_comm (j : Discrete Bool) :
    (sourceCofanU G).ι.app j ≫ truthU G =
      (truthNatU G).app j ≫ (targetCofanTrueU G).ι.app j := by
  cases j using Discrete.casesOn with
  | mk a =>
    cases a
    · exact initial.hom_ext _ _
    · rfl

end FiniteGSetProof

/- accepted add_to_file helper 13 -/
namespace FiniteGSetProof
universe u v
lemma morphismProperty_truthU (G : Type u) [Group G] [Finite G]
    (D : CategoryTheory.MorphismProperty (Action (FintypeCat.{v}) G))
    (hD_id : {X Y : Action (FintypeCat.{v}) G} → (f : X ⟶ Y) →
      D f → D (CategoryTheory.CategoryStruct.id X) ∧
        D (CategoryTheory.CategoryStruct.id Y))
    (hD_pullback : D.IsStableUnderBaseChange)
    (hD_coproduct : D.IsStableUnderFiniteCoproducts)
    (hD_empty : D (CategoryTheory.Limits.initial.to
      (CategoryTheory.Limits.terminal (Action (FintypeCat.{v}) G)))) :
    D (truthU G) := by
  classical
  haveI : D.IsStableUnderBaseChange := hD_pullback
  haveI : D.IsStableUnderFiniteCoproducts := hD_coproduct
  haveI : D.RespectsIso := hD_pullback.respectsIso
  let e := terminalIsoIsTerminal (oneIsTerminalU (G:=G))
  have hInitOne' : D (initial.to (terminal (Action (FintypeCat.{v}) G)) ≫ e.hom) :=
    MorphismProperty.RespectsIso.postcomp D e.hom
      (initial.to (terminal (Action (FintypeCat.{v}) G))) hD_empty
  have hInitOne : D (initial.to (oneObjU G)) := by
    convert hInitOne' using 1
    exact initial.hom_ext _ _
  have hIdOne : D (𝟙 (oneObjU G)) := (hD_id (initial.to (oneObjU G)) hInitOne).2
  have hcomponents : D.functorCategory (Discrete Bool) (truthNatU G) := by
    intro j
    cases j using Discrete.casesOn with
    | mk a =>
      cases a
      · exact hInitOne
      · exact hIdOne
  exact (hD_coproduct.isStableUnderCoproductsOfShape Bool).condition
    (Discrete.functor (truthSourceU G)) (Discrete.functor (truthTargetU G))
    (sourceCofanU G) (targetCofanTrueU G)
    (sourceCofanUIsColimit G) (targetCofanTrueUIsColimit G)
    (truthNatU G) hcomponents (truthU G) (fun j => truthNatU_comm G j)
end FiniteGSetProof

/- accepted add_to_file helper 14 -/
namespace FiniteGSetProof
universe u v
variable (G : Type u) [Group G]

lemma rho_applyU (X : Action (FintypeCat.{v}) G) (g : G) (x : X.V.obj) :
    ConcreteCategory.hom (X.ρ g) x = g • x := by
  rfl

lemma hom_apply_actionU {X Y : Action (FintypeCat.{v}) G} (f : X ⟶ Y) (g : G) (x : X.V.obj) :
    f (ConcreteCategory.hom (X.ρ g) x) = ConcreteCategory.hom (Y.ρ g) (f x) := by
  have h := congrArg (fun φ : X.V ⟶ Y.V => ConcreteCategory.hom φ x) (f.comm g)
  simpa [ConcreteCategory.comp_apply] using h

lemma hom_apply_smulU {X Y : Action (FintypeCat.{v}) G} (f : X ⟶ Y) (g : G) (x : X.V.obj) :
    f (g • x) = g • f x := by
  simpa [rho_applyU G] using hom_apply_actionU G f g x

end FiniteGSetProof

/- accepted add_to_file helper 15 -/
namespace FiniteGSetProof
universe u v
variable (G : Type u) [Group G]

noncomputable def characteristicMapU {X Y : Action (FintypeCat.{v}) G} (f : X ⟶ Y) :
    Y ⟶ twoObjU G := by
  classical
  exact actionHomOfEquivariantU
    (fun y => if ∃ x : X.V.obj, f x = y then (ULift.up true : ULift.{v,0} Bool)
      else (ULift.up false : ULift.{v,0} Bool))
    (by
      intro g y
      change (if ∃ x : X.V.obj, f x = g • y then (ULift.up true : ULift.{v,0} Bool)
          else (ULift.up false : ULift.{v,0} Bool)) =
        (if ∃ x : X.V.obj, f x = y then (ULift.up true : ULift.{v,0} Bool)
          else (ULift.up false : ULift.{v,0} Bool))
      have hiff : (∃ x : X.V.obj, f x = g • y) ↔ (∃ x : X.V.obj, f x = y) := by
        constructor
        · rintro ⟨x, hx⟩
          refine ⟨g⁻¹ • x, ?_⟩
          calc
            f (g⁻¹ • x) = g⁻¹ • f x := hom_apply_smulU G f g⁻¹ x
            _ = g⁻¹ • (g • y) := by rw [hx]
            _ = y := inv_smul_smul g y
        · rintro ⟨x, hx⟩
          refine ⟨g • x, ?_⟩
          calc
            f (g • x) = g • f x := hom_apply_smulU G f g x
            _ = g • y := by rw [hx]
      rw [propext hiff])

lemma characteristicMapU_apply {X Y : Action (FintypeCat.{v}) G} (f : X ⟶ Y) (y : Y.V.obj)
    [Decidable (∃ x : X.V.obj, f x = y)] :
    characteristicMapU G f y =
      (if ∃ x : X.V.obj, f x = y then (ULift.up true : ULift.{v,0} Bool)
        else (ULift.up false : ULift.{v,0} Bool)) := by
  unfold characteristicMapU
  rw [concreteCategoryHom_actionHomOfEquivariantU]
  congr

lemma oneMapU_apply {X : Action (FintypeCat.{v}) G} (x : X.V.obj) :
    oneMapU G x = ULift.up PUnit.unit := by
  cases oneMapU G x with
  | up q =>
    cases q
    rfl

end FiniteGSetProof

/- accepted add_to_file helper 16 -/
namespace FiniteGSetProof
universe u v
variable (G : Type u) [Group G]

noncomputable def characteristicSquareU {X Y : Action (FintypeCat.{v}) G} (f : X ⟶ Y) :
    Square (Action (FintypeCat.{v}) G) := by
  classical
  refine Square.mk (oneMapU G) f (truthU G) (characteristicMapU G f) ?_
  apply ConcreteCategory.ext_apply
  intro x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  rw [oneMapU_apply, concreteCategoryHom_truthU]
  simp [characteristicMapU_apply]

lemma characteristicSquareU_isPullback {X Y : Action (FintypeCat.{v}) G} (f : X ⟶ Y) [Mono f] :
    (characteristicSquareU G f).IsPullback := by
  classical
  have hf_inj : Function.Injective (ConcreteCategory.hom f) :=
    (ConcreteCategory.mono_iff_injective_of_preservesPullback f).mp inferInstance
  let F := Action.forget (FintypeCat.{v}) G ⋙ FintypeCat.incl
  have hmap : ((characteristicSquareU G f).map F).IsPullback := by
    refine (CategoryTheory.Limits.Types.isPullback_iff _ _ _ _).mpr ⟨?_, ?_, ?_⟩
    · exact ((characteristicSquareU G f).map F).fac
    · intro x y h
      exact hf_inj h.2
    · intro p y hp
      cases p with
      | up q =>
        cases q
        have hχ : characteristicMapU G f y = ULift.up true := hp.symm
        rw [characteristicMapU_apply] at hχ
        split at hχ
        case isTrue hmem =>
          rcases hmem with ⟨x, hx⟩
          exact ⟨x, oneMapU_apply G x, hx⟩
        case isFalse hnot =>
          cases hχ
  exact Square.IsPullback.of_map F hmap

end FiniteGSetProof

/- verified submission -/
theorem finite_G_set_subcategory_contains_all_monomorphisms
    (G : Type*) [Group G] [Finite G]
    (D : CategoryTheory.MorphismProperty (Action (FintypeCat) G))
    (hD_id : {X Y : Action (FintypeCat) G} → (f : X ⟶ Y) →
      D f → D (CategoryTheory.CategoryStruct.id X) ∧
        D (CategoryTheory.CategoryStruct.id Y))
    (hD_comp : D.IsStableUnderComposition)
    (hD_pullback : D.IsStableUnderBaseChange)
    (hD_coproduct : D.IsStableUnderFiniteCoproducts)
    (hD_empty : D (CategoryTheory.Limits.initial.to
      (CategoryTheory.Limits.terminal (Action (FintypeCat) G)))) :
    CategoryTheory.MorphismProperty.monomorphisms (Action (FintypeCat) G) ≤ D := by
  intro X Y f hf
  haveI : Mono f := hf
  haveI : D.IsStableUnderBaseChange := hD_pullback
  have htruth : D (FiniteGSetProof.truthU G) :=
    FiniteGSetProof.morphismProperty_truthU G D hD_id hD_pullback hD_coproduct hD_empty
  exact CategoryTheory.MorphismProperty.of_isPullback
    (FiniteGSetProof.characteristicSquareU_isPullback G f) htruth
