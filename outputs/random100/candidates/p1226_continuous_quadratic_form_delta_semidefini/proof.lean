import Mathlib

/- accepted add_to_file helper 1 -/
import Mathlib

/-- A fresh copy of a real vector space, used to equip it with a new pre-inner product. -/
structure QuadraticPreHilbert (X : Type u) [AddCommGroup X] [Module ℝ X] where
  val : X

namespace QuadraticPreHilbert

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

def equiv : QuadraticPreHilbert X ≃ X where
  toFun := val
  invFun := mk
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; rfl

instance : AddCommGroup (QuadraticPreHilbert X) := equiv.addCommGroup
instance : Module ℝ (QuadraticPreHilbert X) := Equiv.module ℝ equiv

@[simp] theorem val_zero : (0 : QuadraticPreHilbert X).val = 0 := rfl
@[simp] theorem val_add (x y : QuadraticPreHilbert X) : (x + y).val = x.val + y.val := rfl
@[simp] theorem val_smul (r : ℝ) (x : QuadraticPreHilbert X) : (r • x).val = r • x.val := rfl

/-- The pre-inner product associated with the symmetrization of a continuous bilinear form. -/
@[implicit_reducible]
noncomputable def preCore (bp : X →L[ℝ] X →L[ℝ] ℝ)
    (hnonneg : ∀ x : X, 0 ≤ (bp x x + bp x x) / 2) :
    PreInnerProductSpace.Core ℝ (QuadraticPreHilbert X) where
  inner x y := (bp x.val y.val + bp y.val x.val) / 2
  conj_inner_symm x y := by
    simp [add_comm]
  re_inner_nonneg x := hnonneg x.val
  add_left x y z := by
    simp [map_add]
    ring_nf
  smul_left x y r := by
    simp [map_smul]
    ring_nf

end QuadraticPreHilbert

/- accepted add_to_file helper 2 -/
lemma dominated_bilinear_abs_le_avg
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : X → ℝ) (T : X →L[ℝ] (X →L[ℝ] ℝ))
    (hTq : ∀ x : X, q x = T x x)
    (hTsymm : ∀ x y : X, T x y = T y x)
    (bp : X →L[ℝ] X →L[ℝ] ℝ)
    (hdom : ∀ x : X, |q x| ≤ bp x x)
    (x y : X) :
    |T x y| ≤ (bp x x + bp y y) / 2 := by
  have hpol : T (x+y) (x+y) - T (x-y) (x-y) = 4 * T x y := by
    simp [map_add, map_sub, hTsymm x y]
    ring
  have hpsum : bp (x+y) (x+y) + bp (x-y) (x-y) =
      2 * (bp x x + bp y y) := by
    simp [map_add, map_sub]
    ring
  have hplus : |T (x+y) (x+y)| ≤ bp (x+y) (x+y) := by
    simpa [hTq] using hdom (x+y)
  have hminus : |T (x-y) (x-y)| ≤ bp (x-y) (x-y) := by
    simpa [hTq] using hdom (x-y)
  have hsub : |T (x+y) (x+y) - T (x-y) (x-y)| ≤
      bp (x+y) (x+y) + bp (x-y) (x-y) := by
    calc
      |T (x+y) (x+y) - T (x-y) (x-y)|
          ≤ |T (x+y) (x+y)| + |T (x-y) (x-y)| := abs_sub _ _
      _ ≤ bp (x+y) (x+y) + bp (x-y) (x-y) := add_le_add hplus hminus
  rw [hpol, hpsum] at hsub
  have habs4 : |4 * T x y| = 4 * |T x y| := by norm_num [abs_of_nonneg]
  rw [habs4] at hsub
  nlinarith [abs_nonneg (T x y)]

/- accepted add_to_file helper 3 -/
lemma dominated_bilinear_abs_le_sqrt_mul
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : X → ℝ) (T : X →L[ℝ] (X →L[ℝ] ℝ))
    (hTq : ∀ x : X, q x = T x x)
    (hTsymm : ∀ x y : X, T x y = T y x)
    (bp : X →L[ℝ] X →L[ℝ] ℝ)
    (hdom : ∀ x : X, |q x| ≤ bp x x)
    (x y : X) :
    |T x y| ≤ Real.sqrt (bp x x) * Real.sqrt (bp y y) := by
  have hpx : 0 ≤ bp x x := le_trans (abs_nonneg _) (hdom x)
  have hpy : 0 ≤ bp y y := le_trans (abs_nonneg _) (hdom y)
  by_cases hx0 : bp x x = 0
  · by_contra hz
    have hzne : |T x y| ≠ 0 := by
      intro hzero
      apply hz
      rw [hzero]
      positivity
    have hzpos : 0 < |T x y| := lt_of_le_of_ne' (abs_nonneg _) hzne
    let r : ℝ := (bp y y / 2 + 1) / |T x y|
    have hrpos : 0 < r := by positivity
    have hb := dominated_bilinear_abs_le_avg q T hTq hTsymm bp hdom (r • x) y
    simp [hx0, map_smul, abs_mul, abs_of_pos hrpos] at hb
    have hreq : r * |T x y| = bp y y / 2 + 1 := by
      dsimp [r]
      field_simp [ne_of_gt hzpos]
    nlinarith [hpy]
  · by_cases hy0 : bp y y = 0
    · by_contra hz
      have hzne : |T x y| ≠ 0 := by
        intro hzero
        apply hz
        rw [hzero]
        positivity
      have hzpos : 0 < |T x y| := lt_of_le_of_ne' (abs_nonneg _) hzne
      let r : ℝ := (bp x x / 2 + 1) / |T x y|
      have hrpos : 0 < r := by positivity
      have hb := dominated_bilinear_abs_le_avg q T hTq hTsymm bp hdom x (r • y)
      simp [hy0, map_smul, abs_mul, abs_of_pos hrpos] at hb
      have hreq : r * |T x y| = bp x x / 2 + 1 := by
        dsimp [r]
        field_simp [ne_of_gt hzpos]
      nlinarith [hpx]
    · have hxpos : 0 < bp x x := lt_of_le_of_ne hpx (Ne.symm hx0)
      have hypos : 0 < bp y y := lt_of_le_of_ne hpy (Ne.symm hy0)
      let a : ℝ := Real.sqrt (bp x x)
      let b : ℝ := Real.sqrt (bp y y)
      let r : ℝ := Real.sqrt (bp y y / bp x x)
      have hapos : 0 < a := Real.sqrt_pos.mpr hxpos
      have hbpos : 0 < b := Real.sqrt_pos.mpr hypos
      have hrpos : 0 < r := Real.sqrt_pos.mpr (div_pos hypos hxpos)
      have hbasic := dominated_bilinear_abs_le_avg q T hTq hTsymm bp hdom (r • x) y
      simp [map_smul, abs_mul, abs_of_pos hrpos] at hbasic
      have hrsq : r ^ 2 * bp x x = bp y y := by
        dsimp [r]
        rw [Real.sq_sqrt (div_nonneg hpy hpx)]
        field_simp [ne_of_gt hxpos]
      have hscale : r * |T x y| ≤ bp y y := by
        nlinarith
      have hsqrtdiv : r = b / a := by
        dsimp [r, b, a]
        exact Real.sqrt_div hpy (bp x x)
      have hmul : a * r = b := by
        rw [hsqrtdiv]
        field_simp [ne_of_gt hapos]
      have hleft : b * |T x y| ≤ a * (b * b) := by
        have h := mul_le_mul_of_nonneg_left hscale (le_of_lt hapos)
        calc
          b * |T x y| = a * (r * |T x y|) := by
            conv_lhs => rw [← hmul]
            ring
          _ ≤ a * bp y y := h
          _ = a * (b * b) := by
            dsimp [b]
            rw [Real.mul_self_sqrt hpy]
      exact le_of_mul_le_mul_right (by
        calc
          |T x y| * b = b * |T x y| := mul_comm _ _
          _ ≤ a * (b * b) := hleft
          _ = (a * b) * b := by ring) hbpos

/- accepted add_to_file helper 4 -/
lemma dominated_implies_hilbert_factorization
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (q : X → ℝ)
    (T : X →L[ℝ] (X →L[ℝ] ℝ))
    (hTq : ∀ x : X, q x = T x x)
    (hTsymm : ∀ x y : X, T x y = T y x)
    (p : X → ℝ) (bp : X →L[ℝ] X →L[ℝ] ℝ)
    (hp : ∀ x : X, p x = bp x x)
    (hdomp : ∀ x : X, |q x| ≤ p x) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
        (_ : CompleteSpace H) (A : X →L[ℝ] H) (B : H →L[ℝ] (X →L[ℝ] ℝ)),
      T = B.comp A := by
  have hdom : ∀ x : X, |q x| ≤ bp x x := by
    intro x
    simpa [hp x] using hdomp x
  have hnonneg : ∀ x : X, 0 ≤ (bp x x + bp x x) / 2 := by
    intro x
    have hx : 0 ≤ bp x x := le_trans (abs_nonneg _) (hdom x)
    nlinarith
  let E := QuadraticPreHilbert X
  letI core : PreInnerProductSpace.Core ℝ E := QuadraticPreHilbert.preCore bp hnonneg
  letI semi : SeminormedAddCommGroup E :=
    InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜:=ℝ) (F:=E)
  letI ips : InnerProductSpace ℝ E := InnerProductSpace.ofCore core
  let toE : X →ₗ[ℝ] E := {
    toFun := QuadraticPreHilbert.mk
    map_add' := by intro x y; rfl
    map_smul' := by intro r x; rfl }
  have hbound : ∀ x : X, ‖toE x‖ ≤ Real.sqrt ‖bp‖ * ‖x‖ := by
    intro x
    have hnorm : ‖toE x‖ = Real.sqrt (bp x x) := by
      change ‖(QuadraticPreHilbert.mk x : QuadraticPreHilbert X)‖ = Real.sqrt (bp x x)
      have h : ‖(QuadraticPreHilbert.mk x : QuadraticPreHilbert X)‖ =
          Real.sqrt ((bp x x + bp x x) / 2) := rfl
      rw [h]
      ring_nf
    have habs : |bp x x| ≤ ‖bp x‖ * ‖x‖ := ContinuousLinearMap.le_opNorm (bp x) x
    have hbp : ‖bp x‖ ≤ ‖bp‖ * ‖x‖ := ContinuousLinearMap.le_opNorm bp x
    have hple : bp x x ≤ ‖bp‖ * (‖x‖ * ‖x‖) := by
      calc
        bp x x ≤ |bp x x| := le_abs_self _
        _ ≤ ‖bp x‖ * ‖x‖ := habs
        _ ≤ (‖bp‖ * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right hbp (norm_nonneg _)
        _ = ‖bp‖ * (‖x‖ * ‖x‖) := by ring
    calc
      ‖toE x‖ = Real.sqrt (bp x x) := hnorm
      _ ≤ Real.sqrt (‖bp‖ * (‖x‖ * ‖x‖)) := Real.sqrt_le_sqrt hple
      _ = Real.sqrt ‖bp‖ * ‖x‖ := by
        rw [Real.sqrt_mul (norm_nonneg bp) (‖x‖ * ‖x‖),
          Real.sqrt_mul_self (norm_nonneg x)]
  let A0 : X →L[ℝ] E := LinearMap.mkContinuous toE (Real.sqrt ‖bp‖) hbound
  let Tlin : E →ₗ[ℝ] (X →L[ℝ] ℝ) := {
    toFun := fun e => T e.val
    map_add' := by
      intro e f
      change T (e.val + f.val) = T e.val + T f.val
      exact map_add T e.val f.val
    map_smul' := by
      intro r e
      change T (r • e.val) = r • T e.val
      exact map_smul T r e.val }
  have hTbound : ∀ e : E, ‖Tlin e‖ ≤ Real.sqrt ‖bp‖ * ‖e‖ := by
    intro e
    have hpoint : ∀ y : X,
        ‖T e.val y‖ ≤ (Real.sqrt ‖bp‖ * Real.sqrt (bp e.val e.val)) * ‖y‖ := by
      intro y
      have hc := dominated_bilinear_abs_le_sqrt_mul q T hTq hTsymm bp hdom e.val y
      have hyb := hbound y
      have hnormy : ‖toE y‖ = Real.sqrt (bp y y) := by
        change ‖(QuadraticPreHilbert.mk y : QuadraticPreHilbert X)‖ =
          Real.sqrt (bp y y)
        have h : ‖(QuadraticPreHilbert.mk y : QuadraticPreHilbert X)‖ =
            Real.sqrt ((bp y y + bp y y) / 2) := rfl
        rw [h]
        ring_nf
      rw [hnormy] at hyb
      calc
        ‖T e.val y‖ = |T e.val y| := Real.norm_eq_abs _
        _ ≤ Real.sqrt (bp e.val e.val) * Real.sqrt (bp y y) := hc
        _ ≤ Real.sqrt (bp e.val e.val) * (Real.sqrt ‖bp‖ * ‖y‖) :=
          mul_le_mul_of_nonneg_left hyb (Real.sqrt_nonneg _)
        _ = (Real.sqrt ‖bp‖ * Real.sqrt (bp e.val e.val)) * ‖y‖ := by ring
    have hop := ContinuousLinearMap.opNorm_le_bound (T e.val)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hpoint
    have hnorme : ‖e‖ = Real.sqrt (bp e.val e.val) := by
      change ‖(QuadraticPreHilbert.mk e.val : QuadraticPreHilbert X)‖ =
        Real.sqrt (bp e.val e.val)
      have h : ‖(QuadraticPreHilbert.mk e.val : QuadraticPreHilbert X)‖ =
          Real.sqrt ((bp e.val e.val + bp e.val e.val) / 2) := rfl
      rw [h]
      ring_nf
    calc
      ‖Tlin e‖ ≤ Real.sqrt ‖bp‖ * Real.sqrt (bp e.val e.val) := hop
      _ = Real.sqrt ‖bp‖ * ‖e‖ := by rw [← hnorme]
  let Tpre : E →L[ℝ] (X →L[ℝ] ℝ) :=
    LinearMap.mkContinuous Tlin (Real.sqrt ‖bp‖) hTbound
  have hTpre_norm : ‖Tpre‖ ≤ Real.sqrt ‖bp‖ :=
    LinearMap.mkContinuous_norm_le Tlin (Real.sqrt_nonneg _) hTbound
  have hf : ∀ e f : E, Inseparable e f → Tpre e = Tpre f := by
    intro e f h
    have hnorm0 : ‖e - f‖ = 0 := by
      have hd := h.dist_eq_zero
      rwa [dist_eq_norm] at hd
    have hle : ‖Tpre e - Tpre f‖ ≤ 0 := by
      calc
        ‖Tpre e - Tpre f‖ = ‖Tpre (e - f)‖ := by simp
        _ ≤ ‖Tpre‖ * ‖e - f‖ := ContinuousLinearMap.le_opNorm Tpre (e-f)
        _ ≤ Real.sqrt ‖bp‖ * ‖e - f‖ :=
          mul_le_mul_of_nonneg_right hTpre_norm (norm_nonneg _)
        _ = 0 := by simp [hnorm0]
    exact eq_of_sub_eq_zero (norm_le_zero_iff.mp hle)
  let Tq : SeparationQuotient E →L[ℝ] (X →L[ℝ] ℝ) :=
    SeparationQuotient.liftCLM Tpre hf
  let Q := SeparationQuotient E
  let H := UniformSpace.Completion Q
  let eCompl : Q →L[ℝ] H := UniformSpace.Completion.toComplL
  have hdense : DenseRange eCompl := by
    change DenseRange (UniformSpace.Completion.toComplL (𝕜:=ℝ) (E:=Q))
    simpa [UniformSpace.Completion.coe_toComplL] using
      (UniformSpace.Completion.isDenseInducing_toCompl Q).dense
  have huniform : IsUniformInducing eCompl := by
    change IsUniformInducing (UniformSpace.Completion.toComplL (𝕜:=ℝ) (E:=Q))
    simpa [UniformSpace.Completion.coe_toComplL] using
      (UniformSpace.Completion.isUniformEmbedding_coe Q).isUniformInducing
  let mkQ : E →L[ℝ] Q := SeparationQuotient.mkCLM ℝ E
  let A : X →L[ℝ] H := eCompl.comp (mkQ.comp A0)
  let B : H →L[ℝ] (X →L[ℝ] ℝ) := Tq.extend eCompl
  refine ⟨H, inferInstance, inferInstance, inferInstance, A, B, ?_⟩
  ext x y
  change T x y = (B (A x)) y
  have hAx : A x = eCompl (mkQ (A0 x)) := rfl
  rw [hAx]
  have hB := ContinuousLinearMap.extend_eq Tq hdense huniform (mkQ (A0 x))
  rw [hB]
  have hmk : mkQ (A0 x) = SeparationQuotient.mk (A0 x) := by
    exact SeparationQuotient.mkCLM_apply ℝ E (A0 x)
  rw [hmk]
  change ((SeparationQuotient.liftCLM Tpre hf) (SeparationQuotient.mk (A0 x))) y =
    T x y
  rw [SeparationQuotient.liftCLM_mk]
  simp [Tpre, Tlin, A0, toE]

/- accepted add_to_file helper 5 -/
lemma hilbert_factorization_implies_dominated
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (q : X → ℝ)
    (T : X →L[ℝ] (X →L[ℝ] ℝ))
    (hTq : ∀ x : X, q x = T x x)
    (hfact : ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
        (_ : CompleteSpace H) (A : X →L[ℝ] H) (B : H →L[ℝ] (X →L[ℝ] ℝ)),
      T = B.comp A) :
    ∃ p : X → ℝ,
      (∃ bp : X →L[ℝ] X →L[ℝ] ℝ, ∀ x : X, p x = bp x x) ∧
      (∀ x : X, |q x| ≤ p x) := by
  rcases hfact with ⟨H, instH, instIH, instCH, A, B, hT⟩
  let RieszSymm : StrongDual ℝ H →L[ℝ] H :=
    ((InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv).toContinuousLinearMap
  let C : X →L[ℝ] H := RieszSymm.comp B.flip
  have hC : ∀ x y : X, B (A x) y = inner ℝ (C y) (A x) := by
    intro x y
    have h := InnerProductSpace.toDual_symm_apply (𝕜:=ℝ) (E:=H)
      (x:=A x) (y:=B.flip y)
    change B (A x) y = inner ℝ (RieszSymm (B.flip y)) (A x)
    exact h.symm
  let innerH : H →L[ℝ] H →L[ℝ] ℝ := innerSL ℝ
  let bp : X →L[ℝ] X →L[ℝ] ℝ :=
    (1/2 : ℝ) • (((innerH.comp A).flip.comp A) +
      ((innerH.comp C).flip.comp C))
  refine ⟨fun x => bp x x, ⟨bp, fun x => rfl⟩, ?_⟩
  intro x
  have hq : q x = inner ℝ (C x) (A x) := by
    rw [hTq, hT]
    exact hC x x
  have hnorm : |inner ℝ (C x) (A x)| ≤
      (‖A x‖ ^ 2 + ‖C x‖ ^ 2) / 2 := by
    calc
      |inner ℝ (C x) (A x)| ≤ ‖C x‖ * ‖A x‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖A x‖ ^ 2 + ‖C x‖ ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖C x‖ - ‖A x‖), norm_nonneg (C x), norm_nonneg (A x)]
  have hp : bp x x = (‖A x‖ ^ 2 + ‖C x‖ ^ 2) / 2 := by
    simp [bp]
    change 2⁻¹ * inner ℝ (A x) (A x) + 2⁻¹ * inner ℝ (C x) (C x) =
      (‖A x‖ ^ 2 + ‖C x‖ ^ 2) / 2
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  rw [hq]
  change |inner ℝ (C x) (A x)| ≤ bp x x
  rw [hp]
  exact hnorm

/- verified submission -/
theorem continuous_quadratic_form_delta_semidefinite_iff_hilbert_factorization
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (q : X → ℝ)
    (hq : ∃ b : X →L[ℝ] X →L[ℝ] ℝ, ∀ x : X, q x = b x x)
    (T : X →L[ℝ] (X →L[ℝ] ℝ))
    (hTq : ∀ x : X, q x = T x x)
    (hTsymm : ∀ x y : X, T x y = T y x) :
    ((∃ q₁ q₂ : X → ℝ,
        (∃ b₁ : X →L[ℝ] X →L[ℝ] ℝ, ∀ x : X, q₁ x = b₁ x x) ∧
        (∃ b₂ : X →L[ℝ] X →L[ℝ] ℝ, ∀ x : X, q₂ x = b₂ x x) ∧
        (∀ x : X, 0 ≤ q₁ x) ∧
        (∀ x : X, 0 ≤ q₂ x) ∧
        (∀ x : X, q x = q₁ x - q₂ x)) ↔
      (∃ p : X → ℝ,
        (∃ bp : X →L[ℝ] X →L[ℝ] ℝ, ∀ x : X, p x = bp x x) ∧
        (∀ x : X, |q x| ≤ p x))) ∧
    ((∃ p : X → ℝ,
        (∃ bp : X →L[ℝ] X →L[ℝ] ℝ, ∀ x : X, p x = bp x x) ∧
        (∀ x : X, |q x| ≤ p x)) ↔
      (∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
          (_ : CompleteSpace H) (A : X →L[ℝ] H) (B : H →L[ℝ] (X →L[ℝ] ℝ)),
        T = B.comp A)) := by
  constructor
  · constructor
    · rintro ⟨q₁, q₂, hq₁, hq₂, hq₁pos, hq₂pos, hqdiff⟩
      rcases hq₁ with ⟨b₁, hb₁⟩
      rcases hq₂ with ⟨b₂, hb₂⟩
      refine ⟨fun x => q₁ x + q₂ x, ?_, ?_⟩
      · refine ⟨b₁ + b₂, ?_⟩
        intro x
        simp [hb₁ x, hb₂ x]
      · intro x
        rw [hqdiff x]
        calc
          |q₁ x - q₂ x| ≤ |q₁ x| + |q₂ x| := abs_sub _ _
          _ = q₁ x + q₂ x := by
            rw [abs_of_nonneg (hq₁pos x), abs_of_nonneg (hq₂pos x)]
    · rintro ⟨p, hbp, hdom⟩
      rcases hbp with ⟨bp, hp⟩
      refine ⟨fun x => (p x + q x) / 2, fun x => (p x - q x) / 2, ?_, ?_, ?_, ?_, ?_⟩
      · refine ⟨(1/2 : ℝ) • (bp + T), ?_⟩
        intro x
        simp [hp x, hTq x]
        ring
      · refine ⟨(1/2 : ℝ) • (bp - T), ?_⟩
        intro x
        simp [hp x, hTq x]
        ring
      · intro x
        have hqabs := abs_le.mp (hdom x)
        nlinarith
      · intro x
        have hqabs := abs_le.mp (hdom x)
        nlinarith
      · intro x
        ring
  · constructor
    · rintro ⟨p, ⟨bp, hp⟩, hdom⟩
      exact dominated_implies_hilbert_factorization q T hTq hTsymm p bp hp hdom
    · intro hfact
      exact hilbert_factorization_implies_dominated q T hTq hfact
