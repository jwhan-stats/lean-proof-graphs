import Mathlib

/- accepted add_to_file helper 1 -/
lemma erosion_iff_pointwise {X : Type*} (f g : X → ℝ) (ε : NNReal) :
    (∀ a b : ℝ, a < b →
      g ⁻¹' Set.Icc a b ⊆ f ⁻¹' Set.Icc (a - (ε : ℝ)) (b + (ε : ℝ)) ∧
      f ⁻¹' Set.Icc a b ⊆ g ⁻¹' Set.Icc (a - (ε : ℝ)) (b + (ε : ℝ))) ↔
    ∀ x : X, |f x - g x| ≤ (ε : ℝ) := by
  constructor
  · intro h x
    apply le_of_forall_pos_le_add
    intro δ hδ
    have hg : x ∈ g ⁻¹' Set.Icc (g x - δ) (g x + δ) := by
      constructor <;> linarith
    have hf := ((h (g x - δ) (g x + δ) (by linarith)).1 hg)
    rw [abs_le]
    constructor <;> linarith [hf.1, hf.2]
  · intro h a b hab
    constructor
    · intro x hx
      have hfg := (abs_sub_le_iff.mp (h x))
      constructor <;> linarith [hx.1, hx.2, hfg.1, hfg.2]
    · intro x hx
      have hfg := (abs_sub_le_iff.mp (h x))
      constructor <;> linarith [hx.1, hx.2, hfg.1, hfg.2]

/- verified submission -/
theorem linfty_eq_erosion_distance {X : Type*} (f g : X → ℝ) :
    (⨆ x : X, ENNReal.ofReal |f x - g x|) =
      sInf {d : ENNReal | ∃ ε : NNReal,
        d = (ε : ENNReal) ∧
        ∀ a b : ℝ, a < b →
          g ⁻¹' Set.Icc a b ⊆
              f ⁻¹' Set.Icc (a - (ε : ℝ)) (b + (ε : ℝ)) ∧
          f ⁻¹' Set.Icc a b ⊆
              g ⁻¹' Set.Icc (a - (ε : ℝ)) (b + (ε : ℝ)) } := by
  let L : ENNReal := ⨆ x : X, ENNReal.ofReal |f x - g x|
  let D : Set ENNReal := {d : ENNReal | ∃ ε : NNReal,
        d = (ε : ENNReal) ∧
        ∀ a b : ℝ, a < b →
          g ⁻¹' Set.Icc a b ⊆
              f ⁻¹' Set.Icc (a - (ε : ℝ)) (b + (ε : ℝ)) ∧
          f ⁻¹' Set.Icc a b ⊆
              g ⁻¹' Set.Icc (a - (ε : ℝ)) (b + (ε : ℝ)) }
  change L = sInf D
  apply le_antisymm
  · apply le_sInf
    intro d hd
    rcases hd with ⟨ε, rfl, hE⟩
    apply iSup_le
    intro x
    have hx : |f x - g x| ≤ (ε : ℝ) :=
      (erosion_iff_pointwise f g ε).mp hE x
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hx
  · by_cases hL : L = ⊤
    · rw [hL]
      exact le_top
    · apply sInf_le
      refine ⟨L.toNNReal, (ENNReal.coe_toNNReal hL).symm, ?_⟩
      apply (erosion_iff_pointwise f g L.toNNReal).mpr
      intro x
      have hxE : ENNReal.ofReal |f x - g x| ≤ (L.toNNReal : ENNReal) := by
        rw [ENNReal.coe_toNNReal hL]
        exact le_iSup (fun x : X => ENNReal.ofReal |f x - g x|) x
      exact (ENNReal.ofReal_le_coe.mp hxE)
