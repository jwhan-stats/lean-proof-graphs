import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p0390_linfty_eq_erosion_distance
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 7169e0ab7d33b8a0fb0a4a39cd644007ca5765397d525bbf754de2f861f69f8d
-- reconstructed_proof_sha256: deefde5b92869d0933b3be406052bb581b3cd1d21e4d80c11cfb23781d849cf0
-- selected_edge_count: 1

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


#check_dependency_graph "linfty_eq_erosion_distance" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"⨆ x, ENNReal.ofReal |f x - g x| = sInf {d | ∃ ε, d = ↑ε ∧ ∀ (a b : ℝ), a < b → g ⁻¹' Set.Icc a b ⊆ f ⁻¹' Set.Icc (a - ↑ε) (b + ↑ε) ∧ f ⁻¹' Set.Icc a b ⊆ g ⁻¹' Set.Icc (a - ↑ε) (b + ↑ε)}\"},\"graphEdgeId\":\"h_goal\",\"premises\":[],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0390_linfty_eq_erosion_distance\",\"reconstructedProofSha256\":\"deefde5b92869d0933b3be406052bb581b3cd1d21e4d80c11cfb23781d849cf0\",\"selectedEdgeCount\":1,\"theoremName\":\"linfty_eq_erosion_distance\",\"topologySha256\":\"7169e0ab7d33b8a0fb0a4a39cd644007ca5765397d525bbf754de2f861f69f8d\"}"
