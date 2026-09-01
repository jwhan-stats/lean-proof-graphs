import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1355_locallycontinuousmeasurableonecocycle_iff_
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: eab7bd635f5869034ed81523c6751d4339c777d86cff6e90df03171b19b7338b
-- reconstructed_proof_sha256: ae0d24f25696f54ce1167414a5110a3cff4a6684f0810477cd99beefaeed2e94
-- selected_edge_count: 1

/- verified submission -/
theorem locallyContinuousMeasurableOneCocycle_iff_continuousCrossedHomomorphism
    {G A : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [DistribMulAction G A] [ContinuousSMul G A]
    [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace A] [BorelSpace A]
    (c : G → A) :
    (Measurable c ∧
        (∀ s t : G, c (s * t) = c s + s • c t) ∧
        ∃ U : Set G, IsOpen U ∧ (1 : G) ∈ U ∧ ContinuousOn c U) ↔
      (Continuous c ∧ ∀ s t : G, c (s * t) = c s + s • c t) := by
  constructor
  · rintro ⟨hmeas, hcoc, U, hUopen, h1U, hcU⟩
    have hc1 : ContinuousAt c 1 := hcU.continuousAt (hUopen.mem_nhds h1U)
    have hcont : Continuous c := by
      rw [continuous_iff_continuousAt]
      intro g
      have hceq : c = fun x => c g + g • c (g⁻¹ * x) := by
        funext x
        calc
          c x = c (g * (g⁻¹ * x)) := by
            congr 1
            rw [← mul_assoc, mul_inv_cancel, one_mul]
          _ = c g + g • c (g⁻¹ * x) := hcoc g (g⁻¹ * x)
      rw [hceq]
      have hgx : ContinuousAt (fun x : G => g⁻¹ * x) g :=
        continuousAt_const.mul continuousAt_id
      have hc1g : ContinuousAt c (g⁻¹ * g) := by
        rw [inv_mul_cancel]
        exact hc1
      have hinner : ContinuousAt (fun x : G => c (g⁻¹ * x)) g :=
        ContinuousAt.comp hc1g hgx
      exact continuousAt_const.add (hinner.const_smul g)
    exact ⟨hcont, hcoc⟩
  · rintro ⟨hcont, hcoc⟩
    exact ⟨hcont.measurable, hcoc, Set.univ, isOpen_univ, Set.mem_univ 1, hcont.continuousOn⟩


#check_dependency_graph "locallyContinuousMeasurableOneCocycle_iff_continuousCrossedHomomorphism" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(Measurable c ∧ (∀ (s t : G), c (s * t) = c s + s • c t) ∧ ∃ U, IsOpen U ∧ 1 ∈ U ∧ ContinuousOn c U) ↔ Continuous c ∧ ∀ (s t : G), c (s * t) = c s + s • c t\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"IsTopologicalGroup G\"},{\"name\":\"<generated-instance>\",\"statement\":\"IsTopologicalAddGroup A\"},{\"name\":\"<generated-instance>\",\"statement\":\"ContinuousSMul G A\"},{\"name\":\"<generated-instance>\",\"statement\":\"BorelSpace G\"},{\"name\":\"<generated-instance>\",\"statement\":\"BorelSpace A\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1355_locallycontinuousmeasurableonecocycle_iff_\",\"reconstructedProofSha256\":\"ae0d24f25696f54ce1167414a5110a3cff4a6684f0810477cd99beefaeed2e94\",\"selectedEdgeCount\":1,\"theoremName\":\"locallyContinuousMeasurableOneCocycle_iff_continuousCrossedHomomorphism\",\"topologySha256\":\"eab7bd635f5869034ed81523c6751d4339c777d86cff6e90df03171b19b7338b\"}"
