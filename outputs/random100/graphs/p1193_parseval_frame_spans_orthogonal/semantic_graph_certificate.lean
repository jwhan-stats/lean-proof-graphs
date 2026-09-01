import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1193_parseval_frame_spans_orthogonal
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 186c22b947cae8b637db1e4cb4152e1e644df8cfea430cf772137e20a4e64fdf
-- reconstructed_proof_sha256: d37f0247e5dd6f81da3dc490b1a5f73d6adc9f4ddf7a0ebc57ff5cd57ca54d4d
-- selected_edge_count: 10

/- accepted add_to_file helper 1 -/
lemma rankOneInner_isSymmetric {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] (a : E) :
    (((innerₗ E) a).smulRight a).IsSymmetric := by
  intro x y
  simp [LinearMap.smulRight_apply, innerₗ_apply_apply,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm x a]
  exact mul_comm (inner ℝ x a) (inner ℝ a y)

noncomputable def partialFrame {M N : ℕ}
    (φ : Fin N → EuclideanSpace ℝ (Fin M)) (J : Set (Fin N)) :
    EuclideanSpace ℝ (Fin M) →ₗ[ℝ] EuclideanSpace ℝ (Fin M) := by
  classical
  exact ∑ i ∈ Finset.univ.filter (fun i => i ∈ J),
    (((innerₗ (EuclideanSpace ℝ (Fin M))) (φ i)).smulRight (φ i))

/- accepted add_to_file helper 2 -/
lemma partialFrame_isSymmetric {M N : ℕ}
    (φ : Fin N → EuclideanSpace ℝ (Fin M)) (J : Set (Fin N)) :
    (partialFrame φ J).IsSymmetric := by
  classical
  unfold partialFrame
  apply LinearMap.isSymmetric_sum
  intro i hi
  exact rankOneInner_isSymmetric (φ i)

/- accepted add_to_file helper 3 -/
lemma partialFrame_mem_span {M N : ℕ}
    (φ : Fin N → EuclideanSpace ℝ (Fin M)) (J : Set (Fin N))
    (x : EuclideanSpace ℝ (Fin M)) :
    partialFrame φ J x ∈ Submodule.span ℝ (φ '' J) := by
  classical
  unfold partialFrame
  simp
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨i, by simpa using hi, rfl⟩

/- accepted add_to_file helper 4 -/
lemma symmetric_eq_id_of_inner_map_self {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (T : E →ₗ[ℝ] E)
    (hT : T.IsSymmetric)
    (hdiag : ∀ x : E, inner ℝ (T x) x = inner ℝ x x) :
    T = LinearMap.id := by
  let R : E →ₗ[ℝ] E := T - LinearMap.id
  have hsymm : R.IsSymmetric := hT.sub LinearMap.IsSymmetric.id
  have hdiagR : ∀ z : E, inner ℝ (R z) z = 0 := by
    intro z
    simp only [R, LinearMap.sub_apply, LinearMap.id_apply]
    rw [inner_sub_left, hdiag z, sub_self]
  have hbilin : ∀ x y : E, inner ℝ (R x) y = 0 := by
    intro x y
    have hp := hsymm.inner_map_polarization x y
    rw [hdiagR (x + y), hdiagR (x - y)] at hp
    simpa using hp
  ext x
  have hzero : inner ℝ (R x) (R x) = 0 := hbilin x (R x)
  have hRx : R x = 0 := (inner_self_eq_zero (𝕜 := ℝ) (x := R x)).mp hzero
  have : T x - x = 0 := by
    simpa [R] using hRx
  exact sub_eq_zero.mp this

/- accepted add_to_file helper 5 -/
lemma partialFrame_univ_eq_id_of_parseval {M N : ℕ}
    (φ : Fin N → EuclideanSpace ℝ (Fin M))
    (hParseval : ∀ x : EuclideanSpace ℝ (Fin M),
      (∑ i : Fin N, (inner ℝ x (φ i)) ^ 2) = ‖x‖ ^ 2) :
    partialFrame φ Set.univ = LinearMap.id := by
  classical
  apply symmetric_eq_id_of_inner_map_self
  · exact partialFrame_isSymmetric φ Set.univ
  · intro x
    calc
      inner ℝ (partialFrame φ Set.univ x) x
          = ∑ i : Fin N, (inner ℝ x (φ i)) ^ 2 := by
            unfold partialFrame
            simp [innerₗ_apply_apply, real_inner_comm]
            rw [inner_sum]
            apply Finset.sum_congr rfl
            intro i hi
            rw [real_inner_smul_right]
            ring
      _ = ‖x‖ ^ 2 := hParseval x
      _ = inner ℝ x x := by rw [real_inner_self_eq_norm_sq]

/- accepted add_to_file helper 6 -/
lemma partialFrame_add_compl {M N : ℕ}
    (φ : Fin N → EuclideanSpace ℝ (Fin M)) (J : Set (Fin N)) :
    partialFrame φ J + partialFrame φ Jᶜ = partialFrame φ Set.univ := by
  classical
  ext x
  simp [partialFrame, Finset.sum_filter_add_sum_filter_not]

/- verified submission -/
theorem parseval_frame_spans_orthogonal
    (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (φ : Fin N → EuclideanSpace ℝ (Fin M))
    (hParseval : ∀ x : EuclideanSpace ℝ (Fin M),
      (∑ i : Fin N, (inner ℝ x (φ i)) ^ 2) = ‖x‖ ^ 2)
    (I : Set (Fin N))
    (hdisjoint : Submodule.span ℝ (φ '' I) ⊓
      Submodule.span ℝ (φ '' Iᶜ) = ⊥) :
    ∀ u ∈ Submodule.span ℝ (φ '' I),
      ∀ v ∈ Submodule.span ℝ (φ '' Iᶜ), inner ℝ u v = 0 := by
  classical
  let E := EuclideanSpace ℝ (Fin M)
  let A : Submodule ℝ E := Submodule.span ℝ (φ '' I)
  let B : Submodule ℝ E := Submodule.span ℝ (φ '' Iᶜ)
  let SI : E →ₗ[ℝ] E := partialFrame φ I
  let SC : E →ₗ[ℝ] E := partialFrame φ Iᶜ
  have hframe : partialFrame φ Set.univ = LinearMap.id :=
    partialFrame_univ_eq_id_of_parseval φ hParseval
  have hdecomp : ∀ x : E, SI x + SC x = x := by
    intro x
    have happ := congrArg (fun T : E →ₗ[ℝ] E => T x)
      (partialFrame_add_compl φ I)
    rw [hframe] at happ
    simpa [SI, SC] using happ
  have hSI_zero_on_B : ∀ v ∈ B, SI v = 0 := by
    intro v hv
    have hSIv_A : SI v ∈ A := by
      simpa [SI, A, E] using partialFrame_mem_span φ I v
    have hSCv_B : SC v ∈ B := by
      simpa [SC, B, E] using partialFrame_mem_span φ Iᶜ v
    have hSIv_B : SI v ∈ B := by
      have hEq : SI v = v - SC v := eq_sub_of_add_eq (hdecomp v)
      rw [hEq]
      exact B.sub_mem hv hSCv_B
    have hbot : SI v ∈ (⊥ : Submodule ℝ E) := by
      rw [← hdisjoint]
      change SI v ∈ A ⊓ B
      exact ⟨hSIv_A, hSIv_B⟩
    exact (Submodule.mem_bot ℝ).mp hbot
  intro u hu v hv
  have hSIu_A : SI u ∈ A := by
    simpa [SI, A, E] using partialFrame_mem_span φ I u
  have hSCu_B : SC u ∈ B := by
    simpa [SC, B, E] using partialFrame_mem_span φ Iᶜ u
  have hSCu_A : SC u ∈ A := by
    have hEq : SC u = u - SI u := eq_sub_of_add_eq' (hdecomp u)
    rw [hEq]
    exact A.sub_mem hu hSIu_A
  have hSCu_zero : SC u = 0 := by
    have hbot : SC u ∈ (⊥ : Submodule ℝ E) := by
      rw [← hdisjoint]
      change SC u ∈ A ⊓ B
      exact ⟨hSCu_A, hSCu_B⟩
    exact (Submodule.mem_bot ℝ).mp hbot
  have hSIu : SI u = u := by
    have h := hdecomp u
    rw [hSCu_zero, add_zero] at h
    exact h
  have hSIv : SI v = 0 := hSI_zero_on_B v hv
  calc
    inner ℝ u v = inner ℝ (SI u) v := by rw [hSIu]
    _ = inner ℝ u (SI v) := partialFrame_isSymmetric φ I u v
    _ = inner ℝ u 0 := by rw [hSIv]
    _ = 0 := by rw [inner_zero_right]


#check_dependency_graph "parseval_frame_spans_orthogonal" against "{\"edges\":[{\"conclusion\":{\"name\":\"hframe\",\"statement\":\"Rollout_p1193_parseval_frame_spans_orthogonal.partialFrame φ Set.univ = LinearMap.id\"},\"graphEdgeId\":\"h_001_hframe\",\"premises\":[{\"name\":\"hParseval\",\"statement\":\"∀ (x : EuclideanSpace ℝ (Fin M)), ∑ i, inner ℝ x (φ i) ^ 2 = ‖x‖ ^ 2\"}],\"rawEdgeId\":\"telescope_13\"},{\"conclusion\":{\"name\":\"hSIu_A\",\"statement\":\"SI u ∈ A\"},\"graphEdgeId\":\"h_004_hsiu_a\",\"premises\":[],\"rawEdgeId\":\"telescope_20\"},{\"conclusion\":{\"name\":\"hSCu_B\",\"statement\":\"SC u ∈ B\"},\"graphEdgeId\":\"h_005_hscu_b\",\"premises\":[],\"rawEdgeId\":\"telescope_21\"},{\"conclusion\":{\"name\":\"hdecomp\",\"statement\":\"∀ (x : E), SI x + SC x = x\"},\"graphEdgeId\":\"h_002_hdecomp\",\"premises\":[{\"name\":\"hframe\",\"statement\":\"Rollout_p1193_parseval_frame_spans_orthogonal.partialFrame φ Set.univ = LinearMap.id\"}],\"rawEdgeId\":\"telescope_14\"},{\"conclusion\":{\"name\":\"hSI_zero_on_B\",\"statement\":\"∀ v ∈ B, SI v = 0\"},\"graphEdgeId\":\"h_003_hsi_zero_on_b\",\"premises\":[{\"name\":\"hdisjoint\",\"statement\":\"Submodule.span ℝ (φ '' I) ⊓ Submodule.span ℝ (φ '' Iᶜ) = ⊥\"},{\"name\":\"hdecomp\",\"statement\":\"∀ (x : E), SI x + SC x = x\"}],\"rawEdgeId\":\"telescope_15\"},{\"conclusion\":{\"name\":\"hSCu_A\",\"statement\":\"SC u ∈ A\"},\"graphEdgeId\":\"h_006_hscu_a\",\"premises\":[{\"name\":\"hdecomp\",\"statement\":\"∀ (x : E), SI x + SC x = x\"},{\"name\":\"hu\",\"statement\":\"u ∈ Submodule.span ℝ (φ '' I)\"},{\"name\":\"hSIu_A\",\"statement\":\"SI u ∈ A\"}],\"rawEdgeId\":\"telescope_22\"},{\"conclusion\":{\"name\":\"hSCu_zero\",\"statement\":\"SC u = 0\"},\"graphEdgeId\":\"h_007_hscu_zero\",\"premises\":[{\"name\":\"hdisjoint\",\"statement\":\"Submodule.span ℝ (φ '' I) ⊓ Submodule.span ℝ (φ '' Iᶜ) = ⊥\"},{\"name\":\"hSCu_B\",\"statement\":\"SC u ∈ B\"},{\"name\":\"hSCu_A\",\"statement\":\"SC u ∈ A\"}],\"rawEdgeId\":\"telescope_23\"},{\"conclusion\":{\"name\":\"hSIv\",\"statement\":\"SI v = 0\"},\"graphEdgeId\":\"h_009_hsiv\",\"premises\":[{\"name\":\"hSI_zero_on_B\",\"statement\":\"∀ v ∈ B, SI v = 0\"},{\"name\":\"hv\",\"statement\":\"v ∈ Submodule.span ℝ (φ '' Iᶜ)\"}],\"rawEdgeId\":\"telescope_25\"},{\"conclusion\":{\"name\":\"hSIu\",\"statement\":\"SI u = u\"},\"graphEdgeId\":\"h_008_hsiu\",\"premises\":[{\"name\":\"hdecomp\",\"statement\":\"∀ (x : E), SI x + SC x = x\"},{\"name\":\"hSCu_zero\",\"statement\":\"SC u = 0\"}],\"rawEdgeId\":\"telescope_24\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"inner ℝ u v = 0\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hSIu\",\"statement\":\"SI u = u\"},{\"name\":\"hSIv\",\"statement\":\"SI v = 0\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1193_parseval_frame_spans_orthogonal\",\"reconstructedProofSha256\":\"d37f0247e5dd6f81da3dc490b1a5f73d6adc9f4ddf7a0ebc57ff5cd57ca54d4d\",\"selectedEdgeCount\":10,\"theoremName\":\"parseval_frame_spans_orthogonal\",\"topologySha256\":\"186c22b947cae8b637db1e4cb4152e1e644df8cfea430cf772137e20a4e64fdf\"}"
