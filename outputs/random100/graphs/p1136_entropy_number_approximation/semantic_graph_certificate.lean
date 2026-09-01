import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1136_entropy_number_approximation
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 35962ed6d9b2ce9c224f8534f09d23127dfd835d3adaae568e40c6c6429a2704
-- reconstructed_proof_sha256: 65dcbe87a8510bbfca50e611c2cc13a0477e85843aad392e6bca057408ee4ba1
-- selected_edge_count: 1

/- accepted add_to_file helper 1 -/
lemma exists_isCover_encard_le_of_externalCoveringNumber_le
    {Z : Type*} [PseudoEMetricSpace Z] {ε : NNReal} {A : Set Z} {m : ℕ}
    (h : Metric.externalCoveringNumber ε A ≤ (m : ℕ∞)) :
    ∃ C : Set Z, Metric.IsCover ε A C ∧ C.encard ≤ (m : ℕ∞) := by
  unfold Metric.externalCoveringNumber at h
  have hlt : (⨅ C : Set Z, ⨅ _ : Metric.IsCover ε A C, C.encard) < (m : ℕ∞) + 1 :=
    lt_of_le_of_lt h ((ENat.lt_add_one_iff (ENat.coe_ne_top m)).mpr le_rfl)
  rcases (iInf_lt_iff.mp hlt) with ⟨C, hC⟩
  rcases (iInf_lt_iff.mp hC) with ⟨hCcover, hCcard⟩
  exact ⟨C, hCcover, (ENat.lt_add_one_iff (ENat.coe_ne_top m)).mp hCcard⟩

/- accepted add_to_file helper 2 -/
lemma exists_covering_radius_lt_of_iInf_lt
    {Z W : Type*} [PseudoEMetricSpace Z] {A : Set Z} {m : ℕ} {r : ENNReal}
    (h : (⨅ (ε : NNReal), ⨅ (_ : 0 < ε),
      ⨅ (_ : Metric.externalCoveringNumber ε A ≤ (m : ℕ∞)), (ε : ENNReal)) < r) :
    ∃ ε : NNReal, 0 < ε ∧ Metric.externalCoveringNumber ε A ≤ (m : ℕ∞) ∧
      (ε : ENNReal) < r := by
  rcases (iInf_lt_iff.mp h) with ⟨ε, hε⟩
  rcases (iInf_lt_iff.mp hε) with ⟨hεpos, hεcover⟩
  rcases (iInf_lt_iff.mp hεcover) with ⟨hcover, hεlt⟩
  exact ⟨ε, hεpos, hcover, hεlt⟩

/- accepted add_to_file helper 3 -/
lemma iInf_covering_radius_le
    {Z : Type*} [PseudoEMetricSpace Z] {A : Set Z} {m : ℕ} {r : NNReal}
    (hr : 0 < r) (hc : Metric.externalCoveringNumber r A ≤ (m : ℕ∞)) :
    (⨅ (ε : NNReal), ⨅ (_ : 0 < ε),
      ⨅ (_ : Metric.externalCoveringNumber ε A ≤ (m : ℕ∞)), (ε : ENNReal)) ≤
      (r : ENNReal) := by
  exact iInf_le_of_le r (iInf_le_of_le hr (iInf_le_of_le hc le_rfl))

/- accepted add_to_file helper 4 -/
lemma card_mul_two_pow_pred_le_pow {c n : ℕ} (hn : 0 < n) :
    (c : ℕ∞) * (2 ^ (n - 1) : ℕ∞) ≤ (2 ^ (n + Nat.log 2 c) : ℕ∞) := by
  have hc : c ≤ 2 ^ (Nat.log 2 c + 1) :=
    Nat.le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) c)
  have hmul : c * 2 ^ (n - 1) ≤ 2 ^ (Nat.log 2 c + 1) * 2 ^ (n - 1) :=
    Nat.mul_le_mul_right _ hc
  have hpow : 2 ^ (Nat.log 2 c + 1) * 2 ^ (n - 1) = 2 ^ (n + Nat.log 2 c) := by
    rw [← pow_add]
    congr 1
    omega
  exact_mod_cast hmul.trans_eq hpow

/- accepted add_to_file helper 5 -/
lemma exists_covering_radius_lt_of_iInf_lt'
    {Z : Type*} [PseudoEMetricSpace Z] {A : Set Z} {m : ℕ} {r : ENNReal}
    (h : (⨅ (ε : NNReal), ⨅ (_ : 0 < ε),
      ⨅ (_ : Metric.externalCoveringNumber ε A ≤ (m : ℕ∞)), (ε : ENNReal)) < r) :
    ∃ ε : NNReal, 0 < ε ∧ Metric.externalCoveringNumber ε A ≤ (m : ℕ∞) ∧
      (ε : ENNReal) < r := by
  rcases (iInf_lt_iff.mp h) with ⟨ε, hε⟩
  rcases (iInf_lt_iff.mp hε) with ⟨hεpos, hεcover⟩
  rcases (iInf_lt_iff.mp hεcover) with ⟨hcover, hεlt⟩
  exact ⟨ε, hεpos, hcover, hεlt⟩

/- verified submission -/
theorem entropy_number_approximation
    (𝕜 : Type*) [RCLike 𝕜]
    (X Y : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (Γ : Type*) [Fintype Γ] [Nonempty Γ]
    (V : X →ₗ[𝕜] Y) (Vγ : Γ → X →ₗ[𝕜] Y)
    (n : ℕ) (hn : 0 < n) :
    let e : ℕ → (X →ₗ[𝕜] Y) → ENNReal := fun k T ↦
      ⨅ (ε : NNReal) (_ : 0 < ε)
        (_ : Metric.externalCoveringNumber ε (T '' Metric.closedBall (0 : X) 1) ≤
          2 ^ (k - 1)),
        (ε : ENNReal)
    e (n + Nat.log 2 (Fintype.card Γ) + 1) V ≤
      (⨆ γ : Γ, e n (Vγ γ)) +
        (⨆ (x : X) (_ : ‖x‖ ≤ 1),
          ⨅ γ : Γ, ENNReal.ofReal ‖V x - Vγ γ x‖) := by
  let e : ℕ → (X →ₗ[𝕜] Y) → ENNReal := fun k T ↦
    ⨅ (ε : NNReal) (_ : 0 < ε)
      (_ : Metric.externalCoveringNumber ε (T '' Metric.closedBall (0 : X) 1) ≤
        2 ^ (k - 1)),
      (ε : ENNReal)
  let A : ENNReal := ⨆ γ : Γ, e n (Vγ γ)
  let B : ENNReal := ⨆ (x : X) (_ : ‖x‖ ≤ 1),
    ⨅ γ : Γ, ENNReal.ofReal ‖V x - Vγ γ x‖
  change e (n + Nat.log 2 (Fintype.card Γ) + 1) V ≤ A + B
  by_cases htop : A + B = ⊤
  · rw [htop]
    exact le_top
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  by_cases hεtop : ε = ⊤
  · rw [hεtop]
    simp
  have hA : A ≠ ⊤ := by
    intro h
    apply htop
    rw [h]
    simp
  have hB : B ≠ ⊤ := by
    intro h
    apply htop
    rw [h]
    simp
  let η : ENNReal := ε / 2
  have hηpos : 0 < η := ENNReal.div_pos (ne_of_gt hε) (by norm_num)
  have hηne : η ≠ 0 := ne_of_gt hηpos
  have hrad : ∀ γ : Γ, ∃ r : NNReal, 0 < r ∧
      Metric.externalCoveringNumber r (Vγ γ '' Metric.closedBall (0 : X) 1) ≤
        ((2 ^ (n - 1) : ℕ) : ℕ∞) ∧
      (r : ENNReal) < A + η := by
    intro γ
    apply exists_covering_radius_lt_of_iInf_lt'
    have hle : e n (Vγ γ) ≤ A := by
      exact le_iSup (fun γ : Γ => e n (Vγ γ)) γ
    exact lt_of_le_of_lt hle (ENNReal.lt_add_right hA hηne)
  choose r hrpos hrcov hrlt using hrad
  have hcover : ∀ γ : Γ, ∃ C : Set Y,
      Metric.IsCover (r γ) (Vγ γ '' Metric.closedBall (0 : X) 1) C ∧
      C.encard ≤ ((2 ^ (n - 1) : ℕ) : ℕ∞) := by
    intro γ
    exact exists_isCover_encard_le_of_externalCoveringNumber_le (hrcov γ)
  choose C hCcover hCcard using hcover
  have htarget_top : A + B + ε ≠ ⊤ := by
    rw [ENNReal.add_ne_top]
    exact ⟨htop, hεtop⟩
  have htarget_zero : A + B + ε ≠ 0 := by
    intro h
    have hεzero : ε = 0 := (add_eq_zero.mp h).2
    exact (ne_of_gt hε) hεzero
  let R : NNReal := (A + B + ε).toNNReal
  have hRpos : 0 < R := ENNReal.toNNReal_pos htarget_zero htarget_top
  have hR_coe : (R : ENNReal) = A + B + ε := ENNReal.coe_toNNReal htarget_top
  have hVcover : Metric.IsCover R (V '' Metric.closedBall (0 : X) 1)
      (⋃ γ : Γ, C γ) := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hxnorm : ‖x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hb_le : (⨅ γ : Γ, ENNReal.ofReal ‖V x - Vγ γ x‖) ≤ B := by
      have hinner : (⨅ γ : Γ, ENNReal.ofReal ‖V x - Vγ γ x‖) ≤
          ⨆ (_ : ‖x‖ ≤ 1), ⨅ γ : Γ, ENNReal.ofReal ‖V x - Vγ γ x‖ := by
        exact le_iSup
          (fun _ : ‖x‖ ≤ 1 => ⨅ γ : Γ, ENNReal.ofReal ‖V x - Vγ γ x‖) hxnorm
      exact hinner.trans
        (le_iSup
          (fun x : X => ⨆ (_ : ‖x‖ ≤ 1),
            ⨅ γ : Γ, ENNReal.ofReal ‖V x - Vγ γ x‖) x)
    have hb_lt : (⨅ γ : Γ, ENNReal.ofReal ‖V x - Vγ γ x‖) < B + η :=
      lt_of_le_of_lt hb_le (ENNReal.lt_add_right hB hηne)
    rcases iInf_lt_iff.mp hb_lt with ⟨γ, hγ⟩
    have hyγ : Vγ γ x ∈ Vγ γ '' Metric.closedBall (0 : X) 1 := ⟨x, hx, rfl⟩
    rcases hCcover γ hyγ with ⟨z, hzC, hz⟩
    have happrox : edist (V x) (Vγ γ x) < B + η := by
      rw [edist_dist, dist_eq_norm]
      exact hγ
    have hsum : (B + η) + (A + η) = A + B + ε := by
      calc
        (B + η) + (A + η) = B + (η + (A + η)) := by rw [add_assoc]
        _ = B + (A + (η + η)) := by
          congr 1
          calc
            η + (A + η) = (η + A) + η := by rw [← add_assoc]
            _ = (A + η) + η := by rw [add_comm η A]
            _ = A + (η + η) := by rw [add_assoc]
        _ = B + A + (η + η) := by rw [← add_assoc]
        _ = A + B + (η + η) := by rw [add_comm B A]
        _ = A + B + ε := by rw [ENNReal.add_halves]
    have hzlt : edist (V x) z < (R : ENNReal) := by
      calc
        edist (V x) z ≤ edist (V x) (Vγ γ x) + edist (Vγ γ x) z :=
          edist_triangle _ _ _
        _ < (B + η) + (A + η) :=
          ENNReal.add_lt_add happrox (lt_of_le_of_lt hz (hrlt γ))
        _ = A + B + ε := hsum
        _ = (R : ENNReal) := hR_coe.symm
    exact ⟨z, Set.mem_iUnion.2 ⟨γ, hzC⟩, hzlt.le⟩
  have hCunion : (⋃ γ : Γ, C γ).encard ≤
      ((2 ^ (n + Nat.log 2 (Fintype.card Γ)) : ℕ) : ℕ∞) := by
    calc
      (⋃ γ : Γ, C γ).encard ≤ ∑ γ : Γ, (C γ).encard :=
        Set.encard_iUnion_le_of_fintype C
      _ ≤ Finset.univ.card • ((2 ^ (n - 1) : ℕ) : ℕ∞) := by
        exact Finset.sum_le_card_nsmul Finset.univ (fun γ : Γ => (C γ).encard)
          ((2 ^ (n - 1) : ℕ) : ℕ∞) (by intro γ _; exact hCcard γ)
      _ = (Fintype.card Γ : ℕ∞) * ((2 ^ (n - 1) : ℕ) : ℕ∞) := by
        rw [Finset.card_univ, nsmul_eq_mul]
      _ ≤ ((2 ^ (n + Nat.log 2 (Fintype.card Γ)) : ℕ) : ℕ∞) :=
        card_mul_two_pow_pred_le_pow hn
  have hnum : Metric.externalCoveringNumber R (V '' Metric.closedBall (0 : X) 1) ≤
      (2 ^ (n + Nat.log 2 (Fintype.card Γ) + 1 - 1) : ℕ∞) := by
    calc
      Metric.externalCoveringNumber R (V '' Metric.closedBall (0 : X) 1) ≤
          (⋃ γ : Γ, C γ).encard :=
        Metric.IsCover.externalCoveringNumber_le_encard hVcover
      _ ≤ ((2 ^ (n + Nat.log 2 (Fintype.card Γ)) : ℕ) : ℕ∞) := hCunion
      _ = (2 ^ (n + Nat.log 2 (Fintype.card Γ) + 1 - 1) : ℕ∞) := rfl
  calc
    e (n + Nat.log 2 (Fintype.card Γ) + 1) V ≤ (R : ENNReal) := by
      exact iInf_covering_radius_le hRpos hnum
    _ = A + B + ε := hR_coe


#check_dependency_graph "entropy_number_approximation" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let e := fun k T => ⨅ ε, ⨅ (_ : 0 < ε), ⨅ (_ : Metric.externalCoveringNumber ε (⇑T '' Metric.closedBall 0 1) ≤ 2 ^ (k - 1)), ↑ε; e (n + Nat.log 2 (Fintype.card Γ) + 1) V ≤ (⨆ γ, e n (Vγ γ)) + ⨆ x, ⨆ (_ : ‖x‖ ≤ 1), ⨅ γ, ENNReal.ofReal ‖V x - (Vγ γ) x‖\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hn\",\"statement\":\"0 < n\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1136_entropy_number_approximation\",\"reconstructedProofSha256\":\"65dcbe87a8510bbfca50e611c2cc13a0477e85843aad392e6bca057408ee4ba1\",\"selectedEdgeCount\":1,\"theoremName\":\"entropy_number_approximation\",\"topologySha256\":\"35962ed6d9b2ce9c224f8534f09d23127dfd835d3adaae568e40c6c6429a2704\"}"
