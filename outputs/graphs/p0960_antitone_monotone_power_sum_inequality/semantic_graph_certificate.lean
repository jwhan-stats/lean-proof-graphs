import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p0960_antitone_monotone_power_sum_inequality
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: e4cd917d0aebd07d32c97b0a51e0e5210516236764cf68793d96a95ef4c7844f
-- reconstructed_proof_sha256: 571ab4248c4ae6b0931865d1da9639561fffc74480b2bc19df7cf281c6bbb8c7
-- selected_edge_count: 10

/- accepted add_to_file helper 1 -/
lemma antitone_monotone_power_sum_pair_nonneg
    {x y u v : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) (hu : 0 ≤ u) (huv : u ≤ v)
    {s : ℝ} (hs : 1 ≤ s) :
    0 ≤ x ^ (s + 1) * (y * v) + y ^ (s + 1) * (x * u) -
        x ^ s * (y ^ 2 * v) - y ^ s * (x ^ 2 * u) := by
  rcases eq_or_lt_of_le hy with rfl | hypos
  · have hs0 : s ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hs)
    have hs10 : s + 1 ≠ 0 := by positivity
    simp [Real.zero_rpow hs0, Real.zero_rpow hs10]
  · have hxpos : 0 < x := lt_of_lt_of_le hypos hxy
    have hx : 0 ≤ x := le_of_lt hxpos
    have hs1 : s - 1 + 1 = s := by ring
    have hxsp : x ^ (s + 1) = x ^ s * x := Real.rpow_add_one (ne_of_gt hxpos) s
    have hysp : y ^ (s + 1) = y ^ s * y := Real.rpow_add_one (ne_of_gt hypos) s
    have hxs : x ^ s = x * x ^ (s - 1) := by
      calc
        x ^ s = x ^ (s - 1 + 1) := by rw [hs1]
        _ = x ^ (s - 1) * x := Real.rpow_add_one (ne_of_gt hxpos) (s - 1)
        _ = x * x ^ (s - 1) := by ring
    have hys : y ^ s = y * y ^ (s - 1) := by
      calc
        y ^ s = y ^ (s - 1 + 1) := by rw [hs1]
        _ = y ^ (s - 1) * y := Real.rpow_add_one (ne_of_gt hypos) (s - 1)
        _ = y * y ^ (s - 1) := by ring
    have hfactor :
        x ^ (s + 1) * (y * v) + y ^ (s + 1) * (x * u) -
            x ^ s * (y ^ 2 * v) - y ^ s * (x ^ 2 * u)
          = x * y * (x - y) * (v * x ^ (s - 1) - u * y ^ (s - 1)) := by
      rw [hxsp, hysp, hxs, hys]
      ring
    rw [hfactor]
    have hxydiff : 0 ≤ x - y := sub_nonneg.mpr hxy
    have hsexp : 0 ≤ s - 1 := sub_nonneg.mpr hs
    have hpow : y ^ (s - 1) ≤ x ^ (s - 1) := Real.rpow_le_rpow hy hxy hsexp
    have hpownonneg : 0 ≤ y ^ (s - 1) := Real.rpow_nonneg hy (s - 1)
    have hv : 0 ≤ v := le_trans hu huv
    have hweighted : u * y ^ (s - 1) ≤ v * x ^ (s - 1) :=
      mul_le_mul huv hpow hpownonneg hv
    have hdiff : 0 ≤ v * x ^ (s - 1) - u * y ^ (s - 1) := sub_nonneg.mpr hweighted
    exact mul_nonneg (mul_nonneg (mul_nonneg hx hy) hxydiff) hdiff

/- verified submission -/
theorem antitone_monotone_power_sum_inequality
    (k : ℕ) (hk : 0 < k)
    (s : ℝ) (hs : 1 ≤ s)
    (a b : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, 0 ≤ b i)
    (ha_antitone : Antitone a)
    (hb_monotone : Monotone b) :
    (∑ i : Fin k, Real.rpow (a i) s) * (∑ i : Fin k, (a i) ^ 2 * b i) ≤
      (∑ i : Fin k, Real.rpow (a i) (s + 1)) * (∑ i : Fin k, a i * b i) := by
  let A : ℝ := ∑ i : Fin k, (a i) ^ s
  let B : ℝ := ∑ i : Fin k, (a i) ^ 2 * b i
  let C : ℝ := ∑ i : Fin k, (a i) ^ (s + 1)
  let D : ℝ := ∑ i : Fin k, a i * b i
  let U : Fin k → Fin k → ℝ := fun i j => (a i) ^ (s + 1) * (a j * b j)
  let V : Fin k → Fin k → ℝ := fun i j => (a i) ^ s * ((a j) ^ 2 * b j)
  let W : Fin k → Fin k → ℝ := fun i j => U i j + U j i - V i j - V j i
  have hWnonneg : ∀ i j : Fin k, 0 ≤ W i j := by
    intro i j
    rcases le_total i j with hij | hji
    · exact antitone_monotone_power_sum_pair_nonneg
        (hy := ha j) (hxy := ha_antitone hij) (hu := hb i)
        (huv := hb_monotone hij) hs
    · have hswap := antitone_monotone_power_sum_pair_nonneg
        (hy := ha i) (hxy := ha_antitone hji) (hu := hb j)
        (huv := hb_monotone hji) hs
      dsimp [W, U, V]
      convert hswap using 1
      ring
  have hsumW : 0 ≤ ∑ i : Fin k, ∑ j : Fin k, W i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hWnonneg i j
  have hU : (∑ i : Fin k, ∑ j : Fin k, U i j) = C * D := by
    simpa [U, C, D] using
      (Fintype.sum_mul_sum (fun i : Fin k => (a i) ^ (s + 1))
        (fun j : Fin k => a j * b j)).symm
  have hUs : (∑ i : Fin k, ∑ j : Fin k, U j i) = C * D := by
    calc
      (∑ i : Fin k, ∑ j : Fin k, U j i)
          = ∑ j : Fin k, ∑ i : Fin k, U j i := Finset.sum_comm
      _ = C * D := hU
  have hV : (∑ i : Fin k, ∑ j : Fin k, V i j) = A * B := by
    simpa [V, A, B] using
      (Fintype.sum_mul_sum (fun i : Fin k => (a i) ^ s)
        (fun j : Fin k => (a j) ^ 2 * b j)).symm
  have hVs : (∑ i : Fin k, ∑ j : Fin k, V j i) = A * B := by
    calc
      (∑ i : Fin k, ∑ j : Fin k, V j i)
          = ∑ j : Fin k, ∑ i : Fin k, V j i := Finset.sum_comm
      _ = A * B := hV
  have hsumEq : (∑ i : Fin k, ∑ j : Fin k, W i j) = 2 * (C * D - A * B) := by
    calc
      (∑ i : Fin k, ∑ j : Fin k, W i j)
          = (∑ i : Fin k, ∑ j : Fin k, U i j) +
              (∑ i : Fin k, ∑ j : Fin k, U j i) -
              (∑ i : Fin k, ∑ j : Fin k, V i j) -
              (∑ i : Fin k, ∑ j : Fin k, V j i) := by
            simp [W, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = 2 * (C * D - A * B) := by
            rw [hU, hUs, hV, hVs]
            ring
  have hdiff : 0 ≤ C * D - A * B := by
    nlinarith
  have hle : A * B ≤ C * D := sub_nonneg.mp hdiff
  simpa [A, B, C, D] using hle


#check_dependency_graph "antitone_monotone_power_sum_inequality" against "{\"edges\":[{\"conclusion\":{\"name\":\"hWnonneg\",\"statement\":\"∀ (i j : Fin k), 0 ≤ W i j\"},\"graphEdgeId\":\"h_001_hwnonneg\",\"premises\":[{\"name\":\"hs\",\"statement\":\"1 ≤ s\"},{\"name\":\"ha\",\"statement\":\"∀ (i : Fin k), 0 ≤ a i\"},{\"name\":\"hb\",\"statement\":\"∀ (i : Fin k), 0 ≤ b i\"},{\"name\":\"ha_antitone\",\"statement\":\"Antitone a\"},{\"name\":\"hb_monotone\",\"statement\":\"Monotone b\"}],\"rawEdgeId\":\"telescope_17\"},{\"conclusion\":{\"name\":\"hU\",\"statement\":\"∑ i, ∑ j, U i j = C * D\"},\"graphEdgeId\":\"h_003_hu\",\"premises\":[],\"rawEdgeId\":\"telescope_19\"},{\"conclusion\":{\"name\":\"hV\",\"statement\":\"∑ i, ∑ j, V i j = A * B\"},\"graphEdgeId\":\"h_005_hv\",\"premises\":[],\"rawEdgeId\":\"telescope_21\"},{\"conclusion\":{\"name\":\"hsumW\",\"statement\":\"0 ≤ ∑ i, ∑ j, W i j\"},\"graphEdgeId\":\"h_002_hsumw\",\"premises\":[{\"name\":\"hWnonneg\",\"statement\":\"∀ (i j : Fin k), 0 ≤ W i j\"}],\"rawEdgeId\":\"telescope_18\"},{\"conclusion\":{\"name\":\"hUs\",\"statement\":\"∑ i, ∑ j, U j i = C * D\"},\"graphEdgeId\":\"h_004_hus\",\"premises\":[{\"name\":\"hU\",\"statement\":\"∑ i, ∑ j, U i j = C * D\"}],\"rawEdgeId\":\"telescope_20\"},{\"conclusion\":{\"name\":\"hVs\",\"statement\":\"∑ i, ∑ j, V j i = A * B\"},\"graphEdgeId\":\"h_006_hvs\",\"premises\":[{\"name\":\"hV\",\"statement\":\"∑ i, ∑ j, V i j = A * B\"}],\"rawEdgeId\":\"telescope_22\"},{\"conclusion\":{\"name\":\"hsumEq\",\"statement\":\"∑ i, ∑ j, W i j = 2 * (C * D - A * B)\"},\"graphEdgeId\":\"h_007_hsumeq\",\"premises\":[{\"name\":\"hU\",\"statement\":\"∑ i, ∑ j, U i j = C * D\"},{\"name\":\"hUs\",\"statement\":\"∑ i, ∑ j, U j i = C * D\"},{\"name\":\"hV\",\"statement\":\"∑ i, ∑ j, V i j = A * B\"},{\"name\":\"hVs\",\"statement\":\"∑ i, ∑ j, V j i = A * B\"}],\"rawEdgeId\":\"telescope_23\"},{\"conclusion\":{\"name\":\"hdiff\",\"statement\":\"0 ≤ C * D - A * B\"},\"graphEdgeId\":\"h_008_hdiff\",\"premises\":[{\"name\":\"hsumW\",\"statement\":\"0 ≤ ∑ i, ∑ j, W i j\"},{\"name\":\"hsumEq\",\"statement\":\"∑ i, ∑ j, W i j = 2 * (C * D - A * B)\"}],\"rawEdgeId\":\"telescope_24\"},{\"conclusion\":{\"name\":\"hle\",\"statement\":\"A * B ≤ C * D\"},\"graphEdgeId\":\"h_009_hle\",\"premises\":[{\"name\":\"hdiff\",\"statement\":\"0 ≤ C * D - A * B\"}],\"rawEdgeId\":\"telescope_25\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(∑ i, (a i).rpow s) * ∑ i, a i ^ 2 * b i ≤ (∑ i, (a i).rpow (s + 1)) * ∑ i, a i * b i\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hle\",\"statement\":\"A * B ≤ C * D\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0960_antitone_monotone_power_sum_inequality\",\"reconstructedProofSha256\":\"571ab4248c4ae6b0931865d1da9639561fffc74480b2bc19df7cf281c6bbb8c7\",\"selectedEdgeCount\":10,\"theoremName\":\"antitone_monotone_power_sum_inequality\",\"topologySha256\":\"e4cd917d0aebd07d32c97b0a51e0e5210516236764cf68793d96a95ef4c7844f\"}"
