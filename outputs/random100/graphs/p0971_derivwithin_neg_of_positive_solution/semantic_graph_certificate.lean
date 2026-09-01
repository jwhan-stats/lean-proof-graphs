import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p0971_derivwithin_neg_of_positive_solution
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 253a8736d821304a70bd1dc324f603e5e16229c1ee25c0de4161930c7617de03
-- reconstructed_proof_sha256: 2cbeb4b491b5982f77e7c068f9d677e932ef9c1cb0b9222481bd34e0cf1ff4ce
-- selected_edge_count: 16

/- accepted add_to_file helper 1 -/
lemma signed_ppower_neg_iff (p s : ℝ) :
    (if s = 0 then 0 else Real.rpow |s| (p - 2) * s) < 0 ↔ s < 0 := by
  by_cases hs : s = 0
  · simp [hs]
  · have habs : 0 < |s| := abs_pos.mpr hs
    have hr : 0 < Real.rpow |s| (p - 2) := Real.rpow_pos_of_pos habs _
    simp [hs]
    constructor
    · intro h
      have hmul := mul_neg_iff.mp h
      rcases hmul with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
      · exact hright
      · exact False.elim ((not_lt_of_ge hr.le) hleft)
    · intro h
      exact mul_neg_of_pos_of_neg hr h

lemma signed_ppower_pos_iff (p s : ℝ) :
    0 < (if s = 0 then 0 else Real.rpow |s| (p - 2) * s) ↔ 0 < s := by
  by_cases hs : s = 0
  · simp [hs]
  · have habs : 0 < |s| := abs_pos.mpr hs
    have hr : 0 < Real.rpow |s| (p - 2) := Real.rpow_pos_of_pos habs _
    simp [hs]
    constructor
    · intro h
      have hmul := mul_pos_iff.mp h
      rcases hmul with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
      · exact hright
      · exact False.elim ((not_lt_of_ge hr.le) hleft)
    · intro h
      exact mul_pos hr h

/- verified submission -/
theorem derivWithin_neg_of_positive_solution
    (n : ℕ) (β p lam : ℝ) (f T : ℝ → ℝ)
    (hn : 2 ≤ n) (hβ : 0 < β) (hp : 1 < p) (hlam : 0 < lam)
    (hf : ContDiffOn ℝ 2 f (Set.Icc 0 β))
    (hf0 : f 0 = 0)
    (hf'0 : derivWithin f (Set.Icc 0 β) 0 = 1)
    (hfpos : ∀ t ∈ Set.Ioc 0 β, 0 < f t)
    (hT : ContDiffOn ℝ 1 T (Set.Icc 0 β)) :
    let ψ : ℝ → ℝ := fun s =>
      if s = 0 then 0 else Real.rpow |s| (p - 2) * s
    let Φ : ℝ → ℝ := fun t =>
      f t ^ (n - 1) * ψ (derivWithin T (Set.Icc 0 β) t)
    ContDiffOn ℝ 1 Φ (Set.Icc 0 β) →
      (∀ t ∈ Set.Ioo 0 β,
        deriv Φ t + lam * f t ^ (n - 1) * ψ (T t) = 0) →
      (∀ t ∈ Set.Ioo 0 β, 0 < T t) →
      ∀ t ∈ Set.Ioc 0 β, derivWithin T (Set.Icc 0 β) t < 0 := by
  intro ψ Φ hΦ hODE hTpos
  have hψneg_iff : ∀ s : ℝ, ψ s < 0 ↔ s < 0 := by
    intro s
    simpa [ψ] using signed_ppower_neg_iff p s
  have hψpos_iff : ∀ s : ℝ, 0 < ψ s ↔ 0 < s := by
    intro s
    simpa [ψ] using signed_ppower_pos_iff p s
  have hderivneg : ∀ t ∈ interior (Set.Icc 0 β), deriv Φ t < 0 := by
    rw [interior_Icc]
    intro t ht
    have hf_t : 0 < f t := hfpos t ⟨ht.1, le_of_lt ht.2⟩
    have hpow : 0 < f t ^ (n - 1) := pow_pos hf_t _
    have hψT : 0 < ψ (T t) := (hψpos_iff (T t)).mpr (hTpos t ht)
    have hflux : 0 < lam * f t ^ (n - 1) * ψ (T t) :=
      mul_pos (mul_pos hlam hpow) hψT
    have heq := hODE t ht
    nlinarith
  have hanti : StrictAntiOn Φ (Set.Icc 0 β) :=
    strictAntiOn_of_deriv_neg (convex_Icc 0 β) hΦ.continuousOn hderivneg
  have hn1 : n - 1 ≠ 0 := by omega
  have hΦ0 : Φ 0 = 0 := by
    have hzero : (0 : ℝ) ^ (n - 1) = 0 := zero_pow hn1
    simp [Φ, hf0, hzero]
  intro t ht
  have htpos : 0 < t := ht.1
  have htβ : t ≤ β := ht.2
  have hmem0 : (0 : ℝ) ∈ Set.Icc 0 β := ⟨le_rfl, le_of_lt hβ⟩
  have hmemt : t ∈ Set.Icc 0 β := ⟨le_of_lt htpos, htβ⟩
  have hΦt_neg : Φ t < 0 := by
    have hlt : Φ t < Φ 0 := hanti hmem0 hmemt htpos
    rwa [hΦ0] at hlt
  have hprod_neg :
      f t ^ (n - 1) * ψ (derivWithin T (Set.Icc 0 β) t) < 0 := by
    simpa [Φ] using hΦt_neg
  have hf_t : 0 < f t := hfpos t ⟨htpos, htβ⟩
  have hpow : 0 < f t ^ (n - 1) := pow_pos hf_t _
  have hψderiv_neg : ψ (derivWithin T (Set.Icc 0 β) t) < 0 := by
    have hmul := mul_neg_iff.mp hprod_neg
    rcases hmul with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
    · exact hright
    · exact False.elim ((not_lt_of_ge hpow.le) hleft)
  exact (hψneg_iff (derivWithin T (Set.Icc 0 β) t)).mp hψderiv_neg


#check_dependency_graph "derivWithin_neg_of_positive_solution" against "{\"edges\":[{\"conclusion\":{\"name\":\"hψneg_iff\",\"statement\":\"∀ (s : ℝ), ψ s < 0 ↔ s < 0\"},\"graphEdgeId\":\"h_001_h_neg_iff\",\"premises\":[],\"rawEdgeId\":\"telescope_20\"},{\"conclusion\":{\"name\":\"hψpos_iff\",\"statement\":\"∀ (s : ℝ), 0 < ψ s ↔ 0 < s\"},\"graphEdgeId\":\"h_002_h_pos_iff\",\"premises\":[],\"rawEdgeId\":\"telescope_21\"},{\"conclusion\":{\"name\":\"hn1\",\"statement\":\"n - 1 ≠ 0\"},\"graphEdgeId\":\"h_005_hn1\",\"premises\":[{\"name\":\"hn\",\"statement\":\"2 ≤ n\"}],\"rawEdgeId\":\"telescope_24\"},{\"conclusion\":{\"name\":\"htpos\",\"statement\":\"0 < t\"},\"graphEdgeId\":\"h_007_htpos\",\"premises\":[{\"name\":\"ht\",\"statement\":\"t ∈ Set.Ioc 0 β\"}],\"rawEdgeId\":\"telescope_28\"},{\"conclusion\":{\"name\":\"htβ\",\"statement\":\"t ≤ β\"},\"graphEdgeId\":\"h_008_ht\",\"premises\":[{\"name\":\"ht\",\"statement\":\"t ∈ Set.Ioc 0 β\"}],\"rawEdgeId\":\"telescope_29\"},{\"conclusion\":{\"name\":\"hmem0\",\"statement\":\"0 ∈ Set.Icc 0 β\"},\"graphEdgeId\":\"h_009_hmem0\",\"premises\":[{\"name\":\"hβ\",\"statement\":\"0 < β\"}],\"rawEdgeId\":\"telescope_30\"},{\"conclusion\":{\"name\":\"hderivneg\",\"statement\":\"∀ t ∈ interior (Set.Icc 0 β), deriv Φ t < 0\"},\"graphEdgeId\":\"h_003_hderivneg\",\"premises\":[{\"name\":\"hlam\",\"statement\":\"0 < lam\"},{\"name\":\"hfpos\",\"statement\":\"∀ t ∈ Set.Ioc 0 β, 0 < f t\"},{\"name\":\"hODE\",\"statement\":\"∀ t ∈ Set.Ioo 0 β, deriv Φ t + lam * f t ^ (n - 1) * ψ (T t) = 0\"},{\"name\":\"hTpos\",\"statement\":\"∀ t ∈ Set.Ioo 0 β, 0 < T t\"},{\"name\":\"hψpos_iff\",\"statement\":\"∀ (s : ℝ), 0 < ψ s ↔ 0 < s\"}],\"rawEdgeId\":\"telescope_22\"},{\"conclusion\":{\"name\":\"hΦ0\",\"statement\":\"Φ 0 = 0\"},\"graphEdgeId\":\"h_006_h_0\",\"premises\":[{\"name\":\"hf0\",\"statement\":\"f 0 = 0\"},{\"name\":\"hn1\",\"statement\":\"n - 1 ≠ 0\"}],\"rawEdgeId\":\"telescope_25\"},{\"conclusion\":{\"name\":\"hmemt\",\"statement\":\"t ∈ Set.Icc 0 β\"},\"graphEdgeId\":\"h_010_hmemt\",\"premises\":[{\"name\":\"htpos\",\"statement\":\"0 < t\"},{\"name\":\"htβ\",\"statement\":\"t ≤ β\"}],\"rawEdgeId\":\"telescope_31\"},{\"conclusion\":{\"name\":\"hf_t\",\"statement\":\"0 < f t\"},\"graphEdgeId\":\"h_013_hf_t\",\"premises\":[{\"name\":\"hfpos\",\"statement\":\"∀ t ∈ Set.Ioc 0 β, 0 < f t\"},{\"name\":\"htpos\",\"statement\":\"0 < t\"},{\"name\":\"htβ\",\"statement\":\"t ≤ β\"}],\"rawEdgeId\":\"telescope_34\"},{\"conclusion\":{\"name\":\"hanti\",\"statement\":\"StrictAntiOn Φ (Set.Icc 0 β)\"},\"graphEdgeId\":\"h_004_hanti\",\"premises\":[{\"name\":\"hΦ\",\"statement\":\"ContDiffOn ℝ 1 Φ (Set.Icc 0 β)\"},{\"name\":\"hderivneg\",\"statement\":\"∀ t ∈ interior (Set.Icc 0 β), deriv Φ t < 0\"}],\"rawEdgeId\":\"telescope_23\"},{\"conclusion\":{\"name\":\"hpow\",\"statement\":\"0 < f t ^ (n - 1)\"},\"graphEdgeId\":\"h_014_hpow\",\"premises\":[{\"name\":\"hf_t\",\"statement\":\"0 < f t\"}],\"rawEdgeId\":\"telescope_35\"},{\"conclusion\":{\"name\":\"hΦt_neg\",\"statement\":\"Φ t < 0\"},\"graphEdgeId\":\"h_011_h_t_neg\",\"premises\":[{\"name\":\"hanti\",\"statement\":\"StrictAntiOn Φ (Set.Icc 0 β)\"},{\"name\":\"hΦ0\",\"statement\":\"Φ 0 = 0\"},{\"name\":\"htpos\",\"statement\":\"0 < t\"},{\"name\":\"hmem0\",\"statement\":\"0 ∈ Set.Icc 0 β\"},{\"name\":\"hmemt\",\"statement\":\"t ∈ Set.Icc 0 β\"}],\"rawEdgeId\":\"telescope_32\"},{\"conclusion\":{\"name\":\"hprod_neg\",\"statement\":\"f t ^ (n - 1) * ψ (derivWithin T (Set.Icc 0 β) t) < 0\"},\"graphEdgeId\":\"h_012_hprod_neg\",\"premises\":[{\"name\":\"hΦt_neg\",\"statement\":\"Φ t < 0\"}],\"rawEdgeId\":\"telescope_33\"},{\"conclusion\":{\"name\":\"hψderiv_neg\",\"statement\":\"ψ (derivWithin T (Set.Icc 0 β) t) < 0\"},\"graphEdgeId\":\"h_015_h_deriv_neg\",\"premises\":[{\"name\":\"hprod_neg\",\"statement\":\"f t ^ (n - 1) * ψ (derivWithin T (Set.Icc 0 β) t) < 0\"},{\"name\":\"hpow\",\"statement\":\"0 < f t ^ (n - 1)\"}],\"rawEdgeId\":\"telescope_36\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"derivWithin T (Set.Icc 0 β) t < 0\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hψneg_iff\",\"statement\":\"∀ (s : ℝ), ψ s < 0 ↔ s < 0\"},{\"name\":\"hψderiv_neg\",\"statement\":\"ψ (derivWithin T (Set.Icc 0 β) t) < 0\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0971_derivwithin_neg_of_positive_solution\",\"reconstructedProofSha256\":\"2cbeb4b491b5982f77e7c068f9d677e932ef9c1cb0b9222481bd34e0cf1ff4ce\",\"selectedEdgeCount\":16,\"theoremName\":\"derivWithin_neg_of_positive_solution\",\"topologySha256\":\"253a8736d821304a70bd1dc324f603e5e16229c1ee25c0de4161930c7617de03\"}"
