import Mathlib

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
