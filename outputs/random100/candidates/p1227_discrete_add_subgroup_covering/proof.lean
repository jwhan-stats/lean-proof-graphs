import Mathlib

/- accepted add_to_file helper 1 -/
import Mathlib

open scoped Pointwise Topology
open Filter Set

lemma cover_nat_scale_of_local_cover
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K : Set E) (L : AddSubgroup E)
    (hK_zero : (0 : E) ∈ K)
    (hK_star : StarConvex ℝ 0 K)
    (ε ε₁ : ℝ) (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (q : ℕ) (hq_pos : 0 < q)
    (hq_recip : (q : ℝ) + 1 > 1 / (1 - ε))
    (hε₁ : ε₁ = (q : ℝ) * ε)
    (hcover : K ⊆ Set.image2 (· + ·) (L : Set E)
      ((fun x => ε • x) '' K)) :
    ∀ m : ℕ,
      (fun x => (m : ℝ) • x) '' K ⊆
        Set.image2 (· + ·) (L : Set E)
          ((fun x => ε₁ • x) '' K) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro y hy
      rcases hy with ⟨k, hk, rfl⟩
      have hkcover := hcover hk
      rw [Set.mem_image2] at hkcover
      rcases hkcover with ⟨l, hl, z, hz, hlz⟩
      rcases hz with ⟨k', hk', rfl⟩
      by_cases hmq : m ≤ q
      · let k₂ : E := ((m : ℝ) / (q : ℝ)) • k'
        have hk₂ : k₂ ∈ K := by
          dsimp [k₂]
          apply hK_star.smul_mem hk'
          · positivity
          · have hm : (m : ℝ) ≤ q := by exact_mod_cast hmq
            have hq : (0 : ℝ) < q := by exact_mod_cast hq_pos
            exact (div_le_one hq).2 hm
        refine Set.mem_image2.2 ⟨m • l, AddSubgroup.nsmul_mem L hl m,
          ε₁ • k₂, Set.mem_image_of_mem (fun x => ε₁ • x) hk₂, ?_⟩
        change m • l + ε₁ • k₂ = (m : ℝ) • k
        rw [← hlz]
        simp only [hε₁]
        rw [smul_add]
        congr 1
        · norm_cast
        · dsimp [k₂]
          rw [← smul_assoc, ← smul_assoc]
          congr 1
          change ((q : ℝ) * ε) * ((m : ℝ) * (q : ℝ)⁻¹) = (m : ℝ) * ε
          field_simp [show (q : ℝ) ≠ 0 by positivity]
      · have hm_pos : 0 < m := lt_trans hq_pos (Nat.not_le.mp hmq)
        let r : ℕ := ⌈(m : ℝ) * ε⌉₊
        have hmr_real : (m : ℝ) * ε < (m : ℝ) - 1 := by
          have hmgt : (m : ℝ) > 1 / (1 - ε) := by
            have hmq_nat : q + 1 ≤ m := Nat.succ_le_of_lt (Nat.not_le.mp hmq)
            have hm_q : (q : ℝ) + 1 ≤ m := by exact_mod_cast hmq_nat
            exact lt_of_lt_of_le hq_recip hm_q
          have hden : 0 < 1 - ε := sub_pos.mpr hε_lt_one
          have hmreal : (0 : ℝ) < m := by positivity
          have h1 : (1 : ℝ) / m < 1 - ε := (one_div_lt hmreal hden).2 hmgt
          have hmul := mul_lt_mul_of_pos_left h1 hmreal
          field_simp [show (m : ℝ) ≠ 0 by positivity] at hmul
          nlinarith
        have hrlt : r < m := by
          have hle : r ≤ m - 1 := by
            rw [Nat.ceil_le]
            have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
              rw [Nat.cast_sub (Nat.succ_le_iff.mpr hm_pos)]
              simp
            rw [hcast]
            exact le_of_lt hmr_real
          exact lt_of_le_of_lt hle (Nat.pred_lt hm_pos.ne')
        have hzscale : (m * ε : ℝ) • k' ∈ (fun x => (r : ℝ) • x) '' K := by
          by_cases hr : r = 0
          · have hnonpos : (m : ℝ) * ε ≤ 0 := by
              have hle0 : (m : ℝ) * ε ≤ (r : ℝ) := Nat.le_ceil _
              rw [hr] at hle0
              simpa using hle0
            have hzero : (m : ℝ) * ε = 0 := le_antisymm hnonpos (mul_nonneg (by positivity) hε_pos.le)
            refine ⟨0, hK_zero, ?_⟩
            simp [hzero]
          · refine ⟨((m * ε : ℝ) / r) • k', ?_, ?_⟩
            · apply hK_star.smul_mem hk'
              · positivity
              · have hceil : (m : ℝ) * ε ≤ r := Nat.le_ceil _
                have hrpos : (0 : ℝ) < r := by positivity
                exact (div_le_one hrpos).2 hceil
            · change (r : ℝ) • (((m * ε : ℝ) / r) • k') = (m * ε : ℝ) • k'
              rw [← smul_assoc]
              congr 1
              change (r : ℝ) * ((m * ε : ℝ) * (r : ℝ)⁻¹) = (m * ε : ℝ)
              field_simp [show (r : ℝ) ≠ 0 by positivity]
        have hzcover := ih r hrlt hzscale
        rw [Set.mem_image2] at hzcover
        rcases hzcover with ⟨l₂, hl₂, z₂, hz₂, hl₂z⟩
        rcases hz₂ with ⟨k₂, hk₂, rfl⟩
        refine Set.mem_image2.2 ⟨m • l + l₂,
          L.add_mem (AddSubgroup.nsmul_mem L hl m) hl₂,
          ε₁ • k₂, Set.mem_image_of_mem (fun x => ε₁ • x) hk₂, ?_⟩
        change m • l + l₂ + ε₁ • k₂ = (m : ℝ) • k
        rw [← hlz]
        calc
          m • l + l₂ + ε₁ • k₂ = (m : ℝ) • l + (l₂ + ε₁ • k₂) := by
            norm_cast
            abel
          _ = (m : ℝ) • l + (m * ε : ℝ) • k' := by rw [hl₂z]
          _ = (m : ℝ) • (l + ε • k') := by
            simp [smul_add, smul_smul, mul_comm]

lemma exists_nat_scale_mem_of_zero_mem_interior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (hK_nhds : (0 : E) ∈ interior K) :
    ∀ x : E, ∃ m : ℕ, x ∈ (fun y => (m : ℝ) • y) '' K := by
  intro x
  have hcont : ContinuousAt (fun c : ℝ => c • x) 0 := by
    exact continuousAt_id.smul continuousAt_const
  have hnhds : interior K ∈ 𝓝 (0 : E) := isOpen_interior.mem_nhds hK_nhds
  have hev : ∀ᶠ c : ℝ in 𝓝 0, c • x ∈ interior K := by
    have ht : Tendsto (fun c : ℝ => c • x) (𝓝 0) (𝓝 (0 : E)) := by
      simpa using hcont.tendsto
    exact ht hnhds
  rw [Metric.eventually_nhds_iff] at hev
  rcases hev with ⟨δ, hδ, hδ'⟩
  rcases exists_nat_one_div_lt hδ with ⟨m, hm⟩
  let M : ℕ := m + 1
  have hdist : dist ((1 : ℝ) / M) 0 < δ := by
    rw [Real.dist_eq, sub_zero]
    have hpos : (0 : ℝ) < 1 / M := by positivity
    rw [abs_of_pos hpos]
    simpa [M] using hm
  have hmem : ((1 : ℝ) / M) • x ∈ interior K := hδ' hdist
  refine ⟨M, ((1 : ℝ) / M) • x, interior_subset hmem, ?_⟩
  change (M : ℝ) • (((1 : ℝ) / M) • x) = x
  rw [← smul_assoc]
  change ((M : ℝ) * (1 / M)) • x = x
  have hcoeff : (M : ℝ) * (1 / M) = 1 := by
    field_simp [show (M : ℝ) ≠ 0 by positivity]
  rw [hcoeff, one_smul]

/- verified submission -/
theorem discrete_add_subgroup_covering
    (n : ℕ) (hn : 1 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (L : AddSubgroup (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (hK_compact : IsCompact K)
    (hK_nhds : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K)
    (hK_star : StarConvex ℝ 0 K)
    (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) (hε₀_lt_one : ε₀ < 1)
    (hcover : K ⊆ Set.image2 (· + ·) (L : Set (EuclideanSpace ℝ (Fin n)))
      ((fun x => ε₀ • x) '' K)) :
    let ε₁ : ℝ := (((⌊ε₀ / (1 - ε₀)⌋ : ℤ) + 1 : ℤ) : ℝ) * ε₀
    Set.univ = Set.image2 (· + ·) (L : Set (EuclideanSpace ℝ (Fin n)))
      ((fun x => ε₁ • x) '' K) := by
  let q : ℕ := (((⌊ε₀ / (1 - ε₀)⌋ : ℤ) + 1 : ℤ).toNat)
  let ε₁ : ℝ := (((⌊ε₀ / (1 - ε₀)⌋ : ℤ) + 1 : ℤ) : ℝ) * ε₀
  change Set.univ = Set.image2 (· + ·) (L : Set (EuclideanSpace ℝ (Fin n)))
      ((fun x => ε₁ • x) '' K)
  have ha_pos : 0 < ε₀ / (1 - ε₀) := by
    exact div_pos hε₀_pos (sub_pos.mpr hε₀_lt_one)
  have hfloor_nonneg : 0 ≤ ⌊ε₀ / (1 - ε₀)⌋ := Int.floor_nonneg.mpr ha_pos.le
  have hq_nonneg_int : 0 ≤ (⌊ε₀ / (1 - ε₀)⌋ : ℤ) + 1 := by omega
  have hq_pos : 0 < q := by
    dsimp [q]
    omega
  have hq_cast_int : (q : ℤ) = (⌊ε₀ / (1 - ε₀)⌋ : ℤ) + 1 := by
    dsimp [q]
    exact Int.toNat_of_nonneg hq_nonneg_int
  have hq_cast : (q : ℝ) = (((⌊ε₀ / (1 - ε₀)⌋ : ℤ) + 1 : ℤ) : ℝ) := by
    exact_mod_cast hq_cast_int
  have hrecip : 1 / (1 - ε₀) = ε₀ / (1 - ε₀) + 1 := by
    field_simp [sub_ne_zero.mpr hε₀_lt_one.ne']
    ring
  have hq_recip : (q : ℝ) + 1 > 1 / (1 - ε₀) := by
    rw [hrecip, hq_cast]
    have hfloor := Int.lt_floor_add_one (ε₀ / (1 - ε₀))
    norm_num at hfloor ⊢
  have hε₁ : ε₁ = (q : ℝ) * ε₀ := by
    dsimp [ε₁]
    rw [hq_cast]
  have hscale :=
    cover_nat_scale_of_local_cover K L (interior_subset hK_nhds) hK_star
      ε₀ ε₁ hε₀_pos hε₀_lt_one q hq_pos hq_recip hε₁ hcover
  ext x
  constructor
  · intro _
    rcases exists_nat_scale_mem_of_zero_mem_interior K hK_nhds x with ⟨m, hm⟩
    exact hscale m hm
  · intro _
    simp
