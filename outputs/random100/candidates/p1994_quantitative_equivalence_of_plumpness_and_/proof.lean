import Mathlib

/- accepted add_to_file helper 1 -/
lemma exists_dyadic_level
    {δ B₀ r : ℝ} (m : ℤ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hB₀ : 0 < B₀) (hr : 0 < r)
    (hrR : r ≤ B₀ * δ ^ (m - 1)) :
    ∃ k : ℤ, m ≤ k ∧ B₀ * δ ^ k ≤ r ∧ r ≤ B₀ * δ ^ (k - 1) := by
  let a : ℝ := δ⁻¹
  have ha : 1 < a := by
    dsimp [a]
    exact (one_lt_inv₀ hδ0).2 hδ1
  have hscale0 : 0 < B₀ * δ ^ (m - 1) := by
    positivity
  have hx : 1 ≤ (B₀ * δ ^ (m - 1)) / r := by
    rw [one_le_div hr]
    exact hrR
  obtain ⟨n, hn₁, hn₂⟩ := exists_nat_pow_near hx ha
  refine ⟨m + n, by omega, ?_, ?_⟩
  · have hn₂' := hn₂
    rw [show a ^ (n + 1) = (δ ^ ((n : ℤ) + 1))⁻¹ by
      have hcast : ((n : ℤ) + 1) = (((n + 1 : ℕ) : ℤ)) := by norm_num
      rw [hcast, zpow_natCast]
      simp [a]] at hn₂'
    have hq : 0 < δ ^ ((n : ℤ) + 1) := by positivity
    have hlt : B₀ * δ ^ (m - 1) * δ ^ ((n : ℤ) + 1) < r := by
      have h1 : B₀ * δ ^ (m - 1) < (δ ^ ((n : ℤ) + 1))⁻¹ * r :=
        (div_lt_iff₀ hr).1 hn₂'
      exact (lt_inv_mul_iff₀' hq).1 h1
    have hprod : δ ^ (m - 1) * δ ^ ((n : ℤ) + 1) = δ ^ (m + n) := by
      rw [← zpow_add₀ hδ0.ne']
      congr 1
      omega
    have hlt' : B₀ * δ ^ (m + n) < r := by
      rw [← hprod]
      nlinarith
    exact hlt'.le
  · have hn₁' := hn₁
    rw [show a ^ n = (δ ^ (n : ℤ))⁻¹ by
      simp [a, zpow_natCast]] at hn₁'
    have hq : 0 < δ ^ (n : ℤ) := by positivity
    have hle0 : (δ ^ (n : ℤ))⁻¹ * r ≤ B₀ * δ ^ (m - 1) :=
      (le_div_iff₀ hr).1 hn₁'
    have hle : r ≤ (B₀ * δ ^ (m - 1)) * δ ^ (n : ℤ) :=
      (inv_mul_le_iff₀' hq).1 hle0
    have hprod : δ ^ (m - 1) * δ ^ (n : ℤ) = δ ^ (m + n - 1) := by
      rw [← zpow_add₀ hδ0.ne']
      congr 1
      omega
    rw [show m + n - 1 = m + (n : ℤ) - 1 by omega] at hprod
    rw [← hprod]
    nlinarith

/- verified submission -/
theorem quantitative_equivalence_of_plumpness_and_dyadic_plumpness
    {X : Type*} [MetricSpace X] (E : Set X) :
    (∀ (R b : ℝ), 0 < R → 0 < b → b < 1 →
      (∀ y ∈ E, ∀ r : ℝ, 0 < r → r ≤ R →
        ∃ z : X, Metric.ball z (b * r) ⊆ Metric.ball y r ∩ E) →
      ∀ (δ : ℝ) (m : ℤ) (b₀ B₀ : ℝ),
        0 < δ → δ < 1 → 0 < b₀ → b₀ ≤ B₀ →
        b₀ / B₀ ≤ b → B₀ * δ ^ m ≤ R →
        ∀ y ∈ E, ∀ k : ℤ, m ≤ k →
          ∃ z : X, Metric.ball z (b₀ * δ ^ k) ⊆
            Metric.ball y (B₀ * δ ^ k) ∩ E) ∧
    (∀ (δ : ℝ) (m : ℤ) (b₀ B₀ : ℝ),
      0 < δ → δ < 1 → 0 < b₀ → b₀ ≤ B₀ →
      (∀ y ∈ E, ∀ k : ℤ, m ≤ k →
        ∃ z : X, Metric.ball z (b₀ * δ ^ k) ⊆
          Metric.ball y (B₀ * δ ^ k) ∩ E) →
      ∀ (R b : ℝ), 0 < R → 0 < b → b < 1 →
        b ≤ δ * b₀ / B₀ → R ≤ B₀ * δ ^ (m - 1) →
        ∀ y ∈ E, ∀ r : ℝ, 0 < r → r ≤ R →
          ∃ z : X, Metric.ball z (b * r) ⊆ Metric.ball y r ∩ E) := by
  constructor
  · intro R b hR hb hb1 hplump δ m b₀ B₀ hδ0 hδ1 hb₀ hb₀B₀ hratio hscale
    intro y hy k hk
    have hB₀ : 0 < B₀ := lt_of_lt_of_le hb₀ hb₀B₀
    have hr : 0 < B₀ * δ ^ k := by positivity
    have hpow : δ ^ k ≤ δ ^ m :=
      zpow_le_zpow_right_of_le_one₀ hδ0 hδ1.le hk
    have hrR : B₀ * δ ^ k ≤ R := by
      have hmul : B₀ * δ ^ k ≤ B₀ * δ ^ m :=
        mul_le_mul_of_nonneg_left hpow hB₀.le
      exact hmul.trans hscale
    obtain ⟨z, hz⟩ := hplump y hy (B₀ * δ ^ k) hr hrR
    refine ⟨z, ?_⟩
    have hbB : b₀ ≤ b * B₀ := by
      have := (div_le_iff₀ hB₀).1 hratio
      nlinarith
    have hb_radius : b₀ * δ ^ k ≤ b * (B₀ * δ ^ k) := by
      have hnonneg : 0 ≤ δ ^ k := by positivity
      have hmul := mul_le_mul_of_nonneg_right hbB hnonneg
      nlinarith
    exact (Metric.ball_subset_ball hb_radius).trans hz
  · intro δ m b₀ B₀ hδ0 hδ1 hb₀ hb₀B₀ hdyadic R b hR hb hb1 hbratio hRscale
    intro y hy r hr hrR
    have hB₀ : 0 < B₀ := lt_of_lt_of_le hb₀ hb₀B₀
    have hrscale : r ≤ B₀ * δ ^ (m - 1) := hrR.trans hRscale
    obtain ⟨k, hk, hk_low, hk_high⟩ :=
      exists_dyadic_level m hδ0 hδ1 hB₀ hr hrscale
    obtain ⟨z, hz⟩ := hdyadic y hy k hk
    refine ⟨z, ?_⟩
    have hbB : b * B₀ ≤ δ * b₀ :=
      (le_div_iff₀ hB₀).1 hbratio
    have hb_radius : b * r ≤ b₀ * δ ^ k := by
      have h1 : b * r ≤ b * (B₀ * δ ^ (k - 1)) :=
        mul_le_mul_of_nonneg_left hk_high hb.le
      have hpow : δ * δ ^ (k - 1) = δ ^ k := by
        nth_rewrite 1 [← zpow_one δ]
        rw [← zpow_add₀ hδ0.ne']
        congr 1
        omega
      have hnonneg : 0 ≤ δ ^ (k - 1) := by positivity
      have h2 : b * (B₀ * δ ^ (k - 1)) ≤ δ * b₀ * δ ^ (k - 1) := by
        have hmul := mul_le_mul_of_nonneg_right hbB hnonneg
        nlinarith
      have h3 : δ * b₀ * δ ^ (k - 1) = b₀ * δ ^ k := by
        calc
          δ * b₀ * δ ^ (k - 1) = b₀ * (δ * δ ^ (k - 1)) := by ring
          _ = b₀ * δ ^ k := by rw [hpow]
      exact h1.trans (h2.trans_eq h3)
    intro x hx
    have hxdy := hz ((Metric.ball_subset_ball hb_radius) hx)
    exact ⟨(Metric.ball_subset_ball hk_low) hxdy.1, hxdy.2⟩
