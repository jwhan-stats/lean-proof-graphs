import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1089_logarithmic_average_bound
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 3b0de1941c8929d9339458ece58933b5a7be4f50c1f8629973513c008d4dd8c3
-- reconstructed_proof_sha256: c6fbcb13365678ea7f4ec991d10ff76066d8d782cca0b446b954f8b737f3882f
-- selected_edge_count: 7

/- accepted add_to_file helper 1 -/
lemma sum_range_mul_eq_sum_filter {M : Type*} [AddCommMonoid M]
    (m N : ℕ) (hm : 0 < m) (f : {n : ℕ // 0 < n} → M) :
    (∑ k ∈ Finset.range (N / m),
        f ⟨m * (k + 1), Nat.mul_pos hm (Nat.zero_lt_succ k)⟩)
      =
    ∑ j ∈ Finset.range N,
      if m ∣ j + 1 then f ⟨j + 1, Nat.zero_lt_succ j⟩ else 0 := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij
    (fun k _ => m * (k + 1) - 1) ?_ ?_ ?_ ?_
  · intro k hk
    have hk1 : k + 1 ≤ N / m := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
    have hmul : m * (k + 1) ≤ N := by
      simpa [mul_comm] using Nat.mul_le_of_le_div m (k + 1) N hk1
    have hpos : 0 < m * (k + 1) := Nat.mul_pos hm (Nat.zero_lt_succ k)
    have hj : m * (k + 1) - 1 < N := Nat.sub_one_lt_of_le hpos hmul
    simp [Finset.mem_filter, Finset.mem_range, hj, Nat.sub_add_cancel hpos]
  · intro k₁ hk₁ k₂ hk₂ h
    have h₁ : 0 < m * (k₁ + 1) := Nat.mul_pos hm (Nat.zero_lt_succ k₁)
    have h₂ : 0 < m * (k₂ + 1) := Nat.mul_pos hm (Nat.zero_lt_succ k₂)
    have hs : m * (k₁ + 1) = m * (k₂ + 1) := by
      have := congrArg (· + 1) h
      simpa [Nat.sub_add_cancel h₁, Nat.sub_add_cancel h₂] using this
    have hk : k₁ + 1 = k₂ + 1 := Nat.mul_left_cancel hm hs
    exact Nat.succ.inj hk
  · intro j hj
    have hjmem := Finset.mem_filter.mp hj
    have hjr : j < N := Finset.mem_range.mp hjmem.1
    have hd : m ∣ j + 1 := hjmem.2
    rcases hd with ⟨t, ht⟩
    have htpos : 0 < t := by
      by_contra htz
      have ht0 : t = 0 := Nat.eq_zero_of_not_pos htz
      have : j + 1 = 0 := by simpa [ht0] using ht
      exact Nat.succ_ne_zero j this
    have htmul : m * t ≤ N := by
      have : j + 1 ≤ N := Nat.succ_le_of_lt hjr
      rw [ht] at this
      exact this
    have htdiv : t ≤ N / m := (Nat.le_div_iff_mul_le hm).mpr (by simpa [mul_comm] using htmul)
    refine ⟨t - 1, Finset.mem_range.mpr (Nat.sub_one_lt_of_le htpos htdiv), ?_⟩
    have hsucc : t - 1 + 1 = t := Nat.sub_add_cancel htpos
    change m * (t - 1 + 1) - 1 = j
    rw [hsucc]
    omega
  · intro k hk
    have hpos : 0 < m * (k + 1) := Nat.mul_pos hm (Nat.zero_lt_succ k)
    simp [Nat.sub_add_cancel hpos]

/- accepted add_to_file helper 2 -/
lemma period_weight_square_avg
    (B : Finset {n : ℕ // 0 < n}) (hB : B.Nonempty) :
    let q : ℕ := ∏ m ∈ B, m.1
    let S : ℝ := ∑ m ∈ B, 1 / (m.1 : ℝ)
    (q : ℝ)⁻¹ *
      (∑ j ∈ Finset.range q,
        (1 - (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) / S) ^ 2)
      =
    S⁻¹ ^ 2 *
      (∑ m ∈ B, ∑ n ∈ B,
        (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - 1 := by
  classical
  intro q S
  have hq : 0 < q := Finset.prod_pos (fun m _ => m.2)
  have hS : 0 < S := by
    apply Finset.sum_pos _ hB
    intro m hm
    exact one_div_pos.mpr (by exact_mod_cast m.2)
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hSR : S ≠ 0 := hS.ne'
  have hdvd : ∀ m ∈ B, m.1 ∣ q := fun m hm => Finset.dvd_prod_of_mem (fun x => x.1) hm
  have hsum_d :
      (∑ j ∈ Finset.range q, ∑ m ∈ B,
          if m.1 ∣ j + 1 then (1 : ℝ) else 0)
        = (q : ℝ) * S := by
    rw [Finset.sum_comm]
    trans ∑ m ∈ B, (((q / m.1 : ℕ) : ℝ))
    · refine Finset.sum_congr rfl ?_
      intro m hm
      rw [Finset.sum_boole, Nat.card_multiples]
    · change (∑ m ∈ B, (((q / m.1 : ℕ) : ℝ))) =
        (q : ℝ) * (∑ m ∈ B, 1 / (m.1 : ℝ))
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro m hm
      have hmR : (m.1 : ℝ) ≠ 0 := by exact_mod_cast m.2.ne'
      rw [Nat.cast_div (hdvd m hm) hmR]
      field_simp [hmR]
  have hsum_d_card :
      (∑ j ∈ Finset.range q,
          (((B.filter fun m => m.1 ∣ j + 1).card : ℝ)))
        = (q : ℝ) * S := by
    trans ∑ j ∈ Finset.range q, ∑ m ∈ B,
      if m.1 ∣ j + 1 then (1 : ℝ) else 0
    · refine Finset.sum_congr rfl ?_
      intro j hj
      rw [← Finset.sum_boole]
    · exact hsum_d
  have hsum_dsq :
      (∑ j ∈ Finset.range q,
          (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) ^ 2)
        =
      ∑ m ∈ B, ∑ n ∈ B, (((q / Nat.lcm m.1 n.1 : ℕ) : ℝ)) := by
    calc
      (∑ j ∈ Finset.range q,
          (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) ^ 2)
          =
        ∑ j ∈ Finset.range q,
          (∑ m ∈ B, ∑ n ∈ B,
            if Nat.lcm m.1 n.1 ∣ j + 1 then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [sq, Finset.sum_mul_sum]
            refine Finset.sum_congr rfl ?_
            intro m hm
            refine Finset.sum_congr rfl ?_
            intro n hn
            by_cases hlm : Nat.lcm m.1 n.1 ∣ j + 1
            · have hm : m.1 ∣ j + 1 := (Nat.lcm_dvd_iff.mp hlm).1
              have hn : n.1 ∣ j + 1 := (Nat.lcm_dvd_iff.mp hlm).2
              simp [hlm, hm, hn]
            · have hnot : ¬ (m.1 ∣ j + 1 ∧ n.1 ∣ j + 1) := by
                intro h
                exact hlm (Nat.lcm_dvd_iff.mpr h)
              by_cases hm : m.1 ∣ j + 1
              · by_cases hn : n.1 ∣ j + 1
                · exact False.elim (hnot ⟨hm, hn⟩)
                · simp [hm, hn, hlm]
              · simp [hm, hlm]
      _ = ∑ m ∈ B, ∑ n ∈ B,
            (∑ j ∈ Finset.range q,
              if Nat.lcm m.1 n.1 ∣ j + 1 then (1 : ℝ) else 0) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro m hm
            rw [Finset.sum_comm]
      _ = ∑ m ∈ B, ∑ n ∈ B, (((q / Nat.lcm m.1 n.1 : ℕ) : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            refine Finset.sum_congr rfl ?_
            intro n hn
            rw [Finset.sum_boole, Nat.card_multiples]
  have hlcm_cast : ∀ m ∈ B, ∀ n ∈ B,
      (((q / Nat.lcm m.1 n.1 : ℕ) : ℝ))
        = (q : ℝ) * ((Nat.gcd m.1 n.1 : ℝ) / ((m.1 : ℝ) * (n.1 : ℝ))) := by
    intro m hm n hn
    have hmpos : (m.1 : ℝ) ≠ 0 := by exact_mod_cast m.2.ne'
    have hnpos : (n.1 : ℝ) ≠ 0 := by exact_mod_cast n.2.ne'
    have hgcdpos_nat : 0 < Nat.gcd m.1 n.1 := Nat.gcd_pos_of_pos_left n.1 m.2
    have hlcmpos_nat : 0 < Nat.lcm m.1 n.1 := Nat.lcm_pos m.2 n.2
    have hlcmdvd : Nat.lcm m.1 n.1 ∣ q := by
      exact Nat.lcm_dvd_iff.mpr ⟨hdvd m hm, hdvd n hn⟩
    have hlcmR : ((Nat.lcm m.1 n.1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast hlcmpos_nat.ne'
    rw [Nat.cast_div hlcmdvd hlcmR]
    have hgl : (Nat.gcd m.1 n.1 : ℝ) * (Nat.lcm m.1 n.1 : ℝ)
        = (m.1 : ℝ) * (n.1 : ℝ) := by
      exact_mod_cast Nat.gcd_mul_lcm m.1 n.1
    field_simp [hlcmR, hmpos, hnpos]
    linarith [hgl]
  have hsum_dsq' :
      (∑ j ∈ Finset.range q,
          (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) ^ 2)
        =
      (q : ℝ) *
      (∑ m ∈ B, ∑ n ∈ B,
        (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) := by
    rw [hsum_dsq]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro m hm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [hlcm_cast m hm n hn]
    have hgcomm : Nat.gcd m.1 n.1 = Nat.gcd n.1 m.1 := Nat.gcd_comm m.1 n.1
    rw [hgcomm]
    ring
  calc
    (q : ℝ)⁻¹ *
        (∑ j ∈ Finset.range q,
          (1 - (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) / S) ^ 2)
        =
      (q : ℝ)⁻¹ *
        (∑ j ∈ Finset.range q,
          (1 - 2 / S *
            (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0)
            +
            (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) ^ 2 / S ^ 2)) := by
          refine congrArg _ ?_
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ = (q : ℝ)⁻¹ *
          ((q : ℝ) - 2 / S * ((q : ℝ) * S)
            + ((q : ℝ) *
              (∑ m ∈ B, ∑ n ∈ B,
                (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ)))) / S ^ 2) := by
          congr 1
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          congr 1
          · congr 1
            · simp
            · first
              | calc
                  (∑ j ∈ Finset.range q,
                      2 / S * (∑ m ∈ B,
                        if m.1 ∣ j + 1 then (1 : ℝ) else 0))
                      =
                    2 / S *
                      (∑ j ∈ Finset.range q, ∑ m ∈ B,
                        if m.1 ∣ j + 1 then (1 : ℝ) else 0) := by
                      rw [← Finset.mul_sum]
                  _ = 2 / S * ((q : ℝ) * S) := by
                      rw [hsum_d]
              | calc
                  (∑ j ∈ Finset.range q,
                      2 / S * (((B.filter fun m => m.1 ∣ j + 1).card : ℝ)))
                      =
                    2 / S *
                      (∑ j ∈ Finset.range q,
                        (((B.filter fun m => m.1 ∣ j + 1).card : ℝ))) := by
                      rw [← Finset.mul_sum]
                  _ = 2 / S * ((q : ℝ) * S) := by
                      rw [hsum_d_card]
          · congr 1
            calc
              (∑ j ∈ Finset.range q,
                  (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) ^ 2 / S ^ 2)
                  =
                (∑ j ∈ Finset.range q,
                  (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) ^ 2) / S ^ 2 := by
                  rw [← Finset.sum_div]
              _ =
                ((q : ℝ) *
                  (∑ m ∈ B, ∑ n ∈ B,
                    (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ)))) / S ^ 2 := by
                  rw [hsum_dsq']
    _ = S⁻¹ ^ 2 *
          (∑ m ∈ B, ∑ n ∈ B,
            (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - 1 := by
          field_simp [hqR, hSR] <;> ring

/- accepted add_to_file helper 3 -/
lemma nested_log_avg_gcd
    (B : Finset {n : ℕ // 0 < n}) (hB : B.Nonempty) :
    let S : ℝ := ∑ m ∈ B, 1 / (m.1 : ℝ)
    (∑ m ∈ B,
        ((∑ n ∈ B, ((Nat.gcd n.1 m.1 : ℝ) - 1) / (n.1 : ℝ)) / S)
          / (m.1 : ℝ)) / S
      =
    S⁻¹ ^ 2 *
      (∑ m ∈ B, ∑ n ∈ B,
        (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - 1 := by
  classical
  intro S
  have hS : 0 < S := by
    apply Finset.sum_pos _ hB
    intro m hm
    exact one_div_pos.mpr (by exact_mod_cast m.2)
  have hS0 : S ≠ 0 := hS.ne'
  have h_inner : ∀ m ∈ B,
      (∑ n ∈ B, ((Nat.gcd n.1 m.1 : ℝ) - 1) / (n.1 : ℝ))
        = (∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S := by
    intro m hm
    calc
      (∑ n ∈ B, ((Nat.gcd n.1 m.1 : ℝ) - 1) / (n.1 : ℝ))
          = ∑ n ∈ B,
            ((Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ) - 1 / (n.1 : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            ring
      _ = (∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S := by
            rw [Finset.sum_sub_distrib]
  have h_factor :
      (∑ m ∈ B,
          (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / S)
            / (m.1 : ℝ)) / S
        =
      S⁻¹ ^ 2 * ∑ m ∈ B,
        (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / (m.1 : ℝ)) := by
    calc
      (∑ m ∈ B,
          (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / S)
            / (m.1 : ℝ)) / S
          =
        ∑ m ∈ B,
          ((((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / S)
            / (m.1 : ℝ)) / S := by
          rw [Finset.sum_div]
      _ =
        ∑ m ∈ B,
          S⁻¹ ^ 2 *
            (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / (m.1 : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          ring
      _ = S⁻¹ ^ 2 * ∑ m ∈ B,
          (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / (m.1 : ℝ)) := by
          rw [← Finset.mul_sum]
  have h_split :
      (∑ m ∈ B,
          (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / (m.1 : ℝ)))
        =
      (∑ m ∈ B, ∑ n ∈ B,
          (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - S ^ 2 := by
    calc
      (∑ m ∈ B,
          (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / (m.1 : ℝ)))
          =
        ∑ m ∈ B,
          (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) / (m.1 : ℝ))
            - S / (m.1 : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          ring
      _ =
        (∑ m ∈ B,
            ((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) / (m.1 : ℝ)))
          - ∑ m ∈ B, S / (m.1 : ℝ) := by
          rw [Finset.sum_sub_distrib]
      _ =
      (∑ m ∈ B, ∑ n ∈ B,
          (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - S ^ 2 := by
          congr 1
          · refine Finset.sum_congr rfl ?_
            intro m hm
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl ?_
            intro n hn
            ring
          · calc
              (∑ m ∈ B, S / (m.1 : ℝ))
                  = S * (∑ m ∈ B, 1 / (m.1 : ℝ)) := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl ?_
                  intro m hm
                  ring
              _ = S ^ 2 := by
                  change S * S = S ^ 2
                  ring
  have hcancel : S⁻¹ ^ 2 * S ^ 2 = 1 := by
    have h : S⁻¹ * S = 1 := inv_mul_cancel₀ hS0
    calc
      S⁻¹ ^ 2 * S ^ 2 = (S⁻¹ * S) ^ 2 := by ring
      _ = 1 ^ 2 := by rw [h]
      _ = 1 := by norm_num
  calc
    (∑ m ∈ B,
        ((∑ n ∈ B, ((Nat.gcd n.1 m.1 : ℝ) - 1) / (n.1 : ℝ)) / S)
          / (m.1 : ℝ)) / S
        =
      (∑ m ∈ B,
        (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / S)
          / (m.1 : ℝ)) / S := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro m hm
        rw [h_inner m hm]
    _ = S⁻¹ ^ 2 * ∑ m ∈ B,
          (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / (m.1 : ℝ)) :=
        h_factor
    _ = S⁻¹ ^ 2 *
          ((∑ m ∈ B, ∑ n ∈ B,
            (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - S ^ 2) := by
        rw [h_split]
    _ = S⁻¹ ^ 2 *
          (∑ m ∈ B, ∑ n ∈ B,
            (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - 1 := by
        calc
          S⁻¹ ^ 2 *
              ((∑ m ∈ B, ∑ n ∈ B,
                (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - S ^ 2)
              =
            S⁻¹ ^ 2 *
              (∑ m ∈ B, ∑ n ∈ B,
                (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ)))
              - S⁻¹ ^ 2 * S ^ 2 := by
            ring
          _ = S⁻¹ ^ 2 *
              (∑ m ∈ B, ∑ n ∈ B,
                (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - 1 := by
            rw [hcancel]

/- accepted add_to_file helper 4 -/
lemma sum_range_blocks_le
    (f W : ℕ → ℝ) (q Q r : ℕ)
    (hW : ∀ j, 0 ≤ W j)
    (hblock : ∀ i j, j < q → f (i * q + j) ≤ W j)
    (htail : ∀ j, j < r → f (Q * q + j) ≤ W j)
    (hr : r ≤ q) :
    (∑ j ∈ Finset.range (Q * q + r), f j) ≤ (Q + 1 : ℝ) * ∑ j ∈ Finset.range q, W j := by
  classical
  have hfull : ∀ Q : ℕ,
      (∑ j ∈ Finset.range (Q * q), f j) ≤ (Q : ℝ) * ∑ j ∈ Finset.range q, W j := by
    intro Q
    induction Q with
    | zero => simp
    | succ Q ih =>
        rw [Nat.succ_mul, Finset.sum_range_add]
        calc
          (∑ j ∈ Finset.range (Q * q), f j) +
              (∑ j ∈ Finset.range q, f (Q * q + j))
              ≤ (Q : ℝ) * (∑ j ∈ Finset.range q, W j) +
                  (∑ j ∈ Finset.range q, W j) := by
                exact add_le_add ih (Finset.sum_le_sum (fun j hj => hblock Q j (Finset.mem_range.mp hj)))
          _ = ((Q + 1 : ℕ) : ℝ) * ∑ j ∈ Finset.range q, W j := by
                norm_num
                ring
  rw [Finset.sum_range_add]
  calc
    (∑ j ∈ Finset.range (Q * q), f j) +
        (∑ j ∈ Finset.range r, f (Q * q + j))
        ≤ (Q : ℝ) * (∑ j ∈ Finset.range q, W j) +
            (∑ j ∈ Finset.range q, W j) := by
          refine add_le_add (hfull Q) ?_
          calc
            (∑ j ∈ Finset.range r, f (Q * q + j))
                ≤ ∑ j ∈ Finset.range r, W j :=
                Finset.sum_le_sum (fun j hj => htail j (Finset.mem_range.mp hj))
            _ ≤ ∑ j ∈ Finset.range q, W j := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro j hj
                  exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) hr)
                · intro j hj _
                  exact hW j
    _ = (Q + 1 : ℝ) * ∑ j ∈ Finset.range q, W j := by
          ring

/- accepted add_to_file helper 5 -/
lemma weighted_prefix_bound_generic
    (a : {n : ℕ // 0 < n} → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (q : ℕ) (hq : 0 < q) (w : ℕ → ℝ)
    (hperiod : ∀ i j, w (i * q + j) = w j)
    (N : ℕ) (hN : 0 < N) :
    let T : ℝ := ∑ j ∈ Finset.range q, |w j|
    ‖(N : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
        a ⟨j + 1, Nat.zero_lt_succ j⟩ * (w j : ℂ)‖
      ≤
    Real.sqrt ((q : ℝ)⁻¹ * ∑ j ∈ Finset.range q, (w j) ^ 2) + T / N := by
  classical
  intro T
  let Q : ℕ := N / q
  let r : ℕ := N % q
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hqr : N = Q * q + r := by
    calc
      N = q * (N / q) + N % q := (Nat.div_add_mod N q).symm
      _ = Q * q + r := by
        dsimp [Q, r]
        rw [mul_comm]
  have hr : r ≤ q := by
    exact le_of_lt (Nat.mod_lt N hq)
  have hTnonneg : 0 ≤ T := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hterm : ∀ i j, j < q →
      ‖a ⟨(i * q + j) + 1, Nat.zero_lt_succ _⟩ * (w (i * q + j) : ℂ)‖ ≤ |w j| := by
    intro i j hj
    rw [hperiod i j]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg _) (ha _)
  have hterm_tail : ∀ j, j < r →
      ‖a ⟨(Q * q + j) + 1, Nat.zero_lt_succ _⟩ * (w (Q * q + j) : ℂ)‖ ≤ |w j| := by
    intro j hj
    rw [hperiod Q j]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg _) (ha _)
  have hsum_norm :
      (∑ j ∈ Finset.range N,
          ‖a ⟨j + 1, Nat.zero_lt_succ j⟩ * (w j : ℂ)‖)
        ≤ (Q + 1 : ℝ) * T := by
    conv_lhs => rw [hqr]
    exact sum_range_blocks_le
      (fun j => ‖a ⟨j + 1, Nat.zero_lt_succ j⟩ * (w j : ℂ)‖)
      (fun j => |w j|) q Q r
      (fun j => abs_nonneg _) hterm hterm_tail hr
  have hmain0 :
      ‖(N : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
          a ⟨j + 1, Nat.zero_lt_succ j⟩ * (w j : ℂ)‖
        ≤ (N : ℝ)⁻¹ * ((Q + 1 : ℝ) * T) := by
    rw [norm_mul]
    have hn : ‖(N : ℂ)⁻¹‖ = (N : ℝ)⁻¹ := by
      simp [norm_inv]
    rw [hn]
    exact mul_le_mul_of_nonneg_left
      ((norm_sum_le _ _).trans hsum_norm)
      (inv_nonneg.mpr (by positivity))
  have hQle : (Q : ℝ) / N ≤ 1 / q := by
    have hmul : Q * q ≤ N := Nat.div_mul_le_self N q
    have hmulR : (Q : ℝ) * q ≤ N := by exact_mod_cast hmul
    have hqposR : (0 : ℝ) < q := by exact_mod_cast hq
    have hNposR : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_le_div_iff₀ hNposR hqposR]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmulR
  have hfactor :
      (N : ℝ)⁻¹ * ((Q + 1 : ℝ) * T) ≤ (1 / q + 1 / N) * T := by
    have hfrac : ((Q + 1 : ℝ)) / N ≤ 1 / q + 1 / N := by
      calc
        ((Q + 1 : ℝ)) / N = (Q : ℝ) / N + 1 / N := by ring
        _ ≤ 1 / q + 1 / N := add_le_add hQle le_rfl
    calc
      (N : ℝ)⁻¹ * ((Q + 1 : ℝ) * T)
          = ((Q + 1 : ℝ) / N) * T := by ring
      _ ≤ (1 / q + 1 / N) * T :=
          mul_le_mul_of_nonneg_right hfrac hTnonneg
  have hcs : T / q ≤
      Real.sqrt ((q : ℝ)⁻¹ * ∑ j ∈ Finset.range q, (w j) ^ 2) := by
    have hsq := sq_sum_le_card_mul_sum_sq (s := Finset.range q) (f := fun j => |w j|)
    have hsq' : T ^ 2 ≤ (q : ℝ) * ∑ j ∈ Finset.range q, (w j) ^ 2 := by
      simpa [T, sq_abs] using hsq
    apply Real.le_sqrt_of_sq_le
    calc
      (T / q) ^ 2 = T ^ 2 / (q : ℝ) ^ 2 := by ring
      _ ≤ ((q : ℝ) * ∑ j ∈ Finset.range q, (w j) ^ 2) / (q : ℝ) ^ 2 := by
          exact div_le_div_of_nonneg_right hsq' (sq_nonneg _)
      _ = (q : ℝ)⁻¹ * ∑ j ∈ Finset.range q, (w j) ^ 2 := by
          field_simp [hqR]
  calc
    ‖(N : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
        a ⟨j + 1, Nat.zero_lt_succ j⟩ * (w j : ℂ)‖
        ≤ (N : ℝ)⁻¹ * ((Q + 1 : ℝ) * T) := hmain0
    _ ≤ (1 / q + 1 / N) * T := hfactor
    _ = T / q + T / N := by ring
    _ ≤ Real.sqrt ((q : ℝ)⁻¹ * ∑ j ∈ Finset.range q, (w j) ^ 2) + T / N :=
        add_le_add hcs le_rfl

/- accepted add_to_file helper 6 -/
lemma local_average_mul_approx
    (a : {n : ℕ // 0 < n} → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (m N : ℕ) (hm : 0 < m) (hN : 0 < N) :
    let A : ℕ → ({n : ℕ // 0 < n} → ℂ) → ℂ := fun M c ↦
      (M : ℂ)⁻¹ * ∑ k ∈ Finset.range M, c ⟨k + 1, Nat.zero_lt_succ k⟩
    ‖A (N / m) (fun k ↦ a ⟨m * k.1, Nat.mul_pos hm k.2⟩) / (m : ℂ)
        - (N : ℂ)⁻¹ * ∑ k ∈ Finset.range (N / m),
            a ⟨m * (k + 1), Nat.mul_pos hm (Nat.zero_lt_succ k)⟩‖
      ≤ 1 / (N : ℝ) := by
  classical
  intro A
  let q : ℕ := N / m
  by_cases hq : q = 0
  · simp [A, q, hq]
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    let X : ℂ := ∑ k ∈ Finset.range q,
      a ⟨m * (k + 1), Nat.mul_pos hm (Nat.zero_lt_succ k)⟩
    have hrewrite :
        A q (fun k ↦ a ⟨m * k.1, Nat.mul_pos hm k.2⟩) / (m : ℂ)
          - (N : ℂ)⁻¹ * X
        =
        (((q : ℂ)⁻¹ / (m : ℂ) - (N : ℂ)⁻¹) * X) := by
      simp [A, X]
      ring
    have hX : ‖X‖ ≤ q := by
      calc
        ‖X‖ ≤ ∑ k ∈ Finset.range q,
            ‖a ⟨m * (k + 1), Nat.mul_pos hm (Nat.zero_lt_succ k)⟩‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.range q, (1 : ℝ) := Finset.sum_le_sum (fun k _ => ha _)
        _ = q := by simp
    have hqm : q * m ≤ N := Nat.div_mul_le_self N m
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have hqposr : (0 : ℝ) < q := by exact_mod_cast hqpos
    have hNposr : (0 : ℝ) < N := by exact_mod_cast hN
    have hdelta :
        ((q : ℂ)⁻¹ / (m : ℂ) - (N : ℂ)⁻¹)
          =
        (((((N - q * m : ℕ) : ℝ) / (((q : ℝ) * m) * N)) : ℝ) : ℂ) := by
      have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hqpos.ne'
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have hcast : (((N - q * m : ℕ) : ℝ)) = (N : ℝ) - (q : ℝ) * m := by
        simpa [Nat.cast_mul] using
          (Nat.cast_sub hqm : (((N - q*m:ℕ):ℝ)) = (N:ℝ) - (q*m:ℕ))
      have hreal : ((q : ℝ)⁻¹ / m - (N : ℝ)⁻¹)
          = (((N - q*m:ℕ):ℝ)) / ((q:ℝ)*m*N) := by
        rw [hcast]
        field_simp [hq0, hm0, hN0]
      rw [show ((q : ℂ)⁻¹ / (m : ℂ) - (N : ℂ)⁻¹)
          = ((((q : ℝ)⁻¹ / m - (N : ℝ)⁻¹) : ℝ) : ℂ) by simp]
      exact congrArg Complex.ofReal hreal
    have hbound :
        (q : ℝ) * ‖((q : ℂ)⁻¹ / (m : ℂ) - (N : ℂ)⁻¹)‖ ≤ 1 / N := by
      rw [hdelta, Complex.norm_real, Real.norm_eq_abs]
      have hnon : 0 ≤ (((N - q * m : ℕ) : ℝ) / (((q : ℝ) * m) * N)) := by positivity
      rw [abs_of_nonneg hnon]
      have hcast : (((N - q * m : ℕ) : ℝ)) = (N : ℝ) - (q : ℝ) * m := by
        simpa [Nat.cast_mul] using
          (Nat.cast_sub hqm : (((N - q*m:ℕ):ℝ)) = (N:ℝ) - (q*m:ℕ))
      rw [hcast]
      calc
        q * ((N - q * m) / (q * m * N))
            = ((N : ℝ) - q * m) / (m * N) := by
              field_simp [hqposr.ne', hmpos.ne', hNposr.ne']
        _ ≤ 1 / N := by
              rw [div_le_iff₀ (mul_pos hmpos hNposr)]
              field_simp [hNposr.ne']
              have hmod : N - q * m = N % m := by
                dsimp [q]
                rw [Nat.mod_eq_sub_mul_div]
                rw [mul_comm]
              have hlt : N - q * m < m := by
                rw [hmod]
                exact Nat.mod_lt N hm
              have hltR : (N : ℝ) - q * m < m := by
                rw [← hcast]
                exact_mod_cast hlt
              linarith
    calc
      ‖A q (fun k ↦ a ⟨m * k.1, Nat.mul_pos hm k.2⟩) / (m : ℂ)
          - (N : ℂ)⁻¹ * X‖
          = ‖((q : ℂ)⁻¹ / (m : ℂ) - (N : ℂ)⁻¹) * X‖ := by rw [hrewrite]
      _ ≤ ‖((q : ℂ)⁻¹ / (m : ℂ) - (N : ℂ)⁻¹)‖ * ‖X‖ := norm_mul_le _ _
      _ ≤ ‖((q : ℂ)⁻¹ / (m : ℂ) - (N : ℂ)⁻¹)‖ * q :=
          mul_le_mul_of_nonneg_left hX (norm_nonneg _)
      _ = (q : ℝ) * ‖((q : ℂ)⁻¹ / (m : ℂ) - (N : ℂ)⁻¹)‖ := by ring
      _ ≤ 1 / N := hbound

/- accepted add_to_file helper 7 -/
lemma global_local_approx
    (B : Finset {n : ℕ // 0 < n}) (hB : B.Nonempty)
    (a : {n : ℕ // 0 < n} → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (N : ℕ) (hN : 0 < N) :
    let A : ℕ → ({n : ℕ // 0 < n} → ℂ) → ℂ := fun M c ↦
      (M : ℂ)⁻¹ * ∑ k ∈ Finset.range M, c ⟨k + 1, Nat.zero_lt_succ k⟩
    let S : ℝ := ∑ m ∈ B, 1 / (m.1 : ℝ)
    let Sℂ : ℂ := ∑ m ∈ B, 1 / (m.1 : ℂ)
    let actual : ℂ := ∑ m ∈ B,
      A (N / m.1) (fun k ↦ a ⟨m.1 * k.1, Nat.mul_pos m.2 k.2⟩) / (m.1 : ℂ)
    let ideal : ℂ := ∑ m ∈ B,
      (N : ℂ)⁻¹ * ∑ k ∈ Finset.range (N / m.1),
        a ⟨m.1 * (k + 1), Nat.mul_pos m.2 (Nat.zero_lt_succ k)⟩
    ‖(A N a - actual / Sℂ) - (A N a - ideal / Sℂ)‖
      ≤ (B.card : ℝ) / ((N : ℝ) * S) := by
  classical
  intro A S Sℂ actual ideal
  have hS : 0 < S := by
    apply Finset.sum_pos _ hB
    intro m hm
    exact one_div_pos.mpr (by exact_mod_cast m.2)
  have hScast : Sℂ = (S : ℂ) := by
    simp [Sℂ, S]
  have hdiff :
      (A N a - actual / Sℂ) - (A N a - ideal / Sℂ)
        = (ideal - actual) / Sℂ := by
    ring
  rw [hdiff, hScast]
  have hnormden : ‖(S : ℂ)‖ = S := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS]
  rw [norm_div, hnormden]
  have hsum :
      ‖ideal - actual‖ ≤ (B.card : ℝ) / N := by
    calc
      ‖ideal - actual‖ ≤ ∑ m ∈ B,
          ‖(N : ℂ)⁻¹ * ∑ k ∈ Finset.range (N / m.1),
              a ⟨m.1 * (k + 1), Nat.mul_pos m.2 (Nat.zero_lt_succ k)⟩
            -
            A (N / m.1) (fun k ↦ a ⟨m.1 * k.1, Nat.mul_pos m.2 k.2⟩) / (m.1 : ℂ)‖ := by
            simpa [ideal, actual, Finset.sum_sub_distrib] using
              (norm_sum_le B (fun m =>
                (N : ℂ)⁻¹ * ∑ k ∈ Finset.range (N / m.1),
                  a ⟨m.1 * (k + 1), Nat.mul_pos m.2 (Nat.zero_lt_succ k)⟩
                -
                A (N / m.1) (fun k ↦ a ⟨m.1 * k.1, Nat.mul_pos m.2 k.2⟩) / (m.1 : ℂ)))
      _ ≤ ∑ m ∈ B, 1 / (N : ℝ) := by
            refine Finset.sum_le_sum ?_
            intro m hm
            rw [norm_sub_rev]
            exact local_average_mul_approx a ha m.1 N m.2 hN
      _ = (B.card : ℝ) / N := by
            rw [Finset.sum_const]
            simp [nsmul_eq_mul]
            ring
  have hSnonneg : 0 ≤ S := le_of_lt hS
  calc
    ‖ideal - actual‖ / S ≤ ((B.card : ℝ) / N) / S :=
      div_le_div_of_nonneg_right hsum hSnonneg
    _ = (B.card : ℝ) / ((N : ℝ) * S) := by ring

/- accepted add_to_file helper 8 -/
lemma weighted_prefix_eq
    (B : Finset {n : ℕ // 0 < n})
    (a : {n : ℕ // 0 < n} → ℂ)
    (N : ℕ) :
    let A : ℕ → ({n : ℕ // 0 < n} → ℂ) → ℂ := fun M c ↦
      (M : ℂ)⁻¹ * ∑ k ∈ Finset.range M, c ⟨k + 1, Nat.zero_lt_succ k⟩
    let S : ℝ := ∑ m ∈ B, 1 / (m.1 : ℝ)
    let Sℂ : ℂ := ∑ m ∈ B, 1 / (m.1 : ℂ)
    let ideal : ℂ := ∑ m ∈ B,
      (N : ℂ)⁻¹ * ∑ k ∈ Finset.range (N / m.1),
        a ⟨m.1 * (k + 1), Nat.mul_pos m.2 (Nat.zero_lt_succ k)⟩
    let w : ℕ → ℝ := fun j ↦
      1 - (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) / S
    A N a - ideal / Sℂ
      =
    (N : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
      a ⟨j + 1, Nat.zero_lt_succ j⟩ * (w j : ℂ) := by
  classical
  intro A S Sℂ ideal w
  have hScast : Sℂ = (S : ℂ) := by
    simp [Sℂ, S]
  have hlocal : ∀ m ∈ B,
      (∑ k ∈ Finset.range (N / m.1),
          a ⟨m.1 * (k + 1), Nat.mul_pos m.2 (Nat.zero_lt_succ k)⟩)
        =
      ∑ j ∈ Finset.range N,
        if m.1 ∣ j + 1 then a ⟨j + 1, Nat.zero_lt_succ j⟩ else 0 := by
    intro m hm
    exact sum_range_mul_eq_sum_filter m.1 N m.2 a
  have hideal :
      ideal =
        (N : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
          a ⟨j + 1, Nat.zero_lt_succ j⟩ *
            ((∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) : ℂ) := by
    calc
      ideal = ∑ m ∈ B, (N : ℂ)⁻¹ *
          (∑ j ∈ Finset.range N,
            if m.1 ∣ j + 1 then a ⟨j + 1, Nat.zero_lt_succ j⟩ else 0) := by
          refine Finset.sum_congr (M := ℂ) rfl ?_
          intro m hm
          rw [hlocal m hm]
      _ = (N : ℂ)⁻¹ * ∑ m ∈ B, ∑ j ∈ Finset.range N,
          (if m.1 ∣ j + 1 then a ⟨j + 1, Nat.zero_lt_succ j⟩ else 0) := by
          rw [Finset.mul_sum]
      _ = (N : ℂ)⁻¹ * ∑ j ∈ Finset.range N, ∑ m ∈ B,
          (if m.1 ∣ j + 1 then a ⟨j + 1, Nat.zero_lt_succ j⟩ else 0) := by
          exact congrArg _ (Finset.sum_comm (s := B) (t := Finset.range N)
            (f := fun m j => if m.1 ∣ j + 1 then a ⟨j + 1, Nat.zero_lt_succ j⟩ else 0))
      _ = (N : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
          a ⟨j + 1, Nat.zero_lt_succ j⟩ *
            ((∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) : ℂ) := by
          refine congrArg _ ?_
          refine Finset.sum_congr (M := ℂ) rfl ?_
          intro j hj
          rw [Finset.mul_sum]
          refine Finset.sum_congr (M := ℂ) rfl ?_
          intro m hm
          by_cases h : m.1 ∣ j + 1 <;> simp [h]
  let X : ℕ → ℂ := fun j => a ⟨j + 1, Nat.zero_lt_succ j⟩
  let Y : ℕ → ℂ := fun j =>
    a ⟨j + 1, Nat.zero_lt_succ j⟩ *
      ((∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) : ℂ)
  have hsub :
      (∑ j ∈ Finset.range N, (X j - Y j / (S : ℂ)))
        = (∑ j ∈ Finset.range N, X j) - ∑ j ∈ Finset.range N, Y j / (S : ℂ) := by
    exact Finset.sum_sub_distrib (ι := ℕ) (G := ℂ) (s := Finset.range N)
      (f := X) (g := fun j => Y j / (S : ℂ))
  have hdiv :
      ((∑ j ∈ Finset.range N, Y j) / (S : ℂ))
        = ∑ j ∈ Finset.range N, Y j / (S : ℂ) := by
    exact Finset.sum_div (ι := ℕ) (K := ℂ) (s := Finset.range N)
      (f := Y) (a := (S : ℂ))
  have hweighted :
      (∑ j ∈ Finset.range N, X j * (w j : ℂ))
        = (∑ j ∈ Finset.range N, X j) - (S : ℂ)⁻¹ * ∑ j ∈ Finset.range N, Y j := by
    calc
      (∑ j ∈ Finset.range N, X j * (w j : ℂ))
          = ∑ j ∈ Finset.range N, (X j - Y j / (S : ℂ)) := by
            refine Finset.sum_congr (M := ℂ) rfl ?_
            intro j hj
            simp [X, Y, w]
            ring
      _ = (∑ j ∈ Finset.range N, X j) - ∑ j ∈ Finset.range N, Y j / (S : ℂ) := hsub
      _ = (∑ j ∈ Finset.range N, X j) - (∑ j ∈ Finset.range N, Y j) / (S : ℂ) := by
            rw [hdiv]
      _ = (∑ j ∈ Finset.range N, X j) - (S : ℂ)⁻¹ * ∑ j ∈ Finset.range N, Y j := by
            ring
  rw [hideal, hScast, hweighted]
  change ((N : ℂ)⁻¹ * ∑ j ∈ Finset.range N, X j)
      - (((N : ℂ)⁻¹ * ∑ j ∈ Finset.range N, Y j) / (S : ℂ))
      =
    (N : ℂ)⁻¹ *
      ((∑ j ∈ Finset.range N, X j) - (S : ℂ)⁻¹ * ∑ j ∈ Finset.range N, Y j)
  ring

/- verified submission -/
theorem logarithmic_average_bound
    (B : Finset {n : ℕ // 0 < n}) (hB : B.Nonempty)
    (a : {n : ℕ // 0 < n} → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) :
    let A : ℕ → ({n : ℕ // 0 < n} → ℂ) → ℂ := fun N c ↦
      (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, c ⟨k + 1, Nat.zero_lt_succ k⟩
    let Lℂ : ({n : ℕ // 0 < n} → ℂ) → ℂ := fun h ↦
      (∑ m ∈ B, h m / (m.1 : ℂ)) / (∑ m ∈ B, 1 / (m.1 : ℂ))
    let Lℝ : ({n : ℕ // 0 < n} → ℝ) → ℝ := fun h ↦
      (∑ m ∈ B, h m / (m.1 : ℝ)) / (∑ m ∈ B, 1 / (m.1 : ℝ))
    Filter.limsup
        (fun N : ℕ ↦ ‖A N a - Lℂ (fun m ↦
          A (N / m.1) (fun k ↦ a ⟨m.1 * k.1, Nat.mul_pos m.2 k.2⟩))‖)
        Filter.atTop ≤
      Real.sqrt (Lℝ (fun m ↦ Lℝ (fun n ↦ (Nat.gcd n.1 m.1 : ℝ) - 1))) := by
  classical
  intro A Lℂ Lℝ
  let q : ℕ := ∏ m ∈ B, m.1
  let S : ℝ := ∑ m ∈ B, 1 / (m.1 : ℝ)
  let Sℂ : ℂ := ∑ m ∈ B, 1 / (m.1 : ℂ)
  let w : ℕ → ℝ := fun j ↦
    1 - (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) / S
  let T : ℝ := ∑ j ∈ Finset.range q, |w j|
  let target : ℝ := Lℝ (fun m ↦ Lℝ (fun n ↦ (Nat.gcd n.1 m.1 : ℝ) - 1))
  let K : ℝ := T + (B.card : ℝ) / S
  have hq : 0 < q := Finset.prod_pos (fun m _ => m.2)
  have hS : 0 < S := by
    apply Finset.sum_pos _ hB
    intro m hm
    exact one_div_pos.mpr (by exact_mod_cast m.2)
  have hT : 0 ≤ T := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hperiod : ∀ i j, w (i * q + j) = w j := by
    intro i j
    dsimp [w]
    congr 2
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hmq : m.1 ∣ q := Finset.dvd_prod_of_mem (fun x => x.1) hm
    have hmiq : m.1 ∣ i * q := dvd_trans hmq (dvd_mul_left q i)
    have hiff : m.1 ∣ i * q + j + 1 ↔ m.1 ∣ j + 1 := by
      have h := Nat.dvd_add_iff_right hmiq (n := j + 1)
      simpa [add_assoc, add_comm, add_left_comm] using h.symm
    simp [hiff]
  have htarget_period :
      target =
        (q : ℝ)⁻¹ * ∑ j ∈ Finset.range q, (w j) ^ 2 := by
    have hp := period_weight_square_avg B hB
    have hn := nested_log_avg_gcd B hB
    dsimp [target, Lℝ, q, S, w]
    rw [hp, hn]
  have hboundN : ∀ N, 0 < N →
      ‖A N a - Lℂ (fun m ↦
          A (N / m.1) (fun k ↦ a ⟨m.1 * k.1, Nat.mul_pos m.2 k.2⟩))‖
        ≤ Real.sqrt target + K / N := by
    intro N hN
    let actual : ℂ := Lℂ (fun m ↦
      A (N / m.1) (fun k ↦ a ⟨m.1 * k.1, Nat.mul_pos m.2 k.2⟩))
    let ideal : ℂ := ∑ m ∈ B,
      (N : ℂ)⁻¹ * ∑ k ∈ Finset.range (N / m.1),
        a ⟨m.1 * (k + 1), Nat.mul_pos m.2 (Nat.zero_lt_succ k)⟩
    let adj : ℂ := A N a - ideal / Sℂ
    have happ :
        ‖(A N a - actual) - adj‖ ≤ (B.card : ℝ) / ((N : ℝ) * S) := by
      have hg := global_local_approx B hB a ha N hN
      dsimp [actual, adj, ideal, Lℂ, Sℂ, A] at *
      exact hg
    have hadj :
        adj = (N : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
          a ⟨j + 1, Nat.zero_lt_succ j⟩ * (w j : ℂ) := by
      have hw := weighted_prefix_eq B a N
      dsimp [adj, ideal, S, Sℂ, w, A] at *
      exact hw
    have hweighted :
        ‖adj‖ ≤ Real.sqrt target + T / N := by
      have hp := weighted_prefix_bound_generic a ha q hq w hperiod N hN
      dsimp [T] at hp
      rw [hadj]
      calc
        ‖(N : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
            a ⟨j + 1, Nat.zero_lt_succ j⟩ * (w j : ℂ)‖
            ≤ Real.sqrt ((q : ℝ)⁻¹ * ∑ j ∈ Finset.range q, (w j) ^ 2) + T / N := hp
        _ = Real.sqrt target + T / N := by rw [htarget_period]
    have htri :
        ‖A N a - actual‖ ≤ ‖adj‖ + ‖(A N a - actual) - adj‖ := by
      calc
        ‖A N a - actual‖ = ‖adj + ((A N a - actual) - adj)‖ := by
          congr 1
          abel
        _ ≤ ‖adj‖ + ‖(A N a - actual) - adj‖ := norm_add_le _ _
    calc
      ‖A N a - actual‖ ≤ ‖adj‖ + ‖(A N a - actual) - adj‖ := htri
      _ ≤ (Real.sqrt target + T / N) + (B.card : ℝ) / ((N : ℝ) * S) :=
          add_le_add hweighted happ
      _ = Real.sqrt target + K / N := by
          dsimp [K]
          field_simp [hS.ne']
          ring
  have hmain : ∀ ε : ℝ, 0 < ε →
      Filter.limsup
        (fun N : ℕ ↦ ‖A N a - Lℂ (fun m ↦
          A (N / m.1) (fun k ↦ a ⟨m.1 * k.1, Nat.mul_pos m.2 k.2⟩))‖)
        Filter.atTop ≤ Real.sqrt target + ε := by
    intro ε hε
    have hlim : Filter.Tendsto (fun N : ℕ => K / (N : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat K
    have hsmall : ∀ᶠ N : ℕ in Filter.atTop, K / (N : ℝ) < ε :=
      hlim.eventually_lt_const hε
    have hpos : ∀ᶠ N : ℕ in Filter.atTop, 0 < N :=
      (Filter.eventually_ge_atTop 1).mono (fun N hN => hN)
    have hev : ∀ᶠ N : ℕ in Filter.atTop,
        ‖A N a - Lℂ (fun m ↦
          A (N / m.1) (fun k ↦ a ⟨m.1 * k.1, Nat.mul_pos m.2 k.2⟩))‖
          ≤ Real.sqrt target + ε := by
      filter_upwards [hpos, hsmall] with N hN hs
      exact (hboundN N hN).trans (add_le_add le_rfl hs.le)
    exact Filter.limsup_le_of_le
      (Filter.isCoboundedUnder_le_of_eventually_le Filter.atTop
        (Filter.Eventually.of_forall (fun N => norm_nonneg _))) hev
  exact le_of_forall_pos_le_add hmain


#check_dependency_graph "logarithmic_average_bound" against "{\"edges\":[{\"conclusion\":{\"name\":\"hq\",\"statement\":\"0 < q\"},\"graphEdgeId\":\"h_001_hq\",\"premises\":[],\"rawEdgeId\":\"telescope_14\"},{\"conclusion\":{\"name\":\"hS\",\"statement\":\"0 < S\"},\"graphEdgeId\":\"h_002_hs\",\"premises\":[{\"name\":\"hB\",\"statement\":\"B.Nonempty\"}],\"rawEdgeId\":\"telescope_15\"},{\"conclusion\":{\"name\":\"hperiod\",\"statement\":\"∀ (i j : ℕ), w (i * q + j) = w j\"},\"graphEdgeId\":\"h_005_hperiod\",\"premises\":[],\"rawEdgeId\":\"telescope_18\"},{\"conclusion\":{\"name\":\"htarget_period\",\"statement\":\"target = (↑q)⁻¹ * ∑ j ∈ Finset.range q, w j ^ 2\"},\"graphEdgeId\":\"h_006_htarget_period\",\"premises\":[{\"name\":\"hB\",\"statement\":\"B.Nonempty\"}],\"rawEdgeId\":\"telescope_19\"},{\"conclusion\":{\"name\":\"hboundN\",\"statement\":\"∀ (N : ℕ), 0 < N → ‖A N a - Lℂ fun m => A (N / ↑m) fun k => a ⟨↑m * ↑k, ⋯⟩‖ ≤ √target + K / ↑N\"},\"graphEdgeId\":\"h_007_hboundn\",\"premises\":[{\"name\":\"hB\",\"statement\":\"B.Nonempty\"},{\"name\":\"ha\",\"statement\":\"∀ (n : { n // 0 < n }), ‖a n‖ ≤ 1\"},{\"name\":\"hq\",\"statement\":\"0 < q\"},{\"name\":\"hS\",\"statement\":\"0 < S\"},{\"name\":\"hperiod\",\"statement\":\"∀ (i j : ℕ), w (i * q + j) = w j\"},{\"name\":\"htarget_period\",\"statement\":\"target = (↑q)⁻¹ * ∑ j ∈ Finset.range q, w j ^ 2\"}],\"rawEdgeId\":\"telescope_20\"},{\"conclusion\":{\"name\":\"hmain\",\"statement\":\"∀ (ε : ℝ), 0 < ε → Filter.limsup (fun N => ‖A N a - Lℂ fun m => A (N / ↑m) fun k => a ⟨↑m * ↑k, ⋯⟩‖) Filter.atTop ≤ √target + ε\"},\"graphEdgeId\":\"h_008_hmain\",\"premises\":[{\"name\":\"hboundN\",\"statement\":\"∀ (N : ℕ), 0 < N → ‖A N a - Lℂ fun m => A (N / ↑m) fun k => a ⟨↑m * ↑k, ⋯⟩‖ ≤ √target + K / ↑N\"}],\"rawEdgeId\":\"telescope_21\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"Filter.limsup (fun N => ‖A N a - Lℂ fun m => A (N / ↑m) fun k => a ⟨↑m * ↑k, ⋯⟩‖) Filter.atTop ≤ √(Lℝ fun m => Lℝ fun n => ↑((↑n).gcd ↑m) - 1)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hmain\",\"statement\":\"∀ (ε : ℝ), 0 < ε → Filter.limsup (fun N => ‖A N a - Lℂ fun m => A (N / ↑m) fun k => a ⟨↑m * ↑k, ⋯⟩‖) Filter.atTop ≤ √target + ε\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1089_logarithmic_average_bound\",\"reconstructedProofSha256\":\"c6fbcb13365678ea7f4ec991d10ff76066d8d782cca0b446b954f8b737f3882f\",\"selectedEdgeCount\":7,\"theoremName\":\"logarithmic_average_bound\",\"topologySha256\":\"3b0de1941c8929d9339458ece58933b5a7be4f50c1f8629973513c008d4dd8c3\"}"
