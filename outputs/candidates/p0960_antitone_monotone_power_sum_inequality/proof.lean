import Mathlib

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
