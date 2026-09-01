import Mathlib

/- accepted add_to_file helper 1 -/
lemma strict_combination_pos {a b x y : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : 0 < x) (hy : 0 < y) :
    0 < a * x + b * y := by
  by_cases h : a = 0
  · have hb' : b = 1 := by linarith
    rw [h, hb']
    simpa using hy
  · have ha' : 0 < a := lt_of_le_of_ne ha (fun hzero => h hzero.symm)
    exact add_pos_of_pos_of_nonneg (mul_pos ha' hx)
      (mul_nonneg hb (le_of_lt hy))

lemma strict_combination_neg {a b x y : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : x < 0) (hy : y < 0) :
    a * x + b * y < 0 := by
  have hpos : 0 < a * (-x) + b * (-y) :=
    strict_combination_pos ha hb hab (neg_pos.mpr hx) (neg_pos.mpr hy)
  linarith

/- verified submission -/
theorem paired_complex_tuple_set_convex
    (l m : ℕ) (hl : 0 < l) (hm : 0 < m)
    (σ : Fin (l + m) → Fin (l + m))
    (hσ_involutive : Function.Involutive σ)
    (hσ_fixedPointFree : ∀ i, σ i ≠ i) :
    Convex ℝ {ζ : Fin (l + m) → ℂ |
      (∀ i, ζ i = ζ (σ i)) ∧
      (∀ i, 0 < (ζ i).re) ∧
      (∀ i : ℕ, 1 ≤ i → i < l →
        0 < (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => k.val < i), ζ k).im) ∧
      (∀ j : ℕ, 1 ≤ j → j < m →
        (∑ k ∈ Finset.univ.filter
          (fun k : Fin (l + m) => l ≤ k.val ∧ k.val < l + j), ζ k).im < 0) ∧
      (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => k.val < l), ζ k) =
        ∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => l ≤ k.val), ζ k} := by
  intro ζ hζ η hη a b ha hb hab
  constructor
  · intro i
    have hzi := hζ.1 i
    have hei := hη.1 i
    simp [Pi.add_apply, Pi.smul_apply, hzi, hei]
  · constructor
    · intro i
      simpa [Pi.add_apply, Pi.smul_apply] using
        strict_combination_pos ha hb hab (hζ.2.1 i) (hη.2.1 i)
    · constructor
      · intro i hi1 hil
        simpa [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, Finset.mul_sum] using
          strict_combination_pos ha hb hab
            (hζ.2.2.1 i hi1 hil) (hη.2.2.1 i hi1 hil)
      · constructor
        · intro j hj1 hjm
          simpa [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, Finset.mul_sum] using
            strict_combination_neg ha hb hab
              (hζ.2.2.2.1 j hj1 hjm) (hη.2.2.2.1 j hj1 hjm)
        · have hzsum := hζ.2.2.2.2
          have hηsum := hη.2.2.2.2
          have hleft :
              (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => k.val < l),
                  (a • ζ + b • η) k) =
                a * (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => k.val < l), ζ k) +
                  b * (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => k.val < l), η k) := by
            simp [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, Finset.mul_sum]
          have hright :
              (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => l ≤ k.val),
                  (a • ζ + b • η) k) =
                a * (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => l ≤ k.val), ζ k) +
                  b * (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => l ≤ k.val), η k) := by
            simp [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, Finset.mul_sum]
          calc
            (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => k.val < l),
                (a • ζ + b • η) k)
                = a * (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => k.val < l), ζ k) +
                    b * (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => k.val < l), η k) :=
              hleft
            _ = a * (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => l ≤ k.val), ζ k) +
                    b * (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => l ≤ k.val), η k) := by
              rw [hzsum, hηsum]
            _ = ∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => l ≤ k.val),
                    (a • ζ + b • η) k :=
              hright.symm
