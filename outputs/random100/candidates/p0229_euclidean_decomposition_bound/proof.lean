import Mathlib

/- verified submission -/
theorem euclidean_decomposition_bound (n e p : ℕ) (hn : 0 < n) (he : 0 < e)
    (hp : Nat.Prime p) (hsize : 4 * p ^ 2 ≤ n + 2) (hep : e ≤ p + 1) :
    ∃ d f : ℕ, f < p ∧ n + 2 = p * d + f + e ∧
      d ≥ e + f + (2 * p - 2) := by
  have hp0 : 0 < p := hp.pos
  have hp2 : 2 ≤ p := hp.two_le
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp2
  have hm : e ≤ n + 2 := by
    have hp_sq : 2 + q + 1 ≤ 4 * (2 + q) ^ 2 := by
      nlinarith
    exact le_trans hep (le_trans hp_sq hsize)
  let d := (n + 2 - e) / (2 + q)
  let f := (n + 2 - e) % (2 + q)
  have hf : f < 2 + q := by
    dsimp [f]
    exact Nat.mod_lt _ (by omega)
  have hdiv : (2 + q) * d + f = n + 2 - e := by
    dsimp [d, f]
    exact Nat.div_add_mod (n + 2 - e) (2 + q)
  have hdecomp : n + 2 = (2 + q) * d + f + e := by
    calc
      n + 2 = (n + 2 - e) + e := (Nat.sub_add_cancel hm).symm
      _ = ((2 + q) * d + f) + e := by rw [hdiv]
      _ = (2 + q) * d + f + e := rfl
  have hd4 : 4 * (2 + q) - 2 ≤ d := by
    dsimp [d]
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2 + q)).mpr
    have hmul : (4 * (2 + q) - 2) * (2 + q) ≤ n + 2 - e := by
      apply (Nat.le_sub_iff_add_le hm).mpr
      have hsub : 4 * (2 + q) - 2 = 6 + 4 * q := by omega
      rw [hsub]
      nlinarith
    exact hmul
  refine ⟨d, f, hf, hdecomp, ?_⟩
  have htarget : e + f + (2 * (2 + q) - 2) ≤ 4 * (2 + q) - 2 := by
    omega
  exact le_trans htarget hd4
