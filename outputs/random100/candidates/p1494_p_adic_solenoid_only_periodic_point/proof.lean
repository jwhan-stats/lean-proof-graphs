import Mathlib

/- accepted add_to_file helper 1 -/
lemma solenoid_iterate_apply (k m : ℕ) (z : ℕ → ℂ) (n : ℕ) :
    ((fun w : ℕ → ℂ => fun n => w n ^ k)^[m] z) n = z n ^ k ^ m := by
  induction m generalizing z with
  | zero =>
      simp
  | succ m ih =>
      rw [Function.iterate_succ_apply]
      rw [ih (fun n => z n ^ k)]
      simp [pow_succ, pow_mul, mul_comm]

lemma pow_sub_one_eq_one_of_pow_eq_self
    (a : ℂ) (ha : a ≠ 0) {K : ℕ} (hK : 0 < K) (h : a ^ K = a) :
    a ^ (K - 1) = 1 := by
  have hK' : K = K - 1 + 1 := (Nat.succ_pred_eq_of_pos hK).symm
  have hpow : a ^ (K - 1) * a = a ^ K := by
    rw [← pow_succ, ← hK']
  have hmul : a ^ (K - 1) * a = 1 * a := by
    calc
      a ^ (K - 1) * a = a ^ K := hpow
      _ = a := h
      _ = 1 * a := by rw [one_mul]
  exact mul_right_cancel₀ ha hmul

lemma prime_power_order_forward
    (z : ℕ → ℂ) (P : ℕ → ℕ)
    (hcompat : ∀ n, z n = z (n + 1) ^ P n)
    {p a N j : ℕ} (hle : N ≤ j)
    (hdiv : p ^ a ∣ orderOf (z N)) :
    p ^ a ∣ orderOf (z j) := by
  induction hle with
  | refl => exact hdiv
  | step hle ih =>
      rename_i n
      have hpow_dvd : orderOf (z (n + 1) ^ P n) ∣ orderOf (z (n + 1)) :=
        orderOf_pow_dvd (P n)
      have hord_eq : orderOf (z n) = orderOf (z (n + 1) ^ P n) := by
        rw [hcompat n]
      exact dvd_trans ih (hord_eq.symm ▸ hpow_dvd)

lemma prime_power_order_of_prime_power
    (x : ℂ) {p a : ℕ} (hp : Nat.Prime p) (ha : 0 < a)
    (h : p ^ a ∣ orderOf (x ^ p)) :
    p ^ (a + 1) ∣ orderOf x := by
  have hd : p ^ a ∣ orderOf x := dvd_trans h (orderOf_pow_dvd p)
  have hp_dvd : p ∣ orderOf x :=
    dvd_trans (dvd_pow_self p (Nat.ne_of_gt ha)) hd
  have hgcd : Nat.gcd (orderOf x) p = p := Nat.gcd_eq_right hp_dvd
  have hquot : p ^ a ∣ orderOf x / p := by
    have h' := h
    rw [orderOf_pow' x hp.ne_zero, hgcd] at h'
    exact h'
  obtain ⟨c, hc⟩ := hp_dvd
  have hc_div : p * c / p = c := Nat.mul_div_cancel_left c hp.pos
  have hdivc : p ^ a ∣ c := by
    have h' := hquot
    rw [hc, hc_div] at h'
    exact h'
  obtain ⟨b, hb⟩ := hdivc
  use b
  rw [hc, hb]
  ring

lemma exists_prime_power_order_forward
    (P : ℕ → ℕ)
    (hP_recurrent : ∀ q, Nat.Prime q → ∀ N, ∃ n, N ≤ n ∧ P n = q)
    (z : ℕ → ℂ)
    (hcompat : ∀ n, z n = z (n + 1) ^ P n)
    {p : ℕ} (hp : Nat.Prime p)
    (a N : ℕ) (hdiv : p ∣ orderOf (z N)) :
    ∃ M, p ^ (a + 1) ∣ orderOf (z M) := by
  induction a generalizing N with
  | zero =>
      exact ⟨N, by simpa using hdiv⟩
  | succ a ih =>
      obtain ⟨M, hM⟩ := ih N hdiv
      obtain ⟨j, hMj, hPj⟩ := hP_recurrent p hp M
      have hdivj : p ^ (a + 1) ∣ orderOf (z j) :=
        prime_power_order_forward z P hcompat hMj hM
      have hdivpow : p ^ (a + 1) ∣ orderOf (z (j + 1) ^ p) := by
        rw [hcompat j, hPj] at hdivj
        exact hdivj
      have hnext : p ^ (a + 1 + 1) ∣ orderOf (z (j + 1)) :=
        prime_power_order_of_prime_power (z (j + 1)) hp (Nat.succ_pos a) hdivpow
      exact ⟨j + 1, hnext⟩

/- verified submission -/
theorem p_adic_solenoid_only_periodic_point
    (P : ℕ → ℕ)
    (hP_prime : ∀ n, Nat.Prime (P n))
    (hP_recurrent : ∀ q, Nat.Prime q → ∀ N, ∃ n, N ≤ n ∧ P n = q)
    (k : ℕ) (hk : 2 ≤ k) :
    ∀ z : ℕ → ℂ,
      ((∀ n, ‖z n‖ = 1) ∧
        ∀ n, z n = z (n + 1) ^ P n) →
      ((∃ m, 0 < m ∧
          Function.IsPeriodicPt (fun w : ℕ → ℂ => fun n => w n ^ k) m z) ↔
        z = fun _ => 1) := by
  intro z hz
  obtain ⟨hznorm, hcompat⟩ := hz
  constructor
  · rintro ⟨m, hm, hper⟩
    funext n
    have hKtwo : 2 ≤ k ^ m := by
      calc
        2 ≤ 2 ^ m := Nat.le_self_pow (Nat.ne_of_gt hm) 2
        _ ≤ k ^ m := Nat.pow_le_pow_left hk m
    have hKpos : 0 < k ^ m := by omega
    have ht : 0 < k ^ m - 1 := by omega
    have hfix : (fun w : ℕ → ℂ => fun n => w n ^ k)^[m] z = z := hper
    have hcoord : ∀ n, z n ^ k ^ m = z n := by
      intro n
      have hn := congrFun hfix n
      rwa [solenoid_iterate_apply k m z n] at hn
    have hroot : ∀ n, z n ^ (k ^ m - 1) = 1 := by
      intro n
      have hzne : z n ≠ 0 := by
        intro hz0
        have hnorm := hznorm n
        rw [hz0] at hnorm
        norm_num at hnorm
      exact pow_sub_one_eq_one_of_pow_eq_self (z n) hzne hKpos (hcoord n)
    by_contra hzn
    have hord_ne_one : orderOf (z n) ≠ 1 := by
      intro hord
      exact hzn (orderOf_eq_one_iff.mp hord)
    obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hord_ne_one
    obtain ⟨M, hM⟩ :=
      exists_prime_power_order_forward P hP_recurrent z hcompat hr (k ^ m - 1) n hrdvd
    have hfin : IsOfFinOrder (z M) := by
      exact isOfFinOrder_iff_pow_eq_one.mpr ⟨k ^ m - 1, ht, hroot M⟩
    have hordMpos : 0 < orderOf (z M) := orderOf_pos_iff.mpr hfin
    have hpow_le : r ^ (k ^ m - 1 + 1) ≤ orderOf (z M) :=
      Nat.le_of_dvd hordMpos hM
    have horder_le : orderOf (z M) ≤ k ^ m - 1 :=
      orderOf_le_of_pow_eq_one ht (hroot M)
    have hpow_le_t : r ^ (k ^ m - 1 + 1) ≤ k ^ m - 1 :=
      le_trans hpow_le horder_le
    have hbig : k ^ m - 1 < r ^ (k ^ m - 1 + 1) := by
      exact lt_trans (Nat.lt_succ_self (k ^ m - 1)) (Nat.lt_pow_self hr.two_le)
    exact (not_lt_of_ge hpow_le_t) hbig
  · intro hz1
    refine ⟨1, Nat.one_pos, ?_⟩
    rw [hz1]
    simp [Function.IsPeriodicPt, Function.IsFixedPt]
