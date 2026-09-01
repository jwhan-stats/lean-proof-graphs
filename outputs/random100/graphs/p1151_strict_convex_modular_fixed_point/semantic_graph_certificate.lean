import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1151_strict_convex_modular_fixed_point
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: d75903c07f3cb6dafb1d31aa074ca2f36785d75d8e5ad8a06a5b6745d6002ea8
-- reconstructed_proof_sha256: cea97ffc432c413055eec64974cc014dba1d8d6801bcea53159b47603dfff4ec
-- selected_edge_count: 1

/- accepted add_to_file helper 1 -/
lemma modular_scale_le
    {X : Type*} (w : NNReal → X → X → ENNReal)
    (hself : ∀ (l : NNReal), 0 < l → ∀ x : X, w l x x = 0)
    (hconv : ∀ (l m : NNReal), 0 < l → 0 < m → ∀ x y z : X,
      w (l + m) x y ≤ ((l : ENNReal) / (l + m)) * w l x z +
        ((m : ENNReal) / (l + m)) * w m y z)
    {l s : NNReal} (hl : 0 < l) (hls : l ≤ s) (x y : X) :
    w s x y ≤ ((l : ENNReal) / (s : ENNReal)) * w l x y := by
  rcases eq_or_lt_of_le hls with rfl | hlt
  · have h0 : (l : ENNReal) ≠ 0 := by exact_mod_cast ne_of_gt hl
    have htop : (l : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    simp [ENNReal.div_self h0 htop]
  · let d : NNReal := s - l
    have hd : 0 < d := tsub_pos_of_lt hlt
    have hsd : l + d = s := add_tsub_cancel_of_le hls
    have h := hconv l d hl hd x y y
    rw [hsd, hself d hd y, mul_zero, add_zero] at h
    rw [← ENNReal.coe_add, hsd] at h
    exact h

lemma ennreal_add_coe_mul_div_sub_self {d : ENNReal} {k : NNReal}
    (hk : (k : ENNReal) < 1) :
    d + (k : ENNReal) * (d / (1 - (k : ENNReal))) =
      d / (1 - (k : ENNReal)) := by
  let e : ENNReal := 1 - (k : ENNReal)
  have he0 : e ≠ 0 := by
    dsimp [e]
    exact ne_of_gt (tsub_pos_of_lt hk)
  have het : e ≠ ⊤ := by
    dsimp [e]
    exact ENNReal.sub_ne_top (by simp)
  have hek : e + (k : ENNReal) = 1 := by
    dsimp [e]
    exact tsub_add_cancel_of_le hk.le
  have hinv : e * e⁻¹ = 1 := ENNReal.mul_inv_cancel he0 het
  calc
    d + (k : ENNReal) * (d / e)
        = d * 1 + (k : ENNReal) * (d * e⁻¹) := by rw [div_eq_mul_inv, mul_one]
    _ = d * (e * e⁻¹) + (k : ENNReal) * (d * e⁻¹) := by rw [hinv]
    _ = e * (d * e⁻¹) + (k : ENNReal) * (d * e⁻¹) := by
          congr 1
          calc
            d * (e * e⁻¹) = (d * e) * e⁻¹ := by rw [mul_assoc]
            _ = (e * d) * e⁻¹ := by rw [mul_comm d e]
            _ = e * (d * e⁻¹) := by rw [mul_assoc]
    _ = (e + (k : ENNReal)) * (d * e⁻¹) := by rw [add_mul]
    _ = d / e := by rw [hek, one_mul, div_eq_mul_inv]

/- accepted add_to_file helper 2 -/
lemma tendsto_ennreal_const_mul_pow_min_zero {C : ENNReal} (hC : C ≠ ⊤)
    {k : NNReal} (hk : k < 1) :
    Filter.Tendsto (fun p : ℕ × ℕ => C * (k : ENNReal) ^ min p.1 p.2)
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
  have hmin : Filter.Tendsto (fun p : ℕ × ℕ => min p.1 p.2)
      (Filter.atTop ×ˢ Filter.atTop) Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro N
    filter_upwards [Filter.tendsto_fst.eventually_ge_atTop N,
      Filter.tendsto_snd.eventually_ge_atTop N] with p hp1 hp2
    exact le_min hp1 hp2
  have hpow : Filter.Tendsto (fun n : ℕ => (k : ℝ) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (NNReal.coe_nonneg k) (by exact_mod_cast hk)
  have hreal : Filter.Tendsto
      (fun p : ℕ × ℕ => C.toReal * (k : ℝ) ^ min p.1 p.2)
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
    simpa using Filter.Tendsto.const_mul C.toReal (hpow.comp hmin)
  have hreal' : Filter.Tendsto
      (fun p : ℕ × ℕ => (C * (k : ENNReal) ^ min p.1 p.2).toReal)
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
    convert hreal using 1
    ext p
    simp [ENNReal.toReal_mul, ← ENNReal.coe_pow]
  exact (ENNReal.tendsto_toReal_zero_iff (fun p => by
    exact ENNReal.mul_ne_top hC (by
      rw [← ENNReal.coe_pow]
      exact ENNReal.coe_ne_top))).1 hreal'

/- accepted add_to_file helper 3 -/
lemma modular_fixed_point_of_displacement
    {X : Type*} (b : X) (w : NNReal → X → X → ENNReal)
    (hself : ∀ (l : NNReal), 0 < l → ∀ x : X, w l x x = 0)
    (hsymm : ∀ (l : NNReal), 0 < l → ∀ x y : X, w l x y = w l y x)
    (hstrict : ∀ x y : X, (∃ l : NNReal, 0 < l ∧ w l x y = 0) → x = y)
    (hconv : ∀ (l m : NNReal), 0 < l → 0 < m → ∀ x y z : X,
      w (l + m) x y ≤ ((l : ENNReal) / (l + m)) * w l x z +
        ((m : ENNReal) / (l + m)) * w m y z)
    (hcomplete : ∀ (x : ℕ → {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤})
      (l : NNReal), 0 < l →
      Filter.Tendsto (fun p : ℕ × ℕ => w l (x p.1) (x p.2))
        (Filter.atTop ×ˢ Filter.atTop) (nhds 0) →
      ∃ y : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
        Filter.Tendsto (fun n => w l (x n) y) Filter.atTop (nhds 0))
    (T : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤} →
      {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤})
    {k L : NNReal} (hk0 : 0 < k) (hk1 : k < 1) (hL0 : 0 < L)
    (hcontr : ∀ x y : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
      ∀ l : NNReal, 0 < l → l ≤ L → w (k * l) (T x) (T y) ≤ w l x y)
    (x0 : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤})
    (hdisp : w ((1 - (1 + k) / 2) * L) x0 (T x0) < ⊤) :
    ∃ y : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
      T y = y ∧
      Filter.Tendsto (fun n : ℕ => w L ((T^[n]) x0) y)
        Filter.atTop (nhds 0) := by
  let q : NNReal := (1 + k) / 2
  let r : NNReal := k / q
  let a : NNReal := (1 - q) * L
  let lam : ℕ → NNReal := fun n => a * q ^ n
  let S : ℕ → NNReal := fun n => L * q ^ n
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hkq : k < q := by dsimp [q]; nlinarith [hk0, hk1]
  have hq1 : q < 1 := by dsimp [q]; nlinarith [hk1]
  have hr1 : r < 1 := by dsimp [r]; rw [div_lt_one hq0]; exact hkq
  have hqr : q * r = k := by
    dsimp [r]; rw [mul_comm]; exact div_mul_cancel₀ k (ne_of_gt hq0)
  have ha0 : 0 < a := by dsimp [a]; exact mul_pos (tsub_pos_of_lt hq1) hL0
  have hlam0 : ∀ n, 0 < lam n := by intro n; dsimp [lam]; exact mul_pos ha0 (pow_pos hq0 n)
  have hlam_le : ∀ n, lam n ≤ L := by
    intro n
    have h1 : 1 - q ≤ (1 : NNReal) := tsub_le_self
    have h2 : q ^ n ≤ (1 : NNReal) := pow_le_one₀ hq0.le hq1.le
    dsimp [lam, a]
    calc
      (1 - q) * L * q ^ n ≤ (1 - q) * L * 1 := mul_le_mul_left' h2 ((1 - q) * L)
      _ ≤ (1 : NNReal) * L * 1 := mul_le_mul_right' (mul_le_mul_right' h1 L) 1
      _ = L := by ring
  have hS0 : ∀ n, 0 < S n := by intro n; dsimp [S]; exact mul_pos hL0 (pow_pos hq0 n)
  have hS_le : ∀ n, S n ≤ L := by
    intro n
    dsimp [S]
    calc
      L * q ^ n ≤ L * 1 := mul_le_mul_left' (pow_le_one₀ hq0.le hq1.le) L
      _ = L := mul_one L
  have hS_add : ∀ n, lam n + S (n + 1) = S n := by
    intro n
    dsimp [lam, S, a]
    calc
      (1 - q) * L * q ^ n + L * q ^ (n + 1)
          = ((1 - q) + q) * L * q ^ n := by rw [pow_succ]; ring
      _ = L * q ^ n := by rw [tsub_add_cancel_of_le hq1.le]; ring
  let d0 : ENNReal := w a x0 (T x0)
  have hd0 : d0 ≠ ⊤ := ne_of_lt hdisp
  have hgeom : ∀ n : ℕ,
      w (lam n) ((T^[n]) x0) ((T^[n + 1]) x0) ≤ d0 * (r : ENNReal) ^ n := by
    intro n
    induction n with
    | zero => simp [lam, a, d0]
    | succ n ih =>
        have hscale : w (lam (n + 1)) ((T^[n + 1]) x0) ((T^[n + 2]) x0) ≤
            (((k * lam n : NNReal) : ENNReal) / (lam (n + 1) : ENNReal)) *
              w (k * lam n) ((T^[n + 1]) x0) ((T^[n + 2]) x0) := by
          apply modular_scale_le w hself hconv
          · exact mul_pos hk0 (hlam0 n)
          · dsimp [lam]
            calc
              k * (a * q ^ n) ≤ q * (a * q ^ n) := by gcongr
              _ = a * q ^ (n + 1) := by rw [pow_succ]; ring
        have hcoeff : (((k * lam n : NNReal) : ENNReal) / (lam (n + 1) : ENNReal)) =
            (r : ENNReal) := by
          have hnext : (lam (n + 1) : ENNReal) = (q : ENNReal) * (lam n : ENNReal) := by
            dsimp [lam]; rw [pow_succ]; ring
          have hk_eq : (k : ENNReal) = (q : ENNReal) * (r : ENNReal) := by
            rw [← ENNReal.coe_mul, hqr]
          have hden : (q : ENNReal) * (lam n : ENNReal) ≠ 0 := by
            exact mul_ne_zero (by exact_mod_cast ne_of_gt hq0)
              (by exact_mod_cast ne_of_gt (hlam0 n))
          have hdenTop : (q : ENNReal) * (lam n : ENNReal) ≠ ⊤ :=
            ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
          calc
            (((k * lam n : NNReal) : ENNReal) / (lam (n + 1) : ENNReal))
                = ((k : ENNReal) * (lam n : ENNReal)) / ((q : ENNReal) * (lam n : ENNReal)) := by
                    rw [ENNReal.coe_mul, hnext]
            _ = (((q : ENNReal) * (r : ENNReal)) * (lam n : ENNReal)) /
                    ((q : ENNReal) * (lam n : ENNReal)) := by rw [hk_eq]
            _ = (r : ENNReal) := by
                    calc
                      (((q : ENNReal) * (r : ENNReal)) * (lam n : ENNReal)) /
                          ((q : ENNReal) * (lam n : ENNReal))
                          = (r : ENNReal) * ((q : ENNReal) * (lam n : ENNReal)) /
                              ((q : ENNReal) * (lam n : ENNReal)) := by ring
                      _ = (r : ENNReal) * 1 := by
                            rw [mul_div_assoc, ENNReal.div_self hden hdenTop]
                      _ = (r : ENNReal) := mul_one _
        have hctr0 := hcontr ((T^[n]) x0) ((T^[n + 1]) x0) (lam n) (hlam0 n) (hlam_le n)
        have hctr : w (k * lam n) ((T^[n + 1]) x0) ((T^[n + 2]) x0) ≤
            w (lam n) ((T^[n]) x0) ((T^[n + 1]) x0) := by
          simpa [Function.iterate_succ_apply'] using hctr0
        calc
          w (lam (n + 1)) ((T^[n + 1]) x0) ((T^[n + 2]) x0)
              ≤ (r : ENNReal) * w (k * lam n) ((T^[n + 1]) x0) ((T^[n + 2]) x0) := by
                  rw [← hcoeff]; exact hscale
          _ ≤ (r : ENNReal) * w (lam n) ((T^[n]) x0) ((T^[n + 1]) x0) :=
                  mul_le_mul_left' hctr _
          _ ≤ (r : ENNReal) * (d0 * (r : ENNReal) ^ n) := mul_le_mul_left' ih _
          _ = d0 * (r : ENNReal) ^ (n + 1) := by rw [pow_succ]; ring
  let C : ENNReal := d0 / (1 - (k : ENNReal))
  have hCeq : d0 + (k : ENNReal) * C = C := by
    dsimp [C]
    exact ennreal_add_coe_mul_div_sub_self (by exact_mod_cast hk1)
  have hCne : C ≠ ⊤ := by
    dsimp [C]
    apply ENNReal.div_ne_top hd0
    exact ne_of_gt (tsub_pos_of_lt (by exact_mod_cast hk1 : (k : ENNReal) < 1))
  have hlam_le_S : ∀ n, lam n ≤ S n := by
    intro n
    have haL : a ≤ L := by
      dsimp [a]
      calc
        (1 - q) * L ≤ 1 * L := mul_le_mul_right' tsub_le_self L
        _ = L := one_mul L
    dsimp [lam, S]
    exact mul_le_mul_right' haL (q ^ n)
  have hSratio : ∀ n, ((S (n + 1) : ENNReal) / (S n : ENNReal)) = (q : ENNReal) := by
    intro n
    have hnext : (S (n + 1) : ENNReal) = (q : ENNReal) * (S n : ENNReal) := by
      dsimp [S]; rw [pow_succ]; ring
    have hden : (S n : ENNReal) ≠ 0 := by exact_mod_cast ne_of_gt (hS0 n)
    have hdenTop : (S n : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    calc
      ((S (n + 1) : ENNReal) / (S n : ENNReal))
          = ((q : ENNReal) * (S n : ENNReal)) / (S n : ENNReal) := by rw [hnext]
      _ = (q : ENNReal) * ((S n : ENNReal) / (S n : ENNReal)) := by rw [mul_div_assoc]
      _ = (q : ENNReal) := by rw [ENNReal.div_self hden hdenTop, mul_one]
  have hpath : ∀ N n : ℕ,
      w (S n) ((T^[n]) x0) ((T^[n + N]) x0) ≤ C * (r : ENNReal) ^ n := by
    intro N
    induction N with
    | zero =>
        intro n
        simp [hself (S n) (hS0 n)]
    | succ N ih =>
        intro n
        have hcv0 := hconv (lam n) (S (n + 1)) (hlam0 n) (hS0 (n + 1))
          ((T^[n]) x0) ((T^[n + (N + 1)]) x0) ((T^[n + 1]) x0)
        rw [← ENNReal.coe_add, hS_add n] at hcv0
        have hcv : w (S n) ((T^[n]) x0) ((T^[n + (N + 1)]) x0) ≤
            ((lam n : ENNReal) / (S n : ENNReal)) *
              w (lam n) ((T^[n]) x0) ((T^[n + 1]) x0) +
            ((S (n + 1) : ENNReal) / (S n : ENNReal)) *
              w (S (n + 1)) ((T^[n + (N + 1)]) x0) ((T^[n + 1]) x0) := by
          simpa [hS_add n, Function.iterate_succ_apply'] using hcv0
        have hfirst : ((lam n : ENNReal) / (S n : ENNReal)) ≤ 1 := by
          have hdiv : lam n / S n ≤ (1 : NNReal) :=
            div_le_one_of_le₀ (hlam_le_S n) (zero_le _)
          rw [← ENNReal.coe_div (ne_of_gt (hS0 n))]
          exact_mod_cast hdiv
        have hidx : n + (N + 1) = (n + 1) + N := by omega
        have hs : w (S (n + 1)) ((T^[n + (N + 1)]) x0) ((T^[n + 1]) x0) =
            w (S (n + 1)) ((T^[n + 1]) x0) ((T^[n + (N + 1)]) x0) :=
          hsymm (S (n + 1)) (hS0 (n + 1)) _ _
        have hih : w (S (n + 1)) ((T^[n + 1]) x0) ((T^[n + (N + 1)]) x0) ≤
            C * (r : ENNReal) ^ (n + 1) := by
          simpa [hidx] using ih (n + 1)
        calc
          w (S n) ((T^[n]) x0) ((T^[n + (N + 1)]) x0)
              ≤ ((lam n : ENNReal) / (S n : ENNReal)) *
                  w (lam n) ((T^[n]) x0) ((T^[n + 1]) x0) +
                ((S (n + 1) : ENNReal) / (S n : ENNReal)) *
                  w (S (n + 1)) ((T^[n + (N + 1)]) x0) ((T^[n + 1]) x0) := hcv
          _ ≤ 1 * (d0 * (r : ENNReal) ^ n) +
                (q : ENNReal) * (C * (r : ENNReal) ^ (n + 1)) := by
                apply add_le_add
                · exact mul_le_mul hfirst (hgeom n) (zero_le _) (zero_le _)
                · rw [hSratio n, hs]
                  exact mul_le_mul_left' hih _
          _ = d0 * (r : ENNReal) ^ n +
                (q : ENNReal) * (C * (r : ENNReal) ^ (n + 1)) := by rw [one_mul]
          _ = (d0 + (k : ENNReal) * C) * (r : ENNReal) ^ n := by
                have hqrE : (q : ENNReal) * (r : ENNReal) = (k : ENNReal) := by
                  rw [← ENNReal.coe_mul, hqr]
                have h : (q : ENNReal) * (C * (r : ENNReal) ^ (n + 1)) =
                    ((k : ENNReal) * C) * (r : ENNReal) ^ n := by
                  calc
                    (q : ENNReal) * (C * (r : ENNReal) ^ (n + 1))
                        = ((q : ENNReal) * (r : ENNReal)) *
                            (C * (r : ENNReal) ^ n) := by rw [pow_succ]; ring
                    _ = ((k : ENNReal) * C) * (r : ENNReal) ^ n := by rw [hqrE]; ring
                rw [h, add_mul]
          _ = C * (r : ENNReal) ^ n := by rw [hCeq]
  have hSratioL : ∀ n, ((S n : ENNReal) / (L : ENNReal)) = (q : ENNReal) ^ n := by
    intro n
    dsimp [S]
    have h0 : (L : ENNReal) ≠ 0 := by exact_mod_cast ne_of_gt hL0
    have ht : (L : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    calc
      (L : ENNReal) * (q : ENNReal) ^ n / (L : ENNReal)
          = (q : ENNReal) ^ n * ((L : ENNReal) / (L : ENNReal)) := by
            rw [mul_comm ((L : ENNReal)) ((q : ENNReal) ^ n), mul_div_assoc]
      _ = (q : ENNReal) ^ n := by rw [ENNReal.div_self h0 ht, mul_one]
  have hpair_left : ∀ n m : ℕ, n ≤ m →
      w L ((T^[n]) x0) ((T^[m]) x0) ≤ C * (k : ENNReal) ^ n := by
    intro n m hnm
    have hp0 := hpath (m - n) n
    have hsum : n + (m - n) = m := Nat.add_sub_of_le hnm
    have hp : w (S n) ((T^[n]) x0) ((T^[m]) x0) ≤ C * (r : ENNReal) ^ n := by
      simpa [hsum] using hp0
    have hsc := modular_scale_le w hself hconv (hS0 n) (hS_le n)
      ((T^[n]) x0) ((T^[m]) x0)
    have hqrpow : (q : ENNReal) ^ n * (C * (r : ENNReal) ^ n) =
        C * (k : ENNReal) ^ n := by
      have h : (q : ENNReal) ^ n * (r : ENNReal) ^ n = (k : ENNReal) ^ n := by
        rw [← ENNReal.coe_pow, ← ENNReal.coe_pow, ← ENNReal.coe_mul, ← mul_pow, hqr,
          ENNReal.coe_pow]
      calc
        (q : ENNReal) ^ n * (C * (r : ENNReal) ^ n)
            = C * ((q : ENNReal) ^ n * (r : ENNReal) ^ n) := by ring
        _ = C * (k : ENNReal) ^ n := by rw [h]
    calc
      w L ((T^[n]) x0) ((T^[m]) x0)
          ≤ ((S n : ENNReal) / (L : ENNReal)) *
              w (S n) ((T^[n]) x0) ((T^[m]) x0) := hsc
      _ = (q : ENNReal) ^ n * w (S n) ((T^[n]) x0) ((T^[m]) x0) := by
            rw [hSratioL n]
      _ ≤ (q : ENNReal) ^ n * (C * (r : ENNReal) ^ n) :=
            mul_le_mul_left' hp _
      _ = C * (k : ENNReal) ^ n := hqrpow
  have hpair : ∀ p : ℕ × ℕ,
      w L ((T^[p.1]) x0) ((T^[p.2]) x0) ≤ C * (k : ENNReal) ^ min p.1 p.2 := by
    intro p
    rcases le_total p.1 p.2 with h | h
    · simpa [min_eq_left h] using hpair_left p.1 p.2 h
    · have hs : w L ((T^[p.1]) x0) ((T^[p.2]) x0) =
          w L ((T^[p.2]) x0) ((T^[p.1]) x0) := hsymm L hL0 _ _
      calc
        w L ((T^[p.1]) x0) ((T^[p.2]) x0)
            = w L ((T^[p.2]) x0) ((T^[p.1]) x0) := hs
        _ ≤ C * (k : ENNReal) ^ p.2 := hpair_left p.2 p.1 h
        _ = C * (k : ENNReal) ^ min p.1 p.2 := by rw [min_eq_right h]
  have hupper : Filter.Tendsto
      (fun p : ℕ × ℕ => C * (k : ENNReal) ^ min p.1 p.2)
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0) :=
    tendsto_ennreal_const_mul_pow_min_zero hCne hk1
  have hCauchy : Filter.Tendsto
      (fun p : ℕ × ℕ => w L ((T^[p.1]) x0) ((T^[p.2]) x0))
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun p => zero_le _) hpair
  rcases hcomplete (fun n => (T^[n]) x0) L hL0 hCauchy with ⟨y, hlim⟩
  have hlim_yx : Filter.Tendsto (fun n : ℕ => w L y ((T^[n]) x0))
      Filter.atTop (nhds 0) := by
    convert hlim using 1
    ext n
    exact hsymm L hL0 _ _
  have htail : Filter.Tendsto (fun n : ℕ => w L y ((T^[n + 1]) x0))
      Filter.atTop (nhds 0) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2 hlim_yx
  have hctr_le : ∀ n : ℕ,
      w (k * L) (T y) ((T^[n + 1]) x0) ≤ w L y ((T^[n]) x0) := by
    intro n
    have hc := hcontr y ((T^[n]) x0) L hL0 le_rfl
    simpa [Function.iterate_succ_apply'] using hc
  have hctr_lim : Filter.Tendsto
      (fun n : ℕ => w (k * L) (T y) ((T^[n + 1]) x0))
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim_yx
      (fun n => zero_le _) hctr_le
  let s : NNReal := k * L + L
  have hs0 : 0 < s := by dsimp [s]; exact add_pos (mul_pos hk0 hL0) hL0
  let A : ENNReal := ((k * L : NNReal) : ENNReal) /
    (((k * L : NNReal) : ENNReal) + (L : ENNReal))
  let B : ENNReal := (L : ENNReal) /
    (((k * L : NNReal) : ENNReal) + (L : ENNReal))
  have hden : (((k * L : NNReal) : ENNReal) + (L : ENNReal)) ≠ 0 := by
    rw [← ENNReal.coe_add]
    exact_mod_cast ne_of_gt hs0
  have hAne : A ≠ ⊤ := by
    dsimp [A]
    exact ENNReal.div_ne_top ENNReal.coe_ne_top hden
  have hBne : B ≠ ⊤ := by
    dsimp [B]
    exact ENNReal.div_ne_top ENNReal.coe_ne_top hden
  have hA_lim : Filter.Tendsto
      (fun n : ℕ => A * w (k * L) (T y) ((T^[n + 1]) x0))
      Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hctr_lim (Or.inr hAne)
  have hB_lim : Filter.Tendsto
      (fun n : ℕ => B * w L y ((T^[n + 1]) x0))
      Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul htail (Or.inr hBne)
  have hsum_lim : Filter.Tendsto
      (fun n : ℕ => A * w (k * L) (T y) ((T^[n + 1]) x0) +
        B * w L y ((T^[n + 1]) x0))
      Filter.atTop (nhds 0) := by
    simpa using hA_lim.add hB_lim
  have hfix_le : ∀ n : ℕ,
      w s (T y) y ≤ A * w (k * L) (T y) ((T^[n + 1]) x0) +
        B * w L y ((T^[n + 1]) x0) := by
    intro n
    exact hconv (k * L) L (mul_pos hk0 hL0) hL0 (T y) y ((T^[n + 1]) x0)
  have hfix_seq : Filter.Tendsto (fun _ : ℕ => w s (T y) y)
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum_lim
      (fun n => zero_le _) hfix_le
  have hfix_zero : w s (T y) y = 0 := (tendsto_const_nhds_iff).1 hfix_seq
  have hfix_val : (T y : X) = (y : X) :=
    hstrict (T y) y ⟨s, hs0, hfix_zero⟩
  have hfix : T y = y := Subtype.ext hfix_val
  exact ⟨y, hfix, hlim⟩

/- accepted add_to_file helper 4 -/
lemma ennreal_eq_zero_of_le_coe_mul_self {d : ENNReal} (hd : d ≠ ⊤)
    {k : NNReal} (hk : k < 1) (h : d ≤ (k : ENNReal) * d) : d = 0 := by
  have hprod : (k : ENNReal) * d ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hd
  have hr : d.toReal ≤ (k : ℝ) * d.toReal := by
    have hr0 := (ENNReal.toReal_le_toReal hd hprod).2 h
    simpa [ENNReal.toReal_mul] using hr0
  have hz : d.toReal = 0 := by
    nlinarith [ENNReal.toReal_nonneg (a := d)]
  exact (ENNReal.toReal_eq_zero_iff d).1 hz |>.resolve_right hd

/- verified submission -/
theorem strict_convex_modular_fixed_point
    {X : Type*} (b : X) (w : NNReal → X → X → ENNReal)
    (hself : ∀ (l : NNReal), 0 < l → ∀ x : X, w l x x = 0)
    (hsymm : ∀ (l : NNReal), 0 < l → ∀ x y : X, w l x y = w l y x)
    (hstrict : ∀ x y : X, (∃ l : NNReal, 0 < l ∧ w l x y = 0) → x = y)
    (hconv : ∀ (l m : NNReal), 0 < l → 0 < m → ∀ x y z : X,
      w (l + m) x y ≤ ((l : ENNReal) / (l + m)) * w l x z +
        ((m : ENNReal) / (l + m)) * w m y z)
    (hcomplete : ∀ (x : ℕ → {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤})
      (l : NNReal), 0 < l →
      Filter.Tendsto (fun p : ℕ × ℕ => w l (x p.1) (x p.2))
        (Filter.atTop ×ˢ Filter.atTop) (nhds 0) →
      ∃ y : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
        Filter.Tendsto (fun n => w l (x n) y) Filter.atTop (nhds 0))
    (T : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤} →
      {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤})
    (hcontractive : ∃ k L : NNReal, 0 < k ∧ k < 1 ∧ 0 < L ∧
      ∀ x y : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
        ∀ l : NNReal, 0 < l → l ≤ L → w (k * l) (T x) (T y) ≤ w l x y) :
    ((∀ l : NNReal, 0 < l →
        ∃ x : {x : X // ∃ m : NNReal, 0 < m ∧ w m x b < ⊤},
          w l x (T x) < ⊤) →
      ∃ x : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤}, T x = x) ∧
    ((∀ l : NNReal, 0 < l →
        ∀ x y : {x : X // ∃ m : NNReal, 0 < m ∧ w m x b < ⊤}, w l x y < ⊤) →
      ∃ xstar : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
        T xstar = xstar ∧
        (∀ y : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
          T y = y → y = xstar) ∧
        ∀ x : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
          ∃ l : NNReal, 0 < l ∧
            Filter.Tendsto (fun n : ℕ => w l ((T^[n]) x) xstar)
              Filter.atTop (nhds 0)) := by
  constructor
  · intro hdisp
    rcases hcontractive with ⟨k, L, hk0, hk1, hL0, hcontr⟩
    let a : NNReal := (1 - (1 + k) / 2) * L
    have ha0 : 0 < a := by
      dsimp [a]
      have h : (1 + k) / 2 < 1 := by nlinarith [hk1]
      exact mul_pos (tsub_pos_of_lt h) hL0
    rcases hdisp a ha0 with ⟨x0, hx0⟩
    rcases modular_fixed_point_of_displacement b w hself hsymm hstrict hconv
        hcomplete T hk0 hk1 hL0 hcontr x0 hx0 with ⟨y, hy, -⟩
    exact ⟨y, hy⟩
  · intro hfinite
    rcases hcontractive with ⟨k, L, hk0, hk1, hL0, hcontr⟩
    let a : NNReal := (1 - (1 + k) / 2) * L
    have ha0 : 0 < a := by
      dsimp [a]
      have h : (1 + k) / 2 < 1 := by nlinarith [hk1]
      exact mul_pos (tsub_pos_of_lt h) hL0
    have hbw : w L b b < ⊤ := by
      rw [hself L hL0 b]
      exact ENNReal.zero_lt_top
    let xb : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤} :=
      ⟨b, ⟨L, hL0, hbw⟩⟩
    have hxb : w a xb (T xb) < ⊤ := hfinite a ha0 xb (T xb)
    rcases modular_fixed_point_of_displacement b w hself hsymm hstrict hconv
        hcomplete T hk0 hk1 hL0 hcontr xb hxb with ⟨xstar, hstar, -⟩
    have huniq : ∀ y : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
        T y = y → y = xstar := by
      intro y hy
      let d : ENNReal := w L y xstar
      have hdne : d ≠ ⊤ := by
        dsimp [d]
        exact ne_of_lt (hfinite L hL0 y xstar)
      have hctr0 := hcontr y xstar L hL0 le_rfl
      have hctr : w (k * L) y xstar ≤ d := by
        simpa [d, hy, hstar] using hctr0
      have hkL : 0 < k * L := mul_pos hk0 hL0
      have hkL_le : k * L ≤ L := by
        calc
          k * L ≤ 1 * L := mul_le_mul_right' hk1.le L
          _ = L := one_mul L
      have hsc := modular_scale_le w hself hconv hkL hkL_le y xstar
      have hcoef : (((k * L : NNReal) : ENNReal) / (L : ENNReal)) = (k : ENNReal) := by
        have h0 : (L : ENNReal) ≠ 0 := by exact_mod_cast ne_of_gt hL0
        have ht : (L : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
        calc
          (((k * L : NNReal) : ENNReal) / (L : ENNReal))
              = ((k : ENNReal) * (L : ENNReal)) / (L : ENNReal) := by
                  rw [ENNReal.coe_mul]
          _ = (k : ENNReal) * ((L : ENNReal) / (L : ENNReal)) := by
                  rw [mul_div_assoc]
          _ = (k : ENNReal) := by
                  rw [ENNReal.div_self h0 ht, mul_one]
      have hdself : d ≤ (k : ENNReal) * d := by
        calc
          d = w L y xstar := rfl
          _ ≤ (((k * L : NNReal) : ENNReal) / (L : ENNReal)) *
                w (k * L) y xstar := hsc
          _ = (k : ENNReal) * w (k * L) y xstar := by rw [hcoef]
          _ ≤ (k : ENNReal) * d := mul_le_mul_left' hctr _
      have hdzero : d = 0 := ennreal_eq_zero_of_le_coe_mul_self hdne hk1 hdself
      have hval : (y : X) = (xstar : X) :=
        hstrict y xstar ⟨L, hL0, hdzero⟩
      exact Subtype.ext hval
    refine ⟨xstar, hstar, huniq, ?_⟩
    intro x
    have hx : w a x (T x) < ⊤ := hfinite a ha0 x (T x)
    rcases modular_fixed_point_of_displacement b w hself hsymm hstrict hconv
        hcomplete T hk0 hk1 hL0 hcontr x hx with ⟨y, hy, hlim⟩
    have hyx : y = xstar := huniq y hy
    exact ⟨L, hL0, by simpa [hyx] using hlim⟩


#check_dependency_graph "strict_convex_modular_fixed_point" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"((∀ (l : NNReal), 0 < l → ∃ x, w l ↑x ↑(T x) < ⊤) → ∃ x, T x = x) ∧ ((∀ (l : NNReal), 0 < l → ∀ (x y : { x // ∃ m, 0 < m ∧ w m x b < ⊤ }), w l ↑x ↑y < ⊤) → ∃ xstar, T xstar = xstar ∧ (∀ (y : { x // ∃ l, 0 < l ∧ w l x b < ⊤ }), T y = y → y = xstar) ∧ ∀ (x : { x // ∃ l, 0 < l ∧ w l x b < ⊤ }), ∃ l, 0 < l ∧ Filter.Tendsto (fun n => w l ↑(T^[n] x) ↑xstar) Filter.atTop (nhds 0))\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hself\",\"statement\":\"∀ (l : NNReal), 0 < l → ∀ (x : X), w l x x = 0\"},{\"name\":\"hsymm\",\"statement\":\"∀ (l : NNReal), 0 < l → ∀ (x y : X), w l x y = w l y x\"},{\"name\":\"hstrict\",\"statement\":\"∀ (x y : X), (∃ l, 0 < l ∧ w l x y = 0) → x = y\"},{\"name\":\"hconv\",\"statement\":\"∀ (l m : NNReal), 0 < l → 0 < m → ∀ (x y z : X), w (l + m) x y ≤ ↑l / (↑l + ↑m) * w l x z + ↑m / (↑l + ↑m) * w m y z\"},{\"name\":\"hcomplete\",\"statement\":\"∀ (x : ℕ → { x // ∃ l, 0 < l ∧ w l x b < ⊤ }) (l : NNReal), 0 < l → Filter.Tendsto (fun p => w l ↑(x p.1) ↑(x p.2)) (Filter.atTop ×ˢ Filter.atTop) (nhds 0) → ∃ y, Filter.Tendsto (fun n => w l ↑(x n) ↑y) Filter.atTop (nhds 0)\"},{\"name\":\"hcontractive\",\"statement\":\"∃ k L, 0 < k ∧ k < 1 ∧ 0 < L ∧ ∀ (x y : { x // ∃ l, 0 < l ∧ w l x b < ⊤ }) (l : NNReal), 0 < l → l ≤ L → w (k * l) ↑(T x) ↑(T y) ≤ w l ↑x ↑y\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1151_strict_convex_modular_fixed_point\",\"reconstructedProofSha256\":\"cea97ffc432c413055eec64974cc014dba1d8d6801bcea53159b47603dfff4ec\",\"selectedEdgeCount\":1,\"theoremName\":\"strict_convex_modular_fixed_point\",\"topologySha256\":\"d75903c07f3cb6dafb1d31aa074ca2f36785d75d8e5ad8a06a5b6745d6002ea8\"}"
