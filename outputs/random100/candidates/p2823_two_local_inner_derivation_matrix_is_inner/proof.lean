import Mathlib

/- accepted add_to_file helper 1 -/
namespace TwoLocalInnerDerivation

variable {R : Type*} [CommRing R]

noncomputable def E {n : ℕ} (i j : Fin n) : Matrix (Fin n) (Fin n) R :=
  Matrix.single i j (1 : R)

lemma E_apply {n : ℕ} (i j a b : Fin n) :
    E (R := R) i j a b = (if i = a ∧ j = b then (1 : R) else 0) := by
  rfl

lemma mul_E_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (i j a b : Fin n) :
    (M * E (R := R) i j) a b = (if j = b then M a i else 0) := by
  rw [Matrix.mul_apply]
  by_cases hb : j = b
  · subst b
    rw [Finset.sum_eq_single i]
    · simp [E, Matrix.single_apply]
    · intro x _ hx
      by_cases hix : i = x
      · exact False.elim (hx hix.symm)
      · simp [E, Matrix.single_apply, hix]
    · simp
  · simp [E, Matrix.single_apply, hb]

lemma E_mul_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (i j a b : Fin n) :
    (E (R := R) i j * M) a b = (if i = a then M j b else 0) := by
  rw [Matrix.mul_apply]
  by_cases ha : i = a
  · subst a
    rw [Finset.sum_eq_single j]
    · simp [E, Matrix.single_apply]
    · intro x _ hx
      by_cases hjx : j = x
      · exact False.elim (hx hjx.symm)
      · simp [E, Matrix.single_apply, hjx]
    · simp
  · simp [E, Matrix.single_apply, ha]

end TwoLocalInnerDerivation

/- accepted add_to_file helper 2 -/
namespace TwoLocalInnerDerivation

variable {R : Type*} [CommRing R]

def Up (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  fun i j => if j.1 = i.1 + 1 then (1 : R) else 0

def Down (n : ℕ) : Matrix (Fin n) (Fin n) R :=
  fun i j => if i.1 = j.1 + 1 then (1 : R) else 0

end TwoLocalInnerDerivation

/- accepted add_to_file helper 3 -/
namespace TwoLocalInnerDerivation

variable {R : Type*} [CommRing R]

lemma mul_Up_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (M * Up (R := R) n) i j =
      if h : 0 < j.1 then M i ⟨j.1 - 1, by omega⟩ else 0 := by
  rw [Matrix.mul_apply]
  by_cases hj : 0 < j.1
  · rw [dif_pos hj]
    rw [Finset.sum_eq_single ⟨j.1 - 1, by omega⟩]
    · have hUp : Up (R := R) n ⟨j.1 - 1, by omega⟩ j = 1 := by
        simp [Up]
        omega
      rw [hUp, mul_one]
    · intro x _ hx
      by_cases hxj : j.1 = x.1 + 1
      · apply False.elim
        apply hx
        have hxval : x.1 = (⟨j.1 - 1, by omega⟩ : Fin n).1 := by
          simp
          omega
        exact Fin.eq_of_val_eq hxval
      · have hzero : Up (R := R) n x j = 0 := by simp [Up, hxj]
        rw [hzero, mul_zero]
    · simp
  · rw [dif_neg hj]
    have hzero : j.1 = 0 := by omega
    apply Finset.sum_eq_zero
    intro x _
    have hUp : Up (R := R) n x j = 0 := by simp [Up, hzero]
    rw [hUp, mul_zero]

lemma Up_mul_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (Up (R := R) n * M) i j =
      if h : i.1 + 1 < n then M ⟨i.1 + 1, h⟩ j else 0 := by
  rw [Matrix.mul_apply]
  by_cases hi : i.1 + 1 < n
  · rw [dif_pos hi]
    rw [Finset.sum_eq_single ⟨i.1 + 1, hi⟩]
    · have hUp : Up (R := R) n i ⟨i.1 + 1, hi⟩ = 1 := by
        simp [Up]
      rw [hUp, one_mul]
    · intro x _ hx
      by_cases hxi : x.1 = i.1 + 1
      · apply False.elim
        apply hx
        have hxval : x.1 = (⟨i.1 + 1, hi⟩ : Fin n).1 := by
          simp [hxi]
        exact Fin.eq_of_val_eq hxval
      · have hzero : Up (R := R) n i x = 0 := by simp [Up, hxi]
        rw [hzero, zero_mul]
    · simp
  · rw [dif_neg hi]
    apply Finset.sum_eq_zero
    intro x _
    have hx : x.1 ≠ i.1 + 1 := by
      intro h
      omega
    have hUp : Up (R := R) n i x = 0 := by simp [Up, hx]
    rw [hUp, zero_mul]

lemma Down_transpose {n : ℕ} :
    Down (R := R) n = (Up (R := R) n).transpose := by
  ext i j
  simp [Down, Up]

end TwoLocalInnerDerivation

/- accepted add_to_file helper 4 -/
namespace TwoLocalInnerDerivation

variable {R : Type*} [CommRing R]

lemma commute_Up_succ_zero {n a : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (hcomm : M * Up (R := R) n = Up (R := R) n * M) (ha : a + 1 < n) :
    M ⟨a + 1, ha⟩ ⟨0, by omega⟩ = 0 := by
  have h := congr_fun (congr_fun hcomm ⟨a, by omega⟩) ⟨0, by omega⟩
  rw [mul_Up_apply, Up_mul_apply] at h
  simpa [ha] using h.symm

lemma commute_Up_succ_succ {n a b : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (hcomm : M * Up (R := R) n = Up (R := R) n * M)
    (ha : a + 1 < n) (hb : b + 1 < n) :
    M ⟨a + 1, ha⟩ ⟨b + 1, hb⟩ = M ⟨a, by omega⟩ ⟨b, by omega⟩ := by
  have h := congr_fun (congr_fun hcomm ⟨a, by omega⟩) ⟨b + 1, hb⟩
  rw [mul_Up_apply, Up_mul_apply] at h
  simpa [ha] using h.symm

lemma commute_Up_below_aux {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (hcomm : M * Up (R := R) n = Up (R := R) n * M) :
    ∀ d : ℕ, ∀ i j : Fin n, j.1 = d → j.1 < i.1 → M i j = 0 := by
  intro d
  induction d with
  | zero =>
      intro i j hj hlt
      have hi : i.1 - 1 + 1 < n := by omega
      have hrow : i = ⟨i.1 - 1 + 1, hi⟩ := by
        apply Fin.eq_of_val_eq
        simp
        omega
      have hcol : j = ⟨0, by omega⟩ := by
        apply Fin.eq_of_val_eq
        simp [hj]
      rw [hrow, hcol]
      exact commute_Up_succ_zero (R := R) (n := n) (a := i.1 - 1) M hcomm hi
  | succ d ih =>
      intro i j hj hlt
      have hip : i.1 - 1 < n := by omega
      have hjp : d < n := by omega
      let ip : Fin n := ⟨i.1 - 1, hip⟩
      let jp : Fin n := ⟨d, hjp⟩
      have hi : ip.1 + 1 < n := by
        have : ip.1 = i.1 - 1 := rfl
        omega
      have hb : jp.1 + 1 < n := by
        have : jp.1 = d := rfl
        omega
      have hrow : i = ⟨ip.1 + 1, hi⟩ := by
        apply Fin.eq_of_val_eq
        have : (⟨ip.1 + 1, hi⟩ : Fin n).1 = ip.1 + 1 := rfl
        rw [this]
        have : ip.1 = i.1 - 1 := rfl
        omega
      have hcol : j = ⟨jp.1 + 1, hb⟩ := by
        apply Fin.eq_of_val_eq
        have : (⟨jp.1 + 1, hb⟩ : Fin n).1 = jp.1 + 1 := rfl
        rw [this]
        have : jp.1 = d := rfl
        omega
      rw [hrow, hcol]
      rw [commute_Up_succ_succ (R := R) (n := n) M hcomm hi hb]
      apply ih ip jp rfl
      have hipval : ip.1 = i.1 - 1 := rfl
      have hjpval : jp.1 = d := rfl
      rw [hipval, hjpval]
      omega

lemma commute_Up_eq_zero_of_lt {n : ℕ} {M : Matrix (Fin n) (Fin n) R}
    (hcomm : M * Up (R := R) n = Up (R := R) n * M) {i j : Fin n} (h : j.1 < i.1) :
    M i j = 0 :=
  commute_Up_below_aux (R := R) M hcomm j.1 i j rfl h

end TwoLocalInnerDerivation

/- accepted add_to_file helper 5 -/
namespace TwoLocalInnerDerivation

variable {R : Type*} [CommRing R]

lemma commute_Up_diag_aux {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (hcomm : M * Up (R := R) n = Up (R := R) n * M) :
    ∀ k : ℕ, ∀ hk : k < n,
      M ⟨k, hk⟩ ⟨k, hk⟩ = M ⟨0, by omega⟩ ⟨0, by omega⟩ := by
  intro k
  induction k with
  | zero =>
      intro hk
      rfl
  | succ k ih =>
      intro hk
      have hk0 : k < n := by omega
      have hsucc : k + 1 < n := hk
      rw [commute_Up_succ_succ (R := R) (n := n) M hcomm hsucc hsucc]
      exact ih hk0

lemma commute_Up_diag_eq {n : ℕ} {M : Matrix (Fin n) (Fin n) R}
    (hcomm : M * Up (R := R) n = Up (R := R) n * M) (i j : Fin n) :
    M i i = M j j := by
  have hi := commute_Up_diag_aux (R := R) M hcomm i.1 i.2
  have hj := commute_Up_diag_aux (R := R) M hcomm j.1 j.2
  rw [hi, hj]

lemma commute_Down_eq_zero_of_lt {n : ℕ} {M : Matrix (Fin n) (Fin n) R}
    (hcomm : M * Down (R := R) n = Down (R := R) n * M) {i j : Fin n}
    (h : i.1 < j.1) : M i j = 0 := by
  have ht : M.transpose * Up (R := R) n = Up (R := R) n * M.transpose := by
    have htr := congrArg Matrix.transpose hcomm
    have hs := htr.symm
    simpa [Matrix.transpose_mul, Down_transpose] using hs
  have hz := commute_Up_eq_zero_of_lt (R := R) (M := M.transpose) ht (i := j) (j := i) h
  simpa [Matrix.transpose_apply] using hz

lemma commute_Down_diag_eq {n : ℕ} {M : Matrix (Fin n) (Fin n) R}
    (hcomm : M * Down (R := R) n = Down (R := R) n * M) (i j : Fin n) :
    M i i = M j j := by
  have ht : M.transpose * Up (R := R) n = Up (R := R) n * M.transpose := by
    have htr := congrArg Matrix.transpose hcomm
    have hs := htr.symm
    simpa [Matrix.transpose_mul, Down_transpose] using hs
  have hd := commute_Up_diag_eq (R := R) (M := M.transpose) ht j i
  exact hd.symm

end TwoLocalInnerDerivation

/- accepted add_to_file helper 6 -/
namespace TwoLocalInnerDerivation

variable {R : Type*} [CommRing R]

lemma commute_E_row_eq_zero {n : ℕ} {M : Matrix (Fin n) (Fin n) R} {r s q : Fin n}
    (hcomm : M * E (R := R) r s = E (R := R) r s * M) (hq : q ≠ s) :
    M s q = 0 := by
  have h := congr_fun (congr_fun hcomm r) q
  rw [mul_E_apply, E_mul_apply] at h
  have hsq : s ≠ q := fun hqs => hq hqs.symm
  simp [hsq] at h
  exact h.symm

lemma commute_E_col_eq_zero {n : ℕ} {M : Matrix (Fin n) (Fin n) R} {r s q : Fin n}
    (hcomm : M * E (R := R) r s = E (R := R) r s * M) (hq : q ≠ r) :
    M q r = 0 := by
  have h := congr_fun (congr_fun hcomm q) s
  rw [mul_E_apply, E_mul_apply] at h
  have hrq : r ≠ q := fun hqr => hq hqr.symm
  simp [hrq] at h
  exact h

lemma commute_E_diag_diag_eq {n : ℕ} {M : Matrix (Fin n) (Fin n) R} {r s : Fin n}
    (hcomm : M * E (R := R) r s = E (R := R) r s * M) :
    M r r = M s s := by
  have h := congr_fun (congr_fun hcomm r) s
  rw [mul_E_apply, E_mul_apply] at h
  simpa using h

end TwoLocalInnerDerivation

/- accepted add_to_file helper 7 -/
namespace TwoLocalInnerDerivation

variable {R : Type*} [CommRing R]

lemma projector_extension {n : ℕ} {W U V : Matrix (Fin n) (Fin n) R} {p : Fin n}
    (hWU : W = U * E (R := R) p p - E (R := R) p p * U)
    (hWV : W = V * E (R := R) p p - E (R := R) p p * V)
    (hU : U * Up (R := R) n = Up (R := R) n * U)
    (hV : V * Down (R := R) n = Down (R := R) n * V) :
    W = 0 := by
  ext i j
  by_cases hi : i = p
  · by_cases hj : j = p
    · subst i
      subst j
      have h := congr_fun (congr_fun hWU p) p
      rw [Matrix.sub_apply, mul_E_apply, E_mul_apply] at h
      simpa [sub_self] using h
    · subst i
      have hpj : p ≠ j := fun h => hj h.symm
      have hUeq := congr_fun (congr_fun hWU p) j
      have hVeq := congr_fun (congr_fun hWV p) j
      rw [Matrix.sub_apply, mul_E_apply, E_mul_apply] at hUeq hVeq
      by_cases hlt : j.1 < p.1
      · have hz := commute_Up_eq_zero_of_lt (R := R) (M := U) hU hlt
        simp [hpj, hz] at hUeq
        exact hUeq
      · have hgt : p.1 < j.1 := by
          have hne : p.1 ≠ j.1 := by
            intro hv
            apply hj
            exact Fin.eq_of_val_eq hv.symm
          omega
        have hz := commute_Down_eq_zero_of_lt (R := R) (M := V) hV hgt
        simp [hpj, hz] at hVeq
        exact hVeq
  · have hpi : p ≠ i := fun h => hi h.symm
    by_cases hj : j = p
    · subst j
      have hUeq := congr_fun (congr_fun hWU i) p
      have hVeq := congr_fun (congr_fun hWV i) p
      rw [Matrix.sub_apply, mul_E_apply, E_mul_apply] at hUeq hVeq
      by_cases hlt : i.1 < p.1
      · have hz := commute_Down_eq_zero_of_lt (R := R) (M := V) hV hlt
        simp [hpi, hz] at hVeq
        exact hVeq
      · have hgt : p.1 < i.1 := by
          have hne : p.1 ≠ i.1 := by
            intro hv
            apply hi
            exact Fin.eq_of_val_eq hv.symm
          omega
        have hz := commute_Up_eq_zero_of_lt (R := R) (M := U) hU hgt
        simp [hpi, hz] at hUeq
        exact hUeq
    · have hpj : p ≠ j := fun h => hj h.symm
      have h := congr_fun (congr_fun hWU i) j
      rw [Matrix.sub_apply, mul_E_apply, E_mul_apply] at h
      simp [hpi, hpj] at h
      simpa using h

end TwoLocalInnerDerivation

/- accepted add_to_file helper 8 -/
namespace TwoLocalInnerDerivation

variable {R : Type*} [CommRing R]

lemma offdiag_extension {n : ℕ} {W U V T : Matrix (Fin n) (Fin n) R}
    {p q : Fin n}
    (hWU : W = U * E (R := R) p q - E (R := R) p q * U)
    (hWV : W = V * E (R := R) p q - E (R := R) p q * V)
    (hWT : W = T * E (R := R) p q - E (R := R) p q * T)
    (hU : U * E (R := R) p p = E (R := R) p p * U)
    (hV : V * E (R := R) q q = E (R := R) q q * V)
    (hT : T * Up (R := R) n = Up (R := R) n * T) :
    W = 0 := by
  ext a b
  by_cases ha : a = p
  · by_cases hb : b = q
    · subst a
      subst b
      have hTeq := congr_fun (congr_fun hWT p) q
      rw [Matrix.sub_apply, mul_E_apply, E_mul_apply] at hTeq
      have hdiag := commute_Up_diag_eq (R := R) (M := T) hT p q
      simp [hdiag] at hTeq
      exact hTeq
    · subst a
      have hqb : q ≠ b := fun h => hb h.symm
      have hVeq := congr_fun (congr_fun hWV p) b
      rw [Matrix.sub_apply, mul_E_apply, E_mul_apply] at hVeq
      have hz := commute_E_row_eq_zero (R := R) (M := V) (r := q) (s := q) (q := b) hV hb
      simp [hqb, hz] at hVeq
      exact hVeq
  · by_cases hb : b = q
    · subst b
      have hpa : p ≠ a := fun h => ha h.symm
      have hUeq := congr_fun (congr_fun hWU a) q
      rw [Matrix.sub_apply, mul_E_apply, E_mul_apply] at hUeq
      have hz := commute_E_col_eq_zero (R := R) (M := U) (r := p) (s := p) (q := a) hU ha
      simp [hpa, hz] at hUeq
      exact hUeq
    · have hpa : p ≠ a := fun h => ha h.symm
      have hqb : q ≠ b := fun h => hb h.symm
      have h := congr_fun (congr_fun hWU a) b
      rw [Matrix.sub_apply, mul_E_apply, E_mul_apply] at h
      simp [hpa, hqb] at h
      simpa using h

end TwoLocalInnerDerivation

/- accepted add_to_file helper 9 -/
namespace TwoLocalInnerDerivation

variable {R : Type*} [CommRing R]

lemma final_diag_entry {n : ℕ} {W U X : Matrix (Fin n) (Fin n) R} {a : Fin n}
    (hW : W = U * X - X * U)
    (hU : U * E (R := R) a a = E (R := R) a a * U) :
    W a a = 0 := by
  have hprod1 : (U * X) a a = U a a * X a a := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single a]
    · intro k _ hk
      have hz := commute_E_row_eq_zero (R := R) (M := U) (r := a) (s := a) (q := k) hU hk
      rw [hz, zero_mul]
    · simp
  have hprod2 : (X * U) a a = X a a * U a a := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single a]
    · intro k _ hk
      have hz := commute_E_col_eq_zero (R := R) (M := U) (r := a) (s := a) (q := k) hU hk
      rw [hz, mul_zero]
    · simp
  have h := congr_fun (congr_fun hW a) a
  rw [Matrix.sub_apply, hprod1, hprod2, mul_comm (U a a) (X a a), sub_self] at h
  exact h

lemma final_offdiag_entry {n : ℕ} {W U X : Matrix (Fin n) (Fin n) R} {a b : Fin n}
    (hW : W = U * X - X * U)
    (hU : U * E (R := R) b a = E (R := R) b a * U) :
    W a b = 0 := by
  have hprod1 : (U * X) a b = U a a * X a b := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single a]
    · intro k _ hk
      have hz := commute_E_row_eq_zero (R := R) (M := U) (r := b) (s := a) (q := k) hU hk
      rw [hz, zero_mul]
    · simp
  have hprod2 : (X * U) a b = X a b * U b b := by
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single b]
    · intro k _ hk
      have hz := commute_E_col_eq_zero (R := R) (M := U) (r := b) (s := a) (q := k) hU hk
      rw [hz, mul_zero]
    · simp
  have hdiag : U a a = U b b :=
    (commute_E_diag_diag_eq (R := R) (M := U) (r := b) (s := a) hU).symm
  have h := congr_fun (congr_fun hW a) b
  rw [Matrix.sub_apply, hprod1, hprod2, hdiag, mul_comm (U b b) (X a b), sub_self] at h
  exact h

end TwoLocalInnerDerivation

/- accepted add_to_file helper 10 -/
namespace TwoLocalInnerDerivation

variable {R : Type*} [CommRing R]

lemma comm_sub_of_comm_eq {n : ℕ} {A B Y : Matrix (Fin n) (Fin n) R}
    (hAB : A * Y - Y * A = B * Y - Y * B) :
    (A - B) * Y = Y * (A - B) := by
  rw [sub_mul, mul_sub]
  calc
    A * Y - B * Y = (A * Y - Y * A) + (Y * A - B * Y) := by abel
    _ = (B * Y - Y * B) + (Y * A - B * Y) := by rw [hAB]
    _ = Y * A - Y * B := by abel

end TwoLocalInnerDerivation

/- verified submission -/
open TwoLocalInnerDerivation

theorem two_local_inner_derivation_matrix_is_inner
    (R : Type*) [CommRing R] (n : ℕ) (hn : 1 < n)
    (h2 : IsUnit (2 : R))
    (Δ : Matrix (Fin n) (Fin n) R → Matrix (Fin n) (Fin n) R)
    (hΔ : ∀ X Y, ∃ A, Δ X = A * X - X * A ∧ Δ Y = A * Y - Y * A) :
    ∃ B, ∀ X, Δ X = B * X - X * B := by
  obtain ⟨B, hBU, hBD⟩ := hΔ (Up (R := R) n) (Down (R := R) n)
  have hBdiag : ∀ p : Fin n,
      Δ (E (R := R) p p) = B * E (R := R) p p - E (R := R) p p * B := by
    intro p
    obtain ⟨AU, hAUP, hAUU⟩ := hΔ (E (R := R) p p) (Up (R := R) n)
    obtain ⟨AD, hADP, hADD⟩ := hΔ (E (R := R) p p) (Down (R := R) n)
    let U : Matrix (Fin n) (Fin n) R := AU - B
    let V : Matrix (Fin n) (Fin n) R := AD - B
    have hU : U * Up (R := R) n = Up (R := R) n * U := by
      dsimp [U]
      apply comm_sub_of_comm_eq
      rw [← hAUU, ← hBU]
    have hV : V * Down (R := R) n = Down (R := R) n * V := by
      dsimp [V]
      apply comm_sub_of_comm_eq
      rw [← hADD, ← hBD]
    let W : Matrix (Fin n) (Fin n) R :=
      Δ (E (R := R) p p) - (B * E (R := R) p p - E (R := R) p p * B)
    have hWU : W = U * E (R := R) p p - E (R := R) p p * U := by
      dsimp [W, U]
      rw [hAUP, sub_mul, mul_sub]
      abel
    have hWV : W = V * E (R := R) p p - E (R := R) p p * V := by
      dsimp [W, V]
      rw [hADP, sub_mul, mul_sub]
      abel
    have hzero : W = 0 := projector_extension (R := R) hWU hWV hU hV
    have hsub : Δ (E (R := R) p p) - (B * E (R := R) p p - E (R := R) p p * B) = 0 := by
      dsimp [W] at hzero
      exact hzero
    exact sub_eq_zero.mp hsub
  have hBunit : ∀ p q : Fin n,
      Δ (E (R := R) p q) = B * E (R := R) p q - E (R := R) p q * B := by
    intro p q
    by_cases hpq : p = q
    · subst q
      exact hBdiag p
    · obtain ⟨AP, hAPQ, hAPP⟩ := hΔ (E (R := R) p q) (E (R := R) p p)
      obtain ⟨AQ, hAQQ, hAQP⟩ := hΔ (E (R := R) p q) (E (R := R) q q)
      obtain ⟨AT, hATQ, hATU⟩ := hΔ (E (R := R) p q) (Up (R := R) n)
      let U : Matrix (Fin n) (Fin n) R := AP - B
      let V : Matrix (Fin n) (Fin n) R := AQ - B
      let T : Matrix (Fin n) (Fin n) R := AT - B
      have hU : U * E (R := R) p p = E (R := R) p p * U := by
        dsimp [U]
        apply comm_sub_of_comm_eq
        rw [← hAPP, ← hBdiag p]
      have hV : V * E (R := R) q q = E (R := R) q q * V := by
        dsimp [V]
        apply comm_sub_of_comm_eq
        rw [← hAQP, ← hBdiag q]
      have hT : T * Up (R := R) n = Up (R := R) n * T := by
        dsimp [T]
        apply comm_sub_of_comm_eq
        rw [← hATU, ← hBU]
      let W : Matrix (Fin n) (Fin n) R :=
        Δ (E (R := R) p q) - (B * E (R := R) p q - E (R := R) p q * B)
      have hWU : W = U * E (R := R) p q - E (R := R) p q * U := by
        dsimp [W, U]
        rw [hAPQ, sub_mul, mul_sub]
        abel
      have hWV : W = V * E (R := R) p q - E (R := R) p q * V := by
        dsimp [W, V]
        rw [hAQQ, sub_mul, mul_sub]
        abel
      have hWT : W = T * E (R := R) p q - E (R := R) p q * T := by
        dsimp [W, T]
        rw [hATQ, sub_mul, mul_sub]
        abel
      have hzero : W = 0 := offdiag_extension (R := R) hWU hWV hWT hU hV hT
      have hsub : Δ (E (R := R) p q) - (B * E (R := R) p q - E (R := R) p q * B) = 0 := by
        dsimp [W] at hzero
        exact hzero
      exact sub_eq_zero.mp hsub
  refine ⟨B, ?_⟩
  intro X
  let W : Matrix (Fin n) (Fin n) R := Δ X - (B * X - X * B)
  have hWzero : W = 0 := by
    ext a b
    by_cases hab : a = b
    · subst b
      obtain ⟨A, hAX, hAE⟩ := hΔ X (E (R := R) a a)
      let U : Matrix (Fin n) (Fin n) R := A - B
      have hU : U * E (R := R) a a = E (R := R) a a * U := by
        dsimp [U]
        apply comm_sub_of_comm_eq
        rw [← hAE, ← hBunit a a]
      have hW : W = U * X - X * U := by
        dsimp [W, U]
        rw [hAX, sub_mul, mul_sub]
        abel
      exact final_diag_entry (R := R) hW hU
    · obtain ⟨A, hAX, hAE⟩ := hΔ X (E (R := R) b a)
      let U : Matrix (Fin n) (Fin n) R := A - B
      have hU : U * E (R := R) b a = E (R := R) b a * U := by
        dsimp [U]
        apply comm_sub_of_comm_eq
        rw [← hAE, ← hBunit b a]
      have hW : W = U * X - X * U := by
        dsimp [W, U]
        rw [hAX, sub_mul, mul_sub]
        abel
      exact final_offdiag_entry (R := R) hW hU
  have hsub : Δ X - (B * X - X * B) = 0 := by
    dsimp [W] at hWzero
    exact hWzero
  exact sub_eq_zero.mp hsub
