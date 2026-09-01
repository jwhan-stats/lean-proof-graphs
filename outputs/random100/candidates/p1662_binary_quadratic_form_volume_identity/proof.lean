import Mathlib

/- accepted add_to_file helper 1 -/
lemma quadratic_root_gt_one {A B C q : ℝ}
    (hA : 0 < A) (hC : C < 0) (h1 : A + B + C < 0)
    (hqpos : 0 < q) (hqroot : A * q ^ 2 + B * q + C = 0) :
    1 < q := by
  have hAne : A ≠ 0 := ne_of_gt hA
  have hqne : q ≠ 0 := ne_of_gt hqpos
  have hfactor : A + B + C = A * (1 - q) * (1 - C / (A * q)) := by
    field_simp [hAne, hqne]
    nlinarith [hqroot]
  have hAq : 0 < A * q := mul_pos hA hqpos
  have hfrac : C / (A * q) < 0 := div_neg_of_neg_of_pos hC hAq
  have hy : 0 < 1 - C / (A * q) := by linarith
  have hprod : A * (1 - q) * (1 - C / (A * q)) < 0 := by
    rw [← hfactor]
    exact h1
  have hAX : A * (1 - q) < 0 := by
    exact neg_of_mul_neg_left hprod hy.le
  have hx : 1 - q < 0 := by
    exact neg_of_mul_neg_right hAX hA.le
  linarith

lemma transformed_root_relation {A B C lam mu : ℝ}
    (hA : 0 < A) (hC : C < 0)
    (hlampos : 0 < lam)
    (hlamroot : A * lam ^ 2 + B * lam + C = 0)
    (hmuunique : ∀ x : ℝ, 0 < x →
      A * x ^ 2 + (-2 * A - B) * x + (A + B + C) = 0 → x = mu) :
    1 - C / (A * lam) = mu := by
  have hAne : A ≠ 0 := ne_of_gt hA
  have hlamne : lam ≠ 0 := ne_of_gt hlampos
  let r : ℝ := C / (A * lam)
  have hrneg : r < 0 := by
    dsimp [r]
    exact div_neg_of_neg_of_pos hC (mul_pos hA hlampos)
  have hother : A * r ^ 2 + B * r + C = 0 := by
    dsimp [r]
    field_simp [hAne, hlamne]
    nlinarith [hlamroot]
  have hxpos : 0 < 1 - r := by linarith
  have hxroot : A * (1 - r) ^ 2 + (-2 * A - B) * (1 - r) + (A + B + C) = 0 := by
    nlinarith [hother]
  have hx : 1 - r = mu := hmuunique (1-r) hxpos hxroot
  dsimp [r] at hx
  exact hx

/- accepted add_to_file helper 2 -/
lemma quadratic_volume_eq {A B C x : ℝ}
    (hA : 0 < A) (hC : C < 0) (h1 : A + B + C < 0)
    (hxpos : 0 < x) (hxgt : 1 < x)
    (hxroot : A * x ^ 2 + B * x + C = 0) :
    A * x * (x - 1) * (1 + 1 / x ^ 2 + 1 / (x - 1) ^ 2) =
      A * (x ^ 2 - x) + 2 * A + A * (A * x + B) / C -
        A * (A * x + A + B) / (A + B + C) := by
  have hAne : A ≠ 0 := ne_of_gt hA
  have hCne : C ≠ 0 := ne_of_lt hC
  have h1ne : A+B+C ≠0 := ne_of_lt h1
  have hxne : x≠0 := ne_of_gt hxpos
  have hx1ne : x-1≠0 := by nlinarith
  have hinvx : 1 / x = -(A * x + B) / C := by
    field_simp [hCne,hxne]
    nlinarith [hxroot]
  have hinvx1 : 1 / (x-1) = -(A * x + A + B) / (A+B+C) := by
    field_simp [h1ne,hx1ne]
    nlinarith [hxroot]
  have hdecomp :
      A * x * (x - 1) * (1 + 1 / x ^ 2 + 1 / (x - 1) ^ 2) =
        A * (x ^ 2 - x) + A * (1 - 1 / x) + A * (1 + 1 / (x - 1)) := by
    field_simp [hxne,hx1ne]
    ring
  rw [hdecomp, hinvx, hinvx1]
  field_simp [hCne,h1ne]
  ring

/- accepted add_to_file helper 3 -/
lemma quadratic_sum_from_relation {A B C lam mu : ℝ}
    (hA : A ≠ 0)
    (hroot : A * lam ^ 2 + B * lam + C = 0)
    (hrel : mu = lam + 1 + B / A) :
    A * (lam ^ 2 - lam) + A * (mu ^ 2 - mu) =
      B + B ^ 2 / A - 2 * C := by
  have hrootA : A ^ 2 * lam ^ 2 + A * B * lam + A * C = 0 := by
    have h := congrArg (fun t : ℝ => A * t) hroot
    ring_nf at h ⊢
    exact h
  rw [hrel]
  field_simp [hA]
  ring_nf
  nlinarith [hrootA]

lemma rational_c_sum_from_relation {A B C lam mu : ℝ}
    (hA : A ≠ 0) (hC : C ≠ 0)
    (hrel : mu = lam + 1 + B / A) :
    A * (A * lam + B) / C -
        A * (A * mu - A - B) / C = A * B / C := by
  rw [hrel]
  field_simp [hA,hC]
  ring

lemma rational_d_sum_from_relation {A B C lam mu : ℝ}
    (hA : A ≠ 0) (hd : A+B+C ≠ 0)
    (hrel : mu = lam + 1 + B / A) :
    - A * (A * lam + A + B) / (A+B+C) +
        A * (A * mu - 2*A - B) / (A+B+C) =
      - A * (2*A+B)/(A+B+C) := by
  rw [hrel]
  field_simp [hA,hd]
  ring

/- verified submission -/
theorem binary_quadratic_form_volume_identity
    (D a b c : ℤ) (lam mu : ℝ)
    (hDpos : 0 < D)
    (hDnsq : ¬ IsSquare D)
    (hDmod : D % 4 = 0 ∨ D % 4 = 1)
    (hdisc : b ^ 2 - 4 * a * c = D)
    (ha : 0 < a)
    (hc : c < 0)
    (hsum : a + b + c < 0)
    (hlamroot : (a : ℝ) * lam ^ 2 + (b : ℝ) * lam + (c : ℝ) = 0)
    (hlampos : 0 < lam)
    (hlamunique : ∀ x : ℝ,
      0 < x → (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0 → x = lam)
    (hmuroot :
      (a : ℝ) * mu ^ 2 + ((-2 * a - b : ℤ) : ℝ) * mu +
        ((a + b + c : ℤ) : ℝ) = 0)
    (hmupos : 0 < mu)
    (hmuunique : ∀ x : ℝ,
      0 < x →
        (a : ℝ) * x ^ 2 + ((-2 * a - b : ℤ) : ℝ) * x +
          ((a + b + c : ℤ) : ℝ) = 0 →
        x = mu) :
    (a : ℝ) * lam * (lam - 1) *
          (1 + 1 / lam ^ 2 + 1 / (lam - 1) ^ 2) +
        (a : ℝ) * mu * (mu - 1) *
          (1 + 1 / mu ^ 2 + 1 / (mu - 1) ^ 2) =
      4 * (a : ℝ) + (b : ℝ) + (b : ℝ) ^ 2 / (a : ℝ) +
        (a : ℝ) * (b : ℝ) / (c : ℝ) - 2 * (c : ℝ) -
        (a : ℝ) * (2 * (a : ℝ) + (b : ℝ)) /
          ((a : ℝ) + (b : ℝ) + (c : ℝ)) := by
  have hA : 0 < (a : ℝ) := by exact_mod_cast ha
  have hC : (c : ℝ) < 0 := by exact_mod_cast hc
  have hsumR : (a : ℝ) + (b : ℝ) + (c : ℝ) < 0 := by exact_mod_cast hsum
  have hlamgt : 1 < lam :=
    quadratic_root_gt_one hA hC hsumR hlampos hlamroot
  have hmurootR :
      (a : ℝ) * mu ^ 2 + (-2 * (a : ℝ) - (b : ℝ)) * mu +
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) = 0 := by
    push_cast at hmuroot
    convert hmuroot using 1 <;> ring_nf
  have hmu_at_one :
      (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) +
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) < 0 := by
    have : (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) +
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) = (c : ℝ) := by ring
    rw [this]
    exact hC
  have hmu_gt : 1 < mu :=
    quadratic_root_gt_one hA hsumR hmu_at_one hmupos hmurootR
  have hmuunique' : ∀ x : ℝ, 0 < x →
      (a : ℝ) * x ^ 2 + (-2 * (a : ℝ) - (b : ℝ)) * x +
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) = 0 → x = mu := by
    intro x hx hxroot
    apply hmuunique x hx
    push_cast
    convert hxroot using 1 <;> ring_nf
  have hrel : 1 - (c : ℝ) / ((a : ℝ) * lam) = mu :=
    transformed_root_relation hA hC hlampos hlamroot hmuunique'
  have hAne : (a : ℝ) ≠ 0 := ne_of_gt hA
  have hlamne : lam ≠ 0 := ne_of_gt hlampos
  have hCne : (c : ℝ) ≠ 0 := ne_of_lt hC
  have hsumne : (a : ℝ) + (b : ℝ) + (c : ℝ) ≠ 0 := ne_of_lt hsumR
  have hcdiv : (c : ℝ) / ((a : ℝ) * lam) = -((b : ℝ) / (a : ℝ)) - lam := by
    field_simp [hAne,hlamne]
    nlinarith [hlamroot]
  have hmlin : mu = lam + 1 + (b : ℝ) / (a : ℝ) := by
    linarith [hrel,hcdiv]
  have hVlam := quadratic_volume_eq hA hC hsumR hlampos hlamgt hlamroot
  have hVmu := quadratic_volume_eq hA hsumR hmu_at_one hmupos hmu_gt hmurootR
  have hfmu : (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) +
      ((a : ℝ) + (b : ℝ) + (c : ℝ)) = (c : ℝ) := by ring
  rw [hfmu] at hVmu
  have hquad := quadratic_sum_from_relation hAne hlamroot hmlin
  have hrC := rational_c_sum_from_relation hAne hCne hmlin
  have hrD := rational_d_sum_from_relation hAne hsumne hmlin
  rw [hVlam, hVmu]
  have harrange :
      ((a : ℝ) * (lam ^ 2 - lam) + 2 * (a : ℝ) +
          (a : ℝ) * ((a : ℝ) * lam + (b : ℝ)) / (c : ℝ) -
          (a : ℝ) * ((a : ℝ) * lam + (a : ℝ) + (b : ℝ)) /
            ((a : ℝ) + (b : ℝ) + (c : ℝ))) +
        ((a : ℝ) * (mu ^ 2 - mu) + 2 * (a : ℝ) +
          (a : ℝ) * ((a : ℝ) * mu + (-2 * (a : ℝ) - (b : ℝ))) /
            ((a : ℝ) + (b : ℝ) + (c : ℝ)) -
          (a : ℝ) * ((a : ℝ) * mu + (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ))) /
            (c : ℝ)) =
      ((a : ℝ) * (lam ^ 2 - lam) + (a : ℝ) * (mu ^ 2 - mu)) +
        4 * (a : ℝ) +
        ((a : ℝ) * ((a : ℝ) * lam + (b : ℝ)) / (c : ℝ) -
          (a : ℝ) * ((a : ℝ) * mu - (a : ℝ) - (b : ℝ)) / (c : ℝ)) +
        (- (a : ℝ) * ((a : ℝ) * lam + (a : ℝ) + (b : ℝ)) /
            ((a : ℝ) + (b : ℝ) + (c : ℝ)) +
          (a : ℝ) * ((a : ℝ) * mu - 2 * (a : ℝ) - (b : ℝ)) /
            ((a : ℝ) + (b : ℝ) + (c : ℝ))) := by
    ring
  rw [harrange, hquad, hrC, hrD]
  ring
