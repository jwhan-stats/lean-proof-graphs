import Mathlib

/-!
Concrete semantic dependency-graph certificate for rollout p1662.

Every `edge_h...` theorem below has the concrete proposition premises recorded
for that selected hyperedge.  The final theorem composes those edge proofs and
restates the original rollout theorem exactly.  The original theorem itself is
not used as a shortcut.
-/

-- graph_id: p1662_binary_quadratic_form_volume_identity
-- certificate_kind: reviewed_edge_theorems
-- topology_sha256: 36740eb1859b61cc84e98c0fba8102c8ee8ee7c1504f40a8dff4ff09d88d2761
-- reconstructed_proof_sha256: 21afe756275a961c4381bc5359a7ca8d9972574331648a2f3086e58cfa9305f8
-- selected_edge_count: 22

namespace P1662ConcreteSemanticGraph

/- Atomic rollout helpers, including their executable proofs. -/

private lemma quadratic_root_gt_one {A B C q : ℝ}
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

private lemma transformed_root_relation {A B C lam mu : ℝ}
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

private lemma quadratic_volume_eq {A B C x : ℝ}
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

private lemma quadratic_sum_from_relation {A B C lam mu : ℝ}
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

private lemma rational_c_sum_from_relation {A B C lam mu : ℝ}
    (hA : A ≠ 0) (hC : C ≠ 0)
    (hrel : mu = lam + 1 + B / A) :
    A * (A * lam + B) / C -
        A * (A * mu - A - B) / C = A * B / C := by
  rw [hrel]
  field_simp [hA,hC]
  ring

private lemma rational_d_sum_from_relation {A B C lam mu : ℝ}
    (hA : A ≠ 0) (hd : A+B+C ≠ 0)
    (hrel : mu = lam + 1 + B / A) :
    - A * (A * lam + A + B) / (A+B+C) +
        A * (A * mu - 2*A - B) / (A+B+C) =
      - A * (2*A+B)/(A+B+C) := by
  rw [hrel]
  field_simp [hA,hd]
  ring

/- Concrete selected hyperedges.  The theorem arguments are exactly the
proposition premises recorded for each graph edge; ordinary data parameters
are not graph nodes. -/

theorem edge_h_001_ha {a : ℤ} (ha : 0 < a) : 0 < (a : ℝ) := by
  exact_mod_cast ha

theorem edge_h_002_hc {c : ℤ} (hc : c < 0) : (c : ℝ) < 0 := by
  exact_mod_cast hc

theorem edge_h_003_hsumr {a b c : ℤ} (hsum : a + b + c < 0) :
    (a : ℝ) + (b : ℝ) + (c : ℝ) < 0 := by
  exact_mod_cast hsum

theorem edge_h_004_hlamgt {a b c : ℤ} {lam : ℝ}
    (hlamroot : (a : ℝ) * lam ^ 2 + (b : ℝ) * lam + (c : ℝ) = 0)
    (hlampos : 0 < lam)
    (hA : 0 < (a : ℝ))
    (hC : (c : ℝ) < 0)
    (hsumR : (a : ℝ) + (b : ℝ) + (c : ℝ) < 0) :
    1 < lam := by
  exact quadratic_root_gt_one hA hC hsumR hlampos hlamroot

theorem edge_h_005_hmurootr {a b c : ℤ} {mu : ℝ}
    (hmuroot :
      (a : ℝ) * mu ^ 2 + ((-2 * a - b : ℤ) : ℝ) * mu +
        ((a + b + c : ℤ) : ℝ) = 0) :
    (a : ℝ) * mu ^ 2 + (-2 * (a : ℝ) - (b : ℝ)) * mu +
      ((a : ℝ) + (b : ℝ) + (c : ℝ)) = 0 := by
  push_cast at hmuroot
  convert hmuroot using 1 <;> ring_nf

theorem edge_h_006_hmu_at_one {a b c : ℤ}
    (hC : (c : ℝ) < 0) :
    (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) +
      ((a : ℝ) + (b : ℝ) + (c : ℝ)) < 0 := by
  have h : (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) +
      ((a : ℝ) + (b : ℝ) + (c : ℝ)) = (c : ℝ) := by ring
  rw [h]
  exact hC

theorem edge_h_007_hmu_gt {a b c : ℤ} {mu : ℝ}
    (hmupos : 0 < mu)
    (hA : 0 < (a : ℝ))
    (hsumR : (a : ℝ) + (b : ℝ) + (c : ℝ) < 0)
    (hmurootR :
      (a : ℝ) * mu ^ 2 + (-2 * (a : ℝ) - (b : ℝ)) * mu +
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) = 0)
    (hmu_at_one :
      (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) +
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) < 0) :
    1 < mu := by
  exact quadratic_root_gt_one hA hsumR hmu_at_one hmupos hmurootR

theorem edge_h_008_hmuunique {a b c : ℤ} {mu : ℝ}
    (hmuunique : ∀ x : ℝ,
      0 < x →
        (a : ℝ) * x ^ 2 + ((-2 * a - b : ℤ) : ℝ) * x +
          ((a + b + c : ℤ) : ℝ) = 0 →
        x = mu) :
    ∀ x : ℝ, 0 < x →
      (a : ℝ) * x ^ 2 + (-2 * (a : ℝ) - (b : ℝ)) * x +
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) = 0 → x = mu := by
  intro x hx hxroot
  apply hmuunique x hx
  push_cast
  convert hxroot using 1 <;> ring_nf

theorem edge_h_009_hrel {a b c : ℤ} {lam mu : ℝ}
    (hlamroot : (a : ℝ) * lam ^ 2 + (b : ℝ) * lam + (c : ℝ) = 0)
    (hlampos : 0 < lam)
    (hA : 0 < (a : ℝ))
    (hC : (c : ℝ) < 0)
    (hmuunique' : ∀ x : ℝ, 0 < x →
      (a : ℝ) * x ^ 2 + (-2 * (a : ℝ) - (b : ℝ)) * x +
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) = 0 → x = mu) :
    1 - (c : ℝ) / ((a : ℝ) * lam) = mu := by
  exact transformed_root_relation hA hC hlampos hlamroot hmuunique'

theorem edge_h_010_hane {a : ℤ}
    (hA : 0 < (a : ℝ)) : (a : ℝ) ≠ 0 := by
  exact ne_of_gt hA

theorem edge_h_011_hlamne {lam : ℝ}
    (hlampos : 0 < lam) : lam ≠ 0 := by
  exact ne_of_gt hlampos

theorem edge_h_012_hcne {c : ℤ}
    (hC : (c : ℝ) < 0) : (c : ℝ) ≠ 0 := by
  exact ne_of_lt hC

theorem edge_h_013_hsumne {a b c : ℤ}
    (hsumR : (a : ℝ) + (b : ℝ) + (c : ℝ) < 0) :
    (a : ℝ) + (b : ℝ) + (c : ℝ) ≠ 0 := by
  exact ne_of_lt hsumR

theorem edge_h_014_hcdiv {a b c : ℤ} {lam : ℝ}
    (hlamroot : (a : ℝ) * lam ^ 2 + (b : ℝ) * lam + (c : ℝ) = 0)
    (hAne : (a : ℝ) ≠ 0)
    (hlamne : lam ≠ 0) :
    (c : ℝ) / ((a : ℝ) * lam) = -((b : ℝ) / (a : ℝ)) - lam := by
  field_simp [hAne,hlamne]
  nlinarith [hlamroot]

theorem edge_h_015_hmlin {a b c : ℤ} {lam mu : ℝ}
    (hrel : 1 - (c : ℝ) / ((a : ℝ) * lam) = mu)
    (hcdiv : (c : ℝ) / ((a : ℝ) * lam) = -((b : ℝ) / (a : ℝ)) - lam) :
    mu = lam + 1 + (b : ℝ) / (a : ℝ) := by
  linarith [hrel,hcdiv]

theorem edge_h_016_hvlam {a b c : ℤ} {lam : ℝ}
    (hlamroot : (a : ℝ) * lam ^ 2 + (b : ℝ) * lam + (c : ℝ) = 0)
    (hlampos : 0 < lam)
    (hA : 0 < (a : ℝ))
    (hC : (c : ℝ) < 0)
    (hsumR : (a : ℝ) + (b : ℝ) + (c : ℝ) < 0)
    (hlamgt : 1 < lam) :
    (a : ℝ) * lam * (lam - 1) *
        (1 + 1 / lam ^ 2 + 1 / (lam - 1) ^ 2) =
      (a : ℝ) * (lam ^ 2 - lam) + 2 * (a : ℝ) +
        (a : ℝ) * ((a : ℝ) * lam + (b : ℝ)) / (c : ℝ) -
        (a : ℝ) * ((a : ℝ) * lam + (a : ℝ) + (b : ℝ)) /
          ((a : ℝ) + (b : ℝ) + (c : ℝ)) := by
  exact quadratic_volume_eq hA hC hsumR hlampos hlamgt hlamroot

theorem edge_h_017_hvmu {a b c : ℤ} {mu : ℝ}
    (hmupos : 0 < mu)
    (hA : 0 < (a : ℝ))
    (hsumR : (a : ℝ) + (b : ℝ) + (c : ℝ) < 0)
    (hmurootR :
      (a : ℝ) * mu ^ 2 + (-2 * (a : ℝ) - (b : ℝ)) * mu +
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) = 0)
    (hmu_at_one :
      (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) +
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) < 0)
    (hmu_gt : 1 < mu) :
    (a : ℝ) * mu * (mu - 1) *
        (1 + 1 / mu ^ 2 + 1 / (mu - 1) ^ 2) =
      (a : ℝ) * (mu ^ 2 - mu) + 2 * (a : ℝ) +
        (a : ℝ) * ((a : ℝ) * mu + (-2 * (a : ℝ) - (b : ℝ))) /
          ((a : ℝ) + (b : ℝ) + (c : ℝ)) -
        (a : ℝ) * ((a : ℝ) * mu + (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ))) /
          ((a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) +
            ((a : ℝ) + (b : ℝ) + (c : ℝ))) := by
  exact quadratic_volume_eq hA hsumR hmu_at_one hmupos hmu_gt hmurootR

theorem edge_h_018_hfmu (a b c : ℤ) :
    (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) +
      ((a : ℝ) + (b : ℝ) + (c : ℝ)) = (c : ℝ) := by
  ring

theorem edge_h_019_hquad {a b c : ℤ} {lam mu : ℝ}
    (hlamroot : (a : ℝ) * lam ^ 2 + (b : ℝ) * lam + (c : ℝ) = 0)
    (hAne : (a : ℝ) ≠ 0)
    (hmlin : mu = lam + 1 + (b : ℝ) / (a : ℝ)) :
    (a : ℝ) * (lam ^ 2 - lam) + (a : ℝ) * (mu ^ 2 - mu) =
      (b : ℝ) + (b : ℝ) ^ 2 / (a : ℝ) - 2 * (c : ℝ) := by
  exact quadratic_sum_from_relation hAne hlamroot hmlin

theorem edge_h_020_hrc {a b c : ℤ} {lam mu : ℝ}
    (hAne : (a : ℝ) ≠ 0)
    (hCne : (c : ℝ) ≠ 0)
    (hmlin : mu = lam + 1 + (b : ℝ) / (a : ℝ)) :
    (a : ℝ) * ((a : ℝ) * lam + (b : ℝ)) / (c : ℝ) -
      (a : ℝ) * ((a : ℝ) * mu - (a : ℝ) - (b : ℝ)) / (c : ℝ) =
        (a : ℝ) * (b : ℝ) / (c : ℝ) := by
  exact rational_c_sum_from_relation hAne hCne hmlin

theorem edge_h_021_hrd {a b c : ℤ} {lam mu : ℝ}
    (hAne : (a : ℝ) ≠ 0)
    (hsumne : (a : ℝ) + (b : ℝ) + (c : ℝ) ≠ 0)
    (hmlin : mu = lam + 1 + (b : ℝ) / (a : ℝ)) :
    - (a : ℝ) * ((a : ℝ) * lam + (a : ℝ) + (b : ℝ)) /
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) +
      (a : ℝ) * ((a : ℝ) * mu - 2 * (a : ℝ) - (b : ℝ)) /
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) =
      - (a : ℝ) * (2 * (a : ℝ) + (b : ℝ)) /
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) := by
  exact rational_d_sum_from_relation hAne hsumne hmlin

theorem edge_h_goal {a b c : ℤ} {lam mu : ℝ}
    (hVlam :
      (a : ℝ) * lam * (lam - 1) *
          (1 + 1 / lam ^ 2 + 1 / (lam - 1) ^ 2) =
        (a : ℝ) * (lam ^ 2 - lam) + 2 * (a : ℝ) +
          (a : ℝ) * ((a : ℝ) * lam + (b : ℝ)) / (c : ℝ) -
          (a : ℝ) * ((a : ℝ) * lam + (a : ℝ) + (b : ℝ)) /
            ((a : ℝ) + (b : ℝ) + (c : ℝ)))
    (hVmu :
      (a : ℝ) * mu * (mu - 1) *
          (1 + 1 / mu ^ 2 + 1 / (mu - 1) ^ 2) =
        (a : ℝ) * (mu ^ 2 - mu) + 2 * (a : ℝ) +
          (a : ℝ) * ((a : ℝ) * mu + (-2 * (a : ℝ) - (b : ℝ))) /
            ((a : ℝ) + (b : ℝ) + (c : ℝ)) -
          (a : ℝ) * ((a : ℝ) * mu + (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ))) /
            ((a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) +
              ((a : ℝ) + (b : ℝ) + (c : ℝ))))
    (hfmu :
      (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) +
        ((a : ℝ) + (b : ℝ) + (c : ℝ)) = (c : ℝ))
    (hquad :
      (a : ℝ) * (lam ^ 2 - lam) + (a : ℝ) * (mu ^ 2 - mu) =
        (b : ℝ) + (b : ℝ) ^ 2 / (a : ℝ) - 2 * (c : ℝ))
    (hrC :
      (a : ℝ) * ((a : ℝ) * lam + (b : ℝ)) / (c : ℝ) -
        (a : ℝ) * ((a : ℝ) * mu - (a : ℝ) - (b : ℝ)) / (c : ℝ) =
          (a : ℝ) * (b : ℝ) / (c : ℝ))
    (hrD :
      - (a : ℝ) * ((a : ℝ) * lam + (a : ℝ) + (b : ℝ)) /
          ((a : ℝ) + (b : ℝ) + (c : ℝ)) +
        (a : ℝ) * ((a : ℝ) * mu - 2 * (a : ℝ) - (b : ℝ)) /
          ((a : ℝ) + (b : ℝ) + (c : ℝ)) =
        - (a : ℝ) * (2 * (a : ℝ) + (b : ℝ)) /
          ((a : ℝ) + (b : ℝ) + (c : ℝ))) :
    (a : ℝ) * lam * (lam - 1) *
          (1 + 1 / lam ^ 2 + 1 / (lam - 1) ^ 2) +
        (a : ℝ) * mu * (mu - 1) *
          (1 + 1 / mu ^ 2 + 1 / (mu - 1) ^ 2) =
      4 * (a : ℝ) + (b : ℝ) + (b : ℝ) ^ 2 / (a : ℝ) +
        (a : ℝ) * (b : ℝ) / (c : ℝ) - 2 * (c : ℝ) -
        (a : ℝ) * (2 * (a : ℝ) + (b : ℝ)) /
          ((a : ℝ) + (b : ℝ) + (c : ℝ)) := by
  rw [hfmu] at hVmu
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

/- Exact final anchor: the original theorem statement, proved only by the
concrete graph edges above. -/

theorem graph_derives_binary_quadratic_form_volume_identity
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
  have hA := edge_h_001_ha ha
  have hC := edge_h_002_hc hc
  have hsumR := edge_h_003_hsumr hsum
  have hlamgt := edge_h_004_hlamgt hlamroot hlampos hA hC hsumR
  have hmurootR := edge_h_005_hmurootr hmuroot
  have hmu_at_one := edge_h_006_hmu_at_one (a := a) (b := b) hC
  have hmu_gt := edge_h_007_hmu_gt hmupos hA hsumR hmurootR hmu_at_one
  have hmuunique' := edge_h_008_hmuunique hmuunique
  have hrel := edge_h_009_hrel hlamroot hlampos hA hC hmuunique'
  have hAne := edge_h_010_hane hA
  have hlamne := edge_h_011_hlamne hlampos
  have hCne := edge_h_012_hcne hC
  have hsumne := edge_h_013_hsumne hsumR
  have hcdiv := edge_h_014_hcdiv hlamroot hAne hlamne
  have hmlin := edge_h_015_hmlin hrel hcdiv
  have hVlam := edge_h_016_hvlam hlamroot hlampos hA hC hsumR hlamgt
  have hVmu := edge_h_017_hvmu hmupos hA hsumR hmurootR hmu_at_one hmu_gt
  have hfmu := edge_h_018_hfmu a b c
  have hquad := edge_h_019_hquad hlamroot hAne hmlin
  have hrC := edge_h_020_hrc hAne hCne hmlin
  have hrD := edge_h_021_hrd hAne hsumne hmlin
  exact edge_h_goal hVlam hVmu hfmu hquad hrC hrD

end P1662ConcreteSemanticGraph

/- Generated exact graph/type bridge. Do not edit this section.
Each example applies the reviewed concrete edge theorem to precisely
the premise and conclusion propositions rendered in graph.json. -/
-- generated_bridge_topology_sha256: 36740eb1859b61cc84e98c0fba8102c8ee8ee7c1504f40a8dff4ff09d88d2761
namespace ConcreteGraphTypeBridge_p1662_binary_quadratic_form_volume_identity

variable (a b c : ℤ)
variable (lam mu : ℝ)

-- graph edge: h_001_ha
example
    (P001 : 0 < a)
    : 0 < (a : ℝ) := by
  exact P1662ConcreteSemanticGraph.edge_h_001_ha (a := a) P001

-- graph edge: h_002_hc
example
    (P001 : c < 0)
    : (c : ℝ) < 0 := by
  exact P1662ConcreteSemanticGraph.edge_h_002_hc (c := c) P001

-- graph edge: h_003_hsumr
example
    (P001 : a + b + c < 0)
    : (a : ℝ) + (b : ℝ) + (c : ℝ) < 0 := by
  exact P1662ConcreteSemanticGraph.edge_h_003_hsumr (a := a) (b := b) (c := c) P001

-- graph edge: h_005_hmurootr
example
    (P001 : (a : ℝ) * mu ^ 2 + ((-2 * a - b : ℤ) : ℝ) * mu + ((a + b + c : ℤ) : ℝ) = 0)
    : (a : ℝ) * mu ^ 2 + (-2 * (a : ℝ) - (b : ℝ)) * mu + ((a : ℝ) + (b : ℝ) + (c : ℝ)) = 0 := by
  exact P1662ConcreteSemanticGraph.edge_h_005_hmurootr (a := a) (b := b) (c := c) (mu := mu) P001

-- graph edge: h_008_hmuunique
example
    (P001 : ∀ (x : ℝ), 0 < x → (a : ℝ) * x ^ 2 + ((-2 * a - b : ℤ) : ℝ) * x + ((a + b + c : ℤ) : ℝ) = 0 → x = mu)
    : ∀ (x : ℝ), 0 < x → (a : ℝ) * x ^ 2 + (-2 * (a : ℝ) - (b : ℝ)) * x + ((a : ℝ) + (b : ℝ) + (c : ℝ)) = 0 → x = mu := by
  exact P1662ConcreteSemanticGraph.edge_h_008_hmuunique (a := a) (b := b) (c := c) (mu := mu) P001

-- graph edge: h_011_hlamne
example
    (P001 : 0 < lam)
    : lam ≠ 0 := by
  exact P1662ConcreteSemanticGraph.edge_h_011_hlamne (lam := lam) P001

-- graph edge: h_018_hfmu
example
    : (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) + ((a : ℝ) + (b : ℝ) + (c : ℝ)) = (c : ℝ) := by
  exact P1662ConcreteSemanticGraph.edge_h_018_hfmu (a := a) (b := b) (c := c)

-- graph edge: h_004_hlamgt
example
    (P001 : (a : ℝ) * lam ^ 2 + (b : ℝ) * lam + (c : ℝ) = 0)
    (P002 : 0 < lam)
    (P003 : 0 < (a : ℝ))
    (P004 : (c : ℝ) < 0)
    (P005 : (a : ℝ) + (b : ℝ) + (c : ℝ) < 0)
    : 1 < lam := by
  exact P1662ConcreteSemanticGraph.edge_h_004_hlamgt (a := a) (b := b) (c := c) (lam := lam) P001 P002 P003 P004 P005

-- graph edge: h_006_hmu_at_one
example
    (P001 : (c : ℝ) < 0)
    : (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) + ((a : ℝ) + (b : ℝ) + (c : ℝ)) < 0 := by
  exact P1662ConcreteSemanticGraph.edge_h_006_hmu_at_one (a := a) (b := b) (c := c) P001

-- graph edge: h_009_hrel
example
    (P001 : (a : ℝ) * lam ^ 2 + (b : ℝ) * lam + (c : ℝ) = 0)
    (P002 : 0 < lam)
    (P003 : 0 < (a : ℝ))
    (P004 : (c : ℝ) < 0)
    (P005 : ∀ (x : ℝ), 0 < x → (a : ℝ) * x ^ 2 + (-2 * (a : ℝ) - (b : ℝ)) * x + ((a : ℝ) + (b : ℝ) + (c : ℝ)) = 0 → x = mu)
    : 1 - (c : ℝ) / ((a : ℝ) * lam) = mu := by
  exact P1662ConcreteSemanticGraph.edge_h_009_hrel (a := a) (b := b) (c := c) (lam := lam) (mu := mu) P001 P002 P003 P004 P005

-- graph edge: h_010_hane
example
    (P001 : 0 < (a : ℝ))
    : (a : ℝ) ≠ 0 := by
  exact P1662ConcreteSemanticGraph.edge_h_010_hane (a := a) P001

-- graph edge: h_012_hcne
example
    (P001 : (c : ℝ) < 0)
    : (c : ℝ) ≠ 0 := by
  exact P1662ConcreteSemanticGraph.edge_h_012_hcne (c := c) P001

-- graph edge: h_013_hsumne
example
    (P001 : (a : ℝ) + (b : ℝ) + (c : ℝ) < 0)
    : (a : ℝ) + (b : ℝ) + (c : ℝ) ≠ 0 := by
  exact P1662ConcreteSemanticGraph.edge_h_013_hsumne (a := a) (b := b) (c := c) P001

-- graph edge: h_007_hmu_gt
example
    (P001 : 0 < mu)
    (P002 : 0 < (a : ℝ))
    (P003 : (a : ℝ) + (b : ℝ) + (c : ℝ) < 0)
    (P004 : (a : ℝ) * mu ^ 2 + (-2 * (a : ℝ) - (b : ℝ)) * mu + ((a : ℝ) + (b : ℝ) + (c : ℝ)) = 0)
    (P005 : (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) + ((a : ℝ) + (b : ℝ) + (c : ℝ)) < 0)
    : 1 < mu := by
  exact P1662ConcreteSemanticGraph.edge_h_007_hmu_gt (a := a) (b := b) (c := c) (mu := mu) P001 P002 P003 P004 P005

-- graph edge: h_014_hcdiv
example
    (P001 : (a : ℝ) * lam ^ 2 + (b : ℝ) * lam + (c : ℝ) = 0)
    (P002 : (a : ℝ) ≠ 0)
    (P003 : lam ≠ 0)
    : (c : ℝ) / ((a : ℝ) * lam) = -((b : ℝ) / (a : ℝ)) - lam := by
  exact P1662ConcreteSemanticGraph.edge_h_014_hcdiv (a := a) (b := b) (c := c) (lam := lam) P001 P002 P003

-- graph edge: h_016_hvlam
example
    (P001 : (a : ℝ) * lam ^ 2 + (b : ℝ) * lam + (c : ℝ) = 0)
    (P002 : 0 < lam)
    (P003 : 0 < (a : ℝ))
    (P004 : (c : ℝ) < 0)
    (P005 : (a : ℝ) + (b : ℝ) + (c : ℝ) < 0)
    (P006 : 1 < lam)
    : (a : ℝ) * lam * (lam - 1) * (1 + 1 / lam ^ 2 + 1 / (lam - 1) ^ 2) = (a : ℝ) * (lam ^ 2 - lam) + 2 * (a : ℝ) + (a : ℝ) * ((a : ℝ) * lam + (b : ℝ)) / (c : ℝ) - (a : ℝ) * ((a : ℝ) * lam + (a : ℝ) + (b : ℝ)) / ((a : ℝ) + (b : ℝ) + (c : ℝ)) := by
  exact P1662ConcreteSemanticGraph.edge_h_016_hvlam (a := a) (b := b) (c := c) (lam := lam) P001 P002 P003 P004 P005 P006

-- graph edge: h_015_hmlin
example
    (P001 : 1 - (c : ℝ) / ((a : ℝ) * lam) = mu)
    (P002 : (c : ℝ) / ((a : ℝ) * lam) = -((b : ℝ) / (a : ℝ)) - lam)
    : mu = lam + 1 + (b : ℝ) / (a : ℝ) := by
  exact P1662ConcreteSemanticGraph.edge_h_015_hmlin (a := a) (b := b) (c := c) (lam := lam) (mu := mu) P001 P002

-- graph edge: h_017_hvmu
example
    (P001 : 0 < mu)
    (P002 : 0 < (a : ℝ))
    (P003 : (a : ℝ) + (b : ℝ) + (c : ℝ) < 0)
    (P004 : (a : ℝ) * mu ^ 2 + (-2 * (a : ℝ) - (b : ℝ)) * mu + ((a : ℝ) + (b : ℝ) + (c : ℝ)) = 0)
    (P005 : (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) + ((a : ℝ) + (b : ℝ) + (c : ℝ)) < 0)
    (P006 : 1 < mu)
    : (a : ℝ) * mu * (mu - 1) * (1 + 1 / mu ^ 2 + 1 / (mu - 1) ^ 2) = (a : ℝ) * (mu ^ 2 - mu) + 2 * (a : ℝ) + (a : ℝ) * ((a : ℝ) * mu + (-2 * (a : ℝ) - (b : ℝ))) / ((a : ℝ) + (b : ℝ) + (c : ℝ)) - (a : ℝ) * ((a : ℝ) * mu + (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ))) / ((a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) + ((a : ℝ) + (b : ℝ) + (c : ℝ))) := by
  exact P1662ConcreteSemanticGraph.edge_h_017_hvmu (a := a) (b := b) (c := c) (mu := mu) P001 P002 P003 P004 P005 P006

-- graph edge: h_019_hquad
example
    (P001 : (a : ℝ) * lam ^ 2 + (b : ℝ) * lam + (c : ℝ) = 0)
    (P002 : (a : ℝ) ≠ 0)
    (P003 : mu = lam + 1 + (b : ℝ) / (a : ℝ))
    : (a : ℝ) * (lam ^ 2 - lam) + (a : ℝ) * (mu ^ 2 - mu) = (b : ℝ) + (b : ℝ) ^ 2 / (a : ℝ) - 2 * (c : ℝ) := by
  exact P1662ConcreteSemanticGraph.edge_h_019_hquad (a := a) (b := b) (c := c) (lam := lam) (mu := mu) P001 P002 P003

-- graph edge: h_020_hrc
example
    (P001 : (a : ℝ) ≠ 0)
    (P002 : (c : ℝ) ≠ 0)
    (P003 : mu = lam + 1 + (b : ℝ) / (a : ℝ))
    : (a : ℝ) * ((a : ℝ) * lam + (b : ℝ)) / (c : ℝ) - (a : ℝ) * ((a : ℝ) * mu - (a : ℝ) - (b : ℝ)) / (c : ℝ) = (a : ℝ) * (b : ℝ) / (c : ℝ) := by
  exact P1662ConcreteSemanticGraph.edge_h_020_hrc (a := a) (b := b) (c := c) (lam := lam) (mu := mu) P001 P002 P003

-- graph edge: h_021_hrd
example
    (P001 : (a : ℝ) ≠ 0)
    (P002 : (a : ℝ) + (b : ℝ) + (c : ℝ) ≠ 0)
    (P003 : mu = lam + 1 + (b : ℝ) / (a : ℝ))
    : -(a : ℝ) * ((a : ℝ) * lam + (a : ℝ) + (b : ℝ)) / ((a : ℝ) + (b : ℝ) + (c : ℝ)) + (a : ℝ) * ((a : ℝ) * mu - 2 * (a : ℝ) - (b : ℝ)) / ((a : ℝ) + (b : ℝ) + (c : ℝ)) = -(a : ℝ) * (2 * (a : ℝ) + (b : ℝ)) / ((a : ℝ) + (b : ℝ) + (c : ℝ)) := by
  exact P1662ConcreteSemanticGraph.edge_h_021_hrd (a := a) (b := b) (c := c) (lam := lam) (mu := mu) P001 P002 P003

-- graph edge: h_goal
example
    (P001 : (a : ℝ) * lam * (lam - 1) * (1 + 1 / lam ^ 2 + 1 / (lam - 1) ^ 2) = (a : ℝ) * (lam ^ 2 - lam) + 2 * (a : ℝ) + (a : ℝ) * ((a : ℝ) * lam + (b : ℝ)) / (c : ℝ) - (a : ℝ) * ((a : ℝ) * lam + (a : ℝ) + (b : ℝ)) / ((a : ℝ) + (b : ℝ) + (c : ℝ)))
    (P002 : (a : ℝ) * mu * (mu - 1) * (1 + 1 / mu ^ 2 + 1 / (mu - 1) ^ 2) = (a : ℝ) * (mu ^ 2 - mu) + 2 * (a : ℝ) + (a : ℝ) * ((a : ℝ) * mu + (-2 * (a : ℝ) - (b : ℝ))) / ((a : ℝ) + (b : ℝ) + (c : ℝ)) - (a : ℝ) * ((a : ℝ) * mu + (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ))) / ((a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) + ((a : ℝ) + (b : ℝ) + (c : ℝ))))
    (P003 : (a : ℝ) + (-2 * (a : ℝ) - (b : ℝ)) + ((a : ℝ) + (b : ℝ) + (c : ℝ)) = (c : ℝ))
    (P004 : (a : ℝ) * (lam ^ 2 - lam) + (a : ℝ) * (mu ^ 2 - mu) = (b : ℝ) + (b : ℝ) ^ 2 / (a : ℝ) - 2 * (c : ℝ))
    (P005 : (a : ℝ) * ((a : ℝ) * lam + (b : ℝ)) / (c : ℝ) - (a : ℝ) * ((a : ℝ) * mu - (a : ℝ) - (b : ℝ)) / (c : ℝ) = (a : ℝ) * (b : ℝ) / (c : ℝ))
    (P006 : -(a : ℝ) * ((a : ℝ) * lam + (a : ℝ) + (b : ℝ)) / ((a : ℝ) + (b : ℝ) + (c : ℝ)) + (a : ℝ) * ((a : ℝ) * mu - 2 * (a : ℝ) - (b : ℝ)) / ((a : ℝ) + (b : ℝ) + (c : ℝ)) = -(a : ℝ) * (2 * (a : ℝ) + (b : ℝ)) / ((a : ℝ) + (b : ℝ) + (c : ℝ)))
    : (a : ℝ) * lam * (lam - 1) * (1 + 1 / lam ^ 2 + 1 / (lam - 1) ^ 2) + (a : ℝ) * mu * (mu - 1) * (1 + 1 / mu ^ 2 + 1 / (mu - 1) ^ 2) = 4 * (a : ℝ) + (b : ℝ) + (b : ℝ) ^ 2 / (a : ℝ) + (a : ℝ) * (b : ℝ) / (c : ℝ) - 2 * (c : ℝ) - (a : ℝ) * (2 * (a : ℝ) + (b : ℝ)) / ((a : ℝ) + (b : ℝ) + (c : ℝ)) := by
  exact P1662ConcreteSemanticGraph.edge_h_goal (a := a) (b := b) (c := c) (lam := lam) (mu := mu) P001 P002 P003 P004 P005 P006

end ConcreteGraphTypeBridge_p1662_binary_quadratic_form_volume_identity
