import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p3255_horseshoelikepenalty_strictconcave
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 35d8c5ea9a37d2b8ec8b339d43d5d2f09b426f320a12ddbb467aa4c09e83f31b
-- reconstructed_proof_sha256: 41101667f44f50494fabd24699c51bd975f8acf936333a2d7c4512aa4f09cec5
-- selected_edge_count: 1

/- accepted add_to_file helper 1 -/

open Set Real Filter

lemma h_hasDerivAt {a x : ℝ} (ha : 0 < a) (hx : x ≠ 0) :
    HasDerivAt (fun x => Real.log (1 + a / x ^ 2))
      (-2 * a / (x * (x ^ 2 + a))) x := by
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hdiv : HasDerivAt (fun x : ℝ => a / x ^ 2)
      ((0 * x ^ 2 - a * (2 * x)) / (x ^ 2) ^ 2) x := by
    exact (hasDerivAt_const x a).div hsq (pow_ne_zero 2 hx)
  have harg : HasDerivAt (fun x : ℝ => 1 + a / x ^ 2)
      (0 + (0 * x ^ 2 - a * (2 * x)) / (x ^ 2) ^ 2) x := by
    exact (hasDerivAt_const x 1).add hdiv
  have hne : (1 + a / x ^ 2) ≠ 0 := by
    positivity
  have hlog := harg.log hne
  convert hlog using 1
  field_simp [hx, ha.ne']
  ring

lemma h_deriv2_hasDerivAt {a x : ℝ} (ha : 0 < a) (hx : x ≠ 0) :
    HasDerivAt (fun x => -2 * a / (x * (x ^ 2 + a)))
      (2 * a * (3 * x ^ 2 + a) / (x ^ 2 * (x ^ 2 + a) ^ 2)) x := by
  have hinner : HasDerivAt (fun x : ℝ => x ^ 2 + a) (2 * x) x := by
    convert ((hasDerivAt_pow 2 x).add (hasDerivAt_const x a)) using 1
    ring
  have hd : HasDerivAt (fun x : ℝ => x * (x ^ 2 + a))
      (1 * (x ^ 2 + a) + x * (2 * x)) x := by
    exact (hasDerivAt_id x).mul hinner
  have hden : x * (x ^ 2 + a) ≠ 0 := by
    positivity
  have hdiv := (hasDerivAt_const x (-2 * a)).div hd hden
  convert hdiv using 1
  field_simp [hx, ha.ne']
  ring

/- accepted add_to_file helper 2 -/
lemma pen_hasDerivAt {a x : ℝ} (ha : 0 < a) (hx : x ≠ 0) :
    HasDerivAt (fun x => -Real.log (Real.log (1 + a / x ^ 2)))
      (2 * a / (x * (x ^ 2 + a) * Real.log (1 + a / x ^ 2))) x := by
  have hh := h_hasDerivAt ha hx
  have hpos : 0 < Real.log (1 + a / x ^ 2) := by
    apply Real.log_pos
    have hq : 0 < a / x ^ 2 := by positivity
    linarith
  have hlog := hh.log (ne_of_gt hpos)
  have hneg := hlog.neg
  convert hneg using 1
  field_simp [hx, ha.ne', ne_of_gt hpos]

/- accepted add_to_file helper 3 -/
lemma pen_deriv2_hasDerivAt {a x : ℝ} (ha : 0 < a) (hx : x ≠ 0) :
    HasDerivAt
      (fun x => 2 * a / (x * (x ^ 2 + a) * Real.log (1 + a / x ^ 2)))
      (-2 * a * ((3 * x ^ 2 + a) * Real.log (1 + a / x ^ 2) - 2 * a) /
        ((x * (x ^ 2 + a)) ^ 2 * (Real.log (1 + a / x ^ 2)) ^ 2)) x := by
  have hinner : HasDerivAt (fun x : ℝ => x ^ 2 + a) (2 * x) x := by
    convert ((hasDerivAt_pow 2 x).add (hasDerivAt_const x a)) using 1
    ring
  have hD : HasDerivAt (fun x : ℝ => x * (x ^ 2 + a))
      (1 * (x ^ 2 + a) + x * (2 * x)) x := by
    exact (hasDerivAt_id x).mul hinner
  have hH := h_hasDerivAt ha hx
  have hden : HasDerivAt
      (fun x : ℝ => x * (x ^ 2 + a) * Real.log (1 + a / x ^ 2))
      ((1 * (x ^ 2 + a) + x * (2 * x)) * Real.log (1 + a / x ^ 2) +
        x * (x ^ 2 + a) * (-2 * a / (x * (x ^ 2 + a)))) x := by
    exact hD.mul hH
  have hHpos : 0 < Real.log (1 + a / x ^ 2) := by
    apply Real.log_pos
    have hq : 0 < a / x ^ 2 := by positivity
    linarith
  have hDne : x * (x ^ 2 + a) ≠ 0 := by positivity
  have hdenne : x * (x ^ 2 + a) * Real.log (1 + a / x ^ 2) ≠ 0 :=
    mul_ne_zero hDne (ne_of_gt hHpos)
  have hdiv := (hasDerivAt_const x (2 * a)).div hden hdenne
  convert hdiv using 1
  field_simp [hx, ha.ne', ne_of_gt hHpos, hDne]
  ring

/- accepted add_to_file helper 4 -/
lemma pen_second_factor_pos {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    0 < (3 * x ^ 2 + a) * Real.log (1 + a / x ^ 2) - 2 * a := by
  let r : ℝ := a / x ^ 2
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hlog : 2 * r / (r + 2) < Real.log (1 + r) := Real.lt_log_one_add_of_pos hr
  have hfrac : 2 * r / (r + 3) < 2 * r / (r + 2) := by
    have hnum : 0 < 2 * r := by positivity
    have hd23 : 0 < r + 2 := by positivity
    have hdle : r + 2 < r + 3 := by linarith
    exact div_lt_div_of_pos_left hnum hd23 hdle
  have hlow : 2 * r / (r + 3) < Real.log (1 + r) := lt_trans hfrac hlog
  have hlow' : 2 * r < (r + 3) * Real.log (1 + r) := by
    rw [mul_comm (r + 3)]
    exact (div_lt_iff₀ (by positivity : 0 < r + 3)).mp hlow
  have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx
  have hmul : 0 < x ^ 2 * ((r + 3) * Real.log (1 + r) - 2 * r) :=
    mul_pos hx2 (sub_pos.mpr hlow')
  have hreq : x ^ 2 * ((r + 3) * Real.log (1 + r) - 2 * r) =
      (3 * x ^ 2 + a) * Real.log (1 + a / x ^ 2) - 2 * a := by
    dsimp [r]
    field_simp [ne_of_gt hx]
    ring
  rwa [hreq] at hmul

/- accepted add_to_file helper 5 -/
lemma pen_strictConcaveOn_pos {a : ℝ} (ha : 0 < a) :
    StrictConcaveOn ℝ (Ioi 0)
      (fun x => -Real.log (Real.log (1 + a / x ^ 2))) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Ioi 0)
  · intro x hx
    exact (pen_hasDerivAt ha (ne_of_gt hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hev : (fun y => deriv (fun x => -Real.log (Real.log (1 + a / x ^ 2))) y)
        =ᶠ[nhds x]
        fun y => 2 * a / (y * (y ^ 2 + a) * Real.log (1 + a / y ^ 2)) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact (pen_hasDerivAt ha (ne_of_gt hy)).deriv
    have h2 : deriv (deriv (fun x => -Real.log (Real.log (1 + a / x ^ 2)))) x =
        -2 * a * ((3 * x ^ 2 + a) * Real.log (1 + a / x ^ 2) - 2 * a) /
          ((x * (x ^ 2 + a)) ^ 2 * (Real.log (1 + a / x ^ 2)) ^ 2) := by
      rw [hev.deriv_eq]
      exact (pen_deriv2_hasDerivAt ha (ne_of_gt hx)).deriv
    have hiter : deriv^[2] (fun x => -Real.log (Real.log (1 + a / x ^ 2))) x =
        deriv (deriv (fun x => -Real.log (Real.log (1 + a / x ^ 2)))) x := rfl
    rw [hiter, h2]
    have hfactor := pen_second_factor_pos ha hx
    have hLpos : 0 < Real.log (1 + a / x ^ 2) := by
      apply Real.log_pos
      have hq : 0 < a / x ^ 2 := div_pos ha (sq_pos_of_pos hx)
      linarith
    have hnum : -2 * a *
        ((3 * x ^ 2 + a) * Real.log (1 + a / x ^ 2) - 2 * a) < 0 := by
      have hcoef : -2 * a < 0 := by nlinarith
      exact mul_neg_of_neg_of_pos hcoef hfactor
    have hden : 0 < (x * (x ^ 2 + a)) ^ 2 *
        (Real.log (1 + a / x ^ 2)) ^ 2 := by
      have hD : 0 < x * (x ^ 2 + a) := by
        exact mul_pos hx (add_pos (sq_pos_of_pos hx) ha)
      exact mul_pos (sq_pos_of_pos hD) (sq_pos_of_pos hLpos)
    exact div_neg_of_neg_of_pos hnum hden

/- verified submission -/
theorem horseshoeLikePenalty_strictConcave (a : ℝ) (ha : 0 < a) :
    let pen_a : ℝ → ℝ := fun x => -Real.log (Real.log (1 + a / x ^ 2))
    ∀ x y t : ℝ,
      x ≠ y →
      ((0 < x ∧ 0 < y) ∨ (x < 0 ∧ y < 0)) →
      0 < t →
      t < 1 →
      pen_a (t * x + (1 - t) * y) >
        t * pen_a x + (1 - t) * pen_a y := by
  dsimp
  intro x y t hxy hs ht ht1
  have hsc := pen_strictConcaveOn_pos ha
  have ht' : 0 < 1 - t := sub_pos.mpr ht1
  have hsum : t + (1 - t) = 1 := by ring
  rcases hs with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact hsc.2 hx hy hxy ht ht' hsum
  · let u : ℝ := -x
    let v : ℝ := -y
    have hu : 0 < u := by
      dsimp [u]
      linarith
    have hv : 0 < v := by
      dsimp [v]
      linarith
    have huv : u ≠ v := by
      intro huv_eq
      apply hxy
      dsimp [u, v] at huv_eq
      linarith
    have hmain := hsc.2 hu hv huv ht ht' hsum
    have hcomb : t * u + (1 - t) * v = -(t * x + (1 - t) * y) := by
      dsimp [u, v]
      ring
    have hsqcomb : (-(t * x + (1 - t) * y)) ^ 2 =
        (t * x + (1 - t) * y) ^ 2 := by ring
    have hsqx : (-x) ^ 2 = x ^ 2 := by ring
    have hsqy : (-y) ^ 2 = y ^ 2 := by ring
    dsimp [u, v] at hmain
    rw [hcomb, hsqcomb, hsqx, hsqy] at hmain
    exact hmain


#check_dependency_graph "horseshoeLikePenalty_strictConcave" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let pen_a := fun x => -Real.log (Real.log (1 + a / x ^ 2)); ∀ (x y t : ℝ), x ≠ y → 0 < x ∧ 0 < y ∨ x < 0 ∧ y < 0 → 0 < t → t < 1 → pen_a (t * x + (1 - t) * y) > t * pen_a x + (1 - t) * pen_a y\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"ha\",\"statement\":\"0 < a\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p3255_horseshoelikepenalty_strictconcave\",\"reconstructedProofSha256\":\"41101667f44f50494fabd24699c51bd975f8acf936333a2d7c4512aa4f09cec5\",\"selectedEdgeCount\":1,\"theoremName\":\"horseshoeLikePenalty_strictConcave\",\"topologySha256\":\"35d8c5ea9a37d2b8ec8b339d43d5d2f09b426f320a12ddbb467aa4c09e83f31b\"}"
