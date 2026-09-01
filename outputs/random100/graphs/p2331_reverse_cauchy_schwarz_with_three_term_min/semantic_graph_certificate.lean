import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p2331_reverse_cauchy_schwarz_with_three_term_min
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: fec88aa8a97a4f2c48e2051cbfc90e6f8d3639b75ec1d7298bc969f8cf03b91b
-- reconstructed_proof_sha256: 1142f8fedc1d083beac4a3e89048b5ec6f4ca63f30f7feb9f0e6155df59e3351
-- selected_edge_count: 1

/- accepted add_to_file helper 1 -/
lemma weighted_variance_bound {n : ℕ} (p z : Fin n → ℝ) (r R : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hzl : ∀ i, r ≤ z i) (hzu : ∀ i, z i ≤ R) :
    (∑ i, p i) * (∑ i, p i * z i ^ 2) - (∑ i, p i * z i) ^ 2 ≤
      (R - r) ^ 2 / 4 * (∑ i, p i) ^ 2 := by
  let U := ∑ i, p i
  let V := ∑ i, p i * z i ^ 2
  let W := ∑ i, p i * z i
  have hU : 0 ≤ U := by
    exact Finset.sum_nonneg fun i _ => hp i
  have hV : V ≤ (r + R) * W - r * R * U := by
    have hpoint : ∀ i ∈ Finset.univ,
        p i * z i ^ 2 ≤ p i * ((r + R) * z i - r * R) := by
      intro i _
      have hzi : z i ^ 2 ≤ (r + R) * z i - r * R := by
        have hnonneg : 0 ≤ (z i - r) * (R - z i) :=
          mul_nonneg (sub_nonneg.mpr (hzl i)) (sub_nonneg.mpr (hzu i))
        nlinarith
      exact mul_le_mul_of_nonneg_left hzi (hp i)
    calc
      V ≤ ∑ i, p i * ((r + R) * z i - r * R) := Finset.sum_le_sum hpoint
      _ = ∑ i, ((p i * z i) * (r + R) - p i * (r * R)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (∑ i, (p i * z i) * (r + R)) - ∑ i, p i * (r * R) := by
        rw [Finset.sum_sub_distrib]
      _ = W * (r + R) - U * (r * R) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
      _ = (r + R) * W - r * R * U := by ring
  have hmul : U * V ≤ U * ((r + R) * W - r * R * U) :=
    mul_le_mul_of_nonneg_left hV hU
  have hsq : 0 ≤ (W - (r + R) * U / 2) ^ 2 := sq_nonneg _
  change U * V - W ^ 2 ≤ (R - r) ^ 2 / 4 * U ^ 2
  nlinarith

/- accepted add_to_file helper 2 -/
lemma interval_variance_bound {n : ℕ}
    (a A b B : ℝ)
    (ha : 0 < a) (haA : a ≤ A) (hb : 0 < b) (hbB : b ≤ B)
    (x y : Fin n → ℝ)
    (hx : ∀ i, a ≤ x i ∧ x i ≤ A)
    (hy : ∀ i, b ≤ y i ∧ y i ≤ B) :
    (∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 ≤
      ((A * B - a * b) ^ 2 / 4) *
        ((∑ i, x i ^ 2) ^ 2 / (A ^ 2 * a ^ 2)) := by
  have hA : 0 < A := lt_of_lt_of_le ha haA
  have hB : 0 < B := lt_of_lt_of_le hb hbB
  have hxpos : ∀ i, 0 < x i := fun i => lt_of_lt_of_le ha (hx i).1
  have hypos : ∀ i, 0 < y i := fun i => lt_of_lt_of_le hb (hy i).1
  have hvarx :
      (∑ i, x i ^ 2) * (∑ i, x i ^ 2 * (y i / x i) ^ 2) -
          (∑ i, x i ^ 2 * (y i / x i)) ^ 2 ≤
        (B / a - b / A) ^ 2 / 4 * (∑ i, x i ^ 2) ^ 2 := by
    apply weighted_variance_bound
    · intro i
      exact sq_nonneg (x i)
    · intro i
      apply (div_le_div_iff₀ hA (hxpos i)).mpr
      calc
        b * x i ≤ y i * x i := mul_le_mul_of_nonneg_right (hy i).1 (hxpos i).le
        _ ≤ y i * A := mul_le_mul_of_nonneg_left (hx i).2 (hypos i).le
    · intro i
      apply (div_le_div_iff₀ (hxpos i) ha).mpr
      calc
        y i * a ≤ B * a := mul_le_mul_of_nonneg_right (hy i).2 ha.le
        _ ≤ B * x i := mul_le_mul_of_nonneg_left (hx i).1 hB.le
  have hVeq : (∑ i, x i ^ 2 * (y i / x i) ^ 2) = ∑ i, y i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    have hxi : x i ≠ 0 := ne_of_gt (hxpos i)
    field_simp [hxi]
  have hWeq : (∑ i, x i ^ 2 * (y i / x i)) = ∑ i, x i * y i := by
    apply Finset.sum_congr rfl
    intro i _
    have hxi : x i ≠ 0 := ne_of_gt (hxpos i)
    field_simp [hxi]
  have hxterm :
      (∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 ≤
        (B / a - b / A) ^ 2 / 4 * (∑ i, x i ^ 2) ^ 2 := by
    simpa [hVeq, hWeq] using hvarx
  calc
    (∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 ≤
        (B / a - b / A) ^ 2 / 4 * (∑ i, x i ^ 2) ^ 2 := hxterm
    _ = ((A * B - a * b) ^ 2 / 4) *
          ((∑ i, x i ^ 2) ^ 2 / (A ^ 2 * a ^ 2)) := by
      field_simp [ha.ne', hA.ne']

/- accepted add_to_file helper 3 -/
lemma interval_cross_bound {n : ℕ}
    (a A b B : ℝ)
    (ha : 0 < a) (haA : a ≤ A) (hb : 0 < b) (hbB : b ≤ B)
    (x y : Fin n → ℝ)
    (hx : ∀ i, a ≤ x i ∧ x i ≤ A)
    (hy : ∀ i, b ≤ y i ∧ y i ≤ B) :
    (∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 ≤
      ((A * B - a * b) ^ 2 / 4) *
        ((∑ i, x i * y i) ^ 2 / (a * b * A * B)) := by
  let U := ∑ i, x i ^ 2
  let V := ∑ i, y i ^ 2
  let W := ∑ i, x i * y i
  have hU : 0 ≤ U := Finset.sum_nonneg fun i _ => sq_nonneg (x i)
  have hV : 0 ≤ V := Finset.sum_nonneg fun i _ => sq_nonneg (y i)
  have hlin :
      b * B * U + a * A * V ≤ (A * B + a * b) * W := by
    have hpoint : ∀ i ∈ Finset.univ,
        b * B * x i ^ 2 + a * A * y i ^ 2 ≤
          (A * B + a * b) * (x i * y i) := by
      intro i _
      have hfactor1 : 0 ≤ A * y i - b * x i := by
        apply sub_nonneg.mpr
        calc
          b * x i ≤ y i * x i := by
            exact mul_le_mul_of_nonneg_right (hy i).1
              (lt_of_lt_of_le ha (hx i).1).le
          _ ≤ y i * A := by
            exact mul_le_mul_of_nonneg_left (hx i).2
              (lt_of_lt_of_le hb (hy i).1).le
          _ = A * y i := by ring
      have hfactor2 : 0 ≤ B * x i - a * y i := by
        apply sub_nonneg.mpr
        calc
          a * y i ≤ a * B := by
            exact mul_le_mul_of_nonneg_left (hy i).2 ha.le
          _ = B * a := by ring
          _ ≤ B * x i := by
            exact mul_le_mul_of_nonneg_left (hx i).1 (lt_of_lt_of_le hb hbB).le
      have hprod : 0 ≤ (A * y i - b * x i) * (B * x i - a * y i) :=
        mul_nonneg hfactor1 hfactor2
      nlinarith
    have hsum := Finset.sum_le_sum hpoint
    have hleft :
        (∑ i, (b * B * x i ^ 2 + a * A * y i ^ 2)) =
          b * B * U + a * A * V := by
      calc
        (∑ i, (b * B * x i ^ 2 + a * A * y i ^ 2)) =
            (∑ i, b * B * x i ^ 2) + ∑ i, a * A * y i ^ 2 :=
          Finset.sum_add_distrib
        _ = b * B * (∑ i, x i ^ 2) + a * A * (∑ i, y i ^ 2) := by
          congr 1
          · rw [← Finset.mul_sum]
          · rw [← Finset.mul_sum]
    have hright :
        (∑ i, (A * B + a * b) * (x i * y i)) =
          (A * B + a * b) * W := by
      rw [← Finset.mul_sum]
    rw [hleft, hright] at hsum
    exact hsum
  have hLnonneg : 0 ≤ b * B * U + a * A * V := by
    exact add_nonneg
      (mul_nonneg (mul_pos hb (lt_of_lt_of_le hb hbB)).le hU)
      (mul_nonneg (mul_pos ha (lt_of_lt_of_le ha haA)).le hV)
  have hsq : (b * B * U + a * A * V) ^ 2 ≤ ((A * B + a * b) * W) ^ 2 :=
    pow_le_pow_left₀ hLnonneg hlin 2
  have h4 : 4 * (b * B) * (a * A) * (U * V) ≤
      (b * B * U + a * A * V) ^ 2 := by
    nlinarith [sq_nonneg (b * B * U - a * A * V)]
  have hmain : 4 * (b * B) * (a * A) * (U * V) ≤
      ((A * B + a * b) * W) ^ 2 := le_trans h4 hsq
  have hnum : 4 * (b * B) * (a * A) * (U * V - W ^ 2) ≤
      (A * B - a * b) ^ 2 * W ^ 2 := by
    nlinarith
  have hden : 0 < 4 * (b * B) * (a * A) := by
    have hA : 0 < A := lt_of_lt_of_le ha haA
    have hB : 0 < B := lt_of_lt_of_le hb hbB
    positivity
  have htarget : U * V - W ^ 2 ≤
      ((A * B - a * b) ^ 2 * W ^ 2) / (4 * (b * B) * (a * A)) := by
    exact (le_div_iff₀ hden).mpr (by nlinarith)
  have hA : 0 < A := lt_of_lt_of_le ha haA
  have hB : 0 < B := lt_of_lt_of_le hb hbB
  calc
    (∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 =
        U * V - W ^ 2 := rfl
    _ ≤ ((A * B - a * b) ^ 2 * W ^ 2) / (4 * (b * B) * (a * A)) := htarget
    _ = ((A * B - a * b) ^ 2 / 4) *
          (W ^ 2 / (a * b * A * B)) := by
      field_simp [ha.ne', hA.ne', hb.ne', hB.ne']

/- accepted add_to_file helper 4 -/
lemma three_term_strict_examples :
    ∀ k : Fin 3,
      ∃ (m : ℕ) (a' A' b' B' : ℝ) (x' y' : Fin m → ℝ),
        1 ≤ m ∧
        0 < a' ∧ a' ≤ A' ∧ 0 < b' ∧ b' ≤ B' ∧
        (∀ i, a' ≤ x' i ∧ x' i ≤ A') ∧
        (∀ i, b' ≤ y' i ∧ y' i ≤ B') ∧
        (let t : Fin 3 → ℝ :=
          ![((∑ i, x' i ^ 2) ^ 2 / (A' ^ 2 * a' ^ 2)),
            ((∑ i, y' i ^ 2) ^ 2 / (B' ^ 2 * b' ^ 2)),
            ((∑ i, x' i * y' i) ^ 2 / (a' * b' * A' * B'))]
         ∀ j : Fin 3, j ≠ k → t k < t j) := by
  intro k
  fin_cases k
  · refine ⟨1, 1, 2, 1, 2, fun _ => 1, fun _ => 2, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · intro i
      norm_num
    · intro i
      norm_num
    · dsimp
      intro j hj
      fin_cases j
      · simp at hj
      · norm_num [Fin.sum_univ_one]
      · norm_num [Fin.sum_univ_one]
  · refine ⟨1, 1, 2, 1, 2, fun _ => 2, fun _ => 1, by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · intro i
      norm_num
    · intro i
      norm_num
    · dsimp
      intro j hj
      fin_cases j
      · norm_num [Fin.sum_univ_one]
      · simp at hj
      · norm_num [Fin.sum_univ_one]
  · refine ⟨2, 1, 2, 1, 2, ![2, 1], ![1, 2], by norm_num, by norm_num,
      by norm_num, by norm_num, by norm_num, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> norm_num
    · intro i
      fin_cases i <;> norm_num
    · dsimp
      intro j hj
      fin_cases j
      · norm_num [Fin.sum_univ_two]
      · norm_num [Fin.sum_univ_two]
      · simp at hj

/- verified submission -/
theorem reverse_cauchy_schwarz_with_three_term_min
    (n : ℕ) (hn : 1 ≤ n)
    (a A b B : ℝ)
    (ha : 0 < a) (haA : a ≤ A) (hb : 0 < b) (hbB : b ≤ B)
    (x y : Fin n → ℝ)
    (hx : ∀ i, a ≤ x i ∧ x i ≤ A)
    (hy : ∀ i, b ≤ y i ∧ y i ≤ B) :
    ((∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 ≤
      ((A * B - a * b) ^ 2 / 4) *
        min ((∑ i, x i ^ 2) ^ 2 / (A ^ 2 * a ^ 2))
          (min ((∑ i, y i ^ 2) ^ 2 / (B ^ 2 * b ^ 2))
            ((∑ i, x i * y i) ^ 2 / (a * b * A * B)))) ∧
    (∀ k : Fin 3,
      ∃ (m : ℕ) (a' A' b' B' : ℝ) (x' y' : Fin m → ℝ),
        1 ≤ m ∧
        0 < a' ∧ a' ≤ A' ∧ 0 < b' ∧ b' ≤ B' ∧
        (∀ i, a' ≤ x' i ∧ x' i ≤ A') ∧
        (∀ i, b' ≤ y' i ∧ y' i ≤ B') ∧
        (let t : Fin 3 → ℝ :=
          ![((∑ i, x' i ^ 2) ^ 2 / (A' ^ 2 * a' ^ 2)),
            ((∑ i, y' i ^ 2) ^ 2 / (B' ^ 2 * b' ^ 2)),
            ((∑ i, x' i * y' i) ^ 2 / (a' * b' * A' * B'))]
         ∀ j : Fin 3, j ≠ k → t k < t j)) := by
  constructor
  · have hxbound :
        (∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 ≤
          ((A * B - a * b) ^ 2 / 4) *
            ((∑ i, x i ^ 2) ^ 2 / (A ^ 2 * a ^ 2)) :=
      interval_variance_bound a A b B ha haA hb hbB x y hx hy
    have hyraw := interval_variance_bound b B a A hb hbB ha haA y x hy hx
    have hybound :
        (∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 ≤
          ((A * B - a * b) ^ 2 / 4) *
            ((∑ i, y i ^ 2) ^ 2 / (B ^ 2 * b ^ 2)) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hyraw
    have hcrossbound :
        (∑ i, x i ^ 2) * (∑ i, y i ^ 2) - (∑ i, x i * y i) ^ 2 ≤
          ((A * B - a * b) ^ 2 / 4) *
            ((∑ i, x i * y i) ^ 2 / (a * b * A * B)) :=
      interval_cross_bound a A b B ha haA hb hbB x y hx hy
    have hc : 0 ≤ ((A * B - a * b) ^ 2 / 4) := by positivity
    rw [mul_min_of_nonneg _ _ hc, mul_min_of_nonneg _ _ hc]
    exact le_min hxbound (le_min hybound hcrossbound)
  · exact three_term_strict_examples


#check_dependency_graph "reverse_cauchy_schwarz_with_three_term_min" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(∑ i, x i ^ 2) * ∑ i, y i ^ 2 - (∑ i, x i * y i) ^ 2 ≤ (A * B - a * b) ^ 2 / 4 * min ((∑ i, x i ^ 2) ^ 2 / (A ^ 2 * a ^ 2)) (min ((∑ i, y i ^ 2) ^ 2 / (B ^ 2 * b ^ 2)) ((∑ i, x i * y i) ^ 2 / (a * b * A * B))) ∧ ∀ (k : Fin 3), ∃ m a' A' b' B' x' y', 1 ≤ m ∧ 0 < a' ∧ a' ≤ A' ∧ 0 < b' ∧ b' ≤ B' ∧ (∀ (i : Fin m), a' ≤ x' i ∧ x' i ≤ A') ∧ (∀ (i : Fin m), b' ≤ y' i ∧ y' i ≤ B') ∧ let t := ![(∑ i, x' i ^ 2) ^ 2 / (A' ^ 2 * a' ^ 2), (∑ i, y' i ^ 2) ^ 2 / (B' ^ 2 * b' ^ 2), (∑ i, x' i * y' i) ^ 2 / (a' * b' * A' * B')]; ∀ (j : Fin 3), j ≠ k → t k < t j\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"ha\",\"statement\":\"0 < a\"},{\"name\":\"haA\",\"statement\":\"a ≤ A\"},{\"name\":\"hb\",\"statement\":\"0 < b\"},{\"name\":\"hbB\",\"statement\":\"b ≤ B\"},{\"name\":\"hx\",\"statement\":\"∀ (i : Fin n), a ≤ x i ∧ x i ≤ A\"},{\"name\":\"hy\",\"statement\":\"∀ (i : Fin n), b ≤ y i ∧ y i ≤ B\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2331_reverse_cauchy_schwarz_with_three_term_min\",\"reconstructedProofSha256\":\"1142f8fedc1d083beac4a3e89048b5ec6f4ca63f30f7feb9f0e6155df59e3351\",\"selectedEdgeCount\":1,\"theoremName\":\"reverse_cauchy_schwarz_with_three_term_min\",\"topologySha256\":\"fec88aa8a97a4f2c48e2051cbfc90e6f8d3639b75ec1d7298bc969f8cf03b91b\"}"
