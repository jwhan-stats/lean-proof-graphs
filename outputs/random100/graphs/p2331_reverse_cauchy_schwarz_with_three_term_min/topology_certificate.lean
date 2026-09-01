import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2331_reverse_cauchy_schwarz_with_three_term_min
-- topology_sha256: fec88aa8a97a4f2c48e2051cbfc90e6f8d3639b75ec1d7298bc969f8cf03b91b
namespace TopologyCertificate_p2331_reverse_cauchy_schwarz_with_three_term_min

-- N001 = ha: 0 < a
-- N002 = haA: a ≤ A
-- N003 = hb: 0 < b
-- N004 = hbB: b ≤ B
-- N005 = hx: ∀ (i : Fin n), a ≤ x i ∧ x i ≤ A
-- N006 = hy: ∀ (i : Fin n), b ≤ y i ∧ y i ≤ B
-- N007 = goal: (∑ i, x i ^ 2) * ∑ i, y i ^ 2 - (∑ i, x i * y i) ^ 2 ≤ (A * B - a * b) ^ 2 / 4 * min ((∑ i, x i ^ 2) ^ 2 / (A ^ 2 * a ^ 2)) (min ((∑ i, y i ^ 2) ^ 2 / (B ^ 2 * b ^ 2)) ((∑ i, x i * y i) ^ 2 / (a * b * A * B))) ∧ ∀ (k : Fin 3), ∃ m a' A' b' B' x' y', 1 ≤ m ∧ 0 < a' ∧ a' ≤ A' ∧ 0 < b' ∧ b' ≤ B' ∧ (∀ (i : Fin m), a' ≤ x' i ∧ x' i ≤ A') ∧ (∀ (i : Fin m), b' ≤ y' i ∧ y' i ≤ B') ∧ let t := ![(∑ i, x' i ^ 2) ^ 2 / (A' ^ 2 * a' ^ 2), (∑ i, y' i ^ 2) ^ 2 / (B' ^ 2 * b' ^ 2), (∑ i, x' i * y' i) ^ 2 / (a' * b' * A' * B')]; ∀ (j : Fin 3), j ≠ k → t k < t j

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (E001 : N001 → N002 → N003 → N004 → N005 → N006 → N007)
    : N007 := by
  have H_N007 : N007 := E001 B001 B002 B003 B004 B005 B006
  exact H_N007

end TopologyCertificate_p2331_reverse_cauchy_schwarz_with_three_term_min
