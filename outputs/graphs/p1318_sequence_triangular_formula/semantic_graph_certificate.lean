import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1318_sequence_triangular_formula
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: e12f68c590d052a3252704376bcc8420bd334abba0895d8d9e6f14d69b56ebc6
-- reconstructed_proof_sha256: 94256b8599ca55d28ef24ab5fc82b764a624b7fdfd52212f74a43478178ddd1f
-- selected_edge_count: 1

/- accepted add_to_file helper 1 -/
lemma triangular_pair (m : ℕ) :
    2 * m ^ 2 = 2 * ((m - 1) * m / 2 + m * (m + 1) / 2) := by
  have hsum :
      2 * m ^ 2 = (m - 1) * m + m * (m + 1) := by
    cases m with
    | zero => norm_num
    | succ a =>
        simp
        ring
  have hA : 2 ∣ (m - 1) * m := by
    rw [Nat.mul_comm]
    exact Nat.two_dvd_mul_sub_one m
  have hB : 2 ∣ m * (m + 1) := Nat.two_dvd_mul_add_one m
  have hAback : 2 * ((m - 1) * m / 2) = (m - 1) * m := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel hA
  have hBback : 2 * (m * (m + 1) / 2) = m * (m + 1) := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel hB
  have hdouble :
      2 * ((m - 1) * m / 2 + m * (m + 1) / 2)
        = (m - 1) * m + m * (m + 1) := by
    rw [Nat.mul_add, hAback, hBback]
  exact hsum.trans hdouble.symm

/- verified submission -/
theorem sequence_triangular_formula
    (c : ℕ → ℕ)
    (hc₁ : c 1 = 2)
    (hc : ∀ k : ℕ, 0 < k →
      c (2 * k) = 2 * (k + 1) ^ 2 ∧
      c (2 * k + 1) = 2 * (k + 1) ^ 2) :
    ∀ n : ℕ, 0 < n →
      let m := (n + 2) / 2
      let t : ℕ → ℕ := fun r => r * (r + 1) / 2
      c n = 2 * m ^ 2 ∧ 2 * m ^ 2 = 2 * (t (m - 1) + t m) := by
  intro n hn
  by_cases h1 : n = 1
  · subst n
    simp [hc₁]
  · let k := n / 2
    have hk : 0 < k := by
      omega
    have hrec := hc k hk
    have hmod := Nat.mod_two_eq_zero_or_one n
    rcases hmod with heven | hodd
    · have hn_eq : n = 2 * k := by
        omega
      have hm : (n + 2) / 2 = k + 1 := by
        omega
      have hcn : c n = 2 * (k + 1) ^ 2 := by
        rw [hn_eq]
        exact hrec.1
      dsimp
      constructor
      · rw [hm]
        exact hcn
      · rw [hm]
        exact triangular_pair (k + 1)
    · have hn_eq : n = 2 * k + 1 := by
        omega
      have hm : (n + 2) / 2 = k + 1 := by
        omega
      have hcn : c n = 2 * (k + 1) ^ 2 := by
        rw [hn_eq]
        exact hrec.2
      dsimp
      constructor
      · rw [hm]
        exact hcn
      · rw [hm]
        exact triangular_pair (k + 1)


#check_dependency_graph "sequence_triangular_formula" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let m := (n + 2) / 2; let t := fun r => r * (r + 1) / 2; c n = 2 * m ^ 2 ∧ 2 * m ^ 2 = 2 * (t (m - 1) + t m)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hc₁\",\"statement\":\"c 1 = 2\"},{\"name\":\"hc\",\"statement\":\"∀ (k : ℕ), 0 < k → c (2 * k) = 2 * (k + 1) ^ 2 ∧ c (2 * k + 1) = 2 * (k + 1) ^ 2\"},{\"name\":\"hn\",\"statement\":\"0 < n\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1318_sequence_triangular_formula\",\"reconstructedProofSha256\":\"94256b8599ca55d28ef24ab5fc82b764a624b7fdfd52212f74a43478178ddd1f\",\"selectedEdgeCount\":1,\"theoremName\":\"sequence_triangular_formula\",\"topologySha256\":\"e12f68c590d052a3252704376bcc8420bd334abba0895d8d9e6f14d69b56ebc6\"}"
