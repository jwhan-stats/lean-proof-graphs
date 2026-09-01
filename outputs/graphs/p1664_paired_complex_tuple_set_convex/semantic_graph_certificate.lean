import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1664_paired_complex_tuple_set_convex
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: b4be8d3735c355ac6e653e0f9dd5a2845135be269c517bc5360bd2601e64ce1b
-- reconstructed_proof_sha256: 3a40aae3bbd5d18b0cace7dde1732824229edf593609c335fcbdcc29088f16e5
-- selected_edge_count: 1

/- accepted add_to_file helper 1 -/
lemma strict_combination_pos {a b x y : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : 0 < x) (hy : 0 < y) :
    0 < a * x + b * y := by
  by_cases h : a = 0
  · have hb' : b = 1 := by linarith
    rw [h, hb']
    simpa using hy
  · have ha' : 0 < a := lt_of_le_of_ne ha (fun hzero => h hzero.symm)
    exact add_pos_of_pos_of_nonneg (mul_pos ha' hx)
      (mul_nonneg hb (le_of_lt hy))

lemma strict_combination_neg {a b x y : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : x < 0) (hy : y < 0) :
    a * x + b * y < 0 := by
  have hpos : 0 < a * (-x) + b * (-y) :=
    strict_combination_pos ha hb hab (neg_pos.mpr hx) (neg_pos.mpr hy)
  linarith

/- verified submission -/
theorem paired_complex_tuple_set_convex
    (l m : ℕ) (hl : 0 < l) (hm : 0 < m)
    (σ : Fin (l + m) → Fin (l + m))
    (hσ_involutive : Function.Involutive σ)
    (hσ_fixedPointFree : ∀ i, σ i ≠ i) :
    Convex ℝ {ζ : Fin (l + m) → ℂ |
      (∀ i, ζ i = ζ (σ i)) ∧
      (∀ i, 0 < (ζ i).re) ∧
      (∀ i : ℕ, 1 ≤ i → i < l →
        0 < (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => k.val < i), ζ k).im) ∧
      (∀ j : ℕ, 1 ≤ j → j < m →
        (∑ k ∈ Finset.univ.filter
          (fun k : Fin (l + m) => l ≤ k.val ∧ k.val < l + j), ζ k).im < 0) ∧
      (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => k.val < l), ζ k) =
        ∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => l ≤ k.val), ζ k} := by
  intro ζ hζ η hη a b ha hb hab
  constructor
  · intro i
    have hzi := hζ.1 i
    have hei := hη.1 i
    simp [Pi.add_apply, Pi.smul_apply, hzi, hei]
  · constructor
    · intro i
      simpa [Pi.add_apply, Pi.smul_apply] using
        strict_combination_pos ha hb hab (hζ.2.1 i) (hη.2.1 i)
    · constructor
      · intro i hi1 hil
        simpa [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, Finset.mul_sum] using
          strict_combination_pos ha hb hab
            (hζ.2.2.1 i hi1 hil) (hη.2.2.1 i hi1 hil)
      · constructor
        · intro j hj1 hjm
          simpa [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, Finset.mul_sum] using
            strict_combination_neg ha hb hab
              (hζ.2.2.2.1 j hj1 hjm) (hη.2.2.2.1 j hj1 hjm)
        · have hzsum := hζ.2.2.2.2
          have hηsum := hη.2.2.2.2
          have hleft :
              (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => k.val < l),
                  (a • ζ + b • η) k) =
                a * (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => k.val < l), ζ k) +
                  b * (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => k.val < l), η k) := by
            simp [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, Finset.mul_sum]
          have hright :
              (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => l ≤ k.val),
                  (a • ζ + b • η) k) =
                a * (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => l ≤ k.val), ζ k) +
                  b * (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => l ≤ k.val), η k) := by
            simp [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, Finset.mul_sum]
          calc
            (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => k.val < l),
                (a • ζ + b • η) k)
                = a * (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => k.val < l), ζ k) +
                    b * (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => k.val < l), η k) :=
              hleft
            _ = a * (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => l ≤ k.val), ζ k) +
                    b * (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => l ≤ k.val), η k) := by
              rw [hzsum, hηsum]
            _ = ∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => l ≤ k.val),
                    (a • ζ + b • η) k :=
              hright.symm


#check_dependency_graph "paired_complex_tuple_set_convex" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(∀ (i : Fin (l + m)), (a • ζ + b • η) i = (a • ζ + b • η) (σ i)) ∧ (∀ (i : Fin (l + m)), 0 < ((a • ζ + b • η) i).re) ∧ (∀ (i : ℕ), 1 ≤ i → i < l → 0 < (∑ k with ↑k < i, (a • ζ + b • η) k).im) ∧ (∀ (j : ℕ), 1 ≤ j → j < m → (∑ k with l ≤ ↑k ∧ ↑k < l + j, (a • ζ + b • η) k).im < 0) ∧ ∑ k with ↑k < l, (a • ζ + b • η) k = ∑ k with l ≤ ↑k, (a • ζ + b • η) k\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hζ\",\"statement\":\"ζ ∈ {ζ | (∀ (i : Fin (l + m)), ζ i = ζ (σ i)) ∧ (∀ (i : Fin (l + m)), 0 < (ζ i).re) ∧ (∀ (i : ℕ), 1 ≤ i → i < l → 0 < (∑ k with ↑k < i, ζ k).im) ∧ (∀ (j : ℕ), 1 ≤ j → j < m → (∑ k with l ≤ ↑k ∧ ↑k < l + j, ζ k).im < 0) ∧ ∑ k with ↑k < l, ζ k = ∑ k with l ≤ ↑k, ζ k}\"},{\"name\":\"hη\",\"statement\":\"η ∈ {ζ | (∀ (i : Fin (l + m)), ζ i = ζ (σ i)) ∧ (∀ (i : Fin (l + m)), 0 < (ζ i).re) ∧ (∀ (i : ℕ), 1 ≤ i → i < l → 0 < (∑ k with ↑k < i, ζ k).im) ∧ (∀ (j : ℕ), 1 ≤ j → j < m → (∑ k with l ≤ ↑k ∧ ↑k < l + j, ζ k).im < 0) ∧ ∑ k with ↑k < l, ζ k = ∑ k with l ≤ ↑k, ζ k}\"},{\"name\":\"ha\",\"statement\":\"0 ≤ a\"},{\"name\":\"hb\",\"statement\":\"0 ≤ b\"},{\"name\":\"hab\",\"statement\":\"a + b = 1\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1664_paired_complex_tuple_set_convex\",\"reconstructedProofSha256\":\"3a40aae3bbd5d18b0cace7dde1732824229edf593609c335fcbdcc29088f16e5\",\"selectedEdgeCount\":1,\"theoremName\":\"paired_complex_tuple_set_convex\",\"topologySha256\":\"b4be8d3735c355ac6e653e0f9dd5a2845135be269c517bc5360bd2601e64ce1b\"}"
