import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p2332_matrix_kronecker_injective_iff_linearindep
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 812999549bfeac040effa04a22a8ad38d1e8fe269f6948bb066701c2a4298133
-- reconstructed_proof_sha256: 5f6b35e57af2756aa3fc75c8250ca61176fbf4c7dc7229c1560ad8136bf4f472
-- selected_edge_count: 1

/- verified submission -/
theorem matrix_kronecker_injective_iff_linearIndependent
    (g d e : ℕ) (hg : 0 < g) (hd : 0 < d) (he : 0 < e)
    (A : Fin g → Matrix (Fin d) (Fin e) ℂ) :
    let c₁ : Prop := ∀ (n : ℕ), 0 < n → ∀ X : Fin g → Matrix (Fin n) (Fin n) ℂ,
      (∑ j, Matrix.kronecker (A j) (X j)) = 0 → ∀ j, X j = 0
    let c₂ : Prop := ∀ z : Fin g → ℂ,
      (∑ j, z j • A j) = 0 → ∀ j, z j = 0
    let c₃ : Prop := LinearIndependent ℂ A
    (c₁ ↔ c₂) ∧ (c₂ ↔ c₃) := by
  constructor
  · constructor
    · intro h₁ z hz
      let X : Fin g → Matrix (Fin 1) (Fin 1) ℂ :=
        fun j => Matrix.of fun _ _ => z j
      have hsum : (∑ j, Matrix.kronecker (A j) (X j)) = 0 := by
        ext ⟨i, a⟩ ⟨k, b⟩
        have hz' := congrFun (congrFun hz i) k
        simp [Matrix.sum_apply, Matrix.smul_apply, X] at hz' ⊢
        simpa [mul_comm] using hz'
      have hX := h₁ 1 zero_lt_one X hsum
      intro j
      have hj := congrFun (congrFun (hX j) 0) 0
      simpa [X] using hj
    · intro h₂ n hn X hX j
      ext r s
      let z : Fin g → ℂ := fun j => X j r s
      have hzsum : (∑ j, z j • A j) = 0 := by
        ext i k
        have hX' := congrFun (congrFun hX (i, r)) (k, s)
        simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.kronecker, z] at hX' ⊢
        simpa [mul_comm] using hX'
      have hz := h₂ z hzsum j
      simpa [z] using hz
  · constructor
    · intro h₂
      rw [linearIndependent_iff_injective_fintypeLinearCombination]
      intro x y hxy
      have hdiff : (∑ j, (x - y) j • A j) = 0 := by
        have hmap : Fintype.linearCombination ℂ A (x - y) = 0 := by
          rw [map_sub, hxy, sub_self]
        simpa [Fintype.linearCombination_apply] using hmap
      have h := h₂ (x - y) hdiff
      ext j
      have hj := h j
      simpa using sub_eq_zero.mp hj
    · intro h₃ z hz
      rw [linearIndependent_iff_injective_fintypeLinearCombination] at h₃
      have hzlin : Fintype.linearCombination ℂ A z = Fintype.linearCombination ℂ A 0 := by
        rw [Fintype.linearCombination_apply]
        simpa using hz
      have hz0 := h₃ hzlin
      intro j
      exact congrFun hz0 j


#check_dependency_graph "matrix_kronecker_injective_iff_linearIndependent" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"((∀ (n : ℕ), 0 < n → ∀ (X : Fin g → Matrix (Fin n) (Fin n) ℂ), ∑ j, (A j).kronecker (X j) = 0 → ∀ (j : Fin g), X j = 0) ↔ ∀ (z : Fin g → ℂ), ∑ j, z j • A j = 0 → ∀ (j : Fin g), z j = 0) ∧ ((∀ (z : Fin g → ℂ), ∑ j, z j • A j = 0 → ∀ (j : Fin g), z j = 0) ↔ LinearIndependent ℂ A)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2332_matrix_kronecker_injective_iff_linearindep\",\"reconstructedProofSha256\":\"5f6b35e57af2756aa3fc75c8250ca61176fbf4c7dc7229c1560ad8136bf4f472\",\"selectedEdgeCount\":1,\"theoremName\":\"matrix_kronecker_injective_iff_linearIndependent\",\"topologySha256\":\"812999549bfeac040effa04a22a8ad38d1e8fe269f6948bb066701c2a4298133\"}"
