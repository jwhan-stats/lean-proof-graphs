import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p3210_substochastic_row_update_product
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: db50fe190604d05227612447bcc66f9ea76bc24aec9dacd3acf69bb671db2c27
-- reconstructed_proof_sha256: 586b32f872bf55ac03d029f74b950b2711def373c5f545730f7a1858a3a88969
-- selected_edge_count: 5

/- accepted add_to_file helper 1 -/
lemma row_update_prod_invariant
    (N : ℕ)
    (C : Matrix (Fin N) (Fin N) ℝ)
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (r : ℝ)
    (hr : IsGreatest (Set.range (fun i : Fin N => ∑ j : Fin N, C i j)) r)
    (hr_lt_one : r < 1)
    (l : List (Fin N)) :
    (∀ x : Fin N,
      (∑ j : Fin N,
        (l.map (fun a : Fin N =>
          Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) a (C a))).prod x j) ≤ 1) ∧
    (∀ i : Fin N, i ∈ l →
      (∑ j : Fin N,
        (l.map (fun a : Fin N =>
          Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) a (C a))).prod i j) ≤ r) := by
  classical
  induction l with
  | nil =>
      constructor
      · intro x
        simp [Matrix.one_apply]
      · intro i hi
        simp at hi
  | cons a t ih =>
      obtain ⟨ih_one, ih_r⟩ := ih
      have hCa : (∑ j : Fin N, C a j) ≤ r := by
        exact hr.2 (by exact ⟨a, rfl⟩)
      have hrow_a :
          (∑ j : Fin N,
            ((Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) a (C a)) *
              (t.map (fun b : Fin N =>
                Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) b (C b))).prod) a j) ≤ r := by
        calc
          (∑ j : Fin N,
            ((Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) a (C a)) *
              (t.map (fun b : Fin N =>
                Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) b (C b))).prod) a j)
              = ∑ k : Fin N, C a k *
                (∑ j : Fin N,
                  (t.map (fun b : Fin N =>
                    Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) b (C b))).prod k j) := by
                rw [Matrix.updateRow_mul, Matrix.one_mul]
                simp [Matrix.vecMul, dotProduct, Finset.mul_sum]
                rw [Finset.sum_comm]
          _ ≤ ∑ k : Fin N, C a k * 1 := by
                exact Finset.sum_le_sum (fun k _ =>
                  mul_le_mul_of_nonneg_left (ih_one k) (hC_nonneg a k))
          _ = ∑ k : Fin N, C a k := by simp
          _ ≤ r := hCa
      constructor
      · intro x
        simp only [List.map_cons, List.prod_cons]
        by_cases hxa : x = a
        · subst x
          exact le_trans hrow_a (le_of_lt hr_lt_one)
        · have hrow_eq :
              (∑ j : Fin N,
                ((Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) a (C a)) *
                  (t.map (fun b : Fin N =>
                    Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) b (C b))).prod) x j)
                = ∑ j : Fin N,
                  (t.map (fun b : Fin N =>
                    Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) b (C b))).prod x j := by
            rw [Matrix.updateRow_mul, Matrix.one_mul]
            simp [Matrix.updateRow_ne hxa]
          rw [hrow_eq]
          exact ih_one x
      · intro i hi
        simp only [List.map_cons, List.prod_cons]
        by_cases hia : i = a
        · subst i
          exact hrow_a
        · have hit : i ∈ t := by
            simp [hia] at hi
            exact hi
          have hrow_eq :
              (∑ j : Fin N,
                ((Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) a (C a)) *
                  (t.map (fun b : Fin N =>
                    Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) b (C b))).prod) i j)
                = ∑ j : Fin N,
                  (t.map (fun b : Fin N =>
                    Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) b (C b))).prod i j := by
            rw [Matrix.updateRow_mul, Matrix.one_mul]
            simp [Matrix.updateRow_ne hia]
          rw [hrow_eq]
          exact ih_r i hit

/- verified submission -/
theorem substochastic_row_update_product
    (N : ℕ) (hN : 1 ≤ N)
    (C : Matrix (Fin N) (Fin N) ℝ)
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hC_diag : ∀ i, C i i = 0)
    (r : ℝ)
    (hr : IsGreatest (Set.range (fun i : Fin N => ∑ j : Fin N, C i j)) r)
    (hr_lt_one : r < 1)
    (Q : Matrix (Fin N) (Fin N) ℝ)
    (hQ : Q = (List.ofFn (fun i : Fin N =>
      Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) i (C i))).reverse.prod) :
    ∀ i : Fin N, (∑ j : Fin N, Q i j) ≤ r := by
  classical
  intro i
  let idx : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hinvariant := row_update_prod_invariant N C hC_nonneg r hr hr_lt_one idx.reverse
  have hi_idx : i ∈ idx := by
    dsimp [idx]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  have hi : i ∈ idx.reverse := by
    exact List.mem_reverse.mpr hi_idx
  have hbound := hinvariant.2 i hi
  rw [hQ]
  simpa [idx, List.map_reverse] using hbound


#check_dependency_graph "substochastic_row_update_product" against "{\"edges\":[{\"conclusion\":{\"name\":\"hinvariant\",\"statement\":\"(∀ (x : Fin N), ∑ j, (List.map (fun a => Matrix.updateRow 1 a (C a)) idx.reverse).prod x j ≤ 1) ∧ ∀ i ∈ idx.reverse, ∑ j, (List.map (fun a => Matrix.updateRow 1 a (C a)) idx.reverse).prod i j ≤ r\"},\"graphEdgeId\":\"h_001_hinvariant\",\"premises\":[{\"name\":\"hC_nonneg\",\"statement\":\"∀ (i j : Fin N), 0 ≤ C i j\"},{\"name\":\"hr\",\"statement\":\"IsGreatest (Set.range fun i => ∑ j, C i j) r\"},{\"name\":\"hr_lt_one\",\"statement\":\"r < 1\"}],\"rawEdgeId\":\"telescope_12\"},{\"conclusion\":{\"name\":\"hi_idx\",\"statement\":\"i ∈ idx\"},\"graphEdgeId\":\"h_002_hi_idx\",\"premises\":[],\"rawEdgeId\":\"telescope_13\"},{\"conclusion\":{\"name\":\"hi\",\"statement\":\"i ∈ idx.reverse\"},\"graphEdgeId\":\"h_003_hi\",\"premises\":[{\"name\":\"hi_idx\",\"statement\":\"i ∈ idx\"}],\"rawEdgeId\":\"telescope_14\"},{\"conclusion\":{\"name\":\"hbound\",\"statement\":\"∑ j, (List.map (fun a => Matrix.updateRow 1 a (C a)) idx.reverse).prod i j ≤ r\"},\"graphEdgeId\":\"h_004_hbound\",\"premises\":[{\"name\":\"hinvariant\",\"statement\":\"(∀ (x : Fin N), ∑ j, (List.map (fun a => Matrix.updateRow 1 a (C a)) idx.reverse).prod x j ≤ 1) ∧ ∀ i ∈ idx.reverse, ∑ j, (List.map (fun a => Matrix.updateRow 1 a (C a)) idx.reverse).prod i j ≤ r\"},{\"name\":\"hi\",\"statement\":\"i ∈ idx.reverse\"}],\"rawEdgeId\":\"telescope_15\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∑ j, Q i j ≤ r\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hQ\",\"statement\":\"Q = (List.ofFn fun i => Matrix.updateRow 1 i (C i)).reverse.prod\"},{\"name\":\"hbound\",\"statement\":\"∑ j, (List.map (fun a => Matrix.updateRow 1 a (C a)) idx.reverse).prod i j ≤ r\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p3210_substochastic_row_update_product\",\"reconstructedProofSha256\":\"586b32f872bf55ac03d029f74b950b2711def373c5f545730f7a1858a3a88969\",\"selectedEdgeCount\":5,\"theoremName\":\"substochastic_row_update_product\",\"topologySha256\":\"db50fe190604d05227612447bcc66f9ea76bc24aec9dacd3acf69bb671db2c27\"}"
