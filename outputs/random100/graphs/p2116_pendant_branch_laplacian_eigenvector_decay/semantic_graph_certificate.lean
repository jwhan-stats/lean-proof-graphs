import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p2116_pendant_branch_laplacian_eigenvector_decay
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 6def72b531159d4e71e5ba8bebbb09ad9dc81baad6b3138a095ddbee09f704e8
-- reconstructed_proof_sha256: 18416f0080ac0f8e9f254f03f684a1e65ca560311ab67da9cf851b467e2d56cc
-- selected_edge_count: 1

/- accepted add_to_file helper 1 -/
lemma pendant_neighborFinset_interior
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 1 ≤ k)
    (i : Fin k → V)
    (hbranch : ∀ a b : Fin k,
      G.Adj (i a) (i b) ↔ a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (hexternal : ∃ x : V,
      x ∉ Set.range i ∧
      G.Adj (i ⟨0, hk⟩) x ∧
      ∀ (a : Fin k) (v : V), v ∉ Set.range i → G.Adj (i a) v →
        a = ⟨0, hk⟩ ∧ v = x)
    (a : Fin k) (ha : 0 < a.val) (hs : a.val + 1 < k) :
    G.neighborFinset (i a) =
      {i ⟨a.val - 1, by omega⟩, i ⟨a.val + 1, hs⟩} := by
  ext v
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hAdj
    by_cases hv : v ∈ Set.range i
    · rcases hv with ⟨b, rfl⟩
      have hb := (hbranch a b).mp hAdj
      rcases hb with h | h
      · right
        have hbv : b.val = a.val + 1 := by omega
        exact congrArg i (Fin.ext hbv)
      · left
        have hbv : b.val = a.val - 1 := by omega
        exact congrArg i (Fin.ext hbv)
    · rcases hexternal with ⟨x, hxrange, hxadj, huniq⟩
      obtain ⟨ha0, hvx⟩ := huniq a v hv hAdj
      have : a.val = 0 := congrArg Fin.val ha0
      omega
  · intro hv
    rcases hv with hv | hv
    · subst v
      have hpred : a.val - 1 + 1 = a.val := by omega
      exact (hbranch a ⟨a.val - 1, by omega⟩).mpr (Or.inr hpred)
    · subst v
      exact (hbranch a ⟨a.val + 1, hs⟩).mpr (Or.inl rfl)

lemma pendant_neighborFinset_last
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 1 ≤ k)
    (i : Fin k → V)
    (hbranch : ∀ a b : Fin k,
      G.Adj (i a) (i b) ↔ a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (hexternal : ∃ x : V,
      x ∉ Set.range i ∧
      G.Adj (i ⟨0, hk⟩) x ∧
      ∀ (a : Fin k) (v : V), v ∉ Set.range i → G.Adj (i a) v →
        a = ⟨0, hk⟩ ∧ v = x)
    (a : Fin k) (ha : 0 < a.val) (hs : a.val + 1 = k) :
    G.neighborFinset (i a) =
      {i ⟨a.val - 1, by omega⟩} := by
  ext v
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hAdj
    by_cases hv : v ∈ Set.range i
    · rcases hv with ⟨b, rfl⟩
      have hb := (hbranch a b).mp hAdj
      rcases hb with h | h
      · have : b.val = k := by omega
        omega
      · have hbv : b.val = a.val - 1 := by omega
        exact congrArg i (Fin.ext hbv)
    · rcases hexternal with ⟨x, hxrange, hxadj, huniq⟩
      obtain ⟨ha0, hvx⟩ := huniq a v hv hAdj
      have : a.val = 0 := congrArg Fin.val ha0
      omega
  · intro hv
    subst v
    have hpred : a.val - 1 + 1 = a.val := by omega
    exact (hbranch a ⟨a.val - 1, by omega⟩).mpr (Or.inr hpred)

/- accepted add_to_file helper 2 -/
theorem pendant_eigen_last
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 1 ≤ k)
    (i : Fin k → V)
    (hbranch : ∀ a b : Fin k,
      G.Adj (i a) (i b) ↔ a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (hexternal : ∃ x : V,
      x ∉ Set.range i ∧
      G.Adj (i ⟨0, hk⟩) x ∧
      ∀ (a : Fin k) (v : V), v ∉ Set.range i → G.Adj (i a) v →
        a = ⟨0, hk⟩ ∧ v = x)
    (lam : ℝ)
    (φ : V → ℝ)
    (heigen : (G.lapMatrix ℝ).mulVec φ = lam • φ)
    (j : Fin k) (hj : j.val + 1 < k)
    (hjd : j.val + 2 = k) :
    φ (i j) = (1 - lam) * φ (i ⟨j.val + 1, hj⟩) := by
  have hpos : 0 < (⟨j.val + 1, hj⟩ : Fin k).val := by
    change 0 < j.val + 1
    omega
  have hlast : (⟨j.val + 1, hj⟩ : Fin k).val + 1 = k := by
    change j.val + 1 + 1 = k
    omega
  have hneigh := pendant_neighborFinset_last G hk i hbranch hexternal
      ⟨j.val + 1, hj⟩ hpos hlast
  have hpred : (⟨(⟨j.val + 1, hj⟩ : Fin k).val - 1, by omega⟩ : Fin k) = j := by
    apply Fin.ext
    change j.val + 1 - 1 = j.val
    omega
  have hcard : (G.neighborFinset (i ⟨j.val + 1, hj⟩)).card = 1 := by
    rw [hneigh]
    simp
  have hdeg : G.degree (i ⟨j.val + 1, hj⟩) = 1 := by
    rw [← G.card_neighborFinset_eq_degree, hcard]
  have hEq := congrFun heigen (i ⟨j.val + 1, hj⟩)
  rw [SimpleGraph.lapMatrix_mulVec_apply] at hEq
  rw [hdeg, hneigh] at hEq
  simp [hpred] at hEq
  linarith

/- accepted add_to_file helper 3 -/
theorem pendant_eigen_interior
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 1 ≤ k)
    (i : Fin k → V)
    (hi : Function.Injective i)
    (hbranch : ∀ a b : Fin k,
      G.Adj (i a) (i b) ↔ a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (hexternal : ∃ x : V,
      x ∉ Set.range i ∧
      G.Adj (i ⟨0, hk⟩) x ∧
      ∀ (a : Fin k) (v : V), v ∉ Set.range i → G.Adj (i a) v →
        a = ⟨0, hk⟩ ∧ v = x)
    (lam : ℝ)
    (φ : V → ℝ)
    (heigen : (G.lapMatrix ℝ).mulVec φ = lam • φ)
    (j : Fin k) (hj : j.val + 1 < k) (hj2 : j.val + 2 < k) :
    φ (i j) + φ (i ⟨j.val + 2, hj2⟩) =
      (2 - lam) * φ (i ⟨j.val + 1, hj⟩) := by
  let s : Fin k := ⟨j.val + 1, hj⟩
  have hsval : s.val = j.val + 1 := rfl
  have hs_pos : 0 < s.val := by
    rw [hsval]
    omega
  have hs_succ : s.val + 1 < k := by
    rw [hsval]
    omega
  have hneigh := pendant_neighborFinset_interior G hk i hbranch hexternal s hs_pos hs_succ
  have hpred : (⟨s.val - 1, by omega⟩ : Fin k) = j := by
    apply Fin.ext
    change s.val - 1 = j.val
    omega
  have hnext : (⟨s.val + 1, hs_succ⟩ : Fin k) = ⟨j.val + 2, hj2⟩ := by
    apply Fin.ext
    change s.val + 1 = j.val + 2
    omega
  have hne : (⟨s.val - 1, by omega⟩ : Fin k) ≠ ⟨s.val + 1, hs_succ⟩ := by
    intro h
    have hv := congrArg Fin.val h
    change s.val - 1 = s.val + 1 at hv
    omega
  have hvne : i ⟨s.val - 1, by omega⟩ ≠ i ⟨s.val + 1, hs_succ⟩ := by
    intro h
    exact hne (hi h)
  have hcard : (G.neighborFinset (i s)).card = 2 := by
    rw [hneigh]
    exact Finset.card_pair hvne
  have hdeg : G.degree (i s) = 2 := by
    rw [← G.card_neighborFinset_eq_degree, hcard]
  have hEq := congrFun heigen (i s)
  rw [SimpleGraph.lapMatrix_mulVec_apply] at hEq
  rw [hdeg, hneigh] at hEq
  rw [Finset.sum_pair hvne] at hEq
  simp [hpred, hnext] at hEq
  linarith

/- accepted add_to_file helper 4 -/
theorem pendant_adjacent_decay
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (hk : 1 ≤ k)
    (i : Fin k → V)
    (hi : Function.Injective i)
    (hbranch : ∀ a b : Fin k,
      G.Adj (i a) (i b) ↔ a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (hexternal : ∃ x : V,
      x ∉ Set.range i ∧
      G.Adj (i ⟨0, hk⟩) x ∧
      ∀ (a : Fin k) (v : V), v ∉ Set.range i → G.Adj (i a) v →
        a = ⟨0, hk⟩ ∧ v = x)
    (lam : ℝ) (hlam : 4 < lam)
    (φ : V → ℝ)
    (heigen : (G.lapMatrix ℝ).mulVec φ = lam • φ) :
    ∀ (j : Fin k) (hj : j.val + 1 < k),
      |φ (i ⟨j.val + 1, hj⟩)| ≤
        (2 / (lam - 2)) * |φ (i j)| := by
  let γ : ℝ := 2 / (lam - 2)
  have ht : 0 < lam - 2 := by nlinarith
  have hγpos : 0 < γ := by
    dsimp [γ]
    positivity
  have hγlt : γ < 1 := by
    dsimp [γ]
    rw [div_lt_one ht]
    nlinarith
  have Haux : ∀ d : ℕ, ∀ (j : Fin k) (hj : j.val + 1 < k),
      j.val + d + 2 = k →
      |φ (i ⟨j.val + 1, hj⟩)| ≤ γ * |φ (i j)| := by
    intro d
    induction d with
    | zero =>
        intro j hj hdist
        have hjd : j.val + 2 = k := by omega
        have heq := pendant_eigen_last G hk i hbranch hexternal lam φ heigen j hj hjd
        have hAbs : |φ (i j)| = (lam - 1) * |φ (i ⟨j.val + 1, hj⟩)| := by
          rw [heq]
          rw [abs_mul]
          have hneg : 1 - lam < 0 := by nlinarith
          rw [abs_of_neg hneg]
          ring
        have hcoef : 1 ≤ γ * (lam - 1) := by
          dsimp [γ]
          field_simp [ne_of_gt ht]
          nlinarith
        calc
          |φ (i ⟨j.val + 1, hj⟩)| = 1 * |φ (i ⟨j.val + 1, hj⟩)| := by
            rw [one_mul]
          _ ≤ (γ * (lam - 1)) * |φ (i ⟨j.val + 1, hj⟩)| :=
            mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
          _ = γ * ((lam - 1) * |φ (i ⟨j.val + 1, hj⟩)|) := by ring
          _ = γ * |φ (i j)| := by rw [← hAbs]
    | succ d ih =>
        intro j hj hdist
        have hj2 : j.val + 2 < k := by omega
        let s : Fin k := ⟨j.val + 1, hj⟩
        have hsval : s.val = j.val + 1 := rfl
        have hs : s.val + 1 < k := by
          rw [hsval]
          omega
        have hsdist : s.val + d + 2 = k := by
          rw [hsval]
          omega
        have hnext := ih s hs hsdist
        have hnext' : |φ (i ⟨j.val + 2, hj2⟩)| ≤ γ * |φ (i s)| := by
          simpa [s] using hnext
        have heq := pendant_eigen_interior G hk i hi hbranch hexternal lam φ heigen j hj hj2
        have hAbs : |φ (i j) + φ (i ⟨j.val + 2, hj2⟩)| =
            (lam - 2) * |φ (i s)| := by
          rw [heq]
          rw [abs_mul]
          have hneg : 2 - lam < 0 := by nlinarith
          rw [abs_of_neg hneg]
          have hsdef : s = ⟨j.val + 1, hj⟩ := rfl
          rw [hsdef]
          ring
        have hineq0 : (lam - 2) * |φ (i s)| ≤
            |φ (i j)| + |φ (i ⟨j.val + 2, hj2⟩)| := by
          rw [← hAbs]
          exact abs_add_le _ _
        have hineq : (lam - 2) * |φ (i s)| ≤
            |φ (i j)| + γ * |φ (i s)| := by
          nlinarith
        have hsub : (lam - 2 - γ) * |φ (i s)| ≤ |φ (i j)| := by
          nlinarith
        have hcoef : 1 ≤ γ * (lam - 2 - γ) := by
          dsimp [γ]
          have htgt : 2 < lam - 2 := by nlinarith
          have htsq : 4 < (lam - 2)^2 := by
            nlinarith [mul_lt_mul_of_pos_left htgt ht]
          field_simp [ne_of_gt ht]
          nlinarith
        calc
          |φ (i ⟨j.val + 1, hj⟩)| = 1 * |φ (i ⟨j.val + 1, hj⟩)| := by
            rw [one_mul]
          _ ≤ (γ * (lam - 2 - γ)) * |φ (i ⟨j.val + 1, hj⟩)| :=
            mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)
          _ = γ * ((lam - 2 - γ) * |φ (i ⟨j.val + 1, hj⟩)|) := by ring
          _ ≤ γ * |φ (i j)| := by
            have hsub' : (lam - 2 - γ) * |φ (i ⟨j.val + 1, hj⟩)| ≤ |φ (i j)| := by
              simpa [s] using hsub
            exact mul_le_mul_of_nonneg_left hsub' hγpos.le
  intro j hj
  exact Haux (k - (j.val + 2)) j hj (by omega)

/- verified submission -/
theorem pendant_branch_laplacian_eigenvector_decay
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (k : ℕ) (hk : 1 ≤ k)
    (i : Fin k → V)
    (hi : Function.Injective i)
    (hbranch : ∀ a b : Fin k,
      G.Adj (i a) (i b) ↔ a.val + 1 = b.val ∨ b.val + 1 = a.val)
    (hexternal : ∃ x : V,
      x ∉ Set.range i ∧
      G.Adj (i ⟨0, hk⟩) x ∧
      ∀ (a : Fin k) (v : V), v ∉ Set.range i → G.Adj (i a) v →
        a = ⟨0, hk⟩ ∧ v = x)
    (lam : ℝ) (hlam : 4 < lam)
    (φ : V → ℝ) (hφ : φ ≠ 0)
    (heigen : (G.lapMatrix ℝ).mulVec φ = lam • φ) :
    let γ : ℝ := 2 / (lam - 2)
    0 < γ ∧ γ < 1 ∧
      (∀ (j : Fin k) (hj : j.val + 1 < k),
        |φ (i ⟨j.val + 1, hj⟩)| ≤ γ * |φ (i j)|) ∧
      ∀ j : Fin k, |φ (i j)| ≤ γ ^ j.val * |φ (i ⟨0, hk⟩)| := by
  dsimp only
  set γ : ℝ := 2 / (lam - 2) with hγdef
  have ht : 0 < lam - 2 := by nlinarith
  have hγpos : 0 < γ := by
    rw [hγdef]
    positivity
  have hγlt : γ < 1 := by
    rw [hγdef, div_lt_one ht]
    nlinarith
  have hadj := pendant_adjacent_decay G hk i hi hbranch hexternal lam hlam φ heigen
  refine ⟨hγpos, hγlt, ?_, ?_⟩
  · intro j hj
    rw [hγdef]
    exact hadj j hj
  · have Hpow_aux : ∀ n : ℕ, ∀ j : Fin k, j.val = n →
        |φ (i j)| ≤ γ ^ j.val * |φ (i ⟨0, hk⟩)| := by
      intro n
      induction n with
      | zero =>
          intro j hjval
          have hzero : j = ⟨0, hk⟩ := Fin.ext (by omega)
          rw [hzero]
          simp
      | succ n ih =>
          intro j hjval
          have hnlt : n < k := by omega
          let p : Fin k := ⟨n, hnlt⟩
          have hsproof : p.val + 1 < k := by
            dsimp [p]
            omega
          have hjp : j = ⟨p.val + 1, hsproof⟩ := by
            apply Fin.ext
            dsimp [p]
            omega
          calc
            |φ (i j)| = |φ (i ⟨p.val + 1, hsproof⟩)| := congrArg (fun v => |φ (i v)|) hjp
            _ ≤ γ * |φ (i p)| := by
              rw [hγdef]
              exact hadj p hsproof
            _ ≤ γ * (γ ^ n * |φ (i ⟨0, hk⟩)|) := by
              have hpval : p.val = n := rfl
              exact mul_le_mul_of_nonneg_left (ih p hpval) hγpos.le
            _ = γ ^ (n + 1) * |φ (i ⟨0, hk⟩)| := by
              rw [pow_succ]
              ring
            _ = γ ^ j.val * |φ (i ⟨0, hk⟩)| := by
              rw [hjval]
    intro j
    exact Hpow_aux j.val j rfl


#check_dependency_graph "pendant_branch_laplacian_eigenvector_decay" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let γ := 2 / (lam - 2); 0 < γ ∧ γ < 1 ∧ (∀ (j : Fin k) (hj : ↑j + 1 < k), |φ (i ⟨↑j + 1, hj⟩)| ≤ γ * |φ (i j)|) ∧ ∀ (j : Fin k), |φ (i j)| ≤ γ ^ ↑j * |φ (i ⟨0, hk⟩)|\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hk\",\"statement\":\"1 ≤ k\"},{\"name\":\"hi\",\"statement\":\"Function.Injective i\"},{\"name\":\"hbranch\",\"statement\":\"∀ (a b : Fin k), G.Adj (i a) (i b) ↔ ↑a + 1 = ↑b ∨ ↑b + 1 = ↑a\"},{\"name\":\"hexternal\",\"statement\":\"∃ x ∉ Set.range i, G.Adj (i ⟨0, hk⟩) x ∧ ∀ (a : Fin k), ∀ v ∉ Set.range i, G.Adj (i a) v → a = ⟨0, hk⟩ ∧ v = x\"},{\"name\":\"hlam\",\"statement\":\"4 < lam\"},{\"name\":\"heigen\",\"statement\":\"(SimpleGraph.lapMatrix ℝ G).mulVec φ = lam • φ\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2116_pendant_branch_laplacian_eigenvector_decay\",\"reconstructedProofSha256\":\"18416f0080ac0f8e9f254f03f684a1e65ca560311ab67da9cf851b467e2d56cc\",\"selectedEdgeCount\":1,\"theoremName\":\"pendant_branch_laplacian_eigenvector_decay\",\"topologySha256\":\"6def72b531159d4e71e5ba8bebbb09ad9dc81baad6b3138a095ddbee09f704e8\"}"
