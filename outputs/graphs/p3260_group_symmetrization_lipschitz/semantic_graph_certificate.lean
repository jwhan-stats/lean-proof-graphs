import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p3260_group_symmetrization_lipschitz
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 98cc2ec8af7eb795746b45890d773629394f9177fe3dbdba47ff1373fbbd3200
-- reconstructed_proof_sha256: f5049a81a77e55fb08e36e0e068ba58d49266977f925d0df7cc9e25e4e6c8bb4
-- selected_edge_count: 5

/- verified submission -/
theorem group_symmetrization_lipschitz
    (D : ℕ)
    (X : Set (EuclideanSpace ℝ (Fin D)))
    (G : Type*) [Group G] [Fintype G] [MulAction G X]
    (hact : ∀ (g : G) (x y : X),
      ‖(↑(g • x) : EuclideanSpace ℝ (Fin D)) - ↑(g • y)‖ ≤
        ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖)
    (L : ℝ) (hL : 0 ≤ L)
    (f : X → ℝ)
    (hf : ∀ x y : X,
      |f x - f y| ≤ L * ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖) :
    ∀ x y : X,
      |((∑ g : G, f (g • x)) / (Fintype.card G : ℝ)) -
          ((∑ g : G, f (g • y)) / (Fintype.card G : ℝ))| ≤
        L * ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖ := by
  intro x y
  let C : ℝ := Fintype.card G
  have hCpos : 0 < C := by
    dsimp [C]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hterm : ∀ g : G,
      |f (g • x) - f (g • y)| ≤
        L * ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖ := by
    intro g
    calc
      |f (g • x) - f (g • y)| ≤
          L * ‖(↑(g • x) : EuclideanSpace ℝ (Fin D)) - ↑(g • y)‖ :=
        hf (g • x) (g • y)
      _ ≤ L * ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖ :=
        mul_le_mul_of_nonneg_left (hact g x y) hL
  have hsum :
      |(∑ g : G, f (g • x)) - (∑ g : G, f (g • y))| ≤
        C * (L * ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖) := by
    calc
      |(∑ g : G, f (g • x)) - (∑ g : G, f (g • y))|
          = |∑ g : G, (f (g • x) - f (g • y))| := by
            rw [← Finset.sum_sub_distrib]
      _ ≤ ∑ g : G, |f (g • x) - f (g • y)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ g : G, L * ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖ := by
        exact Finset.sum_le_sum fun g _ => hterm g
      _ = C * (L * ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖) := by
        dsimp [C]
        rw [Finset.sum_const, Finset.card_univ]
        norm_num
  have hdiv :
      |((∑ g : G, f (g • x)) / C) - ((∑ g : G, f (g • y)) / C)| ≤
        L * ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖ := by
    rw [← sub_div, abs_div, abs_of_nonneg hCpos.le]
    exact (div_le_iff₀ hCpos).2 (by simpa [mul_comm] using hsum)
  dsimp [C] at hdiv
  exact hdiv


#check_dependency_graph "group_symmetrization_lipschitz" against "{\"edges\":[{\"conclusion\":{\"name\":\"hCpos\",\"statement\":\"0 < C\"},\"graphEdgeId\":\"h_001_hcpos\",\"premises\":[],\"rawEdgeId\":\"telescope_14\"},{\"conclusion\":{\"name\":\"hterm\",\"statement\":\"∀ (g : G), |f (g • x) - f (g • y)| ≤ L * ‖↑x - ↑y‖\"},\"graphEdgeId\":\"h_002_hterm\",\"premises\":[{\"name\":\"hact\",\"statement\":\"∀ (g : G) (x y : ↑X), ‖↑(g • x) - ↑(g • y)‖ ≤ ‖↑x - ↑y‖\"},{\"name\":\"hL\",\"statement\":\"0 ≤ L\"},{\"name\":\"hf\",\"statement\":\"∀ (x y : ↑X), |f x - f y| ≤ L * ‖↑x - ↑y‖\"}],\"rawEdgeId\":\"telescope_15\"},{\"conclusion\":{\"name\":\"hsum\",\"statement\":\"|∑ g, f (g • x) - ∑ g, f (g • y)| ≤ C * (L * ‖↑x - ↑y‖)\"},\"graphEdgeId\":\"h_003_hsum\",\"premises\":[{\"name\":\"hterm\",\"statement\":\"∀ (g : G), |f (g • x) - f (g • y)| ≤ L * ‖↑x - ↑y‖\"}],\"rawEdgeId\":\"telescope_16\"},{\"conclusion\":{\"name\":\"hdiv\",\"statement\":\"|(∑ g, f (g • x)) / C - (∑ g, f (g • y)) / C| ≤ L * ‖↑x - ↑y‖\"},\"graphEdgeId\":\"h_004_hdiv\",\"premises\":[{\"name\":\"hCpos\",\"statement\":\"0 < C\"},{\"name\":\"hsum\",\"statement\":\"|∑ g, f (g • x) - ∑ g, f (g • y)| ≤ C * (L * ‖↑x - ↑y‖)\"}],\"rawEdgeId\":\"telescope_17\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"|(∑ g, f (g • x)) / C - (∑ g, f (g • y)) / C| ≤ L * ‖↑x - ↑y‖\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hdiv\",\"statement\":\"|(∑ g, f (g • x)) / C - (∑ g, f (g • y)) / C| ≤ L * ‖↑x - ↑y‖\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p3260_group_symmetrization_lipschitz\",\"reconstructedProofSha256\":\"f5049a81a77e55fb08e36e0e068ba58d49266977f925d0df7cc9e25e4e6c8bb4\",\"selectedEdgeCount\":5,\"theoremName\":\"group_symmetrization_lipschitz\",\"topologySha256\":\"98cc2ec8af7eb795746b45890d773629394f9177fe3dbdba47ff1373fbbd3200\"}"
