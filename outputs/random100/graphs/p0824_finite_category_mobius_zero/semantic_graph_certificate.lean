import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p0824_finite_category_mobius_zero
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: fc0062b16cdb74302d0b069d001d3a9330b4878c76acd8c358807a4adc79c636
-- reconstructed_proof_sha256: 85bb367dff97023e3c5a6706022a1067e32c203f5187dc86b6b8333408893fc5
-- selected_edge_count: 10

/- verified submission -/

open CategoryTheory

theorem finite_category_mobius_zero
    {A : Type u} [CategoryTheory.Category.{v, u} A] [Fintype A]
    [DecidableEq A] [∀ a b : A, Fintype (a ⟶ b)]
    (μ : A → A → ℚ)
    (hμζ : ∀ a c : A,
      ∑ b : A, μ a b * (Fintype.card (b ⟶ c) : ℚ) =
        if a = c then 1 else 0)
    (hζμ : ∀ a c : A,
      ∑ b : A, (Fintype.card (a ⟶ b) : ℚ) * μ b c =
        if a = c then 1 else 0)
    {a b : A} (hab : IsEmpty (a ⟶ b)) :
    μ a b = 0 := by
  let ζ : Matrix A A ℚ := fun i j => (Fintype.card (i ⟶ j) : ℚ)
  let M : Matrix A A ℚ := fun i j => μ i j
  have hMZ : M * ζ = 1 := by
    ext i j
    simpa [M, ζ, Matrix.mul_apply] using hμζ i j
  have hZM : ζ * M = 1 := by
    ext i j
    simpa [M, ζ, Matrix.mul_apply] using hζμ i j
  letI : Invertible ζ := invertibleOfRightInverse ζ M hZM
  let label : A → Bool := fun x => decide (Fintype.card (x ⟶ b) = 0)
  have hζtri : ζ.BlockTriangular label := by
    intro i j hlt
    by_contra hijζ
    have hcard : Fintype.card (i ⟶ j) ≠ 0 := by
      intro hcard
      apply hijζ
      simp [ζ, hcard]
    have hij : Nonempty (i ⟶ j) :=
      Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hcard)
    have hjfalse : label j = false := (Bool.lt_iff.mp hlt).1
    have hitrue : label i = true := (Bool.lt_iff.mp hlt).2
    have hjcard : Fintype.card (j ⟶ b) ≠ 0 := by
      intro hjcard
      simp [label, hjcard] at hjfalse
    have hjreach : Nonempty (j ⟶ b) :=
      Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hjcard)
    have hicard : Fintype.card (i ⟶ b) = 0 := by
      by_contra hicard
      simp [label, hicard] at hitrue
    have hinreach : ¬ Nonempty (i ⟶ b) := by
      intro hi
      have hpos : 0 < Fintype.card (i ⟶ b) := Fintype.card_pos
      omega
    exact hinreach ⟨hij.some ≫ hjreach.some⟩
  have hμtri : (ζ⁻¹).BlockTriangular label :=
    Matrix.blockTriangular_inv_of_blockTriangular hζtri
  have hinv : ζ⁻¹ = M := Matrix.inv_eq_left_inv hMZ
  have hbcard : Fintype.card (b ⟶ b) ≠ 0 := by
    have hb : Nonempty (b ⟶ b) := ⟨𝟙 b⟩
    exact Fintype.card_ne_zero
  have hlt : label b < label a := by
    rw [Bool.lt_iff]
    constructor
    · simp [label, hbcard]
    · simp [label]
  have hzero : (ζ⁻¹) a b = 0 := hμtri hlt
  have : M a b = 0 := by
    simpa [hinv] using hzero
  simpa [M] using this


#check_dependency_graph "finite_category_mobius_zero" against "{\"edges\":[{\"conclusion\":{\"name\":\"hMZ\",\"statement\":\"M * ζ = 1\"},\"graphEdgeId\":\"h_001_hmz\",\"premises\":[{\"name\":\"hμζ\",\"statement\":\"∀ (a c : A), ∑ b, μ a b * ↑(Fintype.card (b ⟶ c)) = if a = c then 1 else 0\"}],\"rawEdgeId\":\"telescope_13\"},{\"conclusion\":{\"name\":\"hZM\",\"statement\":\"ζ * M = 1\"},\"graphEdgeId\":\"h_002_hzm\",\"premises\":[{\"name\":\"hζμ\",\"statement\":\"∀ (a c : A), ∑ b, ↑(Fintype.card (a ⟶ b)) * μ b c = if a = c then 1 else 0\"}],\"rawEdgeId\":\"telescope_14\"},{\"conclusion\":{\"name\":\"hζtri\",\"statement\":\"ζ.BlockTriangular label\"},\"graphEdgeId\":\"h_003_h_tri\",\"premises\":[],\"rawEdgeId\":\"telescope_16\"},{\"conclusion\":{\"name\":\"hbcard\",\"statement\":\"Fintype.card (b ⟶ b) ≠ 0\"},\"graphEdgeId\":\"h_006_hbcard\",\"premises\":[],\"rawEdgeId\":\"telescope_19\"},{\"conclusion\":{\"name\":\"hμtri\",\"statement\":\"ζ⁻¹.BlockTriangular label\"},\"graphEdgeId\":\"h_004_h_tri\",\"premises\":[{\"name\":\"hZM\",\"statement\":\"ζ * M = 1\"},{\"name\":\"hζtri\",\"statement\":\"ζ.BlockTriangular label\"}],\"rawEdgeId\":\"telescope_17\"},{\"conclusion\":{\"name\":\"hinv\",\"statement\":\"ζ⁻¹ = M\"},\"graphEdgeId\":\"h_005_hinv\",\"premises\":[{\"name\":\"hMZ\",\"statement\":\"M * ζ = 1\"}],\"rawEdgeId\":\"telescope_18\"},{\"conclusion\":{\"name\":\"hlt\",\"statement\":\"label b < label a\"},\"graphEdgeId\":\"h_007_hlt\",\"premises\":[{\"name\":\"hab\",\"statement\":\"IsEmpty (a ⟶ b)\"},{\"name\":\"hbcard\",\"statement\":\"Fintype.card (b ⟶ b) ≠ 0\"}],\"rawEdgeId\":\"telescope_20\"},{\"conclusion\":{\"name\":\"hzero\",\"statement\":\"ζ⁻¹ a b = 0\"},\"graphEdgeId\":\"h_008_hzero\",\"premises\":[{\"name\":\"hμtri\",\"statement\":\"ζ⁻¹.BlockTriangular label\"},{\"name\":\"hlt\",\"statement\":\"label b < label a\"}],\"rawEdgeId\":\"telescope_21\"},{\"conclusion\":{\"name\":\"this\",\"statement\":\"M a b = 0\"},\"graphEdgeId\":\"h_009_this\",\"premises\":[{\"name\":\"hinv\",\"statement\":\"ζ⁻¹ = M\"},{\"name\":\"hzero\",\"statement\":\"ζ⁻¹ a b = 0\"}],\"rawEdgeId\":\"telescope_22\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"M a b = 0\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"this\",\"statement\":\"M a b = 0\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0824_finite_category_mobius_zero\",\"reconstructedProofSha256\":\"85bb367dff97023e3c5a6706022a1067e32c203f5187dc86b6b8333408893fc5\",\"selectedEdgeCount\":10,\"theoremName\":\"finite_category_mobius_zero\",\"topologySha256\":\"fc0062b16cdb74302d0b069d001d3a9330b4878c76acd8c358807a4adc79c636\"}"
