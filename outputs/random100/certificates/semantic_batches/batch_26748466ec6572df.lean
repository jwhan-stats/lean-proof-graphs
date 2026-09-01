import GraphCertificate
import Mathlib

namespace Rollout_p0617_sqrt_two_weighted_sum_lt

-- graph_id: p0617_sqrt_two_weighted_sum_lt
-- topology_sha256: 85963c6ebe640ec9f2bbd8441d5657b918440f84f595b189f386721059f5c9f8
/- accepted add_to_file helper 1 -/

open Finset Real

noncomputable section

def wsum (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), ((n - j : ℕ) : ℝ) * (Real.sqrt 2) ^ j

lemma wsum_succ (n : ℕ) :
    wsum (n + 1) = wsum n + ∑ j ∈ Finset.range (n + 1), (Real.sqrt 2) ^ j := by
  unfold wsum
  rw [Finset.sum_range_succ]
  have hlast : ((n + 1 - (n + 1) : ℕ) : ℝ) * (Real.sqrt 2) ^ (n + 1) = 0 := by simp
  rw [hlast, add_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have hnat : n + 1 - j = n - j + 1 := by omega
  rw [hnat]
  norm_num [pow_succ, add_mul, one_mul]

lemma wsum_eq (n : ℕ) :
    wsum n =
      ((Real.sqrt 2) ^ (n + 1) + (n : ℝ) - ((n + 1 : ℕ) : ℝ) * Real.sqrt 2) *
        (Real.sqrt 2 + 1) ^ 2 := by
  induction n with
  | zero =>
      simp [wsum]
  | succ n ih =>
      rw [wsum_succ n, geom_sum_eq, ih]
      · rw [div_eq_mul_inv, Real.inv_sqrt_two_sub_one]
        have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
        have h3 : (Real.sqrt 2) ^ 3 = 2 * Real.sqrt 2 := by
          rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, h2]
        have h4 : (Real.sqrt 2) ^ 4 = 4 := by
          rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, h2]
          norm_num
        ring_nf
        simp only [h2, h3, h4]
        push_cast
        ring
      · exact Real.one_lt_sqrt_two.ne'

/- verified submission -/
theorem sqrt_two_weighted_sum_lt (i : ℕ) :
    (∑ j ∈ Finset.range (i + 1), ((i - j : ℕ) : ℝ) * (Real.sqrt 2) ^ j) <
      (4 + 3 * Real.sqrt 2) * (Real.sqrt 2) ^ i := by
  change wsum i < (4 + 3 * Real.sqrt 2) * (Real.sqrt 2) ^ i
  let r : ℝ := Real.sqrt 2
  let q : ℝ := (r + 1) ^ 2
  let b : ℝ := ((i + 1 : ℕ) : ℝ) * r - (i : ℝ)
  have hr_gt_one : 1 < r := by
    dsimp [r]
    exact Real.one_lt_sqrt_two
  have hr_pos : 0 < r := lt_trans zero_lt_one hr_gt_one
  have hsq : r ^ 2 = 2 := by
    dsimp [r]
    exact Real.sq_sqrt (by norm_num)
  have hcube : r ^ 3 = 2 * r := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, hsq]
  have htarget : (4 + 3 * r) * r ^ i = r ^ (i + 1) * q := by
    have hrq : r * q = 4 + 3 * r := by
      dsimp [q]
      ring_nf
      rw [hcube, hsq]
      ring
    calc
      (4 + 3 * r) * r ^ i = (r * q) * r ^ i := by rw [hrq]
      _ = r ^ (i + 1) * q := by
        rw [pow_succ]
        ring
  have hdiff : (4 + 3 * r) * r ^ i - wsum i = b * q := by
    rw [wsum_eq i]
    dsimp [r, q, b]
    rw [htarget]
    dsimp [r, q]
    push_cast
    ring
  have hb : 0 < b := by
    have hnonneg : 0 ≤ (i : ℝ) * (r - 1) := by
      exact mul_nonneg (Nat.cast_nonneg i) (sub_nonneg.mpr hr_gt_one.le)
    have hsumpos : 0 < (i : ℝ) * (r - 1) + r :=
      add_pos_of_nonneg_of_pos hnonneg hr_pos
    have hb_eq : b = (i : ℝ) * (r - 1) + r := by
      dsimp [b]
      push_cast
      ring
    rw [hb_eq]
    exact hsumpos
  have hq : 0 < q := by
    dsimp [q]
    exact sq_pos_of_pos (add_pos hr_pos zero_lt_one)
  have hdiff_pos : 0 < (4 + 3 * r) * r ^ i - wsum i := by
    rw [hdiff]
    exact mul_pos hb hq
  dsimp [r] at hdiff_pos
  linarith

end
end Rollout_p0617_sqrt_two_weighted_sum_lt

#check_dependency_graph "Rollout_p0617_sqrt_two_weighted_sum_lt.sqrt_two_weighted_sum_lt" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∑ j ∈ Finset.range (i + 1), ↑(i - j) * √2 ^ j < (4 + 3 * √2) * √2 ^ i\"},\"graphEdgeId\":\"h_goal\",\"premises\":[],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0617_sqrt_two_weighted_sum_lt\",\"reconstructedProofSha256\":\"00869fa5da35e7d12e38d58e6a24470dda9d61d1d7f5e9e275594cebca590c9c\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p0617_sqrt_two_weighted_sum_lt.sqrt_two_weighted_sum_lt\",\"topologySha256\":\"85963c6ebe640ec9f2bbd8441d5657b918440f84f595b189f386721059f5c9f8\"}"

namespace Rollout_p0644_collapse_set_partialorder_iff_ordconnected

-- graph_id: p0644_collapse_set_partialorder_iff_ordconnected
-- topology_sha256: ffa7fbe65112bd88a8747c3d228b9e112409eaf0464d453ac16f226471a79af6
/- verified submission -/
theorem collapse_set_partialOrder_iff_ordConnected
    {P : Type*} [PartialOrder P] (B : Set P) (hB : B.Nonempty) :
    let Q := Sum {x : P // x ∉ B} Unit
    let r : Q → Q → Prop := fun x y =>
      match x, y with
      | Sum.inr _, Sum.inr _ => True
      | Sum.inr _, Sum.inl y => ∃ b ∈ B, b ≤ y.1
      | Sum.inl x, Sum.inr _ => ∃ b ∈ B, x.1 ≤ b
      | Sum.inl x, Sum.inl y =>
          x.1 ≤ y.1 ∨ ∃ b ∈ B, ∃ b' ∈ B, x.1 ≤ b ∧ b' ≤ y.1
    IsPartialOrder Q r ↔ B.OrdConnected := by
  let Q := Sum {x : P // x ∉ B} Unit
  let r : Q → Q → Prop := fun x y =>
      match x, y with
      | Sum.inr _, Sum.inr _ => True
      | Sum.inr _, Sum.inl y => ∃ b ∈ B, b ≤ y.1
      | Sum.inl x, Sum.inr _ => ∃ b ∈ B, x.1 ≤ b
      | Sum.inl x, Sum.inl y =>
          x.1 ≤ y.1 ∨ ∃ b ∈ B, ∃ b' ∈ B, x.1 ≤ b ∧ b' ≤ y.1
  change IsPartialOrder Q r ↔ B.OrdConnected
  have _ : B.Nonempty := hB
  constructor
  · intro hpo
    refine Set.OrdConnected.mk ?_
    intro x hx y hy z hz
    rcases Set.mem_Icc.mp hz with ⟨hxz, hzy⟩
    by_contra hzB
    let zq : {x : P // x ∉ B} := ⟨z, hzB⟩
    have hstar_z : r (Sum.inr ()) (Sum.inl zq) := ⟨x, hx, hxz⟩
    have hz_star : r (Sum.inl zq) (Sum.inr ()) := ⟨y, hy, hzy⟩
    have heq := hpo.antisymm (Sum.inr ()) (Sum.inl zq) hstar_z hz_star
    cases heq
  · intro hconn
    have hconvex : ∀ {x y z : P}, x ∈ B → y ∈ B → x ≤ z → z ≤ y → z ∈ B := by
      intro x y z hx hy hxz hzy
      exact hconn.out' hx hy (Set.mem_Icc.mpr ⟨hxz, hzy⟩)
    have hrefl : ∀ q : Q, r q q := by
      intro q
      cases q with
      | inl x =>
          exact Or.inl le_rfl
      | inr u =>
          trivial
    have htrans : ∀ a b c : Q, r a b → r b c → r a c := by
      intro a b c hab hbc
      cases a with
      | inl x =>
          cases b with
          | inl y =>
              cases c with
              | inl z =>
                  rcases hab with hxy | ⟨b₁, hb₁, b₂, hb₂, hxb₁, hb₂y⟩
                  · rcases hbc with hyz | ⟨c₁, hc₁, c₂, hc₂, hyc₁, hc₂z⟩
                    · exact Or.inl (le_trans hxy hyz)
                    · exact Or.inr ⟨c₁, hc₁, c₂, hc₂, le_trans hxy hyc₁, hc₂z⟩
                  · rcases hbc with hyz | ⟨c₁, hc₁, c₂, hc₂, hyc₁, hc₂z⟩
                    · exact Or.inr ⟨b₁, hb₁, b₂, hb₂, hxb₁, le_trans hb₂y hyz⟩
                    · exact Or.inr ⟨b₁, hb₁, c₂, hc₂, hxb₁, hc₂z⟩
              | inr z =>
                  rcases hbc with ⟨c', hc', hyc'⟩
                  rcases hab with hxy | ⟨b₁, hb₁, b₂, hb₂, hxb₁, hb₂y⟩
                  · exact ⟨c', hc', le_trans hxy hyc'⟩
                  · exact ⟨b₁, hb₁, hxb₁⟩
          | inr y =>
              cases c with
              | inl z =>
                  rcases hab with ⟨b₁, hb₁, hxb₁⟩
                  rcases hbc with ⟨b₂, hb₂, hb₂z⟩
                  exact Or.inr ⟨b₁, hb₁, b₂, hb₂, hxb₁, hb₂z⟩
              | inr z =>
                  exact hab
      | inr x =>
          cases b with
          | inl y =>
              cases c with
              | inl z =>
                  rcases hbc with hyz | ⟨c₁, hc₁, c₂, hc₂, hyc₁, hc₂z⟩
                  · rcases hab with ⟨b', hb', hb'y⟩
                    exact ⟨b', hb', le_trans hb'y hyz⟩
                  · exact ⟨c₂, hc₂, hc₂z⟩
              | inr z =>
                  trivial
          | inr y =>
              exact hbc
    have hanti : ∀ a b : Q, r a b → r b a → a = b := by
      intro a b hab hba
      cases a with
      | inl x =>
          cases b with
          | inl y =>
              rcases hab with hxy | ⟨b₁, hb₁, b₂, hb₂, hxb₁, hb₂y⟩
              · rcases hba with hyx | ⟨c₁, hc₁, c₂, hc₂, hyc₁, hc₂x⟩
                · exact congrArg Sum.inl (Subtype.ext (le_antisymm hxy hyx))
                · exfalso
                  exact y.2 (hconvex hc₂ hc₁ (le_trans hc₂x hxy) hyc₁)
              · rcases hba with hyx | ⟨c₁, hc₁, c₂, hc₂, hyc₁, hc₂x⟩
                · exfalso
                  exact x.2 (hconvex hb₂ hb₁ (le_trans hb₂y hyx) hxb₁)
                · exfalso
                  exact y.2 (hconvex hb₂ hc₁ hb₂y hyc₁)
          | inr y =>
              rcases hab with ⟨b₁, hb₁, hxb₁⟩
              rcases hba with ⟨b₂, hb₂, hb₂x⟩
              exfalso
              exact x.2 (hconvex hb₂ hb₁ hb₂x hxb₁)
      | inr x =>
          cases b with
          | inl y =>
              rcases hab with ⟨b₁, hb₁, hb₁y⟩
              rcases hba with ⟨b₂, hb₂, hyb₂⟩
              exfalso
              exact y.2 (hconvex hb₁ hb₂ hb₁y hyb₂)
          | inr y =>
              rfl
    letI : Std.Refl r := ⟨hrefl⟩
    letI : IsTrans Q r := ⟨htrans⟩
    letI : IsPreorder Q r := IsPreorder.mk
    letI : Std.Antisymm r := ⟨hanti⟩
    exact IsPartialOrder.mk

end Rollout_p0644_collapse_set_partialorder_iff_ordconnected

#check_dependency_graph "Rollout_p0644_collapse_set_partialorder_iff_ordconnected.collapse_set_partialOrder_iff_ordConnected" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let Q := { x // x ∉ B } ⊕ Unit; let r := fun x y => match x, y with | Sum.inr val, Sum.inr val_1 => True | Sum.inr val, Sum.inl y => ∃ b ∈ B, b ≤ ↑y | Sum.inl x, Sum.inr val => ∃ b ∈ B, ↑x ≤ b | Sum.inl x, Sum.inl y => ↑x ≤ ↑y ∨ ∃ b ∈ B, ∃ b' ∈ B, ↑x ≤ b ∧ b' ≤ ↑y; IsPartialOrder Q r ↔ B.OrdConnected\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hB\",\"statement\":\"B.Nonempty\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0644_collapse_set_partialorder_iff_ordconnected\",\"reconstructedProofSha256\":\"1ae4cbda6d10f64039fa677ac0ee6fdd29c359f93ee7843f458ca49eb3b79ed2\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p0644_collapse_set_partialorder_iff_ordconnected.collapse_set_partialOrder_iff_ordConnected\",\"topologySha256\":\"ffa7fbe65112bd88a8747c3d228b9e112409eaf0464d453ac16f226471a79af6\"}"

namespace Rollout_p0786_projective_iff_projective_in_thick_subcate

-- graph_id: p0786_projective_iff_projective_in_thick_subcate
-- topology_sha256: 0e507526b3dc3c2fe382547187da09f38ad1d12154a2fa062539f87c58d855eb
/- verified submission -/
open CategoryTheory

theorem projective_iff_projective_in_thick_subcategory
    {C : Type u} [CategoryTheory.Category.{v} C] [CategoryTheory.Abelian C]
    [CategoryTheory.EnoughProjectives C]
    (S : CategoryTheory.ObjectProperty C)
    [S.IsStableUnderRetracts]
    (hS : ∀ (T : CategoryTheory.ShortComplex C), T.ShortExact →
      (S T.X₁ ∧ S T.X₂ → S T.X₃) ∧
      (S T.X₁ ∧ S T.X₃ → S T.X₂) ∧
      (S T.X₂ ∧ S T.X₃ → S T.X₁))
    (hproj : ∀ (P : C), CategoryTheory.Projective P → S P) :
    ∀ (Q : C), S Q →
      (CategoryTheory.Projective Q ↔
        ∀ (T : CategoryTheory.ShortComplex C), T.X₃ = Q →
          S T.X₁ → S T.X₂ → T.ShortExact →
            CategoryTheory.IsSplitEpi T.g) := by
  intro Q hQ
  constructor
  · intro hQproj T hT hS₁ hS₂ hTexact
    subst Q
    letI : CategoryTheory.Epi T.g := hTexact.epi_g
    exact CategoryTheory.IsSplitEpi.mk'
      ⟨CategoryTheory.Projective.factorThru (𝟙 T.X₃) T.g,
        CategoryTheory.Projective.factorThru_comp (𝟙 T.X₃) T.g⟩
  · intro h
    let T : CategoryTheory.ShortComplex C :=
      CategoryTheory.ShortComplex.kernelSequence (CategoryTheory.Projective.π Q)
    haveI : CategoryTheory.Mono T.f := by
      dsimp [T]
      infer_instance
    haveI : CategoryTheory.Epi T.g := by
      dsimp [T]
      exact CategoryTheory.Projective.π_epi Q
    have hTexact : T.ShortExact := by
      exact CategoryTheory.ShortComplex.ShortExact.mk
        (CategoryTheory.ShortComplex.kernelSequence_exact (CategoryTheory.Projective.π Q))
    have hS₂ : S T.X₂ := by
      exact hproj T.X₂ (by
        simpa [T] using CategoryTheory.Projective.projective_over Q)
    have hS₃ : S T.X₃ := by
      simpa [T] using hQ
    have hS₁ : S T.X₁ :=
      (hS T hTexact).2.2 ⟨hS₂, hS₃⟩
    have hsplit : CategoryTheory.IsSplitEpi T.g :=
      h T (by simp [T]) hS₁ hS₂ hTexact
    have hsplitπ : CategoryTheory.IsSplitEpi (CategoryTheory.Projective.π Q) := by
      simpa [T] using hsplit
    letI : CategoryTheory.IsSplitEpi (CategoryTheory.Projective.π Q) := hsplitπ
    exact CategoryTheory.Retract.projective
      ⟨CategoryTheory.section_ (CategoryTheory.Projective.π Q),
        CategoryTheory.Projective.π Q,
        CategoryTheory.IsSplitEpi.id (CategoryTheory.Projective.π Q)⟩

end Rollout_p0786_projective_iff_projective_in_thick_subcate

#check_dependency_graph "Rollout_p0786_projective_iff_projective_in_thick_subcate.projective_iff_projective_in_thick_subcategory" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"CategoryTheory.Projective Q ↔ ∀ (T : CategoryTheory.ShortComplex C), T.X₃ = Q → S T.X₁ → S T.X₂ → T.ShortExact → CategoryTheory.IsSplitEpi T.g\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"CategoryTheory.EnoughProjectives C\"},{\"name\":\"hS\",\"statement\":\"∀ (T : CategoryTheory.ShortComplex C), T.ShortExact → (S T.X₁ ∧ S T.X₂ → S T.X₃) ∧ (S T.X₁ ∧ S T.X₃ → S T.X₂) ∧ (S T.X₂ ∧ S T.X₃ → S T.X₁)\"},{\"name\":\"hproj\",\"statement\":\"∀ (P : C), CategoryTheory.Projective P → S P\"},{\"name\":\"hQ\",\"statement\":\"S Q\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0786_projective_iff_projective_in_thick_subcate\",\"reconstructedProofSha256\":\"9af942818e116aad491584bc5ca3299979d17eed29e03ac8b0e131bad4011d16\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p0786_projective_iff_projective_in_thick_subcate.projective_iff_projective_in_thick_subcategory\",\"topologySha256\":\"0e507526b3dc3c2fe382547187da09f38ad1d12154a2fa062539f87c58d855eb\"}"

namespace Rollout_p0824_finite_category_mobius_zero

-- graph_id: p0824_finite_category_mobius_zero
-- topology_sha256: fc0062b16cdb74302d0b069d001d3a9330b4878c76acd8c358807a4adc79c636
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

end Rollout_p0824_finite_category_mobius_zero

#check_dependency_graph "Rollout_p0824_finite_category_mobius_zero.finite_category_mobius_zero" against "{\"edges\":[{\"conclusion\":{\"name\":\"hMZ\",\"statement\":\"M * ζ = 1\"},\"graphEdgeId\":\"h_001_hmz\",\"premises\":[{\"name\":\"hμζ\",\"statement\":\"∀ (a c : A), ∑ b, μ a b * ↑(Fintype.card (b ⟶ c)) = if a = c then 1 else 0\"}],\"rawEdgeId\":\"telescope_13\"},{\"conclusion\":{\"name\":\"hZM\",\"statement\":\"ζ * M = 1\"},\"graphEdgeId\":\"h_002_hzm\",\"premises\":[{\"name\":\"hζμ\",\"statement\":\"∀ (a c : A), ∑ b, ↑(Fintype.card (a ⟶ b)) * μ b c = if a = c then 1 else 0\"}],\"rawEdgeId\":\"telescope_14\"},{\"conclusion\":{\"name\":\"hζtri\",\"statement\":\"ζ.BlockTriangular label\"},\"graphEdgeId\":\"h_003_h_tri\",\"premises\":[],\"rawEdgeId\":\"telescope_16\"},{\"conclusion\":{\"name\":\"hbcard\",\"statement\":\"Fintype.card (b ⟶ b) ≠ 0\"},\"graphEdgeId\":\"h_006_hbcard\",\"premises\":[],\"rawEdgeId\":\"telescope_19\"},{\"conclusion\":{\"name\":\"hμtri\",\"statement\":\"ζ⁻¹.BlockTriangular label\"},\"graphEdgeId\":\"h_004_h_tri\",\"premises\":[{\"name\":\"hZM\",\"statement\":\"ζ * M = 1\"},{\"name\":\"hζtri\",\"statement\":\"ζ.BlockTriangular label\"}],\"rawEdgeId\":\"telescope_17\"},{\"conclusion\":{\"name\":\"hinv\",\"statement\":\"ζ⁻¹ = M\"},\"graphEdgeId\":\"h_005_hinv\",\"premises\":[{\"name\":\"hMZ\",\"statement\":\"M * ζ = 1\"}],\"rawEdgeId\":\"telescope_18\"},{\"conclusion\":{\"name\":\"hlt\",\"statement\":\"label b < label a\"},\"graphEdgeId\":\"h_007_hlt\",\"premises\":[{\"name\":\"hab\",\"statement\":\"IsEmpty (a ⟶ b)\"},{\"name\":\"hbcard\",\"statement\":\"Fintype.card (b ⟶ b) ≠ 0\"}],\"rawEdgeId\":\"telescope_20\"},{\"conclusion\":{\"name\":\"hzero\",\"statement\":\"ζ⁻¹ a b = 0\"},\"graphEdgeId\":\"h_008_hzero\",\"premises\":[{\"name\":\"hμtri\",\"statement\":\"ζ⁻¹.BlockTriangular label\"},{\"name\":\"hlt\",\"statement\":\"label b < label a\"}],\"rawEdgeId\":\"telescope_21\"},{\"conclusion\":{\"name\":\"this\",\"statement\":\"M a b = 0\"},\"graphEdgeId\":\"h_009_this\",\"premises\":[{\"name\":\"hinv\",\"statement\":\"ζ⁻¹ = M\"},{\"name\":\"hzero\",\"statement\":\"ζ⁻¹ a b = 0\"}],\"rawEdgeId\":\"telescope_22\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"M a b = 0\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"this\",\"statement\":\"M a b = 0\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0824_finite_category_mobius_zero\",\"reconstructedProofSha256\":\"85bb367dff97023e3c5a6706022a1067e32c203f5187dc86b6b8333408893fc5\",\"selectedEdgeCount\":10,\"theoremName\":\"Rollout_p0824_finite_category_mobius_zero.finite_category_mobius_zero\",\"topologySha256\":\"fc0062b16cdb74302d0b069d001d3a9330b4878c76acd8c358807a4adc79c636\"}"

namespace Rollout_p0912_catlin_vertical_curve_is_geodesic

-- graph_id: p0912_catlin_vertical_curve_is_geodesic
-- topology_sha256: ff55e243bcb013b3bb1fe2d4b53943a217b77c71844ab85c4d3c84a7f12cdfd5
/- accepted add_to_file helper 1 -/

open scoped ComplexConjugate

noncomputable section

def evalDiag : ℂ → MvPolynomial (Fin 2) ℂ → ℂ :=
  fun z q => MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z else star z) q

@[simp] lemma evalDiag_zero (z : ℂ) : evalDiag z (0 : MvPolynomial (Fin 2) ℂ) = 0 := by
  change MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z else star z) 0 = 0
  exact map_zero _

@[simp] lemma evalDiag_one (z : ℂ) : evalDiag z (1 : MvPolynomial (Fin 2) ℂ) = 1 := by
  change MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z else star z) 1 = 1
  exact map_one _

@[simp] lemma evalDiag_C (z : ℂ) (a : ℂ) : evalDiag z (MvPolynomial.C a) = a := by
  change MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z else star z) (MvPolynomial.C a) = a
  exact MvPolynomial.eval_C a

@[simp] lemma evalDiag_add (z : ℂ) (q r : MvPolynomial (Fin 2) ℂ) :
    evalDiag z (q + r) = evalDiag z q + evalDiag z r := by
  change MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z else star z) (q + r) = _
  exact map_add _ _ _

@[simp] lemma evalDiag_mul (z : ℂ) (q r : MvPolynomial (Fin 2) ℂ) :
    evalDiag z (q * r) = evalDiag z q * evalDiag z r := by
  change MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z else star z) (q * r) = _
  exact map_mul _ _ _

@[simp] lemma evalDiag_X (z : ℂ) (i : Fin 2) :
    evalDiag z (MvPolynomial.X i) = if i = 0 then z else star z := by
  change MvPolynomial.eval (fun j : Fin 2 => if j = 0 then z else star z) (MvPolynomial.X i) = _
  exact MvPolynomial.eval_X i

lemma hasDerivAt_evalDiag
    (q : MvPolynomial (Fin 2) ℂ) {z : ℝ → ℂ} {z' : ℂ} {x : ℝ}
    (hz : HasDerivAt z z' x) :
    HasDerivAt (fun u => evalDiag (z u) q)
      (z' * evalDiag (z x) ((MvPolynomial.pderiv (0 : Fin 2)) q) +
        star z' * evalDiag (z x) ((MvPolynomial.pderiv (1 : Fin 2)) q)) x := by
  induction q using MvPolynomial.induction_on with
  | C a =>
      have hfun : (fun u => evalDiag (z u) (MvPolynomial.C a)) = fun _ : ℝ => a := by
        ext u; simp
      have hder : z' * evalDiag (z x) ((MvPolynomial.pderiv (0 : Fin 2)) (MvPolynomial.C a)) +
        star z' * evalDiag (z x) ((MvPolynomial.pderiv (1 : Fin 2)) (MvPolynomial.C a)) = 0 := by
        rw [MvPolynomial.pderiv_C, MvPolynomial.pderiv_C]
        simp
      rw [hfun, hder]
      exact hasDerivAt_const x a
  | add q r hq hr =>
      have h := hq.add hr
      convert h using 1
      · ext u; simp
      · rw [map_add, map_add]
        simp
        ring
  | mul_X q i hq =>
      let f : Fin 2 → ℝ → ℂ := fun j u => if j = 0 then z u else star (z u)
      let f' : Fin 2 → ℂ := fun j => if j = 0 then z' else star z'
      have hf : HasDerivAt (fun u => f i u) (f' i) x := by
        by_cases hi : i = 0
        · simp [f, f', hi, hz]
        · have hi1 : i = 1 := by omega
          simpa [f, f', hi, hi1] using hz.star
      have hmul := hq.mul hf
      convert hmul using 1
      · ext u
        simp [f]
      · simp [f, f']
        by_cases hi : i = 0
        · simp [hi, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, Pi.single_apply]
          ring
        · have hi1 : i = 1 := by omega
          simp [hi, hi1, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, Pi.single_apply]
          ring

/- accepted add_to_file helper 2 -/
lemma evalDiag_pderiv_one_eq_conj_pderiv_zero
    (p : MvPolynomial (Fin 2) ℂ)
    (hreal : ∀ z : ℂ, (evalDiag z p).im = 0) (z : ℂ) :
    evalDiag z ((MvPolynomial.pderiv (1 : Fin 2)) p) =
      star (evalDiag z ((MvPolynomial.pderiv (0 : Fin 2)) p)) := by
  let A : ℂ := evalDiag z ((MvPolynomial.pderiv (0 : Fin 2)) p)
  let B : ℂ := evalDiag z ((MvPolynomial.pderiv (1 : Fin 2)) p)
  have hxpath : HasDerivAt (fun t : ℝ => z + (t : ℂ)) 1 0 := by
    have h := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_id (0 : ℝ)))
    simpa [Function.comp_def] using h.const_add z
  have hx := hasDerivAt_evalDiag p hxpath
  have hxim : HasDerivAt (fun t : ℝ => (evalDiag (z + (t : ℂ)) p).im)
      (1 * A + star (1 : ℂ) * B).im 0 := by
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hx
    simpa [A, B, Function.comp_def] using h
  have hxfun : (fun t : ℝ => (evalDiag (z + (t : ℂ)) p).im) = fun _ : ℝ => 0 := by
    ext t
    exact hreal _
  rw [hxfun] at hxim
  have h1 : (A + B).im = 0 := by
    have hu := hxim.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    simpa [A, B] using hu
  have hipath : HasDerivAt (fun t : ℝ => z + Complex.I * (t : ℂ)) Complex.I 0 := by
    have h := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_id (0 : ℝ)))
    have hmul := h.const_mul Complex.I
    simpa [Function.comp_def] using hmul.const_add z
  have hi := hasDerivAt_evalDiag p hipath
  have hiim : HasDerivAt (fun t : ℝ => (evalDiag (z + Complex.I * (t : ℂ)) p).im)
      (Complex.I * A + star Complex.I * B).im 0 := by
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hi
    simpa [A, B, Function.comp_def] using h
  have hifun : (fun t : ℝ => (evalDiag (z + Complex.I * (t : ℂ)) p).im) = fun _ : ℝ => 0 := by
    ext t
    exact hreal _
  rw [hifun] at hiim
  have h2 : (Complex.I * A - Complex.I * B).im = 0 := by
    have hu := hiim.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    simpa [A, B, sub_eq_add_neg] using hu
  apply Complex.ext
  · have h : A.re - B.re = 0 := by
      simpa [A, B, Complex.mul_im] using h2
    have hb : A.re = B.re := by linarith
    simpa [A, B, star] using hb.symm
  · have h : A.im + B.im = 0 := by simpa [A, B] using h1
    have hb : B.im = -A.im := by linarith
    simpa [A, B, star] using hb

/- accepted add_to_file helper 3 -/
lemma continuous_evalDiag (q : MvPolynomial (Fin 2) ℂ) : Continuous fun z => evalDiag z q := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using continuous_const
  | add q r hq hr => simpa using hq.add hr
  | mul_X q i hq =>
      have hi : Continuous fun z : ℂ => (if i = 0 then z else star z) := by
        by_cases h : i = 0
        · simpa [h] using continuous_id
        · have h1 : i = 1 := by omega
          simpa [h, h1] using continuous_star
      have h := hq.mul hi
      convert h using 1
      ext z
      by_cases hiz : i = 0 <;> simp [hiz]

/- accepted add_to_file helper 4 -/
def diagDer (p : MvPolynomial (Fin 2) ℂ) (j k : ℕ) (z : ℂ) : ℂ :=
  evalDiag z ((MvPolynomial.pderiv (1 : Fin 2))^[k]
    ((MvPolynomial.pderiv (0 : Fin 2))^[j] p))

def ASet (p : MvPolynomial (Fin 2) ℂ) (l : ℕ) (z : ℂ) : Set ℝ :=
  {u : ℝ | ∃ j k : ℕ, 0 < j ∧ 0 < k ∧ j + k = l ∧ u = ‖diagDer p j k z‖}

def AIndex (l : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (l + 1)).product (Finset.range (l + 1))

def AValue (p : MvPolynomial (Fin 2) ℂ) (l : ℕ) (z : ℂ) (jk : ℕ × ℕ) : ℝ :=
  if 0 < jk.1 ∧ 0 < jk.2 ∧ jk.1 + jk.2 = l then ‖diagDer p jk.1 jk.2 z‖ else 0

lemma AIndex_nonempty (l : ℕ) : (AIndex l).Nonempty := by
  refine ⟨(0,0), ?_⟩
  simp [AIndex]

lemma ASet_eq_finset_sup' {p : MvPolynomial (Fin 2) ℂ} {l : ℕ} (hl : 2 ≤ l) (z : ℂ) :
    sSup (ASet p l z) = (AIndex l).sup' (AIndex_nonempty l) (AValue p l z) := by
  have hne : (ASet p l z).Nonempty := by
    refine ⟨‖diagDer p 1 (l-1) z‖, 1, l-1, by omega, by omega, by omega, rfl⟩
  refine IsLUB.csSup_eq ?_ hne
  constructor
  · rintro u ⟨j,k,hj,hk,hjk,rfl⟩
    have hmem : (j,k) ∈ AIndex l := by
      simp [AIndex]
      omega
    have hv : AValue p l z (j,k) = ‖diagDer p j k z‖ := by
      simp [AValue,hj,hk,hjk]
    rw [← hv]
    exact Finset.le_sup' (AValue p l z) hmem
  · intro b hb
    apply Finset.sup'_le
    rintro ⟨j,k⟩ hmem
    by_cases hvalid : 0 < j ∧ 0 < k ∧ j + k = l
    · have hbv := hb ⟨j,k,hvalid.1,hvalid.2.1,hvalid.2.2,rfl⟩
      simpa [AValue,hvalid] using hbv
    · have hv : AValue p l z (j,k) = 0 := by simp [AValue,hvalid]
      have hnonneg : 0 ≤ ‖diagDer p 1 (l-1) z‖ := norm_nonneg _
      have hb0 : 0 ≤ b := by
        exact hnonneg.trans (hb ⟨1,l-1,by omega,by omega,by omega,rfl⟩)
      simpa [hv] using hb0

lemma continuous_ASet_sSup {p : MvPolynomial (Fin 2) ℂ} {l : ℕ} (hl : 2 ≤ l) :
    Continuous fun z : ℂ => sSup (ASet p l z) := by
  have hfun : (fun z : ℂ => sSup (ASet p l z)) =
      fun z => (AIndex l).sup' (AIndex_nonempty l) (AValue p l z) := by
    funext z
    exact ASet_eq_finset_sup' hl z
  rw [hfun]
  apply Continuous.finset_sup'_apply
  rintro ⟨j,k⟩ hmem
  by_cases hvalid : 0 < j ∧ 0 < k ∧ j + k = l
  · simpa [AValue, hvalid, diagDer] using (continuous_evalDiag _).norm
  · simpa [AValue, hvalid] using continuous_const

/- accepted add_to_file helper 5 -/
lemma re_evalDiag_chain {p : MvPolynomial (Fin 2) ℂ}
    (hreal : ∀ z : ℂ, (evalDiag z p).im = 0) {z v : ℂ} :
    (v * evalDiag z ((MvPolynomial.pderiv (0 : Fin 2)) p) +
      star v * evalDiag z ((MvPolynomial.pderiv (1 : Fin 2)) p)).re =
      (2 * v * evalDiag z ((MvPolynomial.pderiv (0 : Fin 2)) p)).re := by
  rw [evalDiag_pderiv_one_eq_conj_pderiv_zero p hreal z]
  let X : ℂ := v * evalDiag z ((MvPolynomial.pderiv (0 : Fin 2)) p)
  have hs : star v * star (evalDiag z ((MvPolynomial.pderiv (0 : Fin 2)) p)) = star X := by
    simp [X]
  rw [hs]
  simp [X]
  ring

/- accepted add_to_file helper 6 -/
lemma frontier_sublevel_eq_zero {X : Type*} [TopologicalSpace X] {r : X → ℝ}
    (hr : Continuous r) {Ω : Set X} (hΩ : Ω = {q | r q < 0}) {q : X}
    (hfront : q ∈ frontier Ω) : r q = 0 := by
  have hopen : IsOpen Ω := by
    rw [hΩ]
    exact isOpen_Iio.preimage hr
  have hnot : q ∉ Ω := by
    have hi := hfront.2
    rwa [hopen.interior_eq] at hi
  have hle : r q ≤ 0 := by
    have hsub : Ω ⊆ {x | r x ≤ 0} := by
      intro x hx
      exact le_of_lt (show r x < 0 from by rwa [hΩ] at hx)
    have hclosed : IsClosed {x | r x ≤ 0} := isClosed_le hr continuous_const
    exact closure_minimal hsub hclosed hfront.1
  have hge : 0 ≤ r q := by
    by_contra h
    have : r q < 0 := lt_of_not_ge h
    exact hnot (by rwa [hΩ])
  linarith

/- accepted add_to_file helper 7 -/
def PiecewiseC1Curve : (ℝ → ℂ × ℂ) → Prop := fun γ =>
  ∃ n : ℕ, ∃ u : Fin (n + 1) → ℝ,
    u 0 = 0 ∧ u ⟨n, Nat.lt_add_one n⟩ = 1 ∧ StrictMono u ∧
      ∀ i : Fin n,
        ContDiffOn ℝ 1 γ (Set.Icc (u i.castSucc) (u i.succ))

lemma PiecewiseC1Curve_single {γ : ℝ → ℂ × ℂ} (hγ : ContDiff ℝ 1 γ) :
    PiecewiseC1Curve γ := by
  refine ⟨1, fun i : Fin 2 => (i : ℝ), ?_, ?_, ?_, ?_⟩
  · simp
  · norm_num
  · intro i j hij
    exact Nat.cast_lt.mpr hij
  · intro i
    fin_cases i
    simpa using hγ.contDiffOn

/- accepted add_to_file helper 8 -/
lemma contDiff_evalDiag (q : MvPolynomial (Fin 2) ℂ) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun z => evalDiag z q := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add q r hq hr => simpa using hq.add hr
  | mul_X q i hq =>
      have hi : ContDiff ℝ n fun z : ℂ => (if i = 0 then z else star z) := by
        by_cases h : i = 0
        · simpa [h] using contDiff_id
        · have h1 : i = 1 := by omega
          have hc : ContDiff ℝ n fun z : ℂ => Complex.conjCLE z := Complex.conjCLE.contDiff
          simpa [h, h1, Complex.conjCLE_apply] using hc
      have h := hq.mul hi
      convert h using 1
      ext z
      by_cases hiz : i = 0 <;> simp [hiz]

/- accepted add_to_file helper 9 -/
def catlinP (p : MvPolynomial (Fin 2) ℂ) (z : ℂ) : ℝ := (evalDiag z p).re

def catlinPz (p : MvPolynomial (Fin 2) ℂ) (z : ℂ) : ℂ := diagDer p 1 0 z

def catlinA (p : MvPolynomial (Fin 2) ℂ) (l : ℕ) (z : ℂ) : ℝ := sSup (ASet p l z)

def catlinR (p : MvPolynomial (Fin 2) ℂ) (q : ℂ × ℂ) : ℝ := q.2.re + catlinP p q.1

def catlinM (m : ℕ) (p : MvPolynomial (Fin 2) ℂ) (q v : ℂ × ℂ) : ℝ :=
  ‖v.2 + 2 * v.1 * catlinPz p q.1‖ / |catlinR p q| +
    ‖v.1‖ * ∑ l ∈ Finset.Icc 2 m,
      Real.rpow (catlinA p l q.1 / |catlinR p q|) (1 / (l : ℝ))

/- accepted add_to_file helper 10 -/
lemma continuous_catlinP (p : MvPolynomial (Fin 2) ℂ) : Continuous (catlinP p) := by
  exact Complex.continuous_re.comp (continuous_evalDiag p)

lemma continuous_catlinPz (p : MvPolynomial (Fin 2) ℂ) : Continuous (catlinPz p) := by
  exact continuous_evalDiag _

lemma continuous_catlinR (p : MvPolynomial (Fin 2) ℂ) : Continuous (catlinR p) := by
  exact (Complex.continuous_re.comp continuous_snd).add ((continuous_catlinP p).comp continuous_fst)

lemma continuous_catlinA (p : MvPolynomial (Fin 2) ℂ) {l : ℕ} (hl : 2 ≤ l) :
    Continuous (catlinA p l) := by
  exact continuous_ASet_sSup hl

lemma catlinA_nonneg (p : MvPolynomial (Fin 2) ℂ) (l : ℕ) (z : ℂ) :
    0 ≤ catlinA p l z := by
  apply Real.sSup_nonneg
  rintro u ⟨j,k,hj,hk,hjk,rfl⟩
  exact norm_nonneg _

lemma catlinM_nonneg (m : ℕ) (p : MvPolynomial (Fin 2) ℂ) (q v : ℂ × ℂ) :
    0 ≤ catlinM m p q v := by
  unfold catlinM
  apply add_nonneg
  · exact div_nonneg (norm_nonneg _) (abs_nonneg _)
  · apply mul_nonneg (norm_nonneg _)
    apply Finset.sum_nonneg
    intro l hl
    apply Real.rpow_nonneg
    exact div_nonneg (catlinA_nonneg p l q.1) (abs_nonneg _)

/- accepted add_to_file helper 11 -/
lemma continuousOn_catlinM_comp {m : ℕ} {p : MvPolynomial (Fin 2) ℂ}
    {q v : ℝ → ℂ × ℂ} {s : Set ℝ}
    (hq : ContinuousOn q s) (hv : ContinuousOn v s)
    (hr : ∀ u ∈ s, catlinR p (q u) < 0) :
    ContinuousOn (fun u => catlinM m p (q u) (v u)) s := by
  have hq1 : ContinuousOn (fun u => (q u).1) s := continuous_fst.comp_continuousOn hq
  have hq2 : ContinuousOn (fun u => (q u).2) s := continuous_snd.comp_continuousOn hq
  have hv1 : ContinuousOn (fun u => (v u).1) s := continuous_fst.comp_continuousOn hv
  have hv2 : ContinuousOn (fun u => (v u).2) s := continuous_snd.comp_continuousOn hv
  have hR : ContinuousOn (fun u => catlinR p (q u)) s :=
    (continuous_catlinR p).comp_continuousOn hq
  have habs : ContinuousOn (fun u => |catlinR p (q u)|) s := hR.abs
  have hRne : ∀ u ∈ s, catlinR p (q u) ≠ 0 := fun u hu => ne_of_lt (hr u hu)
  have hfirst_num : ContinuousOn (fun u => ‖(v u).2 + 2 * (v u).1 * catlinPz p (q u).1‖) s := by
    have hpz : ContinuousOn (fun u => catlinPz p (q u).1) s :=
      (continuous_catlinPz p).comp_continuousOn hq1
    exact (hv2.add ((continuousOn_const.mul hv1).mul hpz)).norm
  have hfirst : ContinuousOn (fun u =>
      ‖(v u).2 + 2 * (v u).1 * catlinPz p (q u).1‖ / |catlinR p (q u)|) s := by
    exact hfirst_num.div habs (fun u hu => abs_ne_zero.mpr (hRne u hu))
  have hsum : ContinuousOn (fun u =>
      ∑ l ∈ Finset.Icc 2 m,
        Real.rpow (catlinA p l (q u).1 / |catlinR p (q u)|) (1 / (l : ℝ))) s := by
    apply continuousOn_finset_sum
    intro l hl
    have hl2 : 2 ≤ l := (Finset.mem_Icc.mp hl).1
    have hA : ContinuousOn (fun u => catlinA p l (q u).1) s :=
      (continuous_catlinA p hl2).comp_continuousOn hq1
    have hbase : ContinuousOn (fun u => catlinA p l (q u).1 / |catlinR p (q u)|) s :=
      hA.div habs (fun u hu => abs_ne_zero.mpr (hRne u hu))
    have hpow : ContinuousOn (fun u =>
        (catlinA p l (q u).1 / |catlinR p (q u)|) ^ (1 / (l : ℝ))) s := by
      apply ContinuousOn.rpow hbase continuousOn_const
      intro u hu
      right
      have : (0:ℝ) < l := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < (2:ℕ)) hl2)
      positivity
    simpa using hpow
  have hsecond : ContinuousOn (fun u =>
      ‖(v u).1‖ * ∑ l ∈ Finset.Icc 2 m,
        Real.rpow (catlinA p l (q u).1 / |catlinR p (q u)|) (1 / (l : ℝ))) s :=
    hv1.norm.mul hsum
  simpa [catlinM] using hfirst.add hsecond

/- accepted add_to_file helper 12 -/
lemma hasDerivAt_catlinR_comp {p : MvPolynomial (Fin 2) ℂ}
    (hreal : ∀ z : ℂ, (evalDiag z p).im = 0)
    {γ : ℝ → ℂ × ℂ} {v : ℂ × ℂ} {u : ℝ}
    (hγ : HasDerivAt γ v u) :
    HasDerivAt (fun u => catlinR p (γ u))
      ((v.2 + 2 * v.1 * catlinPz p (γ u).1).re) u := by
  have hγ1 : HasDerivAt (fun u => (γ u).1) v.1 u := by
    have h := (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt u hγ
    simpa [Function.comp_def] using h
  have hγ2 : HasDerivAt (fun u => (γ u).2) v.2 u := by
    have h := (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt u hγ
    simpa [Function.comp_def] using h
  have hp := hasDerivAt_evalDiag p hγ1
  have hp' : HasDerivAt (fun u => (evalDiag (γ u).1 p).re)
      ((2 * v.1 * catlinPz p (γ u).1).re) u := by
    have h0 : HasDerivAt (fun u => (evalDiag (γ u).1 p).re)
        ((v.1 * evalDiag (γ u).1 ((MvPolynomial.pderiv (0 : Fin 2)) p) +
          star v.1 * evalDiag (γ u).1 ((MvPolynomial.pderiv (1 : Fin 2)) p)).re) u := by
      have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hp
      simpa [Function.comp_def, Complex.reCLM_apply] using h
    have hre := re_evalDiag_chain (p:=p) hreal (z:=(γ u).1) (v:=v.1)
    have hre' : (v.1 * evalDiag (γ u).1 ((MvPolynomial.pderiv (0 : Fin 2)) p) +
        star v.1 * evalDiag (γ u).1 ((MvPolynomial.pderiv (1 : Fin 2)) p)).re =
        (2 * v.1 * catlinPz p (γ u).1).re := by
      simpa [catlinPz, diagDer] using hre
    rw [hre'] at h0
    exact h0
  have hw : HasDerivAt (fun u => (γ u).2.re) v.2.re u := by
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt u hγ2
    simpa [Function.comp_def, Complex.reCLM_apply] using h
  have hsum := hw.add hp'
  have hder : v.2.re + (2 * v.1 * catlinPz p (γ u).1).re =
      (v.2 + 2 * v.1 * catlinPz p (γ u).1).re := by
    simp [Complex.add_re]
  rw [hder] at hsum
  simpa [catlinR, catlinP] using hsum

/- accepted add_to_file helper 13 -/
lemma catlinM_first_le (m : ℕ) (p : MvPolynomial (Fin 2) ℂ) (q v : ℂ × ℂ) :
    ‖v.2 + 2 * v.1 * catlinPz p q.1‖ / |catlinR p q| ≤ catlinM m p q v := by
  unfold catlinM
  apply le_add_of_nonneg_right
  apply mul_nonneg (norm_nonneg _)
  apply Finset.sum_nonneg
  intro l hl
  apply Real.rpow_nonneg
  exact div_nonneg (catlinA_nonneg p l q.1) (abs_nonneg _)

/- accepted add_to_file helper 14 -/
lemma abs_deriv_log_neg_catlinR_le {m : ℕ} {p : MvPolynomial (Fin 2) ℂ}
    (hreal : ∀ z : ℂ, (evalDiag z p).im = 0)
    {γ : ℝ → ℂ × ℂ} {v : ℂ × ℂ} {u : ℝ}
    (hγ : HasDerivAt γ v u) (hr : catlinR p (γ u) < 0) :
    |deriv (fun u => Real.log (-catlinR p (γ u))) u| ≤
      catlinM m p (γ u) v := by
  let R : ℝ := catlinR p (γ u)
  let X : ℂ := v.2 + 2 * v.1 * catlinPz p (γ u).1
  have hR := hasDerivAt_catlinR_comp (p:=p) hreal hγ
  have hnegR : HasDerivAt (fun u => -catlinR p (γ u)) (-X.re) u := by
    simpa [X] using hR.neg
  have hlog : HasDerivAt (fun u => Real.log (-catlinR p (γ u)))
      ((-X.re) / (-R)) u := by
    apply hnegR.log
    exact ne_of_gt (neg_pos.mpr hr)
  have hder : deriv (fun u => Real.log (-catlinR p (γ u))) u = (-X.re) / (-R) :=
    hlog.deriv
  have habs_eq : |deriv (fun u => Real.log (-catlinR p (γ u))) u| = |X.re| / |R| := by
    rw [hder]
    rw [abs_div]
    simp [R]
  rw [habs_eq]
  have hden : 0 < |R| := abs_pos.mpr (ne_of_lt hr)
  have hre : |X.re| ≤ ‖X‖ := Complex.abs_re_le_norm X
  have hdiv : |X.re| / |R| ≤ ‖X‖ / |R| := div_le_div_of_nonneg_right hre (le_of_lt hden)
  exact hdiv.trans (catlinM_first_le m p (γ u) v)

/- accepted add_to_file helper 15 -/
lemma ae_imp_of_eqOn_Ioo_Ioc {f g : ℝ → ℝ} {a b : ℝ}
    (hfg : Set.EqOn f g (Set.Ioo a b)) :
    ∀ᵐ x ∂MeasureTheory.volume, x ∈ Set.Ioc a b → f x = g x := by
  change MeasureTheory.volume {x | ¬(x ∈ Set.Ioc a b → f x = g x)} = 0
  refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.NoAtoms.measure_singleton b)
  intro x hx
  by_cases hxb : x = b
  · exact hxb
  · exfalso
    rw [Set.mem_setOf_eq, Classical.not_imp] at hx
    have hxlt : x < b := lt_of_le_of_ne hx.1.2 hxb
    exact hx.2 (hfg ⟨hx.1.1,hxlt⟩)

lemma intervalIntegral_congr_of_eqOn_Ioo_of_le {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfg : Set.EqOn f g (Set.Ioo a b)) :
    ∫ x in a..b, f x = ∫ x in a..b, g x := by
  apply intervalIntegral.integral_congr_ae
  have h := ae_imp_of_eqOn_Ioo_Ioc hfg
  filter_upwards [h] with x hx
  intro hxmem
  have hxmem' : x ∈ Set.Ioc a b := by simpa [Set.uIoc, hab] using hxmem
  exact hx hxmem'

/- accepted add_to_file helper 16 -/
lemma intervalIntegrable_of_continuousOn_eqOn_Ioo {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) (hfg : Set.EqOn f g (Set.Ioo a b)) :
    IntervalIntegrable g MeasureTheory.volume a b := by
  have hFIoo : MeasureTheory.IntegrableOn f (Set.Ioo a b) MeasureTheory.volume := by
    have h := hf.integrableOn_Icc (μ:=MeasureTheory.volume)
    exact h.mono_set Set.Ioo_subset_Icc_self
  have hGIoo : MeasureTheory.IntegrableOn g (Set.Ioo a b) MeasureTheory.volume := by
    exact hFIoo.congr (Set.EqOn.aeEq_restrict hfg measurableSet_Ioo)
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mpr hGIoo

/- accepted add_to_file helper 17 -/
lemma eqOn_deriv_derivWithin_Ioo_of_contDiffOn {γ : ℝ → ℂ × ℂ} {a b : ℝ}
    (hab : a < b) (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b)) :
    Set.EqOn (fun u => deriv γ u) (fun u => derivWithin γ (Set.Icc a b) u)
      (Set.Ioo a b) := by
  intro u huI
  have hIcc_nhds : Set.Icc a b ∈ nhds u := Icc_mem_nhds huI.1 huI.2
  have hdiff : DifferentiableWithinAt ℝ γ (Set.Icc a b) u :=
    hγ.differentiableOn (by norm_num) u (Set.Ioo_subset_Icc_self huI)
  have hwithin : HasDerivWithinAt γ (derivWithin γ (Set.Icc a b) u) (Set.Icc a b) u :=
    hdiff.hasDerivWithinAt
  have hat : HasDerivAt γ (derivWithin γ (Set.Icc a b) u) u := hwithin.hasDerivAt hIcc_nhds
  exact hat.deriv

lemma intervalIntegrable_catlinM_deriv_of_contDiffOn {m : ℕ} {p : MvPolynomial (Fin 2) ℂ}
    {γ : ℝ → ℂ × ℂ} {a b : ℝ} (hab : a < b)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b))
    (hr : ∀ u ∈ Set.Icc a b, catlinR p (γ u) < 0) :
    IntervalIntegrable (fun u => catlinM m p (γ u) (deriv γ u))
      MeasureTheory.volume a b := by
  let F : ℝ → ℝ := fun u => catlinM m p (γ u) (derivWithin γ (Set.Icc a b) u)
  have hderiv : ContinuousOn (fun u => derivWithin γ (Set.Icc a b) u) (Set.Icc a b) :=
    hγ.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)
  have hF : ContinuousOn F (Set.Icc a b) := by
    exact continuousOn_catlinM_comp hγ.continuousOn hderiv hr
  have heq : Set.EqOn F (fun u => catlinM m p (γ u) (deriv γ u)) (Set.Ioo a b) := by
    intro u hu
    have hd := eqOn_deriv_derivWithin_Ioo_of_contDiffOn hab hγ hu
    simp [F, hd]
  exact intervalIntegrable_of_continuousOn_eqOn_Ioo (le_of_lt hab) hF heq

/- accepted add_to_file helper 18 -/
lemma contDiff_catlinP (p : MvPolynomial (Fin 2) ℂ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (catlinP p) := by
  exact Complex.reCLM.contDiff.comp (contDiff_evalDiag p)

lemma contDiff_catlinR (p : MvPolynomial (Fin 2) ℂ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (catlinR p) := by
  have h2 : ContDiff ℝ n fun q : ℂ × ℂ => q.2.re :=
    Complex.reCLM.contDiff.comp (ContinuousLinearMap.snd ℝ ℂ ℂ).contDiff
  have h1 : ContDiff ℝ n fun q : ℂ × ℂ => catlinP p q.1 :=
    (contDiff_catlinP p).comp (ContinuousLinearMap.fst ℝ ℂ ℂ).contDiff
  exact h2.add h1

/- accepted add_to_file helper 19 -/
lemma eqOn_deriv_derivWithin_Ioo_of_contDiffOn_generic {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {γ : ℝ → E} {a b : ℝ}
    (hab : a < b) (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b)) :
    Set.EqOn (fun u => deriv γ u) (fun u => derivWithin γ (Set.Icc a b) u)
      (Set.Ioo a b) := by
  intro u huI
  have hIcc_nhds : Set.Icc a b ∈ nhds u := Icc_mem_nhds huI.1 huI.2
  have hdiff : DifferentiableWithinAt ℝ γ (Set.Icc a b) u :=
    hγ.differentiableOn (by norm_num) u (Set.Ioo_subset_Icc_self huI)
  have hwithin : HasDerivWithinAt γ (derivWithin γ (Set.Icc a b) u) (Set.Icc a b) u :=
    hdiff.hasDerivWithinAt
  have hat : HasDerivAt γ (derivWithin γ (Set.Icc a b) u) u := hwithin.hasDerivAt hIcc_nhds
  exact hat.deriv

/- accepted add_to_file helper 20 -/
lemma catlin_segment_log_bound {m : ℕ} {p : MvPolynomial (Fin 2) ℂ}
    (hreal : ∀ z : ℂ, (evalDiag z p).im = 0)
    {γ : ℝ → ℂ × ℂ} {a b : ℝ} (hab : a < b)
    (hγ : ContDiffOn ℝ 1 γ (Set.Icc a b))
    (hr : ∀ u ∈ Set.Icc a b, catlinR p (γ u) < 0) :
    |Real.log (-catlinR p (γ b)) - Real.log (-catlinR p (γ a))| ≤
      ∫ u in a..b, catlinM m p (γ u) (deriv γ u) := by
  let g : ℝ → ℝ := fun u => Real.log (-catlinR p (γ u))
  let Fg : ℝ → ℝ := fun u => |derivWithin g (Set.Icc a b) u|
  let Fm : ℝ → ℝ := fun u => catlinM m p (γ u) (derivWithin γ (Set.Icc a b) u)
  have hRγ : ContDiffOn ℝ 1 (fun u => catlinR p (γ u)) (Set.Icc a b) := by
    exact (contDiff_catlinR p).comp_contDiffOn hγ
  have hg : ContDiffOn ℝ 1 g (Set.Icc a b) := by
    apply ContDiffOn.log hRγ.neg
    intro u hu
    exact ne_of_gt (neg_pos.mpr (hr u hu))
  have hderivg : ContinuousOn (fun u => derivWithin g (Set.Icc a b) u) (Set.Icc a b) :=
    hg.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)
  have hFg : ContinuousOn Fg (Set.Icc a b) := hderivg.norm
  have hderivγ : ContinuousOn (fun u => derivWithin γ (Set.Icc a b) u) (Set.Icc a b) :=
    hγ.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by norm_num)
  have hFm : ContinuousOn Fm (Set.Icc a b) := by
    exact continuousOn_catlinM_comp hγ.continuousOn hderivγ hr
  have hineq_Ioo : ∀ u ∈ Set.Ioo a b, Fg u ≤ Fm u := by
    intro u huI
    have hdg := eqOn_deriv_derivWithin_Ioo_of_contDiffOn_generic (E:=ℝ) hab hg huI
    have hdg' : deriv (fun u => Real.log (-catlinR p (γ u))) u =
        derivWithin (fun u => Real.log (-catlinR p (γ u))) (Set.Icc a b) u := by
      simpa [g] using hdg
    have hdiffγ : DifferentiableWithinAt ℝ γ (Set.Icc a b) u :=
      hγ.differentiableOn (by norm_num) u (Set.Ioo_subset_Icc_self huI)
    have hwithinγ : HasDerivWithinAt γ (derivWithin γ (Set.Icc a b) u) (Set.Icc a b) u :=
      hdiffγ.hasDerivWithinAt
    have hAtγ : HasDerivAt γ (derivWithin γ (Set.Icc a b) u) u :=
      hwithinγ.hasDerivAt (Icc_mem_nhds huI.1 huI.2)
    have hbound := abs_deriv_log_neg_catlinR_le (m:=m) hreal hAtγ
      (hr u (Set.Ioo_subset_Icc_self huI))
    change |derivWithin (fun u => Real.log (-catlinR p (γ u))) (Set.Icc a b) u| ≤
      catlinM m p (γ u) (derivWithin γ (Set.Icc a b) u)
    rw [← hdg']
    exact hbound
  have hineq : ∀ u ∈ Set.Icc a b, Fg u ≤ Fm u := by
    intro u hu
    have hcl : u ∈ closure (Set.Ioo a b) := by
      rw [closure_Ioo (ne_of_lt hab)]
      exact hu
    exact le_on_closure hineq_Ioo (by simpa [closure_Ioo (ne_of_lt hab)] using hFg)
      (by simpa [closure_Ioo (ne_of_lt hab)] using hFm) hcl
  have hFTC : ∫ u in a..b, derivWithin g (Set.Icc a b) u = g b - g a :=
    intervalIntegral.integral_derivWithin_Icc_of_contDiffOn_Icc hg (le_of_lt hab)
  have hnorm : ‖∫ u in a..b, derivWithin g (Set.Icc a b) u‖ ≤
      ∫ u in a..b, ‖derivWithin g (Set.Icc a b) u‖ :=
    intervalIntegral.norm_integral_le_integral_norm (le_of_lt hab)
  have hFgu : ContinuousOn Fg (Set.uIcc a b) := by
    simpa [Set.uIcc, le_of_lt hab] using hFg
  have hFmu : ContinuousOn Fm (Set.uIcc a b) := by
    simpa [Set.uIcc, le_of_lt hab] using hFm
  have hintFg : IntervalIntegrable Fg MeasureTheory.volume a b := hFgu.intervalIntegrable
  have hintFm : IntervalIntegrable Fm MeasureTheory.volume a b := hFmu.intervalIntegrable
  have hint : ∫ u in a..b, Fg u ≤ ∫ u in a..b, Fm u :=
    intervalIntegral.integral_mono_on (le_of_lt hab) hintFg hintFm hineq
  have heqFm : Set.EqOn Fm (fun u => catlinM m p (γ u) (deriv γ u)) (Set.Ioo a b) := by
    intro u hu
    have hdγ := eqOn_deriv_derivWithin_Ioo_of_contDiffOn_generic (E:=ℂ × ℂ) hab hγ hu
    simp [Fm, hdγ]
  have hint_eq : ∫ u in a..b, Fm u =
      ∫ u in a..b, catlinM m p (γ u) (deriv γ u) :=
    intervalIntegral_congr_of_eqOn_Ioo_of_le (le_of_lt hab) heqFm
  have hmain : |g b - g a| ≤ ∫ u in a..b, Fm u := by
    rw [← hFTC]
    have hnorm' : |∫ u in a..b, derivWithin g (Set.Icc a b) u| ≤ ∫ u in a..b, Fg u := by
      simpa [Fg, Real.norm_eq_abs] using hnorm
    exact hnorm'.trans hint
  exact hmain.trans_eq hint_eq

/- accepted add_to_file helper 21 -/
lemma catlin_piecewise_path_log_bound {m : ℕ} {p : MvPolynomial (Fin 2) ℂ}
    (hreal : ∀ z : ℂ, (evalDiag z p).im = 0)
    {γ : ℝ → ℂ × ℂ} (hpc : PiecewiseC1Curve γ)
    (hΩ : ∀ u ∈ Set.Icc (0 : ℝ) 1, catlinR p (γ u) < 0) :
    |Real.log (-catlinR p (γ 1)) - Real.log (-catlinR p (γ 0))| ≤
      ∫ u in (0 : ℝ)..1, catlinM m p (γ u) (deriv γ u) := by
  rcases hpc with ⟨n,u,hu0,hu1,hmono,hseg⟩
  let idx : ℕ → Fin (n + 1) := fun k =>
    ⟨min k n, Nat.lt_succ_of_le (min_le_right k n)⟩
  let a : ℕ → ℝ := fun k => u (idx k)
  let g : ℝ → ℝ := fun u => Real.log (-catlinR p (γ u))
  let F : ℕ → ℝ := fun k => g (a k)
  have ha0 : a 0 = 0 := by
    simp [a, idx, hu0]
  have han : a n = 1 := by
    have hid : idx n = ⟨n, Nat.lt_add_one n⟩ := by
      ext
      simp [idx]
    simp [a, hid, hu1]
  have hF0 : F 0 = g 0 := by
    simp [F, ha0]
  have hFn : F n = g 1 := by
    simp [F, han]
  have htele : |F n - F 0| ≤ ∑ k ∈ Finset.range n, |F (k+1) - F k| := by
    rw [← Finset.sum_range_sub F n]
    exact IsAbsoluteValue.abv_sum abs (fun k => F (k+1)-F k) (Finset.range n)
  have hsegbound : ∀ k ∈ Finset.range n,
      |F (k+1)-F k| ≤ ∫ x in a k..a (k+1), catlinM m p (γ x) (deriv γ x) := by
    intro k hk
    have hkn : k < n := Finset.mem_range.mp hk
    let i : Fin n := ⟨k,hkn⟩
    have ha : a k = u i.castSucc := by
      apply congrArg u
      ext
      simp [idx, i, hkn.le]
    have hb : a (k+1) = u i.succ := by
      apply congrArg u
      ext
      simp [idx, i, hkn]
    have hab : u i.castSucc < u i.succ := hmono Fin.castSucc_lt_succ
    have hrseg : ∀ x ∈ Set.Icc (u i.castSucc) (u i.succ), catlinR p (γ x) < 0 := by
      intro x hx
      have h0a : (0:ℝ) ≤ u i.castSucc := by
        have hm := hmono.monotone (Fin.zero_le i.castSucc)
        simpa [hu0] using hm
      have hb1 : u i.succ ≤ 1 := by
        have hm := hmono.monotone (Fin.le_last i.succ)
        have hid : (Fin.last n : Fin (n+1)) = ⟨n, Nat.lt_add_one n⟩ := by ext; rfl
        simpa [hid, hu1] using hm
      exact hΩ x ⟨h0a.trans hx.1, hx.2.trans hb1⟩
    have hbnd := catlin_segment_log_bound (m:=m) hreal hab (hseg i) hrseg
    have hFk : F k = g (u i.castSucc) := by
      simp [F, ha]
    have hFk1 : F (k+1) = g (u i.succ) := by
      simp [F, hb]
    rw [hFk, hFk1, ha, hb]
    simpa [g] using hbnd
  have hint : ∀ k < n,
      IntervalIntegrable (fun x => catlinM m p (γ x) (deriv γ x))
        MeasureTheory.volume (a k) (a (k+1)) := by
    intro k hkn
    let i : Fin n := ⟨k,hkn⟩
    have ha : a k = u i.castSucc := by
      apply congrArg u
      ext
      simp [idx, i, hkn.le]
    have hb : a (k+1) = u i.succ := by
      apply congrArg u
      ext
      simp [idx, i, hkn]
    have hab : u i.castSucc < u i.succ := hmono Fin.castSucc_lt_succ
    have hrseg : ∀ x ∈ Set.Icc (u i.castSucc) (u i.succ), catlinR p (γ x) < 0 := by
      intro x hx
      have h0a : (0:ℝ) ≤ u i.castSucc := by
        have hm := hmono.monotone (Fin.zero_le i.castSucc)
        simpa [hu0] using hm
      have hb1 : u i.succ ≤ 1 := by
        have hm := hmono.monotone (Fin.le_last i.succ)
        have hid : (Fin.last n : Fin (n+1)) = ⟨n, Nat.lt_add_one n⟩ := by ext; rfl
        simpa [hid, hu1] using hm
      exact hΩ x ⟨h0a.trans hx.1, hx.2.trans hb1⟩
    have hi := intervalIntegrable_catlinM_deriv_of_contDiffOn (m:=m) (p:=p) hab (hseg i) hrseg
    simpa [ha, hb] using hi
  have hsumint := intervalIntegral.sum_integral_adjacent_intervals
    (f:=fun x => catlinM m p (γ x) (deriv γ x)) (a:=a) (n:=n) hint
  have hsum_abs : |F n-F 0| ≤
      ∑ k ∈ Finset.range n, ∫ x in a k..a (k+1), catlinM m p (γ x) (deriv γ x) := by
    exact htele.trans (Finset.sum_le_sum hsegbound)
  rw [hsumint, ha0, han] at hsum_abs
  simpa [hF0, hFn, g] using hsum_abs

/- accepted add_to_file helper 22 -/
lemma setIntegral_Icc_zero_one_eq_intervalIntegral (f : ℝ → ℝ) :
    ∫ u in Set.Icc (0 : ℝ) 1, f u = ∫ u in (0 : ℝ)..1, f u := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact (intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)).symm

/- accepted add_to_file helper 23 -/
lemma deriv_vertical_second (w₀ : ℂ) (a s c u : ℝ) :
    deriv (fun x : ℝ => w₀ - ((a * Real.exp (-(s+c*x)) : ℝ) : ℂ)) u =
      (((a*c*Real.exp (-(s+c*u)) : ℝ) : ℂ)) := by
  have hlin : HasDerivAt (fun x : ℝ => s+c*x) c u := by
    simpa using ((hasDerivAt_id u).const_mul c).const_add s
  have harg : HasDerivAt (fun x : ℝ => -(s+c*x)) (-c) u := hlin.neg
  have he : HasDerivAt (fun x : ℝ => Real.exp (-(s+c*x)))
    (Real.exp (-(s+c*u)) * (-c)) u := by
    exact (Real.hasDerivAt_exp (-(s+c*u))).comp u harg
  have hm : HasDerivAt (fun x : ℝ => a * Real.exp (-(s+c*x)))
    (a * (Real.exp (-(s+c*u)) * (-c))) u := he.const_mul a
  have hc := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt u hm)
  have hsub := (hasDerivAt_const u w₀).sub hc
  have hfun : ((fun _ : ℝ => w₀) - Complex.ofRealCLM ∘ fun x : ℝ => a * Real.exp (-(s+c*x))) =
      (fun x : ℝ => w₀ - ((a * Real.exp (-(s+c*x)) : ℝ) : ℂ)) := by
    ext x
    rfl
  rw [hfun] at hsub
  rw [hsub.deriv]
  simp
  ring

/- accepted add_to_file helper 24 -/
lemma contDiff_vertical_curve (z₀ w₀ : ℂ) (a s c : ℝ) :
    ContDiff ℝ 1 (fun u : ℝ =>
      (z₀, w₀ - ((a * Real.exp (-(s + c * u)) : ℝ) : ℂ))) := by
  have h1 : ContDiff ℝ 1 (fun u : ℝ => a * Real.exp (-(s+c*u))) := by
    fun_prop
  exact contDiff_const.prodMk (contDiff_const.sub (Complex.ofRealCLM.contDiff.comp h1))

/- accepted add_to_file helper 25 -/
lemma contDiff_vertical_second (w₀ : ℂ) (a s c : ℝ) :
    ContDiff ℝ 1 (fun u : ℝ => w₀ - ((a * Real.exp (-(s+c*u)) : ℝ) : ℂ)) := by
  have h1 : ContDiff ℝ 1 (fun u : ℝ => a * Real.exp (-(s+c*u))) := by
    fun_prop
  exact contDiff_const.sub (Complex.ofRealCLM.contDiff.comp h1)

lemma hasDerivAt_vertical_curve (z₀ w₀ : ℂ) (a s c u : ℝ) :
    HasDerivAt (fun x : ℝ =>
      (z₀, w₀ - ((a * Real.exp (-(s+c*x)) : ℝ) : ℂ)))
      (0, (((a*c*Real.exp (-(s+c*u)) : ℝ) : ℂ))) u := by
  have hdiff := ((contDiff_vertical_second w₀ a s c).differentiable (by norm_num)) u
  have hsecond := hdiff.hasDerivAt
  rw [deriv_vertical_second w₀ a s c u] at hsecond
  exact (hasDerivAt_const u z₀).prodMk hsecond

/- accepted add_to_file helper 26 -/
lemma catlinM_vertical {m : ℕ} {p : MvPolynomial (Fin 2) ℂ} {q : ℂ × ℂ}
    {a c e : ℝ} (ha : 0 < a) (he : 0 < e)
    (hr : catlinR p q = -a*e) :
    catlinM m p q (0, (((a*c*e:ℝ) : ℂ))) = |c| := by
  have hpos : 0 < a*e := mul_pos ha he
  unfold catlinM
  rw [hr]
  simp [hpos.ne', abs_of_pos hpos]
  field_simp [hpos.ne']
  rw [abs_of_pos ha, abs_of_pos he]
  ring

/- accepted add_to_file helper 27 -/
lemma catlinR_vertical {p : MvPolynomial (Fin 2) ℂ} {z₀ w₀ : ℂ} {a t : ℝ}
    (hb : catlinR p (z₀,w₀) = 0) :
    catlinR p (z₀, w₀ - ((a * Real.exp (-t) : ℝ) : ℂ)) =
      -a * Real.exp (-t) := by
  have hb' : w₀.re + catlinP p z₀ = 0 := by
    simpa [catlinR] using hb
  have h : (Complex.exp (-(t : ℂ))).re = Real.exp (-t) := by
    rw [show -(t : ℂ) = (↑(-t) : ℂ) by simp, Complex.exp_ofReal_re]
  simp [catlinR, h]
  nlinarith

/- accepted add_to_file helper 28 -/
lemma log_neg_catlinR_vertical {p : MvPolynomial (Fin 2) ℂ} {z₀ w₀ : ℂ} {a t : ℝ}
    (ha : 0 < a) (hb : catlinR p (z₀,w₀) = 0) :
    Real.log (-catlinR p (z₀, w₀ - ((a * Real.exp (-t) : ℝ) : ℂ))) =
      Real.log a - t := by
  rw [catlinR_vertical hb]
  have hae : a * Real.exp (-t) ≠ 0 := by
    exact mul_ne_zero (ne_of_gt ha) (ne_of_gt (Real.exp_pos _))
  rw [show -(-a * Real.exp (-t)) = a * Real.exp (-t) by ring]
  rw [Real.log_mul (ne_of_gt ha) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
  ring

/- accepted add_to_file helper 29 -/
lemma vertical_catlin_length {m : ℕ} {p : MvPolynomial (Fin 2) ℂ} {z₀ w₀ : ℂ}
    {a s t : ℝ} (ha : 0 < a) (hb : catlinR p (z₀,w₀) = 0) :
    ∫ u in Set.Icc (0 : ℝ) 1,
      catlinM m p
        ((z₀, w₀ - ((a * Real.exp (-(s + (t-s)*u)) : ℝ) : ℂ)))
        (deriv (fun x : ℝ =>
          (z₀, w₀ - ((a * Real.exp (-(s + (t-s)*x)) : ℝ) : ℂ))) u) = |s-t| := by
  have hpoint : ∀ u : ℝ,
      catlinM m p
        ((z₀, w₀ - ((a * Real.exp (-(s + (t-s)*u)) : ℝ) : ℂ)))
        (deriv (fun x : ℝ =>
          (z₀, w₀ - ((a * Real.exp (-(s + (t-s)*x)) : ℝ) : ℂ))) u) = |t-s| := by
    intro u
    have hd := (hasDerivAt_vertical_curve z₀ w₀ a s (t-s) u).deriv
    have hr := catlinR_vertical (p:=p) (z₀:=z₀) (w₀:=w₀) (a:=a) (t:=s+(t-s)*u) hb
    have hm := catlinM_vertical (m:=m) (p:=p)
      (q:=(z₀, w₀ - ((a * Real.exp (-(s+(t-s)*u)) : ℝ) : ℂ)))
      (a:=a) (c:=t-s) (e:=Real.exp (-(s+(t-s)*u))) ha (Real.exp_pos _) hr
    rw [hd]
    exact hm
  rw [setIntegral_Icc_zero_one_eq_intervalIntegral]
  have hc : ∫ u in (0:ℝ)..1,
      catlinM m p
        ((z₀, w₀ - ((a * Real.exp (-(s + (t-s)*u)) : ℝ) : ℂ)))
        (deriv (fun x : ℝ =>
          (z₀, w₀ - ((a * Real.exp (-(s + (t-s)*x)) : ℝ) : ℂ))) u)
      = ∫ _ in (0:ℝ)..1, |t-s| :=
    intervalIntegral.integral_congr (fun u hu => hpoint u)
  rw [hc]
  rw [intervalIntegral.integral_const]
  simp [abs_sub_comm]

/- verified submission -/
theorem catlin_vertical_curve_is_geodesic
    (m : ℕ) (p : MvPolynomial (Fin 2) ℂ) :
    let evalAt : ℂ → MvPolynomial (Fin 2) ℂ → ℂ :=
      fun z q => MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z else star z) q
    let D : ℕ → ℕ → ℂ → ℂ := fun j k z =>
      evalAt z ((MvPolynomial.pderiv (1 : Fin 2))^[k]
        ((MvPolynomial.pderiv (0 : Fin 2))^[j] p))
    let P : ℂ → ℝ := fun z => (evalAt z p).re
    let Pz : ℂ → ℂ := fun z => D 1 0 z
    let A : ℕ → ℂ → ℝ := fun l z =>
      sSup {u : ℝ | ∃ j k : ℕ, 0 < j ∧ 0 < k ∧ j + k = l ∧ u = ‖D j k z‖}
    let r : ℂ × ℂ → ℝ := fun q => q.2.re + P q.1
    let Ω : Set (ℂ × ℂ) := {q | r q < 0}
    let M : (ℂ × ℂ) → (ℂ × ℂ) → ℝ := fun q v =>
      ‖v.2 + 2 * v.1 * Pz q.1‖ / |r q| +
        ‖v.1‖ * ∑ l ∈ Finset.Icc 2 m,
          Real.rpow (A l q.1 / |r q|) (1 / (l : ℝ))
    let PiecewiseC1 : (ℝ → ℂ × ℂ) → Prop := fun γ =>
      ∃ n : ℕ, ∃ u : Fin (n + 1) → ℝ,
        u 0 = 0 ∧ u ⟨n, Nat.lt_add_one n⟩ = 1 ∧ StrictMono u ∧
          ∀ i : Fin n,
            ContDiffOn ℝ 1 γ (Set.Icc (u i.castSucc) (u i.succ))
    let d : (ℂ × ℂ) → (ℂ × ℂ) → ℝ := fun q₁ q₂ =>
      sInf {L : ℝ | ∃ γ : ℝ → ℂ × ℂ,
        PiecewiseC1 γ ∧
        γ 0 = q₁ ∧ γ 1 = q₂ ∧
        (∀ u ∈ Set.Icc (0 : ℝ) 1, γ u ∈ Ω) ∧
        L = ∫ u in Set.Icc (0 : ℝ) 1, M (γ u) (deriv γ u)}
    2 ≤ m →
    p.totalDegree = m →
    (∀ z : ℂ, (evalAt z p).im = 0) →
    P 0 = 0 →
    (∀ z : ℂ, 0 ≤ (D 1 1 z).re) →
    (∀ j : ℕ, 0 < j → p.coeff (Finsupp.single (0 : Fin 2) j) = 0) →
    (∀ k : ℕ, 0 < k → p.coeff (Finsupp.single (1 : Fin 2) k) = 0) →
    ∀ (z₀ w₀ : ℂ) (a : ℝ),
      0 < a →
      (z₀, w₀) ∈ frontier Ω →
      let σ : ℝ → ℂ × ℂ := fun t =>
        (z₀, w₀ - ((a * Real.exp (-t) : ℝ) : ℂ))
      (∀ t : ℝ, σ t ∈ Ω) ∧
        ∀ s t : ℝ, d (σ s) (σ t) = |s - t| := by
  intro evalAt D P Pz A r Ω M PiecewiseC1 d hm hdeg hreal hP0 hsub hpurez hpurebar
  intro z₀ w₀ a ha hfront σ
  have heval : evalAt = evalDiag := rfl
  have hD : D = diagDer p := rfl
  have hP : P = catlinP p := rfl
  have hPz : Pz = catlinPz p := rfl
  have hA : A = catlinA p := rfl
  have hr : r = catlinR p := rfl
  have hM : M = catlinM m p := rfl
  have hPC : PiecewiseC1 = PiecewiseC1Curve := rfl
  have hrealG : ∀ z : ℂ, (evalDiag z p).im = 0 := by
    intro z
    rw [← heval]
    exact hreal z
  have hΩdef : Ω = {q | catlinR p q < 0} := by
    ext q
    change (r q < 0) ↔ (catlinR p q < 0)
    rw [hr]
  have hb : catlinR p (z₀,w₀) = 0 :=
    frontier_sublevel_eq_zero (continuous_catlinR p) hΩdef hfront
  constructor
  · intro t
    show catlinR p (σ t) < 0
    dsimp [σ]
    rw [catlinR_vertical hb]
    have hpos : 0 < a * Real.exp (-t) := mul_pos ha (Real.exp_pos _)
    linarith
  · intro s t
    let S : Set ℝ := {L : ℝ | ∃ γ : ℝ → ℂ × ℂ,
      PiecewiseC1 γ ∧
      γ 0 = σ s ∧ γ 1 = σ t ∧
      (∀ u ∈ Set.Icc (0 : ℝ) 1, γ u ∈ Ω) ∧
      L = ∫ u in Set.Icc (0 : ℝ) 1, M (γ u) (deriv γ u)}
    have hd : d (σ s) (σ t) = sInf S := rfl
    let γ : ℝ → ℂ × ℂ := fun u =>
      (z₀, w₀ - ((a * Real.exp (-(s + (t-s)*u)) : ℝ) : ℂ))
    have hγpc : PiecewiseC1Curve γ :=
      PiecewiseC1Curve_single (contDiff_vertical_curve z₀ w₀ a s (t-s))
    have hγ0 : γ 0 = σ s := by
      simp [γ, σ]
    have hγ1 : γ 1 = σ t := by
      dsimp [γ, σ]
      ext
      · rfl
      · congr 1
        congr 1
        congr 1
        ring
    have hγΩ : ∀ u ∈ Set.Icc (0 : ℝ) 1, γ u ∈ Ω := by
      intro u hu
      show catlinR p (γ u) < 0
      dsimp [γ]
      rw [catlinR_vertical hb]
      have hpos : 0 < a * Real.exp (-(s+(t-s)*u)) :=
        mul_pos ha (Real.exp_pos _)
      linarith
    have hγlen : |s-t| = ∫ u in Set.Icc (0 : ℝ) 1, M (γ u) (deriv γ u) := by
      rw [hM]
      exact (vertical_catlin_length (m:=m) (p:=p) (z₀:=z₀) (w₀:=w₀) (a:=a) (s:=s) (t:=t) ha hb).symm
    have hnonempty : S.Nonempty := by
      refine ⟨|s-t|, γ, ?_, hγ0, hγ1, hγΩ, hγlen⟩
      simpa [hPC] using hγpc
    have hbdd : BddBelow S := by
      refine ⟨0, ?_⟩
      rintro L ⟨δ,hδpc,hδ0,hδ1,hδΩ,hL⟩
      rw [hL, hM]
      apply MeasureTheory.integral_nonneg
      intro u
      exact catlinM_nonneg m p (δ u) (deriv δ u)
    have hlower : ∀ L ∈ S, |s-t| ≤ L := by
      rintro L ⟨δ,hδpc,hδ0,hδ1,hδΩ,hL⟩
      have hδpcG : PiecewiseC1Curve δ := by
        simpa [hPC] using hδpc
      have hδΩG : ∀ u ∈ Set.Icc (0 : ℝ) 1, catlinR p (δ u) < 0 := by
        intro u hu
        have huΩ := hδΩ u hu
        rwa [hΩdef] at huΩ
      have hbound := catlin_piecewise_path_log_bound (m:=m) (p:=p) hrealG hδpcG hδΩG
      rw [hδ0, hδ1] at hbound
      have hlogdiff :
          |Real.log (-catlinR p (σ t)) - Real.log (-catlinR p (σ s))| = |s-t| := by
        dsimp [σ]
        rw [log_neg_catlinR_vertical ha hb, log_neg_catlinR_vertical ha hb]
        have h : Real.log a - t - (Real.log a - s) = s-t := by ring
        rw [h]
      rw [hlogdiff] at hbound
      rw [hL, hM, setIntegral_Icc_zero_one_eq_intervalIntegral]
      exact hbound
    have hle : |s-t| ≤ sInf S := le_csInf hnonempty hlower
    have hge : sInf S ≤ |s-t| := csInf_le hbdd (by
      refine ⟨γ, ?_, hγ0, hγ1, hγΩ, hγlen⟩
      simpa [hPC] using hγpc)
    rw [hd]
    exact le_antisymm hge hle

end
end Rollout_p0912_catlin_vertical_curve_is_geodesic

#check_dependency_graph "Rollout_p0912_catlin_vertical_curve_is_geodesic.catlin_vertical_curve_is_geodesic" against "{\"edges\":[{\"conclusion\":{\"name\":\"heval\",\"statement\":\"evalAt = Rollout_p0912_catlin_vertical_curve_is_geodesic.evalDiag\"},\"graphEdgeId\":\"h_001_heval\",\"premises\":[],\"rawEdgeId\":\"telescope_25\"},{\"conclusion\":{\"name\":\"hr\",\"statement\":\"r = Rollout_p0912_catlin_vertical_curve_is_geodesic.catlinR p\"},\"graphEdgeId\":\"h_006_hr\",\"premises\":[],\"rawEdgeId\":\"telescope_30\"},{\"conclusion\":{\"name\":\"hM\",\"statement\":\"M = Rollout_p0912_catlin_vertical_curve_is_geodesic.catlinM m p\"},\"graphEdgeId\":\"h_007_hm\",\"premises\":[],\"rawEdgeId\":\"telescope_31\"},{\"conclusion\":{\"name\":\"hPC\",\"statement\":\"PiecewiseC1 = Rollout_p0912_catlin_vertical_curve_is_geodesic.PiecewiseC1Curve\"},\"graphEdgeId\":\"h_008_hpc\",\"premises\":[],\"rawEdgeId\":\"telescope_32\"},{\"conclusion\":{\"name\":\"hrealG\",\"statement\":\"∀ (z : ℂ), (Rollout_p0912_catlin_vertical_curve_is_geodesic.evalDiag z p).im = 0\"},\"graphEdgeId\":\"h_009_hrealg\",\"premises\":[{\"name\":\"hreal\",\"statement\":\"∀ (z : ℂ), (evalAt z p).im = 0\"},{\"name\":\"heval\",\"statement\":\"evalAt = Rollout_p0912_catlin_vertical_curve_is_geodesic.evalDiag\"}],\"rawEdgeId\":\"telescope_33\"},{\"conclusion\":{\"name\":\"hΩdef\",\"statement\":\"Ω = {q | Rollout_p0912_catlin_vertical_curve_is_geodesic.catlinR p q < 0}\"},\"graphEdgeId\":\"h_010_h_def\",\"premises\":[{\"name\":\"hr\",\"statement\":\"r = Rollout_p0912_catlin_vertical_curve_is_geodesic.catlinR p\"}],\"rawEdgeId\":\"telescope_34\"},{\"conclusion\":{\"name\":\"hb\",\"statement\":\"Rollout_p0912_catlin_vertical_curve_is_geodesic.catlinR p (z₀, w₀) = 0\"},\"graphEdgeId\":\"h_011_hb\",\"premises\":[{\"name\":\"hfront\",\"statement\":\"(z₀, w₀) ∈ frontier Ω\"},{\"name\":\"hΩdef\",\"statement\":\"Ω = {q | Rollout_p0912_catlin_vertical_curve_is_geodesic.catlinR p q < 0}\"}],\"rawEdgeId\":\"telescope_35\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(∀ (t : ℝ), σ t ∈ Ω) ∧ ∀ (s t : ℝ), d (σ s) (σ t) = |s - t|\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"ha\",\"statement\":\"0 < a\"},{\"name\":\"hM\",\"statement\":\"M = Rollout_p0912_catlin_vertical_curve_is_geodesic.catlinM m p\"},{\"name\":\"hPC\",\"statement\":\"PiecewiseC1 = Rollout_p0912_catlin_vertical_curve_is_geodesic.PiecewiseC1Curve\"},{\"name\":\"hrealG\",\"statement\":\"∀ (z : ℂ), (Rollout_p0912_catlin_vertical_curve_is_geodesic.evalDiag z p).im = 0\"},{\"name\":\"hΩdef\",\"statement\":\"Ω = {q | Rollout_p0912_catlin_vertical_curve_is_geodesic.catlinR p q < 0}\"},{\"name\":\"hb\",\"statement\":\"Rollout_p0912_catlin_vertical_curve_is_geodesic.catlinR p (z₀, w₀) = 0\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0912_catlin_vertical_curve_is_geodesic\",\"reconstructedProofSha256\":\"cc6d4973114cc0c7a9784655505a6f48359de722e3a69ec905f1f7d26470c626\",\"selectedEdgeCount\":8,\"theoremName\":\"Rollout_p0912_catlin_vertical_curve_is_geodesic.catlin_vertical_curve_is_geodesic\",\"topologySha256\":\"ff55e243bcb013b3bb1fe2d4b53943a217b77c71844ab85c4d3c84a7f12cdfd5\"}"

namespace Rollout_p0968_unique_nonzero_zero_of_exponential_factori

-- graph_id: p0968_unique_nonzero_zero_of_exponential_factori
-- topology_sha256: d4ca74383152f0bfeefc3bc82eda301a06f7f3b5f660876d151afe5a084e3479
/- accepted add_to_file helper 1 -/
noncomputable def Ftrunc (n : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    (-1 : ℝ) ^ (n - j) * ((n.factorial : ℝ) / (j.factorial : ℝ)) * t ^ j

lemma Ftrunc_shift_term_eq_neg (n i : ℕ) (hi : i < n) (t : ℝ) :
    (-1 : ℝ) ^ (n - (i + 1)) * ((n.factorial : ℝ) / ((i + 1).factorial : ℝ)) *
        ((i + 1 : ℝ) * t ^ i)
      =
    - ((-1 : ℝ) ^ (n - i) * ((n.factorial : ℝ) / (i.factorial : ℝ)) * t ^ i) := by
  have hfact : ((i + 1).factorial : ℝ) = (i + 1 : ℝ) * (i.factorial : ℝ) := by
    norm_num [Nat.factorial_succ]
  have hsub : n - (i + 1) + 1 = n - i := by omega
  have hpow : (-1 : ℝ) ^ (n - i) = - (-1 : ℝ) ^ (n - (i + 1)) := by
    rw [← hsub]
    rw [pow_succ]
    ring
  rw [hfact, hpow]
  field_simp

lemma Ftrunc_deriv_eq_neg_sum (n : ℕ) (t : ℝ) :
    deriv (Ftrunc n) t =
      - ∑ i ∈ Finset.range n,
        (-1 : ℝ) ^ (n - i) * ((n.factorial : ℝ) / (i.factorial : ℝ)) * t ^ i := by
  unfold Ftrunc
  rw [deriv_fun_sum]
  · rw [Finset.sum_range_succ']
    simp
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    exact Ftrunc_shift_term_eq_neg n i hi' t
  · intro i hi
    fun_prop

lemma Ftrunc_add_deriv (n : ℕ) (t : ℝ) :
    Ftrunc n t + deriv (Ftrunc n) t = t ^ n := by
  rw [Ftrunc_deriv_eq_neg_sum]
  unfold Ftrunc
  rw [Finset.sum_range_succ]
  simp
  field_simp

/- accepted add_to_file helper 2 -/
lemma Ftrunc_differentiableAt (n : ℕ) (t : ℝ) : DifferentiableAt ℝ (Ftrunc n) t := by
  unfold Ftrunc
  fun_prop

lemma hasDerivAt_exp_mul_Ftrunc (n : ℕ) (t : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Real.exp t * Ftrunc n t) (Real.exp t * t ^ n) t := by
  have hF := (Ftrunc_differentiableAt n t).hasDerivAt
  have h := (Real.hasDerivAt_exp t).mul hF
  convert h using 1
  rw [← Ftrunc_add_deriv]
  ring

lemma Ftrunc_integral (n : ℕ) (a b : ℝ) :
    ∫ t in a..b, Real.exp t * t ^ n =
      Real.exp b * Ftrunc n b - Real.exp a * Ftrunc n a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    exact hasDerivAt_exp_mul_Ftrunc n x
  · exact (Real.continuous_exp.mul (continuous_pow n)).intervalIntegrable a b

/- accepted add_to_file helper 3 -/
noncomputable def Porig (n : ℕ) (a x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    (-1 : ℝ) ^ (n - j) * ((n.factorial : ℝ) / (j.factorial : ℝ)) *
      a ^ ((j : ℤ) - 1) * (a - (j : ℝ)) * x ^ j

lemma Porig_succ_term (n i : ℕ) (a x : ℝ) :
    (-1 : ℝ) ^ (n - (i + 1)) * ((n.factorial : ℝ) / ((i + 1).factorial : ℝ)) *
        a ^ (((i + 1 : ℕ) : ℤ) - 1) * (a - ((i + 1 : ℕ) : ℝ)) * x ^ (i + 1)
      =
    (-1 : ℝ) ^ (n - (i + 1)) * ((n.factorial : ℝ) / ((i + 1).factorial : ℝ)) *
        (a * x) ^ (i + 1)
      -
      x * ((-1 : ℝ) ^ (n - (i + 1)) * ((n.factorial : ℝ) / (i.factorial : ℝ)) *
        (a * x) ^ i) := by
  have hz : a ^ (((i + 1 : ℕ) : ℤ) - 1) = a ^ i := by
    norm_num
  rw [hz]
  have hfact : ((i + 1).factorial : ℝ) = (i + 1 : ℝ) * (i.factorial : ℝ) := by
    norm_num [Nat.factorial_succ]
  rw [hfact]
  field_simp
  norm_num
  ring

lemma Porig_D_eq_neg_Fterm (n i : ℕ) (hi : i < n) (a x : ℝ) :
    (-1 : ℝ) ^ (n - (i + 1)) * ((n.factorial : ℝ) / (i.factorial : ℝ)) *
        (a * x) ^ i
      =
    - ((-1 : ℝ) ^ (n - i) * ((n.factorial : ℝ) / (i.factorial : ℝ)) * (a * x) ^ i) := by
  have hsub : n - (i + 1) + 1 = n - i := by omega
  have hpow : (-1 : ℝ) ^ (n - i) = - (-1 : ℝ) ^ (n - (i + 1)) := by
    rw [← hsub]
    rw [pow_succ]
    ring
  rw [hpow]
  ring

/- accepted add_to_file helper 4 -/
lemma Porig_eq (n : ℕ) {a x : ℝ} (ha : a ≠ 0) :
    Porig n a x = (1 + x) * Ftrunc n (a * x) - x * (a * x) ^ n := by
  classical
  let D : ℕ → ℝ := fun i ↦
    (-1 : ℝ) ^ (n - (i + 1)) * ((n.factorial : ℝ) / (i.factorial : ℝ)) * (a * x) ^ i
  have hdecomp : Porig n a x = Ftrunc n (a * x) - x * ∑ i ∈ Finset.range n, D i := by
    unfold Porig Ftrunc
    rw [Finset.sum_range_succ']
    rw [Finset.sum_range_succ']
    have hzero :
        (-1 : ℝ) ^ (n - 0) * ((n.factorial : ℝ) / (((0 : ℕ).factorial : ℝ))) *
          a ^ (((0 : ℕ) : ℤ) - 1) * (a - ((0 : ℕ) : ℝ)) * x ^ 0
        = (-1 : ℝ) ^ n * (n.factorial : ℝ) := by
      norm_num [zpow_neg_one, ha]
    rw [hzero]
    have hsum := Finset.sum_congr (rfl : Finset.range n = Finset.range n)
      (fun i hi ↦ Porig_succ_term n i a x)
    rw [hsum]
    rw [Finset.sum_sub_distrib]
    rw [← Finset.mul_sum]
    dsimp [D]
    norm_num
    ring
  rw [hdecomp]
  have hD :
      ∑ i ∈ Finset.range n, D i =
        - ∑ i ∈ Finset.range n,
          (-1 : ℝ) ^ (n - i) * ((n.factorial : ℝ) / (i.factorial : ℝ)) * (a * x) ^ i := by
    dsimp [D]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact Porig_D_eq_neg_Fterm n i (Finset.mem_range.mp hi) a x
  rw [hD]
  unfold Ftrunc
  rw [Finset.sum_range_succ]
  field_simp
  simp
  ring_nf

/- accepted add_to_file helper 5 -/
lemma exp_pow_endpoint_integral (n : ℕ) (x a b : ℝ) :
    ∫ u in b..a, Real.exp (x * u) * (x * u ^ n + (n : ℝ) * u ^ (n - 1)) =
      Real.exp (x * a) * a ^ n - Real.exp (x * b) * b ^ n := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    have hexp : HasDerivAt (fun u : ℝ ↦ Real.exp (x * u)) (x * Real.exp (x * u)) u := by
      have h := (Real.hasDerivAt_exp (x * u)).comp u ((hasDerivAt_id u).const_mul x)
      simpa [mul_assoc, mul_comm, mul_left_comm] using h
    have hpow : HasDerivAt (fun u : ℝ ↦ u ^ n) ((n : ℝ) * u ^ (n - 1)) u := by
      simpa using hasDerivAt_pow n u
    have h := hexp.mul hpow
    convert h using 1
    ring
  · have hc : Continuous fun u : ℝ ↦ Real.exp (x * u) * (x * u ^ n + (n : ℝ) * u ^ (n - 1)) := by
      continuity
    exact hc.intervalIntegrable b a

/- accepted add_to_file helper 6 -/
lemma exp_Ftrunc_diff (n : ℕ) (x a b : ℝ) :
    Real.exp ((a - b) * x) * Ftrunc n (a * x) - Ftrunc n (b * x)
      =
    Real.exp (-(b * x)) *
      ∫ s in b * x..a * x, Real.exp s * s ^ n := by
  have hmul : Real.exp (-(b * x)) * Real.exp (a * x) = Real.exp ((a - b) * x) := by
    rw [← Real.exp_add]
    ring_nf
  have hone : Real.exp (-(b * x)) * Real.exp (b * x) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    Real.exp ((a - b) * x) * Ftrunc n (a * x) - Ftrunc n (b * x)
        = Real.exp (-(b * x)) *
            (Real.exp (a * x) * Ftrunc n (a * x) - Real.exp (b * x) * Ftrunc n (b * x)) := by
          rw [mul_sub]
          congr 1
          · calc
              Real.exp ((a - b) * x) * Ftrunc n (a * x)
                  = (Real.exp (-(b * x)) * Real.exp (a * x)) * Ftrunc n (a * x) := by
                    rw [hmul]
              _ = Real.exp (-(b * x)) * (Real.exp (a * x) * Ftrunc n (a * x)) := by
                    ring
          · calc
              Ftrunc n (b * x)
                  = (Real.exp (-(b * x)) * Real.exp (b * x)) * Ftrunc n (b * x) := by
                    rw [hone]
                    simp
              _ = Real.exp (-(b * x)) * (Real.exp (b * x) * Ftrunc n (b * x)) := by
                    ring
    _ = Real.exp (-(b * x)) *
          ∫ s in b * x..a * x, Real.exp s * s ^ n := by
          rw [Ftrunc_integral]

/- accepted add_to_file helper 7 -/
lemma scaled_exp_pow_integral (n : ℕ) {x a b : ℝ} (hx : x ≠ 0) :
    ∫ s in b * x..a * x, Real.exp s * s ^ n =
      x ^ (n + 1) * ∫ u in b..a, Real.exp (x * u) * u ^ n := by
  have hcomp :
      ∫ u in b..a, Real.exp (x * u) * (x * u) ^ n =
        x⁻¹ * ∫ s in x * b..x * a, Real.exp s * s ^ n := by
    simpa using intervalIntegral.integral_comp_mul_left
      (fun s : ℝ ↦ Real.exp s * s ^ n) hx (a := b) (b := a)
  have hI :
      ∫ s in x * b..x * a, Real.exp s * s ^ n =
        x * ∫ u in b..a, Real.exp (x * u) * (x * u) ^ n := by
    rw [hcomp]
    field_simp [hx]
  have hcongr :
      ∫ u in b..a, Real.exp (x * u) * (x * u) ^ n =
        x ^ n * ∫ u in b..a, Real.exp (x * u) * u ^ n := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    ring
  rw [show b * x = x * b by ring, show a * x = x * a by ring]
  rw [hI, hcongr]
  ring

/- accepted add_to_file helper 8 -/
lemma exp_sub_factor (x a b A B : ℝ) :
    Real.exp ((a - b) * x) * A - B =
      Real.exp (-(b * x)) * (Real.exp (x * a) * A - Real.exp (x * b) * B) := by
  have hmul : Real.exp (-(b * x)) * Real.exp (x * a) = Real.exp ((a - b) * x) := by
    rw [← Real.exp_add]
    ring_nf
  have hone : Real.exp (-(b * x)) * Real.exp (x * b) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  rw [mul_sub]
  congr 1
  · calc
      Real.exp ((a - b) * x) * A
          = (Real.exp (-(b * x)) * Real.exp (x * a)) * A := by rw [hmul]
      _ = Real.exp (-(b * x)) * (Real.exp (x * a) * A) := by ring
  · calc
      B = (Real.exp (-(b * x)) * Real.exp (x * b)) * B := by
        rw [hone]
        simp
      _ = Real.exp (-(b * x)) * (Real.exp (x * b) * B) := by ring

lemma exp_pow_endpoint_diff (n : ℕ) (x a b : ℝ) :
    Real.exp ((a - b) * x) * a ^ n - b ^ n =
      Real.exp (-(b * x)) *
        ∫ u in b..a, Real.exp (x * u) * (x * u ^ n + (n : ℝ) * u ^ (n - 1)) := by
  rw [exp_sub_factor, exp_pow_endpoint_integral]

/- accepted add_to_file helper 9 -/
lemma combine_exp_integrals (n : ℕ) (hn : 1 ≤ n) (x a b : ℝ) :
    (1 + x) * (∫ u in b..a, Real.exp (x * u) * u ^ n)
      - (∫ u in b..a, Real.exp (x * u) * (x * u ^ n + (n : ℝ) * u ^ (n - 1)))
    =
    ∫ u in b..a, Real.exp (x * u) * u ^ (n - 1) * (u - (n : ℝ)) := by
  have hA : IntervalIntegrable (fun u : ℝ ↦ Real.exp (x * u) * u ^ n)
      MeasureTheory.volume b a := by
    have hc : Continuous fun u : ℝ ↦ Real.exp (x * u) * u ^ n := by continuity
    exact hc.intervalIntegrable b a
  have hB : IntervalIntegrable
      (fun u : ℝ ↦ Real.exp (x * u) * (x * u ^ n + (n : ℝ) * u ^ (n - 1)))
      MeasureTheory.volume b a := by
    have hc : Continuous fun u : ℝ ↦ Real.exp (x * u) * (x * u ^ n + (n : ℝ) * u ^ (n - 1)) := by
      continuity
    exact hc.intervalIntegrable b a
  rw [← intervalIntegral.integral_const_mul]
  rw [← intervalIntegral.integral_sub (hA.const_mul (1 + x)) hB]
  apply intervalIntegral.integral_congr
  intro u hu
  cases n with
  | zero => omega
  | succ m =>
      have hm : m + 1 - 1 = m := by omega
      rw [hm]
      ring

/- accepted add_to_file helper 10 -/
noncomputable def Hdiff (n : ℕ) (x a b : ℝ) : ℝ :=
  Real.exp ((a - b) * x) * Porig n a x - Porig n b x

noncomputable def Kbase (n : ℕ) (a b x : ℝ) : ℝ :=
  ∫ u in b..a, Real.exp (x * u) * u ^ (n - 1) * (u - (n : ℝ))

lemma Hdiff_eq_of_ne (n : ℕ) (hn : 1 ≤ n) {x a b : ℝ} (hx : x ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Hdiff n x a b = Real.exp (-(b * x)) * x ^ (n + 1) * Kbase n a b x := by
  unfold Hdiff Kbase
  rw [Porig_eq n ha, Porig_eq n hb]
  have hcalc :
      Real.exp ((a - b) * x) * ((1 + x) * Ftrunc n (a * x) - x * (a * x) ^ n) -
          ((1 + x) * Ftrunc n (b * x) - x * (b * x) ^ n)
      =
      (1 + x) * (Real.exp ((a - b) * x) * Ftrunc n (a * x) - Ftrunc n (b * x))
        - x ^ (n + 1) * (Real.exp ((a - b) * x) * a ^ n - b ^ n) := by
    ring
  rw [hcalc]
  rw [exp_Ftrunc_diff]
  rw [scaled_exp_pow_integral n hx]
  rw [exp_pow_endpoint_diff]
  have hcombine := combine_exp_integrals n hn x a b
  rw [← hcombine]
  ring

lemma Hdiff_zero (n : ℕ) {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Hdiff n 0 a b = 0 := by
  unfold Hdiff
  rw [Porig_eq n ha, Porig_eq n hb]
  simp

lemma Hdiff_eq (n : ℕ) (hn : 1 ≤ n) (x a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Hdiff n x a b = Real.exp (-(b * x)) * x ^ (n + 1) * Kbase n a b x := by
  by_cases hx : x = 0
  · subst x
    rw [Hdiff_zero n ha hb]
    have hnp : n + 1 ≠ 0 := by omega
    simp [hnp]
  · exact Hdiff_eq_of_ne n hn hx ha hb

/- accepted add_to_file helper 11 -/
noncomputable def Kcenter (n k : ℕ) (x : ℝ) : ℝ :=
  ∫ v in -(k : ℝ)..(k : ℝ),
    Real.exp (x * v) * ((n : ℝ) + v) ^ (n - 1) * v

lemma Kbase_eq_exp_mul_Kcenter (n k : ℕ) (x : ℝ) :
    Kbase n ((n : ℝ) + (k : ℝ)) ((n : ℝ) - (k : ℝ)) x =
      Real.exp ((n : ℝ) * x) * Kcenter n k x := by
  unfold Kbase Kcenter
  have hshift :
      ∫ v in -(k : ℝ)..(k : ℝ),
          Real.exp (x * v) * ((n : ℝ) + v) ^ (n - 1) * v
        =
      ∫ u in (n : ℝ) - (k : ℝ)..(n : ℝ) + (k : ℝ),
        Real.exp (x * (u - (n : ℝ))) * u ^ (n - 1) * (u - (n : ℝ)) := by
    have h := intervalIntegral.integral_comp_add_left
      (fun u : ℝ ↦ Real.exp (x * (u - (n : ℝ))) * u ^ (n - 1) * (u - (n : ℝ)))
      (n : ℝ) (a := -(k : ℝ)) (b := (k : ℝ))
    simpa [sub_eq_add_neg] using h
  rw [hshift]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u hu
  dsimp
  have hexp : Real.exp (x * u) = Real.exp ((n : ℝ) * x) * Real.exp (x * (u - (n : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  ring

/- accepted add_to_file helper 12 -/
lemma Hdiff_eq_center (n k : ℕ) (hn : 2 ≤ n) (hk₂ : k ≤ n - 1) (x : ℝ) :
    Hdiff n x ((n : ℝ) + (k : ℝ)) ((n : ℝ) - (k : ℝ)) =
      Real.exp ((k : ℝ) * x) * x ^ (n + 1) * Kcenter n k x := by
  have hn1 : 1 ≤ n := by omega
  have hkn : k < n := by omega
  have ha : ((n : ℝ) + (k : ℝ)) ≠ 0 := by
    have : 0 < (n : ℝ) + (k : ℝ) := by positivity
    exact ne_of_gt this
  have hb : ((n : ℝ) - (k : ℝ)) ≠ 0 := by
    have hcastlt : (k : ℝ) < (n : ℝ) := by exact_mod_cast hkn
    have : 0 < (n : ℝ) - (k : ℝ) := sub_pos.mpr hcastlt
    exact ne_of_gt this
  rw [Hdiff_eq n hn1 x _ _ ha hb]
  rw [Kbase_eq_exp_mul_Kcenter]
  have hexp : Real.exp (-(((n : ℝ) - (k : ℝ)) * x)) * Real.exp ((n : ℝ) * x)
      = Real.exp ((k : ℝ) * x) := by
    rw [← Real.exp_add]
    congr 1
    have hknle : k ≤ n := by omega
    have hcast : ((n - k : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) := by
      exact Nat.cast_sub hknle
    have hknr : ((k : ℝ) + ((n : ℝ) - (k : ℝ))) = (n : ℝ) := by
      rw [← hcast]
      have : k + (n - k) = n := by omega
      exact_mod_cast this
    nlinarith
  rw [show Real.exp (-(((n : ℝ) - (k : ℝ)) * x)) * x ^ (n + 1) *
        (Real.exp ((n : ℝ) * x) * Kcenter n k x)
      =
      (Real.exp (-(((n : ℝ) - (k : ℝ)) * x)) * Real.exp ((n : ℝ) * x)) *
        x ^ (n + 1) * Kcenter n k x by ring]
  rw [hexp]

/- accepted add_to_file helper 13 -/
lemma Kcenter_strictMono {n k : ℕ} (hn : 2 ≤ n) (hk₁ : 1 ≤ k)
    (hk₂ : k ≤ n - 1) :
    StrictMono (Kcenter n k) := by
  intro x y hxy
  let g : ℝ → ℝ := fun v ↦
    (Real.exp (y * v) - Real.exp (x * v)) * ((n : ℝ) + v) ^ (n - 1) * v
  have hdiff :
      Kcenter n k y - Kcenter n k x =
        ∫ v in -(k : ℝ)..(k : ℝ), g v := by
    unfold Kcenter
    dsimp [g]
    have hf : IntervalIntegrable
        (fun v : ℝ ↦ Real.exp (y * v) * ((n : ℝ) + v) ^ (n - 1) * v)
        MeasureTheory.volume (-(k : ℝ)) (k : ℝ) := by
      have hc : Continuous fun v : ℝ ↦ Real.exp (y * v) * ((n : ℝ) + v) ^ (n - 1) * v := by
        continuity
      exact hc.intervalIntegrable _ _
    have hg : IntervalIntegrable
        (fun v : ℝ ↦ Real.exp (x * v) * ((n : ℝ) + v) ^ (n - 1) * v)
        MeasureTheory.volume (-(k : ℝ)) (k : ℝ) := by
      have hc : Continuous fun v : ℝ ↦ Real.exp (x * v) * ((n : ℝ) + v) ^ (n - 1) * v := by
        continuity
      exact hc.intervalIntegrable _ _
    rw [← intervalIntegral.integral_sub hf hg]
    apply intervalIntegral.integral_congr
    intro v hv
    ring
  have hpos : 0 < ∫ v in -(k : ℝ)..(k : ℝ), g v := by
    apply intervalIntegral.integral_pos
    · have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk₁
      linarith
    · have hc : Continuous g := by
        dsimp [g]
        continuity
      exact hc.continuousOn
    · intro v hv
      dsimp [g]
      have hvge : -(k : ℝ) ≤ v := hv.1.le
      have hvle : v ≤ (k : ℝ) := hv.2
      have hnv : 0 ≤ ((n : ℝ) + v) ^ (n - 1) := by
        have hklt : (k : ℝ) < (n : ℝ) := by
          have hkn : k < n := by omega
          exact_mod_cast hkn
        have hbase : 0 < (n : ℝ) + v := by nlinarith
        exact pow_nonneg hbase.le _
      by_cases hv0 : 0 ≤ v
      · have hexp : 0 ≤ Real.exp (y * v) - Real.exp (x * v) := by
          have : x * v ≤ y * v := mul_le_mul_of_nonneg_right hxy.le hv0
          exact sub_nonneg.mpr (Real.exp_le_exp.mpr this)
        exact mul_nonneg (mul_nonneg hexp hnv) hv0
      · have hv0' : v ≤ 0 := le_of_not_ge hv0
        have hexp : Real.exp (y * v) - Real.exp (x * v) ≤ 0 := by
          have : y * v ≤ x * v := mul_le_mul_of_nonpos_right hxy.le hv0'
          exact sub_nonpos.mpr (Real.exp_le_exp.mpr this)
        have hprod : (Real.exp (y * v) - Real.exp (x * v)) * ((n : ℝ) + v) ^ (n - 1) ≤ 0 := by
          exact mul_nonpos_of_nonpos_of_nonneg hexp hnv
        exact mul_nonneg_of_nonpos_of_nonpos hprod hv0'
    · use 1
      constructor
      · constructor
        · have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk₁
          linarith
        · exact_mod_cast hk₁
      · dsimp [g]
        have hexp : 0 < Real.exp y - Real.exp x := by
          exact sub_pos.mpr (Real.exp_lt_exp.mpr hxy)
        have hpow : 0 < ((n : ℝ) + (1 : ℝ)) ^ (n - 1) := by
          have hb : 0 < (n : ℝ) + 1 := by positivity
          exact pow_pos hb _
        have hprod := mul_pos (mul_pos hexp hpow) (by norm_num : (0 : ℝ) < 1)
        simpa [mul_assoc] using hprod
  rw [← hdiff] at hpos
  linarith

/- accepted add_to_file helper 14 -/
lemma Kcenter_pair (n k : ℕ) (x : ℝ) :
    Kcenter n k x =
      ∫ v in (0 : ℝ)..(k : ℝ),
        v * (((n : ℝ) + v) ^ (n - 1) * Real.exp (x * v)
          - ((n : ℝ) - v) ^ (n - 1) * Real.exp (-(x * v))) := by
  let f : ℝ → ℝ := fun v ↦ Real.exp (x * v) * ((n : ℝ) + v) ^ (n - 1) * v
  have hcont : Continuous f := by
    dsimp [f]
    continuity
  have hneg :
      ∫ v in (0 : ℝ)..(k : ℝ), f (-v) =
        ∫ v in -(k : ℝ)..(0 : ℝ), f v := by
    simpa using intervalIntegral.integral_comp_neg f (a := (0 : ℝ)) (b := (k : ℝ))
  have hsplit :
      (∫ v in -(k : ℝ)..(0 : ℝ), f v) + (∫ v in (0 : ℝ)..(k : ℝ), f v) =
        ∫ v in -(k : ℝ)..(k : ℝ), f v := by
    simpa using
      (intervalIntegral.integral_add_adjacent_intervals
        (a := -(k : ℝ)) (b := (0 : ℝ)) (c := (k : ℝ)) (μ := MeasureTheory.volume)
        (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _))
  unfold Kcenter
  change ∫ v in -(k : ℝ)..(k : ℝ), f v = _
  calc
    ∫ v in -(k : ℝ)..(k : ℝ), f v
        = (∫ v in -(k : ℝ)..(0 : ℝ), f v) + (∫ v in (0 : ℝ)..(k : ℝ), f v) := hsplit.symm
    _ = (∫ v in (0 : ℝ)..(k : ℝ), f (-v)) + (∫ v in (0 : ℝ)..(k : ℝ), f v) := by
          exact congrArg (fun z ↦ z + (∫ v in (0 : ℝ)..(k : ℝ), f v)) hneg.symm
    _ = ∫ v in (0 : ℝ)..(k : ℝ),
          v * (((n : ℝ) + v) ^ (n - 1) * Real.exp (x * v)
            - ((n : ℝ) - v) ^ (n - 1) * Real.exp (-(x * v))) := by
          have hi : IntervalIntegrable (fun v : ℝ ↦ f (-v)) MeasureTheory.volume 0 (k : ℝ) := by
            exact (hcont.comp continuous_neg).intervalIntegrable _ _
          have hp : IntervalIntegrable f MeasureTheory.volume 0 (k : ℝ) := by
            exact hcont.intervalIntegrable _ _
          have hcongr :
              ∫ v in (0 : ℝ)..(k : ℝ),
                  v * (((n : ℝ) + v) ^ (n - 1) * Real.exp (x * v)
                    - ((n : ℝ) - v) ^ (n - 1) * Real.exp (-(x * v)))
                =
              ∫ v in (0 : ℝ)..(k : ℝ), f (-v) + f v := by
            apply intervalIntegral.integral_congr
            intro v hv
            dsimp [f]
            have hnegexp : x * -v = -(x * v) := by ring
            rw [hnegexp]
            ring
          rw [hcongr]
          exact (intervalIntegral.integral_add hi hp).symm

/- accepted add_to_file helper 15 -/
lemma Kcenter_zero_pos {n k : ℕ} (hn : 2 ≤ n) (hk₁ : 1 ≤ k)
    (hk₂ : k ≤ n - 1) : 0 < Kcenter n k 0 := by
  rw [Kcenter_pair]
  simp
  apply intervalIntegral.integral_pos
  · have : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk₁
    exact this
  · have hc : Continuous fun v : ℝ ↦
        v * (((n : ℝ) + v) ^ (n - 1) - ((n : ℝ) - v) ^ (n - 1)) := by
      continuity
    exact hc.continuousOn
  · intro v hv
    have hv0 : 0 ≤ v := hv.1.le
    have hvle : v ≤ (k : ℝ) := hv.2
    have hkn : (k : ℝ) < (n : ℝ) := by
      have : k < n := by omega
      exact_mod_cast this
    have hb1 : 0 ≤ (n : ℝ) - v := by nlinarith
    have hb2 : (n : ℝ) - v ≤ (n : ℝ) + v := by nlinarith
    have hpow := pow_le_pow_left₀ hb1 hb2 (n - 1)
    exact mul_nonneg hv0 (sub_nonneg.mpr hpow)
  · use 1
    constructor
    · constructor
      · norm_num
      · exact_mod_cast hk₁
    · have hkn : (k : ℝ) < (n : ℝ) := by
        have : k < n := by omega
        exact_mod_cast this
      have hb : 0 ≤ (n : ℝ) - 1 := by
        have h1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk₁
        nlinarith
      have hbase : (n : ℝ) - 1 < (n : ℝ) + 1 := by nlinarith
      have hexp : n - 1 ≠ 0 := by omega
      have hpow : ((n : ℝ) - 1) ^ (n - 1) < ((n : ℝ) + 1) ^ (n - 1) :=
        pow_lt_pow_left₀ hbase hb hexp
      have hbr : 0 < ((n : ℝ) + 1) ^ (n - 1) - ((n : ℝ) - 1) ^ (n - 1) :=
        sub_pos.mpr hpow
      exact mul_pos (by norm_num : (0 : ℝ) < 1) hbr

/- accepted add_to_file helper 16 -/
lemma neg_exp_weight_integral (n : ℕ) (hn : 1 ≤ n) (a b : ℝ) :
    ∫ u in b..a, Real.exp (-u) * u ^ (n - 1) * (u - (n : ℝ)) =
      Real.exp (-b) * b ^ n - Real.exp (-a) * a ^ n := by
  have hderiv :
      ∀ u ∈ Set.uIcc b a,
        HasDerivAt (fun u : ℝ ↦ Real.exp (-u) * u ^ n)
          (-(Real.exp (-u) * u ^ (n - 1) * (u - (n : ℝ)))) u := by
    intro u hu
    have hexp : HasDerivAt (fun u : ℝ ↦ Real.exp (-u)) (-Real.exp (-u)) u := by
      have h := (Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_id u).neg
      simpa using h
    have hpow : HasDerivAt (fun u : ℝ ↦ u ^ n) ((n : ℝ) * u ^ (n - 1)) u := by
      simpa using hasDerivAt_pow n u
    have h := hexp.mul hpow
    convert h using 1
    cases n with
    | zero => omega
    | succ m =>
        have hm : m + 1 - 1 = m := by omega
        rw [hm]
        ring
  have hint : IntervalIntegrable
      (fun u : ℝ ↦ -(Real.exp (-u) * u ^ (n - 1) * (u - (n : ℝ))))
      MeasureTheory.volume b a := by
    have hc : Continuous fun u : ℝ ↦ -(Real.exp (-u) * u ^ (n - 1) * (u - (n : ℝ))) := by
      continuity
    exact hc.intervalIntegrable b a
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have htarget :
      ∫ u in b..a, Real.exp (-u) * u ^ (n - 1) * (u - (n : ℝ))
        =
      -(∫ u in b..a, -(Real.exp (-u) * u ^ (n - 1) * (u - (n : ℝ)))) := by
    rw [← intervalIntegral.integral_neg]
    simp
  rw [htarget, hI]
  ring

/- accepted add_to_file helper 17 -/
lemma endpoint_log_ratio {n k : ℕ} (hk₁ : 1 ≤ k) (hk₂ : k ≤ n - 1) :
    2 * (k : ℝ) / (n : ℝ) <
      Real.log (((n : ℝ) + (k : ℝ)) / ((n : ℝ) - (k : ℝ))) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hbpos : (0 : ℝ) < (n : ℝ) - (k : ℝ) := by
    have hkn : k < n := by omega
    have : (k : ℝ) < (n : ℝ) := by exact_mod_cast hkn
    exact sub_pos.mpr this
  let t : ℝ := 2 * (k : ℝ) / ((n : ℝ) - (k : ℝ))
  have htpos : 0 < t := by
    dsimp [t]
    positivity
  have hbound := Real.lt_log_one_add_of_pos htpos
  have harg : 1 + t = ((n : ℝ) + (k : ℝ)) / ((n : ℝ) - (k : ℝ)) := by
    dsimp [t]
    field_simp [ne_of_gt hbpos]
    ring
  have hleft : 2 * t / (t + 2) = 2 * (k : ℝ) / (n : ℝ) := by
    dsimp [t]
    field_simp [ne_of_gt hbpos, ne_of_gt hnpos]
    ring
  rw [harg, hleft] at hbound
  exact hbound

/- accepted add_to_file helper 18 -/
lemma endpoint_exp_pow_lt {n k : ℕ} (hk₁ : 1 ≤ k) (hk₂ : k ≤ n - 1) :
    Real.exp (-((n : ℝ) - (k : ℝ))) * ((n : ℝ) - (k : ℝ)) ^ n <
      Real.exp (-((n : ℝ) + (k : ℝ))) * ((n : ℝ) + (k : ℝ)) ^ n := by
  let N : ℝ := n
  let K : ℝ := k
  let B : ℝ := N - K
  let A : ℝ := N + K
  have hN : 0 < N := by
    dsimp [N]
    have : 0 < n := by omega
    exact_mod_cast this
  have hB : 0 < B := by
    dsimp [B, N, K]
    have hkn : k < n := by omega
    have : (k : ℝ) < (n : ℝ) := by exact_mod_cast hkn
    exact sub_pos.mpr this
  have hA : 0 < A := by positivity
  have hleftpos : 0 < Real.exp (-B) * B ^ n := by positivity
  have hrightpos : 0 < Real.exp (-A) * A ^ n := by positivity
  have hlog : Real.log (Real.exp (-B) * B ^ n) <
      Real.log (Real.exp (-A) * A ^ n) := by
    have hleftlog : Real.log (Real.exp (-B) * B ^ n) = -B + N * Real.log B := by
      rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt (pow_pos hB n))]
      rw [Real.log_exp, Real.log_pow]
    have hrightlog : Real.log (Real.exp (-A) * A ^ n) = -A + N * Real.log A := by
      rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt (pow_pos hA n))]
      rw [Real.log_exp, Real.log_pow]
    rw [hleftlog, hrightlog]
    have hratio : 2 * K / N < Real.log (A / B) := by
      dsimp [A, B, N, K]
      exact endpoint_log_ratio hk₁ hk₂
    have hmul := mul_lt_mul_of_pos_left hratio hN
    have htwo : N * (2 * K / N) = 2 * K := by
      field_simp [ne_of_gt hN]
    have hlogdiv : Real.log (A / B) = Real.log A - Real.log B := by
      exact Real.log_div (ne_of_gt hA) (ne_of_gt hB)
    have hdiff : A - B = 2 * K := by
      dsimp [A, B]
      ring
    rw [htwo] at hmul
    rw [hlogdiv] at hmul
    nlinarith
  exact (Real.log_lt_log_iff hleftpos hrightpos).mp hlog

/- accepted add_to_file helper 19 -/
lemma Kcenter_neg_one_neg {n k : ℕ} (hn : 2 ≤ n) (hk₁ : 1 ≤ k)
    (hk₂ : k ≤ n - 1) : Kcenter n k (-1) < 0 := by
  have hn1 : 1 ≤ n := by omega
  let A : ℝ := (n : ℝ) + (k : ℝ)
  let B : ℝ := (n : ℝ) - (k : ℝ)
  have hbaseeq : Kbase n A B (-1) =
      Real.exp (-B) * B ^ n - Real.exp (-A) * A ^ n := by
    unfold Kbase
    dsimp [A, B]
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (neg_exp_weight_integral n hn1 ((n : ℝ) + (k : ℝ)) ((n : ℝ) - (k : ℝ)))
  have hbaseneg : Kbase n A B (-1) < 0 := by
    rw [hbaseeq]
    have h := endpoint_exp_pow_lt hk₁ hk₂
    dsimp [A, B]
    exact sub_neg.mpr h
  have hrel := Kbase_eq_exp_mul_Kcenter n k (-1)
  dsimp [A, B] at hbaseeq hbaseneg
  have hrel' : Kbase n ((n : ℝ) + (k : ℝ)) ((n : ℝ) - (k : ℝ)) (-1) =
      Real.exp (-(n : ℝ)) * Kcenter n k (-1) := by
    simpa using hrel
  have hK : Kcenter n k (-1) =
      Real.exp (n : ℝ) * Kbase n ((n : ℝ) + (k : ℝ)) ((n : ℝ) - (k : ℝ)) (-1) := by
    calc
      Kcenter n k (-1)
          = Real.exp (n : ℝ) * (Real.exp (-(n : ℝ)) * Kcenter n k (-1)) := by
            have hone : Real.exp (n : ℝ) * Real.exp (-(n : ℝ)) = 1 := by
              rw [← Real.exp_add]
              simp
            rw [show Real.exp (n : ℝ) * (Real.exp (-(n : ℝ)) * Kcenter n k (-1))
                = (Real.exp (n : ℝ) * Real.exp (-(n : ℝ))) * Kcenter n k (-1) by ring]
            rw [hone]
            simp
      _ = Real.exp (n : ℝ) * Kbase n ((n : ℝ) + (k : ℝ)) ((n : ℝ) - (k : ℝ)) (-1) := by
            rw [← hrel']
  rw [hK]
  exact mul_neg_of_pos_of_neg (Real.exp_pos _) hbaseneg

/- accepted add_to_file helper 20 -/
lemma Kcenter_continuous (n k : ℕ) : Continuous (Kcenter n k) := by
  unfold Kcenter
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have hf : Continuous fun p : ℝ × ℝ ↦
      Real.exp (p.1 * p.2) * ((n : ℝ) + p.2) ^ (n - 1) * p.2 := by
    continuity
  exact hf

lemma exists_Kcenter_root {n k : ℕ} (hn : 2 ≤ n) (hk₁ : 1 ≤ k)
    (hk₂ : k ≤ n - 1) :
    ∃ c : ℝ, -1 < c ∧ c < 0 ∧ Kcenter n k c = 0 := by
  have hcont : ContinuousOn (Kcenter n k) (Set.Icc (-1 : ℝ) 0) :=
    (Kcenter_continuous n k).continuousOn
  have hivt := intermediate_value_Ioo (by norm_num : (-1 : ℝ) ≤ 0) hcont
  have hzero_mem : (0 : ℝ) ∈ Set.Ioo (Kcenter n k (-1)) (Kcenter n k 0) := by
    exact ⟨Kcenter_neg_one_neg hn hk₁ hk₂, Kcenter_zero_pos hn hk₁ hk₂⟩
  have himage := hivt hzero_mem
  rcases himage with ⟨c, hc, hfc⟩
  exact ⟨c, hc.1, hc.2, hfc⟩

/- accepted add_to_file helper 21 -/
noncomputable def Hformal (n k : ℕ) (x : ℝ) : ℝ :=
  Real.exp (2 * (k : ℝ) * x) *
      Porig n ((n : ℝ) + (k : ℝ)) x
    - Porig n ((n : ℝ) - (k : ℝ)) x

lemma Hformal_eq_Hdiff (n k : ℕ) (x : ℝ) :
    Hformal n k x =
      Hdiff n x ((n : ℝ) + (k : ℝ)) ((n : ℝ) - (k : ℝ)) := by
  unfold Hformal Hdiff
  congr 1
  congr 1
  ring

lemma Hformal_eq_factor (n k : ℕ) (hn : 2 ≤ n) (hk₂ : k ≤ n - 1) (x : ℝ) :
    Hformal n k x =
      Real.exp ((k : ℝ) * x) * x ^ (n + 1) * Kcenter n k x := by
  rw [Hformal_eq_Hdiff]
  exact Hdiff_eq_center n k hn hk₂ x

/- verified submission -/
theorem unique_nonzero_zero_of_exponential_factorial_sum
    (n k : ℕ) (hn : 2 ≤ n) (hk₁ : 1 ≤ k) (hk₂ : k ≤ n - 1) :
    let h : ℝ → ℝ := fun x ↦
      Real.exp (2 * (k : ℝ) * x) *
          (∑ j ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ (n - j) *
              ((n.factorial : ℝ) / (j.factorial : ℝ)) *
              ((n : ℝ) + (k : ℝ)) ^ ((j : ℤ) - 1) *
              ((n : ℝ) + (k : ℝ) - (j : ℝ)) * x ^ j)
        - (∑ j ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ (n - j) *
              ((n.factorial : ℝ) / (j.factorial : ℝ)) *
              ((n : ℝ) - (k : ℝ)) ^ ((j : ℤ) - 1) *
              ((n : ℝ) - (k : ℝ) - (j : ℝ)) * x ^ j)
    ∃ c : ℝ, -1 < c ∧ c < 0 ∧ h c = 0 ∧
      ∀ x : ℝ, h x = 0 ↔ x = 0 ∨ x = c := by
  dsimp
  rcases exists_Kcenter_root hn hk₁ hk₂ with ⟨c, hcneg, hcneg0, hcK⟩
  refine ⟨c, hcneg, hcneg0, ?_, ?_⟩
  · show Hformal n k c = 0
    rw [Hformal_eq_factor n k hn hk₂ c, hcK]
    simp
  · intro x
    show Hformal n k x = 0 ↔ x = 0 ∨ x = c
    rw [Hformal_eq_factor n k hn hk₂ x]
    constructor
    · intro hz
      have hz' := (mul_eq_zero.mp hz)
      rcases hz' with hz' | hz'
      · have hxp := (mul_eq_zero.mp hz')
        rcases hxp with hexp | hxp
        · exact False.elim ((ne_of_gt (Real.exp_pos _)) hexp)
        · left
          exact eq_zero_of_pow_eq_zero hxp
      · right
        have hEq : Kcenter n k x = Kcenter n k c := by
          rw [hz', hcK]
        exact (Kcenter_strictMono hn hk₁ hk₂).injective hEq
    · intro hxc
      rcases hxc with rfl | rfl
      · simp
      · rw [hcK]
        simp

end Rollout_p0968_unique_nonzero_zero_of_exponential_factori

#check_dependency_graph "Rollout_p0968_unique_nonzero_zero_of_exponential_factori.unique_nonzero_zero_of_exponential_factorial_sum" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let h := fun x => Real.exp (2 * ↑k * x) * ∑ j ∈ Finset.range (n + 1), (-1) ^ (n - j) * (↑n.factorial / ↑j.factorial) * (↑n + ↑k) ^ (↑j - 1) * (↑n + ↑k - ↑j) * x ^ j - ∑ j ∈ Finset.range (n + 1), (-1) ^ (n - j) * (↑n.factorial / ↑j.factorial) * (↑n - ↑k) ^ (↑j - 1) * (↑n - ↑k - ↑j) * x ^ j; ∃ c, -1 < c ∧ c < 0 ∧ h c = 0 ∧ ∀ (x : ℝ), h x = 0 ↔ x = 0 ∨ x = c\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hn\",\"statement\":\"2 ≤ n\"},{\"name\":\"hk₁\",\"statement\":\"1 ≤ k\"},{\"name\":\"hk₂\",\"statement\":\"k ≤ n - 1\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0968_unique_nonzero_zero_of_exponential_factori\",\"reconstructedProofSha256\":\"bf8a4a32dc8d93f9d5c451210c6638eff106fdeaeea22a88064cfad84dd73581\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p0968_unique_nonzero_zero_of_exponential_factori.unique_nonzero_zero_of_exponential_factorial_sum\",\"topologySha256\":\"d4ca74383152f0bfeefc3bc82eda301a06f7f3b5f660876d151afe5a084e3479\"}"

namespace Rollout_p0971_derivwithin_neg_of_positive_solution

-- graph_id: p0971_derivwithin_neg_of_positive_solution
-- topology_sha256: 253a8736d821304a70bd1dc324f603e5e16229c1ee25c0de4161930c7617de03
/- accepted add_to_file helper 1 -/
lemma signed_ppower_neg_iff (p s : ℝ) :
    (if s = 0 then 0 else Real.rpow |s| (p - 2) * s) < 0 ↔ s < 0 := by
  by_cases hs : s = 0
  · simp [hs]
  · have habs : 0 < |s| := abs_pos.mpr hs
    have hr : 0 < Real.rpow |s| (p - 2) := Real.rpow_pos_of_pos habs _
    simp [hs]
    constructor
    · intro h
      have hmul := mul_neg_iff.mp h
      rcases hmul with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
      · exact hright
      · exact False.elim ((not_lt_of_ge hr.le) hleft)
    · intro h
      exact mul_neg_of_pos_of_neg hr h

lemma signed_ppower_pos_iff (p s : ℝ) :
    0 < (if s = 0 then 0 else Real.rpow |s| (p - 2) * s) ↔ 0 < s := by
  by_cases hs : s = 0
  · simp [hs]
  · have habs : 0 < |s| := abs_pos.mpr hs
    have hr : 0 < Real.rpow |s| (p - 2) := Real.rpow_pos_of_pos habs _
    simp [hs]
    constructor
    · intro h
      have hmul := mul_pos_iff.mp h
      rcases hmul with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
      · exact hright
      · exact False.elim ((not_lt_of_ge hr.le) hleft)
    · intro h
      exact mul_pos hr h

/- verified submission -/
theorem derivWithin_neg_of_positive_solution
    (n : ℕ) (β p lam : ℝ) (f T : ℝ → ℝ)
    (hn : 2 ≤ n) (hβ : 0 < β) (hp : 1 < p) (hlam : 0 < lam)
    (hf : ContDiffOn ℝ 2 f (Set.Icc 0 β))
    (hf0 : f 0 = 0)
    (hf'0 : derivWithin f (Set.Icc 0 β) 0 = 1)
    (hfpos : ∀ t ∈ Set.Ioc 0 β, 0 < f t)
    (hT : ContDiffOn ℝ 1 T (Set.Icc 0 β)) :
    let ψ : ℝ → ℝ := fun s =>
      if s = 0 then 0 else Real.rpow |s| (p - 2) * s
    let Φ : ℝ → ℝ := fun t =>
      f t ^ (n - 1) * ψ (derivWithin T (Set.Icc 0 β) t)
    ContDiffOn ℝ 1 Φ (Set.Icc 0 β) →
      (∀ t ∈ Set.Ioo 0 β,
        deriv Φ t + lam * f t ^ (n - 1) * ψ (T t) = 0) →
      (∀ t ∈ Set.Ioo 0 β, 0 < T t) →
      ∀ t ∈ Set.Ioc 0 β, derivWithin T (Set.Icc 0 β) t < 0 := by
  intro ψ Φ hΦ hODE hTpos
  have hψneg_iff : ∀ s : ℝ, ψ s < 0 ↔ s < 0 := by
    intro s
    simpa [ψ] using signed_ppower_neg_iff p s
  have hψpos_iff : ∀ s : ℝ, 0 < ψ s ↔ 0 < s := by
    intro s
    simpa [ψ] using signed_ppower_pos_iff p s
  have hderivneg : ∀ t ∈ interior (Set.Icc 0 β), deriv Φ t < 0 := by
    rw [interior_Icc]
    intro t ht
    have hf_t : 0 < f t := hfpos t ⟨ht.1, le_of_lt ht.2⟩
    have hpow : 0 < f t ^ (n - 1) := pow_pos hf_t _
    have hψT : 0 < ψ (T t) := (hψpos_iff (T t)).mpr (hTpos t ht)
    have hflux : 0 < lam * f t ^ (n - 1) * ψ (T t) :=
      mul_pos (mul_pos hlam hpow) hψT
    have heq := hODE t ht
    nlinarith
  have hanti : StrictAntiOn Φ (Set.Icc 0 β) :=
    strictAntiOn_of_deriv_neg (convex_Icc 0 β) hΦ.continuousOn hderivneg
  have hn1 : n - 1 ≠ 0 := by omega
  have hΦ0 : Φ 0 = 0 := by
    have hzero : (0 : ℝ) ^ (n - 1) = 0 := zero_pow hn1
    simp [Φ, hf0, hzero]
  intro t ht
  have htpos : 0 < t := ht.1
  have htβ : t ≤ β := ht.2
  have hmem0 : (0 : ℝ) ∈ Set.Icc 0 β := ⟨le_rfl, le_of_lt hβ⟩
  have hmemt : t ∈ Set.Icc 0 β := ⟨le_of_lt htpos, htβ⟩
  have hΦt_neg : Φ t < 0 := by
    have hlt : Φ t < Φ 0 := hanti hmem0 hmemt htpos
    rwa [hΦ0] at hlt
  have hprod_neg :
      f t ^ (n - 1) * ψ (derivWithin T (Set.Icc 0 β) t) < 0 := by
    simpa [Φ] using hΦt_neg
  have hf_t : 0 < f t := hfpos t ⟨htpos, htβ⟩
  have hpow : 0 < f t ^ (n - 1) := pow_pos hf_t _
  have hψderiv_neg : ψ (derivWithin T (Set.Icc 0 β) t) < 0 := by
    have hmul := mul_neg_iff.mp hprod_neg
    rcases hmul with ⟨hleft, hright⟩ | ⟨hleft, hright⟩
    · exact hright
    · exact False.elim ((not_lt_of_ge hpow.le) hleft)
  exact (hψneg_iff (derivWithin T (Set.Icc 0 β) t)).mp hψderiv_neg

end Rollout_p0971_derivwithin_neg_of_positive_solution

#check_dependency_graph "Rollout_p0971_derivwithin_neg_of_positive_solution.derivWithin_neg_of_positive_solution" against "{\"edges\":[{\"conclusion\":{\"name\":\"hψneg_iff\",\"statement\":\"∀ (s : ℝ), ψ s < 0 ↔ s < 0\"},\"graphEdgeId\":\"h_001_h_neg_iff\",\"premises\":[],\"rawEdgeId\":\"telescope_20\"},{\"conclusion\":{\"name\":\"hψpos_iff\",\"statement\":\"∀ (s : ℝ), 0 < ψ s ↔ 0 < s\"},\"graphEdgeId\":\"h_002_h_pos_iff\",\"premises\":[],\"rawEdgeId\":\"telescope_21\"},{\"conclusion\":{\"name\":\"hn1\",\"statement\":\"n - 1 ≠ 0\"},\"graphEdgeId\":\"h_005_hn1\",\"premises\":[{\"name\":\"hn\",\"statement\":\"2 ≤ n\"}],\"rawEdgeId\":\"telescope_24\"},{\"conclusion\":{\"name\":\"htpos\",\"statement\":\"0 < t\"},\"graphEdgeId\":\"h_007_htpos\",\"premises\":[{\"name\":\"ht\",\"statement\":\"t ∈ Set.Ioc 0 β\"}],\"rawEdgeId\":\"telescope_28\"},{\"conclusion\":{\"name\":\"htβ\",\"statement\":\"t ≤ β\"},\"graphEdgeId\":\"h_008_ht\",\"premises\":[{\"name\":\"ht\",\"statement\":\"t ∈ Set.Ioc 0 β\"}],\"rawEdgeId\":\"telescope_29\"},{\"conclusion\":{\"name\":\"hmem0\",\"statement\":\"0 ∈ Set.Icc 0 β\"},\"graphEdgeId\":\"h_009_hmem0\",\"premises\":[{\"name\":\"hβ\",\"statement\":\"0 < β\"}],\"rawEdgeId\":\"telescope_30\"},{\"conclusion\":{\"name\":\"hderivneg\",\"statement\":\"∀ t ∈ interior (Set.Icc 0 β), deriv Φ t < 0\"},\"graphEdgeId\":\"h_003_hderivneg\",\"premises\":[{\"name\":\"hlam\",\"statement\":\"0 < lam\"},{\"name\":\"hfpos\",\"statement\":\"∀ t ∈ Set.Ioc 0 β, 0 < f t\"},{\"name\":\"hODE\",\"statement\":\"∀ t ∈ Set.Ioo 0 β, deriv Φ t + lam * f t ^ (n - 1) * ψ (T t) = 0\"},{\"name\":\"hTpos\",\"statement\":\"∀ t ∈ Set.Ioo 0 β, 0 < T t\"},{\"name\":\"hψpos_iff\",\"statement\":\"∀ (s : ℝ), 0 < ψ s ↔ 0 < s\"}],\"rawEdgeId\":\"telescope_22\"},{\"conclusion\":{\"name\":\"hΦ0\",\"statement\":\"Φ 0 = 0\"},\"graphEdgeId\":\"h_006_h_0\",\"premises\":[{\"name\":\"hf0\",\"statement\":\"f 0 = 0\"},{\"name\":\"hn1\",\"statement\":\"n - 1 ≠ 0\"}],\"rawEdgeId\":\"telescope_25\"},{\"conclusion\":{\"name\":\"hmemt\",\"statement\":\"t ∈ Set.Icc 0 β\"},\"graphEdgeId\":\"h_010_hmemt\",\"premises\":[{\"name\":\"htpos\",\"statement\":\"0 < t\"},{\"name\":\"htβ\",\"statement\":\"t ≤ β\"}],\"rawEdgeId\":\"telescope_31\"},{\"conclusion\":{\"name\":\"hf_t\",\"statement\":\"0 < f t\"},\"graphEdgeId\":\"h_013_hf_t\",\"premises\":[{\"name\":\"hfpos\",\"statement\":\"∀ t ∈ Set.Ioc 0 β, 0 < f t\"},{\"name\":\"htpos\",\"statement\":\"0 < t\"},{\"name\":\"htβ\",\"statement\":\"t ≤ β\"}],\"rawEdgeId\":\"telescope_34\"},{\"conclusion\":{\"name\":\"hanti\",\"statement\":\"StrictAntiOn Φ (Set.Icc 0 β)\"},\"graphEdgeId\":\"h_004_hanti\",\"premises\":[{\"name\":\"hΦ\",\"statement\":\"ContDiffOn ℝ 1 Φ (Set.Icc 0 β)\"},{\"name\":\"hderivneg\",\"statement\":\"∀ t ∈ interior (Set.Icc 0 β), deriv Φ t < 0\"}],\"rawEdgeId\":\"telescope_23\"},{\"conclusion\":{\"name\":\"hpow\",\"statement\":\"0 < f t ^ (n - 1)\"},\"graphEdgeId\":\"h_014_hpow\",\"premises\":[{\"name\":\"hf_t\",\"statement\":\"0 < f t\"}],\"rawEdgeId\":\"telescope_35\"},{\"conclusion\":{\"name\":\"hΦt_neg\",\"statement\":\"Φ t < 0\"},\"graphEdgeId\":\"h_011_h_t_neg\",\"premises\":[{\"name\":\"hanti\",\"statement\":\"StrictAntiOn Φ (Set.Icc 0 β)\"},{\"name\":\"hΦ0\",\"statement\":\"Φ 0 = 0\"},{\"name\":\"htpos\",\"statement\":\"0 < t\"},{\"name\":\"hmem0\",\"statement\":\"0 ∈ Set.Icc 0 β\"},{\"name\":\"hmemt\",\"statement\":\"t ∈ Set.Icc 0 β\"}],\"rawEdgeId\":\"telescope_32\"},{\"conclusion\":{\"name\":\"hprod_neg\",\"statement\":\"f t ^ (n - 1) * ψ (derivWithin T (Set.Icc 0 β) t) < 0\"},\"graphEdgeId\":\"h_012_hprod_neg\",\"premises\":[{\"name\":\"hΦt_neg\",\"statement\":\"Φ t < 0\"}],\"rawEdgeId\":\"telescope_33\"},{\"conclusion\":{\"name\":\"hψderiv_neg\",\"statement\":\"ψ (derivWithin T (Set.Icc 0 β) t) < 0\"},\"graphEdgeId\":\"h_015_h_deriv_neg\",\"premises\":[{\"name\":\"hprod_neg\",\"statement\":\"f t ^ (n - 1) * ψ (derivWithin T (Set.Icc 0 β) t) < 0\"},{\"name\":\"hpow\",\"statement\":\"0 < f t ^ (n - 1)\"}],\"rawEdgeId\":\"telescope_36\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"derivWithin T (Set.Icc 0 β) t < 0\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hψneg_iff\",\"statement\":\"∀ (s : ℝ), ψ s < 0 ↔ s < 0\"},{\"name\":\"hψderiv_neg\",\"statement\":\"ψ (derivWithin T (Set.Icc 0 β) t) < 0\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0971_derivwithin_neg_of_positive_solution\",\"reconstructedProofSha256\":\"2cbeb4b491b5982f77e7c068f9d677e932ef9c1cb0b9222481bd34e0cf1ff4ce\",\"selectedEdgeCount\":16,\"theoremName\":\"Rollout_p0971_derivwithin_neg_of_positive_solution.derivWithin_neg_of_positive_solution\",\"topologySha256\":\"253a8736d821304a70bd1dc324f603e5e16229c1ee25c0de4161930c7617de03\"}"

namespace Rollout_p1067_complex_exp_modulus_bounds

-- graph_id: p1067_complex_exp_modulus_bounds
-- topology_sha256: ae0775c9de803f41c6b91d674b58b5dd7eeb7343638294ca094a3b916b2a3aff
/- verified submission -/
theorem complex_exp_modulus_bounds :
  let f : ℂ → ℂ := fun z => z + 1 + Complex.exp (-z)
  ∀ z : ℂ, -z.re ≥ ‖z‖ / 2 ∧ -z.re ≥ 3 →
    (1 / 2) * Real.exp (-z.re) ≤ ‖f z‖ ∧
      ‖f z‖ ≤ 2 * Real.exp (-z.re) := by
  intro f z hz
  have hx3 : 3 ≤ -z.re := hz.2
  have hnormz : ‖z‖ ≤ 2 * (-z.re) := by
    have h := hz.1
    nlinarith
  have hexp : 4 * (-z.re) + 2 ≤ Real.exp (-z.re) := by
    have hsum := Real.sum_le_exp_of_nonneg (show 0 ≤ -z.re by linarith) 5
    norm_num [Finset.sum_range_succ] at hsum
    nlinarith [sq_nonneg ((-z.re) - 3), sq_nonneg (-z.re)]
  have hz1 : ‖z + 1‖ ≤ (1 / 2) * Real.exp (-z.re) := by
    calc
      ‖z + 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_add_le z 1
      _ = ‖z‖ + 1 := by simp
      _ ≤ (1 / 2) * Real.exp (-z.re) := by
        nlinarith [Real.exp_nonneg (-z.re)]
  have hnormexp : ‖Complex.exp (-z)‖ = Real.exp (-z.re) := by
    simpa using Complex.norm_exp (-z)
  have hlower_core :
      (1 / 2) * Real.exp (-z.re) ≤ ‖z + 1 + Complex.exp (-z)‖ := by
    have hrev := norm_sub_le_norm_add (Complex.exp (-z)) (z + 1)
    rw [hnormexp] at hrev
    have hrev' : Real.exp (-z.re) - ‖z + 1‖ ≤ ‖z + 1 + Complex.exp (-z)‖ := by
      simpa [add_comm, add_left_comm, add_assoc] using hrev
    nlinarith [Real.exp_nonneg (-z.re)]
  have hupper_core :
      ‖z + 1 + Complex.exp (-z)‖ ≤ 2 * Real.exp (-z.re) := by
    have htri := norm_add_le (z + 1) (Complex.exp (-z))
    rw [hnormexp] at htri
    nlinarith [Real.exp_nonneg (-z.re)]
  exact ⟨hlower_core, hupper_core⟩

end Rollout_p1067_complex_exp_modulus_bounds

#check_dependency_graph "Rollout_p1067_complex_exp_modulus_bounds.complex_exp_modulus_bounds" against "{\"edges\":[{\"conclusion\":{\"name\":\"hexp\",\"statement\":\"4 * -z.re + 2 ≤ Real.exp (-z.re)\"},\"graphEdgeId\":\"h_003_hexp\",\"premises\":[{\"name\":\"hz\",\"statement\":\"-z.re ≥ ‖z‖ / 2 ∧ -z.re ≥ 3\"}],\"rawEdgeId\":\"telescope_5\"},{\"conclusion\":{\"name\":\"hnormexp\",\"statement\":\"‖Complex.exp (-z)‖ = Real.exp (-z.re)\"},\"graphEdgeId\":\"h_005_hnormexp\",\"premises\":[],\"rawEdgeId\":\"telescope_7\"},{\"conclusion\":{\"name\":\"hz1\",\"statement\":\"‖z + 1‖ ≤ 1 / 2 * Real.exp (-z.re)\"},\"graphEdgeId\":\"h_004_hz1\",\"premises\":[{\"name\":\"hz\",\"statement\":\"-z.re ≥ ‖z‖ / 2 ∧ -z.re ≥ 3\"},{\"name\":\"hexp\",\"statement\":\"4 * -z.re + 2 ≤ Real.exp (-z.re)\"}],\"rawEdgeId\":\"telescope_6\"},{\"conclusion\":{\"name\":\"hlower_core\",\"statement\":\"1 / 2 * Real.exp (-z.re) ≤ ‖z + 1 + Complex.exp (-z)‖\"},\"graphEdgeId\":\"h_006_hlower_core\",\"premises\":[{\"name\":\"hz1\",\"statement\":\"‖z + 1‖ ≤ 1 / 2 * Real.exp (-z.re)\"},{\"name\":\"hnormexp\",\"statement\":\"‖Complex.exp (-z)‖ = Real.exp (-z.re)\"}],\"rawEdgeId\":\"telescope_8\"},{\"conclusion\":{\"name\":\"hupper_core\",\"statement\":\"‖z + 1 + Complex.exp (-z)‖ ≤ 2 * Real.exp (-z.re)\"},\"graphEdgeId\":\"h_007_hupper_core\",\"premises\":[{\"name\":\"hz\",\"statement\":\"-z.re ≥ ‖z‖ / 2 ∧ -z.re ≥ 3\"},{\"name\":\"hexp\",\"statement\":\"4 * -z.re + 2 ≤ Real.exp (-z.re)\"},{\"name\":\"hz1\",\"statement\":\"‖z + 1‖ ≤ 1 / 2 * Real.exp (-z.re)\"},{\"name\":\"hnormexp\",\"statement\":\"‖Complex.exp (-z)‖ = Real.exp (-z.re)\"}],\"rawEdgeId\":\"telescope_9\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"1 / 2 * Real.exp (-z.re) ≤ ‖f z‖ ∧ ‖f z‖ ≤ 2 * Real.exp (-z.re)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hlower_core\",\"statement\":\"1 / 2 * Real.exp (-z.re) ≤ ‖z + 1 + Complex.exp (-z)‖\"},{\"name\":\"hupper_core\",\"statement\":\"‖z + 1 + Complex.exp (-z)‖ ≤ 2 * Real.exp (-z.re)\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1067_complex_exp_modulus_bounds\",\"reconstructedProofSha256\":\"92a592b1c935f0f8a3fd913ea903056af176ecec6c7d55b162b8348316811d42\",\"selectedEdgeCount\":6,\"theoremName\":\"Rollout_p1067_complex_exp_modulus_bounds.complex_exp_modulus_bounds\",\"topologySha256\":\"ae0775c9de803f41c6b91d674b58b5dd7eeb7343638294ca094a3b916b2a3aff\"}"

namespace Rollout_p1078_khexpansive_iff_separating_and_isopen_fixe

-- graph_id: p1078_khexpansive_iff_separating_and_isopen_fixe
-- topology_sha256: 1d21a2c271cc6d89ca8dd8b3bb2cfd8d6957cb59c12c94472e01d3e82f68c8b9
/- accepted add_to_file helper 1 -/
lemma flow_apply_neg_left
    {Λ : Type*} (φ : ℝ × Λ → Λ)
    (hzero : ∀ x : Λ, φ (0, x) = x)
    (hadd : ∀ (t u : ℝ) (x : Λ), φ (t + u, x) = φ (t, φ (u, x)))
    (t : ℝ) (x : Λ) : φ (-t, φ (t, x)) = x := by
  have h := hadd (-t) t x
  have hz := hzero x
  norm_num at h
  rw [hz] at h
  exact h.symm

lemma flow_apply_neg_right
    {Λ : Type*} (φ : ℝ × Λ → Λ)
    (hzero : ∀ x : Λ, φ (0, x) = x)
    (hadd : ∀ (t u : ℝ) (x : Λ), φ (t + u, x) = φ (t, φ (u, x)))
    (t : ℝ) (x : Λ) : φ (t, φ (-t, x)) = x := by
  have h := hadd t (-t) x
  have hz := hzero x
  norm_num at h
  rw [hz] at h
  exact h.symm

lemma flow_period_nat
    {Λ : Type*} (φ : ℝ × Λ → Λ)
    (hzero : ∀ x : Λ, φ (0, x) = x)
    (hadd : ∀ (t u : ℝ) (x : Λ), φ (t + u, x) = φ (t, φ (u, x)))
    {u : ℝ} {x : Λ} (hper : φ (u, x) = x) (n : ℕ) :
    φ ((n : ℝ) * u, x) = x := by
  induction n with
  | zero => simp [hzero]
  | succ n ih =>
      have hcalc : ((n + 1 : ℕ) : ℝ) * u = u + (n : ℝ) * u := by
        rw [Nat.cast_add, Nat.cast_one]
        ring
      rw [hcalc, hadd, ih, hper]

lemma flow_period_int
    {Λ : Type*} (φ : ℝ × Λ → Λ)
    (hzero : ∀ x : Λ, φ (0, x) = x)
    (hadd : ∀ (t u : ℝ) (x : Λ), φ (t + u, x) = φ (t, φ (u, x)))
    {u : ℝ} {x : Λ} (hper : φ (u, x) = x) (k : ℤ) :
    φ ((k : ℝ) * u, x) = x := by
  cases k with
  | ofNat n =>
      simpa using flow_period_nat φ hzero hadd hper n
  | negSucc n =>
      let q : ℝ := (((n + 1 : ℕ) : ℝ) * u)
      have hnq : φ (q, x) = x := flow_period_nat φ hzero hadd hper (n + 1)
      have hneg := hadd (-q) q x
      have hz := hzero x
      norm_num at hneg
      rw [hz, hnq] at hneg
      have hcast : ((Int.negSucc n : ℤ) : ℝ) * u = -q := by
        dsimp [q]
        rw [Nat.cast_add, Nat.cast_one]
        norm_num [Int.negSucc]
        ring
      rw [hcast]
      exact hneg.symm

lemma fixed_of_flow_fixed
    {Λ : Type*} (φ : ℝ × Λ → Λ)
    (hzero : ∀ x : Λ, φ (0, x) = x)
    (hadd : ∀ (t u : ℝ) (x : Λ), φ (t + u, x) = φ (t, φ (u, x)))
    {t : ℝ} {x : Λ}
    (h : ∀ r : ℝ, φ (r, φ (t, x)) = φ (t, x)) :
    ∀ r : ℝ, φ (r, x) = x := by
  have hxt : x = φ (t, x) := by
    have hneg := h (-t)
    rw [flow_apply_neg_left φ hzero hadd t x] at hneg
    exact hneg
  intro r
  calc
    φ (r, x) = φ ((r - t) + t, x) := by ring_nf
    _ = φ (r - t, φ (t, x)) := hadd (r - t) t x
    _ = φ (t, x) := h (r - t)
    _ = x := hxt.symm

/- accepted add_to_file helper 2 -/
lemma exists_pos_no_small_period_of_isOpen_fixed
    {Λ : Type*} [MetricSpace Λ] [CompactSpace Λ]
    (φ : ℝ × Λ → Λ)
    (hcont : Continuous φ)
    (hzero : ∀ x : Λ, φ (0, x) = x)
    (hadd : ∀ (t u : ℝ) (x : Λ), φ (t + u, x) = φ (t, φ (u, x)))
    (hfix : IsOpen {x : Λ | ∀ t : ℝ, φ (t, x) = x}) :
    ∃ η : ℝ, 0 < η ∧
      ∀ x : Λ, x ∉ {x : Λ | ∀ t : ℝ, φ (t, x) = x} →
        ∀ u : ℝ, 0 < |u| → |u| < η → φ (u, x) ≠ x := by
  classical
  by_contra hnone
  push_neg at hnone
  let F : Set Λ := {x : Λ | ∀ t : ℝ, φ (t, x) = x}
  have hseq : ∀ n : ℕ, ∃ x : Λ, ∃ u : ℝ,
      x ∉ F ∧ 0 < |u| ∧ |u| < 1 / ((n : ℝ) + 1) ∧ φ (u, x) = x := by
    intro n
    have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    rcases hnone _ hn with ⟨x, hx, u, hupos, hu, hper⟩
    exact ⟨x, u, hx, hupos, hu, hper⟩
  choose x u hx hupos hub hper using hseq
  have hCclosed : IsClosed Fᶜ := hfix.isClosed_compl
  have hCcompact : IsCompact Fᶜ := hCclosed.isCompact
  have hxC : ∀ n : ℕ, x n ∈ Fᶜ := by
    intro n
    exact hx n
  rcases hCcompact.tendsto_subseq hxC with ⟨xLim, hxLimC, ρ, hρmono, hxlim⟩
  have hρtop : Filter.Tendsto ρ Filter.atTop Filter.atTop := hρmono.tendsto_atTop
  have hone : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hg : Filter.Tendsto (fun n : ℕ => 1 / ((ρ n : ℝ) + 1)) Filter.atTop (nhds 0) :=
    hone.comp hρtop
  have hpabs : Filter.Tendsto (fun n : ℕ => |u (ρ n)|) Filter.atTop (nhds 0) := by
    apply squeeze_zero
    · intro n
      exact abs_nonneg _
    · intro n
      exact le_of_lt (hub (ρ n))
    · exact hg
  have hpne : ∀ n : ℕ, u (ρ n) ≠ 0 := fun n => abs_pos.mp (hupos (ρ n))
  have hfixed : ∀ T : ℝ, φ (T, xLim) = xLim := by
    intro T
    let k : ℕ → ℤ := fun n => round (T / u (ρ n))
    let τ : ℕ → ℝ := fun n => (k n : ℝ) * u (ρ n)
    have hbound : ∀ n : ℕ, |τ n - T| ≤ |u (ρ n)| / 2 := by
      intro n
      calc
        |τ n - T| = |u (ρ n)| * |(k n : ℝ) - T / u (ρ n)| := by
          rw [← abs_mul]
          apply congrArg abs
          dsimp [τ, k]
          field_simp [hpne n]
        _ ≤ |u (ρ n)| * (1 / 2) := by
          gcongr
          dsimp [k]
          rw [abs_sub_comm]
          exact abs_sub_round (T / u (ρ n))
        _ = |u (ρ n)| / 2 := by ring
    have hsubabs : Filter.Tendsto (fun n : ℕ => |τ n - T|) Filter.atTop (nhds 0) := by
      apply squeeze_zero
      · intro n
        exact abs_nonneg _
      · intro n
        exact hbound n
      · simpa using hpabs.div_const 2
    have hsub0 : Filter.Tendsto (fun n : ℕ => τ n - T) Filter.atTop (nhds 0) :=
      (tendsto_zero_iff_abs_tendsto_zero (fun n : ℕ => τ n - T)).mpr hsubabs
    have hτ : Filter.Tendsto τ Filter.atTop (nhds T) := by
      have hconst : Filter.Tendsto (fun _ : ℕ => T) Filter.atTop (nhds T) := tendsto_const_nhds
      have h := hsub0.add hconst
      simpa using h
    have hpern : ∀ n : ℕ, φ (τ n, x (ρ n)) = x (ρ n) := by
      intro n
      exact flow_period_int φ hzero hadd (hper (ρ n)) (k n)
    have hpair : Filter.Tendsto (fun n : ℕ => (τ n, x (ρ n))) Filter.atTop (nhds (T, xLim)) :=
      hτ.prodMk_nhds hxlim
    have hlimφ : Filter.Tendsto (fun n : ℕ => φ (τ n, x (ρ n))) Filter.atTop
        (nhds (φ (T, xLim))) := by
      exact (hcont.tendsto (T, xLim)).comp hpair
    have hlimx : Filter.Tendsto (fun n : ℕ => φ (τ n, x (ρ n))) Filter.atTop
        (nhds xLim) := by
      have hfun : (fun n : ℕ => φ (τ n, x (ρ n))) = fun n : ℕ => x (ρ n) := by
        funext n
        exact hpern n
      simpa [hfun] using hxlim
    exact tendsto_nhds_unique hlimφ hlimx
  have hxLimF : xLim ∈ F := hfixed
  exact hxLimC hxLimF

/- accepted add_to_file helper 3 -/
lemma exists_pos_flow_displacement_of_isOpen_fixed
    {Λ : Type*} [MetricSpace Λ] [CompactSpace Λ]
    (φ : ℝ × Λ → Λ)
    (hcont : Continuous φ)
    (hzero : ∀ x : Λ, φ (0, x) = x)
    (hadd : ∀ (t u : ℝ) (x : Λ), φ (t + u, x) = φ (t, φ (u, x)))
    (hfix : IsOpen {x : Λ | ∀ t : ℝ, φ (t, x) = x}) :
    ∃ τ e : ℝ, 0 < τ ∧ 0 < e ∧
      ∀ x : Λ, x ∉ {x : Λ | ∀ t : ℝ, φ (t, x) = x} →
        e ≤ dist (φ (τ, x)) x ∧ e ≤ dist (φ (-τ, x)) x := by
  rcases exists_pos_no_small_period_of_isOpen_fixed φ hcont hzero hadd hfix with
    ⟨η, hη, hnoper⟩
  let F : Set Λ := {x : Λ | ∀ t : ℝ, φ (t, x) = x}
  let τ : ℝ := η / 2
  have hτ : 0 < τ := by positivity
  have hτlt : τ < η := by
    dsimp [τ]
    linarith
  have hCclosed : IsClosed Fᶜ := hfix.isClosed_compl
  have hCcompact : IsCompact Fᶜ := hCclosed.isCompact
  have hflowτ : Continuous fun x : Λ => φ (τ, x) := by
    exact hcont.comp (continuous_const.prodMk continuous_id)
  have hdistτ : Continuous fun x : Λ => dist (φ (τ, x)) x :=
    hflowτ.dist continuous_id
  have hposτ : ∀ x ∈ Fᶜ, 0 < dist (φ (τ, x)) x := by
    intro x hx
    have hne : φ (τ, x) ≠ x := by
      apply hnoper x hx τ
      · rw [abs_of_pos hτ]
        exact hτ
      · rw [abs_of_pos hτ]
        exact hτlt
    exact dist_pos.mpr hne
  rcases hCcompact.exists_forall_le' hdistτ.continuousOn hposτ with ⟨eτ, heτ, hleτ⟩
  have hflow_negτ : Continuous fun x : Λ => φ (-τ, x) := by
    exact hcont.comp (continuous_const.prodMk continuous_id)
  have hdist_negτ : Continuous fun x : Λ => dist (φ (-τ, x)) x :=
    hflow_negτ.dist continuous_id
  have hpos_negτ : ∀ x ∈ Fᶜ, 0 < dist (φ (-τ, x)) x := by
    intro x hx
    have hne : φ (-τ, x) ≠ x := by
      apply hnoper x hx (-τ)
      · rw [abs_neg, abs_of_pos hτ]
        exact hτ
      · rw [abs_neg, abs_of_pos hτ]
        exact hτlt
    exact dist_pos.mpr hne
  rcases hCcompact.exists_forall_le' hdist_negτ.continuousOn hpos_negτ with
    ⟨e_neg, he_neg, hle_neg⟩
  refine ⟨τ, min eτ e_neg, hτ, lt_min heτ he_neg, ?_⟩
  intro x hx
  have hxC : x ∈ Fᶜ := hx
  constructor
  · exact le_trans (min_le_left _ _) (hleτ x hxC)
  · exact le_trans (min_le_right _ _) (hle_neg x hxC)

/- accepted add_to_file helper 4 -/
lemma nonfixed_flow_of_nonfixed
    {Λ : Type*} (φ : ℝ × Λ → Λ)
    (hzero : ∀ x : Λ, φ (0, x) = x)
    (hadd : ∀ (t u : ℝ) (x : Λ), φ (t + u, x) = φ (t, φ (u, x)))
    {t : ℝ} {x : Λ}
    (hx : x ∉ {x : Λ | ∀ t : ℝ, φ (t, x) = x}) :
    φ (t, x) ∉ {x : Λ | ∀ t : ℝ, φ (t, x) = x} := by
  intro h
  exact hx (fixed_of_flow_fixed φ hzero hadd h)

/- accepted add_to_file helper 5 -/
lemma isClosed_fixedPoints_of_continuous_flow
    {Λ : Type*} [MetricSpace Λ]
    (φ : ℝ × Λ → Λ)
    (hcont : Continuous φ) :
    IsClosed {x : Λ | ∀ t : ℝ, φ (t, x) = x} := by
  rw [Set.setOf_forall]
  apply isClosed_iInter
  intro t
  have hflow : Continuous fun x : Λ => φ (t, x) :=
    hcont.comp (continuous_const.prodMk continuous_id)
  exact isClosed_eq hflow continuous_id

/- accepted add_to_file helper 6 -/
lemma exists_pos_fixed_nonfixed_dist
    {Λ : Type*} [MetricSpace Λ] [CompactSpace Λ]
    (φ : ℝ × Λ → Λ)
    (hcont : Continuous φ)
    (hfix : IsOpen {x : Λ | ∀ t : ℝ, φ (t, x) = x}) :
    ∃ r : ℝ, 0 < r ∧
      ∀ x : Λ, x ∈ {x : Λ | ∀ t : ℝ, φ (t, x) = x} →
        ∀ z : Λ, z ∉ {x : Λ | ∀ t : ℝ, φ (t, x) = x} →
          r < dist x z := by
  let F : Set Λ := {x : Λ | ∀ t : ℝ, φ (t, x) = x}
  have hFclosed : IsClosed F := isClosed_fixedPoints_of_continuous_flow φ hcont
  have hCclosed : IsClosed Fᶜ := hfix.isClosed_compl
  have hCcompact : IsCompact Fᶜ := hCclosed.isCompact
  have hdisj : Disjoint Fᶜ F := disjoint_compl_left
  rcases Metric.exists_pos_forall_lt_edist hCcompact hFclosed hdisj with ⟨r, hr, hrpos⟩
  refine ⟨r, ?_, ?_⟩
  · exact_mod_cast hr
  · intro x hxF z hzF
    have hzC : z ∈ Fᶜ := hzF
    have hnedist := hrpos z hzC x hxF
    have hzx : z ≠ x := by
      intro hzx_eq
      subst hzx_eq
      exact hzF hxF
    have hdistpos : 0 < dist z x := dist_pos.mpr hzx
    have hof : ENNReal.ofReal (r : ℝ) < ENNReal.ofReal (dist z x) := by
      rw [ENNReal.ofReal_coe_nnreal]
      simpa [edist_dist] using hnedist
    have hreal : (r : ℝ) < dist z x :=
      (ENNReal.ofReal_lt_ofReal_iff hdistpos).mp hof
    rwa [dist_comm] at hreal

/- accepted add_to_file helper 7 -/
lemma reparam_surjective_of_nonfixed
    {Λ : Type*} [MetricSpace Λ] [CompactSpace Λ]
    (φ : ℝ × Λ → Λ)
    (hzero : ∀ x : Λ, φ (0, x) = x)
    (hadd : ∀ (t u : ℝ) (x : Λ), φ (t + u, x) = φ (t, φ (u, x)))
    {x : Λ} (hx : x ∉ {x : Λ | ∀ t : ℝ, φ (t, x) = x})
    {s : ℝ → ℝ} (hs : Continuous s) (hs0 : s 0 = 0)
    {τ e δ : ℝ} (hτ : 0 < τ)
    (hdis : ∀ z : Λ, z ∉ {x : Λ | ∀ t : ℝ, φ (t, x) = x} →
      e ≤ dist (φ (τ, z)) z ∧ e ≤ dist (φ (-τ, z)) z)
    (hA : ∀ t : ℝ, dist (φ (t, x)) (φ (s t, x)) < δ)
    (hδe : δ < e) :
    Function.Surjective s := by
  let F : Set Λ := {x : Λ | ∀ t : ℝ, φ (t, x) = x}
  let u : ℝ → ℝ := fun t => s t - t
  have hucont : Continuous u := hs.sub continuous_id
  have hu0 : u 0 = 0 := by
    dsimp [u]
    simp [hs0]
  have hbound : ∀ t : ℝ, |u t| < τ := by
    intro t
    by_contra hnot
    have htaule : τ ≤ |u t| := le_of_not_gt hnot
    let v : ℝ → ℝ := fun r => |u r|
    have hvcont : Continuous v := hucont.abs
    have hv0 : v 0 = 0 := by
      dsimp [v]
      simp [hu0]
    have hexists : ∃ t0 : ℝ, |u t0| = τ := by
      by_cases ht : 0 ≤ t
      · have hsubset : Set.Icc (v 0) (v t) ⊆ v '' Set.Icc 0 t :=
          intermediate_value_Icc ht hvcont.continuousOn
        have hτmem : τ ∈ Set.Icc (v 0) (v t) := by
          constructor
          · rw [hv0]
            exact le_of_lt hτ
          · exact htaule
        rcases hsubset hτmem with ⟨t0, ht0, ht0val⟩
        exact ⟨t0, ht0val⟩
      · have ht0 : t ≤ 0 := le_of_not_ge ht
        have hsubset : Set.Icc (v 0) (v t) ⊆ v '' Set.Icc t 0 :=
          intermediate_value_Icc' ht0 hvcont.continuousOn
        have hτmem : τ ∈ Set.Icc (v 0) (v t) := by
          constructor
          · rw [hv0]
            exact le_of_lt hτ
          · exact htaule
        rcases hsubset hτmem with ⟨t0, ht0range, ht0val⟩
        exact ⟨t0, ht0val⟩
    rcases hexists with ⟨t0, ht0abs⟩
    let z : Λ := φ (t0, x)
    have hz : z ∉ F := by
      dsimp [z, F]
      exact nonfixed_flow_of_nonfixed φ hzero hadd hx
    have hfloweq : φ (u t0, z) = φ (s t0, x) := by
      dsimp [u, z]
      have hh := hadd (s t0 - t0) t0 x
      have hsum : s t0 - t0 + t0 = s t0 := by ring
      rw [hsum] at hh
      exact hh.symm
    have hA0 : dist z (φ (u t0, z)) < δ := by
      have h0 := hA t0
      rw [← hfloweq] at h0
      exact h0
    rcases hdis z hz with ⟨hlowτ, hlow_negτ⟩
    rcases eq_or_eq_neg_of_abs_eq ht0abs with hu_eq | hu_eq
    · have hsmall : dist (φ (τ, z)) z < δ := by
        rw [hu_eq, dist_comm] at hA0
        exact hA0
      exact (not_lt_of_ge hlowτ) (lt_trans hsmall hδe)
    · have hsmall : dist (φ (-τ, z)) z < δ := by
        rw [hu_eq, dist_comm] at hA0
        exact hA0
      exact (not_lt_of_ge hlow_negτ) (lt_trans hsmall hδe)
  intro r
  let a : ℝ := r - τ
  let b : ℝ := r + τ
  have ha : s a < r := by
    have hb := hbound a
    rcases abs_lt.mp hb with ⟨hleft, hright⟩
    dsimp [u, a] at hright
    linarith
  have hb : r < s b := by
    have hbnd := hbound b
    rcases abs_lt.mp hbnd with ⟨hleft, hright⟩
    dsimp [u, b] at hleft
    linarith
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith
  have hsubset : Set.Icc (s a) (s b) ⊆ s '' Set.Icc a b :=
    intermediate_value_Icc hab hs.continuousOn
  have hmem : r ∈ Set.Icc (s a) (s b) := ⟨le_of_lt ha, le_of_lt hb⟩
  rcases hsubset hmem with ⟨t, ht, hts⟩
  exact ⟨t, hts⟩

/- verified submission -/
theorem khExpansive_iff_separating_and_isOpen_fixedPoints
    {Λ : Type*} [MetricSpace Λ] [CompactSpace Λ]
    (φ : ℝ × Λ → Λ)
    (hcont : Continuous φ)
    (hzero : ∀ x : Λ, φ (0, x) = x)
    (hadd : ∀ (t u : ℝ) (x : Λ), φ (t + u, x) = φ (t, φ (u, x))) :
    (∃ δ : ℝ, 0 < δ ∧
      ∀ (x y : Λ) (s : ℝ → ℝ), Continuous s → s 0 = 0 →
        ((∀ t : ℝ, dist (φ (t, x)) (φ (s t, x)) < δ) ∧
          (∀ t : ℝ, dist (φ (t, x)) (φ (s t, y)) < δ)) →
        y ∈ Set.range (fun t : ℝ => φ (t, x))) ↔
      ((∃ α : ℝ, 0 < α ∧
        ∀ x y : Λ,
          (∀ t : ℝ, dist (φ (t, x)) (φ (t, y)) < α) →
          y ∈ Set.range (fun t : ℝ => φ (t, x))) ∧
        IsOpen {x : Λ | ∀ t : ℝ, φ (t, x) = x}) := by
  constructor
  · intro h
    rcases h with ⟨δ, hδ, hK⟩
    constructor
    · refine ⟨δ, hδ, ?_⟩
      intro x y hxy
      apply hK x y (fun t : ℝ => t) continuous_id rfl
      constructor
      · intro t
        simpa using hδ
      · exact hxy
    · rw [isOpen_iff_forall_mem_open]
      intro x hx
      have hsub : Metric.ball x δ ⊆ {x : Λ | ∀ t : ℝ, φ (t, x) = x} := by
        intro y hy
        have hy' : dist x y < δ := by
          rw [dist_comm]
          exact hy
        have horb : y ∈ Set.range (fun t : ℝ => φ (t, x)) := by
          apply hK x y (fun _ : ℝ => 0) continuous_const rfl
          constructor
          · intro t
            have hxt : φ (t, x) = x := hx t
            rw [hxt, hzero]
            simpa using hδ
          · intro t
            have hxt : φ (t, x) = x := hx t
            rw [hxt, hzero]
            exact hy'
        rcases horb with ⟨t, rfl⟩
        change ∀ u : ℝ, φ (u, φ (t, x)) = φ (t, x)
        rw [hx t]
        exact hx
      exact ⟨Metric.ball x δ, hsub, Metric.isOpen_ball, Metric.mem_ball_self hδ⟩
  · intro h
    rcases h with ⟨⟨α, hα, hsep⟩, hfix⟩
    rcases exists_pos_flow_displacement_of_isOpen_fixed φ hcont hzero hadd hfix with
      ⟨τ, e, hτ, he, hdis⟩
    rcases exists_pos_fixed_nonfixed_dist φ hcont hfix with ⟨r, hr, hrdist⟩
    let δ : ℝ := min (min (α / 3) (e / 2)) (r / 2)
    have hδ : 0 < δ := by
      dsimp [δ]
      exact lt_min (lt_min (by positivity) (by positivity)) (by positivity)
    have hδ_le_α3 : δ ≤ α / 3 := by
      dsimp [δ]
      exact le_trans (min_le_left _ _) (min_le_left _ _)
    have hδ_le_e2 : δ ≤ e / 2 := by
      dsimp [δ]
      exact le_trans (min_le_left _ _) (min_le_right _ _)
    have hδ_le_r2 : δ ≤ r / 2 := by
      dsimp [δ]
      exact min_le_right _ _
    have hδ_lt_e : δ < e := by
      have : e / 2 < e := by linarith
      exact lt_of_le_of_lt hδ_le_e2 this
    have hδ_lt_r : δ < r := by
      have : r / 2 < r := by linarith
      exact lt_of_le_of_lt hδ_le_r2 this
    have hδ_lt_α : δ < α := by
      have : α / 3 < α := by linarith
      exact lt_of_le_of_lt hδ_le_α3 this
    have h2δ_lt_α : 2 * δ < α := by
      have hle : 2 * δ ≤ 2 * (α / 3) := by
        exact mul_le_mul_of_nonneg_left hδ_le_α3 (by norm_num)
      have : 2 * (α / 3) < α := by linarith
      exact lt_of_le_of_lt hle this
    refine ⟨δ, hδ, ?_⟩
    intro x y s hs hs0 hcond
    by_cases hxF : x ∈ {x : Λ | ∀ t : ℝ, φ (t, x) = x}
    · have hxy : dist x y < δ := by
        have h0 := hcond.2 0
        have hx0 : φ (0, x) = x := hzero x
        have hsy : φ (s 0, y) = y := by
          rw [hs0, hzero]
        simpa [hx0, hsy] using h0
      have hyF : y ∈ {x : Λ | ∀ t : ℝ, φ (t, x) = x} := by
        by_contra hyC
        have hrlt : r < dist x y := hrdist x hxF y hyC
        have : dist x y < r := lt_trans hxy hδ_lt_r
        exact (not_lt_of_ge (le_of_lt hrlt)) this
      apply hsep x y
      intro t
      rw [hxF t, hyF t]
      exact lt_trans hxy hδ_lt_α
    · have hsurj : Function.Surjective s :=
        reparam_surjective_of_nonfixed φ hzero hadd hxF hs hs0 hτ hdis hcond.1 hδ_lt_e
      apply hsep x y
      intro q
      rcases hsurj q with ⟨t, ht⟩
      have hA : dist (φ (q, x)) (φ (t, x)) < δ := by
        have h0 := hcond.1 t
        rw [ht] at h0
        rwa [dist_comm] at h0
      have hB : dist (φ (t, x)) (φ (q, y)) < δ := by
        have h0 := hcond.2 t
        rwa [ht] at h0
      calc
        dist (φ (q, x)) (φ (q, y))
            ≤ dist (φ (q, x)) (φ (t, x)) + dist (φ (t, x)) (φ (q, y)) :=
              dist_triangle _ _ _
        _ < δ + δ := add_lt_add hA hB
        _ = 2 * δ := by ring
        _ < α := h2δ_lt_α

end Rollout_p1078_khexpansive_iff_separating_and_isopen_fixe

#check_dependency_graph "Rollout_p1078_khexpansive_iff_separating_and_isopen_fixe.khExpansive_iff_separating_and_isOpen_fixedPoints" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(∃ δ, 0 < δ ∧ ∀ (x y : Λ) (s : ℝ → ℝ), Continuous s → s 0 = 0 → ((∀ (t : ℝ), dist (φ (t, x)) (φ (s t, x)) < δ) ∧ ∀ (t : ℝ), dist (φ (t, x)) (φ (s t, y)) < δ) → y ∈ Set.range fun t => φ (t, x)) ↔ (∃ α, 0 < α ∧ ∀ (x y : Λ), (∀ (t : ℝ), dist (φ (t, x)) (φ (t, y)) < α) → y ∈ Set.range fun t => φ (t, x)) ∧ IsOpen {x | ∀ (t : ℝ), φ (t, x) = x}\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"CompactSpace Λ\"},{\"name\":\"hcont\",\"statement\":\"Continuous φ\"},{\"name\":\"hzero\",\"statement\":\"∀ (x : Λ), φ (0, x) = x\"},{\"name\":\"hadd\",\"statement\":\"∀ (t u : ℝ) (x : Λ), φ (t + u, x) = φ (t, φ (u, x))\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1078_khexpansive_iff_separating_and_isopen_fixe\",\"reconstructedProofSha256\":\"de379f18f56776441b114786daf0a381730e90673f496ebdb56d06e795acaa41\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1078_khexpansive_iff_separating_and_isopen_fixe.khExpansive_iff_separating_and_isOpen_fixedPoints\",\"topologySha256\":\"1d21a2c271cc6d89ca8dd8b3bb2cfd8d6957cb59c12c94472e01d3e82f68c8b9\"}"

namespace Rollout_p1089_logarithmic_average_bound

-- graph_id: p1089_logarithmic_average_bound
-- topology_sha256: 3b0de1941c8929d9339458ece58933b5a7be4f50c1f8629973513c008d4dd8c3
/- accepted add_to_file helper 1 -/
lemma sum_range_mul_eq_sum_filter {M : Type*} [AddCommMonoid M]
    (m N : ℕ) (hm : 0 < m) (f : {n : ℕ // 0 < n} → M) :
    (∑ k ∈ Finset.range (N / m),
        f ⟨m * (k + 1), Nat.mul_pos hm (Nat.zero_lt_succ k)⟩)
      =
    ∑ j ∈ Finset.range N,
      if m ∣ j + 1 then f ⟨j + 1, Nat.zero_lt_succ j⟩ else 0 := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij
    (fun k _ => m * (k + 1) - 1) ?_ ?_ ?_ ?_
  · intro k hk
    have hk1 : k + 1 ≤ N / m := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
    have hmul : m * (k + 1) ≤ N := by
      simpa [mul_comm] using Nat.mul_le_of_le_div m (k + 1) N hk1
    have hpos : 0 < m * (k + 1) := Nat.mul_pos hm (Nat.zero_lt_succ k)
    have hj : m * (k + 1) - 1 < N := Nat.sub_one_lt_of_le hpos hmul
    simp [Finset.mem_filter, Finset.mem_range, hj, Nat.sub_add_cancel hpos]
  · intro k₁ hk₁ k₂ hk₂ h
    have h₁ : 0 < m * (k₁ + 1) := Nat.mul_pos hm (Nat.zero_lt_succ k₁)
    have h₂ : 0 < m * (k₂ + 1) := Nat.mul_pos hm (Nat.zero_lt_succ k₂)
    have hs : m * (k₁ + 1) = m * (k₂ + 1) := by
      have := congrArg (· + 1) h
      simpa [Nat.sub_add_cancel h₁, Nat.sub_add_cancel h₂] using this
    have hk : k₁ + 1 = k₂ + 1 := Nat.mul_left_cancel hm hs
    exact Nat.succ.inj hk
  · intro j hj
    have hjmem := Finset.mem_filter.mp hj
    have hjr : j < N := Finset.mem_range.mp hjmem.1
    have hd : m ∣ j + 1 := hjmem.2
    rcases hd with ⟨t, ht⟩
    have htpos : 0 < t := by
      by_contra htz
      have ht0 : t = 0 := Nat.eq_zero_of_not_pos htz
      have : j + 1 = 0 := by simpa [ht0] using ht
      exact Nat.succ_ne_zero j this
    have htmul : m * t ≤ N := by
      have : j + 1 ≤ N := Nat.succ_le_of_lt hjr
      rw [ht] at this
      exact this
    have htdiv : t ≤ N / m := (Nat.le_div_iff_mul_le hm).mpr (by simpa [mul_comm] using htmul)
    refine ⟨t - 1, Finset.mem_range.mpr (Nat.sub_one_lt_of_le htpos htdiv), ?_⟩
    have hsucc : t - 1 + 1 = t := Nat.sub_add_cancel htpos
    change m * (t - 1 + 1) - 1 = j
    rw [hsucc]
    omega
  · intro k hk
    have hpos : 0 < m * (k + 1) := Nat.mul_pos hm (Nat.zero_lt_succ k)
    simp [Nat.sub_add_cancel hpos]

/- accepted add_to_file helper 2 -/
lemma period_weight_square_avg
    (B : Finset {n : ℕ // 0 < n}) (hB : B.Nonempty) :
    let q : ℕ := ∏ m ∈ B, m.1
    let S : ℝ := ∑ m ∈ B, 1 / (m.1 : ℝ)
    (q : ℝ)⁻¹ *
      (∑ j ∈ Finset.range q,
        (1 - (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) / S) ^ 2)
      =
    S⁻¹ ^ 2 *
      (∑ m ∈ B, ∑ n ∈ B,
        (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - 1 := by
  classical
  intro q S
  have hq : 0 < q := Finset.prod_pos (fun m _ => m.2)
  have hS : 0 < S := by
    apply Finset.sum_pos _ hB
    intro m hm
    exact one_div_pos.mpr (by exact_mod_cast m.2)
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hSR : S ≠ 0 := hS.ne'
  have hdvd : ∀ m ∈ B, m.1 ∣ q := fun m hm => Finset.dvd_prod_of_mem (fun x => x.1) hm
  have hsum_d :
      (∑ j ∈ Finset.range q, ∑ m ∈ B,
          if m.1 ∣ j + 1 then (1 : ℝ) else 0)
        = (q : ℝ) * S := by
    rw [Finset.sum_comm]
    trans ∑ m ∈ B, (((q / m.1 : ℕ) : ℝ))
    · refine Finset.sum_congr rfl ?_
      intro m hm
      rw [Finset.sum_boole, Nat.card_multiples]
    · change (∑ m ∈ B, (((q / m.1 : ℕ) : ℝ))) =
        (q : ℝ) * (∑ m ∈ B, 1 / (m.1 : ℝ))
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro m hm
      have hmR : (m.1 : ℝ) ≠ 0 := by exact_mod_cast m.2.ne'
      rw [Nat.cast_div (hdvd m hm) hmR]
      field_simp [hmR]
  have hsum_d_card :
      (∑ j ∈ Finset.range q,
          (((B.filter fun m => m.1 ∣ j + 1).card : ℝ)))
        = (q : ℝ) * S := by
    trans ∑ j ∈ Finset.range q, ∑ m ∈ B,
      if m.1 ∣ j + 1 then (1 : ℝ) else 0
    · refine Finset.sum_congr rfl ?_
      intro j hj
      rw [← Finset.sum_boole]
    · exact hsum_d
  have hsum_dsq :
      (∑ j ∈ Finset.range q,
          (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) ^ 2)
        =
      ∑ m ∈ B, ∑ n ∈ B, (((q / Nat.lcm m.1 n.1 : ℕ) : ℝ)) := by
    calc
      (∑ j ∈ Finset.range q,
          (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) ^ 2)
          =
        ∑ j ∈ Finset.range q,
          (∑ m ∈ B, ∑ n ∈ B,
            if Nat.lcm m.1 n.1 ∣ j + 1 then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [sq, Finset.sum_mul_sum]
            refine Finset.sum_congr rfl ?_
            intro m hm
            refine Finset.sum_congr rfl ?_
            intro n hn
            by_cases hlm : Nat.lcm m.1 n.1 ∣ j + 1
            · have hm : m.1 ∣ j + 1 := (Nat.lcm_dvd_iff.mp hlm).1
              have hn : n.1 ∣ j + 1 := (Nat.lcm_dvd_iff.mp hlm).2
              simp [hlm, hm, hn]
            · have hnot : ¬ (m.1 ∣ j + 1 ∧ n.1 ∣ j + 1) := by
                intro h
                exact hlm (Nat.lcm_dvd_iff.mpr h)
              by_cases hm : m.1 ∣ j + 1
              · by_cases hn : n.1 ∣ j + 1
                · exact False.elim (hnot ⟨hm, hn⟩)
                · simp [hm, hn, hlm]
              · simp [hm, hlm]
      _ = ∑ m ∈ B, ∑ n ∈ B,
            (∑ j ∈ Finset.range q,
              if Nat.lcm m.1 n.1 ∣ j + 1 then (1 : ℝ) else 0) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro m hm
            rw [Finset.sum_comm]
      _ = ∑ m ∈ B, ∑ n ∈ B, (((q / Nat.lcm m.1 n.1 : ℕ) : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            refine Finset.sum_congr rfl ?_
            intro n hn
            rw [Finset.sum_boole, Nat.card_multiples]
  have hlcm_cast : ∀ m ∈ B, ∀ n ∈ B,
      (((q / Nat.lcm m.1 n.1 : ℕ) : ℝ))
        = (q : ℝ) * ((Nat.gcd m.1 n.1 : ℝ) / ((m.1 : ℝ) * (n.1 : ℝ))) := by
    intro m hm n hn
    have hmpos : (m.1 : ℝ) ≠ 0 := by exact_mod_cast m.2.ne'
    have hnpos : (n.1 : ℝ) ≠ 0 := by exact_mod_cast n.2.ne'
    have hgcdpos_nat : 0 < Nat.gcd m.1 n.1 := Nat.gcd_pos_of_pos_left n.1 m.2
    have hlcmpos_nat : 0 < Nat.lcm m.1 n.1 := Nat.lcm_pos m.2 n.2
    have hlcmdvd : Nat.lcm m.1 n.1 ∣ q := by
      exact Nat.lcm_dvd_iff.mpr ⟨hdvd m hm, hdvd n hn⟩
    have hlcmR : ((Nat.lcm m.1 n.1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast hlcmpos_nat.ne'
    rw [Nat.cast_div hlcmdvd hlcmR]
    have hgl : (Nat.gcd m.1 n.1 : ℝ) * (Nat.lcm m.1 n.1 : ℝ)
        = (m.1 : ℝ) * (n.1 : ℝ) := by
      exact_mod_cast Nat.gcd_mul_lcm m.1 n.1
    field_simp [hlcmR, hmpos, hnpos]
    linarith [hgl]
  have hsum_dsq' :
      (∑ j ∈ Finset.range q,
          (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) ^ 2)
        =
      (q : ℝ) *
      (∑ m ∈ B, ∑ n ∈ B,
        (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) := by
    rw [hsum_dsq]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro m hm
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro n hn
    rw [hlcm_cast m hm n hn]
    have hgcomm : Nat.gcd m.1 n.1 = Nat.gcd n.1 m.1 := Nat.gcd_comm m.1 n.1
    rw [hgcomm]
    ring
  calc
    (q : ℝ)⁻¹ *
        (∑ j ∈ Finset.range q,
          (1 - (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) / S) ^ 2)
        =
      (q : ℝ)⁻¹ *
        (∑ j ∈ Finset.range q,
          (1 - 2 / S *
            (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0)
            +
            (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) ^ 2 / S ^ 2)) := by
          refine congrArg _ ?_
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ = (q : ℝ)⁻¹ *
          ((q : ℝ) - 2 / S * ((q : ℝ) * S)
            + ((q : ℝ) *
              (∑ m ∈ B, ∑ n ∈ B,
                (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ)))) / S ^ 2) := by
          congr 1
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          congr 1
          · congr 1
            · simp
            · first
              | calc
                  (∑ j ∈ Finset.range q,
                      2 / S * (∑ m ∈ B,
                        if m.1 ∣ j + 1 then (1 : ℝ) else 0))
                      =
                    2 / S *
                      (∑ j ∈ Finset.range q, ∑ m ∈ B,
                        if m.1 ∣ j + 1 then (1 : ℝ) else 0) := by
                      rw [← Finset.mul_sum]
                  _ = 2 / S * ((q : ℝ) * S) := by
                      rw [hsum_d]
              | calc
                  (∑ j ∈ Finset.range q,
                      2 / S * (((B.filter fun m => m.1 ∣ j + 1).card : ℝ)))
                      =
                    2 / S *
                      (∑ j ∈ Finset.range q,
                        (((B.filter fun m => m.1 ∣ j + 1).card : ℝ))) := by
                      rw [← Finset.mul_sum]
                  _ = 2 / S * ((q : ℝ) * S) := by
                      rw [hsum_d_card]
          · congr 1
            calc
              (∑ j ∈ Finset.range q,
                  (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) ^ 2 / S ^ 2)
                  =
                (∑ j ∈ Finset.range q,
                  (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) ^ 2) / S ^ 2 := by
                  rw [← Finset.sum_div]
              _ =
                ((q : ℝ) *
                  (∑ m ∈ B, ∑ n ∈ B,
                    (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ)))) / S ^ 2 := by
                  rw [hsum_dsq']
    _ = S⁻¹ ^ 2 *
          (∑ m ∈ B, ∑ n ∈ B,
            (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - 1 := by
          field_simp [hqR, hSR] <;> ring

/- accepted add_to_file helper 3 -/
lemma nested_log_avg_gcd
    (B : Finset {n : ℕ // 0 < n}) (hB : B.Nonempty) :
    let S : ℝ := ∑ m ∈ B, 1 / (m.1 : ℝ)
    (∑ m ∈ B,
        ((∑ n ∈ B, ((Nat.gcd n.1 m.1 : ℝ) - 1) / (n.1 : ℝ)) / S)
          / (m.1 : ℝ)) / S
      =
    S⁻¹ ^ 2 *
      (∑ m ∈ B, ∑ n ∈ B,
        (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - 1 := by
  classical
  intro S
  have hS : 0 < S := by
    apply Finset.sum_pos _ hB
    intro m hm
    exact one_div_pos.mpr (by exact_mod_cast m.2)
  have hS0 : S ≠ 0 := hS.ne'
  have h_inner : ∀ m ∈ B,
      (∑ n ∈ B, ((Nat.gcd n.1 m.1 : ℝ) - 1) / (n.1 : ℝ))
        = (∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S := by
    intro m hm
    calc
      (∑ n ∈ B, ((Nat.gcd n.1 m.1 : ℝ) - 1) / (n.1 : ℝ))
          = ∑ n ∈ B,
            ((Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ) - 1 / (n.1 : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            ring
      _ = (∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S := by
            rw [Finset.sum_sub_distrib]
  have h_factor :
      (∑ m ∈ B,
          (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / S)
            / (m.1 : ℝ)) / S
        =
      S⁻¹ ^ 2 * ∑ m ∈ B,
        (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / (m.1 : ℝ)) := by
    calc
      (∑ m ∈ B,
          (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / S)
            / (m.1 : ℝ)) / S
          =
        ∑ m ∈ B,
          ((((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / S)
            / (m.1 : ℝ)) / S := by
          rw [Finset.sum_div]
      _ =
        ∑ m ∈ B,
          S⁻¹ ^ 2 *
            (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / (m.1 : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          ring
      _ = S⁻¹ ^ 2 * ∑ m ∈ B,
          (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / (m.1 : ℝ)) := by
          rw [← Finset.mul_sum]
  have h_split :
      (∑ m ∈ B,
          (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / (m.1 : ℝ)))
        =
      (∑ m ∈ B, ∑ n ∈ B,
          (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - S ^ 2 := by
    calc
      (∑ m ∈ B,
          (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / (m.1 : ℝ)))
          =
        ∑ m ∈ B,
          (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) / (m.1 : ℝ))
            - S / (m.1 : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          ring
      _ =
        (∑ m ∈ B,
            ((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) / (m.1 : ℝ)))
          - ∑ m ∈ B, S / (m.1 : ℝ) := by
          rw [Finset.sum_sub_distrib]
      _ =
      (∑ m ∈ B, ∑ n ∈ B,
          (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - S ^ 2 := by
          congr 1
          · refine Finset.sum_congr rfl ?_
            intro m hm
            rw [Finset.sum_div]
            refine Finset.sum_congr rfl ?_
            intro n hn
            ring
          · calc
              (∑ m ∈ B, S / (m.1 : ℝ))
                  = S * (∑ m ∈ B, 1 / (m.1 : ℝ)) := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl ?_
                  intro m hm
                  ring
              _ = S ^ 2 := by
                  change S * S = S ^ 2
                  ring
  have hcancel : S⁻¹ ^ 2 * S ^ 2 = 1 := by
    have h : S⁻¹ * S = 1 := inv_mul_cancel₀ hS0
    calc
      S⁻¹ ^ 2 * S ^ 2 = (S⁻¹ * S) ^ 2 := by ring
      _ = 1 ^ 2 := by rw [h]
      _ = 1 := by norm_num
  calc
    (∑ m ∈ B,
        ((∑ n ∈ B, ((Nat.gcd n.1 m.1 : ℝ) - 1) / (n.1 : ℝ)) / S)
          / (m.1 : ℝ)) / S
        =
      (∑ m ∈ B,
        (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / S)
          / (m.1 : ℝ)) / S := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro m hm
        rw [h_inner m hm]
    _ = S⁻¹ ^ 2 * ∑ m ∈ B,
          (((∑ n ∈ B, (Nat.gcd n.1 m.1 : ℝ) / (n.1 : ℝ)) - S) / (m.1 : ℝ)) :=
        h_factor
    _ = S⁻¹ ^ 2 *
          ((∑ m ∈ B, ∑ n ∈ B,
            (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - S ^ 2) := by
        rw [h_split]
    _ = S⁻¹ ^ 2 *
          (∑ m ∈ B, ∑ n ∈ B,
            (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - 1 := by
        calc
          S⁻¹ ^ 2 *
              ((∑ m ∈ B, ∑ n ∈ B,
                (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - S ^ 2)
              =
            S⁻¹ ^ 2 *
              (∑ m ∈ B, ∑ n ∈ B,
                (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ)))
              - S⁻¹ ^ 2 * S ^ 2 := by
            ring
          _ = S⁻¹ ^ 2 *
              (∑ m ∈ B, ∑ n ∈ B,
                (Nat.gcd n.1 m.1 : ℝ) / ((n.1 : ℝ) * (m.1 : ℝ))) - 1 := by
            rw [hcancel]

/- accepted add_to_file helper 4 -/
lemma sum_range_blocks_le
    (f W : ℕ → ℝ) (q Q r : ℕ)
    (hW : ∀ j, 0 ≤ W j)
    (hblock : ∀ i j, j < q → f (i * q + j) ≤ W j)
    (htail : ∀ j, j < r → f (Q * q + j) ≤ W j)
    (hr : r ≤ q) :
    (∑ j ∈ Finset.range (Q * q + r), f j) ≤ (Q + 1 : ℝ) * ∑ j ∈ Finset.range q, W j := by
  classical
  have hfull : ∀ Q : ℕ,
      (∑ j ∈ Finset.range (Q * q), f j) ≤ (Q : ℝ) * ∑ j ∈ Finset.range q, W j := by
    intro Q
    induction Q with
    | zero => simp
    | succ Q ih =>
        rw [Nat.succ_mul, Finset.sum_range_add]
        calc
          (∑ j ∈ Finset.range (Q * q), f j) +
              (∑ j ∈ Finset.range q, f (Q * q + j))
              ≤ (Q : ℝ) * (∑ j ∈ Finset.range q, W j) +
                  (∑ j ∈ Finset.range q, W j) := by
                exact add_le_add ih (Finset.sum_le_sum (fun j hj => hblock Q j (Finset.mem_range.mp hj)))
          _ = ((Q + 1 : ℕ) : ℝ) * ∑ j ∈ Finset.range q, W j := by
                norm_num
                ring
  rw [Finset.sum_range_add]
  calc
    (∑ j ∈ Finset.range (Q * q), f j) +
        (∑ j ∈ Finset.range r, f (Q * q + j))
        ≤ (Q : ℝ) * (∑ j ∈ Finset.range q, W j) +
            (∑ j ∈ Finset.range q, W j) := by
          refine add_le_add (hfull Q) ?_
          calc
            (∑ j ∈ Finset.range r, f (Q * q + j))
                ≤ ∑ j ∈ Finset.range r, W j :=
                Finset.sum_le_sum (fun j hj => htail j (Finset.mem_range.mp hj))
            _ ≤ ∑ j ∈ Finset.range q, W j := by
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · intro j hj
                  exact Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) hr)
                · intro j hj _
                  exact hW j
    _ = (Q + 1 : ℝ) * ∑ j ∈ Finset.range q, W j := by
          ring

/- accepted add_to_file helper 5 -/
lemma weighted_prefix_bound_generic
    (a : {n : ℕ // 0 < n} → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (q : ℕ) (hq : 0 < q) (w : ℕ → ℝ)
    (hperiod : ∀ i j, w (i * q + j) = w j)
    (N : ℕ) (hN : 0 < N) :
    let T : ℝ := ∑ j ∈ Finset.range q, |w j|
    ‖(N : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
        a ⟨j + 1, Nat.zero_lt_succ j⟩ * (w j : ℂ)‖
      ≤
    Real.sqrt ((q : ℝ)⁻¹ * ∑ j ∈ Finset.range q, (w j) ^ 2) + T / N := by
  classical
  intro T
  let Q : ℕ := N / q
  let r : ℕ := N % q
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hqr : N = Q * q + r := by
    calc
      N = q * (N / q) + N % q := (Nat.div_add_mod N q).symm
      _ = Q * q + r := by
        dsimp [Q, r]
        rw [mul_comm]
  have hr : r ≤ q := by
    exact le_of_lt (Nat.mod_lt N hq)
  have hTnonneg : 0 ≤ T := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hterm : ∀ i j, j < q →
      ‖a ⟨(i * q + j) + 1, Nat.zero_lt_succ _⟩ * (w (i * q + j) : ℂ)‖ ≤ |w j| := by
    intro i j hj
    rw [hperiod i j]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg _) (ha _)
  have hterm_tail : ∀ j, j < r →
      ‖a ⟨(Q * q + j) + 1, Nat.zero_lt_succ _⟩ * (w (Q * q + j) : ℂ)‖ ≤ |w j| := by
    intro j hj
    rw [hperiod Q j]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg _) (ha _)
  have hsum_norm :
      (∑ j ∈ Finset.range N,
          ‖a ⟨j + 1, Nat.zero_lt_succ j⟩ * (w j : ℂ)‖)
        ≤ (Q + 1 : ℝ) * T := by
    conv_lhs => rw [hqr]
    exact sum_range_blocks_le
      (fun j => ‖a ⟨j + 1, Nat.zero_lt_succ j⟩ * (w j : ℂ)‖)
      (fun j => |w j|) q Q r
      (fun j => abs_nonneg _) hterm hterm_tail hr
  have hmain0 :
      ‖(N : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
          a ⟨j + 1, Nat.zero_lt_succ j⟩ * (w j : ℂ)‖
        ≤ (N : ℝ)⁻¹ * ((Q + 1 : ℝ) * T) := by
    rw [norm_mul]
    have hn : ‖(N : ℂ)⁻¹‖ = (N : ℝ)⁻¹ := by
      simp [norm_inv]
    rw [hn]
    exact mul_le_mul_of_nonneg_left
      ((norm_sum_le _ _).trans hsum_norm)
      (inv_nonneg.mpr (by positivity))
  have hQle : (Q : ℝ) / N ≤ 1 / q := by
    have hmul : Q * q ≤ N := Nat.div_mul_le_self N q
    have hmulR : (Q : ℝ) * q ≤ N := by exact_mod_cast hmul
    have hqposR : (0 : ℝ) < q := by exact_mod_cast hq
    have hNposR : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_le_div_iff₀ hNposR hqposR]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmulR
  have hfactor :
      (N : ℝ)⁻¹ * ((Q + 1 : ℝ) * T) ≤ (1 / q + 1 / N) * T := by
    have hfrac : ((Q + 1 : ℝ)) / N ≤ 1 / q + 1 / N := by
      calc
        ((Q + 1 : ℝ)) / N = (Q : ℝ) / N + 1 / N := by ring
        _ ≤ 1 / q + 1 / N := add_le_add hQle le_rfl
    calc
      (N : ℝ)⁻¹ * ((Q + 1 : ℝ) * T)
          = ((Q + 1 : ℝ) / N) * T := by ring
      _ ≤ (1 / q + 1 / N) * T :=
          mul_le_mul_of_nonneg_right hfrac hTnonneg
  have hcs : T / q ≤
      Real.sqrt ((q : ℝ)⁻¹ * ∑ j ∈ Finset.range q, (w j) ^ 2) := by
    have hsq := sq_sum_le_card_mul_sum_sq (s := Finset.range q) (f := fun j => |w j|)
    have hsq' : T ^ 2 ≤ (q : ℝ) * ∑ j ∈ Finset.range q, (w j) ^ 2 := by
      simpa [T, sq_abs] using hsq
    apply Real.le_sqrt_of_sq_le
    calc
      (T / q) ^ 2 = T ^ 2 / (q : ℝ) ^ 2 := by ring
      _ ≤ ((q : ℝ) * ∑ j ∈ Finset.range q, (w j) ^ 2) / (q : ℝ) ^ 2 := by
          exact div_le_div_of_nonneg_right hsq' (sq_nonneg _)
      _ = (q : ℝ)⁻¹ * ∑ j ∈ Finset.range q, (w j) ^ 2 := by
          field_simp [hqR]
  calc
    ‖(N : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
        a ⟨j + 1, Nat.zero_lt_succ j⟩ * (w j : ℂ)‖
        ≤ (N : ℝ)⁻¹ * ((Q + 1 : ℝ) * T) := hmain0
    _ ≤ (1 / q + 1 / N) * T := hfactor
    _ = T / q + T / N := by ring
    _ ≤ Real.sqrt ((q : ℝ)⁻¹ * ∑ j ∈ Finset.range q, (w j) ^ 2) + T / N :=
        add_le_add hcs le_rfl

/- accepted add_to_file helper 6 -/
lemma local_average_mul_approx
    (a : {n : ℕ // 0 < n} → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (m N : ℕ) (hm : 0 < m) (hN : 0 < N) :
    let A : ℕ → ({n : ℕ // 0 < n} → ℂ) → ℂ := fun M c ↦
      (M : ℂ)⁻¹ * ∑ k ∈ Finset.range M, c ⟨k + 1, Nat.zero_lt_succ k⟩
    ‖A (N / m) (fun k ↦ a ⟨m * k.1, Nat.mul_pos hm k.2⟩) / (m : ℂ)
        - (N : ℂ)⁻¹ * ∑ k ∈ Finset.range (N / m),
            a ⟨m * (k + 1), Nat.mul_pos hm (Nat.zero_lt_succ k)⟩‖
      ≤ 1 / (N : ℝ) := by
  classical
  intro A
  let q : ℕ := N / m
  by_cases hq : q = 0
  · simp [A, q, hq]
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    let X : ℂ := ∑ k ∈ Finset.range q,
      a ⟨m * (k + 1), Nat.mul_pos hm (Nat.zero_lt_succ k)⟩
    have hrewrite :
        A q (fun k ↦ a ⟨m * k.1, Nat.mul_pos hm k.2⟩) / (m : ℂ)
          - (N : ℂ)⁻¹ * X
        =
        (((q : ℂ)⁻¹ / (m : ℂ) - (N : ℂ)⁻¹) * X) := by
      simp [A, X]
      ring
    have hX : ‖X‖ ≤ q := by
      calc
        ‖X‖ ≤ ∑ k ∈ Finset.range q,
            ‖a ⟨m * (k + 1), Nat.mul_pos hm (Nat.zero_lt_succ k)⟩‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.range q, (1 : ℝ) := Finset.sum_le_sum (fun k _ => ha _)
        _ = q := by simp
    have hqm : q * m ≤ N := Nat.div_mul_le_self N m
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have hqposr : (0 : ℝ) < q := by exact_mod_cast hqpos
    have hNposr : (0 : ℝ) < N := by exact_mod_cast hN
    have hdelta :
        ((q : ℂ)⁻¹ / (m : ℂ) - (N : ℂ)⁻¹)
          =
        (((((N - q * m : ℕ) : ℝ) / (((q : ℝ) * m) * N)) : ℝ) : ℂ) := by
      have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hqpos.ne'
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have hcast : (((N - q * m : ℕ) : ℝ)) = (N : ℝ) - (q : ℝ) * m := by
        simpa [Nat.cast_mul] using
          (Nat.cast_sub hqm : (((N - q*m:ℕ):ℝ)) = (N:ℝ) - (q*m:ℕ))
      have hreal : ((q : ℝ)⁻¹ / m - (N : ℝ)⁻¹)
          = (((N - q*m:ℕ):ℝ)) / ((q:ℝ)*m*N) := by
        rw [hcast]
        field_simp [hq0, hm0, hN0]
      rw [show ((q : ℂ)⁻¹ / (m : ℂ) - (N : ℂ)⁻¹)
          = ((((q : ℝ)⁻¹ / m - (N : ℝ)⁻¹) : ℝ) : ℂ) by simp]
      exact congrArg Complex.ofReal hreal
    have hbound :
        (q : ℝ) * ‖((q : ℂ)⁻¹ / (m : ℂ) - (N : ℂ)⁻¹)‖ ≤ 1 / N := by
      rw [hdelta, Complex.norm_real, Real.norm_eq_abs]
      have hnon : 0 ≤ (((N - q * m : ℕ) : ℝ) / (((q : ℝ) * m) * N)) := by positivity
      rw [abs_of_nonneg hnon]
      have hcast : (((N - q * m : ℕ) : ℝ)) = (N : ℝ) - (q : ℝ) * m := by
        simpa [Nat.cast_mul] using
          (Nat.cast_sub hqm : (((N - q*m:ℕ):ℝ)) = (N:ℝ) - (q*m:ℕ))
      rw [hcast]
      calc
        q * ((N - q * m) / (q * m * N))
            = ((N : ℝ) - q * m) / (m * N) := by
              field_simp [hqposr.ne', hmpos.ne', hNposr.ne']
        _ ≤ 1 / N := by
              rw [div_le_iff₀ (mul_pos hmpos hNposr)]
              field_simp [hNposr.ne']
              have hmod : N - q * m = N % m := by
                dsimp [q]
                rw [Nat.mod_eq_sub_mul_div]
                rw [mul_comm]
              have hlt : N - q * m < m := by
                rw [hmod]
                exact Nat.mod_lt N hm
              have hltR : (N : ℝ) - q * m < m := by
                rw [← hcast]
                exact_mod_cast hlt
              linarith
    calc
      ‖A q (fun k ↦ a ⟨m * k.1, Nat.mul_pos hm k.2⟩) / (m : ℂ)
          - (N : ℂ)⁻¹ * X‖
          = ‖((q : ℂ)⁻¹ / (m : ℂ) - (N : ℂ)⁻¹) * X‖ := by rw [hrewrite]
      _ ≤ ‖((q : ℂ)⁻¹ / (m : ℂ) - (N : ℂ)⁻¹)‖ * ‖X‖ := norm_mul_le _ _
      _ ≤ ‖((q : ℂ)⁻¹ / (m : ℂ) - (N : ℂ)⁻¹)‖ * q :=
          mul_le_mul_of_nonneg_left hX (norm_nonneg _)
      _ = (q : ℝ) * ‖((q : ℂ)⁻¹ / (m : ℂ) - (N : ℂ)⁻¹)‖ := by ring
      _ ≤ 1 / N := hbound

/- accepted add_to_file helper 7 -/
lemma global_local_approx
    (B : Finset {n : ℕ // 0 < n}) (hB : B.Nonempty)
    (a : {n : ℕ // 0 < n} → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1)
    (N : ℕ) (hN : 0 < N) :
    let A : ℕ → ({n : ℕ // 0 < n} → ℂ) → ℂ := fun M c ↦
      (M : ℂ)⁻¹ * ∑ k ∈ Finset.range M, c ⟨k + 1, Nat.zero_lt_succ k⟩
    let S : ℝ := ∑ m ∈ B, 1 / (m.1 : ℝ)
    let Sℂ : ℂ := ∑ m ∈ B, 1 / (m.1 : ℂ)
    let actual : ℂ := ∑ m ∈ B,
      A (N / m.1) (fun k ↦ a ⟨m.1 * k.1, Nat.mul_pos m.2 k.2⟩) / (m.1 : ℂ)
    let ideal : ℂ := ∑ m ∈ B,
      (N : ℂ)⁻¹ * ∑ k ∈ Finset.range (N / m.1),
        a ⟨m.1 * (k + 1), Nat.mul_pos m.2 (Nat.zero_lt_succ k)⟩
    ‖(A N a - actual / Sℂ) - (A N a - ideal / Sℂ)‖
      ≤ (B.card : ℝ) / ((N : ℝ) * S) := by
  classical
  intro A S Sℂ actual ideal
  have hS : 0 < S := by
    apply Finset.sum_pos _ hB
    intro m hm
    exact one_div_pos.mpr (by exact_mod_cast m.2)
  have hScast : Sℂ = (S : ℂ) := by
    simp [Sℂ, S]
  have hdiff :
      (A N a - actual / Sℂ) - (A N a - ideal / Sℂ)
        = (ideal - actual) / Sℂ := by
    ring
  rw [hdiff, hScast]
  have hnormden : ‖(S : ℂ)‖ = S := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS]
  rw [norm_div, hnormden]
  have hsum :
      ‖ideal - actual‖ ≤ (B.card : ℝ) / N := by
    calc
      ‖ideal - actual‖ ≤ ∑ m ∈ B,
          ‖(N : ℂ)⁻¹ * ∑ k ∈ Finset.range (N / m.1),
              a ⟨m.1 * (k + 1), Nat.mul_pos m.2 (Nat.zero_lt_succ k)⟩
            -
            A (N / m.1) (fun k ↦ a ⟨m.1 * k.1, Nat.mul_pos m.2 k.2⟩) / (m.1 : ℂ)‖ := by
            simpa [ideal, actual, Finset.sum_sub_distrib] using
              (norm_sum_le B (fun m =>
                (N : ℂ)⁻¹ * ∑ k ∈ Finset.range (N / m.1),
                  a ⟨m.1 * (k + 1), Nat.mul_pos m.2 (Nat.zero_lt_succ k)⟩
                -
                A (N / m.1) (fun k ↦ a ⟨m.1 * k.1, Nat.mul_pos m.2 k.2⟩) / (m.1 : ℂ)))
      _ ≤ ∑ m ∈ B, 1 / (N : ℝ) := by
            refine Finset.sum_le_sum ?_
            intro m hm
            rw [norm_sub_rev]
            exact local_average_mul_approx a ha m.1 N m.2 hN
      _ = (B.card : ℝ) / N := by
            rw [Finset.sum_const]
            simp [nsmul_eq_mul]
            ring
  have hSnonneg : 0 ≤ S := le_of_lt hS
  calc
    ‖ideal - actual‖ / S ≤ ((B.card : ℝ) / N) / S :=
      div_le_div_of_nonneg_right hsum hSnonneg
    _ = (B.card : ℝ) / ((N : ℝ) * S) := by ring

/- accepted add_to_file helper 8 -/
lemma weighted_prefix_eq
    (B : Finset {n : ℕ // 0 < n})
    (a : {n : ℕ // 0 < n} → ℂ)
    (N : ℕ) :
    let A : ℕ → ({n : ℕ // 0 < n} → ℂ) → ℂ := fun M c ↦
      (M : ℂ)⁻¹ * ∑ k ∈ Finset.range M, c ⟨k + 1, Nat.zero_lt_succ k⟩
    let S : ℝ := ∑ m ∈ B, 1 / (m.1 : ℝ)
    let Sℂ : ℂ := ∑ m ∈ B, 1 / (m.1 : ℂ)
    let ideal : ℂ := ∑ m ∈ B,
      (N : ℂ)⁻¹ * ∑ k ∈ Finset.range (N / m.1),
        a ⟨m.1 * (k + 1), Nat.mul_pos m.2 (Nat.zero_lt_succ k)⟩
    let w : ℕ → ℝ := fun j ↦
      1 - (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) / S
    A N a - ideal / Sℂ
      =
    (N : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
      a ⟨j + 1, Nat.zero_lt_succ j⟩ * (w j : ℂ) := by
  classical
  intro A S Sℂ ideal w
  have hScast : Sℂ = (S : ℂ) := by
    simp [Sℂ, S]
  have hlocal : ∀ m ∈ B,
      (∑ k ∈ Finset.range (N / m.1),
          a ⟨m.1 * (k + 1), Nat.mul_pos m.2 (Nat.zero_lt_succ k)⟩)
        =
      ∑ j ∈ Finset.range N,
        if m.1 ∣ j + 1 then a ⟨j + 1, Nat.zero_lt_succ j⟩ else 0 := by
    intro m hm
    exact sum_range_mul_eq_sum_filter m.1 N m.2 a
  have hideal :
      ideal =
        (N : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
          a ⟨j + 1, Nat.zero_lt_succ j⟩ *
            ((∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) : ℂ) := by
    calc
      ideal = ∑ m ∈ B, (N : ℂ)⁻¹ *
          (∑ j ∈ Finset.range N,
            if m.1 ∣ j + 1 then a ⟨j + 1, Nat.zero_lt_succ j⟩ else 0) := by
          refine Finset.sum_congr (M := ℂ) rfl ?_
          intro m hm
          rw [hlocal m hm]
      _ = (N : ℂ)⁻¹ * ∑ m ∈ B, ∑ j ∈ Finset.range N,
          (if m.1 ∣ j + 1 then a ⟨j + 1, Nat.zero_lt_succ j⟩ else 0) := by
          rw [Finset.mul_sum]
      _ = (N : ℂ)⁻¹ * ∑ j ∈ Finset.range N, ∑ m ∈ B,
          (if m.1 ∣ j + 1 then a ⟨j + 1, Nat.zero_lt_succ j⟩ else 0) := by
          exact congrArg _ (Finset.sum_comm (s := B) (t := Finset.range N)
            (f := fun m j => if m.1 ∣ j + 1 then a ⟨j + 1, Nat.zero_lt_succ j⟩ else 0))
      _ = (N : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
          a ⟨j + 1, Nat.zero_lt_succ j⟩ *
            ((∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) : ℂ) := by
          refine congrArg _ ?_
          refine Finset.sum_congr (M := ℂ) rfl ?_
          intro j hj
          rw [Finset.mul_sum]
          refine Finset.sum_congr (M := ℂ) rfl ?_
          intro m hm
          by_cases h : m.1 ∣ j + 1 <;> simp [h]
  let X : ℕ → ℂ := fun j => a ⟨j + 1, Nat.zero_lt_succ j⟩
  let Y : ℕ → ℂ := fun j =>
    a ⟨j + 1, Nat.zero_lt_succ j⟩ *
      ((∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) : ℂ)
  have hsub :
      (∑ j ∈ Finset.range N, (X j - Y j / (S : ℂ)))
        = (∑ j ∈ Finset.range N, X j) - ∑ j ∈ Finset.range N, Y j / (S : ℂ) := by
    exact Finset.sum_sub_distrib (ι := ℕ) (G := ℂ) (s := Finset.range N)
      (f := X) (g := fun j => Y j / (S : ℂ))
  have hdiv :
      ((∑ j ∈ Finset.range N, Y j) / (S : ℂ))
        = ∑ j ∈ Finset.range N, Y j / (S : ℂ) := by
    exact Finset.sum_div (ι := ℕ) (K := ℂ) (s := Finset.range N)
      (f := Y) (a := (S : ℂ))
  have hweighted :
      (∑ j ∈ Finset.range N, X j * (w j : ℂ))
        = (∑ j ∈ Finset.range N, X j) - (S : ℂ)⁻¹ * ∑ j ∈ Finset.range N, Y j := by
    calc
      (∑ j ∈ Finset.range N, X j * (w j : ℂ))
          = ∑ j ∈ Finset.range N, (X j - Y j / (S : ℂ)) := by
            refine Finset.sum_congr (M := ℂ) rfl ?_
            intro j hj
            simp [X, Y, w]
            ring
      _ = (∑ j ∈ Finset.range N, X j) - ∑ j ∈ Finset.range N, Y j / (S : ℂ) := hsub
      _ = (∑ j ∈ Finset.range N, X j) - (∑ j ∈ Finset.range N, Y j) / (S : ℂ) := by
            rw [hdiv]
      _ = (∑ j ∈ Finset.range N, X j) - (S : ℂ)⁻¹ * ∑ j ∈ Finset.range N, Y j := by
            ring
  rw [hideal, hScast, hweighted]
  change ((N : ℂ)⁻¹ * ∑ j ∈ Finset.range N, X j)
      - (((N : ℂ)⁻¹ * ∑ j ∈ Finset.range N, Y j) / (S : ℂ))
      =
    (N : ℂ)⁻¹ *
      ((∑ j ∈ Finset.range N, X j) - (S : ℂ)⁻¹ * ∑ j ∈ Finset.range N, Y j)
  ring

/- verified submission -/
theorem logarithmic_average_bound
    (B : Finset {n : ℕ // 0 < n}) (hB : B.Nonempty)
    (a : {n : ℕ // 0 < n} → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) :
    let A : ℕ → ({n : ℕ // 0 < n} → ℂ) → ℂ := fun N c ↦
      (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, c ⟨k + 1, Nat.zero_lt_succ k⟩
    let Lℂ : ({n : ℕ // 0 < n} → ℂ) → ℂ := fun h ↦
      (∑ m ∈ B, h m / (m.1 : ℂ)) / (∑ m ∈ B, 1 / (m.1 : ℂ))
    let Lℝ : ({n : ℕ // 0 < n} → ℝ) → ℝ := fun h ↦
      (∑ m ∈ B, h m / (m.1 : ℝ)) / (∑ m ∈ B, 1 / (m.1 : ℝ))
    Filter.limsup
        (fun N : ℕ ↦ ‖A N a - Lℂ (fun m ↦
          A (N / m.1) (fun k ↦ a ⟨m.1 * k.1, Nat.mul_pos m.2 k.2⟩))‖)
        Filter.atTop ≤
      Real.sqrt (Lℝ (fun m ↦ Lℝ (fun n ↦ (Nat.gcd n.1 m.1 : ℝ) - 1))) := by
  classical
  intro A Lℂ Lℝ
  let q : ℕ := ∏ m ∈ B, m.1
  let S : ℝ := ∑ m ∈ B, 1 / (m.1 : ℝ)
  let Sℂ : ℂ := ∑ m ∈ B, 1 / (m.1 : ℂ)
  let w : ℕ → ℝ := fun j ↦
    1 - (∑ m ∈ B, if m.1 ∣ j + 1 then (1 : ℝ) else 0) / S
  let T : ℝ := ∑ j ∈ Finset.range q, |w j|
  let target : ℝ := Lℝ (fun m ↦ Lℝ (fun n ↦ (Nat.gcd n.1 m.1 : ℝ) - 1))
  let K : ℝ := T + (B.card : ℝ) / S
  have hq : 0 < q := Finset.prod_pos (fun m _ => m.2)
  have hS : 0 < S := by
    apply Finset.sum_pos _ hB
    intro m hm
    exact one_div_pos.mpr (by exact_mod_cast m.2)
  have hT : 0 ≤ T := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hperiod : ∀ i j, w (i * q + j) = w j := by
    intro i j
    dsimp [w]
    congr 2
    refine Finset.sum_congr rfl ?_
    intro m hm
    have hmq : m.1 ∣ q := Finset.dvd_prod_of_mem (fun x => x.1) hm
    have hmiq : m.1 ∣ i * q := dvd_trans hmq (dvd_mul_left q i)
    have hiff : m.1 ∣ i * q + j + 1 ↔ m.1 ∣ j + 1 := by
      have h := Nat.dvd_add_iff_right hmiq (n := j + 1)
      simpa [add_assoc, add_comm, add_left_comm] using h.symm
    simp [hiff]
  have htarget_period :
      target =
        (q : ℝ)⁻¹ * ∑ j ∈ Finset.range q, (w j) ^ 2 := by
    have hp := period_weight_square_avg B hB
    have hn := nested_log_avg_gcd B hB
    dsimp [target, Lℝ, q, S, w]
    rw [hp, hn]
  have hboundN : ∀ N, 0 < N →
      ‖A N a - Lℂ (fun m ↦
          A (N / m.1) (fun k ↦ a ⟨m.1 * k.1, Nat.mul_pos m.2 k.2⟩))‖
        ≤ Real.sqrt target + K / N := by
    intro N hN
    let actual : ℂ := Lℂ (fun m ↦
      A (N / m.1) (fun k ↦ a ⟨m.1 * k.1, Nat.mul_pos m.2 k.2⟩))
    let ideal : ℂ := ∑ m ∈ B,
      (N : ℂ)⁻¹ * ∑ k ∈ Finset.range (N / m.1),
        a ⟨m.1 * (k + 1), Nat.mul_pos m.2 (Nat.zero_lt_succ k)⟩
    let adj : ℂ := A N a - ideal / Sℂ
    have happ :
        ‖(A N a - actual) - adj‖ ≤ (B.card : ℝ) / ((N : ℝ) * S) := by
      have hg := global_local_approx B hB a ha N hN
      dsimp [actual, adj, ideal, Lℂ, Sℂ, A] at *
      exact hg
    have hadj :
        adj = (N : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
          a ⟨j + 1, Nat.zero_lt_succ j⟩ * (w j : ℂ) := by
      have hw := weighted_prefix_eq B a N
      dsimp [adj, ideal, S, Sℂ, w, A] at *
      exact hw
    have hweighted :
        ‖adj‖ ≤ Real.sqrt target + T / N := by
      have hp := weighted_prefix_bound_generic a ha q hq w hperiod N hN
      dsimp [T] at hp
      rw [hadj]
      calc
        ‖(N : ℂ)⁻¹ * ∑ j ∈ Finset.range N,
            a ⟨j + 1, Nat.zero_lt_succ j⟩ * (w j : ℂ)‖
            ≤ Real.sqrt ((q : ℝ)⁻¹ * ∑ j ∈ Finset.range q, (w j) ^ 2) + T / N := hp
        _ = Real.sqrt target + T / N := by rw [htarget_period]
    have htri :
        ‖A N a - actual‖ ≤ ‖adj‖ + ‖(A N a - actual) - adj‖ := by
      calc
        ‖A N a - actual‖ = ‖adj + ((A N a - actual) - adj)‖ := by
          congr 1
          abel
        _ ≤ ‖adj‖ + ‖(A N a - actual) - adj‖ := norm_add_le _ _
    calc
      ‖A N a - actual‖ ≤ ‖adj‖ + ‖(A N a - actual) - adj‖ := htri
      _ ≤ (Real.sqrt target + T / N) + (B.card : ℝ) / ((N : ℝ) * S) :=
          add_le_add hweighted happ
      _ = Real.sqrt target + K / N := by
          dsimp [K]
          field_simp [hS.ne']
          ring
  have hmain : ∀ ε : ℝ, 0 < ε →
      Filter.limsup
        (fun N : ℕ ↦ ‖A N a - Lℂ (fun m ↦
          A (N / m.1) (fun k ↦ a ⟨m.1 * k.1, Nat.mul_pos m.2 k.2⟩))‖)
        Filter.atTop ≤ Real.sqrt target + ε := by
    intro ε hε
    have hlim : Filter.Tendsto (fun N : ℕ => K / (N : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat K
    have hsmall : ∀ᶠ N : ℕ in Filter.atTop, K / (N : ℝ) < ε :=
      hlim.eventually_lt_const hε
    have hpos : ∀ᶠ N : ℕ in Filter.atTop, 0 < N :=
      (Filter.eventually_ge_atTop 1).mono (fun N hN => hN)
    have hev : ∀ᶠ N : ℕ in Filter.atTop,
        ‖A N a - Lℂ (fun m ↦
          A (N / m.1) (fun k ↦ a ⟨m.1 * k.1, Nat.mul_pos m.2 k.2⟩))‖
          ≤ Real.sqrt target + ε := by
      filter_upwards [hpos, hsmall] with N hN hs
      exact (hboundN N hN).trans (add_le_add le_rfl hs.le)
    exact Filter.limsup_le_of_le
      (Filter.isCoboundedUnder_le_of_eventually_le Filter.atTop
        (Filter.Eventually.of_forall (fun N => norm_nonneg _))) hev
  exact le_of_forall_pos_le_add hmain

end Rollout_p1089_logarithmic_average_bound

#check_dependency_graph "Rollout_p1089_logarithmic_average_bound.logarithmic_average_bound" against "{\"edges\":[{\"conclusion\":{\"name\":\"hq\",\"statement\":\"0 < q\"},\"graphEdgeId\":\"h_001_hq\",\"premises\":[],\"rawEdgeId\":\"telescope_14\"},{\"conclusion\":{\"name\":\"hS\",\"statement\":\"0 < S\"},\"graphEdgeId\":\"h_002_hs\",\"premises\":[{\"name\":\"hB\",\"statement\":\"B.Nonempty\"}],\"rawEdgeId\":\"telescope_15\"},{\"conclusion\":{\"name\":\"hperiod\",\"statement\":\"∀ (i j : ℕ), w (i * q + j) = w j\"},\"graphEdgeId\":\"h_005_hperiod\",\"premises\":[],\"rawEdgeId\":\"telescope_18\"},{\"conclusion\":{\"name\":\"htarget_period\",\"statement\":\"target = (↑q)⁻¹ * ∑ j ∈ Finset.range q, w j ^ 2\"},\"graphEdgeId\":\"h_006_htarget_period\",\"premises\":[{\"name\":\"hB\",\"statement\":\"B.Nonempty\"}],\"rawEdgeId\":\"telescope_19\"},{\"conclusion\":{\"name\":\"hboundN\",\"statement\":\"∀ (N : ℕ), 0 < N → ‖A N a - Lℂ fun m => A (N / ↑m) fun k => a ⟨↑m * ↑k, ⋯⟩‖ ≤ √target + K / ↑N\"},\"graphEdgeId\":\"h_007_hboundn\",\"premises\":[{\"name\":\"hB\",\"statement\":\"B.Nonempty\"},{\"name\":\"ha\",\"statement\":\"∀ (n : { n // 0 < n }), ‖a n‖ ≤ 1\"},{\"name\":\"hq\",\"statement\":\"0 < q\"},{\"name\":\"hS\",\"statement\":\"0 < S\"},{\"name\":\"hperiod\",\"statement\":\"∀ (i j : ℕ), w (i * q + j) = w j\"},{\"name\":\"htarget_period\",\"statement\":\"target = (↑q)⁻¹ * ∑ j ∈ Finset.range q, w j ^ 2\"}],\"rawEdgeId\":\"telescope_20\"},{\"conclusion\":{\"name\":\"hmain\",\"statement\":\"∀ (ε : ℝ), 0 < ε → Filter.limsup (fun N => ‖A N a - Lℂ fun m => A (N / ↑m) fun k => a ⟨↑m * ↑k, ⋯⟩‖) Filter.atTop ≤ √target + ε\"},\"graphEdgeId\":\"h_008_hmain\",\"premises\":[{\"name\":\"hboundN\",\"statement\":\"∀ (N : ℕ), 0 < N → ‖A N a - Lℂ fun m => A (N / ↑m) fun k => a ⟨↑m * ↑k, ⋯⟩‖ ≤ √target + K / ↑N\"}],\"rawEdgeId\":\"telescope_21\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"Filter.limsup (fun N => ‖A N a - Lℂ fun m => A (N / ↑m) fun k => a ⟨↑m * ↑k, ⋯⟩‖) Filter.atTop ≤ √(Lℝ fun m => Lℝ fun n => ↑((↑n).gcd ↑m) - 1)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hmain\",\"statement\":\"∀ (ε : ℝ), 0 < ε → Filter.limsup (fun N => ‖A N a - Lℂ fun m => A (N / ↑m) fun k => a ⟨↑m * ↑k, ⋯⟩‖) Filter.atTop ≤ √target + ε\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1089_logarithmic_average_bound\",\"reconstructedProofSha256\":\"c6fbcb13365678ea7f4ec991d10ff76066d8d782cca0b446b954f8b737f3882f\",\"selectedEdgeCount\":7,\"theoremName\":\"Rollout_p1089_logarithmic_average_bound.logarithmic_average_bound\",\"topologySha256\":\"3b0de1941c8929d9339458ece58933b5a7be4f50c1f8629973513c008d4dd8c3\"}"

namespace Rollout_p1136_entropy_number_approximation

-- graph_id: p1136_entropy_number_approximation
-- topology_sha256: 35962ed6d9b2ce9c224f8534f09d23127dfd835d3adaae568e40c6c6429a2704
/- accepted add_to_file helper 1 -/
lemma exists_isCover_encard_le_of_externalCoveringNumber_le
    {Z : Type*} [PseudoEMetricSpace Z] {ε : NNReal} {A : Set Z} {m : ℕ}
    (h : Metric.externalCoveringNumber ε A ≤ (m : ℕ∞)) :
    ∃ C : Set Z, Metric.IsCover ε A C ∧ C.encard ≤ (m : ℕ∞) := by
  unfold Metric.externalCoveringNumber at h
  have hlt : (⨅ C : Set Z, ⨅ _ : Metric.IsCover ε A C, C.encard) < (m : ℕ∞) + 1 :=
    lt_of_le_of_lt h ((ENat.lt_add_one_iff (ENat.coe_ne_top m)).mpr le_rfl)
  rcases (iInf_lt_iff.mp hlt) with ⟨C, hC⟩
  rcases (iInf_lt_iff.mp hC) with ⟨hCcover, hCcard⟩
  exact ⟨C, hCcover, (ENat.lt_add_one_iff (ENat.coe_ne_top m)).mp hCcard⟩

/- accepted add_to_file helper 2 -/
lemma exists_covering_radius_lt_of_iInf_lt
    {Z W : Type*} [PseudoEMetricSpace Z] {A : Set Z} {m : ℕ} {r : ENNReal}
    (h : (⨅ (ε : NNReal), ⨅ (_ : 0 < ε),
      ⨅ (_ : Metric.externalCoveringNumber ε A ≤ (m : ℕ∞)), (ε : ENNReal)) < r) :
    ∃ ε : NNReal, 0 < ε ∧ Metric.externalCoveringNumber ε A ≤ (m : ℕ∞) ∧
      (ε : ENNReal) < r := by
  rcases (iInf_lt_iff.mp h) with ⟨ε, hε⟩
  rcases (iInf_lt_iff.mp hε) with ⟨hεpos, hεcover⟩
  rcases (iInf_lt_iff.mp hεcover) with ⟨hcover, hεlt⟩
  exact ⟨ε, hεpos, hcover, hεlt⟩

/- accepted add_to_file helper 3 -/
lemma iInf_covering_radius_le
    {Z : Type*} [PseudoEMetricSpace Z] {A : Set Z} {m : ℕ} {r : NNReal}
    (hr : 0 < r) (hc : Metric.externalCoveringNumber r A ≤ (m : ℕ∞)) :
    (⨅ (ε : NNReal), ⨅ (_ : 0 < ε),
      ⨅ (_ : Metric.externalCoveringNumber ε A ≤ (m : ℕ∞)), (ε : ENNReal)) ≤
      (r : ENNReal) := by
  exact iInf_le_of_le r (iInf_le_of_le hr (iInf_le_of_le hc le_rfl))

/- accepted add_to_file helper 4 -/
lemma card_mul_two_pow_pred_le_pow {c n : ℕ} (hn : 0 < n) :
    (c : ℕ∞) * (2 ^ (n - 1) : ℕ∞) ≤ (2 ^ (n + Nat.log 2 c) : ℕ∞) := by
  have hc : c ≤ 2 ^ (Nat.log 2 c + 1) :=
    Nat.le_of_lt (Nat.lt_pow_succ_log_self (by norm_num) c)
  have hmul : c * 2 ^ (n - 1) ≤ 2 ^ (Nat.log 2 c + 1) * 2 ^ (n - 1) :=
    Nat.mul_le_mul_right _ hc
  have hpow : 2 ^ (Nat.log 2 c + 1) * 2 ^ (n - 1) = 2 ^ (n + Nat.log 2 c) := by
    rw [← pow_add]
    congr 1
    omega
  exact_mod_cast hmul.trans_eq hpow

/- accepted add_to_file helper 5 -/
lemma exists_covering_radius_lt_of_iInf_lt'
    {Z : Type*} [PseudoEMetricSpace Z] {A : Set Z} {m : ℕ} {r : ENNReal}
    (h : (⨅ (ε : NNReal), ⨅ (_ : 0 < ε),
      ⨅ (_ : Metric.externalCoveringNumber ε A ≤ (m : ℕ∞)), (ε : ENNReal)) < r) :
    ∃ ε : NNReal, 0 < ε ∧ Metric.externalCoveringNumber ε A ≤ (m : ℕ∞) ∧
      (ε : ENNReal) < r := by
  rcases (iInf_lt_iff.mp h) with ⟨ε, hε⟩
  rcases (iInf_lt_iff.mp hε) with ⟨hεpos, hεcover⟩
  rcases (iInf_lt_iff.mp hεcover) with ⟨hcover, hεlt⟩
  exact ⟨ε, hεpos, hcover, hεlt⟩

/- verified submission -/
theorem entropy_number_approximation
    (𝕜 : Type*) [RCLike 𝕜]
    (X Y : Type*) [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (Γ : Type*) [Fintype Γ] [Nonempty Γ]
    (V : X →ₗ[𝕜] Y) (Vγ : Γ → X →ₗ[𝕜] Y)
    (n : ℕ) (hn : 0 < n) :
    let e : ℕ → (X →ₗ[𝕜] Y) → ENNReal := fun k T ↦
      ⨅ (ε : NNReal) (_ : 0 < ε)
        (_ : Metric.externalCoveringNumber ε (T '' Metric.closedBall (0 : X) 1) ≤
          2 ^ (k - 1)),
        (ε : ENNReal)
    e (n + Nat.log 2 (Fintype.card Γ) + 1) V ≤
      (⨆ γ : Γ, e n (Vγ γ)) +
        (⨆ (x : X) (_ : ‖x‖ ≤ 1),
          ⨅ γ : Γ, ENNReal.ofReal ‖V x - Vγ γ x‖) := by
  let e : ℕ → (X →ₗ[𝕜] Y) → ENNReal := fun k T ↦
    ⨅ (ε : NNReal) (_ : 0 < ε)
      (_ : Metric.externalCoveringNumber ε (T '' Metric.closedBall (0 : X) 1) ≤
        2 ^ (k - 1)),
      (ε : ENNReal)
  let A : ENNReal := ⨆ γ : Γ, e n (Vγ γ)
  let B : ENNReal := ⨆ (x : X) (_ : ‖x‖ ≤ 1),
    ⨅ γ : Γ, ENNReal.ofReal ‖V x - Vγ γ x‖
  change e (n + Nat.log 2 (Fintype.card Γ) + 1) V ≤ A + B
  by_cases htop : A + B = ⊤
  · rw [htop]
    exact le_top
  refine le_of_forall_pos_le_add ?_
  intro ε hε
  by_cases hεtop : ε = ⊤
  · rw [hεtop]
    simp
  have hA : A ≠ ⊤ := by
    intro h
    apply htop
    rw [h]
    simp
  have hB : B ≠ ⊤ := by
    intro h
    apply htop
    rw [h]
    simp
  let η : ENNReal := ε / 2
  have hηpos : 0 < η := ENNReal.div_pos (ne_of_gt hε) (by norm_num)
  have hηne : η ≠ 0 := ne_of_gt hηpos
  have hrad : ∀ γ : Γ, ∃ r : NNReal, 0 < r ∧
      Metric.externalCoveringNumber r (Vγ γ '' Metric.closedBall (0 : X) 1) ≤
        ((2 ^ (n - 1) : ℕ) : ℕ∞) ∧
      (r : ENNReal) < A + η := by
    intro γ
    apply exists_covering_radius_lt_of_iInf_lt'
    have hle : e n (Vγ γ) ≤ A := by
      exact le_iSup (fun γ : Γ => e n (Vγ γ)) γ
    exact lt_of_le_of_lt hle (ENNReal.lt_add_right hA hηne)
  choose r hrpos hrcov hrlt using hrad
  have hcover : ∀ γ : Γ, ∃ C : Set Y,
      Metric.IsCover (r γ) (Vγ γ '' Metric.closedBall (0 : X) 1) C ∧
      C.encard ≤ ((2 ^ (n - 1) : ℕ) : ℕ∞) := by
    intro γ
    exact exists_isCover_encard_le_of_externalCoveringNumber_le (hrcov γ)
  choose C hCcover hCcard using hcover
  have htarget_top : A + B + ε ≠ ⊤ := by
    rw [ENNReal.add_ne_top]
    exact ⟨htop, hεtop⟩
  have htarget_zero : A + B + ε ≠ 0 := by
    intro h
    have hεzero : ε = 0 := (add_eq_zero.mp h).2
    exact (ne_of_gt hε) hεzero
  let R : NNReal := (A + B + ε).toNNReal
  have hRpos : 0 < R := ENNReal.toNNReal_pos htarget_zero htarget_top
  have hR_coe : (R : ENNReal) = A + B + ε := ENNReal.coe_toNNReal htarget_top
  have hVcover : Metric.IsCover R (V '' Metric.closedBall (0 : X) 1)
      (⋃ γ : Γ, C γ) := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hxnorm : ‖x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hx
    have hb_le : (⨅ γ : Γ, ENNReal.ofReal ‖V x - Vγ γ x‖) ≤ B := by
      have hinner : (⨅ γ : Γ, ENNReal.ofReal ‖V x - Vγ γ x‖) ≤
          ⨆ (_ : ‖x‖ ≤ 1), ⨅ γ : Γ, ENNReal.ofReal ‖V x - Vγ γ x‖ := by
        exact le_iSup
          (fun _ : ‖x‖ ≤ 1 => ⨅ γ : Γ, ENNReal.ofReal ‖V x - Vγ γ x‖) hxnorm
      exact hinner.trans
        (le_iSup
          (fun x : X => ⨆ (_ : ‖x‖ ≤ 1),
            ⨅ γ : Γ, ENNReal.ofReal ‖V x - Vγ γ x‖) x)
    have hb_lt : (⨅ γ : Γ, ENNReal.ofReal ‖V x - Vγ γ x‖) < B + η :=
      lt_of_le_of_lt hb_le (ENNReal.lt_add_right hB hηne)
    rcases iInf_lt_iff.mp hb_lt with ⟨γ, hγ⟩
    have hyγ : Vγ γ x ∈ Vγ γ '' Metric.closedBall (0 : X) 1 := ⟨x, hx, rfl⟩
    rcases hCcover γ hyγ with ⟨z, hzC, hz⟩
    have happrox : edist (V x) (Vγ γ x) < B + η := by
      rw [edist_dist, dist_eq_norm]
      exact hγ
    have hsum : (B + η) + (A + η) = A + B + ε := by
      calc
        (B + η) + (A + η) = B + (η + (A + η)) := by rw [add_assoc]
        _ = B + (A + (η + η)) := by
          congr 1
          calc
            η + (A + η) = (η + A) + η := by rw [← add_assoc]
            _ = (A + η) + η := by rw [add_comm η A]
            _ = A + (η + η) := by rw [add_assoc]
        _ = B + A + (η + η) := by rw [← add_assoc]
        _ = A + B + (η + η) := by rw [add_comm B A]
        _ = A + B + ε := by rw [ENNReal.add_halves]
    have hzlt : edist (V x) z < (R : ENNReal) := by
      calc
        edist (V x) z ≤ edist (V x) (Vγ γ x) + edist (Vγ γ x) z :=
          edist_triangle _ _ _
        _ < (B + η) + (A + η) :=
          ENNReal.add_lt_add happrox (lt_of_le_of_lt hz (hrlt γ))
        _ = A + B + ε := hsum
        _ = (R : ENNReal) := hR_coe.symm
    exact ⟨z, Set.mem_iUnion.2 ⟨γ, hzC⟩, hzlt.le⟩
  have hCunion : (⋃ γ : Γ, C γ).encard ≤
      ((2 ^ (n + Nat.log 2 (Fintype.card Γ)) : ℕ) : ℕ∞) := by
    calc
      (⋃ γ : Γ, C γ).encard ≤ ∑ γ : Γ, (C γ).encard :=
        Set.encard_iUnion_le_of_fintype C
      _ ≤ Finset.univ.card • ((2 ^ (n - 1) : ℕ) : ℕ∞) := by
        exact Finset.sum_le_card_nsmul Finset.univ (fun γ : Γ => (C γ).encard)
          ((2 ^ (n - 1) : ℕ) : ℕ∞) (by intro γ _; exact hCcard γ)
      _ = (Fintype.card Γ : ℕ∞) * ((2 ^ (n - 1) : ℕ) : ℕ∞) := by
        rw [Finset.card_univ, nsmul_eq_mul]
      _ ≤ ((2 ^ (n + Nat.log 2 (Fintype.card Γ)) : ℕ) : ℕ∞) :=
        card_mul_two_pow_pred_le_pow hn
  have hnum : Metric.externalCoveringNumber R (V '' Metric.closedBall (0 : X) 1) ≤
      (2 ^ (n + Nat.log 2 (Fintype.card Γ) + 1 - 1) : ℕ∞) := by
    calc
      Metric.externalCoveringNumber R (V '' Metric.closedBall (0 : X) 1) ≤
          (⋃ γ : Γ, C γ).encard :=
        Metric.IsCover.externalCoveringNumber_le_encard hVcover
      _ ≤ ((2 ^ (n + Nat.log 2 (Fintype.card Γ)) : ℕ) : ℕ∞) := hCunion
      _ = (2 ^ (n + Nat.log 2 (Fintype.card Γ) + 1 - 1) : ℕ∞) := rfl
  calc
    e (n + Nat.log 2 (Fintype.card Γ) + 1) V ≤ (R : ENNReal) := by
      exact iInf_covering_radius_le hRpos hnum
    _ = A + B + ε := hR_coe

end Rollout_p1136_entropy_number_approximation

#check_dependency_graph "Rollout_p1136_entropy_number_approximation.entropy_number_approximation" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let e := fun k T => ⨅ ε, ⨅ (_ : 0 < ε), ⨅ (_ : Metric.externalCoveringNumber ε (⇑T '' Metric.closedBall 0 1) ≤ 2 ^ (k - 1)), ↑ε; e (n + Nat.log 2 (Fintype.card Γ) + 1) V ≤ (⨆ γ, e n (Vγ γ)) + ⨆ x, ⨆ (_ : ‖x‖ ≤ 1), ⨅ γ, ENNReal.ofReal ‖V x - (Vγ γ) x‖\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hn\",\"statement\":\"0 < n\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1136_entropy_number_approximation\",\"reconstructedProofSha256\":\"65dcbe87a8510bbfca50e611c2cc13a0477e85843aad392e6bca057408ee4ba1\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1136_entropy_number_approximation.entropy_number_approximation\",\"topologySha256\":\"35962ed6d9b2ce9c224f8534f09d23127dfd835d3adaae568e40c6c6429a2704\"}"

namespace Rollout_p1151_strict_convex_modular_fixed_point

-- graph_id: p1151_strict_convex_modular_fixed_point
-- topology_sha256: d75903c07f3cb6dafb1d31aa074ca2f36785d75d8e5ad8a06a5b6745d6002ea8
/- accepted add_to_file helper 1 -/
lemma modular_scale_le
    {X : Type*} (w : NNReal → X → X → ENNReal)
    (hself : ∀ (l : NNReal), 0 < l → ∀ x : X, w l x x = 0)
    (hconv : ∀ (l m : NNReal), 0 < l → 0 < m → ∀ x y z : X,
      w (l + m) x y ≤ ((l : ENNReal) / (l + m)) * w l x z +
        ((m : ENNReal) / (l + m)) * w m y z)
    {l s : NNReal} (hl : 0 < l) (hls : l ≤ s) (x y : X) :
    w s x y ≤ ((l : ENNReal) / (s : ENNReal)) * w l x y := by
  rcases eq_or_lt_of_le hls with rfl | hlt
  · have h0 : (l : ENNReal) ≠ 0 := by exact_mod_cast ne_of_gt hl
    have htop : (l : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    simp [ENNReal.div_self h0 htop]
  · let d : NNReal := s - l
    have hd : 0 < d := tsub_pos_of_lt hlt
    have hsd : l + d = s := add_tsub_cancel_of_le hls
    have h := hconv l d hl hd x y y
    rw [hsd, hself d hd y, mul_zero, add_zero] at h
    rw [← ENNReal.coe_add, hsd] at h
    exact h

lemma ennreal_add_coe_mul_div_sub_self {d : ENNReal} {k : NNReal}
    (hk : (k : ENNReal) < 1) :
    d + (k : ENNReal) * (d / (1 - (k : ENNReal))) =
      d / (1 - (k : ENNReal)) := by
  let e : ENNReal := 1 - (k : ENNReal)
  have he0 : e ≠ 0 := by
    dsimp [e]
    exact ne_of_gt (tsub_pos_of_lt hk)
  have het : e ≠ ⊤ := by
    dsimp [e]
    exact ENNReal.sub_ne_top (by simp)
  have hek : e + (k : ENNReal) = 1 := by
    dsimp [e]
    exact tsub_add_cancel_of_le hk.le
  have hinv : e * e⁻¹ = 1 := ENNReal.mul_inv_cancel he0 het
  calc
    d + (k : ENNReal) * (d / e)
        = d * 1 + (k : ENNReal) * (d * e⁻¹) := by rw [div_eq_mul_inv, mul_one]
    _ = d * (e * e⁻¹) + (k : ENNReal) * (d * e⁻¹) := by rw [hinv]
    _ = e * (d * e⁻¹) + (k : ENNReal) * (d * e⁻¹) := by
          congr 1
          calc
            d * (e * e⁻¹) = (d * e) * e⁻¹ := by rw [mul_assoc]
            _ = (e * d) * e⁻¹ := by rw [mul_comm d e]
            _ = e * (d * e⁻¹) := by rw [mul_assoc]
    _ = (e + (k : ENNReal)) * (d * e⁻¹) := by rw [add_mul]
    _ = d / e := by rw [hek, one_mul, div_eq_mul_inv]

/- accepted add_to_file helper 2 -/
lemma tendsto_ennreal_const_mul_pow_min_zero {C : ENNReal} (hC : C ≠ ⊤)
    {k : NNReal} (hk : k < 1) :
    Filter.Tendsto (fun p : ℕ × ℕ => C * (k : ENNReal) ^ min p.1 p.2)
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
  have hmin : Filter.Tendsto (fun p : ℕ × ℕ => min p.1 p.2)
      (Filter.atTop ×ˢ Filter.atTop) Filter.atTop := by
    rw [Filter.tendsto_atTop]
    intro N
    filter_upwards [Filter.tendsto_fst.eventually_ge_atTop N,
      Filter.tendsto_snd.eventually_ge_atTop N] with p hp1 hp2
    exact le_min hp1 hp2
  have hpow : Filter.Tendsto (fun n : ℕ => (k : ℝ) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (NNReal.coe_nonneg k) (by exact_mod_cast hk)
  have hreal : Filter.Tendsto
      (fun p : ℕ × ℕ => C.toReal * (k : ℝ) ^ min p.1 p.2)
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
    simpa using Filter.Tendsto.const_mul C.toReal (hpow.comp hmin)
  have hreal' : Filter.Tendsto
      (fun p : ℕ × ℕ => (C * (k : ENNReal) ^ min p.1 p.2).toReal)
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0) := by
    convert hreal using 1
    ext p
    simp [ENNReal.toReal_mul, ← ENNReal.coe_pow]
  exact (ENNReal.tendsto_toReal_zero_iff (fun p => by
    exact ENNReal.mul_ne_top hC (by
      rw [← ENNReal.coe_pow]
      exact ENNReal.coe_ne_top))).1 hreal'

/- accepted add_to_file helper 3 -/
lemma modular_fixed_point_of_displacement
    {X : Type*} (b : X) (w : NNReal → X → X → ENNReal)
    (hself : ∀ (l : NNReal), 0 < l → ∀ x : X, w l x x = 0)
    (hsymm : ∀ (l : NNReal), 0 < l → ∀ x y : X, w l x y = w l y x)
    (hstrict : ∀ x y : X, (∃ l : NNReal, 0 < l ∧ w l x y = 0) → x = y)
    (hconv : ∀ (l m : NNReal), 0 < l → 0 < m → ∀ x y z : X,
      w (l + m) x y ≤ ((l : ENNReal) / (l + m)) * w l x z +
        ((m : ENNReal) / (l + m)) * w m y z)
    (hcomplete : ∀ (x : ℕ → {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤})
      (l : NNReal), 0 < l →
      Filter.Tendsto (fun p : ℕ × ℕ => w l (x p.1) (x p.2))
        (Filter.atTop ×ˢ Filter.atTop) (nhds 0) →
      ∃ y : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
        Filter.Tendsto (fun n => w l (x n) y) Filter.atTop (nhds 0))
    (T : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤} →
      {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤})
    {k L : NNReal} (hk0 : 0 < k) (hk1 : k < 1) (hL0 : 0 < L)
    (hcontr : ∀ x y : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
      ∀ l : NNReal, 0 < l → l ≤ L → w (k * l) (T x) (T y) ≤ w l x y)
    (x0 : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤})
    (hdisp : w ((1 - (1 + k) / 2) * L) x0 (T x0) < ⊤) :
    ∃ y : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
      T y = y ∧
      Filter.Tendsto (fun n : ℕ => w L ((T^[n]) x0) y)
        Filter.atTop (nhds 0) := by
  let q : NNReal := (1 + k) / 2
  let r : NNReal := k / q
  let a : NNReal := (1 - q) * L
  let lam : ℕ → NNReal := fun n => a * q ^ n
  let S : ℕ → NNReal := fun n => L * q ^ n
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hkq : k < q := by dsimp [q]; nlinarith [hk0, hk1]
  have hq1 : q < 1 := by dsimp [q]; nlinarith [hk1]
  have hr1 : r < 1 := by dsimp [r]; rw [div_lt_one hq0]; exact hkq
  have hqr : q * r = k := by
    dsimp [r]; rw [mul_comm]; exact div_mul_cancel₀ k (ne_of_gt hq0)
  have ha0 : 0 < a := by dsimp [a]; exact mul_pos (tsub_pos_of_lt hq1) hL0
  have hlam0 : ∀ n, 0 < lam n := by intro n; dsimp [lam]; exact mul_pos ha0 (pow_pos hq0 n)
  have hlam_le : ∀ n, lam n ≤ L := by
    intro n
    have h1 : 1 - q ≤ (1 : NNReal) := tsub_le_self
    have h2 : q ^ n ≤ (1 : NNReal) := pow_le_one₀ hq0.le hq1.le
    dsimp [lam, a]
    calc
      (1 - q) * L * q ^ n ≤ (1 - q) * L * 1 := mul_le_mul_left' h2 ((1 - q) * L)
      _ ≤ (1 : NNReal) * L * 1 := mul_le_mul_right' (mul_le_mul_right' h1 L) 1
      _ = L := by ring
  have hS0 : ∀ n, 0 < S n := by intro n; dsimp [S]; exact mul_pos hL0 (pow_pos hq0 n)
  have hS_le : ∀ n, S n ≤ L := by
    intro n
    dsimp [S]
    calc
      L * q ^ n ≤ L * 1 := mul_le_mul_left' (pow_le_one₀ hq0.le hq1.le) L
      _ = L := mul_one L
  have hS_add : ∀ n, lam n + S (n + 1) = S n := by
    intro n
    dsimp [lam, S, a]
    calc
      (1 - q) * L * q ^ n + L * q ^ (n + 1)
          = ((1 - q) + q) * L * q ^ n := by rw [pow_succ]; ring
      _ = L * q ^ n := by rw [tsub_add_cancel_of_le hq1.le]; ring
  let d0 : ENNReal := w a x0 (T x0)
  have hd0 : d0 ≠ ⊤ := ne_of_lt hdisp
  have hgeom : ∀ n : ℕ,
      w (lam n) ((T^[n]) x0) ((T^[n + 1]) x0) ≤ d0 * (r : ENNReal) ^ n := by
    intro n
    induction n with
    | zero => simp [lam, a, d0]
    | succ n ih =>
        have hscale : w (lam (n + 1)) ((T^[n + 1]) x0) ((T^[n + 2]) x0) ≤
            (((k * lam n : NNReal) : ENNReal) / (lam (n + 1) : ENNReal)) *
              w (k * lam n) ((T^[n + 1]) x0) ((T^[n + 2]) x0) := by
          apply modular_scale_le w hself hconv
          · exact mul_pos hk0 (hlam0 n)
          · dsimp [lam]
            calc
              k * (a * q ^ n) ≤ q * (a * q ^ n) := by gcongr
              _ = a * q ^ (n + 1) := by rw [pow_succ]; ring
        have hcoeff : (((k * lam n : NNReal) : ENNReal) / (lam (n + 1) : ENNReal)) =
            (r : ENNReal) := by
          have hnext : (lam (n + 1) : ENNReal) = (q : ENNReal) * (lam n : ENNReal) := by
            dsimp [lam]; rw [pow_succ]; ring
          have hk_eq : (k : ENNReal) = (q : ENNReal) * (r : ENNReal) := by
            rw [← ENNReal.coe_mul, hqr]
          have hden : (q : ENNReal) * (lam n : ENNReal) ≠ 0 := by
            exact mul_ne_zero (by exact_mod_cast ne_of_gt hq0)
              (by exact_mod_cast ne_of_gt (hlam0 n))
          have hdenTop : (q : ENNReal) * (lam n : ENNReal) ≠ ⊤ :=
            ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top
          calc
            (((k * lam n : NNReal) : ENNReal) / (lam (n + 1) : ENNReal))
                = ((k : ENNReal) * (lam n : ENNReal)) / ((q : ENNReal) * (lam n : ENNReal)) := by
                    rw [ENNReal.coe_mul, hnext]
            _ = (((q : ENNReal) * (r : ENNReal)) * (lam n : ENNReal)) /
                    ((q : ENNReal) * (lam n : ENNReal)) := by rw [hk_eq]
            _ = (r : ENNReal) := by
                    calc
                      (((q : ENNReal) * (r : ENNReal)) * (lam n : ENNReal)) /
                          ((q : ENNReal) * (lam n : ENNReal))
                          = (r : ENNReal) * ((q : ENNReal) * (lam n : ENNReal)) /
                              ((q : ENNReal) * (lam n : ENNReal)) := by ring
                      _ = (r : ENNReal) * 1 := by
                            rw [mul_div_assoc, ENNReal.div_self hden hdenTop]
                      _ = (r : ENNReal) := mul_one _
        have hctr0 := hcontr ((T^[n]) x0) ((T^[n + 1]) x0) (lam n) (hlam0 n) (hlam_le n)
        have hctr : w (k * lam n) ((T^[n + 1]) x0) ((T^[n + 2]) x0) ≤
            w (lam n) ((T^[n]) x0) ((T^[n + 1]) x0) := by
          simpa [Function.iterate_succ_apply'] using hctr0
        calc
          w (lam (n + 1)) ((T^[n + 1]) x0) ((T^[n + 2]) x0)
              ≤ (r : ENNReal) * w (k * lam n) ((T^[n + 1]) x0) ((T^[n + 2]) x0) := by
                  rw [← hcoeff]; exact hscale
          _ ≤ (r : ENNReal) * w (lam n) ((T^[n]) x0) ((T^[n + 1]) x0) :=
                  mul_le_mul_left' hctr _
          _ ≤ (r : ENNReal) * (d0 * (r : ENNReal) ^ n) := mul_le_mul_left' ih _
          _ = d0 * (r : ENNReal) ^ (n + 1) := by rw [pow_succ]; ring
  let C : ENNReal := d0 / (1 - (k : ENNReal))
  have hCeq : d0 + (k : ENNReal) * C = C := by
    dsimp [C]
    exact ennreal_add_coe_mul_div_sub_self (by exact_mod_cast hk1)
  have hCne : C ≠ ⊤ := by
    dsimp [C]
    apply ENNReal.div_ne_top hd0
    exact ne_of_gt (tsub_pos_of_lt (by exact_mod_cast hk1 : (k : ENNReal) < 1))
  have hlam_le_S : ∀ n, lam n ≤ S n := by
    intro n
    have haL : a ≤ L := by
      dsimp [a]
      calc
        (1 - q) * L ≤ 1 * L := mul_le_mul_right' tsub_le_self L
        _ = L := one_mul L
    dsimp [lam, S]
    exact mul_le_mul_right' haL (q ^ n)
  have hSratio : ∀ n, ((S (n + 1) : ENNReal) / (S n : ENNReal)) = (q : ENNReal) := by
    intro n
    have hnext : (S (n + 1) : ENNReal) = (q : ENNReal) * (S n : ENNReal) := by
      dsimp [S]; rw [pow_succ]; ring
    have hden : (S n : ENNReal) ≠ 0 := by exact_mod_cast ne_of_gt (hS0 n)
    have hdenTop : (S n : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    calc
      ((S (n + 1) : ENNReal) / (S n : ENNReal))
          = ((q : ENNReal) * (S n : ENNReal)) / (S n : ENNReal) := by rw [hnext]
      _ = (q : ENNReal) * ((S n : ENNReal) / (S n : ENNReal)) := by rw [mul_div_assoc]
      _ = (q : ENNReal) := by rw [ENNReal.div_self hden hdenTop, mul_one]
  have hpath : ∀ N n : ℕ,
      w (S n) ((T^[n]) x0) ((T^[n + N]) x0) ≤ C * (r : ENNReal) ^ n := by
    intro N
    induction N with
    | zero =>
        intro n
        simp [hself (S n) (hS0 n)]
    | succ N ih =>
        intro n
        have hcv0 := hconv (lam n) (S (n + 1)) (hlam0 n) (hS0 (n + 1))
          ((T^[n]) x0) ((T^[n + (N + 1)]) x0) ((T^[n + 1]) x0)
        rw [← ENNReal.coe_add, hS_add n] at hcv0
        have hcv : w (S n) ((T^[n]) x0) ((T^[n + (N + 1)]) x0) ≤
            ((lam n : ENNReal) / (S n : ENNReal)) *
              w (lam n) ((T^[n]) x0) ((T^[n + 1]) x0) +
            ((S (n + 1) : ENNReal) / (S n : ENNReal)) *
              w (S (n + 1)) ((T^[n + (N + 1)]) x0) ((T^[n + 1]) x0) := by
          simpa [hS_add n, Function.iterate_succ_apply'] using hcv0
        have hfirst : ((lam n : ENNReal) / (S n : ENNReal)) ≤ 1 := by
          have hdiv : lam n / S n ≤ (1 : NNReal) :=
            div_le_one_of_le₀ (hlam_le_S n) (zero_le _)
          rw [← ENNReal.coe_div (ne_of_gt (hS0 n))]
          exact_mod_cast hdiv
        have hidx : n + (N + 1) = (n + 1) + N := by omega
        have hs : w (S (n + 1)) ((T^[n + (N + 1)]) x0) ((T^[n + 1]) x0) =
            w (S (n + 1)) ((T^[n + 1]) x0) ((T^[n + (N + 1)]) x0) :=
          hsymm (S (n + 1)) (hS0 (n + 1)) _ _
        have hih : w (S (n + 1)) ((T^[n + 1]) x0) ((T^[n + (N + 1)]) x0) ≤
            C * (r : ENNReal) ^ (n + 1) := by
          simpa [hidx] using ih (n + 1)
        calc
          w (S n) ((T^[n]) x0) ((T^[n + (N + 1)]) x0)
              ≤ ((lam n : ENNReal) / (S n : ENNReal)) *
                  w (lam n) ((T^[n]) x0) ((T^[n + 1]) x0) +
                ((S (n + 1) : ENNReal) / (S n : ENNReal)) *
                  w (S (n + 1)) ((T^[n + (N + 1)]) x0) ((T^[n + 1]) x0) := hcv
          _ ≤ 1 * (d0 * (r : ENNReal) ^ n) +
                (q : ENNReal) * (C * (r : ENNReal) ^ (n + 1)) := by
                apply add_le_add
                · exact mul_le_mul hfirst (hgeom n) (zero_le _) (zero_le _)
                · rw [hSratio n, hs]
                  exact mul_le_mul_left' hih _
          _ = d0 * (r : ENNReal) ^ n +
                (q : ENNReal) * (C * (r : ENNReal) ^ (n + 1)) := by rw [one_mul]
          _ = (d0 + (k : ENNReal) * C) * (r : ENNReal) ^ n := by
                have hqrE : (q : ENNReal) * (r : ENNReal) = (k : ENNReal) := by
                  rw [← ENNReal.coe_mul, hqr]
                have h : (q : ENNReal) * (C * (r : ENNReal) ^ (n + 1)) =
                    ((k : ENNReal) * C) * (r : ENNReal) ^ n := by
                  calc
                    (q : ENNReal) * (C * (r : ENNReal) ^ (n + 1))
                        = ((q : ENNReal) * (r : ENNReal)) *
                            (C * (r : ENNReal) ^ n) := by rw [pow_succ]; ring
                    _ = ((k : ENNReal) * C) * (r : ENNReal) ^ n := by rw [hqrE]; ring
                rw [h, add_mul]
          _ = C * (r : ENNReal) ^ n := by rw [hCeq]
  have hSratioL : ∀ n, ((S n : ENNReal) / (L : ENNReal)) = (q : ENNReal) ^ n := by
    intro n
    dsimp [S]
    have h0 : (L : ENNReal) ≠ 0 := by exact_mod_cast ne_of_gt hL0
    have ht : (L : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
    calc
      (L : ENNReal) * (q : ENNReal) ^ n / (L : ENNReal)
          = (q : ENNReal) ^ n * ((L : ENNReal) / (L : ENNReal)) := by
            rw [mul_comm ((L : ENNReal)) ((q : ENNReal) ^ n), mul_div_assoc]
      _ = (q : ENNReal) ^ n := by rw [ENNReal.div_self h0 ht, mul_one]
  have hpair_left : ∀ n m : ℕ, n ≤ m →
      w L ((T^[n]) x0) ((T^[m]) x0) ≤ C * (k : ENNReal) ^ n := by
    intro n m hnm
    have hp0 := hpath (m - n) n
    have hsum : n + (m - n) = m := Nat.add_sub_of_le hnm
    have hp : w (S n) ((T^[n]) x0) ((T^[m]) x0) ≤ C * (r : ENNReal) ^ n := by
      simpa [hsum] using hp0
    have hsc := modular_scale_le w hself hconv (hS0 n) (hS_le n)
      ((T^[n]) x0) ((T^[m]) x0)
    have hqrpow : (q : ENNReal) ^ n * (C * (r : ENNReal) ^ n) =
        C * (k : ENNReal) ^ n := by
      have h : (q : ENNReal) ^ n * (r : ENNReal) ^ n = (k : ENNReal) ^ n := by
        rw [← ENNReal.coe_pow, ← ENNReal.coe_pow, ← ENNReal.coe_mul, ← mul_pow, hqr,
          ENNReal.coe_pow]
      calc
        (q : ENNReal) ^ n * (C * (r : ENNReal) ^ n)
            = C * ((q : ENNReal) ^ n * (r : ENNReal) ^ n) := by ring
        _ = C * (k : ENNReal) ^ n := by rw [h]
    calc
      w L ((T^[n]) x0) ((T^[m]) x0)
          ≤ ((S n : ENNReal) / (L : ENNReal)) *
              w (S n) ((T^[n]) x0) ((T^[m]) x0) := hsc
      _ = (q : ENNReal) ^ n * w (S n) ((T^[n]) x0) ((T^[m]) x0) := by
            rw [hSratioL n]
      _ ≤ (q : ENNReal) ^ n * (C * (r : ENNReal) ^ n) :=
            mul_le_mul_left' hp _
      _ = C * (k : ENNReal) ^ n := hqrpow
  have hpair : ∀ p : ℕ × ℕ,
      w L ((T^[p.1]) x0) ((T^[p.2]) x0) ≤ C * (k : ENNReal) ^ min p.1 p.2 := by
    intro p
    rcases le_total p.1 p.2 with h | h
    · simpa [min_eq_left h] using hpair_left p.1 p.2 h
    · have hs : w L ((T^[p.1]) x0) ((T^[p.2]) x0) =
          w L ((T^[p.2]) x0) ((T^[p.1]) x0) := hsymm L hL0 _ _
      calc
        w L ((T^[p.1]) x0) ((T^[p.2]) x0)
            = w L ((T^[p.2]) x0) ((T^[p.1]) x0) := hs
        _ ≤ C * (k : ENNReal) ^ p.2 := hpair_left p.2 p.1 h
        _ = C * (k : ENNReal) ^ min p.1 p.2 := by rw [min_eq_right h]
  have hupper : Filter.Tendsto
      (fun p : ℕ × ℕ => C * (k : ENNReal) ^ min p.1 p.2)
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0) :=
    tendsto_ennreal_const_mul_pow_min_zero hCne hk1
  have hCauchy : Filter.Tendsto
      (fun p : ℕ × ℕ => w L ((T^[p.1]) x0) ((T^[p.2]) x0))
      (Filter.atTop ×ˢ Filter.atTop) (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
      (fun p => zero_le _) hpair
  rcases hcomplete (fun n => (T^[n]) x0) L hL0 hCauchy with ⟨y, hlim⟩
  have hlim_yx : Filter.Tendsto (fun n : ℕ => w L y ((T^[n]) x0))
      Filter.atTop (nhds 0) := by
    convert hlim using 1
    ext n
    exact hsymm L hL0 _ _
  have htail : Filter.Tendsto (fun n : ℕ => w L y ((T^[n + 1]) x0))
      Filter.atTop (nhds 0) :=
    (Filter.tendsto_add_atTop_iff_nat 1).2 hlim_yx
  have hctr_le : ∀ n : ℕ,
      w (k * L) (T y) ((T^[n + 1]) x0) ≤ w L y ((T^[n]) x0) := by
    intro n
    have hc := hcontr y ((T^[n]) x0) L hL0 le_rfl
    simpa [Function.iterate_succ_apply'] using hc
  have hctr_lim : Filter.Tendsto
      (fun n : ℕ => w (k * L) (T y) ((T^[n + 1]) x0))
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim_yx
      (fun n => zero_le _) hctr_le
  let s : NNReal := k * L + L
  have hs0 : 0 < s := by dsimp [s]; exact add_pos (mul_pos hk0 hL0) hL0
  let A : ENNReal := ((k * L : NNReal) : ENNReal) /
    (((k * L : NNReal) : ENNReal) + (L : ENNReal))
  let B : ENNReal := (L : ENNReal) /
    (((k * L : NNReal) : ENNReal) + (L : ENNReal))
  have hden : (((k * L : NNReal) : ENNReal) + (L : ENNReal)) ≠ 0 := by
    rw [← ENNReal.coe_add]
    exact_mod_cast ne_of_gt hs0
  have hAne : A ≠ ⊤ := by
    dsimp [A]
    exact ENNReal.div_ne_top ENNReal.coe_ne_top hden
  have hBne : B ≠ ⊤ := by
    dsimp [B]
    exact ENNReal.div_ne_top ENNReal.coe_ne_top hden
  have hA_lim : Filter.Tendsto
      (fun n : ℕ => A * w (k * L) (T y) ((T^[n + 1]) x0))
      Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul hctr_lim (Or.inr hAne)
  have hB_lim : Filter.Tendsto
      (fun n : ℕ => B * w L y ((T^[n + 1]) x0))
      Filter.atTop (nhds 0) := by
    simpa using ENNReal.Tendsto.const_mul htail (Or.inr hBne)
  have hsum_lim : Filter.Tendsto
      (fun n : ℕ => A * w (k * L) (T y) ((T^[n + 1]) x0) +
        B * w L y ((T^[n + 1]) x0))
      Filter.atTop (nhds 0) := by
    simpa using hA_lim.add hB_lim
  have hfix_le : ∀ n : ℕ,
      w s (T y) y ≤ A * w (k * L) (T y) ((T^[n + 1]) x0) +
        B * w L y ((T^[n + 1]) x0) := by
    intro n
    exact hconv (k * L) L (mul_pos hk0 hL0) hL0 (T y) y ((T^[n + 1]) x0)
  have hfix_seq : Filter.Tendsto (fun _ : ℕ => w s (T y) y)
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum_lim
      (fun n => zero_le _) hfix_le
  have hfix_zero : w s (T y) y = 0 := (tendsto_const_nhds_iff).1 hfix_seq
  have hfix_val : (T y : X) = (y : X) :=
    hstrict (T y) y ⟨s, hs0, hfix_zero⟩
  have hfix : T y = y := Subtype.ext hfix_val
  exact ⟨y, hfix, hlim⟩

/- accepted add_to_file helper 4 -/
lemma ennreal_eq_zero_of_le_coe_mul_self {d : ENNReal} (hd : d ≠ ⊤)
    {k : NNReal} (hk : k < 1) (h : d ≤ (k : ENNReal) * d) : d = 0 := by
  have hprod : (k : ENNReal) * d ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top hd
  have hr : d.toReal ≤ (k : ℝ) * d.toReal := by
    have hr0 := (ENNReal.toReal_le_toReal hd hprod).2 h
    simpa [ENNReal.toReal_mul] using hr0
  have hz : d.toReal = 0 := by
    nlinarith [ENNReal.toReal_nonneg (a := d)]
  exact (ENNReal.toReal_eq_zero_iff d).1 hz |>.resolve_right hd

/- verified submission -/
theorem strict_convex_modular_fixed_point
    {X : Type*} (b : X) (w : NNReal → X → X → ENNReal)
    (hself : ∀ (l : NNReal), 0 < l → ∀ x : X, w l x x = 0)
    (hsymm : ∀ (l : NNReal), 0 < l → ∀ x y : X, w l x y = w l y x)
    (hstrict : ∀ x y : X, (∃ l : NNReal, 0 < l ∧ w l x y = 0) → x = y)
    (hconv : ∀ (l m : NNReal), 0 < l → 0 < m → ∀ x y z : X,
      w (l + m) x y ≤ ((l : ENNReal) / (l + m)) * w l x z +
        ((m : ENNReal) / (l + m)) * w m y z)
    (hcomplete : ∀ (x : ℕ → {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤})
      (l : NNReal), 0 < l →
      Filter.Tendsto (fun p : ℕ × ℕ => w l (x p.1) (x p.2))
        (Filter.atTop ×ˢ Filter.atTop) (nhds 0) →
      ∃ y : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
        Filter.Tendsto (fun n => w l (x n) y) Filter.atTop (nhds 0))
    (T : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤} →
      {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤})
    (hcontractive : ∃ k L : NNReal, 0 < k ∧ k < 1 ∧ 0 < L ∧
      ∀ x y : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
        ∀ l : NNReal, 0 < l → l ≤ L → w (k * l) (T x) (T y) ≤ w l x y) :
    ((∀ l : NNReal, 0 < l →
        ∃ x : {x : X // ∃ m : NNReal, 0 < m ∧ w m x b < ⊤},
          w l x (T x) < ⊤) →
      ∃ x : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤}, T x = x) ∧
    ((∀ l : NNReal, 0 < l →
        ∀ x y : {x : X // ∃ m : NNReal, 0 < m ∧ w m x b < ⊤}, w l x y < ⊤) →
      ∃ xstar : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
        T xstar = xstar ∧
        (∀ y : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
          T y = y → y = xstar) ∧
        ∀ x : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
          ∃ l : NNReal, 0 < l ∧
            Filter.Tendsto (fun n : ℕ => w l ((T^[n]) x) xstar)
              Filter.atTop (nhds 0)) := by
  constructor
  · intro hdisp
    rcases hcontractive with ⟨k, L, hk0, hk1, hL0, hcontr⟩
    let a : NNReal := (1 - (1 + k) / 2) * L
    have ha0 : 0 < a := by
      dsimp [a]
      have h : (1 + k) / 2 < 1 := by nlinarith [hk1]
      exact mul_pos (tsub_pos_of_lt h) hL0
    rcases hdisp a ha0 with ⟨x0, hx0⟩
    rcases modular_fixed_point_of_displacement b w hself hsymm hstrict hconv
        hcomplete T hk0 hk1 hL0 hcontr x0 hx0 with ⟨y, hy, -⟩
    exact ⟨y, hy⟩
  · intro hfinite
    rcases hcontractive with ⟨k, L, hk0, hk1, hL0, hcontr⟩
    let a : NNReal := (1 - (1 + k) / 2) * L
    have ha0 : 0 < a := by
      dsimp [a]
      have h : (1 + k) / 2 < 1 := by nlinarith [hk1]
      exact mul_pos (tsub_pos_of_lt h) hL0
    have hbw : w L b b < ⊤ := by
      rw [hself L hL0 b]
      exact ENNReal.zero_lt_top
    let xb : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤} :=
      ⟨b, ⟨L, hL0, hbw⟩⟩
    have hxb : w a xb (T xb) < ⊤ := hfinite a ha0 xb (T xb)
    rcases modular_fixed_point_of_displacement b w hself hsymm hstrict hconv
        hcomplete T hk0 hk1 hL0 hcontr xb hxb with ⟨xstar, hstar, -⟩
    have huniq : ∀ y : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
        T y = y → y = xstar := by
      intro y hy
      let d : ENNReal := w L y xstar
      have hdne : d ≠ ⊤ := by
        dsimp [d]
        exact ne_of_lt (hfinite L hL0 y xstar)
      have hctr0 := hcontr y xstar L hL0 le_rfl
      have hctr : w (k * L) y xstar ≤ d := by
        simpa [d, hy, hstar] using hctr0
      have hkL : 0 < k * L := mul_pos hk0 hL0
      have hkL_le : k * L ≤ L := by
        calc
          k * L ≤ 1 * L := mul_le_mul_right' hk1.le L
          _ = L := one_mul L
      have hsc := modular_scale_le w hself hconv hkL hkL_le y xstar
      have hcoef : (((k * L : NNReal) : ENNReal) / (L : ENNReal)) = (k : ENNReal) := by
        have h0 : (L : ENNReal) ≠ 0 := by exact_mod_cast ne_of_gt hL0
        have ht : (L : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
        calc
          (((k * L : NNReal) : ENNReal) / (L : ENNReal))
              = ((k : ENNReal) * (L : ENNReal)) / (L : ENNReal) := by
                  rw [ENNReal.coe_mul]
          _ = (k : ENNReal) * ((L : ENNReal) / (L : ENNReal)) := by
                  rw [mul_div_assoc]
          _ = (k : ENNReal) := by
                  rw [ENNReal.div_self h0 ht, mul_one]
      have hdself : d ≤ (k : ENNReal) * d := by
        calc
          d = w L y xstar := rfl
          _ ≤ (((k * L : NNReal) : ENNReal) / (L : ENNReal)) *
                w (k * L) y xstar := hsc
          _ = (k : ENNReal) * w (k * L) y xstar := by rw [hcoef]
          _ ≤ (k : ENNReal) * d := mul_le_mul_left' hctr _
      have hdzero : d = 0 := ennreal_eq_zero_of_le_coe_mul_self hdne hk1 hdself
      have hval : (y : X) = (xstar : X) :=
        hstrict y xstar ⟨L, hL0, hdzero⟩
      exact Subtype.ext hval
    refine ⟨xstar, hstar, huniq, ?_⟩
    intro x
    have hx : w a x (T x) < ⊤ := hfinite a ha0 x (T x)
    rcases modular_fixed_point_of_displacement b w hself hsymm hstrict hconv
        hcomplete T hk0 hk1 hL0 hcontr x hx with ⟨y, hy, hlim⟩
    have hyx : y = xstar := huniq y hy
    exact ⟨L, hL0, by simpa [hyx] using hlim⟩

end Rollout_p1151_strict_convex_modular_fixed_point

#check_dependency_graph "Rollout_p1151_strict_convex_modular_fixed_point.strict_convex_modular_fixed_point" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"((∀ (l : NNReal), 0 < l → ∃ x, w l ↑x ↑(T x) < ⊤) → ∃ x, T x = x) ∧ ((∀ (l : NNReal), 0 < l → ∀ (x y : { x // ∃ m, 0 < m ∧ w m x b < ⊤ }), w l ↑x ↑y < ⊤) → ∃ xstar, T xstar = xstar ∧ (∀ (y : { x // ∃ l, 0 < l ∧ w l x b < ⊤ }), T y = y → y = xstar) ∧ ∀ (x : { x // ∃ l, 0 < l ∧ w l x b < ⊤ }), ∃ l, 0 < l ∧ Filter.Tendsto (fun n => w l ↑(T^[n] x) ↑xstar) Filter.atTop (nhds 0))\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hself\",\"statement\":\"∀ (l : NNReal), 0 < l → ∀ (x : X), w l x x = 0\"},{\"name\":\"hsymm\",\"statement\":\"∀ (l : NNReal), 0 < l → ∀ (x y : X), w l x y = w l y x\"},{\"name\":\"hstrict\",\"statement\":\"∀ (x y : X), (∃ l, 0 < l ∧ w l x y = 0) → x = y\"},{\"name\":\"hconv\",\"statement\":\"∀ (l m : NNReal), 0 < l → 0 < m → ∀ (x y z : X), w (l + m) x y ≤ ↑l / (↑l + ↑m) * w l x z + ↑m / (↑l + ↑m) * w m y z\"},{\"name\":\"hcomplete\",\"statement\":\"∀ (x : ℕ → { x // ∃ l, 0 < l ∧ w l x b < ⊤ }) (l : NNReal), 0 < l → Filter.Tendsto (fun p => w l ↑(x p.1) ↑(x p.2)) (Filter.atTop ×ˢ Filter.atTop) (nhds 0) → ∃ y, Filter.Tendsto (fun n => w l ↑(x n) ↑y) Filter.atTop (nhds 0)\"},{\"name\":\"hcontractive\",\"statement\":\"∃ k L, 0 < k ∧ k < 1 ∧ 0 < L ∧ ∀ (x y : { x // ∃ l, 0 < l ∧ w l x b < ⊤ }) (l : NNReal), 0 < l → l ≤ L → w (k * l) ↑(T x) ↑(T y) ≤ w l ↑x ↑y\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1151_strict_convex_modular_fixed_point\",\"reconstructedProofSha256\":\"cea97ffc432c413055eec64974cc014dba1d8d6801bcea53159b47603dfff4ec\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1151_strict_convex_modular_fixed_point.strict_convex_modular_fixed_point\",\"topologySha256\":\"d75903c07f3cb6dafb1d31aa074ca2f36785d75d8e5ad8a06a5b6745d6002ea8\"}"

namespace Rollout_p1180_inversealong_units

-- graph_id: p1180_inversealong_units
-- topology_sha256: 14da5c37624322edd95e16aea21e85ecc3ac5185160255fc6420240c3d494907
/- verified submission -/
lemma rightIdeal_subset_of_units
    {R : Type*} [Ring R] {b d : R} (u v : Rˣ)
    (h : Set.range (fun y : R => b * y) ⊆ Set.range (fun y : R => d * y)) :
    Set.range (fun y : R => ((u : R) * b * (v : R)) * y) ⊆
      Set.range (fun y : R => ((u : R) * d * (v : R)) * y) := by
  intro z hz
  rcases hz with ⟨y, rfl⟩
  have hb : b * ((v : R) * y) ∈ Set.range (fun y : R => d * y) := by
    exact h ⟨((v : R) * y), rfl⟩
  rcases hb with ⟨w, hw⟩
  use (((v⁻¹ : Rˣ) : R) * w)
  simpa [mul_assoc] using congrArg (fun t : R => (u : R) * t) hw

lemma rightIdeal_eq_of_units
    {R : Type*} [Ring R] {b d : R} (u v : Rˣ)
    (h : Set.range (fun y : R => b * y) = Set.range (fun y : R => d * y)) :
    Set.range (fun y : R => ((u : R) * b * (v : R)) * y) =
      Set.range (fun y : R => ((u : R) * d * (v : R)) * y) := by
  apply Set.Subset.antisymm
  · exact rightIdeal_subset_of_units u v (subset_of_eq h)
  · exact rightIdeal_subset_of_units u v (subset_of_eq h.symm)

lemma leftIdeal_subset_of_units
    {R : Type*} [Ring R] {b d : R} (u v : Rˣ)
    (h : Set.range (fun y : R => y * b) ⊆ Set.range (fun y : R => y * d)) :
    Set.range (fun y : R => y * ((u : R) * b * (v : R))) ⊆
      Set.range (fun y : R => y * ((u : R) * d * (v : R))) := by
  intro z hz
  rcases hz with ⟨y, rfl⟩
  have hb : ((y * (u : R)) * b) ∈ Set.range (fun y : R => y * d) := by
    exact h ⟨(y * (u : R)), rfl⟩
  rcases hb with ⟨w, hw⟩
  use w * (((u⁻¹ : Rˣ) : R))
  simpa [mul_assoc] using congrArg (fun t : R => t * (v : R)) hw

lemma leftIdeal_eq_of_units
    {R : Type*} [Ring R] {b d : R} (u v : Rˣ)
    (h : Set.range (fun y : R => y * b) = Set.range (fun y : R => y * d)) :
    Set.range (fun y : R => y * ((u : R) * b * (v : R))) =
      Set.range (fun y : R => y * ((u : R) * d * (v : R))) := by
  apply Set.Subset.antisymm
  · exact leftIdeal_subset_of_units u v (subset_of_eq h)
  · exact leftIdeal_subset_of_units u v (subset_of_eq h.symm)

theorem inverseAlong_units
    {R : Type*} [Ring R] {a b d : R} (r s : Rˣ)
    (h_inner : b * a * b = b)
    (h_right : Set.range (fun y : R => b * y) = Set.range (fun y : R => d * y))
    (h_left : Set.range (fun y : R => y * b) = Set.range (fun y : R => y * d)) :
    (((r : R) * b * ((s⁻¹ : Rˣ) : R)) *
          ((s : R) * a * ((r⁻¹ : Rˣ) : R)) *
          ((r : R) * b * ((s⁻¹ : Rˣ) : R)) =
        (r : R) * b * ((s⁻¹ : Rˣ) : R)) ∧
      Set.range (fun y : R => ((r : R) * b * ((s⁻¹ : Rˣ) : R)) * y) =
        Set.range (fun y : R => ((r : R) * d * ((s⁻¹ : Rˣ) : R)) * y) ∧
      Set.range (fun y : R => y * ((r : R) * b * ((s⁻¹ : Rˣ) : R))) =
        Set.range (fun y : R => y * ((r : R) * d * ((s⁻¹ : Rˣ) : R))) := by
  refine ⟨?_, ?_, ?_⟩
  · calc
      ((r : R) * b * ((s⁻¹ : Rˣ) : R)) *
          ((s : R) * a * ((r⁻¹ : Rˣ) : R)) *
          ((r : R) * b * ((s⁻¹ : Rˣ) : R))
          = (r : R) * (b * a * b) * ((s⁻¹ : Rˣ) : R) := by
            simp [mul_assoc]
      _ = (r : R) * b * ((s⁻¹ : Rˣ) : R) := by
            simp [h_inner, mul_assoc]
  · exact rightIdeal_eq_of_units r s⁻¹ h_right
  · exact leftIdeal_eq_of_units r s⁻¹ h_left

end Rollout_p1180_inversealong_units

#check_dependency_graph "Rollout_p1180_inversealong_units.inverseAlong_units" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"↑r * b * ↑s⁻¹ * (↑s * a * ↑r⁻¹) * (↑r * b * ↑s⁻¹) = ↑r * b * ↑s⁻¹ ∧ ((Set.range fun y => ↑r * b * ↑s⁻¹ * y) = Set.range fun y => ↑r * d * ↑s⁻¹ * y) ∧ (Set.range fun y => y * (↑r * b * ↑s⁻¹)) = Set.range fun y => y * (↑r * d * ↑s⁻¹)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"h_inner\",\"statement\":\"b * a * b = b\"},{\"name\":\"h_right\",\"statement\":\"(Set.range fun y => b * y) = Set.range fun y => d * y\"},{\"name\":\"h_left\",\"statement\":\"(Set.range fun y => y * b) = Set.range fun y => y * d\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1180_inversealong_units\",\"reconstructedProofSha256\":\"0abd807556561f5c6db374723fbd7946a23f6ffc525373644d657d7653813c8a\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1180_inversealong_units.inverseAlong_units\",\"topologySha256\":\"14da5c37624322edd95e16aea21e85ecc3ac5185160255fc6420240c3d494907\"}"

namespace Rollout_p1193_parseval_frame_spans_orthogonal

-- graph_id: p1193_parseval_frame_spans_orthogonal
-- topology_sha256: 186c22b947cae8b637db1e4cb4152e1e644df8cfea430cf772137e20a4e64fdf
/- accepted add_to_file helper 1 -/
lemma rankOneInner_isSymmetric {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] (a : E) :
    (((innerₗ E) a).smulRight a).IsSymmetric := by
  intro x y
  simp [LinearMap.smulRight_apply, innerₗ_apply_apply,
    real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm x a]
  exact mul_comm (inner ℝ x a) (inner ℝ a y)

noncomputable def partialFrame {M N : ℕ}
    (φ : Fin N → EuclideanSpace ℝ (Fin M)) (J : Set (Fin N)) :
    EuclideanSpace ℝ (Fin M) →ₗ[ℝ] EuclideanSpace ℝ (Fin M) := by
  classical
  exact ∑ i ∈ Finset.univ.filter (fun i => i ∈ J),
    (((innerₗ (EuclideanSpace ℝ (Fin M))) (φ i)).smulRight (φ i))

/- accepted add_to_file helper 2 -/
lemma partialFrame_isSymmetric {M N : ℕ}
    (φ : Fin N → EuclideanSpace ℝ (Fin M)) (J : Set (Fin N)) :
    (partialFrame φ J).IsSymmetric := by
  classical
  unfold partialFrame
  apply LinearMap.isSymmetric_sum
  intro i hi
  exact rankOneInner_isSymmetric (φ i)

/- accepted add_to_file helper 3 -/
lemma partialFrame_mem_span {M N : ℕ}
    (φ : Fin N → EuclideanSpace ℝ (Fin M)) (J : Set (Fin N))
    (x : EuclideanSpace ℝ (Fin M)) :
    partialFrame φ J x ∈ Submodule.span ℝ (φ '' J) := by
  classical
  unfold partialFrame
  simp
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨i, by simpa using hi, rfl⟩

/- accepted add_to_file helper 4 -/
lemma symmetric_eq_id_of_inner_map_self {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (T : E →ₗ[ℝ] E)
    (hT : T.IsSymmetric)
    (hdiag : ∀ x : E, inner ℝ (T x) x = inner ℝ x x) :
    T = LinearMap.id := by
  let R : E →ₗ[ℝ] E := T - LinearMap.id
  have hsymm : R.IsSymmetric := hT.sub LinearMap.IsSymmetric.id
  have hdiagR : ∀ z : E, inner ℝ (R z) z = 0 := by
    intro z
    simp only [R, LinearMap.sub_apply, LinearMap.id_apply]
    rw [inner_sub_left, hdiag z, sub_self]
  have hbilin : ∀ x y : E, inner ℝ (R x) y = 0 := by
    intro x y
    have hp := hsymm.inner_map_polarization x y
    rw [hdiagR (x + y), hdiagR (x - y)] at hp
    simpa using hp
  ext x
  have hzero : inner ℝ (R x) (R x) = 0 := hbilin x (R x)
  have hRx : R x = 0 := (inner_self_eq_zero (𝕜 := ℝ) (x := R x)).mp hzero
  have : T x - x = 0 := by
    simpa [R] using hRx
  exact sub_eq_zero.mp this

/- accepted add_to_file helper 5 -/
lemma partialFrame_univ_eq_id_of_parseval {M N : ℕ}
    (φ : Fin N → EuclideanSpace ℝ (Fin M))
    (hParseval : ∀ x : EuclideanSpace ℝ (Fin M),
      (∑ i : Fin N, (inner ℝ x (φ i)) ^ 2) = ‖x‖ ^ 2) :
    partialFrame φ Set.univ = LinearMap.id := by
  classical
  apply symmetric_eq_id_of_inner_map_self
  · exact partialFrame_isSymmetric φ Set.univ
  · intro x
    calc
      inner ℝ (partialFrame φ Set.univ x) x
          = ∑ i : Fin N, (inner ℝ x (φ i)) ^ 2 := by
            unfold partialFrame
            simp [innerₗ_apply_apply, real_inner_comm]
            rw [inner_sum]
            apply Finset.sum_congr rfl
            intro i hi
            rw [real_inner_smul_right]
            ring
      _ = ‖x‖ ^ 2 := hParseval x
      _ = inner ℝ x x := by rw [real_inner_self_eq_norm_sq]

/- accepted add_to_file helper 6 -/
lemma partialFrame_add_compl {M N : ℕ}
    (φ : Fin N → EuclideanSpace ℝ (Fin M)) (J : Set (Fin N)) :
    partialFrame φ J + partialFrame φ Jᶜ = partialFrame φ Set.univ := by
  classical
  ext x
  simp [partialFrame, Finset.sum_filter_add_sum_filter_not]

/- verified submission -/
theorem parseval_frame_spans_orthogonal
    (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (φ : Fin N → EuclideanSpace ℝ (Fin M))
    (hParseval : ∀ x : EuclideanSpace ℝ (Fin M),
      (∑ i : Fin N, (inner ℝ x (φ i)) ^ 2) = ‖x‖ ^ 2)
    (I : Set (Fin N))
    (hdisjoint : Submodule.span ℝ (φ '' I) ⊓
      Submodule.span ℝ (φ '' Iᶜ) = ⊥) :
    ∀ u ∈ Submodule.span ℝ (φ '' I),
      ∀ v ∈ Submodule.span ℝ (φ '' Iᶜ), inner ℝ u v = 0 := by
  classical
  let E := EuclideanSpace ℝ (Fin M)
  let A : Submodule ℝ E := Submodule.span ℝ (φ '' I)
  let B : Submodule ℝ E := Submodule.span ℝ (φ '' Iᶜ)
  let SI : E →ₗ[ℝ] E := partialFrame φ I
  let SC : E →ₗ[ℝ] E := partialFrame φ Iᶜ
  have hframe : partialFrame φ Set.univ = LinearMap.id :=
    partialFrame_univ_eq_id_of_parseval φ hParseval
  have hdecomp : ∀ x : E, SI x + SC x = x := by
    intro x
    have happ := congrArg (fun T : E →ₗ[ℝ] E => T x)
      (partialFrame_add_compl φ I)
    rw [hframe] at happ
    simpa [SI, SC] using happ
  have hSI_zero_on_B : ∀ v ∈ B, SI v = 0 := by
    intro v hv
    have hSIv_A : SI v ∈ A := by
      simpa [SI, A, E] using partialFrame_mem_span φ I v
    have hSCv_B : SC v ∈ B := by
      simpa [SC, B, E] using partialFrame_mem_span φ Iᶜ v
    have hSIv_B : SI v ∈ B := by
      have hEq : SI v = v - SC v := eq_sub_of_add_eq (hdecomp v)
      rw [hEq]
      exact B.sub_mem hv hSCv_B
    have hbot : SI v ∈ (⊥ : Submodule ℝ E) := by
      rw [← hdisjoint]
      change SI v ∈ A ⊓ B
      exact ⟨hSIv_A, hSIv_B⟩
    exact (Submodule.mem_bot ℝ).mp hbot
  intro u hu v hv
  have hSIu_A : SI u ∈ A := by
    simpa [SI, A, E] using partialFrame_mem_span φ I u
  have hSCu_B : SC u ∈ B := by
    simpa [SC, B, E] using partialFrame_mem_span φ Iᶜ u
  have hSCu_A : SC u ∈ A := by
    have hEq : SC u = u - SI u := eq_sub_of_add_eq' (hdecomp u)
    rw [hEq]
    exact A.sub_mem hu hSIu_A
  have hSCu_zero : SC u = 0 := by
    have hbot : SC u ∈ (⊥ : Submodule ℝ E) := by
      rw [← hdisjoint]
      change SC u ∈ A ⊓ B
      exact ⟨hSCu_A, hSCu_B⟩
    exact (Submodule.mem_bot ℝ).mp hbot
  have hSIu : SI u = u := by
    have h := hdecomp u
    rw [hSCu_zero, add_zero] at h
    exact h
  have hSIv : SI v = 0 := hSI_zero_on_B v hv
  calc
    inner ℝ u v = inner ℝ (SI u) v := by rw [hSIu]
    _ = inner ℝ u (SI v) := partialFrame_isSymmetric φ I u v
    _ = inner ℝ u 0 := by rw [hSIv]
    _ = 0 := by rw [inner_zero_right]

end Rollout_p1193_parseval_frame_spans_orthogonal

#check_dependency_graph "Rollout_p1193_parseval_frame_spans_orthogonal.parseval_frame_spans_orthogonal" against "{\"edges\":[{\"conclusion\":{\"name\":\"hframe\",\"statement\":\"Rollout_p1193_parseval_frame_spans_orthogonal.partialFrame φ Set.univ = LinearMap.id\"},\"graphEdgeId\":\"h_001_hframe\",\"premises\":[{\"name\":\"hParseval\",\"statement\":\"∀ (x : EuclideanSpace ℝ (Fin M)), ∑ i, inner ℝ x (φ i) ^ 2 = ‖x‖ ^ 2\"}],\"rawEdgeId\":\"telescope_13\"},{\"conclusion\":{\"name\":\"hSIu_A\",\"statement\":\"SI u ∈ A\"},\"graphEdgeId\":\"h_004_hsiu_a\",\"premises\":[],\"rawEdgeId\":\"telescope_20\"},{\"conclusion\":{\"name\":\"hSCu_B\",\"statement\":\"SC u ∈ B\"},\"graphEdgeId\":\"h_005_hscu_b\",\"premises\":[],\"rawEdgeId\":\"telescope_21\"},{\"conclusion\":{\"name\":\"hdecomp\",\"statement\":\"∀ (x : E), SI x + SC x = x\"},\"graphEdgeId\":\"h_002_hdecomp\",\"premises\":[{\"name\":\"hframe\",\"statement\":\"Rollout_p1193_parseval_frame_spans_orthogonal.partialFrame φ Set.univ = LinearMap.id\"}],\"rawEdgeId\":\"telescope_14\"},{\"conclusion\":{\"name\":\"hSI_zero_on_B\",\"statement\":\"∀ v ∈ B, SI v = 0\"},\"graphEdgeId\":\"h_003_hsi_zero_on_b\",\"premises\":[{\"name\":\"hdisjoint\",\"statement\":\"Submodule.span ℝ (φ '' I) ⊓ Submodule.span ℝ (φ '' Iᶜ) = ⊥\"},{\"name\":\"hdecomp\",\"statement\":\"∀ (x : E), SI x + SC x = x\"}],\"rawEdgeId\":\"telescope_15\"},{\"conclusion\":{\"name\":\"hSCu_A\",\"statement\":\"SC u ∈ A\"},\"graphEdgeId\":\"h_006_hscu_a\",\"premises\":[{\"name\":\"hdecomp\",\"statement\":\"∀ (x : E), SI x + SC x = x\"},{\"name\":\"hu\",\"statement\":\"u ∈ Submodule.span ℝ (φ '' I)\"},{\"name\":\"hSIu_A\",\"statement\":\"SI u ∈ A\"}],\"rawEdgeId\":\"telescope_22\"},{\"conclusion\":{\"name\":\"hSCu_zero\",\"statement\":\"SC u = 0\"},\"graphEdgeId\":\"h_007_hscu_zero\",\"premises\":[{\"name\":\"hdisjoint\",\"statement\":\"Submodule.span ℝ (φ '' I) ⊓ Submodule.span ℝ (φ '' Iᶜ) = ⊥\"},{\"name\":\"hSCu_B\",\"statement\":\"SC u ∈ B\"},{\"name\":\"hSCu_A\",\"statement\":\"SC u ∈ A\"}],\"rawEdgeId\":\"telescope_23\"},{\"conclusion\":{\"name\":\"hSIv\",\"statement\":\"SI v = 0\"},\"graphEdgeId\":\"h_009_hsiv\",\"premises\":[{\"name\":\"hSI_zero_on_B\",\"statement\":\"∀ v ∈ B, SI v = 0\"},{\"name\":\"hv\",\"statement\":\"v ∈ Submodule.span ℝ (φ '' Iᶜ)\"}],\"rawEdgeId\":\"telescope_25\"},{\"conclusion\":{\"name\":\"hSIu\",\"statement\":\"SI u = u\"},\"graphEdgeId\":\"h_008_hsiu\",\"premises\":[{\"name\":\"hdecomp\",\"statement\":\"∀ (x : E), SI x + SC x = x\"},{\"name\":\"hSCu_zero\",\"statement\":\"SC u = 0\"}],\"rawEdgeId\":\"telescope_24\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"inner ℝ u v = 0\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hSIu\",\"statement\":\"SI u = u\"},{\"name\":\"hSIv\",\"statement\":\"SI v = 0\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1193_parseval_frame_spans_orthogonal\",\"reconstructedProofSha256\":\"d37f0247e5dd6f81da3dc490b1a5f73d6adc9f4ddf7a0ebc57ff5cd57ca54d4d\",\"selectedEdgeCount\":10,\"theoremName\":\"Rollout_p1193_parseval_frame_spans_orthogonal.parseval_frame_spans_orthogonal\",\"topologySha256\":\"186c22b947cae8b637db1e4cb4152e1e644df8cfea430cf772137e20a4e64fdf\"}"

namespace Rollout_p1226_continuous_quadratic_form_delta_semidefini

-- graph_id: p1226_continuous_quadratic_form_delta_semidefini
-- topology_sha256: fcee227336671d974a9daef65058f17ab415ea536aaf240335313305cad50f04
/- accepted add_to_file helper 1 -/

/-- A fresh copy of a real vector space, used to equip it with a new pre-inner product. -/
structure QuadraticPreHilbert (X : Type u) [AddCommGroup X] [Module ℝ X] where
  val : X

namespace QuadraticPreHilbert

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

def equiv : QuadraticPreHilbert X ≃ X where
  toFun := val
  invFun := mk
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; rfl

instance : AddCommGroup (QuadraticPreHilbert X) := equiv.addCommGroup
instance : Module ℝ (QuadraticPreHilbert X) := Equiv.module ℝ equiv

@[simp] theorem val_zero : (0 : QuadraticPreHilbert X).val = 0 := rfl
@[simp] theorem val_add (x y : QuadraticPreHilbert X) : (x + y).val = x.val + y.val := rfl
@[simp] theorem val_smul (r : ℝ) (x : QuadraticPreHilbert X) : (r • x).val = r • x.val := rfl

/-- The pre-inner product associated with the symmetrization of a continuous bilinear form. -/
@[implicit_reducible]
noncomputable def preCore (bp : X →L[ℝ] X →L[ℝ] ℝ)
    (hnonneg : ∀ x : X, 0 ≤ (bp x x + bp x x) / 2) :
    PreInnerProductSpace.Core ℝ (QuadraticPreHilbert X) where
  inner x y := (bp x.val y.val + bp y.val x.val) / 2
  conj_inner_symm x y := by
    simp [add_comm]
  re_inner_nonneg x := hnonneg x.val
  add_left x y z := by
    simp [map_add]
    ring_nf
  smul_left x y r := by
    simp [map_smul]
    ring_nf

end QuadraticPreHilbert

/- accepted add_to_file helper 2 -/
lemma dominated_bilinear_abs_le_avg
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : X → ℝ) (T : X →L[ℝ] (X →L[ℝ] ℝ))
    (hTq : ∀ x : X, q x = T x x)
    (hTsymm : ∀ x y : X, T x y = T y x)
    (bp : X →L[ℝ] X →L[ℝ] ℝ)
    (hdom : ∀ x : X, |q x| ≤ bp x x)
    (x y : X) :
    |T x y| ≤ (bp x x + bp y y) / 2 := by
  have hpol : T (x+y) (x+y) - T (x-y) (x-y) = 4 * T x y := by
    simp [map_add, map_sub, hTsymm x y]
    ring
  have hpsum : bp (x+y) (x+y) + bp (x-y) (x-y) =
      2 * (bp x x + bp y y) := by
    simp [map_add, map_sub]
    ring
  have hplus : |T (x+y) (x+y)| ≤ bp (x+y) (x+y) := by
    simpa [hTq] using hdom (x+y)
  have hminus : |T (x-y) (x-y)| ≤ bp (x-y) (x-y) := by
    simpa [hTq] using hdom (x-y)
  have hsub : |T (x+y) (x+y) - T (x-y) (x-y)| ≤
      bp (x+y) (x+y) + bp (x-y) (x-y) := by
    calc
      |T (x+y) (x+y) - T (x-y) (x-y)|
          ≤ |T (x+y) (x+y)| + |T (x-y) (x-y)| := abs_sub _ _
      _ ≤ bp (x+y) (x+y) + bp (x-y) (x-y) := add_le_add hplus hminus
  rw [hpol, hpsum] at hsub
  have habs4 : |4 * T x y| = 4 * |T x y| := by norm_num [abs_of_nonneg]
  rw [habs4] at hsub
  nlinarith [abs_nonneg (T x y)]

/- accepted add_to_file helper 3 -/
lemma dominated_bilinear_abs_le_sqrt_mul
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (q : X → ℝ) (T : X →L[ℝ] (X →L[ℝ] ℝ))
    (hTq : ∀ x : X, q x = T x x)
    (hTsymm : ∀ x y : X, T x y = T y x)
    (bp : X →L[ℝ] X →L[ℝ] ℝ)
    (hdom : ∀ x : X, |q x| ≤ bp x x)
    (x y : X) :
    |T x y| ≤ Real.sqrt (bp x x) * Real.sqrt (bp y y) := by
  have hpx : 0 ≤ bp x x := le_trans (abs_nonneg _) (hdom x)
  have hpy : 0 ≤ bp y y := le_trans (abs_nonneg _) (hdom y)
  by_cases hx0 : bp x x = 0
  · by_contra hz
    have hzne : |T x y| ≠ 0 := by
      intro hzero
      apply hz
      rw [hzero]
      positivity
    have hzpos : 0 < |T x y| := lt_of_le_of_ne' (abs_nonneg _) hzne
    let r : ℝ := (bp y y / 2 + 1) / |T x y|
    have hrpos : 0 < r := by positivity
    have hb := dominated_bilinear_abs_le_avg q T hTq hTsymm bp hdom (r • x) y
    simp [hx0, map_smul, abs_mul, abs_of_pos hrpos] at hb
    have hreq : r * |T x y| = bp y y / 2 + 1 := by
      dsimp [r]
      field_simp [ne_of_gt hzpos]
    nlinarith [hpy]
  · by_cases hy0 : bp y y = 0
    · by_contra hz
      have hzne : |T x y| ≠ 0 := by
        intro hzero
        apply hz
        rw [hzero]
        positivity
      have hzpos : 0 < |T x y| := lt_of_le_of_ne' (abs_nonneg _) hzne
      let r : ℝ := (bp x x / 2 + 1) / |T x y|
      have hrpos : 0 < r := by positivity
      have hb := dominated_bilinear_abs_le_avg q T hTq hTsymm bp hdom x (r • y)
      simp [hy0, map_smul, abs_mul, abs_of_pos hrpos] at hb
      have hreq : r * |T x y| = bp x x / 2 + 1 := by
        dsimp [r]
        field_simp [ne_of_gt hzpos]
      nlinarith [hpx]
    · have hxpos : 0 < bp x x := lt_of_le_of_ne hpx (Ne.symm hx0)
      have hypos : 0 < bp y y := lt_of_le_of_ne hpy (Ne.symm hy0)
      let a : ℝ := Real.sqrt (bp x x)
      let b : ℝ := Real.sqrt (bp y y)
      let r : ℝ := Real.sqrt (bp y y / bp x x)
      have hapos : 0 < a := Real.sqrt_pos.mpr hxpos
      have hbpos : 0 < b := Real.sqrt_pos.mpr hypos
      have hrpos : 0 < r := Real.sqrt_pos.mpr (div_pos hypos hxpos)
      have hbasic := dominated_bilinear_abs_le_avg q T hTq hTsymm bp hdom (r • x) y
      simp [map_smul, abs_mul, abs_of_pos hrpos] at hbasic
      have hrsq : r ^ 2 * bp x x = bp y y := by
        dsimp [r]
        rw [Real.sq_sqrt (div_nonneg hpy hpx)]
        field_simp [ne_of_gt hxpos]
      have hscale : r * |T x y| ≤ bp y y := by
        nlinarith
      have hsqrtdiv : r = b / a := by
        dsimp [r, b, a]
        exact Real.sqrt_div hpy (bp x x)
      have hmul : a * r = b := by
        rw [hsqrtdiv]
        field_simp [ne_of_gt hapos]
      have hleft : b * |T x y| ≤ a * (b * b) := by
        have h := mul_le_mul_of_nonneg_left hscale (le_of_lt hapos)
        calc
          b * |T x y| = a * (r * |T x y|) := by
            conv_lhs => rw [← hmul]
            ring
          _ ≤ a * bp y y := h
          _ = a * (b * b) := by
            dsimp [b]
            rw [Real.mul_self_sqrt hpy]
      exact le_of_mul_le_mul_right (by
        calc
          |T x y| * b = b * |T x y| := mul_comm _ _
          _ ≤ a * (b * b) := hleft
          _ = (a * b) * b := by ring) hbpos

/- accepted add_to_file helper 4 -/
lemma dominated_implies_hilbert_factorization
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (q : X → ℝ)
    (T : X →L[ℝ] (X →L[ℝ] ℝ))
    (hTq : ∀ x : X, q x = T x x)
    (hTsymm : ∀ x y : X, T x y = T y x)
    (p : X → ℝ) (bp : X →L[ℝ] X →L[ℝ] ℝ)
    (hp : ∀ x : X, p x = bp x x)
    (hdomp : ∀ x : X, |q x| ≤ p x) :
    ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
        (_ : CompleteSpace H) (A : X →L[ℝ] H) (B : H →L[ℝ] (X →L[ℝ] ℝ)),
      T = B.comp A := by
  have hdom : ∀ x : X, |q x| ≤ bp x x := by
    intro x
    simpa [hp x] using hdomp x
  have hnonneg : ∀ x : X, 0 ≤ (bp x x + bp x x) / 2 := by
    intro x
    have hx : 0 ≤ bp x x := le_trans (abs_nonneg _) (hdom x)
    nlinarith
  let E := QuadraticPreHilbert X
  letI core : PreInnerProductSpace.Core ℝ E := QuadraticPreHilbert.preCore bp hnonneg
  letI semi : SeminormedAddCommGroup E :=
    InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜:=ℝ) (F:=E)
  letI ips : InnerProductSpace ℝ E := InnerProductSpace.ofCore core
  let toE : X →ₗ[ℝ] E := {
    toFun := QuadraticPreHilbert.mk
    map_add' := by intro x y; rfl
    map_smul' := by intro r x; rfl }
  have hbound : ∀ x : X, ‖toE x‖ ≤ Real.sqrt ‖bp‖ * ‖x‖ := by
    intro x
    have hnorm : ‖toE x‖ = Real.sqrt (bp x x) := by
      change ‖(QuadraticPreHilbert.mk x : QuadraticPreHilbert X)‖ = Real.sqrt (bp x x)
      have h : ‖(QuadraticPreHilbert.mk x : QuadraticPreHilbert X)‖ =
          Real.sqrt ((bp x x + bp x x) / 2) := rfl
      rw [h]
      ring_nf
    have habs : |bp x x| ≤ ‖bp x‖ * ‖x‖ := ContinuousLinearMap.le_opNorm (bp x) x
    have hbp : ‖bp x‖ ≤ ‖bp‖ * ‖x‖ := ContinuousLinearMap.le_opNorm bp x
    have hple : bp x x ≤ ‖bp‖ * (‖x‖ * ‖x‖) := by
      calc
        bp x x ≤ |bp x x| := le_abs_self _
        _ ≤ ‖bp x‖ * ‖x‖ := habs
        _ ≤ (‖bp‖ * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right hbp (norm_nonneg _)
        _ = ‖bp‖ * (‖x‖ * ‖x‖) := by ring
    calc
      ‖toE x‖ = Real.sqrt (bp x x) := hnorm
      _ ≤ Real.sqrt (‖bp‖ * (‖x‖ * ‖x‖)) := Real.sqrt_le_sqrt hple
      _ = Real.sqrt ‖bp‖ * ‖x‖ := by
        rw [Real.sqrt_mul (norm_nonneg bp) (‖x‖ * ‖x‖),
          Real.sqrt_mul_self (norm_nonneg x)]
  let A0 : X →L[ℝ] E := LinearMap.mkContinuous toE (Real.sqrt ‖bp‖) hbound
  let Tlin : E →ₗ[ℝ] (X →L[ℝ] ℝ) := {
    toFun := fun e => T e.val
    map_add' := by
      intro e f
      change T (e.val + f.val) = T e.val + T f.val
      exact map_add T e.val f.val
    map_smul' := by
      intro r e
      change T (r • e.val) = r • T e.val
      exact map_smul T r e.val }
  have hTbound : ∀ e : E, ‖Tlin e‖ ≤ Real.sqrt ‖bp‖ * ‖e‖ := by
    intro e
    have hpoint : ∀ y : X,
        ‖T e.val y‖ ≤ (Real.sqrt ‖bp‖ * Real.sqrt (bp e.val e.val)) * ‖y‖ := by
      intro y
      have hc := dominated_bilinear_abs_le_sqrt_mul q T hTq hTsymm bp hdom e.val y
      have hyb := hbound y
      have hnormy : ‖toE y‖ = Real.sqrt (bp y y) := by
        change ‖(QuadraticPreHilbert.mk y : QuadraticPreHilbert X)‖ =
          Real.sqrt (bp y y)
        have h : ‖(QuadraticPreHilbert.mk y : QuadraticPreHilbert X)‖ =
            Real.sqrt ((bp y y + bp y y) / 2) := rfl
        rw [h]
        ring_nf
      rw [hnormy] at hyb
      calc
        ‖T e.val y‖ = |T e.val y| := Real.norm_eq_abs _
        _ ≤ Real.sqrt (bp e.val e.val) * Real.sqrt (bp y y) := hc
        _ ≤ Real.sqrt (bp e.val e.val) * (Real.sqrt ‖bp‖ * ‖y‖) :=
          mul_le_mul_of_nonneg_left hyb (Real.sqrt_nonneg _)
        _ = (Real.sqrt ‖bp‖ * Real.sqrt (bp e.val e.val)) * ‖y‖ := by ring
    have hop := ContinuousLinearMap.opNorm_le_bound (T e.val)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hpoint
    have hnorme : ‖e‖ = Real.sqrt (bp e.val e.val) := by
      change ‖(QuadraticPreHilbert.mk e.val : QuadraticPreHilbert X)‖ =
        Real.sqrt (bp e.val e.val)
      have h : ‖(QuadraticPreHilbert.mk e.val : QuadraticPreHilbert X)‖ =
          Real.sqrt ((bp e.val e.val + bp e.val e.val) / 2) := rfl
      rw [h]
      ring_nf
    calc
      ‖Tlin e‖ ≤ Real.sqrt ‖bp‖ * Real.sqrt (bp e.val e.val) := hop
      _ = Real.sqrt ‖bp‖ * ‖e‖ := by rw [← hnorme]
  let Tpre : E →L[ℝ] (X →L[ℝ] ℝ) :=
    LinearMap.mkContinuous Tlin (Real.sqrt ‖bp‖) hTbound
  have hTpre_norm : ‖Tpre‖ ≤ Real.sqrt ‖bp‖ :=
    LinearMap.mkContinuous_norm_le Tlin (Real.sqrt_nonneg _) hTbound
  have hf : ∀ e f : E, Inseparable e f → Tpre e = Tpre f := by
    intro e f h
    have hnorm0 : ‖e - f‖ = 0 := by
      have hd := h.dist_eq_zero
      rwa [dist_eq_norm] at hd
    have hle : ‖Tpre e - Tpre f‖ ≤ 0 := by
      calc
        ‖Tpre e - Tpre f‖ = ‖Tpre (e - f)‖ := by simp
        _ ≤ ‖Tpre‖ * ‖e - f‖ := ContinuousLinearMap.le_opNorm Tpre (e-f)
        _ ≤ Real.sqrt ‖bp‖ * ‖e - f‖ :=
          mul_le_mul_of_nonneg_right hTpre_norm (norm_nonneg _)
        _ = 0 := by simp [hnorm0]
    exact eq_of_sub_eq_zero (norm_le_zero_iff.mp hle)
  let Tq : SeparationQuotient E →L[ℝ] (X →L[ℝ] ℝ) :=
    SeparationQuotient.liftCLM Tpre hf
  let Q := SeparationQuotient E
  let H := UniformSpace.Completion Q
  let eCompl : Q →L[ℝ] H := UniformSpace.Completion.toComplL
  have hdense : DenseRange eCompl := by
    change DenseRange (UniformSpace.Completion.toComplL (𝕜:=ℝ) (E:=Q))
    simpa [UniformSpace.Completion.coe_toComplL] using
      (UniformSpace.Completion.isDenseInducing_toCompl Q).dense
  have huniform : IsUniformInducing eCompl := by
    change IsUniformInducing (UniformSpace.Completion.toComplL (𝕜:=ℝ) (E:=Q))
    simpa [UniformSpace.Completion.coe_toComplL] using
      (UniformSpace.Completion.isUniformEmbedding_coe Q).isUniformInducing
  let mkQ : E →L[ℝ] Q := SeparationQuotient.mkCLM ℝ E
  let A : X →L[ℝ] H := eCompl.comp (mkQ.comp A0)
  let B : H →L[ℝ] (X →L[ℝ] ℝ) := Tq.extend eCompl
  refine ⟨H, inferInstance, inferInstance, inferInstance, A, B, ?_⟩
  ext x y
  change T x y = (B (A x)) y
  have hAx : A x = eCompl (mkQ (A0 x)) := rfl
  rw [hAx]
  have hB := ContinuousLinearMap.extend_eq Tq hdense huniform (mkQ (A0 x))
  rw [hB]
  have hmk : mkQ (A0 x) = SeparationQuotient.mk (A0 x) := by
    exact SeparationQuotient.mkCLM_apply ℝ E (A0 x)
  rw [hmk]
  change ((SeparationQuotient.liftCLM Tpre hf) (SeparationQuotient.mk (A0 x))) y =
    T x y
  rw [SeparationQuotient.liftCLM_mk]
  simp [Tpre, Tlin, A0, toE]

/- accepted add_to_file helper 5 -/
lemma hilbert_factorization_implies_dominated
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (q : X → ℝ)
    (T : X →L[ℝ] (X →L[ℝ] ℝ))
    (hTq : ∀ x : X, q x = T x x)
    (hfact : ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
        (_ : CompleteSpace H) (A : X →L[ℝ] H) (B : H →L[ℝ] (X →L[ℝ] ℝ)),
      T = B.comp A) :
    ∃ p : X → ℝ,
      (∃ bp : X →L[ℝ] X →L[ℝ] ℝ, ∀ x : X, p x = bp x x) ∧
      (∀ x : X, |q x| ≤ p x) := by
  rcases hfact with ⟨H, instH, instIH, instCH, A, B, hT⟩
  let RieszSymm : StrongDual ℝ H →L[ℝ] H :=
    ((InnerProductSpace.toDual ℝ H).symm.toContinuousLinearEquiv).toContinuousLinearMap
  let C : X →L[ℝ] H := RieszSymm.comp B.flip
  have hC : ∀ x y : X, B (A x) y = inner ℝ (C y) (A x) := by
    intro x y
    have h := InnerProductSpace.toDual_symm_apply (𝕜:=ℝ) (E:=H)
      (x:=A x) (y:=B.flip y)
    change B (A x) y = inner ℝ (RieszSymm (B.flip y)) (A x)
    exact h.symm
  let innerH : H →L[ℝ] H →L[ℝ] ℝ := innerSL ℝ
  let bp : X →L[ℝ] X →L[ℝ] ℝ :=
    (1/2 : ℝ) • (((innerH.comp A).flip.comp A) +
      ((innerH.comp C).flip.comp C))
  refine ⟨fun x => bp x x, ⟨bp, fun x => rfl⟩, ?_⟩
  intro x
  have hq : q x = inner ℝ (C x) (A x) := by
    rw [hTq, hT]
    exact hC x x
  have hnorm : |inner ℝ (C x) (A x)| ≤
      (‖A x‖ ^ 2 + ‖C x‖ ^ 2) / 2 := by
    calc
      |inner ℝ (C x) (A x)| ≤ ‖C x‖ * ‖A x‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖A x‖ ^ 2 + ‖C x‖ ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖C x‖ - ‖A x‖), norm_nonneg (C x), norm_nonneg (A x)]
  have hp : bp x x = (‖A x‖ ^ 2 + ‖C x‖ ^ 2) / 2 := by
    simp [bp]
    change 2⁻¹ * inner ℝ (A x) (A x) + 2⁻¹ * inner ℝ (C x) (C x) =
      (‖A x‖ ^ 2 + ‖C x‖ ^ 2) / 2
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  rw [hq]
  change |inner ℝ (C x) (A x)| ≤ bp x x
  rw [hp]
  exact hnorm

/- verified submission -/
theorem continuous_quadratic_form_delta_semidefinite_iff_hilbert_factorization
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (q : X → ℝ)
    (hq : ∃ b : X →L[ℝ] X →L[ℝ] ℝ, ∀ x : X, q x = b x x)
    (T : X →L[ℝ] (X →L[ℝ] ℝ))
    (hTq : ∀ x : X, q x = T x x)
    (hTsymm : ∀ x y : X, T x y = T y x) :
    ((∃ q₁ q₂ : X → ℝ,
        (∃ b₁ : X →L[ℝ] X →L[ℝ] ℝ, ∀ x : X, q₁ x = b₁ x x) ∧
        (∃ b₂ : X →L[ℝ] X →L[ℝ] ℝ, ∀ x : X, q₂ x = b₂ x x) ∧
        (∀ x : X, 0 ≤ q₁ x) ∧
        (∀ x : X, 0 ≤ q₂ x) ∧
        (∀ x : X, q x = q₁ x - q₂ x)) ↔
      (∃ p : X → ℝ,
        (∃ bp : X →L[ℝ] X →L[ℝ] ℝ, ∀ x : X, p x = bp x x) ∧
        (∀ x : X, |q x| ≤ p x))) ∧
    ((∃ p : X → ℝ,
        (∃ bp : X →L[ℝ] X →L[ℝ] ℝ, ∀ x : X, p x = bp x x) ∧
        (∀ x : X, |q x| ≤ p x)) ↔
      (∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
          (_ : CompleteSpace H) (A : X →L[ℝ] H) (B : H →L[ℝ] (X →L[ℝ] ℝ)),
        T = B.comp A)) := by
  constructor
  · constructor
    · rintro ⟨q₁, q₂, hq₁, hq₂, hq₁pos, hq₂pos, hqdiff⟩
      rcases hq₁ with ⟨b₁, hb₁⟩
      rcases hq₂ with ⟨b₂, hb₂⟩
      refine ⟨fun x => q₁ x + q₂ x, ?_, ?_⟩
      · refine ⟨b₁ + b₂, ?_⟩
        intro x
        simp [hb₁ x, hb₂ x]
      · intro x
        rw [hqdiff x]
        calc
          |q₁ x - q₂ x| ≤ |q₁ x| + |q₂ x| := abs_sub _ _
          _ = q₁ x + q₂ x := by
            rw [abs_of_nonneg (hq₁pos x), abs_of_nonneg (hq₂pos x)]
    · rintro ⟨p, hbp, hdom⟩
      rcases hbp with ⟨bp, hp⟩
      refine ⟨fun x => (p x + q x) / 2, fun x => (p x - q x) / 2, ?_, ?_, ?_, ?_, ?_⟩
      · refine ⟨(1/2 : ℝ) • (bp + T), ?_⟩
        intro x
        simp [hp x, hTq x]
        ring
      · refine ⟨(1/2 : ℝ) • (bp - T), ?_⟩
        intro x
        simp [hp x, hTq x]
        ring
      · intro x
        have hqabs := abs_le.mp (hdom x)
        nlinarith
      · intro x
        have hqabs := abs_le.mp (hdom x)
        nlinarith
      · intro x
        ring
  · constructor
    · rintro ⟨p, ⟨bp, hp⟩, hdom⟩
      exact dominated_implies_hilbert_factorization q T hTq hTsymm p bp hp hdom
    · intro hfact
      exact hilbert_factorization_implies_dominated q T hTq hfact

end Rollout_p1226_continuous_quadratic_form_delta_semidefini

#check_dependency_graph "Rollout_p1226_continuous_quadratic_form_delta_semidefini.continuous_quadratic_form_delta_semidefinite_iff_hilbert_factorization" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"((∃ q₁ q₂, (∃ b₁, ∀ (x : X), q₁ x = (b₁ x) x) ∧ (∃ b₂, ∀ (x : X), q₂ x = (b₂ x) x) ∧ (∀ (x : X), 0 ≤ q₁ x) ∧ (∀ (x : X), 0 ≤ q₂ x) ∧ ∀ (x : X), q x = q₁ x - q₂ x) ↔ ∃ p, (∃ bp, ∀ (x : X), p x = (bp x) x) ∧ ∀ (x : X), |q x| ≤ p x) ∧ ((∃ p, (∃ bp, ∀ (x : X), p x = (bp x) x) ∧ ∀ (x : X), |q x| ≤ p x) ↔ ∃ H x x_1, ∃ (_ : CompleteSpace H), ∃ A B, T = B.comp A)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"CompleteSpace X\"},{\"name\":\"hTq\",\"statement\":\"∀ (x : X), q x = (T x) x\"},{\"name\":\"hTsymm\",\"statement\":\"∀ (x y : X), (T x) y = (T y) x\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1226_continuous_quadratic_form_delta_semidefini\",\"reconstructedProofSha256\":\"7ef62ab1e754f1daf0dc4981b42590c7d7135acd677d6fba909d8229bb88c864\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1226_continuous_quadratic_form_delta_semidefini.continuous_quadratic_form_delta_semidefinite_iff_hilbert_factorization\",\"topologySha256\":\"fcee227336671d974a9daef65058f17ab415ea536aaf240335313305cad50f04\"}"

namespace Rollout_p1227_discrete_add_subgroup_covering

-- graph_id: p1227_discrete_add_subgroup_covering
-- topology_sha256: 37dc515db3c9a5abba24bc857578d4649ea4d16bcd42ddc2a2cc4e5fe39fc62d
/- accepted add_to_file helper 1 -/

open scoped Pointwise Topology
open Filter Set

lemma cover_nat_scale_of_local_cover
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (K : Set E) (L : AddSubgroup E)
    (hK_zero : (0 : E) ∈ K)
    (hK_star : StarConvex ℝ 0 K)
    (ε ε₁ : ℝ) (hε_pos : 0 < ε) (hε_lt_one : ε < 1)
    (q : ℕ) (hq_pos : 0 < q)
    (hq_recip : (q : ℝ) + 1 > 1 / (1 - ε))
    (hε₁ : ε₁ = (q : ℝ) * ε)
    (hcover : K ⊆ Set.image2 (· + ·) (L : Set E)
      ((fun x => ε • x) '' K)) :
    ∀ m : ℕ,
      (fun x => (m : ℝ) • x) '' K ⊆
        Set.image2 (· + ·) (L : Set E)
          ((fun x => ε₁ • x) '' K) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro y hy
      rcases hy with ⟨k, hk, rfl⟩
      have hkcover := hcover hk
      rw [Set.mem_image2] at hkcover
      rcases hkcover with ⟨l, hl, z, hz, hlz⟩
      rcases hz with ⟨k', hk', rfl⟩
      by_cases hmq : m ≤ q
      · let k₂ : E := ((m : ℝ) / (q : ℝ)) • k'
        have hk₂ : k₂ ∈ K := by
          dsimp [k₂]
          apply hK_star.smul_mem hk'
          · positivity
          · have hm : (m : ℝ) ≤ q := by exact_mod_cast hmq
            have hq : (0 : ℝ) < q := by exact_mod_cast hq_pos
            exact (div_le_one hq).2 hm
        refine Set.mem_image2.2 ⟨m • l, AddSubgroup.nsmul_mem L hl m,
          ε₁ • k₂, Set.mem_image_of_mem (fun x => ε₁ • x) hk₂, ?_⟩
        change m • l + ε₁ • k₂ = (m : ℝ) • k
        rw [← hlz]
        simp only [hε₁]
        rw [smul_add]
        congr 1
        · norm_cast
        · dsimp [k₂]
          rw [← smul_assoc, ← smul_assoc]
          congr 1
          change ((q : ℝ) * ε) * ((m : ℝ) * (q : ℝ)⁻¹) = (m : ℝ) * ε
          field_simp [show (q : ℝ) ≠ 0 by positivity]
      · have hm_pos : 0 < m := lt_trans hq_pos (Nat.not_le.mp hmq)
        let r : ℕ := ⌈(m : ℝ) * ε⌉₊
        have hmr_real : (m : ℝ) * ε < (m : ℝ) - 1 := by
          have hmgt : (m : ℝ) > 1 / (1 - ε) := by
            have hmq_nat : q + 1 ≤ m := Nat.succ_le_of_lt (Nat.not_le.mp hmq)
            have hm_q : (q : ℝ) + 1 ≤ m := by exact_mod_cast hmq_nat
            exact lt_of_lt_of_le hq_recip hm_q
          have hden : 0 < 1 - ε := sub_pos.mpr hε_lt_one
          have hmreal : (0 : ℝ) < m := by positivity
          have h1 : (1 : ℝ) / m < 1 - ε := (one_div_lt hmreal hden).2 hmgt
          have hmul := mul_lt_mul_of_pos_left h1 hmreal
          field_simp [show (m : ℝ) ≠ 0 by positivity] at hmul
          nlinarith
        have hrlt : r < m := by
          have hle : r ≤ m - 1 := by
            rw [Nat.ceil_le]
            have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
              rw [Nat.cast_sub (Nat.succ_le_iff.mpr hm_pos)]
              simp
            rw [hcast]
            exact le_of_lt hmr_real
          exact lt_of_le_of_lt hle (Nat.pred_lt hm_pos.ne')
        have hzscale : (m * ε : ℝ) • k' ∈ (fun x => (r : ℝ) • x) '' K := by
          by_cases hr : r = 0
          · have hnonpos : (m : ℝ) * ε ≤ 0 := by
              have hle0 : (m : ℝ) * ε ≤ (r : ℝ) := Nat.le_ceil _
              rw [hr] at hle0
              simpa using hle0
            have hzero : (m : ℝ) * ε = 0 := le_antisymm hnonpos (mul_nonneg (by positivity) hε_pos.le)
            refine ⟨0, hK_zero, ?_⟩
            simp [hzero]
          · refine ⟨((m * ε : ℝ) / r) • k', ?_, ?_⟩
            · apply hK_star.smul_mem hk'
              · positivity
              · have hceil : (m : ℝ) * ε ≤ r := Nat.le_ceil _
                have hrpos : (0 : ℝ) < r := by positivity
                exact (div_le_one hrpos).2 hceil
            · change (r : ℝ) • (((m * ε : ℝ) / r) • k') = (m * ε : ℝ) • k'
              rw [← smul_assoc]
              congr 1
              change (r : ℝ) * ((m * ε : ℝ) * (r : ℝ)⁻¹) = (m * ε : ℝ)
              field_simp [show (r : ℝ) ≠ 0 by positivity]
        have hzcover := ih r hrlt hzscale
        rw [Set.mem_image2] at hzcover
        rcases hzcover with ⟨l₂, hl₂, z₂, hz₂, hl₂z⟩
        rcases hz₂ with ⟨k₂, hk₂, rfl⟩
        refine Set.mem_image2.2 ⟨m • l + l₂,
          L.add_mem (AddSubgroup.nsmul_mem L hl m) hl₂,
          ε₁ • k₂, Set.mem_image_of_mem (fun x => ε₁ • x) hk₂, ?_⟩
        change m • l + l₂ + ε₁ • k₂ = (m : ℝ) • k
        rw [← hlz]
        calc
          m • l + l₂ + ε₁ • k₂ = (m : ℝ) • l + (l₂ + ε₁ • k₂) := by
            norm_cast
            abel
          _ = (m : ℝ) • l + (m * ε : ℝ) • k' := by rw [hl₂z]
          _ = (m : ℝ) • (l + ε • k') := by
            simp [smul_add, smul_smul, mul_comm]

lemma exists_nat_scale_mem_of_zero_mem_interior
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (hK_nhds : (0 : E) ∈ interior K) :
    ∀ x : E, ∃ m : ℕ, x ∈ (fun y => (m : ℝ) • y) '' K := by
  intro x
  have hcont : ContinuousAt (fun c : ℝ => c • x) 0 := by
    exact continuousAt_id.smul continuousAt_const
  have hnhds : interior K ∈ 𝓝 (0 : E) := isOpen_interior.mem_nhds hK_nhds
  have hev : ∀ᶠ c : ℝ in 𝓝 0, c • x ∈ interior K := by
    have ht : Tendsto (fun c : ℝ => c • x) (𝓝 0) (𝓝 (0 : E)) := by
      simpa using hcont.tendsto
    exact ht hnhds
  rw [Metric.eventually_nhds_iff] at hev
  rcases hev with ⟨δ, hδ, hδ'⟩
  rcases exists_nat_one_div_lt hδ with ⟨m, hm⟩
  let M : ℕ := m + 1
  have hdist : dist ((1 : ℝ) / M) 0 < δ := by
    rw [Real.dist_eq, sub_zero]
    have hpos : (0 : ℝ) < 1 / M := by positivity
    rw [abs_of_pos hpos]
    simpa [M] using hm
  have hmem : ((1 : ℝ) / M) • x ∈ interior K := hδ' hdist
  refine ⟨M, ((1 : ℝ) / M) • x, interior_subset hmem, ?_⟩
  change (M : ℝ) • (((1 : ℝ) / M) • x) = x
  rw [← smul_assoc]
  change ((M : ℝ) * (1 / M)) • x = x
  have hcoeff : (M : ℝ) * (1 / M) = 1 := by
    field_simp [show (M : ℝ) ≠ 0 by positivity]
  rw [hcoeff, one_smul]

/- verified submission -/
theorem discrete_add_subgroup_covering
    (n : ℕ) (hn : 1 ≤ n)
    (K : Set (EuclideanSpace ℝ (Fin n)))
    (L : AddSubgroup (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (hK_compact : IsCompact K)
    (hK_nhds : (0 : EuclideanSpace ℝ (Fin n)) ∈ interior K)
    (hK_star : StarConvex ℝ 0 K)
    (ε₀ : ℝ) (hε₀_pos : 0 < ε₀) (hε₀_lt_one : ε₀ < 1)
    (hcover : K ⊆ Set.image2 (· + ·) (L : Set (EuclideanSpace ℝ (Fin n)))
      ((fun x => ε₀ • x) '' K)) :
    let ε₁ : ℝ := (((⌊ε₀ / (1 - ε₀)⌋ : ℤ) + 1 : ℤ) : ℝ) * ε₀
    Set.univ = Set.image2 (· + ·) (L : Set (EuclideanSpace ℝ (Fin n)))
      ((fun x => ε₁ • x) '' K) := by
  let q : ℕ := (((⌊ε₀ / (1 - ε₀)⌋ : ℤ) + 1 : ℤ).toNat)
  let ε₁ : ℝ := (((⌊ε₀ / (1 - ε₀)⌋ : ℤ) + 1 : ℤ) : ℝ) * ε₀
  change Set.univ = Set.image2 (· + ·) (L : Set (EuclideanSpace ℝ (Fin n)))
      ((fun x => ε₁ • x) '' K)
  have ha_pos : 0 < ε₀ / (1 - ε₀) := by
    exact div_pos hε₀_pos (sub_pos.mpr hε₀_lt_one)
  have hfloor_nonneg : 0 ≤ ⌊ε₀ / (1 - ε₀)⌋ := Int.floor_nonneg.mpr ha_pos.le
  have hq_nonneg_int : 0 ≤ (⌊ε₀ / (1 - ε₀)⌋ : ℤ) + 1 := by omega
  have hq_pos : 0 < q := by
    dsimp [q]
    omega
  have hq_cast_int : (q : ℤ) = (⌊ε₀ / (1 - ε₀)⌋ : ℤ) + 1 := by
    dsimp [q]
    exact Int.toNat_of_nonneg hq_nonneg_int
  have hq_cast : (q : ℝ) = (((⌊ε₀ / (1 - ε₀)⌋ : ℤ) + 1 : ℤ) : ℝ) := by
    exact_mod_cast hq_cast_int
  have hrecip : 1 / (1 - ε₀) = ε₀ / (1 - ε₀) + 1 := by
    field_simp [sub_ne_zero.mpr hε₀_lt_one.ne']
    ring
  have hq_recip : (q : ℝ) + 1 > 1 / (1 - ε₀) := by
    rw [hrecip, hq_cast]
    have hfloor := Int.lt_floor_add_one (ε₀ / (1 - ε₀))
    norm_num at hfloor ⊢
  have hε₁ : ε₁ = (q : ℝ) * ε₀ := by
    dsimp [ε₁]
    rw [hq_cast]
  have hscale :=
    cover_nat_scale_of_local_cover K L (interior_subset hK_nhds) hK_star
      ε₀ ε₁ hε₀_pos hε₀_lt_one q hq_pos hq_recip hε₁ hcover
  ext x
  constructor
  · intro _
    rcases exists_nat_scale_mem_of_zero_mem_interior K hK_nhds x with ⟨m, hm⟩
    exact hscale m hm
  · intro _
    simp

end Rollout_p1227_discrete_add_subgroup_covering

#check_dependency_graph "Rollout_p1227_discrete_add_subgroup_covering.discrete_add_subgroup_covering" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let ε₁ := ↑(⌊ε₀ / (1 - ε₀)⌋ + 1) * ε₀; Set.univ = Set.image2 (fun x1 x2 => x1 + x2) (↑L) ((fun x => ε₁ • x) '' K)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hK_nhds\",\"statement\":\"0 ∈ interior K\"},{\"name\":\"hK_star\",\"statement\":\"StarConvex ℝ 0 K\"},{\"name\":\"hε₀_pos\",\"statement\":\"0 < ε₀\"},{\"name\":\"hε₀_lt_one\",\"statement\":\"ε₀ < 1\"},{\"name\":\"hcover\",\"statement\":\"K ⊆ Set.image2 (fun x1 x2 => x1 + x2) (↑L) ((fun x => ε₀ • x) '' K)\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1227_discrete_add_subgroup_covering\",\"reconstructedProofSha256\":\"22c2cef82ec59d3c5360b949af8ffc36d89d416aa5263abebf257d242b4f3885\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1227_discrete_add_subgroup_covering.discrete_add_subgroup_covering\",\"topologySha256\":\"37dc515db3c9a5abba24bc857578d4649ea4d16bcd42ddc2a2cc4e5fe39fc62d\"}"

namespace Rollout_p1232_diagonal_homogeneous_polynomial_norm_bound

-- graph_id: p1232_diagonal_homogeneous_polynomial_norm_bound
-- topology_sha256: 910854e5c1c89e9dea383bc8c54c2f4098dc9bdd1ead6751c521e969dbe06da9
/- accepted add_to_file helper 1 -/
lemma one_le_diagonal_lp_norm {𝕂 : Type*} [RCLike 𝕂] {k : ℕ} (p : ENNReal)
    (hp : 1 < p) (α : Fin k → 𝕂) {j : Fin k} (hj : α j = 1) :
    1 ≤ (if p = ⊤ then ‖α‖ else
      Real.rpow (∑ i : Fin k, Real.rpow ‖α i‖ p.toReal) (1 / p.toReal)) := by
  by_cases hpt : p = ⊤
  · simp [hpt]
    calc
      (1:ℝ) = ‖α j‖ := by simp [hj]
      _ ≤ ‖α‖ := norm_le_pi_norm α j
  · have hpreal : 0 < p.toReal := by
      exact ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hp.le)) hpt
    simp [hpt]
    have hterm : (1:ℝ) ≤ ∑ i : Fin k, ‖α i‖ ^ p.toReal := by
      calc
        (1:ℝ) = ‖α j‖ ^ p.toReal := by simp [hj]
        _ ≤ ∑ i : Fin k, ‖α i‖ ^ p.toReal := by
          exact Finset.single_le_sum (fun i _ => Real.rpow_nonneg (norm_nonneg _) _) (Finset.mem_univ j)
    have h := Real.rpow_le_rpow zero_le_one hterm (by positivity : 0 ≤ 1 / p.toReal)
    simpa [Real.one_rpow] using h

/- accepted add_to_file helper 2 -/
noncomputable section

instance instNormSubmoduleDualCLM
    {𝕂 E : Type*} [RCLike 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
    (K : Submodule 𝕂 E) : Norm (K →L[𝕂] 𝕂) :=
  ContinuousLinearMap.hasOpNorm

lemma diagonal_functional_restriction_norm_ge
    {𝕂 E : Type*} [RCLike 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
    {k : ℕ} (φ : Fin k → E →L[𝕂] 𝕂)
    {A B : ℝ} (hA : 0 < A) (p : ENNReal) (hp : 1 < p)
    (hφ : ∀ α : Fin k → 𝕂,
      A * (if p = ⊤ then ‖α‖ else
        Real.rpow (∑ j : Fin k, Real.rpow ‖α j‖ p.toReal) (1 / p.toReal)) ≤
          ‖∑ j : Fin k, α j • φ j‖ ∧
      ‖∑ j : Fin k, α j • φ j‖ ≤
        B * (if p = ⊤ then ‖α‖ else
          Real.rpow (∑ j : Fin k, Real.rpow ‖α j‖ p.toReal) (1 / p.toReal)))
    (j : Fin k) :
    A ≤ ‖(φ j).comp
      ((⨅ i : {i // i ∈ Finset.univ \ {j}}, ((φ i.1).toLinearMap).ker).subtypeL)‖ := by
  let I := {i : Fin k // i ∈ Finset.univ \ {j}}
  let K : Submodule 𝕂 E := ⨅ i : I, ((φ i.1).toLinearMap).ker
  let f : K →L[𝕂] 𝕂 := (φ j).comp K.subtypeL
  rcases exists_extension_norm_eq K f with ⟨g, hgext, hgnorm⟩
  have hker : ⨅ i : I, ((φ i.1).toLinearMap).ker ≤ (g - φ j).toLinearMap.ker := by
    intro x hx
    rw [LinearMap.mem_ker]
    have hgx : g x = φ j x := by
      simpa [f, K] using hgext ⟨x, hx⟩
    simp [hgx]
  rcases (Submodule.mem_span_range_iff_exists_fun 𝕂).mp
      (mem_span_of_iInf_ker_le_ker hker) with ⟨c, hc⟩
  let β : Fin k → 𝕂 := fun l =>
    if h : l ∈ Finset.univ \ {j} then c ⟨l, h⟩ else 1
  have hgsum : g = ∑ l : Fin k, β l • φ l := by
    apply ContinuousLinearMap.ext
    intro x
    have hsum_split :
        (∑ l : Fin k, β l • φ l) x =
          φ j x + ∑ i : I, c i * (φ i.1) x := by
      rw [ContinuousLinearMap.sum_apply]
      simp_rw [ContinuousLinearMap.smul_apply]
      calc
        ∑ l : Fin k, β l * φ l x =
            β j * φ j x + ∑ l ∈ Finset.univ \ {j}, β l * φ l x := by
          exact Finset.sum_eq_add_sum_diff_singleton (s := Finset.univ) j
            (fun l => β l * φ l x) (fun h => False.elim (by simpa using h))
        _ = φ j x + ∑ i : I, c i * (φ i.1) x := by
          congr 1
          · simp [β]
          · rw [Finset.sum_subtype (Finset.univ \ {j}) (fun l => Iff.rfl)
              (fun l => β l * φ l x)]
            apply Finset.sum_congr rfl
            intro i hi
            have hne : i.1 ≠ j := by
              have hnotmem : i.1 ∉ ({j} : Finset (Fin k)) :=
                (Finset.mem_sdiff.mp i.2).2
              intro hij
              exact hnotmem (by simpa [hij])
            simp [β, hne]
    have hcx : (∑ i : I, c i • (φ i.1).toLinearMap) x = (g - φ j).toLinearMap x := by
      simpa using congrFun (congrArg DFunLike.coe hc) x
    simp at hcx
    rw [hsum_split]
    calc
      g x = (g x - φ j x) + φ j x := by abel
      _ = (∑ i : I, c i * (φ i.1) x) + φ j x := by rw [← hcx]
      _ = φ j x + ∑ i : I, c i * (φ i.1) x := by rw [add_comm]
  have hone : β j = 1 := by simp [β]
  have hnormβ := one_le_diagonal_lp_norm p hp β hone
  calc
    A = A * 1 := by rw [mul_one]
    _ ≤ A * (if p = ⊤ then ‖β‖ else
        Real.rpow (∑ i : Fin k, Real.rpow ‖β i‖ p.toReal) (1 / p.toReal)) := by
          exact mul_le_mul_of_nonneg_left hnormβ hA.le
    _ ≤ ‖∑ l : Fin k, β l • φ l‖ := (hφ β).1
    _ = ‖g‖ := by rw [← hgsum]
    _ = ‖f‖ := hgnorm

end

/- accepted add_to_file helper 3 -/
noncomputable section

lemma diagonal_pairing_le_of_lp_le_one
    {𝕂 E : Type*} [RCLike 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
    {k : ℕ} (φ : Fin k → E →L[𝕂] 𝕂)
    {B : ℝ} (hB : 0 < B) (p : ENNReal) (hp : 1 < p) (hpt : p ≠ ⊤)
    (hφ : ∀ α : Fin k → 𝕂,
      ‖∑ j : Fin k, α j • φ j‖ ≤
        B * Real.rpow (∑ j : Fin k, Real.rpow ‖α j‖ p.toReal) (1 / p.toReal))
    (x : E) (hx : ‖x‖ ≤ 1) (g : Fin k → NNReal)
    (hg : Real.rpow (∑ i : Fin k, ((g i : ℝ) ^ p.toReal)) (1 / p.toReal) ≤ 1) :
    ∑ i : Fin k, (g i : ℝ) * ‖φ i x‖ ≤ B := by
  let y : Fin k → 𝕂 := fun i => φ i x
  let phase : 𝕂 → 𝕂 := fun z => if z = 0 then 0 else (‖z‖ : 𝕂) / z
  let β : Fin k → 𝕂 := fun i => ((g i : ℝ) : 𝕂) * phase (y i)
  have hphase_norm : ∀ z : 𝕂, ‖phase z‖ ≤ 1 := by
    intro z
    by_cases hz : z = 0
    · simp [phase, hz]
    · simp only [phase, if_neg hz]
      rw [norm_div, RCLike.norm_ofReal]
      rw [abs_of_nonneg (norm_nonneg z)]
      rw [div_self (norm_ne_zero_iff.mpr hz)]
  have hphase_apply : ∀ z : 𝕂, phase z * z = (‖z‖ : 𝕂) := by
    intro z
    by_cases hz : z = 0
    · simp [phase, hz]
    · simp only [phase, if_neg hz]
      field_simp [hz]
  have hβnorm : ∀ i, ‖β i‖ ≤ (g i : ℝ) := by
    intro i
    have hg0 : 0 ≤ (g i : ℝ) := NNReal.coe_nonneg _
    calc
      ‖β i‖ = |(g i : ℝ)| * ‖phase (y i)‖ := by
        simp [β, norm_mul]
      _ ≤ |(g i : ℝ)| * 1 := by
        exact mul_le_mul_of_nonneg_left (hphase_norm (y i)) (abs_nonneg _)
      _ = (g i : ℝ) := by simp [abs_of_nonneg hg0]
  have hpreal : 0 < p.toReal := by
    exact ENNReal.toReal_pos (ne_of_gt (lt_of_lt_of_le zero_lt_one hp.le)) hpt
  have hβlp : Real.rpow (∑ i : Fin k, ‖β i‖ ^ p.toReal) (1 / p.toReal) ≤ 1 := by
    have hsum : (∑ i : Fin k, ‖β i‖ ^ p.toReal) ≤
        ∑ i : Fin k, ((g i : ℝ) ^ p.toReal) := by
      apply Finset.sum_le_sum
      intro i hi
      exact Real.rpow_le_rpow (norm_nonneg _) (hβnorm i) hpreal.le
    calc
      Real.rpow (∑ i : Fin k, ‖β i‖ ^ p.toReal) (1 / p.toReal)
          ≤ Real.rpow (∑ i : Fin k, ((g i : ℝ) ^ p.toReal)) (1 / p.toReal) := by
            exact Real.rpow_le_rpow (by positivity) hsum (by positivity)
      _ ≤ 1 := hg
  let F : E →L[𝕂] 𝕂 := ∑ i : Fin k, β i • φ i
  have hF : ‖F‖ ≤ B := by
    calc
      ‖F‖ ≤ B * Real.rpow (∑ i : Fin k, ‖β i‖ ^ p.toReal) (1 / p.toReal) := hφ β
      _ ≤ B * 1 := mul_le_mul_of_nonneg_left hβlp hB.le
      _ = B := by ring
  have hFx : ‖F x‖ ≤ B := by
    calc
      ‖F x‖ ≤ ‖F‖ * ‖x‖ := ContinuousLinearMap.le_opNorm F x
      _ ≤ ‖F‖ * 1 := mul_le_mul_of_nonneg_left hx (norm_nonneg F)
      _ = ‖F‖ := by ring
      _ ≤ B := hF
  have hvalue : F x = ((∑ i : Fin k, (g i : ℝ) * ‖y i‖ : ℝ) : 𝕂) := by
    calc
      F x = ∑ i : Fin k, β i * y i := by
        simp [F, y, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
      _ = ∑ i : Fin k, (((g i : ℝ) * ‖y i‖ : ℝ) : 𝕂) := by
        apply Finset.sum_congr rfl
        intro i hi
        calc
          β i * y i = ((g i : ℝ) : 𝕂) * (phase (y i) * y i) := by
            simp [β, mul_assoc]
          _ = ((g i : ℝ) : 𝕂) * (‖y i‖ : 𝕂) := by rw [hphase_apply]
          _ = (((g i : ℝ) * ‖y i‖ : ℝ) : 𝕂) := by norm_num [RCLike.ofReal_mul]
      _ = ((∑ i : Fin k, (g i : ℝ) * ‖y i‖ : ℝ) : 𝕂) := by
        norm_num [map_sum]
  have hsum_nonneg : 0 ≤ ∑ i : Fin k, (g i : ℝ) * ‖y i‖ := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _)
  have hnormcast : ‖(((∑ i : Fin k, (g i : ℝ) * ‖y i‖) : ℝ) : 𝕂)‖ =
      ∑ i : Fin k, (g i : ℝ) * ‖y i‖ := by
    rw [RCLike.norm_ofReal, abs_of_nonneg hsum_nonneg]
  calc
    ∑ i : Fin k, (g i : ℝ) * ‖φ i x‖ = ∑ i : Fin k, (g i : ℝ) * ‖y i‖ := by
      simp [y]
    _ = ‖(((∑ i : Fin k, (g i : ℝ) * ‖y i‖) : ℝ) : 𝕂)‖ := hnormcast.symm
    _ = ‖F x‖ := by rw [← hvalue]
    _ ≤ B := hFx

end

/- accepted add_to_file helper 4 -/
noncomputable section

lemma diagonal_coordinate_lq_norm_le
    {𝕂 E : Type*} [RCLike 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
    {k : ℕ} (φ : Fin k → E →L[𝕂] 𝕂)
    {B : ℝ} (hB : 0 < B) (p : ENNReal) (hp : 1 < p) (hpt : p ≠ ⊤)
    (hφ : ∀ α : Fin k → 𝕂,
      ‖∑ j : Fin k, α j • φ j‖ ≤
        B * Real.rpow (∑ j : Fin k, Real.rpow ‖α j‖ p.toReal) (1 / p.toReal))
    (x : E) (hx : ‖x‖ ≤ 1) :
    Real.rpow (∑ i : Fin k, ‖φ i x‖ ^ (ENNReal.conjExponent p).toReal)
        (1 / (ENNReal.conjExponent p).toReal) ≤ B := by
  let q : ENNReal := ENNReal.conjExponent p
  haveI hpq : p.HolderConjugate q := ENNReal.HolderConjugate.conjExponent hp.le
  have hpreal : 1 < p.toReal := by
    have h := (ENNReal.toReal_lt_toReal (by norm_num : (1 : ENNReal) ≠ ⊤) hpt).2 hp
    simpa using h
  have hqp_real : q.toReal.HolderConjugate p.toReal :=
    (ENNReal.HolderConjugate.toReal hpreal).symm
  let f : Fin k → NNReal := fun i => ⟨‖φ i x‖, norm_nonneg _⟩
  let qnorm : NNReal := (∑ i : Fin k, f i ^ q.toReal) ^ (1 / q.toReal)
  have hgreat := NNReal.isGreatest_Lp Finset.univ f hqp_real
  rcases hgreat.1 with ⟨g, hgset, hgpair⟩
  have hgreal : (∑ i : Fin k, ((g i : ℝ) ^ p.toReal)) ≤ 1 := by
    exact_mod_cast hgset
  have hp_pos : 0 < p.toReal := by positivity
  have hgroot : (∑ i : Fin k, ((g i : ℝ) ^ p.toReal)) ^ (1 / p.toReal) ≤ 1 := by
    calc
      (∑ i : Fin k, ((g i : ℝ) ^ p.toReal)) ^ (1 / p.toReal)
          ≤ (1 : ℝ) ^ (1 / p.toReal) := by
            exact Real.rpow_le_rpow (by positivity) hgreal (by positivity)
      _ = 1 := by simp
  have hpair : ∑ i : Fin k, (g i : ℝ) * ‖φ i x‖ ≤ B :=
    diagonal_pairing_le_of_lp_le_one φ hB p hp hpt hφ x hx g hgroot
  have hpair' : ((∑ i : Fin k, f i * g i : NNReal) : ℝ) =
      ∑ i : Fin k, (g i : ℝ) * ‖φ i x‖ := by
    simp [f, mul_comm]
  have hqnorm_eq : (qnorm : ℝ) =
      Real.rpow (∑ i : Fin k, ‖φ i x‖ ^ q.toReal) (1 / q.toReal) := by
    simp [qnorm, f]
  calc
    Real.rpow (∑ i : Fin k, ‖φ i x‖ ^ (ENNReal.conjExponent p).toReal)
        (1 / (ENNReal.conjExponent p).toReal)
        = (qnorm : ℝ) := by simp [q, hqnorm_eq]
    _ = (∑ i : Fin k, (g i : ℝ) * ‖φ i x‖) := by
      calc
        (qnorm : ℝ) = ((∑ i : Fin k, f i * g i : NNReal) : ℝ) := by
          exact congrArg (fun r : NNReal => (r : ℝ)) hgpair.symm
        _ = ∑ i : Fin k, (g i : ℝ) * ‖φ i x‖ := hpair'
    _ ≤ B := hpair

end

/- accepted add_to_file helper 5 -/
lemma sum_nat_pow_le_of_lq_norm_le
    {k : ℕ} (hk : 1 ≤ k) {q B : ℝ} (hq : 0 < q) (hB : 0 < B)
    {n : ℕ} (hqn : q ≤ n) (f : Fin k → ℝ) (hf : ∀ i, 0 ≤ f i)
    (hC : (∑ i : Fin k, f i ^ q) ^ (1 / q) ≤ B) :
    ∑ i : Fin k, f i ^ n ≤ B ^ n := by
  haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  rcases Finset.exists_max_image Finset.univ f Finset.univ_nonempty with ⟨j, hjmem, hjmax⟩
  let M : ℝ := f j
  have hM0 : 0 ≤ M := hf j
  have hsum_nonneg : 0 ≤ ∑ i : Fin k, f i ^ q := by
    exact Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hf i) _)
  have hMq_sum : M ^ q ≤ ∑ i : Fin k, f i ^ q := by
    calc
      M ^ q = f j ^ q := rfl
      _ ≤ ∑ i : Fin k, f i ^ q := by
        exact Finset.single_le_sum (fun i _ => Real.rpow_nonneg (hf i) _) hjmem
  have hM : M ≤ B := by
    calc
      M = (M ^ q) ^ (1 / q) := by
        symm
        simpa [one_div] using Real.rpow_rpow_inv hM0 hq.ne'
      _ ≤ (∑ i : Fin k, f i ^ q) ^ (1 / q) := by
        exact Real.rpow_le_rpow (Real.rpow_nonneg hM0 _) hMq_sum (by positivity)
      _ ≤ B := hC
  have hCq : ((∑ i : Fin k, f i ^ q) ^ (1 / q)) ^ q = ∑ i : Fin k, f i ^ q := by
    simpa [one_div] using Real.rpow_inv_rpow hsum_nonneg hq.ne'
  have hterm : ∀ i : Fin k, f i ^ n ≤ M ^ ((n : ℝ) - q) * f i ^ q := by
    intro i
    by_cases hi : f i = 0
    · have hnpos : 0 < n := by
        by_contra hnot
        have hn0 : n = 0 := by omega
        rw [hn0] at hqn
        norm_num at hqn
        linarith
      simp [hi, hnpos.ne', hq.ne']
    · have hi0 : 0 < f i := lt_of_le_of_ne (hf i) (Ne.symm hi)
      have hsplit : f i ^ (n : ℝ) = f i ^ ((n : ℝ) - q) * f i ^ q := by
        rw [← Real.rpow_add hi0]
        congr 1
        ring
      have hpow : f i ^ ((n : ℝ) - q) ≤ M ^ ((n : ℝ) - q) := by
        exact Real.rpow_le_rpow (hf i) (hjmax i (Finset.mem_univ i)) (by linarith)
      calc
        f i ^ n = f i ^ (n : ℝ) := by rw [Real.rpow_natCast]
        _ = f i ^ ((n : ℝ) - q) * f i ^ q := hsplit
        _ ≤ M ^ ((n : ℝ) - q) * f i ^ q := by
          exact mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg (hf i) _)
  have hC_nonneg : 0 ≤ (∑ i : Fin k, f i ^ q) ^ (1 / q) := Real.rpow_nonneg hsum_nonneg _
  calc
    ∑ i : Fin k, f i ^ n ≤ ∑ i : Fin k, M ^ ((n : ℝ) - q) * f i ^ q := by
      exact Finset.sum_le_sum (fun i _ => hterm i)
    _ = M ^ ((n : ℝ) - q) * ∑ i : Fin k, f i ^ q := by
      rw [Finset.mul_sum]
    _ = M ^ ((n : ℝ) - q) * (((∑ i : Fin k, f i ^ q) ^ (1 / q)) ^ q) := by
      rw [hCq]
    _ ≤ B ^ ((n : ℝ) - q) * B ^ q := by
      have h1 : M ^ ((n : ℝ) - q) ≤ B ^ ((n : ℝ) - q) := by
        exact Real.rpow_le_rpow hM0 hM (by linarith)
      have h2 : ((∑ i : Fin k, f i ^ q) ^ (1 / q)) ^ q ≤ B ^ q := by
        exact Real.rpow_le_rpow hC_nonneg hC hq.le
      exact mul_le_mul h1 h2 (Real.rpow_nonneg hC_nonneg _)
        (Real.rpow_nonneg hB.le _)
    _ = B ^ (n : ℝ) := by
      rw [← Real.rpow_add_of_nonneg hB.le (by linarith : 0 ≤ (n : ℝ) - q) hq.le]
      congr 1
      ring
    _ = B ^ n := by rw [Real.rpow_natCast]

/- accepted add_to_file helper 6 -/
noncomputable section

lemma diagonal_sum_norms_le_top
    {𝕂 E : Type*} [RCLike 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
    {k : ℕ} (φ : Fin k → E →L[𝕂] 𝕂)
    {B : ℝ} (hB : 0 < B) (p : ENNReal) (hpt : p = ⊤)
    (hφ : ∀ α : Fin k → 𝕂,
      ‖∑ j : Fin k, α j • φ j‖ ≤ B * ‖α‖)
    (x : E) (hx : ‖x‖ ≤ 1) :
    ∑ i : Fin k, ‖φ i x‖ ≤ B := by
  let y : Fin k → 𝕂 := fun i => φ i x
  let phase : 𝕂 → 𝕂 := fun z => if z = 0 then 0 else (‖z‖ : 𝕂) / z
  let β : Fin k → 𝕂 := fun i => phase (y i)
  have hphase_norm : ∀ z : 𝕂, ‖phase z‖ ≤ 1 := by
    intro z
    by_cases hz : z = 0
    · simp [phase, hz]
    · simp only [phase, if_neg hz]
      rw [norm_div, RCLike.norm_ofReal]
      rw [abs_of_nonneg (norm_nonneg z)]
      rw [div_self (norm_ne_zero_iff.mpr hz)]
  have hphase_apply : ∀ z : 𝕂, phase z * z = (‖z‖ : 𝕂) := by
    intro z
    by_cases hz : z = 0
    · simp [phase, hz]
    · simp only [phase, if_neg hz]
      field_simp [hz]
  have hβnorm : ‖β‖ ≤ 1 := by
    rw [Pi.norm_def]
    norm_cast
    rw [Finset.sup_le_iff]
    intro i hi
    exact_mod_cast hphase_norm (y i)
  let F : E →L[𝕂] 𝕂 := ∑ i : Fin k, β i • φ i
  have hF : ‖F‖ ≤ B := by
    calc
      ‖F‖ ≤ B * ‖β‖ := hφ β
      _ ≤ B * 1 := mul_le_mul_of_nonneg_left hβnorm hB.le
      _ = B := by ring
  have hFx : ‖F x‖ ≤ B := by
    calc
      ‖F x‖ ≤ ‖F‖ * ‖x‖ := ContinuousLinearMap.le_opNorm F x
      _ ≤ ‖F‖ * 1 := mul_le_mul_of_nonneg_left hx (norm_nonneg F)
      _ = ‖F‖ := by ring
      _ ≤ B := hF
  have hvalue : F x = ((∑ i : Fin k, ‖y i‖ : ℝ) : 𝕂) := by
    calc
      F x = ∑ i : Fin k, β i * y i := by
        simp [F, y, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
      _ = ∑ i : Fin k, ((‖y i‖ : ℝ) : 𝕂) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [β, hphase_apply]
      _ = ((∑ i : Fin k, ‖y i‖ : ℝ) : 𝕂) := by norm_num [map_sum]
  have hsum_nonneg : 0 ≤ ∑ i : Fin k, ‖y i‖ := by
    exact Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hnormcast : ‖(((∑ i : Fin k, ‖y i‖) : ℝ) : 𝕂)‖ = ∑ i : Fin k, ‖y i‖ := by
    rw [RCLike.norm_ofReal, abs_of_nonneg hsum_nonneg]
  calc
    ∑ i : Fin k, ‖φ i x‖ = ∑ i : Fin k, ‖y i‖ := by simp [y]
    _ = ‖(((∑ i : Fin k, ‖y i‖) : ℝ) : 𝕂)‖ := hnormcast.symm
    _ = ‖F x‖ := by rw [← hvalue]
    _ ≤ B := hFx

end

/- accepted add_to_file helper 7 -/
noncomputable section

lemma diagonal_polynomial_pointwise_upper
    {𝕂 E : Type*} [RCLike 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
    {k : ℕ} (hk : 1 ≤ k) (φ : Fin k → E →L[𝕂] 𝕂)
    {A B : ℝ} (hB : 0 < B) (p : ENNReal) (hp : 1 < p)
    (hφ : ∀ α : Fin k → 𝕂,
      A * (if p = ⊤ then ‖α‖ else
        Real.rpow (∑ j : Fin k, Real.rpow ‖α j‖ p.toReal) (1 / p.toReal)) ≤
          ‖∑ j : Fin k, α j • φ j‖ ∧
      ‖∑ j : Fin k, α j • φ j‖ ≤
        B * (if p = ⊤ then ‖α‖ else
          Real.rpow (∑ j : Fin k, Real.rpow ‖α j‖ p.toReal) (1 / p.toReal)))
    (n : ℕ) (hn : 1 ≤ n) (hnq : ENNReal.conjExponent p ≤ n)
    (α : Fin k → 𝕂) (x : E) (hx : ‖x‖ ≤ 1) :
    ‖∑ j : Fin k, α j * (φ j x) ^ n‖ ≤ B ^ n * ‖α‖ := by
  have hsumy : ∑ i : Fin k, ‖φ i x‖ ^ n ≤ B ^ n := by
    by_cases hpt : p = ⊤
    · have hupper : ∀ β : Fin k → 𝕂, ‖∑ j : Fin k, β j • φ j‖ ≤ B * ‖β‖ := by
        intro β
        simpa [hpt] using (hφ β).2
      have hs := diagonal_sum_norms_le_top φ hB p hpt hupper x hx
      have hC : (∑ i : Fin k, ‖φ i x‖ ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) ≤ B := by
        simpa using hs
      have hq1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      simpa using sum_nat_pow_le_of_lq_norm_le hk zero_lt_one hB hq1
        (fun i => ‖φ i x‖) (fun i => norm_nonneg _) hC
    · have hupper : ∀ β : Fin k → 𝕂,
          ‖∑ j : Fin k, β j • φ j‖ ≤
            B * Real.rpow (∑ j : Fin k, Real.rpow ‖β j‖ p.toReal) (1 / p.toReal) := by
        intro β
        simpa [hpt] using (hφ β).2
      have hC := diagonal_coordinate_lq_norm_le φ hB p hp hpt hupper x hx
      let q : ENNReal := ENNReal.conjExponent p
      haveI hpq : p.HolderConjugate q := ENNReal.HolderConjugate.conjExponent hp.le
      haveI hqp : q.HolderConjugate p := ENNReal.HolderConjugate.symm
      have hqposEN : 0 < q := ENNReal.HolderConjugate.pos q p
      have hqtop : q ≠ ⊤ := by
        intro hqt
        have hpone : p = 1 :=
          (ENNReal.HolderConjugate.eq_top_iff_eq_one q p).1 hqt
        exact ne_of_gt hp hpone
      have hqpos : 0 < q.toReal := ENNReal.toReal_pos hqposEN.ne' hqtop
      have hqn : q.toReal ≤ (n : ℝ) := by
        have h := (ENNReal.toReal_le_toReal hqtop (by simp : ((n : ENNReal) ≠ ⊤))).2 hnq
        simpa using h
      have hC' : (∑ i : Fin k, ‖φ i x‖ ^ q.toReal) ^ (1 / q.toReal) ≤ B := by
        simpa [q] using hC
      simpa [q] using sum_nat_pow_le_of_lq_norm_le hk hqpos hB hqn
        (fun i => ‖φ i x‖) (fun i => norm_nonneg _) hC'
  calc
    ‖∑ j : Fin k, α j * (φ j x) ^ n‖
        ≤ ∑ j : Fin k, ‖α j * (φ j x) ^ n‖ := norm_sum_le _ _
    _ = ∑ j : Fin k, ‖α j‖ * ‖φ j x‖ ^ n := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [norm_mul, norm_pow]
    _ ≤ ∑ j : Fin k, ‖α‖ * ‖φ j x‖ ^ n := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (norm_le_pi_norm α j)
        (pow_nonneg (norm_nonneg _) _)
    _ = ‖α‖ * ∑ j : Fin k, ‖φ j x‖ ^ n := by rw [Finset.mul_sum]
    _ ≤ ‖α‖ * B ^ n := by
      exact mul_le_mul_of_nonneg_left hsumy (norm_nonneg α)
    _ = B ^ n * ‖α‖ := by rw [mul_comm]

end

/- accepted add_to_file helper 8 -/
noncomputable section

lemma diagonal_polynomial_coordinate_lower
    {𝕂 E : Type*} [RCLike 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
    {k : ℕ} (φ : Fin k → E →L[𝕂] 𝕂)
    {A B : ℝ} (hA : 0 < A) (p : ENNReal) (hp : 1 < p)
    (hφ : ∀ α : Fin k → 𝕂,
      A * (if p = ⊤ then ‖α‖ else
        Real.rpow (∑ j : Fin k, Real.rpow ‖α j‖ p.toReal) (1 / p.toReal)) ≤
          ‖∑ j : Fin k, α j • φ j‖ ∧
      ‖∑ j : Fin k, α j • φ j‖ ≤
        B * (if p = ⊤ then ‖α‖ else
          Real.rpow (∑ j : Fin k, Real.rpow ‖α j‖ p.toReal) (1 / p.toReal)))
    (n : ℕ) (hn : 1 ≤ n) (α : Fin k → 𝕂) (j : Fin k)
    (hBdd : BddAbove (Set.range (fun x : {x : E // ‖x‖ ≤ 1} =>
      ‖∑ l : Fin k, α l * (φ l x) ^ n‖))) :
    A ^ n * ‖α j‖ ≤ sSup (Set.range (fun x : {x : E // ‖x‖ ≤ 1} =>
      ‖∑ l : Fin k, α l * (φ l x) ^ n‖)) := by
  let I := {i : Fin k // i ∈ Finset.univ \ {j}}
  let K : Submodule 𝕂 E := ⨅ i : I, ((φ i.1).toLinearMap).ker
  let f : K →L[𝕂] 𝕂 := (φ j).comp K.subtypeL
  let S : Set ℝ := Set.range (fun x : {x : E // ‖x‖ ≤ 1} =>
    ‖∑ l : Fin k, α l * (φ l x) ^ n‖)
  have hrest : A ≤ ‖f‖ := by
    simpa [f, K, I] using diagonal_functional_restriction_norm_ge φ hA p hp hφ j
  change A ^ n * ‖α j‖ ≤ sSup S
  have hnp : 0 < n := by omega
  by_cases hα : ‖α j‖ = 0
  · have hzero_mem : (0 : ℝ) ∈ S := by
      refine ⟨⟨0, by simp⟩, ?_⟩
      simp [hnp.ne']
    have hzero_le : (0 : ℝ) ≤ sSup S := le_csSup hBdd hzero_mem
    simpa [hα] using hzero_le
  · apply le_of_forall_lt
    intro c hc
    have hαpos : 0 < ‖α j‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hα)
    let C : ℝ := c / ‖α j‖
    have hC : C < A ^ n := by
      exact (div_lt_iff₀ hαpos).2 hc
    have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hnp.ne'
    by_cases hCpos : 0 < C
    · let s : ℝ := C ^ (1 / (n : ℝ))
      have hsA : s < A := by
        calc
          s < (A ^ (n : ℝ)) ^ (1 / (n : ℝ)) := by
            apply Real.rpow_lt_rpow hCpos.le
            · simpa [Real.rpow_natCast] using hC
            · positivity
          _ = A := by
            simpa [one_div] using Real.rpow_rpow_inv hA.le hnreal
      rcases exists_between hsA with ⟨r, hsr, hrA⟩
      have hr : r < ‖f‖ := lt_of_lt_of_le hrA hrest
      rcases ContinuousLinearMap.exists_lt_apply_of_lt_opNorm f hr with ⟨z, hznorm, hzval⟩
      have hzero : ∀ i : Fin k, i ≠ j → φ i z.1 = 0 := by
        intro i hij
        have hmem : z.1 ∈ K := z.2
        have hker : z.1 ∈ ((φ i).toLinearMap).ker := by
          exact ((Submodule.mem_iInf _).1 hmem) ⟨i, by simp [hij]⟩
        simpa [LinearMap.mem_ker] using hker
      have hsum : (∑ l : Fin k, α l * (φ l z.1) ^ n) = α j * (φ j z.1) ^ n := by
        apply Finset.sum_eq_single j
        · intro i hi hij
          simp [hzero i hij, hnp.ne']
        · intro hj
          simp at hj
      let v : ℝ := ‖α j‖ * ‖f z‖ ^ n
      have hv_eq : v = ‖∑ l : Fin k, α l * (φ l z.1) ^ n‖ := by
        rw [hsum]
        simp [v, f, norm_mul, norm_pow]
      have hvmem : v ∈ S := by
        refine ⟨⟨z.1, hznorm.le⟩, ?_⟩
        simpa [S] using hv_eq.symm
      have hs_nonneg : 0 ≤ s := Real.rpow_nonneg hCpos.le _
      have hr_nonneg : 0 ≤ r := le_trans hs_nonneg hsr.le
      have hCs : C = s ^ n := by
        calc
          C = s ^ (n : ℝ) := by
            symm
            simpa [s, one_div] using Real.rpow_inv_rpow hCpos.le hnreal
          _ = s ^ n := by rw [Real.rpow_natCast]
      have hCr : C < r ^ n := by
        rw [hCs]
        exact pow_lt_pow_left₀ hsr hs_nonneg hnp.ne'
      have hrv : r ^ n < ‖f z‖ ^ n := by
        exact pow_lt_pow_left₀ hzval hr_nonneg hnp.ne'
      have hCv : C < ‖f z‖ ^ n := lt_trans hCr hrv
      have hcv : c < v := by
        have h := mul_lt_mul_of_pos_left hCv hαpos
        have hmul : ‖α j‖ * C = c := by
          simpa [C] using mul_div_cancel₀ c hα
        rwa [hmul] at h
      exact lt_of_lt_of_le hcv (le_csSup hBdd hvmem)
    · have hCnonpos : C ≤ 0 := le_of_not_gt hCpos
      have hfpos : 0 < ‖f‖ := lt_of_lt_of_le hA hrest
      rcases ContinuousLinearMap.exists_lt_apply_of_lt_opNorm f hfpos with ⟨z, hznorm, hzval⟩
      have hzero : ∀ i : Fin k, i ≠ j → φ i z.1 = 0 := by
        intro i hij
        have hmem : z.1 ∈ K := z.2
        have hker : z.1 ∈ ((φ i).toLinearMap).ker := by
          exact ((Submodule.mem_iInf _).1 hmem) ⟨i, by simp [hij]⟩
        simpa [LinearMap.mem_ker] using hker
      have hsum : (∑ l : Fin k, α l * (φ l z.1) ^ n) = α j * (φ j z.1) ^ n := by
        apply Finset.sum_eq_single j
        · intro i hi hij
          simp [hzero i hij, hnp.ne']
        · intro hj
          simp at hj
      let v : ℝ := ‖α j‖ * ‖f z‖ ^ n
      have hv_eq : v = ‖∑ l : Fin k, α l * (φ l z.1) ^ n‖ := by
        rw [hsum]
        simp [v, f, norm_mul, norm_pow]
      have hvmem : v ∈ S := by
        refine ⟨⟨z.1, hznorm.le⟩, ?_⟩
        simpa [S] using hv_eq.symm
      have hvpos : 0 < v := by
        exact mul_pos hαpos (pow_pos hzval _)
      have hc0 : c ≤ 0 := by
        have h := (div_le_iff₀ hαpos).1 hCnonpos
        simpa using h
      have hcv : c < v := lt_of_le_of_lt hc0 hvpos
      exact lt_of_lt_of_le hcv (le_csSup hBdd hvmem)

end

/- accepted add_to_file helper 9 -/
lemma exists_norm_eq_pi_norm {G : Type*} [SeminormedAddCommGroup G]
    {k : ℕ} (hk : 1 ≤ k) (α : Fin k → G) : ∃ j : Fin k, ‖α‖ = ‖α j‖ := by
  haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  rcases Finset.exists_max_image Finset.univ (fun j => ‖α j‖) Finset.univ_nonempty with
    ⟨j, hjmem, hjmax⟩
  refine ⟨j, ?_⟩
  have hsup : Finset.univ.sup (fun i => ‖α i‖₊) = ‖α j‖₊ := by
    apply le_antisymm
    · rw [Finset.sup_le_iff]
      intro i hi
      exact_mod_cast hjmax i hi
    · exact Finset.le_sup (s := Finset.univ) (f := fun i => ‖α i‖₊) hjmem
  rw [Pi.norm_def, hsup, coe_nnnorm]

/- verified submission -/
theorem diagonal_homogeneous_polynomial_norm_bounds
    {𝕂 E : Type*} [RCLike 𝕂] [NormedAddCommGroup E] [NormedSpace 𝕂 E]
    [CompleteSpace E] {k : ℕ} (hk : 1 ≤ k) (φ : Fin k → E →L[𝕂] 𝕂)
    {A B : ℝ} (hA : 0 < A) (hB : 0 < B) (p : ENNReal) (hp : 1 < p)
    (hφ : ∀ α : Fin k → 𝕂,
      A * (if p = ⊤ then ‖α‖ else
        Real.rpow (∑ j : Fin k, Real.rpow ‖α j‖ p.toReal) (1 / p.toReal)) ≤
          ‖∑ j : Fin k, α j • φ j‖ ∧
      ‖∑ j : Fin k, α j • φ j‖ ≤
        B * (if p = ⊤ then ‖α‖ else
          Real.rpow (∑ j : Fin k, Real.rpow ‖α j‖ p.toReal) (1 / p.toReal)))
    (n : ℕ) (hn : 1 ≤ n) (hnq : ENNReal.conjExponent p ≤ n) :
    ∀ α : Fin k → 𝕂,
      A ^ n * ‖α‖ ≤
          sSup (Set.range (fun x : {x : E // ‖x‖ ≤ 1} =>
            ‖∑ j : Fin k, α j * (φ j x) ^ n‖)) ∧
      sSup (Set.range (fun x : {x : E // ‖x‖ ≤ 1} =>
            ‖∑ j : Fin k, α j * (φ j x) ^ n‖)) ≤
        B ^ n * ‖α‖ := by
  intro α
  let S : Set ℝ := Set.range (fun x : {x : E // ‖x‖ ≤ 1} =>
    ‖∑ j : Fin k, α j * (φ j x) ^ n‖)
  have hpoint : ∀ y ∈ S, y ≤ B ^ n * ‖α‖ := by
    rintro y ⟨x, rfl⟩
    exact diagonal_polynomial_pointwise_upper hk φ hB p hp hφ n hn hnq α x x.2
  have hBdd : BddAbove S := ⟨B ^ n * ‖α‖, hpoint⟩
  have hnonempty : S.Nonempty := by
    refine ⟨0, ⟨⟨0, by simp⟩, ?_⟩⟩
    simp [show n ≠ 0 by omega]
  have hupper : sSup S ≤ B ^ n * ‖α‖ := (csSup_le_iff hBdd hnonempty).2 hpoint
  rcases exists_norm_eq_pi_norm hk α with ⟨j, hj⟩
  have hcoord : A ^ n * ‖α j‖ ≤ sSup S := by
    exact diagonal_polynomial_coordinate_lower φ hA p hp hφ n hn α j hBdd
  constructor
  · calc
      A ^ n * ‖α‖ = A ^ n * ‖α j‖ := by rw [hj]
      _ ≤ sSup S := hcoord
  · exact hupper

end Rollout_p1232_diagonal_homogeneous_polynomial_norm_bound

#check_dependency_graph "Rollout_p1232_diagonal_homogeneous_polynomial_norm_bound.diagonal_homogeneous_polynomial_norm_bounds" against "{\"edges\":[{\"conclusion\":{\"name\":\"hpoint\",\"statement\":\"∀ y ∈ S, y ≤ B ^ n * ‖α‖\"},\"graphEdgeId\":\"h_001_hpoint\",\"premises\":[{\"name\":\"hk\",\"statement\":\"1 ≤ k\"},{\"name\":\"hB\",\"statement\":\"0 < B\"},{\"name\":\"hp\",\"statement\":\"1 < p\"},{\"name\":\"hφ\",\"statement\":\"∀ (α : Fin k → 𝕂), (A * if p = ⊤ then ‖α‖ else (∑ j, ‖α j‖.rpow p.toReal).rpow (1 / p.toReal)) ≤ ‖∑ j, α j • φ j‖ ∧ ‖∑ j, α j • φ j‖ ≤ B * if p = ⊤ then ‖α‖ else (∑ j, ‖α j‖.rpow p.toReal).rpow (1 / p.toReal)\"},{\"name\":\"hn\",\"statement\":\"1 ≤ n\"},{\"name\":\"hnq\",\"statement\":\"p.conjExponent ≤ ↑n\"}],\"rawEdgeId\":\"telescope_21\"},{\"conclusion\":{\"name\":\"hnonempty\",\"statement\":\"S.Nonempty\"},\"graphEdgeId\":\"h_003_hnonempty\",\"premises\":[{\"name\":\"hn\",\"statement\":\"1 ≤ n\"}],\"rawEdgeId\":\"telescope_23\"},{\"conclusion\":{\"name\":\"hBdd\",\"statement\":\"BddAbove S\"},\"graphEdgeId\":\"h_002_hbdd\",\"premises\":[{\"name\":\"hpoint\",\"statement\":\"∀ y ∈ S, y ≤ B ^ n * ‖α‖\"}],\"rawEdgeId\":\"telescope_22\"},{\"conclusion\":{\"name\":\"hupper\",\"statement\":\"sSup S ≤ B ^ n * ‖α‖\"},\"graphEdgeId\":\"h_004_hupper\",\"premises\":[{\"name\":\"hpoint\",\"statement\":\"∀ y ∈ S, y ≤ B ^ n * ‖α‖\"},{\"name\":\"hBdd\",\"statement\":\"BddAbove S\"},{\"name\":\"hnonempty\",\"statement\":\"S.Nonempty\"}],\"rawEdgeId\":\"telescope_24\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"A ^ n * ‖α‖ ≤ sSup (Set.range fun x => ‖∑ j, α j * (φ j) ↑x ^ n‖) ∧ sSup (Set.range fun x => ‖∑ j, α j * (φ j) ↑x ^ n‖) ≤ B ^ n * ‖α‖\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hk\",\"statement\":\"1 ≤ k\"},{\"name\":\"hA\",\"statement\":\"0 < A\"},{\"name\":\"hp\",\"statement\":\"1 < p\"},{\"name\":\"hφ\",\"statement\":\"∀ (α : Fin k → 𝕂), (A * if p = ⊤ then ‖α‖ else (∑ j, ‖α j‖.rpow p.toReal).rpow (1 / p.toReal)) ≤ ‖∑ j, α j • φ j‖ ∧ ‖∑ j, α j • φ j‖ ≤ B * if p = ⊤ then ‖α‖ else (∑ j, ‖α j‖.rpow p.toReal).rpow (1 / p.toReal)\"},{\"name\":\"hn\",\"statement\":\"1 ≤ n\"},{\"name\":\"hBdd\",\"statement\":\"BddAbove S\"},{\"name\":\"hupper\",\"statement\":\"sSup S ≤ B ^ n * ‖α‖\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1232_diagonal_homogeneous_polynomial_norm_bound\",\"reconstructedProofSha256\":\"b8f10276bbe374ea501413c930e4b9cfd65a9b32b3a6e31d71acb2f2acb8700c\",\"selectedEdgeCount\":5,\"theoremName\":\"Rollout_p1232_diagonal_homogeneous_polynomial_norm_bound.diagonal_homogeneous_polynomial_norm_bounds\",\"topologySha256\":\"910854e5c1c89e9dea383bc8c54c2f4098dc9bdd1ead6751c521e969dbe06da9\"}"

namespace Rollout_p1268_flower_graph_equitable_coloring_moments

-- graph_id: p1268_flower_graph_equitable_coloring_moments
-- topology_sha256: 62fc5d51e2f8984904db07fbb0ba470440156ede0fd07187201aad0c3ef5f3f5
/- accepted add_to_file helper 1 -/

abbrev FlowerVertex (n : ℕ) := Unit ⊕ (Fin n ⊕ Fin n)

def flowerRel (n : ℕ) : FlowerVertex n → FlowerVertex n → Prop := fun a b =>
  (∃ i : Fin n, a = Sum.inl () ∧ b = Sum.inr (Sum.inl i)) ∨
  (∃ i : Fin n,
    a = Sum.inr (Sum.inl i) ∧
      b = Sum.inr (Sum.inl ((finRotate n) i))) ∨
  (∃ i : Fin n, a = Sum.inr (Sum.inl i) ∧ b = Sum.inr (Sum.inr i)) ∨
  (∃ i : Fin n, a = Sum.inl () ∧ b = Sum.inr (Sum.inr i))

def flowerGraph (n : ℕ) : SimpleGraph (FlowerVertex n) :=
  SimpleGraph.fromRel (flowerRel n)

def flowerPairColor (n : ℕ) : FlowerVertex n → Fin (n + 1)
  | Sum.inl _ => Fin.last n
  | Sum.inr (Sum.inl i) => i.castSucc
  | Sum.inr (Sum.inr i) => ((finRotate n) i).castSucc

lemma finRotate_ne_self_of_two_le {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    (finRotate n) i ≠ i := by
  cases n with
  | zero => exact i.elim0
  | succ m =>
      intro h
      have hv := congrArg Fin.val h
      rw [coe_finRotate] at hv
      by_cases hi : i = Fin.last m
      · simp [hi] at hv
        omega
      · simp [hi] at hv

lemma flowerPairColor_rel_ne {n : ℕ} (hn : 2 ≤ n) {a b : FlowerVertex n}
    (h : flowerRel n a b) : flowerPairColor n a ≠ flowerPairColor n b := by
  rcases h with ⟨i, ha, hb⟩ | ⟨i, ha, hb⟩ | ⟨i, ha, hb⟩ | ⟨i, ha, hb⟩
  · subst a
    subst b
    exact (Fin.castSucc_ne_last i).symm
  · subst a
    subst b
    exact fun heq => finRotate_ne_self_of_two_le hn i
      (Fin.castSucc_injective n heq).symm
  · subst a
    subst b
    exact fun heq => finRotate_ne_self_of_two_le hn i
      (Fin.castSucc_injective n heq).symm
  · subst a
    subst b
    exact (Fin.castSucc_ne_last ((finRotate n) i)).symm

def flowerPairColoring {n : ℕ} (hn : 2 ≤ n) :
    (flowerGraph n).Coloring (Fin (n + 1)) where
  toFun := flowerPairColor n
  map_rel' := by
    intro a b hab
    rw [flowerGraph, SimpleGraph.fromRel_adj] at hab
    rcases hab with ⟨_, h | h⟩
    · exact flowerPairColor_rel_ne hn h
    · exact (flowerPairColor_rel_ne hn h).symm

lemma flowerPairColoring_surjective {n : ℕ} (hn : 2 ≤ n) :
    Function.Surjective (flowerPairColoring hn) := by
  intro j
  by_cases hj : j = Fin.last n
  · refine ⟨Sum.inl (), ?_⟩
    simp [flowerPairColoring, flowerPairColor, hj]
  · obtain ⟨i, hi⟩ := Fin.eq_castSucc_of_ne_last hj
    refine ⟨Sum.inr (Sum.inl i), ?_⟩
    simp [flowerPairColoring, flowerPairColor, hi]

lemma flowerPairColor_colorClass_last (n : ℕ) :
    Set.ncard {x : FlowerVertex n | flowerPairColor n x = Fin.last n} = 1 := by
  have hset : {x : FlowerVertex n | flowerPairColor n x = Fin.last n} = {Sum.inl ()} := by
    ext x
    cases x with
    | inl u =>
        cases u
        simp [flowerPairColor]
    | inr x =>
        cases x with
        | inl i => simp [flowerPairColor, (Fin.castSucc_ne_last i).symm]
        | inr i => simp [flowerPairColor, (Fin.castSucc_ne_last ((finRotate n) i)).symm]
  rw [hset, Set.ncard_singleton]

lemma flowerPairColor_colorClass_castSucc (n : ℕ) (i : Fin n) :
    Set.ncard {x : FlowerVertex n | flowerPairColor n x = i.castSucc} = 2 := by
  let y : Fin n := (finRotate n).symm i
  have hset : {x : FlowerVertex n | flowerPairColor n x = i.castSucc} =
      {Sum.inr (Sum.inl i), Sum.inr (Sum.inr y)} := by
    ext x
    cases x with
    | inl u =>
        cases u
        simp [flowerPairColor, (Fin.castSucc_ne_last i).symm]
    | inr x =>
        cases x with
        | inl j =>
            simp [flowerPairColor, Fin.castSucc_injective n |>.eq_iff]
        | inr j =>
            simp [flowerPairColor, Fin.castSucc_injective n |>.eq_iff,
              Equiv.apply_eq_iff_eq_symm_apply, y]
  rw [hset]
  exact Set.ncard_pair (by simp)

lemma flowerPairColoring_equitable {n : ℕ} (hn : 2 ≤ n) :
    ∀ i j : Fin (n + 1),
      Nat.dist ((flowerPairColoring hn).colorClass i).ncard
        ((flowerPairColoring hn).colorClass j).ncard ≤ 1 := by
  intro i j
  have hi : ((flowerPairColoring hn).colorClass i).ncard = 1 ∨
      ((flowerPairColoring hn).colorClass i).ncard = 2 := by
    by_cases h : i = Fin.last n
    · left
      simp [SimpleGraph.Coloring.colorClass, flowerPairColoring, h,
        flowerPairColor_colorClass_last]
    · obtain ⟨a, ha⟩ := Fin.eq_castSucc_of_ne_last h
      right
      simp [SimpleGraph.Coloring.colorClass, flowerPairColoring, ← ha,
        flowerPairColor_colorClass_castSucc]
  have hj : ((flowerPairColoring hn).colorClass j).ncard = 1 ∨
      ((flowerPairColoring hn).colorClass j).ncard = 2 := by
    by_cases h : j = Fin.last n
    · left
      simp [SimpleGraph.Coloring.colorClass, flowerPairColoring, h,
        flowerPairColor_colorClass_last]
    · obtain ⟨a, ha⟩ := Fin.eq_castSucc_of_ne_last h
      right
      simp [SimpleGraph.Coloring.colorClass, flowerPairColoring, ← ha,
        flowerPairColor_colorClass_castSucc]
  rcases hi with hi | hi <;> rcases hj with hj | hj <;> rw [hi, hj] <;> decide

/- accepted add_to_file helper 2 -/
lemma flowerGraph_adj_center_rim (n : ℕ) (i : Fin n) :
    (flowerGraph n).Adj (Sum.inl () : FlowerVertex n) (Sum.inr (Sum.inl i)) := by
  rw [flowerGraph, SimpleGraph.fromRel_adj]
  constructor
  · simp
  · left
    left
    exact ⟨i, rfl, rfl⟩

lemma flowerGraph_adj_center_outer (n : ℕ) (i : Fin n) :
    (flowerGraph n).Adj (Sum.inl () : FlowerVertex n) (Sum.inr (Sum.inr i)) := by
  rw [flowerGraph, SimpleGraph.fromRel_adj]
  constructor
  · simp
  · left
    right
    right
    right
    exact ⟨i, rfl, rfl⟩

lemma flowerGraph_center_colorClass_singleton {n : ℕ} {β : Type}
    (f : (flowerGraph n).Coloring β) :
    f.colorClass (f (Sum.inl () : FlowerVertex n)) = {Sum.inl ()} := by
  ext x
  constructor
  · intro hx
    cases x with
    | inl u =>
        cases u
        rfl
    | inr x =>
        cases x with
        | inl i =>
            exfalso
            exact f.valid (flowerGraph_adj_center_rim n i) hx.symm
        | inr i =>
            exfalso
            exact f.valid (flowerGraph_adj_center_outer n i) hx.symm
  · intro hx
    simp at hx
    simp [SimpleGraph.Coloring.colorClass, hx]

lemma FlowerVertex_card (n : ℕ) :
    Fintype.card (FlowerVertex n) = 2 * n + 1 := by
  simp [FlowerVertex]
  omega

lemma Set.ncard_eq_filter_card {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (f : α → β) (b : β) :
    Set.ncard {a : α | f a = b} = (Finset.univ.filter fun a => f a = b).card := by
  rw [Set.ncard_eq_toFinset_card']
  congr 1
  ext a
  simp

lemma sum_ncard_colorClass {V β : Type} [Fintype V] [DecidableEq V]
    [Fintype β] [DecidableEq β] {G : SimpleGraph V} (f : G.Coloring β) :
    ∑ i : β, (f.colorClass i).ncard = Fintype.card V := by
  have hpoint : ∀ i : β, (f.colorClass i).ncard =
      (Finset.univ.filter fun x : V => f x = i).card := by
    intro i
    exact Set.ncard_eq_filter_card f i
  calc
    ∑ i : β, (f.colorClass i).ncard
        = ∑ i : β, (Finset.univ.filter fun x : V => f x = i).card := by
            exact Finset.sum_congr rfl fun i _ => hpoint i
    _ = ∑ i : β, ∑ x ∈ Finset.univ.filter (fun x : V => f x = i), 1 := by
            simp
    _ = ∑ x : V, 1 := Finset.sum_fiberwise Finset.univ f (fun _ : V => (1 : ℕ))
    _ = Fintype.card V := (Fintype.card_eq_sum_ones (α := V)).symm

lemma flowerGraph_color_lower {n ℓ : ℕ} (f : (flowerGraph n).Coloring (Fin ℓ))
    (hsurj : Function.Surjective f)
    (heq : ∀ i j : Fin ℓ,
      Nat.dist (f.colorClass i).ncard (f.colorClass j).ncard ≤ 1) :
    n + 1 ≤ ℓ := by
  classical
  let s : Fin ℓ → ℕ := fun i => (f.colorClass i).ncard
  have hcenter_set := flowerGraph_center_colorClass_singleton f
  have hcenter : s (f (Sum.inl () : FlowerVertex n)) = 1 := by
    simp [s, hcenter_set]
  have hpos : ∀ i : Fin ℓ, 0 < s i := by
    intro i
    obtain ⟨x, hx⟩ := hsurj i
    apply (Set.ncard_pos).mpr
    exact ⟨x, by simpa [SimpleGraph.Coloring.colorClass, s] using hx⟩
  have hsle : ∀ i : Fin ℓ, s i ≤ 2 := by
    intro i
    have hd := heq (f (Sum.inl () : FlowerVertex n)) i
    change Nat.dist (s (f (Sum.inl () : FlowerVertex n))) (s i) ≤ 1 at hd
    rw [hcenter, Nat.dist] at hd
    have hp := hpos i
    omega
  have hsum := sum_ncard_colorClass f
  have hbound : ∑ i : Fin ℓ, s i ≤ ∑ i : Fin ℓ, 2 := by
    exact Finset.sum_le_sum fun i _ => hsle i
  rw [FlowerVertex_card] at hsum
  change ∑ i : Fin ℓ, s i = 2 * n + 1 at hsum
  have hbound' : ∑ i : Fin ℓ, s i ≤ ℓ * 2 := by
    simpa using hbound
  omega

/- accepted add_to_file helper 3 -/
lemma flowerGraph_min_color_class_sizes {n : ℕ}
    (f : (flowerGraph n).Coloring (Fin (n + 1)))
    (hsurj : Function.Surjective f)
    (heq : ∀ i j : Fin (n + 1),
      Nat.dist (f.colorClass i).ncard (f.colorClass j).ncard ≤ 1)
    (hsort : ∀ i j : Fin (n + 1), i ≤ j →
      (f.colorClass j).ncard ≤ (f.colorClass i).ncard) :
    (∀ i : Fin n, (f.colorClass i.castSucc).ncard = 2) ∧
      (f.colorClass (Fin.last n)).ncard = 1 := by
  classical
  let s : Fin (n + 1) → ℕ := fun i => (f.colorClass i).ncard
  have hcenter_set := flowerGraph_center_colorClass_singleton f
  have hcenter : s (f (Sum.inl () : FlowerVertex n)) = 1 := by
    simp [s, hcenter_set]
  have hpos : ∀ i : Fin (n + 1), 0 < s i := by
    intro i
    obtain ⟨x, hx⟩ := hsurj i
    apply (Set.ncard_pos).mpr
    exact ⟨x, by simpa [SimpleGraph.Coloring.colorClass, s] using hx⟩
  have hs12 : ∀ i : Fin (n + 1), s i = 1 ∨ s i = 2 := by
    intro i
    have hd := heq (f (Sum.inl () : FlowerVertex n)) i
    change Nat.dist (s (f (Sum.inl () : FlowerVertex n))) (s i) ≤ 1 at hd
    rw [hcenter, Nat.dist] at hd
    have hp := hpos i
    omega
  have hsum := sum_ncard_colorClass f
  rw [FlowerVertex_card] at hsum
  change ∑ i : Fin (n + 1), s i = 2 * n + 1 at hsum
  have hdecomp : ∑ i : Fin (n + 1), s i =
      (n + 1) + (Finset.univ.filter fun i => s i = 2).card := by
    calc
      ∑ i : Fin (n + 1), s i
          = ∑ i : Fin (n + 1), (1 + if s i = 2 then 1 else 0) := by
              apply Finset.sum_congr rfl
              intro i _
              rcases hs12 i with hi | hi <;> simp [hi]
      _ = (∑ i : Fin (n + 1), (1 : ℕ)) +
            ∑ i : Fin (n + 1), (if s i = 2 then 1 else 0) := by
              rw [Finset.sum_add_distrib]
      _ = (n + 1) + (Finset.univ.filter fun i => s i = 2).card := by
              simp
  have hfilter : (Finset.univ.filter fun i => s i = 2).card = n := by
    omega
  have hnotcard : (Finset.univ.filter fun i => ¬ s i = 2).card = 1 := by
    have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (p := fun i : Fin (n + 1) => s i = 2)
    have huniv : (Finset.univ : Finset (Fin (n + 1))).card = n + 1 := by simp
    omega
  obtain ⟨i, hi_mem⟩ := Finset.card_pos.mp (by
    rw [hnotcard]
    norm_num : 0 < (Finset.univ.filter fun i => ¬ s i = 2).card)
  have hi_not2 : ¬ s i = 2 := by
    simpa using hi_mem
  have hi1 : s i = 1 := by
    rcases hs12 i with h | h
    · exact h
    · exact False.elim (hi_not2 h)
  have hlast : s (Fin.last n) = 1 := by
    have hle := hsort i (Fin.last n) (Fin.le_last i)
    change s (Fin.last n) ≤ s i at hle
    rw [hi1] at hle
    have hp := hpos (Fin.last n)
    omega
  have hunique : ∀ a b : Fin (n + 1), ¬ s a = 2 → ¬ s b = 2 → a = b := by
    have hle1 : (Finset.univ.filter fun i => ¬ s i = 2).card ≤ 1 := by omega
    have hu := Finset.card_le_one.mp hle1
    intro a b ha hb
    exact hu a (by simpa using ha) b (by simpa using hb)
  have hcast : ∀ a : Fin n, s a.castSucc = 2 := by
    intro a
    by_contra hnot
    have heqind := hunique a.castSucc (Fin.last n) hnot (by omega)
    exact Fin.castSucc_ne_last a heqind
  constructor
  · intro a
    exact hcast a
  · exact hlast

/- accepted add_to_file helper 4 -/
lemma sum_comp_colorClass {V β : Type} [Fintype V] [DecidableEq V]
    [Fintype β] [DecidableEq β] {G : SimpleGraph V}
    (f : G.Coloring β) (Y : β → ℝ) :
    ∑ x : V, Y (f x) = ∑ i : β, ((f.colorClass i).ncard : ℝ) * Y i := by
  have hfib := Finset.sum_fiberwise (s := Finset.univ) (g := f)
    (f := fun x : V => Y (f x))
  calc
    ∑ x : V, Y (f x) = ∑ i : β,
        ∑ x ∈ Finset.univ.filter (fun x : V => f x = i), Y (f x) := hfib.symm
    _ = ∑ i : β, ((Finset.univ.filter fun x : V => f x = i).card : ℝ) * Y i := by
          apply Finset.sum_congr rfl
          intro i _
          have hconst :
              (∑ x ∈ Finset.univ.filter (fun x : V => f x = i), Y (f x)) =
              ∑ x ∈ Finset.univ.filter (fun x : V => f x = i), Y i := by
            apply Finset.sum_congr rfl
            intro x hx
            simp at hx
            simp [hx]
          rw [hconst]
          simp [mul_comm]
    _ = ∑ i : β, ((f.colorClass i).ncard : ℝ) * Y i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← Set.ncard_eq_filter_card f i]
          rfl

lemma uniformPMF_integral_color_comp {V β : Type} [Fintype V] [Nonempty V]
    [DecidableEq V] [Fintype β] [DecidableEq β] {G : SimpleGraph V}
    (f : G.Coloring β) (Y : β → ℝ) :
    @MeasureTheory.integral V ℝ _ _ ⊤
      (@PMF.toMeasure V ⊤ (PMF.uniformOfFintype V)) (fun x => Y (f x)) =
    (∑ i : β, ((f.colorClass i).ncard : ℝ) * Y i) / (Fintype.card V : ℝ) := by
  letI : MeasurableSpace V := ⊤
  rw [PMF.integral_eq_sum]
  have hpoint : ∀ x : V, ((PMF.uniformOfFintype V) x).toReal • Y (f x) =
      ((Fintype.card V : ℝ)⁻¹) * Y (f x) := by
    intro x
    simp [PMF.uniformOfFintype_apply]
  calc
    ∑ a : V, ((PMF.uniformOfFintype V) a).toReal • Y (f a)
        = ∑ a : V, ((Fintype.card V : ℝ)⁻¹) * Y (f a) := by
            exact Finset.sum_congr rfl fun x _ => hpoint x
    _ = ((Fintype.card V : ℝ)⁻¹) * ∑ x : V, Y (f x) := by
            rw [Finset.mul_sum]
    _ = ((Fintype.card V : ℝ)⁻¹) *
          ∑ i : β, ((f.colorClass i).ncard : ℝ) * Y i := by
            rw [sum_comp_colorClass f Y]
    _ = (∑ i : β, ((f.colorClass i).ncard : ℝ) * Y i) / (Fintype.card V : ℝ) := by
            ring

/- accepted add_to_file helper 5 -/
lemma two_mul_sum_range_add_one (n : ℕ) :
    2 * (∑ i ∈ Finset.range n, ((i : ℝ) + 1)) = (n : ℝ) * ((n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      rw [mul_add, ih]
      push_cast
      ring

lemma six_mul_sum_range_add_one_sq (n : ℕ) :
    6 * (∑ i ∈ Finset.range n, (((i : ℝ) + 1) ^ 2)) =
      (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ]
      rw [mul_add, ih]
      push_cast
      ring_nf

lemma flower_weighted_sum_first {n : ℕ}
    {f : (flowerGraph n).Coloring (Fin (n + 1))}
    (hcast : ∀ i : Fin n, (f.colorClass i.castSucc).ncard = 2)
    (hlast : (f.colorClass (Fin.last n)).ncard = 1) :
    ∑ i : Fin (n + 1), ((f.colorClass i).ncard : ℝ) * ((i.val : ℝ) + 1) =
      ((n : ℝ) + 1) ^ 2 := by
  rw [Fin.sum_univ_castSucc]
  have hfirst :
      (∑ i : Fin n, ((f.colorClass i.castSucc).ncard : ℝ) *
        ((i.castSucc.val : ℝ) + 1)) =
      2 * ∑ i : Fin n, ((i.val : ℝ) + 1) := by
    calc
      ∑ i : Fin n, ((f.colorClass i.castSucc).ncard : ℝ) *
          ((i.castSucc.val : ℝ) + 1)
          = ∑ i : Fin n, 2 * ((i.val : ℝ) + 1) := by
              apply Finset.sum_congr rfl
              intro i _
              simp [hcast i]
      _ = 2 * ∑ i : Fin n, ((i.val : ℝ) + 1) := by
              rw [Finset.mul_sum]
  rw [hfirst]
  have hlastval :
      ((f.colorClass (Fin.last n)).ncard : ℝ) * (((Fin.last n).val : ℝ) + 1) =
      (n : ℝ) + 1 := by
    simp [hlast]
  rw [hlastval]
  rw [Fin.sum_univ_eq_sum_range (fun i => ((i : ℝ) + 1)) n]
  have h2 := two_mul_sum_range_add_one n
  nlinarith

lemma flower_weighted_sum_second {n : ℕ}
    {f : (flowerGraph n).Coloring (Fin (n + 1))}
    (hcast : ∀ i : Fin n, (f.colorClass i.castSucc).ncard = 2)
    (hlast : (f.colorClass (Fin.last n)).ncard = 1) :
    ∑ i : Fin (n + 1), ((f.colorClass i).ncard : ℝ) * (((i.val : ℝ) + 1) ^ 2) =
      ((n : ℝ) ^ 4 + 2 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 + (n : ℝ)) /
        (3 * (2 * (n : ℝ) + 1)) + ((n : ℝ) + 1) ^ 4 / (2 * (n : ℝ) + 1) := by
  rw [Fin.sum_univ_castSucc]
  have hfirst :
      (∑ i : Fin n, ((f.colorClass i.castSucc).ncard : ℝ) *
        (((i.castSucc.val : ℝ) + 1) ^ 2)) =
      2 * ∑ i : Fin n, (((i.val : ℝ) + 1) ^ 2) := by
    calc
      ∑ i : Fin n, ((f.colorClass i.castSucc).ncard : ℝ) *
          (((i.castSucc.val : ℝ) + 1) ^ 2)
          = ∑ i : Fin n, 2 * (((i.val : ℝ) + 1) ^ 2) := by
              apply Finset.sum_congr rfl
              intro i _
              simp [hcast i]
      _ = 2 * ∑ i : Fin n, (((i.val : ℝ) + 1) ^ 2) := by
              rw [Finset.mul_sum]
  rw [hfirst]
  have hlastval :
      ((f.colorClass (Fin.last n)).ncard : ℝ) * ((((Fin.last n).val : ℝ) + 1) ^ 2) =
      ((n : ℝ) + 1) ^ 2 := by
    simp [hlast]
  rw [hlastval]
  rw [Fin.sum_univ_eq_sum_range (fun i => (((i : ℝ) + 1) ^ 2)) n]
  have h6 := six_mul_sum_range_add_one_sq n
  have h2S : 2 * (∑ i ∈ Finset.range n, (((i : ℝ) + 1) ^ 2)) =
      (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / 3 := by
    nlinarith
  rw [h2S]
  have hden : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  field_simp [hden]
  ring

/- accepted add_to_file helper 6 -/
lemma flower_graph_moments_of_min {n : ℕ}
    (f : (flowerGraph n).Coloring (Fin (n + 1)))
    (hsurj : Function.Surjective f)
    (heq : ∀ i j : Fin (n + 1),
      Nat.dist (f.colorClass i).ncard (f.colorClass j).ncard ≤ 1)
    (hsort : ∀ i j : Fin (n + 1), i ≤ j →
      (f.colorClass j).ncard ≤ (f.colorClass i).ncard) :
    let X : FlowerVertex n → ℝ := fun x => (↑((f x).val + 1) : ℝ)
    let μ := @PMF.toMeasure (FlowerVertex n) ⊤ (PMF.uniformOfFintype (FlowerVertex n))
    @MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ X =
        ((n : ℝ) + 1) ^ 2 / (2 * (n : ℝ) + 1) ∧
      @ProbabilityTheory.variance (FlowerVertex n) ⊤ X μ =
        ((n : ℝ) ^ 4 + 2 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 + (n : ℝ)) /
          (3 * (2 * (n : ℝ) + 1) ^ 2) := by
  classical
  let X : FlowerVertex n → ℝ := fun x => (↑((f x).val + 1) : ℝ)
  let μ := @PMF.toMeasure (FlowerVertex n) ⊤ (PMF.uniformOfFintype (FlowerVertex n))
  obtain ⟨hcast, hlast⟩ := flowerGraph_min_color_class_sizes f hsurj heq hsort
  have hweighted1 := flower_weighted_sum_first (f := f) hcast hlast
  have hweighted2 := flower_weighted_sum_second (f := f) hcast hlast
  have hN : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have hmean : @MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ X =
      ((n : ℝ) + 1) ^ 2 / (2 * (n : ℝ) + 1) := by
    have h := uniformPMF_integral_color_comp (V := FlowerVertex n)
      (β := Fin (n + 1)) (G := flowerGraph n) f
      (fun i => ((i.val : ℝ) + 1))
    calc
      @MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ X
          = (∑ i : Fin (n + 1), ((f.colorClass i).ncard : ℝ) *
              ((i.val : ℝ) + 1)) / (Fintype.card (FlowerVertex n) : ℝ) := by
                simpa [X, μ] using h
      _ = ((n : ℝ) + 1) ^ 2 / (2 * (n : ℝ) + 1) := by
              rw [hweighted1, FlowerVertex_card]
              norm_num
  have hsecond : @MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ (fun x => X x ^ 2) =
      ((n : ℝ) ^ 4 + 2 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 + (n : ℝ)) /
          (3 * (2 * (n : ℝ) + 1) ^ 2) +
        ((n : ℝ) + 1) ^ 4 / ((2 * (n : ℝ) + 1) ^ 2) := by
    have h := uniformPMF_integral_color_comp (V := FlowerVertex n)
      (β := Fin (n + 1)) (G := flowerGraph n) f
      (fun i => (((i.val : ℝ) + 1) ^ 2))
    calc
      @MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ (fun x => X x ^ 2)
          = (∑ i : Fin (n + 1), ((f.colorClass i).ncard : ℝ) *
              (((i.val : ℝ) + 1) ^ 2)) / (Fintype.card (FlowerVertex n) : ℝ) := by
                simpa [X, μ] using h
      _ = ((n : ℝ) ^ 4 + 2 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 + (n : ℝ)) /
            (3 * (2 * (n : ℝ) + 1) ^ 2) +
          ((n : ℝ) + 1) ^ 4 / ((2 * (n : ℝ) + 1) ^ 2) := by
            rw [hweighted2, FlowerVertex_card]
            field_simp [hN]
            ring_nf
            norm_num
  have hmem : MeasureTheory.MemLp X 2 μ := by
    exact MeasureTheory.MemLp.of_discrete
  have hvar : @ProbabilityTheory.variance (FlowerVertex n) ⊤ X μ =
      @MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ (fun x => X x ^ 2) -
        (@MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ X) ^ 2 := by
    have hv := ProbabilityTheory.variance_eq_sub (μ := μ) (X := X) hmem
    simpa [pow_two] using hv
  constructor
  · exact hmean
  · calc
      @ProbabilityTheory.variance (FlowerVertex n) ⊤ X μ
          = @MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ (fun x => X x ^ 2) -
              (@MeasureTheory.integral (FlowerVertex n) ℝ _ _ ⊤ μ X) ^ 2 := hvar
      _ = (((n : ℝ) ^ 4 + 2 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 + (n : ℝ)) /
              (3 * (2 * (n : ℝ) + 1) ^ 2) +
            ((n : ℝ) + 1) ^ 4 / ((2 * (n : ℝ) + 1) ^ 2)) -
            (((n : ℝ) + 1) ^ 2 / (2 * (n : ℝ) + 1)) ^ 2 := by
              rw [hsecond, hmean]
      _ = ((n : ℝ) ^ 4 + 2 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 + (n : ℝ)) /
            (3 * (2 * (n : ℝ) + 1) ^ 2) := by
              field_simp [hN]
              ring

/- verified submission -/
theorem flower_graph_equitable_coloring_moments
    (n k : ℕ) (hn : 3 ≤ n) :
    let V := Unit ⊕ (Fin n ⊕ Fin n)
    let F : SimpleGraph V := SimpleGraph.fromRel fun a b =>
      (∃ i : Fin n, a = Sum.inl () ∧ b = Sum.inr (Sum.inl i)) ∨
      (∃ i : Fin n,
        a = Sum.inr (Sum.inl i) ∧
          b = Sum.inr (Sum.inl ((finRotate n) i))) ∨
      (∃ i : Fin n, a = Sum.inr (Sum.inl i) ∧ b = Sum.inr (Sum.inr i)) ∨
      (∃ i : Fin n, a = Sum.inl () ∧ b = Sum.inr (Sum.inr i))
    ∀ f : F.Coloring (Fin k),
      Function.Surjective f →
      (∀ i j : Fin k,
        Nat.dist (f.colorClass i).ncard (f.colorClass j).ncard ≤ 1) →
      (∀ ℓ : ℕ, ℓ < k →
        ¬ ∃ g : F.Coloring (Fin ℓ),
          Function.Surjective g ∧
          (∀ i j : Fin ℓ,
            Nat.dist (g.colorClass i).ncard (g.colorClass j).ncard ≤ 1)) →
      (∀ i j : Fin k, i ≤ j →
        (f.colorClass j).ncard ≤ (f.colorClass i).ncard) →
      let X : V → ℝ := fun x => (↑((f x).val + 1) : ℝ)
      let μ := @PMF.toMeasure V ⊤ (PMF.uniformOfFintype V)
      @MeasureTheory.integral V ℝ _ _ ⊤ μ X =
          ((n : ℝ) + 1) ^ 2 / (2 * (n : ℝ) + 1) ∧
        @ProbabilityTheory.variance V ⊤ X μ =
          ((n : ℝ) ^ 4 + 2 * (n : ℝ) ^ 3 + 2 * (n : ℝ) ^ 2 + (n : ℝ)) /
            (3 * (2 * (n : ℝ) + 1) ^ 2) := by
  classical
  intro V F f hsurj heq hmin hsort
  have h2n : 2 ≤ n := by omega
  have hk_lower : n + 1 ≤ k :=
    flowerGraph_color_lower f hsurj heq
  have hk_upper : k ≤ n + 1 := by
    by_contra h
    have hlt : n + 1 < k := Nat.lt_of_not_ge h
    exact hmin (n + 1) hlt
      ⟨flowerPairColoring h2n, flowerPairColoring_surjective h2n,
        flowerPairColoring_equitable h2n⟩
  have hk : k = n + 1 := le_antisymm hk_upper hk_lower
  subst k
  exact flower_graph_moments_of_min f hsurj heq hsort

end Rollout_p1268_flower_graph_equitable_coloring_moments

#check_dependency_graph "Rollout_p1268_flower_graph_equitable_coloring_moments.flower_graph_equitable_coloring_moments" against "{\"edges\":[{\"conclusion\":{\"name\":\"h2n\",\"statement\":\"2 ≤ n\"},\"graphEdgeId\":\"h_001_h2n\",\"premises\":[{\"name\":\"hn\",\"statement\":\"3 ≤ n\"}],\"rawEdgeId\":\"telescope_10\"},{\"conclusion\":{\"name\":\"hk_lower\",\"statement\":\"n + 1 ≤ k\"},\"graphEdgeId\":\"h_002_hk_lower\",\"premises\":[{\"name\":\"hsurj\",\"statement\":\"Function.Surjective ⇑f\"},{\"name\":\"heq\",\"statement\":\"∀ (i j : Fin k), (f.colorClass i).ncard.dist (f.colorClass j).ncard ≤ 1\"}],\"rawEdgeId\":\"telescope_11\"},{\"conclusion\":{\"name\":\"hk_upper\",\"statement\":\"k ≤ n + 1\"},\"graphEdgeId\":\"h_003_hk_upper\",\"premises\":[{\"name\":\"hmin\",\"statement\":\"∀ ℓ < k, ¬∃ g, Function.Surjective ⇑g ∧ ∀ (i j : Fin ℓ), (g.colorClass i).ncard.dist (g.colorClass j).ncard ≤ 1\"},{\"name\":\"h2n\",\"statement\":\"2 ≤ n\"}],\"rawEdgeId\":\"telescope_12\"},{\"conclusion\":{\"name\":\"hk\",\"statement\":\"k = n + 1\"},\"graphEdgeId\":\"h_004_hk\",\"premises\":[{\"name\":\"hk_lower\",\"statement\":\"n + 1 ≤ k\"},{\"name\":\"hk_upper\",\"statement\":\"k ≤ n + 1\"}],\"rawEdgeId\":\"telescope_13\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let X := fun x => ↑(↑(f x) + 1); let μ := (PMF.uniformOfFintype V).toMeasure; MeasureTheory.integral μ X = (↑n + 1) ^ 2 / (2 * ↑n + 1) ∧ ProbabilityTheory.variance X μ = (↑n ^ 4 + 2 * ↑n ^ 3 + 2 * ↑n ^ 2 + ↑n) / (3 * (2 * ↑n + 1) ^ 2)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hsurj\",\"statement\":\"Function.Surjective ⇑f\"},{\"name\":\"heq\",\"statement\":\"∀ (i j : Fin k), (f.colorClass i).ncard.dist (f.colorClass j).ncard ≤ 1\"},{\"name\":\"hmin\",\"statement\":\"∀ ℓ < k, ¬∃ g, Function.Surjective ⇑g ∧ ∀ (i j : Fin ℓ), (g.colorClass i).ncard.dist (g.colorClass j).ncard ≤ 1\"},{\"name\":\"hsort\",\"statement\":\"∀ (i j : Fin k), i ≤ j → (f.colorClass j).ncard ≤ (f.colorClass i).ncard\"},{\"name\":\"hk_lower\",\"statement\":\"n + 1 ≤ k\"},{\"name\":\"hk_upper\",\"statement\":\"k ≤ n + 1\"},{\"name\":\"hk\",\"statement\":\"k = n + 1\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1268_flower_graph_equitable_coloring_moments\",\"reconstructedProofSha256\":\"6cbdaa3ce12753bec5a1e8f5b3c39103eac821254f2029d25666a14413033484\",\"selectedEdgeCount\":5,\"theoremName\":\"Rollout_p1268_flower_graph_equitable_coloring_moments.flower_graph_equitable_coloring_moments\",\"topologySha256\":\"62fc5d51e2f8984904db07fbb0ba470440156ede0fd07187201aad0c3ef5f3f5\"}"

namespace Rollout_p1286_lebesgue_integral_modified_salem

-- graph_id: p1286_lebesgue_integral_modified_salem
-- topology_sha256: c173f2fd3f41805f05c416c106daa252296564e158ccbe52222c879356552a75
/- accepted add_to_file helper 1 -/

noncomputable section

def msP (p₀ p₁ p₂ : ℝ) : Fin 3 → ℝ := ![p₀, p₁, p₂]

def msB (p₀ p₁ p₂ : ℝ) : Fin 3 → ℝ := ![0, p₀, p₀ + p₁]

def msE (p₀ p₁ p₂ : ℝ) (i : ℕ → Fin 3) : ℝ :=
  ∑' k : ℕ, msB p₀ p₁ p₂ (i k) * ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i r)

def msTheta : Fin 3 → Fin 3 := ![0, 2, 1]

lemma msP_pos {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1) (j : Fin 3) :
    0 < msP p₀ p₁ p₂ j := by
  fin_cases j <;> simp [msP, hp₀.1, hp₁.1, hp₂.1]

lemma msP_lt_one {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1) (j : Fin 3) :
    msP p₀ p₁ p₂ j < 1 := by
  fin_cases j <;> simp [msP, hp₀.2, hp₁.2, hp₂.2]

lemma msP_nonneg {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1) (j : Fin 3) :
    0 ≤ msP p₀ p₁ p₂ j :=
  (msP_pos hp₀ hp₁ hp₂ j).le

lemma msB_nonneg {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1) (j : Fin 3) :
    0 ≤ msB p₀ p₁ p₂ j := by
  fin_cases j <;> simp [msB, hp₀.1.le, add_nonneg hp₀.1.le hp₁.1.le]

lemma msB_add_msP_le_one {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (j : Fin 3) :
    msB p₀ p₁ p₂ j + msP p₀ p₁ p₂ j ≤ 1 := by
  fin_cases j <;> simp [msB, msP]
  · exact hp₀.2.le
  · have : p₀ + p₁ < 1 := by
      rw [← hsum]
      linarith [hp₂.1]
    exact this.le
  · exact hsum.le

lemma msB_le_one {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (j : Fin 3) :
    msB p₀ p₁ p₂ j ≤ 1 := by
  have h := msB_add_msP_le_one hp₀ hp₁ hp₂ hsum j
  have hp := msP_nonneg hp₀ hp₁ hp₂ j
  linarith

end

/- accepted add_to_file helper 2 -/
noncomputable section

lemma msE_term_nonneg {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (i : ℕ → Fin 3) (k : ℕ) :
    0 ≤ msB p₀ p₁ p₂ (i k) * ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i r) := by
  exact mul_nonneg (msB_nonneg hp₀ hp₁ _)
    (Finset.prod_nonneg fun r _ => msP_nonneg hp₀ hp₁ hp₂ _)

lemma msE_summable {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (i : ℕ → Fin 3) :
    Summable fun k : ℕ =>
      msB p₀ p₁ p₂ (i k) * ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i r) := by
  let q := max p₀ (max p₁ p₂)
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact le_trans hp₀.1.le (le_max_left _ _)
  have hq_lt_one : q < 1 := by
    dsimp [q]
    exact max_lt hp₀.2 (max_lt hp₁.2 hp₂.2)
  refine Summable.of_nonneg_of_le
    (fun k => msE_term_nonneg hp₀ hp₁ hp₂ i k) ?_ (summable_geometric_of_lt_one hq_nonneg hq_lt_one)
  intro k
  have hp_le_q : ∀ r ∈ Finset.range k, msP p₀ p₁ p₂ (i r) ≤ q := by
    intro r hr
    generalize hj : i r = j
    fin_cases j <;> simp [msP, q]
  have hprod : (∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i r)) ≤ q ^ k := by
    calc
      (∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i r)) ≤
          ∏ r ∈ Finset.range k, q :=
        Finset.prod_le_prod
          (fun r _ => msP_nonneg hp₀ hp₁ hp₂ _)
          (fun r hr => hp_le_q r hr)
      _ = q ^ k := by simp
  calc
    msB p₀ p₁ p₂ (i k) * ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i r)
        ≤ 1 * q ^ k := by
          exact mul_le_mul (msB_le_one hp₀ hp₁ hp₂ hsum _) hprod
            (Finset.prod_nonneg fun r _ => msP_nonneg hp₀ hp₁ hp₂ _) zero_le_one
    _ = q ^ k := one_mul _

end

/- accepted add_to_file helper 3 -/
noncomputable section

lemma msE_eq_beta_add_mul_tail {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (i : ℕ → Fin 3) :
    msE p₀ p₁ p₂ i =
      msB p₀ p₁ p₂ (i 0) + msP p₀ p₁ p₂ (i 0) * msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) := by
  let term : (ℕ → Fin 3) → ℕ → ℝ := fun j k ↦
    msB p₀ p₁ p₂ (j k) * ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (j r)
  have hsplit : msE p₀ p₁ p₂ i = term i 0 + ∑' k : ℕ, term i (k + 1) := by
    dsimp [msE, term]
    exact (msE_summable hp₀ hp₁ hp₂ hsum i).tsum_eq_zero_add
  rw [hsplit]
  have hshift : (∑' k : ℕ, term i (k + 1)) =
      msP p₀ p₁ p₂ (i 0) * msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) := by
    calc
      (∑' k : ℕ, term i (k + 1)) =
          ∑' k : ℕ, msP p₀ p₁ p₂ (i 0) * term (fun n ↦ i (n + 1)) k := by
            congr 1
            ext k
            dsimp [term]
            rw [Finset.prod_range_succ']
            ring
      _ = msP p₀ p₁ p₂ (i 0) * msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) := by
            rw [tsum_mul_left]
            rfl
  rw [hshift]
  dsimp [term]
  simp

end

/- accepted add_to_file helper 4 -/
noncomputable section

lemma msE_partial_succ {p₀ p₁ p₂ : ℝ} (i : ℕ → Fin 3) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
        msB p₀ p₁ p₂ (i k) * ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i r)) =
      msB p₀ p₁ p₂ (i 0) + msP p₀ p₁ p₂ (i 0) *
        (∑ k ∈ Finset.range n,
          msB p₀ p₁ p₂ (i (k + 1)) *
            ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i (r + 1))) := by
  calc
    (∑ k ∈ Finset.range (n + 1),
        msB p₀ p₁ p₂ (i k) * ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i r))
        = msB p₀ p₁ p₂ (i 0) +
          ∑ k ∈ Finset.range n,
            msB p₀ p₁ p₂ (i (k + 1)) *
              ∏ r ∈ Finset.range (k + 1), msP p₀ p₁ p₂ (i r) := by
            rw [Finset.sum_range_succ']
            rw [add_comm]
            simp
    _ = msB p₀ p₁ p₂ (i 0) + msP p₀ p₁ p₂ (i 0) *
          (∑ k ∈ Finset.range n,
            msB p₀ p₁ p₂ (i (k + 1)) *
              ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i (r + 1))) := by
          rw [Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl ?_
          intro k hk
          rw [Finset.prod_range_succ']
          ring

lemma msE_partial_le_one {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) :
    ∀ n : ℕ, ∀ i : ℕ → Fin 3,
      (∑ k ∈ Finset.range n,
        msB p₀ p₁ p₂ (i k) * ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i r)) ≤ 1 := by
  intro n
  induction n with
  | zero =>
      intro i
      simp
  | succ n ih =>
      intro i
      rw [msE_partial_succ]
      have hpnonneg := msP_nonneg hp₀ hp₁ hp₂ (i 0)
      have htail := ih (fun k ↦ i (k + 1))
      have hbound := msB_add_msP_le_one hp₀ hp₁ hp₂ hsum (i 0)
      calc
        msB p₀ p₁ p₂ (i 0) + msP p₀ p₁ p₂ (i 0) *
            (∑ k ∈ Finset.range n,
              msB p₀ p₁ p₂ (i (k + 1)) *
                ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i (r + 1)))
            ≤ msB p₀ p₁ p₂ (i 0) + msP p₀ p₁ p₂ (i 0) * 1 := by
              exact add_le_add_right (mul_le_mul_of_nonneg_left htail hpnonneg) _
        _ = msB p₀ p₁ p₂ (i 0) + msP p₀ p₁ p₂ (i 0) := by ring
        _ ≤ 1 := hbound

lemma msE_nonneg {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1) (i : ℕ → Fin 3) :
    0 ≤ msE p₀ p₁ p₂ i := by
  dsimp [msE]
  exact tsum_nonneg (msE_term_nonneg hp₀ hp₁ hp₂ i)

lemma msE_le_one {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (i : ℕ → Fin 3) :
    msE p₀ p₁ p₂ i ≤ 1 := by
  have hs := msE_summable hp₀ hp₁ hp₂ hsum i
  exact le_of_tendsto hs.hasSum.tendsto_sum_nat
    (Filter.Eventually.of_forall fun n ↦ msE_partial_le_one hp₀ hp₁ hp₂ hsum n i)

lemma msE_mem_Icc {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (i : ℕ → Fin 3) :
    msE p₀ p₁ p₂ i ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨msE_nonneg hp₀ hp₁ hp₂ i, msE_le_one hp₀ hp₁ hp₂ hsum i⟩

end

/- accepted add_to_file helper 5 -/
noncomputable section

lemma msE_eq_one_head {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) {i : ℕ → Fin 3}
    (hi : msE p₀ p₁ p₂ i = 1) :
    i 0 = 2 := by
  have hrec := msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum i
  have htail := msE_le_one hp₀ hp₁ hp₂ hsum (fun k ↦ i (k + 1))
  generalize hj : i 0 = j
  fin_cases j
  · have hE : msE p₀ p₁ p₂ i = p₀ * msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) := by
      rw [hrec, hj]
      simp [msB, msP]
    have hle : msE p₀ p₁ p₂ i ≤ p₀ := by
      rw [hE]
      calc
        p₀ * msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) ≤ p₀ * 1 :=
          mul_le_mul_of_nonneg_left htail hp₀.1.le
        _ = p₀ := by ring
    have hp1 : (1 : ℝ) ≤ p₀ := by
      rw [← hi]
      exact hle
    linarith [hp₀.2]
  · have hp01 : p₀ + p₁ < 1 := by
      rw [← hsum]
      linarith [hp₂.1]
    have hE : msE p₀ p₁ p₂ i = p₀ + p₁ * msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) := by
      rw [hrec, hj]
      simp [msB, msP]
    have hle : msE p₀ p₁ p₂ i ≤ p₀ + p₁ := by
      rw [hE]
      calc
        p₀ + p₁ * msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) ≤ p₀ + p₁ * 1 :=
          add_le_add_right (mul_le_mul_of_nonneg_left htail hp₁.1.le) _
        _ = p₀ + p₁ := by ring
    have hp1 : (1 : ℝ) ≤ p₀ + p₁ := by
      rw [← hi]
      exact hle
    linarith
  · rfl

lemma msE_eq_one_tail {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) {i : ℕ → Fin 3}
    (hi : msE p₀ p₁ p₂ i = 1) :
    msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) = 1 := by
  have hhead := msE_eq_one_head hp₀ hp₁ hp₂ hsum hi
  have hrec := msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum i
  rw [hhead] at hrec
  simp [msB, msP] at hrec
  have hmul : p₂ * (msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) - 1) = 0 := by
    linarith
  have hfactor := mul_eq_zero.mp hmul
  rcases hfactor with hp | ht
  · linarith [hp₂.1]
  · linarith

lemma msE_eq_one_apply {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) :
    ∀ k : ℕ, ∀ i : ℕ → Fin 3, msE p₀ p₁ p₂ i = 1 → i k = 2 := by
  intro k
  induction k with
  | zero =>
      intro i hi
      exact msE_eq_one_head hp₀ hp₁ hp₂ hsum hi
  | succ k ih =>
      intro i hi
      exact ih (fun n ↦ i (n + 1))
        (msE_eq_one_tail hp₀ hp₁ hp₂ hsum hi)

lemma msE_eq_zero_head {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) {i : ℕ → Fin 3}
    (hi : msE p₀ p₁ p₂ i = 0) :
    i 0 = 0 := by
  have hrec := msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum i
  have htail_nonneg := msE_nonneg hp₀ hp₁ hp₂ (fun k ↦ i (k + 1))
  generalize hj : i 0 = j
  fin_cases j
  · rfl
  · have hE : msE p₀ p₁ p₂ i = p₀ + p₁ * msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) := by
      rw [hrec, hj]
      simp [msB, msP]
    have hnonneg : 0 ≤ p₁ * msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) :=
      mul_nonneg hp₁.1.le htail_nonneg
    rw [hE] at hi
    linarith [hp₀.1]
  · have hE : msE p₀ p₁ p₂ i = p₀ + p₁ + p₂ * msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) := by
      rw [hrec, hj]
      simp [msB, msP]
    have hnonneg : 0 ≤ p₂ * msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) :=
      mul_nonneg hp₂.1.le htail_nonneg
    have hp01 : 0 < p₀ + p₁ := add_pos hp₀.1 hp₁.1
    rw [hE] at hi
    linarith

lemma msE_eq_zero_tail {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) {i : ℕ → Fin 3}
    (hi : msE p₀ p₁ p₂ i = 0) :
    msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) = 0 := by
  have hhead := msE_eq_zero_head hp₀ hp₁ hp₂ hsum hi
  have hrec := msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum i
  rw [hhead] at hrec
  simp [msB, msP] at hrec
  have hmul : p₀ * msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) = 0 := by linarith
  have hfactor := mul_eq_zero.mp hmul
  rcases hfactor with hp | ht
  · linarith [hp₀.1]
  · exact ht

lemma msE_eq_zero_apply {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) :
    ∀ k : ℕ, ∀ i : ℕ → Fin 3, msE p₀ p₁ p₂ i = 0 → i k = 0 := by
  intro k
  induction k with
  | zero =>
      intro i hi
      exact msE_eq_zero_head hp₀ hp₁ hp₂ hsum hi
  | succ k ih =>
      intro i hi
      exact ih (fun n ↦ i (n + 1))
        (msE_eq_zero_tail hp₀ hp₁ hp₂ hsum hi)

end

/- accepted add_to_file helper 6 -/
noncomputable section

def msEventuallyZero (i : ℕ → Fin 3) : Prop :=
  ∃ N : ℕ, ∀ k : ℕ, N ≤ k → i k = 0

lemma msEventuallyZero.tail {i : ℕ → Fin 3} (hi : msEventuallyZero i) :
    msEventuallyZero (fun k ↦ i (k + 1)) := by
  rcases hi with ⟨N, hN⟩
  cases N with
  | zero =>
      refine ⟨0, ?_⟩
      intro k hk
      exact hN (k + 1) (Nat.zero_le _)
  | succ N =>
      refine ⟨N, ?_⟩
      intro k hk
      exact hN (k + 1) (Nat.succ_le_succ hk)

lemma msE_head_lower {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (i : ℕ → Fin 3) :
    msB p₀ p₁ p₂ (i 0) ≤ msE p₀ p₁ p₂ i := by
  rw [msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum i]
  have h := mul_nonneg (msP_nonneg hp₀ hp₁ hp₂ (i 0))
    (msE_nonneg hp₀ hp₁ hp₂ (fun k ↦ i (k + 1)))
  linarith

lemma msE_head_upper {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (i : ℕ → Fin 3) :
    msE p₀ p₁ p₂ i ≤
      msB p₀ p₁ p₂ (i 0) + msP p₀ p₁ p₂ (i 0) := by
  rw [msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum i]
  have htail := msE_le_one hp₀ hp₁ hp₂ hsum (fun k ↦ i (k + 1))
  have hmul := mul_le_mul_of_nonneg_left htail (msP_nonneg hp₀ hp₁ hp₂ (i 0))
  rw [mul_one] at hmul
  exact add_le_add_right hmul _

end

/- accepted add_to_file helper 7 -/
noncomputable section

lemma msE_eq_one_not_eventuallyZero {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) {i : ℕ → Fin 3}
    (hi : msE p₀ p₁ p₂ i = 1) :
    ¬ msEventuallyZero i := by
  rintro ⟨N, hN⟩
  have htwo := msE_eq_one_apply hp₀ hp₁ hp₂ hsum N i hi
  have hzero := hN N le_rfl
  rw [hzero] at htwo
  exact (by decide : (0 : Fin 3) ≠ 2) htwo

lemma msE_eventuallyZero_head_eq {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) {i j : ℕ → Fin 3}
    (hEq : msE p₀ p₁ p₂ i = msE p₀ p₁ p₂ j)
    (hi_zero : msEventuallyZero i) (hj_zero : msEventuallyZero j) :
    i 0 = j 0 := by
  have cross01 : ∀ {a b : ℕ → Fin 3},
      msE p₀ p₁ p₂ a = msE p₀ p₁ p₂ b →
      msEventuallyZero a → a 0 = 0 → b 0 = 1 → False := by
    intro a b hab ha_zero ha0 hb1
    have ha_tail_zero := ha_zero.tail
    have hEa : msE p₀ p₁ p₂ a = p₀ * msE p₀ p₁ p₂ (fun k ↦ a (k + 1)) := by
      rw [msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum a, ha0]
      simp [msB, msP]
    have hEb : msE p₀ p₁ p₂ b = p₀ + p₁ * msE p₀ p₁ p₂ (fun k ↦ b (k + 1)) := by
      rw [msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum b, hb1]
      simp [msB, msP]
    have ha_upper : msE p₀ p₁ p₂ a ≤ p₀ := by
      rw [hEa]
      have htail := msE_le_one hp₀ hp₁ hp₂ hsum (fun k ↦ a (k + 1))
      calc
        p₀ * msE p₀ p₁ p₂ (fun k ↦ a (k + 1)) ≤ p₀ * 1 :=
          mul_le_mul_of_nonneg_left htail hp₀.1.le
        _ = p₀ := by ring
    have hb_lower : p₀ ≤ msE p₀ p₁ p₂ b := by
      rw [hEb]
      have htail := msE_nonneg hp₀ hp₁ hp₂ (fun k ↦ b (k + 1))
      have hmul := mul_nonneg hp₁.1.le htail
      linarith
    have ha_eq : msE p₀ p₁ p₂ a = p₀ := le_antisymm ha_upper (by linarith)
    have hb_eq : msE p₀ p₁ p₂ b = p₀ := le_antisymm (by linarith) hb_lower
    have htail_one : msE p₀ p₁ p₂ (fun k ↦ a (k + 1)) = 1 := by
      have hmul : p₀ * msE p₀ p₁ p₂ (fun k ↦ a (k + 1)) = p₀ * 1 := by
        rw [← hEa, ha_eq]
        ring
      exact mul_left_cancel₀ (ne_of_gt hp₀.1) hmul
    exact msE_eq_one_not_eventuallyZero hp₀ hp₁ hp₂ hsum htail_one ha_tail_zero
  have cross12 : ∀ {a b : ℕ → Fin 3},
      msE p₀ p₁ p₂ a = msE p₀ p₁ p₂ b →
      msEventuallyZero a → a 0 = 1 → b 0 = 2 → False := by
    intro a b hab ha_zero ha1 hb2
    have ha_tail_zero := ha_zero.tail
    have hEa : msE p₀ p₁ p₂ a = p₀ + p₁ * msE p₀ p₁ p₂ (fun k ↦ a (k + 1)) := by
      rw [msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum a, ha1]
      simp [msB, msP]
    have hEb : msE p₀ p₁ p₂ b = p₀ + p₁ + p₂ * msE p₀ p₁ p₂ (fun k ↦ b (k + 1)) := by
      rw [msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum b, hb2]
      simp [msB, msP]
    have ha_upper : msE p₀ p₁ p₂ a ≤ p₀ + p₁ := by
      rw [hEa]
      have htail := msE_le_one hp₀ hp₁ hp₂ hsum (fun k ↦ a (k + 1))
      calc
        p₀ + p₁ * msE p₀ p₁ p₂ (fun k ↦ a (k + 1)) ≤ p₀ + p₁ * 1 :=
          add_le_add_right (mul_le_mul_of_nonneg_left htail hp₁.1.le) _
        _ = p₀ + p₁ := by ring
    have hb_lower : p₀ + p₁ ≤ msE p₀ p₁ p₂ b := by
      rw [hEb]
      have htail := msE_nonneg hp₀ hp₁ hp₂ (fun k ↦ b (k + 1))
      have hmul := mul_nonneg hp₂.1.le htail
      linarith
    have ha_eq : msE p₀ p₁ p₂ a = p₀ + p₁ := le_antisymm ha_upper (by linarith)
    have hb_eq : msE p₀ p₁ p₂ b = p₀ + p₁ := le_antisymm (by linarith) hb_lower
    have htail_one : msE p₀ p₁ p₂ (fun k ↦ a (k + 1)) = 1 := by
      have hmul : p₁ * msE p₀ p₁ p₂ (fun k ↦ a (k + 1)) = p₁ * 1 := by
        have : p₀ + p₁ * msE p₀ p₁ p₂ (fun k ↦ a (k + 1)) = p₀ + p₁ := by
          rw [← hEa, ha_eq]
        linarith
      exact mul_left_cancel₀ (ne_of_gt hp₁.1) hmul
    exact msE_eq_one_not_eventuallyZero hp₀ hp₁ hp₂ hsum htail_one ha_tail_zero
  have cross02 : ∀ {a b : ℕ → Fin 3},
      msE p₀ p₁ p₂ a = msE p₀ p₁ p₂ b → a 0 = 0 → b 0 = 2 → False := by
    intro a b hab ha0 hb2
    have ha_upper : msE p₀ p₁ p₂ a ≤ p₀ := by
      have h := msE_head_upper hp₀ hp₁ hp₂ hsum a
      rw [ha0] at h
      simpa [msB, msP] using h
    have hb_lower : p₀ + p₁ ≤ msE p₀ p₁ p₂ b := by
      have h := msE_head_lower hp₀ hp₁ hp₂ hsum b
      rw [hb2] at h
      simpa [msB, msP] using h
    linarith [hp₁.1]
  generalize hi0 : i 0 = a
  generalize hj0 : j 0 = b
  fin_cases a <;> fin_cases b
  · rfl
  · exact False.elim (cross01 hEq hi_zero hi0 hj0)
  · exact False.elim (cross02 hEq hi0 hj0)
  · exact False.elim ((by decide : (0 : Fin 3) ≠ 1)
      (False.elim (cross01 hEq.symm hj_zero hj0 hi0)))
  · rfl
  · exact False.elim (cross12 hEq hi_zero hi0 hj0)
  · exact False.elim ((by decide : (0 : Fin 3) ≠ 2)
      (False.elim (cross02 hEq.symm hj0 hi0)))
  · exact False.elim ((by decide : (1 : Fin 3) ≠ 2)
      (False.elim (cross12 hEq.symm hj_zero hj0 hi0)))
  · rfl

end

/- accepted add_to_file helper 8 -/
noncomputable section

lemma msE_eventuallyZero_tail_eq {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) {i j : ℕ → Fin 3}
    (hEq : msE p₀ p₁ p₂ i = msE p₀ p₁ p₂ j)
    (hi_zero : msEventuallyZero i) (hj_zero : msEventuallyZero j) :
    msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) =
      msE p₀ p₁ p₂ (fun k ↦ j (k + 1)) := by
  have hhead := msE_eventuallyZero_head_eq hp₀ hp₁ hp₂ hsum hEq hi_zero hj_zero
  have hrec_i := msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum i
  have hrec_j := msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum j
  rw [hhead] at hrec_i
  have hpos := msP_pos hp₀ hp₁ hp₂ (j 0)
  have hmul :
      msP p₀ p₁ p₂ (j 0) * msE p₀ p₁ p₂ (fun k ↦ i (k + 1)) =
        msP p₀ p₁ p₂ (j 0) * msE p₀ p₁ p₂ (fun k ↦ j (k + 1)) := by
    linarith
  exact mul_left_cancel₀ (ne_of_gt hpos) hmul

lemma msE_eventuallyZero_injective {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) :
    ∀ k : ℕ, ∀ i j : ℕ → Fin 3,
      msE p₀ p₁ p₂ i = msE p₀ p₁ p₂ j →
      msEventuallyZero i → msEventuallyZero j → i k = j k := by
  intro k
  induction k with
  | zero =>
      intro i j hEq hi hj
      exact msE_eventuallyZero_head_eq hp₀ hp₁ hp₂ hsum hEq hi hj
  | succ k ih =>
      intro i j hEq hi hj
      exact ih (fun n ↦ i (n + 1)) (fun n ↦ j (n + 1))
        (msE_eventuallyZero_tail_eq hp₀ hp₁ hp₂ hsum hEq hi hj)
        hi.tail hj.tail

end

/- accepted add_to_file helper 9 -/
noncomputable section

def msDigit (p₀ p₁ : ℝ) (x : ℝ) : Fin 3 :=
  if x < p₀ then 0 else if x < p₀ + p₁ then 1 else 2

def msTail (p₀ p₁ p₂ : ℝ) (x : ℝ) : ℝ :=
  (x - msB p₀ p₁ p₂ (msDigit p₀ p₁ x)) /
    msP p₀ p₁ p₂ (msDigit p₀ p₁ x)

def msTailIter (p₀ p₁ p₂ : ℝ) : ℕ → ℝ → ℝ
  | 0, x => x
  | n + 1, x => msTailIter p₀ p₁ p₂ n (msTail p₀ p₁ p₂ x)

def msSeq (p₀ p₁ p₂ : ℝ) (x : ℝ) (n : ℕ) : Fin 3 :=
  msDigit p₀ p₁ (msTailIter p₀ p₁ p₂ n x)

lemma msSeq_zero (p₀ p₁ p₂ : ℝ) (x : ℝ) :
    msSeq p₀ p₁ p₂ x 0 = msDigit p₀ p₁ x := rfl

lemma msSeq_succ (p₀ p₁ p₂ : ℝ) (x : ℝ) (n : ℕ) :
    msSeq p₀ p₁ p₂ x (n + 1) = msSeq p₀ p₁ p₂ (msTail p₀ p₁ p₂ x) n := rfl

lemma msTailIter_succ (p₀ p₁ p₂ : ℝ) (x : ℝ) (n : ℕ) :
    msTailIter p₀ p₁ p₂ (n + 1) x =
      msTailIter p₀ p₁ p₂ n (msTail p₀ p₁ p₂ x) := rfl

lemma msTail_mem_Icc {p₀ p₁ p₂ x : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    msTail p₀ p₁ p₂ x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold msTail msDigit
  by_cases h0 : x < p₀
  · simp [h0, msB, msP]
    constructor
    · exact div_nonneg hx.1 hp₀.1.le
    · rw [div_le_one hp₀.1]
      exact h0.le
  · by_cases h1 : x < p₀ + p₁
    · simp [h0, h1, msB, msP]
      constructor
      · exact div_nonneg (sub_nonneg.mpr (le_of_not_gt h0)) hp₁.1.le
      · rw [div_le_one hp₁.1]
        linarith
    · simp [h0, h1, msB, msP]
      constructor
      · exact div_nonneg (sub_nonneg.mpr (le_of_not_gt h1)) hp₂.1.le
      · rw [div_le_one hp₂.1]
        have hx1 : x ≤ p₀ + p₁ + p₂ := by
          rw [hsum]
          exact hx.2
        linarith

lemma msTailIter_mem_Icc {p₀ p₁ p₂ x : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ n : ℕ, msTailIter p₀ p₁ p₂ n x ∈ Set.Icc (0 : ℝ) 1 := by
  intro n
  induction n generalizing x with
  | zero => exact hx
  | succ n ih =>
      exact ih (msTail_mem_Icc hp₀ hp₁ hp₂ hsum hx)

lemma ms_eq_beta_add_mul_tail {p₀ p₁ p₂ x : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1) :
    x = msB p₀ p₁ p₂ (msDigit p₀ p₁ x) +
      msP p₀ p₁ p₂ (msDigit p₀ p₁ x) * msTail p₀ p₁ p₂ x := by
  unfold msTail
  have hp : msP p₀ p₁ p₂ (msDigit p₀ p₁ x) ≠ 0 :=
    ne_of_gt (msP_pos hp₀ hp₁ hp₂ _)
  field_simp [hp]
  ring

end

/- accepted add_to_file helper 10 -/
noncomputable section

lemma ms_expansion {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) :
    ∀ n : ℕ, ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
      x = (∑ k ∈ Finset.range n,
          msB p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k) *
            ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x r)) +
        (∏ k ∈ Finset.range n, msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k)) *
          msTailIter p₀ p₁ p₂ n x := by
  intro n
  induction n with
  | zero =>
      intro x hx
      simp
      rfl
  | succ n ih =>
      intro x hx
      have htx : msTail p₀ p₁ p₂ x ∈ Set.Icc (0 : ℝ) 1 :=
        msTail_mem_Icc hp₀ hp₁ hp₂ hsum hx
      have htail := ih (msTail p₀ p₁ p₂ x) htx
      have hxeq := ms_eq_beta_add_mul_tail hp₀ hp₁ hp₂ (x := x)
      let S : ℝ := ∑ k ∈ Finset.range n,
        msB p₀ p₁ p₂ (msSeq p₀ p₁ p₂ (msTail p₀ p₁ p₂ x) k) *
          ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ (msTail p₀ p₁ p₂ x) r)
      let Q : ℝ := ∏ k ∈ Finset.range n,
        msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ (msTail p₀ p₁ p₂ x) k)
      have hsumshift :
          (∑ k ∈ Finset.range (n + 1),
            msB p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k) *
              ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x r)) =
            msB p₀ p₁ p₂ (msDigit p₀ p₁ x) +
              msP p₀ p₁ p₂ (msDigit p₀ p₁ x) * S := by
        dsimp [S]
        rw [msE_partial_succ (msSeq p₀ p₁ p₂ x) n]
        simp [msSeq_zero, msSeq_succ]
      have hprodshift :
          (∏ k ∈ Finset.range (n + 1),
            msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k)) =
            Q * msP p₀ p₁ p₂ (msDigit p₀ p₁ x) := by
        dsimp [Q]
        rw [Finset.prod_range_succ']
        simp [msSeq_zero, msSeq_succ]
      calc
        x = msB p₀ p₁ p₂ (msDigit p₀ p₁ x) +
            msP p₀ p₁ p₂ (msDigit p₀ p₁ x) * msTail p₀ p₁ p₂ x := hxeq
        _ = msB p₀ p₁ p₂ (msDigit p₀ p₁ x) +
            msP p₀ p₁ p₂ (msDigit p₀ p₁ x) *
              (S + Q * msTailIter p₀ p₁ p₂ n (msTail p₀ p₁ p₂ x)) := by
              dsimp [S, Q]
              nth_rewrite 1 [htail]
              rfl
        _ = (∑ k ∈ Finset.range (n + 1),
              msB p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k) *
                ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x r)) +
            (∏ k ∈ Finset.range (n + 1),
                msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k)) *
              msTailIter p₀ p₁ p₂ (n + 1) x := by
              rw [hsumshift, hprodshift]
              simp [msTailIter_succ]
              ring

end

/- accepted add_to_file helper 11 -/
noncomputable section

lemma msSeq_eval {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    msE p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x) = x := by
  let term : ℕ → ℝ := fun k ↦
    msB p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k) *
      ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x r)
  let rem : ℕ → ℝ := fun n ↦
    (∏ k ∈ Finset.range n, msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k)) *
      msTailIter p₀ p₁ p₂ n x
  let q := max p₀ (max p₁ p₂)
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact le_trans hp₀.1.le (le_max_left _ _)
  have hq_lt_one : q < 1 := by
    dsimp [q]
    exact max_lt hp₀.2 (max_lt hp₁.2 hp₂.2)
  have hp_le_q : ∀ n k : ℕ, k ∈ Finset.range n →
      msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k) ≤ q := by
    intro n k hk
    generalize hj : msSeq p₀ p₁ p₂ x k = j
    fin_cases j <;> simp [msP, q]
  have hrem_bound : ∀ n : ℕ, ‖rem n‖ ≤ q ^ n := by
    intro n
    have hprod_nonneg : 0 ≤ ∏ k ∈ Finset.range n,
        msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k) :=
      Finset.prod_nonneg fun k _ => msP_nonneg hp₀ hp₁ hp₂ _
    have hprod_le : (∏ k ∈ Finset.range n,
        msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k)) ≤ q ^ n := by
      calc
        (∏ k ∈ Finset.range n, msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k)) ≤
            ∏ k ∈ Finset.range n, q :=
          Finset.prod_le_prod
            (fun k _ => msP_nonneg hp₀ hp₁ hp₂ _)
            (fun k hk => hp_le_q n k hk)
        _ = q ^ n := by simp
    have hiter_abs : |msTailIter p₀ p₁ p₂ n x| ≤ 1 := by
      have hmem := msTailIter_mem_Icc hp₀ hp₁ hp₂ hsum hx n
      exact abs_le.mpr ⟨by linarith [hmem.1], hmem.2⟩
    calc
      ‖rem n‖ = |(∏ k ∈ Finset.range n,
          msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k)) *
        msTailIter p₀ p₁ p₂ n x| := by rfl
      _ = |(∏ k ∈ Finset.range n,
          msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k))| *
          |msTailIter p₀ p₁ p₂ n x| := abs_mul _ _
      _ = (∏ k ∈ Finset.range n,
          msP p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x k)) *
          |msTailIter p₀ p₁ p₂ n x| := by rw [abs_of_nonneg hprod_nonneg]
      _ ≤ q ^ n * 1 := mul_le_mul hprod_le hiter_abs (abs_nonneg _) (pow_nonneg hq_nonneg _)
      _ = q ^ n := by ring
  have hrem_tendsto : Filter.Tendsto rem Filter.atTop (nhds 0) :=
    squeeze_zero_norm hrem_bound (tendsto_pow_atTop_nhds_zero_of_lt_one hq_nonneg hq_lt_one)
  have hpartial_tendsto : Filter.Tendsto
      (fun n ↦ ∑ k ∈ Finset.range n, term k) Filter.atTop (nhds x) := by
    have hsub := (tendsto_const_nhds (x := x)).sub hrem_tendsto
    have hfun : (fun n ↦ ∑ k ∈ Finset.range n, term k) = fun n ↦ x - rem n := by
      funext n
      have hexp := ms_expansion hp₀ hp₁ hp₂ hsum n x hx
      dsimp [term, rem]
      linarith
    rw [hfun]
    simpa using hsub
  have hE_tendsto : Filter.Tendsto
      (fun n ↦ ∑ k ∈ Finset.range n, term k) Filter.atTop
      (nhds (msE p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x))) := by
    have hs := msE_summable hp₀ hp₁ hp₂ hsum (msSeq p₀ p₁ p₂ x)
    exact hs.hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique hE_tendsto hpartial_tendsto

end

/- accepted add_to_file helper 12 -/
noncomputable section

def msSuffix (i : ℕ → Fin 3) (k n : ℕ) : Fin 3 := i (k + n)

lemma msSuffix_zero (i : ℕ → Fin 3) : msSuffix i 0 = i := by
  funext n
  simp [msSuffix]

lemma msE_decompose {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) :
    ∀ k : ℕ, ∀ i : ℕ → Fin 3,
      msE p₀ p₁ p₂ i =
        (∑ r ∈ Finset.range k,
          msB p₀ p₁ p₂ (i r) * ∏ s ∈ Finset.range r, msP p₀ p₁ p₂ (i s)) +
        (∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i r)) *
          msE p₀ p₁ p₂ (msSuffix i k) := by
  intro k
  induction k with
  | zero =>
      intro i
      simp
      rw [msSuffix_zero]
  | succ k ih =>
      intro i
      have hrec := msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum i
      have htail := ih (fun n ↦ i (n + 1))
      have hsuffix : msSuffix (fun n ↦ i (n + 1)) k = msSuffix i (k + 1) := by
        funext n
        dsimp [msSuffix]
        congr 1
        omega
      rw [hrec, htail, hsuffix]
      rw [msE_partial_succ i k]
      rw [Finset.prod_range_succ']
      ring

end

/- accepted add_to_file helper 13 -/
noncomputable section

lemma msE_suffix_eq_of_prefix {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) {i j : ℕ → Fin 3} {k : ℕ}
    (hEq : msE p₀ p₁ p₂ i = msE p₀ p₁ p₂ j)
    (hprefix : ∀ r : ℕ, r < k → i r = j r) :
    msE p₀ p₁ p₂ (msSuffix i k) = msE p₀ p₁ p₂ (msSuffix j k) := by
  have hpartial :
      (∑ r ∈ Finset.range k,
        msB p₀ p₁ p₂ (i r) * ∏ s ∈ Finset.range r, msP p₀ p₁ p₂ (i s)) =
      ∑ r ∈ Finset.range k,
        msB p₀ p₁ p₂ (j r) * ∏ s ∈ Finset.range r, msP p₀ p₁ p₂ (j s) := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    have hrr : r < k := Finset.mem_range.mp hr
    have hprod_inner :
        (∏ s ∈ Finset.range r, msP p₀ p₁ p₂ (i s)) =
          ∏ s ∈ Finset.range r, msP p₀ p₁ p₂ (j s) := by
      refine Finset.prod_congr rfl ?_
      intro s hs
      exact congrArg (msP p₀ p₁ p₂)
        (hprefix s (lt_trans (Finset.mem_range.mp hs) hrr))
    rw [hprefix r hrr, hprod_inner]
  have hprod :
      (∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (i r)) =
        ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (j r) := by
    refine Finset.prod_congr rfl ?_
    intro r hr
    exact congrArg (msP p₀ p₁ p₂) (hprefix r (Finset.mem_range.mp hr))
  have hdec_i := msE_decompose hp₀ hp₁ hp₂ hsum k i
  have hdec_j := msE_decompose hp₀ hp₁ hp₂ hsum k j
  have hdec_i' :
      msE p₀ p₁ p₂ i =
        (∑ r ∈ Finset.range k,
          msB p₀ p₁ p₂ (j r) * ∏ s ∈ Finset.range r, msP p₀ p₁ p₂ (j s)) +
        (∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (j r)) *
          msE p₀ p₁ p₂ (msSuffix i k) := by
    rw [hdec_i, hpartial, hprod]
  have hPpos : 0 < ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (j r) :=
    Finset.prod_pos fun r _ => msP_pos hp₀ hp₁ hp₂ _
  have hmul :
      (∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (j r)) *
          msE p₀ p₁ p₂ (msSuffix i k) =
        (∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (j r)) *
          msE p₀ p₁ p₂ (msSuffix j k) := by
    linarith
  exact mul_left_cancel₀ (ne_of_gt hPpos) hmul

end

/- accepted add_to_file helper 14 -/
noncomputable section

lemma msTailIter_add (p₀ p₁ p₂ : ℝ) (k n : ℕ) (x : ℝ) :
    msTailIter p₀ p₁ p₂ (k + n) x =
      msTailIter p₀ p₁ p₂ n (msTailIter p₀ p₁ p₂ k x) := by
  induction k generalizing x with
  | zero =>
      simp [msTailIter]
  | succ k ih =>
      calc
        msTailIter p₀ p₁ p₂ (k + 1 + n) x
            = msTailIter p₀ p₁ p₂ (k + n + 1) x := by rw [Nat.succ_add]
        _ = msTailIter p₀ p₁ p₂ (k + n) (msTail p₀ p₁ p₂ x) := rfl
        _ = msTailIter p₀ p₁ p₂ n
              (msTailIter p₀ p₁ p₂ k (msTail p₀ p₁ p₂ x)) := ih _
        _ = msTailIter p₀ p₁ p₂ n
              (msTailIter p₀ p₁ p₂ (k + 1) x) := rfl

lemma msDigit_eq_zero_imp_lt {p₀ p₁ x : ℝ}
    (h : msDigit p₀ p₁ x = 0) : x < p₀ := by
  unfold msDigit at h
  by_cases h0 : x < p₀
  · exact h0
  · by_cases h1 : x < p₀ + p₁
    · simp [h0, h1] at h
    · simp [h0, h1] at h

lemma msDigit_eq_one_imp {p₀ p₁ x : ℝ}
    (h : msDigit p₀ p₁ x = 1) : p₀ ≤ x ∧ x < p₀ + p₁ := by
  unfold msDigit at h
  by_cases h0 : x < p₀
  · simp [h0] at h
  · by_cases h1 : x < p₀ + p₁
    · exact ⟨le_of_not_gt h0, h1⟩
    · simp [h0, h1] at h

lemma msDigit_eq_two_imp {p₀ p₁ x : ℝ}
    (h : msDigit p₀ p₁ x = 2) : p₀ + p₁ ≤ x := by
  unfold msDigit at h
  by_cases h0 : x < p₀
  · simp [h0] at h
  · by_cases h1 : x < p₀ + p₁
    · simp [h0, h1] at h
    · exact le_of_not_gt h1

end

/- accepted add_to_file helper 15 -/
noncomputable section

lemma msSeq_eventuallyZero_of_head_ne {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) {a b : ℕ → Fin 3} {y : ℝ}
    (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (hb : b = msSeq p₀ p₁ p₂ y)
    (hEq : msE p₀ p₁ p₂ a = msE p₀ p₁ p₂ b)
    (hne : a 0 ≠ b 0) :
    msEventuallyZero b := by
  have hEb : msE p₀ p₁ p₂ b = y := by
    rw [hb]
    exact msSeq_eval hp₀ hp₁ hp₂ hsum hy
  have hb0 : b 0 = msDigit p₀ p₁ y := by
    rw [hb]
    rfl
  generalize ha0 : a 0 = A
  generalize hb0v : b 0 = B
  fin_cases B <;> fin_cases A
  · exact False.elim (hne (by rw [ha0, hb0v]))
  · have hdigit : msDigit p₀ p₁ y = 0 := by
      rw [← hb0]
      exact hb0v
    have hyb := msDigit_eq_zero_imp_lt hdigit
    have ha_lower : p₀ ≤ msE p₀ p₁ p₂ a := by
      have h := msE_head_lower hp₀ hp₁ hp₂ hsum a
      rw [ha0] at h
      simpa [msB, msP] using h
    have ha_y : msE p₀ p₁ p₂ a = y := by rw [hEq, hEb]
    linarith
  · have hdigit : msDigit p₀ p₁ y = 0 := by
      rw [← hb0]
      exact hb0v
    have hyb := msDigit_eq_zero_imp_lt hdigit
    have ha_lower : p₀ + p₁ ≤ msE p₀ p₁ p₂ a := by
      have h := msE_head_lower hp₀ hp₁ hp₂ hsum a
      rw [ha0] at h
      simpa [msB, msP] using h
    have ha_y : msE p₀ p₁ p₂ a = y := by rw [hEq, hEb]
    linarith [hp₁.1]
  · have hdigit : msDigit p₀ p₁ y = 1 := by
      rw [← hb0]
      exact hb0v
    have hyb := msDigit_eq_one_imp hdigit
    have ha_upper : msE p₀ p₁ p₂ a ≤ p₀ := by
      have h := msE_head_upper hp₀ hp₁ hp₂ hsum a
      rw [ha0] at h
      simpa [msB, msP] using h
    have hy_eq : y = p₀ := by
      have ha_y : msE p₀ p₁ p₂ a = y := by rw [hEq, hEb]
      linarith [hyb.1]
    have hb_eq : msE p₀ p₁ p₂ b = p₀ := by rw [hEb, hy_eq]
    have hbrec := msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum b
    rw [hb0v] at hbrec
    simp [msB, msP] at hbrec
    rw [hb_eq] at hbrec
    have htail_zero : msE p₀ p₁ p₂ (fun k ↦ b (k + 1)) = 0 := by
      have hmul : p₁ * msE p₀ p₁ p₂ (fun k ↦ b (k + 1)) = 0 := by
        linarith
      rcases mul_eq_zero.mp hmul with hp | ht
      · linarith [hp₁.1]
      · exact ht
    refine ⟨1, ?_⟩
    intro n hn
    cases n with
    | zero => omega
    | succ m =>
        exact msE_eq_zero_apply hp₀ hp₁ hp₂ hsum m
          (fun k ↦ b (k + 1)) htail_zero
  · exact False.elim (hne (by rw [ha0, hb0v]))
  · have hdigit : msDigit p₀ p₁ y = 1 := by
      rw [← hb0]
      exact hb0v
    have hyb := msDigit_eq_one_imp hdigit
    have ha_lower : p₀ + p₁ ≤ msE p₀ p₁ p₂ a := by
      have h := msE_head_lower hp₀ hp₁ hp₂ hsum a
      rw [ha0] at h
      simpa [msB, msP] using h
    have ha_y : msE p₀ p₁ p₂ a = y := by rw [hEq, hEb]
    linarith
  · have hdigit : msDigit p₀ p₁ y = 2 := by
      rw [← hb0]
      exact hb0v
    have hyb := msDigit_eq_two_imp hdigit
    have ha_upper : msE p₀ p₁ p₂ a ≤ p₀ := by
      have h := msE_head_upper hp₀ hp₁ hp₂ hsum a
      rw [ha0] at h
      simpa [msB, msP] using h
    have ha_y : msE p₀ p₁ p₂ a = y := by rw [hEq, hEb]
    linarith [hp₁.1]
  · have hdigit : msDigit p₀ p₁ y = 2 := by
      rw [← hb0]
      exact hb0v
    have hyb := msDigit_eq_two_imp hdigit
    have ha_upper : msE p₀ p₁ p₂ a ≤ p₀ + p₁ := by
      have h := msE_head_upper hp₀ hp₁ hp₂ hsum a
      rw [ha0] at h
      simpa [msB, msP] using h
    have hy_eq : y = p₀ + p₁ := by
      have ha_y : msE p₀ p₁ p₂ a = y := by rw [hEq, hEb]
      linarith [hyb]
    have hb_eq : msE p₀ p₁ p₂ b = p₀ + p₁ := by rw [hEb, hy_eq]
    have hbrec := msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum b
    rw [hb0v] at hbrec
    simp [msB, msP] at hbrec
    rw [hb_eq] at hbrec
    have htail_zero : msE p₀ p₁ p₂ (fun k ↦ b (k + 1)) = 0 := by
      have hmul : p₂ * msE p₀ p₁ p₂ (fun k ↦ b (k + 1)) = 0 := by
        linarith
      rcases mul_eq_zero.mp hmul with hp | ht
      · linarith [hp₂.1]
      · exact ht
    refine ⟨1, ?_⟩
    intro n hn
    cases n with
    | zero => omega
    | succ m =>
        exact msE_eq_zero_apply hp₀ hp₁ hp₂ hsum m
          (fun k ↦ b (k + 1)) htail_zero
  · exact False.elim (hne (by rw [ha0, hb0v]))

end

/- accepted add_to_file helper 16 -/
noncomputable section

lemma msSeq_eventuallyZero_of_exists_ne {p₀ p₁ p₂ x : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    {j : ℕ → Fin 3} (hj : msE p₀ p₁ p₂ j = x)
    (hne : j ≠ msSeq p₀ p₁ p₂ x) :
    msEventuallyZero (msSeq p₀ p₁ p₂ x) := by
  let s : ℕ → Fin 3 := msSeq p₀ p₁ p₂ x
  have hs : msE p₀ p₁ p₂ s = x := msSeq_eval hp₀ hp₁ hp₂ hsum hx
  have hex : ∃ k : ℕ, j k ≠ s k := by
    by_contra hnone
    apply hne
    funext k
    by_contra hk
    exact hnone ⟨k, hk⟩
  let k : ℕ := Nat.find hex
  have hk_ne : j k ≠ s k := Nat.find_spec hex
  have hprefix : ∀ r : ℕ, r < k → j r = s r := by
    intro r hr
    have hnot := Nat.find_min hex hr
    by_contra hdiff
    exact hnot hdiff
  have hEq : msE p₀ p₁ p₂ j = msE p₀ p₁ p₂ s := by rw [hj, hs]
  have hsuffix_E :
      msE p₀ p₁ p₂ (msSuffix j k) = msE p₀ p₁ p₂ (msSuffix s k) :=
    msE_suffix_eq_of_prefix hp₀ hp₁ hp₂ hsum hEq hprefix
  let y : ℝ := msTailIter p₀ p₁ p₂ k x
  have hy : y ∈ Set.Icc (0 : ℝ) 1 :=
    msTailIter_mem_Icc hp₀ hp₁ hp₂ hsum hx k
  have hb : msSuffix s k = msSeq p₀ p₁ p₂ y := by
    funext n
    dsimp [msSuffix, s, msSeq, y]
    rw [msTailIter_add]
  have hhead_ne : msSuffix j k 0 ≠ msSuffix s k 0 := by
    dsimp [msSuffix]
    simpa using hk_ne
  have hsuffix_zero := msSeq_eventuallyZero_of_head_ne hp₀ hp₁ hp₂ hsum hy hb
    hsuffix_E hhead_ne
  rcases hsuffix_zero with ⟨N, hN⟩
  refine ⟨k + N, ?_⟩
  intro m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  have h := hN (N + d) (Nat.le_add_right N d)
  dsimp [msSuffix, s] at h
  simpa [Nat.add_assoc] using h

end

/- accepted add_to_file helper 17 -/
noncomputable section

def msCanonical (p₀ p₁ p₂ : ℝ) (x : ℝ) : ℕ → Fin 3 :=
  Classical.epsilon fun i ↦
    msE p₀ p₁ p₂ i = x ∧
      ((∃ j, msE p₀ p₁ p₂ j = x ∧ j ≠ i) → msEventuallyZero i)

lemma msCanonical_spec {p₀ p₁ p₂ x : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    msE p₀ p₁ p₂ (msCanonical p₀ p₁ p₂ x) = x ∧
      ((∃ j, msE p₀ p₁ p₂ j = x ∧ j ≠ msCanonical p₀ p₁ p₂ x) →
        msEventuallyZero (msCanonical p₀ p₁ p₂ x)) := by
  dsimp [msCanonical]
  let P : (ℕ → Fin 3) → Prop := fun i ↦
    msE p₀ p₁ p₂ i = x ∧
      ((∃ j, msE p₀ p₁ p₂ j = x ∧ j ≠ i) → msEventuallyZero i)
  have hex : ∃ i, P i := by
    refine ⟨msSeq p₀ p₁ p₂ x, msSeq_eval hp₀ hp₁ hp₂ hsum hx, ?_⟩
    rintro ⟨j, hj, hjne⟩
    exact msSeq_eventuallyZero_of_exists_ne hp₀ hp₁ hp₂ hsum hx hj hjne
  have h := Classical.epsilon_spec (p := P) hex
  dsimp [P] at h
  exact h

lemma msCanonical_eq_msSeq {p₀ p₁ p₂ x : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    msCanonical p₀ p₁ p₂ x = msSeq p₀ p₁ p₂ x := by
  have hc := msCanonical_spec hp₀ hp₁ hp₂ hsum hx
  have hs : msE p₀ p₁ p₂ (msSeq p₀ p₁ p₂ x) = x :=
    msSeq_eval hp₀ hp₁ hp₂ hsum hx
  by_contra hne
  have hsc : msSeq p₀ p₁ p₂ x ≠ msCanonical p₀ p₁ p₂ x := by
    intro h
    exact hne h.symm
  have hc_zero : msEventuallyZero (msCanonical p₀ p₁ p₂ x) :=
    hc.2 ⟨msSeq p₀ p₁ p₂ x, hs, hsc⟩
  have hs_zero : msEventuallyZero (msSeq p₀ p₁ p₂ x) :=
    msSeq_eventuallyZero_of_exists_ne hp₀ hp₁ hp₂ hsum hx hc.1 hne
  have hcoords : ∀ k : ℕ,
      msCanonical p₀ p₁ p₂ x k = msSeq p₀ p₁ p₂ x k := by
    intro k
    exact msE_eventuallyZero_injective hp₀ hp₁ hp₂ hsum k
      (msCanonical p₀ p₁ p₂ x) (msSeq p₀ p₁ p₂ x)
      (by rw [hc.1, hs]) hc_zero hs_zero
  exact hne (funext hcoords)

end

/- accepted add_to_file helper 18 -/
noncomputable section

lemma measurable_msDigit (p₀ p₁ : ℝ) : Measurable (msDigit p₀ p₁) := by
  unfold msDigit
  refine Measurable.piecewise
    (measurableSet_lt measurable_id measurable_const) measurable_const ?_
  exact Measurable.piecewise
    (measurableSet_lt measurable_id measurable_const) measurable_const measurable_const

lemma measurable_msTail (p₀ p₁ p₂ : ℝ) : Measurable (msTail p₀ p₁ p₂) := by
  have hd := measurable_msDigit p₀ p₁
  have hB : Measurable fun x ↦ msB p₀ p₁ p₂ (msDigit p₀ p₁ x) :=
    (measurable_of_finite (msB p₀ p₁ p₂)).comp hd
  have hP : Measurable fun x ↦ msP p₀ p₁ p₂ (msDigit p₀ p₁ x) :=
    (measurable_of_finite (msP p₀ p₁ p₂)).comp hd
  exact (measurable_id.sub hB).div hP

lemma measurable_msTailIter (p₀ p₁ p₂ : ℝ) (n : ℕ) :
    Measurable fun x ↦ msTailIter p₀ p₁ p₂ n x := by
  induction n with
  | zero =>
      simpa [msTailIter] using measurable_id
  | succ n ih =>
      simpa [msTailIter] using ih.comp (measurable_msTail p₀ p₁ p₂)

lemma measurable_msSeq (p₀ p₁ p₂ : ℝ) (n : ℕ) :
    Measurable fun x ↦ msSeq p₀ p₁ p₂ x n := by
  unfold msSeq
  exact (measurable_msDigit p₀ p₁).comp (measurable_msTailIter p₀ p₁ p₂ n)

def msG (p₀ p₁ p₂ : ℝ) (x : ℝ) : ℝ :=
  msE p₀ p₁ p₂ (fun k ↦ msTheta (msSeq p₀ p₁ p₂ x k))

lemma measurable_msG {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) : Measurable (msG p₀ p₁ p₂) := by
  let term : ℕ → ℝ → ℝ := fun k x ↦
    msB p₀ p₁ p₂ (msTheta (msSeq p₀ p₁ p₂ x k)) *
      ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (msTheta (msSeq p₀ p₁ p₂ x r))
  have hterm : ∀ k : ℕ, Measurable (term k) := by
    intro k
    have hB : Measurable fun x ↦
        msB p₀ p₁ p₂ (msTheta (msSeq p₀ p₁ p₂ x k)) := by
      exact (measurable_of_finite (fun j ↦ msB p₀ p₁ p₂ (msTheta j))).comp
        (measurable_msSeq p₀ p₁ p₂ k)
    have hP : Measurable fun x ↦
        ∏ r ∈ Finset.range k, msP p₀ p₁ p₂ (msTheta (msSeq p₀ p₁ p₂ x r)) := by
      refine Finset.measurable_prod (Finset.range k) ?_
      intro r hr
      exact (measurable_of_finite (fun j ↦ msP p₀ p₁ p₂ (msTheta j))).comp
        (measurable_msSeq p₀ p₁ p₂ r)
    exact hB.mul hP
  have hpartial : ∀ n : ℕ,
      Measurable fun x ↦ ∑ k ∈ Finset.range n, term k x := by
    intro n
    exact Finset.measurable_sum (Finset.range n) fun k _ => hterm k
  have hlim : Filter.Tendsto
      (fun n x ↦ ∑ k ∈ Finset.range n, term k x) Filter.atTop
      (nhds (msG p₀ p₁ p₂)) := by
    rw [tendsto_pi_nhds]
    intro x
    have hs : Summable fun k ↦ term k x := by
      dsimp [term]
      exact msE_summable hp₀ hp₁ hp₂ hsum
        (fun k ↦ msTheta (msSeq p₀ p₁ p₂ x k))
    have h := hs.hasSum.tendsto_sum_nat
    dsimp [msG, msE, term]
    exact h
  exact measurable_of_tendsto_metrizable hpartial hlim

end

/- accepted add_to_file helper 19 -/
noncomputable section

lemma msDigit_map0 {p₀ p₁ y : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1) (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    msDigit p₀ p₁ (p₀ * y) = 0 := by
  unfold msDigit
  rw [if_pos (mul_lt_of_lt_one_right hp₀.1 hy.2)]

lemma msTail_map0 {p₀ p₁ p₂ y : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1) (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    msTail p₀ p₁ p₂ (p₀ * y) = y := by
  unfold msTail
  rw [msDigit_map0 hp₀ hy]
  simp [msB, msP]
  field_simp [ne_of_gt hp₀.1]

lemma msDigit_map1 {p₀ p₁ y : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1) (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    msDigit p₀ p₁ (p₀ + p₁ * y) = 1 := by
  have hnot0 : ¬ p₀ + p₁ * y < p₀ := by
    have hnonneg : 0 ≤ p₁ * y := mul_nonneg hp₁.1.le hy.1
    linarith
  have hlt : p₀ + p₁ * y < p₀ + p₁ := by
    have h := mul_lt_of_lt_one_right hp₁.1 hy.2
    linarith
  unfold msDigit
  rw [if_neg hnot0, if_pos hlt]

lemma msTail_map1 {p₀ p₁ p₂ y : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1) (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    msTail p₀ p₁ p₂ (p₀ + p₁ * y) = y := by
  unfold msTail
  rw [msDigit_map1 hp₀ hp₁ hy]
  simp [msB, msP]
  field_simp [ne_of_gt hp₁.1]

lemma msDigit_map2 {p₀ p₁ p₂ y : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    msDigit p₀ p₁ (p₀ + p₁ + p₂ * y) = 2 := by
  have hnot0 : ¬ p₀ + p₁ + p₂ * y < p₀ := by
    have h : p₁ ≤ p₁ + p₂ * y := by
      have hnonneg : 0 ≤ p₂ * y := mul_nonneg hp₂.1.le hy.1
      linarith
    linarith [hp₁.1]
  have hnot1 : ¬ p₀ + p₁ + p₂ * y < p₀ + p₁ := by
    have hnonneg : 0 ≤ p₂ * y := mul_nonneg hp₂.1.le hy.1
    linarith
  unfold msDigit
  rw [if_neg hnot0, if_neg hnot1]

lemma msTail_map2 {p₀ p₁ p₂ y : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    msTail p₀ p₁ p₂ (p₀ + p₁ + p₂ * y) = y := by
  unfold msTail
  rw [msDigit_map2 hp₀ hp₁ hp₂ hsum hy]
  simp [msB, msP]
  field_simp [ne_of_gt hp₂.1]

end

/- accepted add_to_file helper 20 -/
noncomputable section

lemma msG_eq_of_digit_tail {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) {x y : ℝ} {a : Fin 3}
    (hdigit : msDigit p₀ p₁ x = a)
    (htail : msTail p₀ p₁ p₂ x = y) :
    msG p₀ p₁ p₂ x =
      msB p₀ p₁ p₂ (msTheta a) +
        msP p₀ p₁ p₂ (msTheta a) * msG p₀ p₁ p₂ y := by
  unfold msG
  have hrec := msE_eq_beta_add_mul_tail hp₀ hp₁ hp₂ hsum
    (fun k ↦ msTheta (msSeq p₀ p₁ p₂ x k))
  have htailseq :
      (fun k ↦ msTheta (msSeq p₀ p₁ p₂ x (k + 1))) =
        fun k ↦ msTheta (msSeq p₀ p₁ p₂ y k) := by
    funext k
    rw [msSeq_succ, htail]
  have hhead : msSeq p₀ p₁ p₂ x 0 = a := by
    rw [msSeq_zero, hdigit]
  rw [hrec, hhead, htailseq]

lemma msG_map0 {p₀ p₁ p₂ y : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    msG p₀ p₁ p₂ (p₀ * y) = p₀ * msG p₀ p₁ p₂ y := by
  have h := msG_eq_of_digit_tail hp₀ hp₁ hp₂ hsum
    (msDigit_map0 hp₀ hy) (msTail_map0 hp₀ hy)
  simpa [msTheta, msB, msP] using h

lemma msG_map1 {p₀ p₁ p₂ y : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    msG p₀ p₁ p₂ (p₀ + p₁ * y) =
      p₀ + p₁ + p₂ * msG p₀ p₁ p₂ y := by
  have h := msG_eq_of_digit_tail hp₀ hp₁ hp₂ hsum
    (msDigit_map1 hp₀ hp₁ hy) (msTail_map1 hp₀ hp₁ hy)
  simpa [msTheta, msB, msP] using h

lemma msG_map2 {p₀ p₁ p₂ y : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    msG p₀ p₁ p₂ (p₀ + p₁ + p₂ * y) =
      p₀ + p₁ * msG p₀ p₁ p₂ y := by
  have h := msG_eq_of_digit_tail hp₀ hp₁ hp₂ hsum
    (msDigit_map2 hp₀ hp₁ hp₂ hsum hy) (msTail_map2 hp₀ hp₁ hp₂ hsum hy)
  simpa [msTheta, msB, msP] using h

end

/- accepted add_to_file helper 21 -/
noncomputable section

lemma msG_mem_Icc {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (x : ℝ) :
    msG p₀ p₁ p₂ x ∈ Set.Icc (0 : ℝ) 1 := by
  unfold msG
  exact msE_mem_Icc hp₀ hp₁ hp₂ hsum _

end

/- accepted add_to_file helper 22 -/
noncomputable section

lemma msG_integrableOn_Icc {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) (a b : ℝ) :
    MeasureTheory.IntegrableOn (msG p₀ p₁ p₂) (Set.Icc a b) MeasureTheory.volume := by
  have hmeas : MeasureTheory.AEStronglyMeasurable (msG p₀ p₁ p₂)
      (MeasureTheory.volume.restrict (Set.Icc a b)) :=
    (measurable_msG hp₀ hp₁ hp₂ hsum).aestronglyMeasurable
  have hbound : ∀ᵐ (x : ℝ) ∂(MeasureTheory.volume.restrict (Set.Icc a b)),
      ‖msG p₀ p₁ p₂ x‖ ≤ 1 := by
    refine Filter.Eventually.of_forall fun x ↦ ?_
    have hmem := msG_mem_Icc hp₀ hp₁ hp₂ hsum x
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hmem.1], hmem.2⟩
  exact MeasureTheory.IntegrableOn.of_bound measure_Icc_lt_top hmeas 1 hbound

end

/- accepted add_to_file helper 23 -/
noncomputable section

lemma msG_intervalIntegrable {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (msG p₀ p₁ p₂) MeasureTheory.volume a b := by
  unfold IntervalIntegrable
  constructor
  · exact (msG_integrableOn_Icc hp₀ hp₁ hp₂ hsum a b).mono_set
      Set.Ioc_subset_Icc_self
  · rw [Set.Ioc_eq_empty (not_lt.mpr hab)]
    exact MeasureTheory.integrableOn_empty

end

/- accepted add_to_file helper 24 -/
noncomputable section

lemma msG_integral_segment0 {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) :
    (∫ x in (0 : ℝ)..p₀, msG p₀ p₁ p₂ x) =
      p₀ ^ 2 * ∫ x in (0 : ℝ)..1, msG p₀ p₁ p₂ x := by
  let g := msG p₀ p₁ p₂
  let I0 := ∫ x in (0 : ℝ)..p₀, g x
  let J := ∫ x in (0 : ℝ)..1, g x
  have hcongr : (∫ y in (0 : ℝ)..1, g (p₀ * y)) = p₀ * J := by
    have hae : ∀ᵐ y ∂MeasureTheory.volume,
        y ∈ Set.uIoc (0 : ℝ) 1 → g (p₀ * y) = p₀ * g y := by
      rw [MeasureTheory.ae_iff]
      apply MeasureTheory.measure_mono_null ?_ (Real.volume_singleton (a := (1 : ℝ)))
      intro y hybad
      by_contra hyne
      have hcond : y ∈ Set.uIoc (0 : ℝ) 1 → g (p₀ * y) = p₀ * g y := by
        intro hy
        have hyIoc : y ∈ Set.Ioc (0 : ℝ) 1 := by
          simpa [Set.uIoc_of_le zero_le_one] using hy
        have hyIco : y ∈ Set.Ico (0 : ℝ) 1 :=
          ⟨hyIoc.1.le, lt_of_le_of_ne hyIoc.2 hyne⟩
        exact msG_map0 hp₀ hp₁ hp₂ hsum hyIco
      exact hybad hcond
    have h := intervalIntegral.integral_congr_ae hae
    calc
      (∫ y in (0 : ℝ)..1, g (p₀ * y)) =
          ∫ y in (0 : ℝ)..1, p₀ * g y := h
      _ = p₀ * J := by
          dsimp [J]
          exact intervalIntegral.integral_const_mul p₀ g
  have hsubst : (∫ y in (0 : ℝ)..1, g (p₀ * y)) = p₀⁻¹ * I0 := by
    have h := intervalIntegral.integral_comp_mul_left
      (a := (0 : ℝ)) (b := (1 : ℝ)) (c := p₀) g (ne_of_gt hp₀.1)
    dsimp [I0]
    simpa using h
  have hpne : p₀ ≠ 0 := ne_of_gt hp₀.1
  have hcalc : p₀⁻¹ * I0 = p₀ * J := by
    rw [← hsubst, hcongr]
  calc
    (∫ x in (0 : ℝ)..p₀, msG p₀ p₁ p₂ x) = I0 := rfl
    _ = p₀ * (p₀⁻¹ * I0) := by field_simp [hpne]
    _ = p₀ * (p₀ * J) := by rw [hcalc]
    _ = p₀ ^ 2 * ∫ x in (0 : ℝ)..1, msG p₀ p₁ p₂ x := by
        dsimp [J, g]
        ring

end

/- accepted add_to_file helper 25 -/
noncomputable section

lemma msG_integral_segment1 {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) :
    (∫ x in p₀..(p₀ + p₁), msG p₀ p₁ p₂ x) =
      p₁ * (p₀ + p₁ + p₂ * ∫ x in (0 : ℝ)..1, msG p₀ p₁ p₂ x) := by
  let g := msG p₀ p₁ p₂
  let I1 := ∫ x in p₀..(p₀ + p₁), g x
  let J := ∫ x in (0 : ℝ)..1, g x
  have hcongr : (∫ y in (0 : ℝ)..1, g (p₀ + p₁ * y)) =
      p₀ + p₁ + p₂ * J := by
    have hae : ∀ᵐ y ∂MeasureTheory.volume,
        y ∈ Set.uIoc (0 : ℝ) 1 →
          g (p₀ + p₁ * y) = p₀ + p₁ + p₂ * g y := by
      rw [MeasureTheory.ae_iff]
      apply MeasureTheory.measure_mono_null ?_ (Real.volume_singleton (a := (1 : ℝ)))
      intro y hybad
      by_contra hyne
      have hcond : y ∈ Set.uIoc (0 : ℝ) 1 →
          g (p₀ + p₁ * y) = p₀ + p₁ + p₂ * g y := by
        intro hy
        have hyIoc : y ∈ Set.Ioc (0 : ℝ) 1 := by
          simpa [Set.uIoc_of_le zero_le_one] using hy
        have hyIco : y ∈ Set.Ico (0 : ℝ) 1 :=
          ⟨hyIoc.1.le, lt_of_le_of_ne hyIoc.2 hyne⟩
        exact msG_map1 hp₀ hp₁ hp₂ hsum hyIco
      exact hybad hcond
    have h := intervalIntegral.integral_congr_ae hae
    have hgint := msG_intervalIntegrable hp₀ hp₁ hp₂ hsum (a := (0 : ℝ)) (b := 1)
      zero_le_one
    calc
      (∫ y in (0 : ℝ)..1, g (p₀ + p₁ * y)) =
          ∫ y in (0 : ℝ)..1, (fun _ ↦ p₀ + p₁) y + p₂ * g y := h
      _ = (∫ y in (0 : ℝ)..1, (fun _ ↦ p₀ + p₁) y) +
          ∫ y in (0 : ℝ)..1, p₂ * g y :=
        intervalIntegral.integral_add intervalIntegrable_const (hgint.const_mul p₂)
      _ = p₀ + p₁ + p₂ * J := by
        rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
        dsimp [J]
        simp
  have hsubst : (∫ y in (0 : ℝ)..1, g (p₀ + p₁ * y)) = p₁⁻¹ * I1 := by
    have hmul := intervalIntegral.integral_comp_mul_left
      (a := (0 : ℝ)) (b := (1 : ℝ)) (c := p₁)
      (fun z ↦ g (p₀ + z)) (ne_of_gt hp₁.1)
    have hshift : (∫ z in (0 : ℝ)..p₁, g (p₀ + z)) = I1 := by
      have h := intervalIntegral.integral_comp_add_right
        (a := (0 : ℝ)) (b := p₁) g p₀
      dsimp [I1]
      simpa [add_comm] using h
    calc
      (∫ y in (0 : ℝ)..1, g (p₀ + p₁ * y)) =
          p₁⁻¹ * ∫ z in p₁ * (0 : ℝ)..p₁ * (1 : ℝ), g (p₀ + z) := by
            simpa using hmul
      _ = p₁⁻¹ * I1 := by
            simp [hshift]
  have hpne : p₁ ≠ 0 := ne_of_gt hp₁.1
  have hcalc : p₁⁻¹ * I1 = p₀ + p₁ + p₂ * J := by
    rw [← hsubst, hcongr]
  calc
    (∫ x in p₀..(p₀ + p₁), msG p₀ p₁ p₂ x) = I1 := rfl
    _ = p₁ * (p₁⁻¹ * I1) := by field_simp [hpne]
    _ = p₁ * (p₀ + p₁ + p₂ * J) := by rw [hcalc]
    _ = p₁ * (p₀ + p₁ + p₂ * ∫ x in (0 : ℝ)..1, msG p₀ p₁ p₂ x) := by
        dsimp [J, g]

end

/- accepted add_to_file helper 26 -/
noncomputable section

lemma msG_integral_segment2 {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) :
    (∫ x in (p₀ + p₁)..1, msG p₀ p₁ p₂ x) =
      p₂ * (p₀ + p₁ * ∫ x in (0 : ℝ)..1, msG p₀ p₁ p₂ x) := by
  let g := msG p₀ p₁ p₂
  let I2 := ∫ x in (p₀ + p₁)..1, g x
  let J := ∫ x in (0 : ℝ)..1, g x
  have hcongr : (∫ y in (0 : ℝ)..1, g (p₀ + p₁ + p₂ * y)) =
      p₀ + p₁ * J := by
    have hae : ∀ᵐ y ∂MeasureTheory.volume,
        y ∈ Set.uIoc (0 : ℝ) 1 →
          g (p₀ + p₁ + p₂ * y) = p₀ + p₁ * g y := by
      exact Filter.Eventually.of_forall fun y hy ↦ by
        have hyIoc : y ∈ Set.Ioc (0 : ℝ) 1 := by
          simpa [Set.uIoc_of_le zero_le_one] using hy
        exact msG_map2 hp₀ hp₁ hp₂ hsum ⟨hyIoc.1.le, hyIoc.2⟩
    have h := intervalIntegral.integral_congr_ae hae
    have hgint := msG_intervalIntegrable hp₀ hp₁ hp₂ hsum (a := (0 : ℝ)) (b := 1)
      zero_le_one
    calc
      (∫ y in (0 : ℝ)..1, g (p₀ + p₁ + p₂ * y)) =
          ∫ y in (0 : ℝ)..1, (fun _ ↦ p₀) y + p₁ * g y := h
      _ = (∫ y in (0 : ℝ)..1, (fun _ ↦ p₀) y) +
          ∫ y in (0 : ℝ)..1, p₁ * g y :=
        intervalIntegral.integral_add intervalIntegrable_const (hgint.const_mul p₁)
      _ = p₀ + p₁ * J := by
        rw [intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
        dsimp [J]
        simp
  have hsubst : (∫ y in (0 : ℝ)..1, g (p₀ + p₁ + p₂ * y)) = p₂⁻¹ * I2 := by
    have hmul := intervalIntegral.integral_comp_mul_left
      (a := (0 : ℝ)) (b := (1 : ℝ)) (c := p₂)
      (fun z ↦ g (p₀ + p₁ + z)) (ne_of_gt hp₂.1)
    have hshift : (∫ z in (0 : ℝ)..p₂, g (p₀ + p₁ + z)) = I2 := by
      have h := intervalIntegral.integral_comp_add_right
        (a := (0 : ℝ)) (b := p₂) g (p₀ + p₁)
      dsimp [I2]
      rw [add_comm p₂ (p₀ + p₁)] at h
      have hone : p₀ + p₁ + p₂ = 1 := hsum
      simpa [hone, add_comm, add_left_comm, add_assoc] using h
    calc
      (∫ y in (0 : ℝ)..1, g (p₀ + p₁ + p₂ * y)) =
          p₂⁻¹ * ∫ z in p₂ * (0 : ℝ)..p₂ * (1 : ℝ), g (p₀ + p₁ + z) := by
            simpa [add_assoc] using hmul
      _ = p₂⁻¹ * I2 := by
            simp [hshift]
  have hpne : p₂ ≠ 0 := ne_of_gt hp₂.1
  have hcalc : p₂⁻¹ * I2 = p₀ + p₁ * J := by
    rw [← hsubst, hcongr]
  calc
    (∫ x in (p₀ + p₁)..1, msG p₀ p₁ p₂ x) = I2 := rfl
    _ = p₂ * (p₂⁻¹ * I2) := by field_simp [hpne]
    _ = p₂ * (p₀ + p₁ * J) := by rw [hcalc]
    _ = p₂ * (p₀ + p₁ * ∫ x in (0 : ℝ)..1, msG p₀ p₁ p₂ x) := by
        dsimp [J, g]

end

/- accepted add_to_file helper 27 -/
noncomputable section

lemma msG_integral_eq {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) :
    (∫ x in (0 : ℝ)..1, msG p₀ p₁ p₂ x) =
      (p₁ ^ 2 + p₀ * p₁ + p₀ * p₂) /
        (1 - p₀ ^ 2 - 2 * p₁ * p₂) := by
  let g := msG p₀ p₁ p₂
  let I0 := ∫ x in (0 : ℝ)..p₀, g x
  let I1 := ∫ x in p₀..(p₀ + p₁), g x
  let I2 := ∫ x in (p₀ + p₁)..1, g x
  let J := ∫ x in (0 : ℝ)..1, g x
  have hp0le : (0 : ℝ) ≤ p₀ := hp₀.1.le
  have hp01 : p₀ ≤ p₀ + p₁ := by linarith [hp₁.1]
  have hp01nonneg : (0 : ℝ) ≤ p₀ + p₁ := by linarith [hp₀.1, hp₁.1]
  have hp01le1 : p₀ + p₁ ≤ 1 := by
    rw [← hsum]
    linarith [hp₂.1]
  have hi0 := msG_intervalIntegrable hp₀ hp₁ hp₂ hsum hp0le
  have hi1 := msG_intervalIntegrable hp₀ hp₁ hp₂ hsum hp01
  have hi2 := msG_intervalIntegrable hp₀ hp₁ hp₂ hsum hp01le1
  have hsplit1 : I0 + I1 = ∫ x in (0 : ℝ)..(p₀ + p₁), g x :=
    intervalIntegral.integral_add_adjacent_intervals hi0 hi1
  have hsplit2 : (∫ x in (0 : ℝ)..(p₀ + p₁), g x) + I2 = J :=
    intervalIntegral.integral_add_adjacent_intervals
      (msG_intervalIntegrable hp₀ hp₁ hp₂ hsum hp01nonneg) hi2
  have hsplit : J = I0 + I1 + I2 := by
    rw [← hsplit2, ← hsplit1]
  have hseg0 : I0 = p₀ ^ 2 * J := msG_integral_segment0 hp₀ hp₁ hp₂ hsum
  have hseg1 : I1 = p₁ * (p₀ + p₁ + p₂ * J) :=
    msG_integral_segment1 hp₀ hp₁ hp₂ hsum
  have hseg2 : I2 = p₂ * (p₀ + p₁ * J) :=
    msG_integral_segment2 hp₀ hp₁ hp₂ hsum
  rw [hseg0, hseg1, hseg2] at hsplit
  let D : ℝ := 1 - p₀ ^ 2 - 2 * p₁ * p₂
  let N : ℝ := p₁ ^ 2 + p₀ * p₁ + p₀ * p₂
  have hDfactor :
      D = p₁ * (1 - p₂) + p₂ * (1 - p₁) + p₀ * (p₁ + p₂) := by
    dsimp [D]
    nlinarith [hsum]
  have hDpos : 0 < D := by
    rw [hDfactor]
    have h1 : 0 < p₁ * (1 - p₂) := mul_pos hp₁.1 (sub_pos.mpr hp₂.2)
    have h2 : 0 < p₂ * (1 - p₁) := mul_pos hp₂.1 (sub_pos.mpr hp₁.2)
    have h3 : 0 < p₀ * (p₁ + p₂) := mul_pos hp₀.1 (add_pos hp₁.1 hp₂.1)
    linarith
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hlin : D * J = N := by
    have hleft : D * J = J - p₀ ^ 2 * J - 2 * p₁ * p₂ * J := by
      dsimp [D]
      ring
    rw [hleft]
    dsimp [N]
    linarith
  calc
    (∫ x in (0 : ℝ)..1, msG p₀ p₁ p₂ x) = J := rfl
    _ = D * J / D := by field_simp [hDne]
    _ = N / D := by rw [hlin]
    _ = (p₁ ^ 2 + p₀ * p₁ + p₀ * p₂) /
          (1 - p₀ ^ 2 - 2 * p₁ * p₂) := rfl

end

/- accepted add_to_file helper 28 -/
noncomputable section

lemma msF_eq_msG_on {p₀ p₁ p₂ : ℝ}
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) :
    Set.EqOn
      (fun x ↦ msE p₀ p₁ p₂ (fun k ↦ msTheta (msCanonical p₀ p₁ p₂ x k)))
      (msG p₀ p₁ p₂) (Set.Icc (0 : ℝ) 1) := by
  intro x hx
  dsimp [msG]
  rw [msCanonical_eq_msSeq hp₀ hp₁ hp₂ hsum hx]

end

/- verified submission -/
theorem lebesgue_integral_modified_salem
    (p₀ p₁ p₂ : ℝ)
    (hp₀ : p₀ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₁ : p₁ ∈ Set.Ioo (0 : ℝ) 1)
    (hp₂ : p₂ ∈ Set.Ioo (0 : ℝ) 1)
    (hsum : p₀ + p₁ + p₂ = 1) :
    let p : Fin 3 → ℝ := ![p₀, p₁, p₂]
    let β : Fin 3 → ℝ := ![0, p₀, p₀ + p₁]
    let E : (ℕ → Fin 3) → ℝ := fun i ↦
      ∑' k : ℕ, β (i k) * ∏ r ∈ Finset.range k, p (i r)
    let canonical : ℝ → (ℕ → Fin 3) := fun x ↦
      Classical.epsilon fun i ↦
        E i = x ∧
          ((∃ j, E j = x ∧ j ≠ i) →
            ∃ N, ∀ k, N ≤ k → i k = 0)
    let θ : Fin 3 → Fin 3 := ![0, 2, 1]
    let f : ℝ → ℝ := fun x ↦ E (fun k ↦ θ (canonical x k))
    MeasureTheory.IntegrableOn f (Set.Icc 0 1) ∧
      (∫ x in (0 : ℝ)..1, f x) =
        (p₁ ^ 2 + p₀ * p₁ + p₀ * p₂) /
          (1 - p₀ ^ 2 - 2 * p₁ * p₂) := by
  dsimp
  constructor
  · refine MeasureTheory.IntegrableOn.congr_fun
      (msG_integrableOn_Icc hp₀ hp₁ hp₂ hsum 0 1) ?_ measurableSet_Icc
    exact fun x hx ↦ (msF_eq_msG_on hp₀ hp₁ hp₂ hsum hx).symm
  · trans ∫ x in (0 : ℝ)..1, msG p₀ p₁ p₂ x
    · apply intervalIntegral.integral_congr_ae
      exact Filter.Eventually.of_forall fun x hx ↦ by
        have hxIoc : x ∈ Set.Ioc (0 : ℝ) 1 := by
          simpa [Set.uIoc_of_le zero_le_one] using hx
        have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hxIoc.1.le, hxIoc.2⟩
        exact msF_eq_msG_on hp₀ hp₁ hp₂ hsum hxIcc
    · exact msG_integral_eq hp₀ hp₁ hp₂ hsum

end Rollout_p1286_lebesgue_integral_modified_salem

#check_dependency_graph "Rollout_p1286_lebesgue_integral_modified_salem.lebesgue_integral_modified_salem" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let p := ![p₀, p₁, p₂]; let β := ![0, p₀, p₀ + p₁]; let E := fun i => ∑' (k : ℕ), β (i k) * ∏ r ∈ Finset.range k, p (i r); let canonical := fun x => Classical.epsilon fun i => E i = x ∧ ((∃ j, E j = x ∧ j ≠ i) → ∃ N, ∀ (k : ℕ), N ≤ k → i k = 0); let θ := ![0, 2, 1]; let f := fun x => E fun k => θ (canonical x k); MeasureTheory.IntegrableOn f (Set.Icc 0 1) MeasureTheory.volume ∧ ∫ (x : ℝ) in 0..1, f x = (p₁ ^ 2 + p₀ * p₁ + p₀ * p₂) / (1 - p₀ ^ 2 - 2 * p₁ * p₂)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hp₀\",\"statement\":\"p₀ ∈ Set.Ioo 0 1\"},{\"name\":\"hp₁\",\"statement\":\"p₁ ∈ Set.Ioo 0 1\"},{\"name\":\"hp₂\",\"statement\":\"p₂ ∈ Set.Ioo 0 1\"},{\"name\":\"hsum\",\"statement\":\"p₀ + p₁ + p₂ = 1\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1286_lebesgue_integral_modified_salem\",\"reconstructedProofSha256\":\"55a2ceea55db23b81b327bd46bf5a5fdb2fa82204952dc164ee7a4d0c21391b9\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1286_lebesgue_integral_modified_salem.lebesgue_integral_modified_salem\",\"topologySha256\":\"c173f2fd3f41805f05c416c106daa252296564e158ccbe52222c879356552a75\"}"

namespace Rollout_p1299_convexpolytope_trace_latticeembedding

-- graph_id: p1299_convexpolytope_trace_latticeembedding
-- topology_sha256: 05c80beeafdb73c7eb8a5d1fdb49b2806e9f9882af8cd90b50f37d0303868e47
/- accepted add_to_file helper 1 -/
lemma Convex.sum_mem_divisionRing
    {R E ι : Type*} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup E] [Module R E]
    {s : Set E} (hs : Convex R s) {t : Finset ι} {w : ι → R} {z : ι → E}
    (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1)
    (hz : ∀ i ∈ t, z i ∈ s) :
    ∑ i ∈ t, w i • z i ∈ s := by
  classical
  induction t using Finset.induction generalizing w with
  | empty =>
      simp at h₁
  | insert i t hi ih =>
      have hsum : w i + ∑ j ∈ t, w j = 1 := by
        simpa [hi] using h₁
      by_cases hwi : w i = 1
      · have hsumt : ∑ j ∈ t, w j = 0 := by
          have : 1 + ∑ j ∈ t, w j = 1 := by simpa [hwi] using hsum
          exact add_eq_left.mp this
        have hzero : ∀ j ∈ t, w j = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => h₀ j (Finset.mem_insert_of_mem hj))).mp hsumt
        have hweighted_zero : ∑ j ∈ t, w j • z j = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          rw [hzero j hj, zero_smul]
        have hzmem : z i ∈ s := hz i (Finset.mem_insert_self i t)
        rw [Finset.sum_insert hi, hweighted_zero, hwi, one_smul, add_zero]
        exact hzmem
      · set r : R := ∑ j ∈ t, w j with hrdef
        have hrnonneg : 0 ≤ r := by
          rw [hrdef]
          exact Finset.sum_nonneg (fun j hj => h₀ j (Finset.mem_insert_of_mem hj))
        have hwile : w i ≤ 1 := by
          rw [← hsum]
          exact le_add_of_nonneg_right hrnonneg
        have hwilt : w i < 1 := lt_of_le_of_ne hwile hwi
        have hsum' : r + w i = 1 := by
          simpa [hrdef, add_comm] using hsum
        have hr_eq : r = 1 - w i := eq_sub_of_add_eq hsum'
        have hwi_eq : w i = 1 - r := eq_sub_of_add_eq hsum
        have hrle : r ≤ 1 := by
          rw [← hsum']
          exact le_add_of_nonneg_right (h₀ i (Finset.mem_insert_self i t))
        have hrpos : 0 < r := by
          rw [hr_eq]
          exact sub_pos.mpr hwilt
        let w' : ι → R := fun j => r⁻¹ * w j
        have hw'₀ : ∀ j ∈ t, 0 ≤ w' j := by
          intro j hj
          exact mul_nonneg (inv_nonneg.mpr hrnonneg)
            (h₀ j (Finset.mem_insert_of_mem hj))
        have hw'₁ : ∑ j ∈ t, w' j = 1 := by
          calc
            ∑ j ∈ t, w' j = r⁻¹ * r := by
              rw [hrdef]
              exact (Finset.mul_sum t w r⁻¹).symm
            _ = 1 := inv_mul_cancel₀ hrpos.ne'
        have hy : ∑ j ∈ t, w' j • z j ∈ s :=
          ih (fun j hj => hw'₀ j hj) hw'₁ (fun j hj => hz j (Finset.mem_insert_of_mem hj))
        have hrest : ∑ j ∈ t, w j • z j = r • ∑ j ∈ t, w' j • z j := by
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          calc
            w j • z j = ((r * r⁻¹) * w j) • z j := by
              rw [mul_inv_cancel₀ hrpos.ne', one_mul]
            _ = (r * (r⁻¹ * w j)) • z j := by rw [mul_assoc]
            _ = r • ((r⁻¹ * w j) • z j) := mul_smul r (r⁻¹ * w j) (z j)
            _ = r • (w' j • z j) := rfl
        rw [Finset.sum_insert hi, hrest, hwi_eq]
        exact hs (hz i (Finset.mem_insert_self i t)) hy (sub_nonneg.mpr hrle) hrnonneg
          (sub_add_cancel 1 r)

/- accepted add_to_file helper 2 -/
lemma convexHull_eq_divisionRing
    {R E : Type*} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup E] [Module R E] (s : Set E) :
    convexHull R s =
      {x | ∃ (ι : Type) (t : Finset ι) (w : ι → R) (z : ι → E),
        (∀ i ∈ t, 0 ≤ w i) ∧ (∑ i ∈ t, w i = 1) ∧
        (∀ i ∈ t, z i ∈ s) ∧ (∑ i ∈ t, w i • z i) = x} := by
  classical
  apply Set.Subset.antisymm
  · apply convexHull_min
    · intro x hx
      refine ⟨PUnit, {PUnit.unit}, fun _ => 1, fun _ => x, ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · simpa using hx
      · simp
    · intro x hx y hy a b ha hb hab
      rcases hx with ⟨ιx, tx, wx, zx, hwx₀, hwx₁, hzx, hxeq⟩
      rcases hy with ⟨ιy, ty, wy, zy, hwy₀, hwy₁, hzy, hyeq⟩
      refine ⟨ιx ⊕ ιy, tx.disjSum ty,
        Sum.elim (fun i => a * wx i) (fun j => b * wy j), Sum.elim zx zy,
        ?_, ?_, ?_, ?_⟩
      · intro k hk
        rcases Finset.mem_disjSum.mp hk with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
        · exact mul_nonneg ha (hwx₀ i hi)
        · exact mul_nonneg hb (hwy₀ j hj)
      · simp only [Finset.sum_disjSum, Sum.elim_inl, Sum.elim_inr]
        rw [← Finset.mul_sum tx wx a, hwx₁]
        rw [← Finset.mul_sum ty wy b, hwy₁]
        simpa using hab
      · intro k hk
        rcases Finset.mem_disjSum.mp hk with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
        · exact hzx i hi
        · exact hzy j hj
      · calc
          (∑ k ∈ tx.disjSum ty,
              Sum.elim (fun i => a * wx i) (fun j => b * wy j) k • Sum.elim zx zy k)
              = a • (∑ i ∈ tx, wx i • zx i) + b • (∑ j ∈ ty, wy j • zy j) := by
                simp only [Finset.sum_disjSum, Sum.elim_inl, Sum.elim_inr]
                congr 1
                · rw [Finset.smul_sum]
                  apply Finset.sum_congr rfl
                  intro i hi
                  exact mul_smul a (wx i) (zx i)
                · rw [Finset.smul_sum]
                  apply Finset.sum_congr rfl
                  intro j hj
                  exact mul_smul b (wy j) (zy j)
          _ = a • x + b • y := by rw [hxeq, hyeq]
  · intro x hx
    rcases hx with ⟨ι, t, w, z, hw₀, hw₁, hz, hxeq⟩
    rw [← hxeq]
    exact Convex.sum_mem_divisionRing (convex_convexHull R s) hw₀ hw₁
      (fun i hi => subset_convexHull R s (hz i hi))

/- accepted add_to_file helper 3 -/
lemma mem_convexHull_finset_divisionRing
    {R E : Type*} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup E] [Module R E] {s : Finset E} {x : E} :
    x ∈ convexHull R (↑s : Set E) ↔
      ∃ w : E → R, (∀ y ∈ s, 0 ≤ w y) ∧ (∑ y ∈ s, w y = 1) ∧
        (∑ y ∈ s, w y • y) = x := by
  classical
  constructor
  · intro hx
    rw [convexHull_eq_divisionRing (↑s : Set E)] at hx
    rcases hx with ⟨ι, t, u, z, hu₀, hu₁, hz, hxeq⟩
    let w : E → R := fun y => ∑ i ∈ t.filter (fun i => z i = y), u i
    refine ⟨w, ?_, ?_, ?_⟩
    · intro y hy
      exact Finset.sum_nonneg (fun i hi => hu₀ i (Finset.mem_filter.mp hi).1)
    · calc
        ∑ y ∈ s, w y = ∑ y ∈ s, ∑ i ∈ t.filter (fun i => z i = y), u i := rfl
        _ = ∑ i ∈ t, u i := by
          exact Finset.sum_fiberwise_of_maps_to (fun i hi => by simpa using hz i hi) u
        _ = 1 := hu₁
    · calc
        ∑ y ∈ s, w y • y
            = ∑ y ∈ s, ∑ i ∈ t.filter (fun i => z i = y), u i • z i := by
              apply Finset.sum_congr rfl
              intro y hy
              calc
                w y • y = (∑ i ∈ t.filter (fun i => z i = y), u i) • y := rfl
                _ = ∑ i ∈ t.filter (fun i => z i = y), u i • y := Finset.sum_smul
                _ = ∑ i ∈ t.filter (fun i => z i = y), u i • z i := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [Finset.mem_filter] at hi
                  rw [hi.2]
        _ = ∑ i ∈ t, u i • z i := by
          exact Finset.sum_fiberwise_of_maps_to (fun i hi => by simpa using hz i hi)
            (fun i => u i • z i)
        _ = x := hxeq
  · intro hx
    rcases hx with ⟨w, hw₀, hw₁, hxeq⟩
    rw [← hxeq]
    exact Convex.sum_mem_divisionRing (convex_convexHull R (↑s : Set E)) hw₀ hw₁
      (fun y hy => subset_convexHull R (↑s : Set E) (by simpa using hy))

/- accepted add_to_file helper 4 -/
lemma exists_convexCombination_coeff_lt_one_divisionRing
    {R E : Type*} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup E] [Module R E]
    {s : Finset E} {a p : E} (ha : a ∈ s)
    (hp : p ∈ convexHull R (↑s : Set E)) (hpa : p ≠ a) :
    ∃ w : E → R, (∀ y ∈ s, 0 ≤ w y) ∧ (∑ y ∈ s, w y = 1) ∧
      (∑ y ∈ s, w y • y) = p ∧ w a < 1 := by
  classical
  rcases (mem_convexHull_finset_divisionRing.mp hp) with ⟨w, hw₀, hw₁, hwp⟩
  refine ⟨w, hw₀, hw₁, hwp, ?_⟩
  have hwale : w a ≤ 1 := by
    calc
      w a ≤ ∑ y ∈ s, w y := Finset.single_le_sum hw₀ ha
      _ = 1 := hw₁
  refine lt_of_le_of_ne hwale ?_
  intro hwa
  have herase_sum : ∑ y ∈ s.erase a, w y = 0 := by
    have h := Finset.sum_erase_add s w ha
    rw [hwa, hw₁] at h
    exact add_eq_right.mp h
  have hzero : ∀ y ∈ s.erase a, w y = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun y hy => hw₀ y (Finset.mem_of_mem_erase hy))).mp herase_sum
  have hsum_single : ∑ y ∈ s, w y • y = w a • a := by
    apply Finset.sum_eq_single_of_mem a ha
    intro y hy hya
    have hyerase : y ∈ s.erase a := Finset.mem_erase.mpr ⟨hya, hy⟩
    rw [hzero y hyerase, zero_smul]
  have : p = a := by
    rw [← hwp, hsum_single, hwa, one_smul]
  exact hpa this

/- accepted add_to_file helper 5 -/
lemma mem_convexHull_erase_of_combination_self_divisionRing
    {R E : Type*} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup E] [Module R E] [DecidableEq E]
    {s : Finset E} {a : E} (ha : a ∈ s) {w : E → R}
    (hw₀ : ∀ y ∈ s, 0 ≤ w y) (hw₁ : ∑ y ∈ s, w y = 1)
    (hwa : w a < 1) (hsum : ∑ y ∈ s, w y • y = a) :
    a ∈ convexHull R (↑(s.erase a) : Set E) := by
  classical
  set r : R := 1 - w a with hrdef
  have hrpos : 0 < r := by
    rw [hrdef]
    exact sub_pos.mpr hwa
  let v : E → R := fun y => r⁻¹ * w y
  have hv₀ : ∀ y ∈ s.erase a, 0 ≤ v y := by
    intro y hy
    exact mul_nonneg (inv_nonneg.mpr hrpos.le)
      (hw₀ y (Finset.mem_of_mem_erase hy))
  have hsum_erase_w : ∑ y ∈ s.erase a, w y = r := by
    rw [hrdef, Finset.sum_erase_eq_sub ha, hw₁]
  have hv₁ : ∑ y ∈ s.erase a, v y = 1 := by
    calc
      ∑ y ∈ s.erase a, v y = r⁻¹ * ∑ y ∈ s.erase a, w y := by
        exact (Finset.mul_sum (s.erase a) w r⁻¹).symm
      _ = r⁻¹ * r := by rw [hsum_erase_w]
      _ = 1 := inv_mul_cancel₀ hrpos.ne'
  have hweighted_erase : ∑ y ∈ s.erase a, w y • y = r • a := by
    have hdecomp := Finset.sum_erase_add s (fun y => w y • y) ha
    rw [hsum] at hdecomp
    calc
      ∑ y ∈ s.erase a, w y • y = a - w a • a := eq_sub_of_add_eq hdecomp
      _ = (1 : R) • a - w a • a := by rw [one_smul]
      _ = (1 - w a) • a := (sub_smul (1 : R) (w a) a).symm
      _ = r • a := rfl
  have hvsum : ∑ y ∈ s.erase a, v y • y = a := by
    calc
      ∑ y ∈ s.erase a, v y • y
          = ∑ y ∈ s.erase a, r⁻¹ • (w y • y) := by
            apply Finset.sum_congr rfl
            intro y hy
            exact mul_smul r⁻¹ (w y) y
      _ = r⁻¹ • ∑ y ∈ s.erase a, w y • y := (Finset.smul_sum).symm
      _ = r⁻¹ • (r • a) := by rw [hweighted_erase]
      _ = (r⁻¹ * r) • a := (mul_smul r⁻¹ r a).symm
      _ = a := by rw [inv_mul_cancel₀ hrpos.ne', one_smul]
  exact mem_convexHull_finset_divisionRing.mpr ⟨v, hv₀, hv₁, hvsum⟩

/- accepted add_to_file helper 6 -/
lemma mem_convexHull_erase_of_mem_openSegment_left_ne_divisionRing
    {R E : Type*} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup E] [Module R E] [DecidableEq E]
    {s : Finset E} {a x₁ x₂ : E} (ha : a ∈ s)
    (hx₁ : x₁ ∈ convexHull R (↑s : Set E))
    (hx₂ : x₂ ∈ convexHull R (↑s : Set E))
    (hseg : a ∈ openSegment R x₁ x₂) (hx₁a : x₁ ≠ a) :
    a ∈ convexHull R (↑(s.erase a) : Set E) := by
  classical
  rcases hseg with ⟨c₁, c₂, hc₁, hc₂, hcsum, hcombo⟩
  rcases exists_convexCombination_coeff_lt_one_divisionRing ha hx₁ hx₁a with
    ⟨w₁, hw₁₀, hw₁₁, hw₁sum, hw₁a⟩
  rcases (mem_convexHull_finset_divisionRing.mp hx₂) with ⟨w₂, hw₂₀, hw₂₁, hw₂sum⟩
  let u : E → R := fun y => c₁ * w₁ y + c₂ * w₂ y
  have hu₀ : ∀ y ∈ s, 0 ≤ u y := by
    intro y hy
    exact add_nonneg (mul_nonneg hc₁.le (hw₁₀ y hy))
      (mul_nonneg hc₂.le (hw₂₀ y hy))
  have hu₁ : ∑ y ∈ s, u y = 1 := by
    calc
      ∑ y ∈ s, u y = ∑ y ∈ s, (c₁ * w₁ y + c₂ * w₂ y) := rfl
      _ = 1 := by
        rw [Finset.sum_add_distrib]
        rw [← Finset.mul_sum s w₁ c₁, hw₁₁]
        rw [← Finset.mul_sum s w₂ c₂, hw₂₁]
        simpa using hcsum
  have hw₂a : w₂ a ≤ 1 := by
    calc
      w₂ a ≤ ∑ y ∈ s, w₂ y := Finset.single_le_sum hw₂₀ ha
      _ = 1 := hw₂₁
  have hua : u a < 1 := by
    calc
      u a = c₁ * w₁ a + c₂ * w₂ a := rfl
      _ < c₁ * 1 + c₂ * 1 :=
        add_lt_add_of_lt_of_le
          (mul_lt_mul_of_pos_left hw₁a hc₁)
          (mul_le_mul_of_nonneg_left hw₂a hc₂.le)
      _ = 1 := by simpa using hcsum
  have husum : ∑ y ∈ s, u y • y = a := by
    calc
      ∑ y ∈ s, u y • y = ∑ y ∈ s, (c₁ * w₁ y + c₂ * w₂ y) • y := rfl
      _ = ∑ y ∈ s, (c₁ • (w₁ y • y) + c₂ • (w₂ y • y)) := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [add_smul, mul_smul, mul_smul]
      _ = c₁ • (∑ y ∈ s, w₁ y • y) + c₂ • (∑ y ∈ s, w₂ y • y) := by
        rw [Finset.sum_add_distrib, Finset.smul_sum, Finset.smul_sum]
      _ = c₁ • x₁ + c₂ • x₂ := by rw [hw₁sum, hw₂sum]
      _ = a := hcombo
  exact mem_convexHull_erase_of_combination_self_divisionRing ha hu₀ hu₁ hua husum

/- accepted add_to_file helper 7 -/
lemma convexHull_erase_eq_of_not_extremePoint_divisionRing
    {R E : Type*} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup E] [Module R E] [DecidableEq E]
    {s : Finset E} {a : E} (ha : a ∈ s)
    (hne : a ∉ Set.extremePoints R (convexHull R (↑s : Set E))) :
    convexHull R (↑(s.erase a) : Set E) = convexHull R (↑s : Set E) := by
  classical
  have haP : a ∈ convexHull R (↑s : Set E) :=
    subset_convexHull R (↑s : Set E) (by simpa using ha)
  rw [mem_extremePoints] at hne
  push Not at hne
  rcases hne haP with ⟨x₁, hx₁, x₂, hx₂, hseg, hnot⟩
  have hamem : a ∈ convexHull R (↑(s.erase a) : Set E) := by
    by_cases hx₁a : x₁ = a
    · have hx₂a : x₂ ≠ a := hnot hx₁a
      have hseg' : a ∈ openSegment R x₂ x₁ := by
        rwa [openSegment_symm]
      exact mem_convexHull_erase_of_mem_openSegment_left_ne_divisionRing
        ha hx₂ hx₁ hseg' hx₂a
    · exact mem_convexHull_erase_of_mem_openSegment_left_ne_divisionRing
        ha hx₁ hx₂ hseg hx₁a
  apply Set.Subset.antisymm
  · exact convexHull_mono (by intro y hy; simpa using (Finset.erase_subset a s hy))
  · apply convexHull_min
    · intro y hy
      by_cases hya : y = a
      · rwa [hya]
      · apply subset_convexHull R (↑(s.erase a) : Set E)
        exact (Finset.mem_erase (a := y) (b := a) (s := s)).mpr
          ⟨hya, by simpa using hy⟩
    · exact convex_convexHull R (↑(s.erase a) : Set E)

/- accepted add_to_file helper 8 -/
lemma convexHull_subset_convexHull_of_extremePoints_subset_divisionRing
    {R E : Type*} [DivisionRing R] [LinearOrder R] [IsStrictOrderedRing R]
    [AddCommGroup E] [Module R E] [DecidableEq E]
    {C : Set E} (s : Finset E)
    (hC : C ⊆ convexHull R (↑s : Set E))
    (hext : Set.extremePoints R (convexHull R (↑s : Set E)) ⊆ C) :
    convexHull R (↑s : Set E) ⊆ convexHull R C := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
      by_cases hall : ∀ a ∈ s, a ∈ C
      · exact convexHull_mono (by
          intro a ha
          exact hall a (by simpa using ha))
      · push Not at hall
        rcases hall with ⟨a, ha, haC⟩
        have haext : a ∉ Set.extremePoints R (convexHull R (↑s : Set E)) := by
          intro h
          exact haC (hext h)
        have herase : convexHull R (↑(s.erase a) : Set E) =
            convexHull R (↑s : Set E) :=
          convexHull_erase_eq_of_not_extremePoint_divisionRing ha haext
        have hC_erase : C ⊆ convexHull R (↑(s.erase a) : Set E) := by
          rw [herase]
          exact hC
        have hext_erase :
            Set.extremePoints R (convexHull R (↑(s.erase a) : Set E)) ⊆ C := by
          rw [herase]
          exact hext
        have hsub := ih (s.erase a) (Finset.erase_ssubset ha) hC_erase hext_erase
        rw [← herase]
        exact hsub

/- verified submission -/
theorem convexPolytope_trace_latticeEmbedding
    {F V L : Type*} [DivisionRing F] [LinearOrder F] [IsStrictOrderedRing F]
    [AddCommGroup V] [Module F V] [Lattice L]
    (φ : L → Set V) (Ω : Set V)
    (hpoly : ∀ x : L, ∃ A : Set V, A.Finite ∧ convexHull F A = φ x)
    (hinj : Function.Injective φ)
    (hmeet : ∀ x y : L, φ (x ⊓ y) = φ x ∩ φ y)
    (hjoin : ∀ x y : L, φ (x ⊔ y) = convexHull F (φ x ∪ φ y))
    (hextreme : ∀ x : L, Set.extremePoints F (φ x) ⊆ Ω) :
    let ψ : L → Set V := fun x => φ x ∩ Ω
    Function.Injective ψ ∧
      (∀ x : L, Ω ∩ convexHull F (ψ x) = ψ x) ∧
      (∀ x y : L, ψ (x ⊓ y) = ψ x ∩ ψ y) ∧
      (∀ x y : L, ψ (x ⊔ y) = Ω ∩ convexHull F (ψ x ∪ ψ y)) ∧
      ∀ x : L, convexHull F (ψ x) = φ x := by
  classical
  let ψ : L → Set V := fun x => φ x ∩ Ω
  have hconv : ∀ x : L, convexHull F (ψ x) = φ x := by
    intro x
    rcases hpoly x with ⟨A, hAfin, hA⟩
    let s : Finset V := hAfin.toFinset
    have hsA : (↑s : Set V) = A := hAfin.coe_toFinset
    have hφ : φ x = convexHull F (↑s : Set V) := by
      rw [hsA, ← hA]
    have hψ_sub : ψ x ⊆ convexHull F (↑s : Set V) := by
      intro p hp
      rw [← hφ]
      exact hp.1
    have hext_sub :
        Set.extremePoints F (convexHull F (↑s : Set V)) ⊆ ψ x := by
      intro p hp
      constructor
      · rw [hφ]
        exact extremePoints_subset hp
      · apply hextreme x
        simpa [hφ] using hp
    have hsub : convexHull F (↑s : Set V) ⊆ convexHull F (ψ x) :=
      convexHull_subset_convexHull_of_extremePoints_subset_divisionRing s hψ_sub hext_sub
    have hrev : convexHull F (ψ x) ⊆ convexHull F (↑s : Set V) := by
      apply convexHull_min hψ_sub
      exact convex_convexHull F (↑s : Set V)
    calc
      convexHull F (ψ x) = convexHull F (↑s : Set V) :=
        Set.Subset.antisymm hrev hsub
      _ = φ x := hφ.symm
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    apply hinj
    rw [← hconv x, ← hconv y, hxy]
  refine ⟨hψinj, ?_, ?_, ?_, hconv⟩
  · intro x
    rw [hconv x]
    ext p
    simp [and_comm]
  · intro x y
    ext p
    simp [hmeet, and_assoc, and_left_comm, and_comm]
  · intro x y
    have hunion : convexHull F (ψ x ∪ ψ y) = convexHull F (φ x ∪ φ y) := by
      apply Set.Subset.antisymm
      · apply convexHull_min
        · intro p hp
          rcases hp with hp | hp
          · exact subset_convexHull F (φ x ∪ φ y) (Or.inl hp.1)
          · exact subset_convexHull F (φ x ∪ φ y) (Or.inr hp.1)
        · exact convex_convexHull F (φ x ∪ φ y)
      · apply convexHull_min
        · intro p hp
          rcases hp with hp | hp
          · have hp' : p ∈ convexHull F (ψ x) := by
              rw [hconv x]
              exact hp
            exact convexHull_mono Set.subset_union_left hp'
          · have hp' : p ∈ convexHull F (ψ y) := by
              rw [hconv y]
              exact hp
            exact convexHull_mono Set.subset_union_right hp'
        · exact convex_convexHull F (ψ x ∪ ψ y)
    change φ (x ⊔ y) ∩ Ω = Ω ∩ convexHull F (ψ x ∪ ψ y)
    rw [hjoin, hunion]
    ext p
    simp [and_comm]

end Rollout_p1299_convexpolytope_trace_latticeembedding

#check_dependency_graph "Rollout_p1299_convexpolytope_trace_latticeembedding.convexPolytope_trace_latticeEmbedding" against "{\"edges\":[{\"conclusion\":{\"name\":\"hconv\",\"statement\":\"∀ (x : L), (convexHull F) (ψ x) = φ x\"},\"graphEdgeId\":\"h_001_hconv\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"IsStrictOrderedRing F\"},{\"name\":\"hpoly\",\"statement\":\"∀ (x : L), ∃ A, A.Finite ∧ (convexHull F) A = φ x\"},{\"name\":\"hextreme\",\"statement\":\"∀ (x : L), Set.extremePoints F (φ x) ⊆ Ω\"}],\"rawEdgeId\":\"telescope_17\"},{\"conclusion\":{\"name\":\"hψinj\",\"statement\":\"Function.Injective ψ\"},\"graphEdgeId\":\"h_002_h_inj\",\"premises\":[{\"name\":\"hinj\",\"statement\":\"Function.Injective φ\"},{\"name\":\"hconv\",\"statement\":\"∀ (x : L), (convexHull F) (ψ x) = φ x\"}],\"rawEdgeId\":\"telescope_18\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(Function.Injective fun x => φ x ∩ Ω) ∧ (∀ (x : L), Ω ∩ (convexHull F) ((fun x => φ x ∩ Ω) x) = (fun x => φ x ∩ Ω) x) ∧ (∀ (x y : L), (fun x => φ x ∩ Ω) (x ⊓ y) = (fun x => φ x ∩ Ω) x ∩ (fun x => φ x ∩ Ω) y) ∧ (∀ (x y : L), (fun x => φ x ∩ Ω) (x ⊔ y) = Ω ∩ (convexHull F) ((fun x => φ x ∩ Ω) x ∪ (fun x => φ x ∩ Ω) y)) ∧ ∀ (x : L), (convexHull F) ((fun x => φ x ∩ Ω) x) = φ x\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hmeet\",\"statement\":\"∀ (x y : L), φ (x ⊓ y) = φ x ∩ φ y\"},{\"name\":\"hjoin\",\"statement\":\"∀ (x y : L), φ (x ⊔ y) = (convexHull F) (φ x ∪ φ y)\"},{\"name\":\"hconv\",\"statement\":\"∀ (x : L), (convexHull F) (ψ x) = φ x\"},{\"name\":\"hψinj\",\"statement\":\"Function.Injective ψ\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1299_convexpolytope_trace_latticeembedding\",\"reconstructedProofSha256\":\"d2e8da6d1a6e2bda5ee7fdc2b245db64d06e568a7aea01be31cda195b9818b8c\",\"selectedEdgeCount\":3,\"theoremName\":\"Rollout_p1299_convexpolytope_trace_latticeembedding.convexPolytope_trace_latticeEmbedding\",\"topologySha256\":\"05c80beeafdb73c7eb8a5d1fdb49b2806e9f9882af8cd90b50f37d0303868e47\"}"
