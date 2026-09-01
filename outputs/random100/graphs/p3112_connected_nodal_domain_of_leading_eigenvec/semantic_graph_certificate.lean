import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p3112_connected_nodal_domain_of_leading_eigenvec
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: c39b7c8c6116dc2fd9aec5c5f12c8be8cfbb66665a78d6ee1e6b4f19fc34ca34
-- reconstructed_proof_sha256: 235e94dde3532449f95ea5f6668c983cfdbcd1de853e57639b4f5cb26ffe128e
-- selected_edge_count: 8

/- accepted add_to_file helper 1 -/
lemma Matrix.IsSymm.isHermitian_real {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (h : A.IsSymm) : A.IsHermitian := by
  ext i j
  exact (congr_fun (congr_fun h j) i).symm

lemma eig_shift_algebra {n : Type*} [Fintype n] [DecidableEq n]
    {B C : Matrix n n ℝ} (l μ : ℝ) (e : n → ℝ)
    (hC : C = l • (1 : Matrix n n ℝ) - B)
    (heigC : C.mulVec e = μ • e) :
    B.mulVec e = (l - μ) • e := by
  calc
    B.mulVec e = (l • (1 : Matrix n n ℝ)).mulVec e - C.mulVec e := by
      rw [hC]
      simp [Matrix.sub_mulVec]
    _ = l • e - μ • e := by
      rw [heigC]
      simp [Matrix.smul_mulVec, Matrix.one_mulVec]
    _ = (l - μ) • e := by
      funext i
      simp
      ring

lemma quad_le_largest_of_symm {n : Type*} [Fintype n] [DecidableEq n]
    {B : Matrix n n ℝ} (hB : B.IsSymm) {l : ℝ}
    (hl : ∀ μ : ℝ, (∃ u : n → ℝ, u ≠ 0 ∧ B.mulVec u = μ • u) → μ ≤ l)
    (z : n → ℝ) :
    dotProduct z (B.mulVec z) ≤ l * dotProduct z z := by
  classical
  let C : Matrix n n ℝ := l • (1 : Matrix n n ℝ) - B
  have hCsymm : C.IsSymm := (Matrix.isSymm_one.smul l).sub hB
  have hCherm : C.IsHermitian := hCsymm.isHermitian_real
  have hCpsd : C.PosSemidef := by
    rw [hCherm.posSemidef_iff_eigenvalues_nonneg]
    intro j
    let e : n → ℝ := (hCherm.eigenvectorBasis j).ofLp
    have hene : e ≠ 0 := by
      intro hz
      exact hCherm.eigenvectorBasis.toBasis.ne_zero j (by
        ext i
        exact congr_fun hz i)
    have heigC : C.mulVec e = hCherm.eigenvalues j • e :=
      hCherm.mulVec_eigenvectorBasis j
    have heigB : B.mulVec e = (l - hCherm.eigenvalues j) • e :=
      eig_shift_algebra (B := B) (C := C) l (hCherm.eigenvalues j) e rfl heigC
    have hle := hl (l - hCherm.eigenvalues j) ⟨e, hene, heigB⟩
    change 0 ≤ hCherm.eigenvalues j
    linarith
  have hquad := hCpsd.dotProduct_mulVec_nonneg z
  change 0 ≤ dotProduct z (C.mulVec z) at hquad
  have hq : dotProduct z (C.mulVec z) =
      l * dotProduct z z - dotProduct z (B.mulVec z) := by
    simp [C, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul]
  rw [hq] at hquad
  linarith

lemma reachable_mem_of_closed {V : Type*} {G : SimpleGraph V} {C : Set V}
    (hclosed : ∀ a ∈ C, ∀ b, G.Adj a b → b ∈ C)
    {u v : V} (hu : u ∈ C) (h : G.Reachable u v) : v ∈ C := by
  rcases h with ⟨p⟩
  induction p with
  | nil => exact hu
  | cons huv p ih =>
      exact ih (hclosed _ hu _ huv)

/- accepted add_to_file helper 2 -/
lemma dot_indicator_split {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (z : ι → ℝ) (U : Finset ι) :
    let u : ι → ℝ := fun i => if i ∈ U then z i else 0
    dotProduct u (B.mulVec u) =
      (∑ i ∈ U, z i * (B.mulVec z) i) -
      ∑ i ∈ U, ∑ j ∈ Uᶜ, z i * B i j * z j := by
  intro u
  simp [u, dotProduct, Matrix.mulVec]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum, Finset.mul_sum]
  have hs := Finset.sum_add_sum_compl U (fun j => z i * (B i j * z j))
  rw [← hs]
  ring_nf

/- accepted add_to_file helper 3 -/
lemma posSemidef_sub_of_symm_forall_eigenvalue_le
    {n : Type*} [Fintype n] [DecidableEq n]
    {B : Matrix n n ℝ} (hB : B.IsSymm) (l : ℝ)
    (hl : ∀ μ : ℝ, (∃ u : n → ℝ, u ≠ 0 ∧ B.mulVec u = μ • u) → μ ≤ l) :
    (l • (1 : Matrix n n ℝ) - B).PosSemidef := by
  classical
  let C : Matrix n n ℝ := l • (1 : Matrix n n ℝ) - B
  have hCsymm : C.IsSymm := (Matrix.isSymm_one.smul l).sub hB
  have hCherm : C.IsHermitian := hCsymm.isHermitian_real
  change C.PosSemidef
  rw [hCherm.posSemidef_iff_eigenvalues_nonneg]
  intro j
  let e : n → ℝ := (hCherm.eigenvectorBasis j).ofLp
  have hene : e ≠ 0 := by
    intro hz
    exact hCherm.eigenvectorBasis.toBasis.ne_zero j (by
      ext i
      exact congr_fun hz i)
  have heigC : C.mulVec e = hCherm.eigenvalues j • e :=
    hCherm.mulVec_eigenvectorBasis j
  have heigB : B.mulVec e = (l - hCherm.eigenvalues j) • e :=
    eig_shift_algebra (B := B) (C := C) l (hCherm.eigenvalues j) e rfl heigC
  have hle := hl (l - hCherm.eigenvalues j) ⟨e, hene, heigB⟩
  change 0 ≤ hCherm.eigenvalues j
  linarith

/- accepted add_to_file helper 4 -/
lemma quad_abs_ge {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℝ} (hoff : ∀ i j, i ≠ j → 0 ≤ B i j) (x : ι → ℝ) :
    dotProduct x (B.mulVec x) ≤
      dotProduct (fun i => |x i|) (B.mulVec fun i => |x i|) := by
  simp only [dotProduct, Matrix.mulVec]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hij : i = j
  · subst hij
    ring_nf
    rw [sq_abs]
    ring_nf
    exact le_rfl
  · have h1 : x i * x j ≤ |x i * x j| := le_abs_self _
    have h2 : (x i * x j) * B i j ≤ |x i * x j| * B i j :=
      mul_le_mul_of_nonneg_right h1 (hoff i j hij)
    rw [abs_mul] at h2
    ring_nf at h2 ⊢
    exact h2

lemma quad_abs_eq_terms {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℝ} (hoff : ∀ i j, i ≠ j → 0 ≤ B i j) (x : ι → ℝ)
    (heq : dotProduct x (B.mulVec x) =
      dotProduct (fun i => |x i|) (B.mulVec fun i => |x i|)) :
    ∀ i j, x i * (B i j * x j) = |x i| * (B i j * |x j|) := by
  have hterm_le : ∀ i ∈ Finset.univ, (∑ j, x i * (B i j * x j)) ≤
      ∑ j, |x i| * (B i j * |x j|) := by
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    by_cases hij : i = j
    · subst hij
      ring_nf
      rw [sq_abs]
      ring_nf
      exact le_rfl
    · have h1 : x i * x j ≤ |x i * x j| := le_abs_self _
      have h2 : (x i * x j) * B i j ≤ |x i * x j| * B i j :=
        mul_le_mul_of_nonneg_right h1 (hoff i j hij)
      rw [abs_mul] at h2
      ring_nf at h2 ⊢
      exact h2
  have heq_exp : (∑ i, ∑ j, x i * (B i j * x j)) =
      ∑ i, ∑ j, |x i| * (B i j * |x j|) := by
    simpa [dotProduct, Matrix.mulVec, Finset.mul_sum] using heq
  have houter : ∀ i ∈ Finset.univ,
      (∑ j, x i * (B i j * x j)) =
        ∑ j, |x i| * (B i j * |x j|) :=
    (Finset.sum_eq_sum_iff_of_le hterm_le).mp heq_exp
  intro i j
  have hinner_le : ∀ j ∈ Finset.univ,
      x i * (B i j * x j) ≤ |x i| * (B i j * |x j|) := by
    intro j hj
    by_cases hij : i = j
    · subst hij
      ring_nf
      rw [sq_abs]
      ring_nf
      exact le_rfl
    · have h1 : x i * x j ≤ |x i * x j| := le_abs_self _
      have h2 : (x i * x j) * B i j ≤ |x i * x j| * B i j :=
        mul_le_mul_of_nonneg_right h1 (hoff i j hij)
      rw [abs_mul] at h2
      ring_nf at h2 ⊢
      exact h2
  exact (Finset.sum_eq_sum_iff_of_le hinner_le).mp
    (houter i (Finset.mem_univ i)) j (Finset.mem_univ j)

/- accepted add_to_file helper 5 -/
lemma abs_eigen_of_top {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B : Matrix ι ι ℝ} (hB : B.IsSymm)
    (hoff : ∀ i j, i ≠ j → 0 ≤ B i j)
    {l : ℝ}
    (hl : ∀ μ : ℝ, (∃ u : ι → ℝ, u ≠ 0 ∧ B.mulVec u = μ • u) → μ ≤ l)
    {x : ι → ℝ} (hx : B.mulVec x = l • x) :
    B.mulVec (fun i => |x i|) = l • fun i => |x i| := by
  classical
  let r : ι → ℝ := fun i => |x i|
  let C : Matrix ι ι ℝ := l • (1 : Matrix ι ι ℝ) - B
  have hCpsd : C.PosSemidef :=
    posSemidef_sub_of_symm_forall_eigenvalue_le hB l hl
  have hCnonneg := hCpsd.dotProduct_mulVec_nonneg r
  change 0 ≤ dotProduct r (C.mulVec r) at hCnonneg
  have hnorm : dotProduct r r = dotProduct x x := by
    simp [r, dotProduct]
  have hqx : dotProduct x (B.mulVec x) = l * dotProduct x x := by
    rw [hx]
    simp [dotProduct_smul]
  have hqabs_ge : l * dotProduct r r ≤ dotProduct r (B.mulVec r) := by
    rw [hnorm, ← hqx]
    exact quad_abs_ge hoff x
  have hqC : dotProduct r (C.mulVec r) =
      l * dotProduct r r - dotProduct r (B.mulVec r) := by
    simp [C, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul]
  have hqC_le : dotProduct r (C.mulVec r) ≤ 0 := by
    rw [hqC]
    linarith
  have hqC_zero : dotProduct r (C.mulVec r) = 0 := le_antisymm hqC_le hCnonneg
  have hCr : C.mulVec r = 0 := by
    apply (hCpsd.dotProduct_mulVec_zero_iff r).mp
    change dotProduct r (C.mulVec r) = 0
    exact hqC_zero
  have hCr0 : C.mulVec r = (0 : ℝ) • r := by simpa using hCr
  have hB := eig_shift_algebra (B := B) (C := C) l (0 : ℝ) r rfl hCr0
  simpa using hB

/- accepted add_to_file helper 6 -/
lemma abs_pos_of_connected {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ}
    (hA_symm : A.IsSymm) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (hoffB : ∀ i j, i ≠ j → B i j = A i j)
    (hG_conn : (SimpleGraph.fromRel (fun i j : ι => 0 < A i j)).Connected)
    {l : ℝ} {x : ι → ℝ} (hx_nonzero : x ≠ 0)
    (habs : B.mulVec (fun i => |x i|) = l • fun i => |x i|) :
    ∀ j, 0 < |x j| := by
  classical
  let r : ι → ℝ := fun i => |x i|
  let t : ℝ := |l| + (∑ i, |B i i|) + 1
  let N : Matrix ι ι ℝ := B + t • (1 : Matrix ι ι ℝ)
  have hsum_diag_nonneg : 0 ≤ ∑ i, |B i i| := by
    apply Finset.sum_nonneg
    intro i hi
    exact abs_nonneg _
  have hlt : 0 < l + t := by
    have hle : |l| ≤ t := by
      dsimp [t]
      linarith [abs_nonneg l, hsum_diag_nonneg]
    have := neg_abs_le l
    linarith
  have hdiag : ∀ i, 0 < B i i + t := by
    intro i
    have hterm : |B i i| ≤ ∑ k, |B k k| :=
      Finset.single_le_sum (s := Finset.univ) (f := fun k => |B k k|)
        (fun k hk => abs_nonneg _) (Finset.mem_univ i)
    have htdiff : 1 ≤ t - |B i i| := by
      dsimp [t]
      linarith [abs_nonneg l, hterm]
    have := neg_abs_le (B i i)
    linarith
  have hNnonneg : ∀ i j, 0 ≤ N i j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have := hdiag i
      simp [N]
      linarith
    · simp [N, hij, hoffB i j hij, hA_nonneg i j]
  have hshift : N.mulVec r = (l + t) • r := by
    simp [N, r, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      habs, add_smul]
  let P : Set ι := {i | 0 < r i}
  have hclosed : ∀ i ∈ P, ∀ j,
      (SimpleGraph.fromRel (fun i j : ι => 0 < A i j)).Adj i j → j ∈ P := by
    intro i hi j hAdj
    rcases (SimpleGraph.fromRel_adj _ _ _).mp hAdj with ⟨hij, hEdge⟩
    have hAji : 0 < A j i := by
      rcases hEdge with h | h
      · have hs := congr_fun (congr_fun hA_symm j) i
        rw [Matrix.transpose_apply] at hs
        rw [← hs]
        exact h
      · exact h
    have hNji : 0 < N j i := by
      have hji : j ≠ i := Ne.symm hij
      simp [N, hji, hoffB j i hji, hAji]
    have hcoord := congr_fun hshift j
    have hcoord' : (∑ k, N j k * r k) = (l + t) * r j := by
      simpa [Matrix.mulVec, dotProduct] using hcoord
    have hdecomp := Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ i)
      (fun k => N j k * r k)
    have hrest : 0 ≤ ∑ k ∈ Finset.univ \ {i}, N j k * r k := by
      apply Finset.sum_nonneg
      intro k hk
      exact mul_nonneg (hNnonneg j k) (abs_nonneg _)
    have hterm : 0 < N j i * r i := mul_pos hNji hi
    have hsumpos : 0 < ∑ k, N j k * r k := by
      rw [hdecomp]
      linarith
    rw [hcoord'] at hsumpos
    exact (mul_pos_iff_of_pos_left hlt).mp hsumpos
  obtain ⟨i0, hi0⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    apply hx_nonzero
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  have hiP : i0 ∈ P := by
    change 0 < |x i0|
    exact abs_pos.mpr hi0
  intro j
  exact reachable_mem_of_closed hclosed hiP (hG_conn.preconnected i0 j)

/- accepted add_to_file helper 7 -/
lemma top_eigenvector_positive_of_nonneg_connected {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (v x : ι → ℝ)
    (hA_symm : A.IsSymm) (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (hB_symm : B.IsSymm)
    (hoffB : ∀ i j, i ≠ j → B i j = A i j)
    (hG_conn : (SimpleGraph.fromRel (fun i j : ι => 0 < A i j)).Connected)
    {l : ℝ}
    (hl : ∀ μ : ℝ, (∃ u : ι → ℝ, u ≠ 0 ∧ B.mulVec u = μ • u) → μ ≤ l)
    (hx_nonzero : x ≠ 0)
    (hx_eigen : B.mulVec x = l • x)
    (hv_nonzero : v ≠ 0) (hv_nonneg : ∀ i, 0 ≤ v i)
    (hx_sign : 0 ≤ dotProduct v x) :
    ∀ i, 0 < x i := by
  classical
  let r : ι → ℝ := fun i => |x i|
  have hoff_nonneg : ∀ i j, i ≠ j → 0 ≤ B i j := by
    intro i j hij
    rw [hoffB i j hij]
    exact hA_nonneg i j
  have habs_eigen : B.mulVec r = l • r :=
    abs_eigen_of_top hB_symm hoff_nonneg hl hx_eigen
  have habs_pos : ∀ i, 0 < r i :=
    abs_pos_of_connected hA_symm hA_nonneg hoffB hG_conn hx_nonzero habs_eigen
  have hx_ne : ∀ i, x i ≠ 0 := by
    intro i hzero
    have hr := habs_pos i
    have hri : r i = |x i| := rfl
    rw [hri, hzero] at hr
    simp at hr
  have hnorm : dotProduct r r = dotProduct x x := by
    simp [r, dotProduct]
  have hqx : dotProduct x (B.mulVec x) = l * dotProduct x x := by
    rw [hx_eigen]
    simp [dotProduct_smul]
  have hqr : dotProduct r (B.mulVec r) = l * dotProduct r r := by
    rw [habs_eigen]
    simp [dotProduct_smul]
  have hq_eq : dotProduct x (B.mulVec x) = dotProduct r (B.mulVec r) := by
    rw [hqx, hqr, hnorm]
  have hterms := quad_abs_eq_terms hoff_nonneg x hq_eq
  by_cases hpos_exists : ∃ i, 0 < x i
  · rcases hpos_exists with ⟨i0, hi0⟩
    let P : Set ι := {i | 0 < x i}
    have hclosed : ∀ i ∈ P, ∀ j,
        (SimpleGraph.fromRel (fun i j : ι => 0 < A i j)).Adj i j → j ∈ P := by
      intro i hi j hAdj
      rcases (SimpleGraph.fromRel_adj _ _ _).mp hAdj with ⟨hij, hEdge⟩
      have hAij : 0 < A i j := by
        rcases hEdge with h | h
        · exact h
        · have hs := congr_fun (congr_fun hA_symm i) j
          rw [Matrix.transpose_apply] at hs
          rw [← hs]
          exact h
      have ht := hterms i j
      rw [hoffB i j hij] at ht
      have hprod : x i * x j = |x i| * |x j| := by
        have ht' : A i j * (x i * x j) = A i j * (|x i| * |x j|) := by
          ring_nf at ht ⊢
          linarith
        exact mul_left_cancel₀ (ne_of_gt hAij) ht'
      rw [abs_of_pos hi] at hprod
      have hxj_eq : x j = |x j| :=
        mul_left_cancel₀ (ne_of_gt hi) hprod
      have hxj_nonneg : 0 ≤ x j := by
        rw [hxj_eq]
        exact abs_nonneg _
      exact lt_of_le_of_ne hxj_nonneg (hx_ne j).symm
    intro j
    exact reachable_mem_of_closed hclosed hi0 (hG_conn.preconnected i0 j)
  · have hall_neg : ∀ i, x i < 0 := by
      intro i
      have hnotpos : ¬ 0 < x i := by
        intro hi
        exact hpos_exists ⟨i, hi⟩
      exact lt_of_le_of_ne (le_of_not_gt hnotpos) (hx_ne i)
    obtain ⟨i0, hvi0⟩ : ∃ i, 0 < v i := by
      by_contra h
      apply hv_nonzero
      funext i
      have hle := hv_nonneg i
      have hnot : ¬ 0 < v i := by
        intro hi
        exact h ⟨i, hi⟩
      exact le_antisymm (le_of_not_gt hnot) hle
    have hterms_nonpos : ∀ i ∈ Finset.univ, v i * x i ≤ 0 := by
      intro i hi
      exact mul_nonpos_of_nonneg_of_nonpos (hv_nonneg i) (hall_neg i).le
    have hsplit := Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ i0)
      (fun i => v i * x i)
    have hrest : (∑ i ∈ Finset.univ \ {i0}, v i * x i) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i hi
      exact hterms_nonpos i (Finset.mem_univ i)
    have hterm_neg : v i0 * x i0 < 0 :=
      mul_neg_of_pos_of_neg hvi0 (hall_neg i0)
    have hdot_neg : dotProduct v x < 0 := by
      simp only [dotProduct]
      rw [hsplit]
      linarith
    linarith

/- accepted add_to_file helper 8 -/
lemma quad_strict_on_positive_component {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A W : Matrix ι ι ℝ) (v y z : ι → ℝ)
    (σ d m l ε : ℝ)
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (hW_diag : W.IsDiag)
    (hσ : 0 < σ) (hd : 0 ≤ d) (hε : 0 < ε) (hml : m < l)
    (hv_nonneg : ∀ i, 0 ≤ v i) (hy_pos : ∀ i, 0 < y i)
    (hBz : ∀ i, ((A + W).mulVec z) i =
      m * z i + σ * d * v i + ε * (l - m) * y i)
    (SF U : Finset ι)
    (hSF : ∀ i, i ∈ SF ↔ 0 ≤ z i)
    (hUS : ∀ i ∈ U, i ∈ SF)
    (hclosed : ∀ i ∈ U, ∀ j ∈ SF, j ∉ U → A i j = 0)
    (hpos : ∃ i ∈ U, 0 < z i) :
    let u : ι → ℝ := fun i => if i ∈ U then z i else 0
    m * dotProduct u u < dotProduct u ((A + W).mulVec u) := by
  intro u
  let P : Finset ι := Uᶜ.filter fun j => j ∈ SF
  let N : Finset ι := Uᶜ.filter fun j => j ∉ SF
  have hq := dot_indicator_split (A + W) z U
  have hnorm : dotProduct u u = ∑ i ∈ U, z i * z i := by
    simp [u, dotProduct]
  have hsumB : (∑ i ∈ U, z i * ((A + W).mulVec z) i) =
      m * (∑ i ∈ U, z i * z i) +
      σ * d * (∑ i ∈ U, z i * v i) +
      ε * (l - m) * (∑ i ∈ U, z i * y i) := by
    simp only [hBz]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hcross_eq : (∑ i ∈ U, ∑ j ∈ Uᶜ, z i * (A + W) i j * z j) =
      ∑ i ∈ U, ∑ j ∈ Uᶜ, z i * A i j * z j := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have hij : i ≠ j := by
      intro h
      subst h
      exact (Finset.mem_compl.mp hj) hi
    have hWij : W i j = 0 := hW_diag hij
    simp [Matrix.add_apply, hWij]
  have hPzero : (∑ i ∈ U, ∑ j ∈ P, z i * A i j * z j) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    apply Finset.sum_eq_zero
    intro j hj
    have hjS : j ∈ SF := (Finset.mem_filter.mp hj).2
    have hjnotU : j ∉ U := Finset.mem_compl.mp (Finset.mem_filter.mp hj).1
    rw [hclosed i hi j hjS hjnotU]
    ring
  have hN_nonpos : (∑ i ∈ U, ∑ j ∈ N, z i * A i j * z j) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    apply Finset.sum_nonpos
    intro j hj
    have hjS : j ∉ SF := (Finset.mem_filter.mp hj).2
    have hzi : 0 ≤ z i := (hSF i).mp (hUS i hi)
    have hzj : z j < 0 := lt_of_not_ge ((hSF j).not.mp hjS)
    have hnonneg : 0 ≤ z i * A i j := mul_nonneg hzi (hA_nonneg i j)
    nlinarith
  have hcross_split : (∑ i ∈ U, ∑ j ∈ Uᶜ, z i * A i j * z j) =
      (∑ i ∈ U, ∑ j ∈ P, z i * A i j * z j) +
      (∑ i ∈ U, ∑ j ∈ N, z i * A i j * z j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hs := Finset.sum_filter_add_sum_filter_not Uᶜ (fun j => j ∈ SF)
      (fun j => z i * A i j * z j)
    simpa [P, N] using hs.symm
  have hcross_nonpos : (∑ i ∈ U, ∑ j ∈ Uᶜ, z i * (A + W) i j * z j) ≤ 0 := by
    rw [hcross_eq, hcross_split, hPzero]
    simpa using hN_nonpos
  have hT1 : 0 ≤ ∑ i ∈ U, z i * v i := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg ((hSF i).mp (hUS i hi)) (hv_nonneg i)
  have hT2 : 0 < ∑ i ∈ U, z i * y i := by
    rcases hpos with ⟨i0, hi0, hzi0⟩
    have hdecomp := Finset.sum_eq_sum_diff_singleton_add hi0
      (fun i => z i * y i)
    have hrest : 0 ≤ ∑ i ∈ U \ {i0}, z i * y i := by
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg ((hSF i).mp (hUS i (Finset.mem_sdiff.mp hi).1)) (hy_pos i).le
    have hterm : 0 < z i0 * y i0 := mul_pos hzi0 (hy_pos i0)
    rw [hdecomp]
    linarith
  have hP1 : 0 ≤ σ * d * (∑ i ∈ U, z i * v i) := by
    exact mul_nonneg (mul_nonneg hσ.le hd) hT1
  have hP2 : 0 < ε * (l - m) * (∑ i ∈ U, z i * y i) := by
    exact mul_pos (mul_pos hε (sub_pos.mpr hml)) hT2
  rw [hq, hnorm, hsumB]
  linarith

/- accepted add_to_file helper 9 -/
lemma dot_mulVec_comm_of_symm {ι : Type*} [Fintype ι]
    {B : Matrix ι ι ℝ} (hB : B.IsSymm) (u w : ι → ℝ) :
    dotProduct u (B.mulVec w) = dotProduct w (B.mulVec u) := by
  simp [dotProduct, Matrix.mulVec]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hs := congr_fun (congr_fun hB i) j
  rw [Matrix.transpose_apply] at hs
  ring_nf
  rw [hs]
  ring

/- accepted add_to_file helper 10 -/
lemma quad_combo_of_cross_zero {ι : Type*} [Fintype ι]
    {B : Matrix ι ι ℝ} (hB : B.IsSymm) (u w : ι → ℝ) (a b : ℝ)
    (hcross : dotProduct u (B.mulVec w) = 0) :
    dotProduct (a • u + b • w) (B.mulVec (a • u + b • w)) =
      a * a * dotProduct u (B.mulVec u) +
      b * b * dotProduct w (B.mulVec w) := by
  have hcross' : dotProduct w (B.mulVec u) = 0 := by
    rw [← dot_mulVec_comm_of_symm hB]
    exact hcross
  simp [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
    smul_dotProduct, dotProduct_smul, hcross, hcross']
  ring

lemma norm_combo_of_dot_zero {ι : Type*} [Fintype ι]
    (u w : ι → ℝ) (a b : ℝ)
    (hcross : dotProduct u w = 0) :
    dotProduct (a • u + b • w) (a • u + b • w) =
      a * a * dotProduct u u + b * b * dotProduct w w := by
  have hcross' : dotProduct w u = 0 := by
    rw [dotProduct_comm]
    exact hcross
  simp [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    hcross, hcross']
  ring

/- accepted add_to_file helper 11 -/
lemma two_component_contradiction {ι : Type*} [Fintype ι] [DecidableEq ι]
    {B M : Matrix ι ι ℝ} (v u w : ι → ℝ) (σ m a b : ℝ)
    (hB : B.IsSymm) (hM : M.IsSymm)
    (hMquad : ∀ z, dotProduct z (M.mulVec z) =
      dotProduct z (B.mulVec z) - σ * (dotProduct v z)^2)
    (hm_largest : ∀ μ : ℝ, (∃ r : ι → ℝ, r ≠ 0 ∧ M.mulVec r = μ • r) → μ ≤ m)
    (hcrossB : dotProduct u (B.mulVec w) = 0)
    (hdotuw : dotProduct u w = 0)
    (hdiffpos : 0 <
      a * a * (dotProduct u (B.mulVec u) - m * dotProduct u u) +
      b * b * (dotProduct w (B.mulVec w) - m * dotProduct w w))
    (hvorth : dotProduct v (a • u + b • w) = 0) :
    False := by
  let z : ι → ℝ := a • u + b • w
  have hqcombo : dotProduct z (B.mulVec z) =
      a * a * dotProduct u (B.mulVec u) +
      b * b * dotProduct w (B.mulVec w) :=
    quad_combo_of_cross_zero hB u w a b hcrossB
  have hnormcombo : dotProduct z z =
      a * a * dotProduct u u + b * b * dotProduct w w :=
    norm_combo_of_dot_zero u w a b hdotuw
  have hMle : dotProduct z (M.mulVec z) ≤ m * dotProduct z z :=
    quad_le_largest_of_symm hM hm_largest z
  have hM_eq_B : dotProduct z (M.mulVec z) = dotProduct z (B.mulVec z) := by
    have hq := hMquad z
    rw [hvorth] at hq
    simp at hq
    exact hq
  rw [hM_eq_B, hqcombo, hnormcombo] at hMle
  nlinarith

/- accepted add_to_file helper 12 -/
lemma addW_mulVec_apply_diag {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A W : Matrix ι ι ℝ) (hW : W.IsDiag) (z : ι → ℝ) (i : ι) :
    ((A + W).mulVec z) i = (∑ j, A i j * z j) + W i i * z i := by
  rw [Matrix.add_mulVec]
  simp [Matrix.mulVec, dotProduct]
  have hWsum : (∑ j, W i j * z j) = W i i * z i := by
    rw [← Finset.sum_subset (Finset.subset_univ {i})]
    · simp
    intro j hj hjnot
    have hij : i ≠ j := by
      intro h
      subst h
      exact hjnot (Finset.mem_singleton_self i)
    rw [hW hij]
    ring
  rw [hWsum]

/- accepted add_to_file helper 13 -/
lemma positive_component_has_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A W : Matrix ι ι ℝ) (v y z : ι → ℝ)
    (σ d m l ε : ℝ)
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (hW_diag : W.IsDiag)
    (hσ : 0 < σ) (hd : 0 ≤ d) (hε : 0 < ε) (hml : m < l)
    (hv_nonneg : ∀ i, 0 ≤ v i) (hy_pos : ∀ i, 0 < y i)
    (hBz : ∀ i, ((A + W).mulVec z) i =
      m * z i + σ * d * v i + ε * (l - m) * y i)
    (SF U : Finset ι)
    (hSF : ∀ i, i ∈ SF ↔ 0 ≤ z i)
    (hUS : ∀ i ∈ U, i ∈ SF)
    (hclosed : ∀ i ∈ U, ∀ j ∈ SF, j ∉ U → A i j = 0)
    (hU_nonempty : U.Nonempty)
    (hnotpos : ∀ i ∈ U, ¬ 0 < z i) :
    False := by
  rcases hU_nonempty with ⟨i0, hi0⟩
  have hzU : ∀ i ∈ U, z i = 0 := by
    intro i hi
    exact le_antisymm (le_of_not_gt (hnotpos i hi)) ((hSF i).mp (hUS i hi))
  have hzi0 : z i0 = 0 := hzU i0 hi0
  have hcoord := addW_mulVec_apply_diag A W hW_diag z i0
  have hAsum_nonpos : (∑ j, A i0 j * z j) ≤ 0 := by
    apply Finset.sum_nonpos
    intro j hj
    by_cases hjU : j ∈ U
    · rw [hzU j hjU]
      simp
    · by_cases hjS : j ∈ SF
      · rw [hclosed i0 hi0 j hjS hjU]
        simp
      · have hzj : z j < 0 := lt_of_not_ge ((hSF j).not.mp hjS)
        have hA : 0 ≤ A i0 j := hA_nonneg i0 j
        nlinarith
  have hB_nonpos : ((A + W).mulVec z) i0 ≤ 0 := by
    rw [hcoord, hzi0]
    simp
    exact hAsum_nonpos
  have hRHS_pos : 0 < m * z i0 + σ * d * v i0 + ε * (l - m) * y i0 := by
    rw [hzi0]
    have hfirst : 0 ≤ σ * d * v i0 :=
      mul_nonneg (mul_nonneg hσ.le hd) (hv_nonneg i0)
    have hsecond : 0 < ε * (l - m) * y i0 :=
      mul_pos (mul_pos hε (sub_pos.mpr hml)) (hy_pos i0)
    linarith
  have heq := hBz i0
  linarith

/- accepted add_to_file helper 14 -/
lemma dot_pos_of_nonneg_nonzero_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {v y : ι → ℝ} (hv_nonzero : v ≠ 0) (hv_nonneg : ∀ i, 0 ≤ v i)
    (hy_pos : ∀ i, 0 < y i) :
    0 < dotProduct v y := by
  classical
  obtain ⟨i0, hvi0⟩ : ∃ i, 0 < v i := by
    by_contra h
    apply hv_nonzero
    funext i
    have hle := hv_nonneg i
    have hnot : ¬ 0 < v i := by
      intro hi
      exact h ⟨i, hi⟩
    exact le_antisymm (le_of_not_gt hnot) hle
  have hsplit := Finset.sum_eq_sum_diff_singleton_add (Finset.mem_univ i0)
    (fun i => v i * y i)
  have hrest : 0 ≤ ∑ i ∈ Finset.univ \ {i0}, v i * y i := by
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hv_nonneg i) (hy_pos i).le
  have hterm : 0 < v i0 * y i0 := mul_pos hvi0 (hy_pos i0)
  simp only [dotProduct]
  rw [hsplit]
  linarith

/- accepted add_to_file helper 15 -/
lemma Matrix.vecMulVec_isSymm {n : Type*} (v : n → ℝ) :
    (Matrix.vecMulVec v v).IsSymm := by
  ext i j
  simp [Matrix.vecMulVec, mul_comm]

/- accepted add_to_file helper 16 -/
lemma rank_quad {ι : Type*} [Fintype ι] (B : Matrix ι ι ℝ)
    (v z : ι → ℝ) (σ : ℝ) :
    dotProduct z ((B - σ • Matrix.vecMulVec v v).mulVec z) =
      dotProduct z (B.mulVec z) - σ * (dotProduct v z)^2 := by
  have hvv : (Matrix.vecMulVec v v).mulVec z = (dotProduct v z) • v := by
    simp [Matrix.vecMulVec_mulVec]
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hvv]
  simp only [dotProduct_sub, dotProduct_smul]
  rw [dotProduct_comm z v]
  rw [smul_eq_mul, smul_eq_mul]
  ring

/- accepted add_to_file helper 17 -/
lemma two_reach_components_contradiction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A W M : Matrix ι ι ℝ) (v y z : ι → ℝ)
    (σ d m l ε : ℝ)
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (hW_diag : W.IsDiag)
    (hB_symm : (A + W).IsSymm) (hM_symm : M.IsSymm)
    (hMquad : ∀ r, dotProduct r (M.mulVec r) =
      dotProduct r ((A + W).mulVec r) - σ * (dotProduct v r)^2)
    (hm_largest : ∀ μ : ℝ, (∃ r : ι → ℝ, r ≠ 0 ∧ M.mulVec r = μ • r) → μ ≤ m)
    (hσ : 0 < σ) (hd : 0 ≤ d) (hε : 0 < ε) (hml : m < l)
    (hv_nonneg : ∀ i, 0 ≤ v i) (hy_pos : ∀ i, 0 < y i)
    (hBz : ∀ i, ((A + W).mulVec z) i =
      m * z i + σ * d * v i + ε * (l - m) * y i)
    (SF U D : Finset ι)
    (hSF : ∀ i, i ∈ SF ↔ 0 ≤ z i)
    (hUS : ∀ i ∈ U, i ∈ SF) (hDS : ∀ i ∈ D, i ∈ SF)
    (hclosedU : ∀ i ∈ U, ∀ j ∈ SF, j ∉ U → A i j = 0)
    (hclosedD : ∀ i ∈ D, ∀ j ∈ SF, j ∉ D → A i j = 0)
    (hdisjoint : ∀ i, ¬ (i ∈ U ∧ i ∈ D))
    (hU_nonempty : U.Nonempty) (hD_nonempty : D.Nonempty) :
    False := by
  classical
  let u : ι → ℝ := fun i => if i ∈ U then z i else 0
  let w : ι → ℝ := fun i => if i ∈ D then z i else 0
  have hUpos : ∃ i ∈ U, 0 < z i := by
    by_contra hnot
    have hnotpos : ∀ i ∈ U, ¬ 0 < z i := by
      intro i hi hzi
      exact hnot ⟨i, hi, hzi⟩
    exact positive_component_has_positive A W v y z σ d m l ε
      hA_nonneg hW_diag hσ hd hε hml hv_nonneg hy_pos hBz SF U
      hSF hUS hclosedU hU_nonempty hnotpos
  have hDpos : ∃ i ∈ D, 0 < z i := by
    by_contra hnot
    have hnotpos : ∀ i ∈ D, ¬ 0 < z i := by
      intro i hi hzi
      exact hnot ⟨i, hi, hzi⟩
    exact positive_component_has_positive A W v y z σ d m l ε
      hA_nonneg hW_diag hσ hd hε hml hv_nonneg hy_pos hBz SF D
      hSF hDS hclosedD hD_nonempty hnotpos
  have hq_u : m * dotProduct u u < dotProduct u ((A + W).mulVec u) :=
    quad_strict_on_positive_component A W v y z σ d m l ε
      hA_nonneg hW_diag hσ hd hε hml hv_nonneg hy_pos hBz SF U
      hSF hUS hclosedU hUpos
  have hq_w : m * dotProduct w w < dotProduct w ((A + W).mulVec w) :=
    quad_strict_on_positive_component A W v y z σ d m l ε
      hA_nonneg hW_diag hσ hd hε hml hv_nonneg hy_pos hBz SF D
      hSF hDS hclosedD hDpos
  have hdiff_u : 0 < dotProduct u ((A + W).mulVec u) - m * dotProduct u u := by linarith
  have hdiff_w : 0 < dotProduct w ((A + W).mulVec w) - m * dotProduct w w := by linarith
  have hdotuw : dotProduct u w = 0 := by
    simp [u, w, dotProduct]
    apply Finset.sum_eq_zero
    intro i hi
    exact False.elim (hdisjoint i
      ⟨(Finset.mem_inter.mp hi).2, (Finset.mem_inter.mp hi).1⟩)
  have hBzero : ∀ i ∈ U, ∀ j ∈ D, (A + W) i j = 0 := by
    intro i hi j hj
    have hij : i ≠ j := by
      intro h
      subst h
      exact hdisjoint i ⟨hi, hj⟩
    have hAij : A i j = 0 := hclosedU i hi j (hDS j hj) (by
      intro hji
      exact hdisjoint j ⟨hji, hj⟩)
    have hWij : W i j = 0 := hW_diag hij
    simp [Matrix.add_apply, hAij, hWij]
  have hcrossB : dotProduct u ((A + W).mulVec w) = 0 := by
    simp [u, w, dotProduct, Matrix.mulVec]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro j hj
    have hzero : A i j + W i j = 0 := by
      simpa [Matrix.add_apply] using hBzero i hi j hj
    rw [hzero]
    simp
  have hvu_nonneg : 0 ≤ dotProduct v u := by
    have h : dotProduct v u = ∑ i ∈ U, v i * z i := by
      simp [u, dotProduct]
    rw [h]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hv_nonneg i) ((hSF i).mp (hUS i hi))
  have hvw_nonneg : 0 ≤ dotProduct v w := by
    have h : dotProduct v w = ∑ i ∈ D, v i * z i := by
      simp [w, dotProduct]
    rw [h]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hv_nonneg i) ((hSF i).mp (hDS i hi))
  by_cases hboth : dotProduct v u = 0 ∧ dotProduct v w = 0
  · have hvorth : dotProduct v ((1 : ℝ) • u + (1 : ℝ) • w) = 0 := by
      simp [hboth.1, hboth.2]
    have hdiffpos : 0 <
        (1 : ℝ) * 1 * (dotProduct u ((A + W).mulVec u) - m * dotProduct u u) +
        (1 : ℝ) * 1 * (dotProduct w ((A + W).mulVec w) - m * dotProduct w w) := by
      nlinarith
    exact two_component_contradiction v u w σ m 1 1 hB_symm hM_symm
      hMquad hm_largest hcrossB hdotuw hdiffpos hvorth
  · have hune : dotProduct v u ≠ 0 ∨ dotProduct v w ≠ 0 := by
      by_contra h
      push Not at h
      exact hboth h
    let a : ℝ := dotProduct v w
    let b : ℝ := -dotProduct v u
    have hvorth : dotProduct v (a • u + b • w) = 0 := by
      simp [a, b]
      ring
    rcases hune with hu_ne | hw_ne
    · have hbne : b ≠ 0 := by
        simp [b, hu_ne]
      have hbsq : 0 < b * b := by nlinarith [sq_pos_of_ne_zero hbne]
      have hterm1 : 0 ≤ a * a * (dotProduct u ((A + W).mulVec u) - m * dotProduct u u) := by
        have hsqa : 0 ≤ a * a := by nlinarith [sq_nonneg a]
        exact mul_nonneg hsqa hdiff_u.le
      have hterm2 : 0 < b * b * (dotProduct w ((A + W).mulVec w) - m * dotProduct w w) :=
        mul_pos hbsq hdiff_w
      have hdiffpos : 0 <
          a * a * (dotProduct u ((A + W).mulVec u) - m * dotProduct u u) +
          b * b * (dotProduct w ((A + W).mulVec w) - m * dotProduct w w) := by
        linarith
      exact two_component_contradiction v u w σ m a b hB_symm hM_symm
        hMquad hm_largest hcrossB hdotuw hdiffpos hvorth
    · have hane : a ≠ 0 := by
        simp [a, hw_ne]
      have hasq : 0 < a * a := by nlinarith [sq_pos_of_ne_zero hane]
      have hterm1 : 0 < a * a * (dotProduct u ((A + W).mulVec u) - m * dotProduct u u) :=
        mul_pos hasq hdiff_u
      have hterm2 : 0 ≤ b * b * (dotProduct w ((A + W).mulVec w) - m * dotProduct w w) := by
        have hsqb : 0 ≤ b * b := by nlinarith [sq_nonneg b]
        exact mul_nonneg hsqb hdiff_w.le
      have hdiffpos : 0 <
          a * a * (dotProduct u ((A + W).mulVec u) - m * dotProduct u u) +
          b * b * (dotProduct w ((A + W).mulVec w) - m * dotProduct w w) := by
        linarith
      exact two_component_contradiction v u w σ m a b hB_symm hM_symm
        hMquad hm_largest hcrossB hdotuw hdiffpos hvorth

/- accepted add_to_file helper 18 -/
lemma connected_nodal_positive_epsilon
    (n : ℕ) (hn : 1 ≤ n)
    (A W : Matrix (Fin n) (Fin n) ℝ)
    (v x y : Fin n → ℝ) (σ m l ε : ℝ)
    (hA_symm : A.IsSymm)
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (hG_conn : (SimpleGraph.fromRel (fun i j : Fin n => 0 < A i j)).Connected)
    (hW_diag : W.IsDiag)
    (hv_nonzero : v ≠ 0)
    (hv_nonneg : ∀ i, 0 ≤ v i)
    (hσ : 0 < σ)
    (hx_nonzero : x ≠ 0)
    (hx_eigen : (A + W - σ • Matrix.vecMulVec v v).mulVec x = m • x)
    (hm_largest : ∀ μ : ℝ, (∃ u : Fin n → ℝ, u ≠ 0 ∧
      (A + W - σ • Matrix.vecMulVec v v).mulVec u = μ • u) → μ ≤ m)
    (hx_sign : 0 ≤ dotProduct v x)
    (hy_pos : ∀ i, 0 < y i)
    (hy_eigen : (A + W).mulVec y = l • y)
    (hl_largest : ∀ μ : ℝ, (∃ u : Fin n → ℝ, u ≠ 0 ∧
      (A + W).mulVec u = μ • u) → μ ≤ l)
    (hml_lt : m < l) (hε : 0 < ε) :
    ((SimpleGraph.fromRel (fun i j : Fin n => 0 < A i j)).induce
      {i | 0 ≤ x i + ε * y i}).Connected := by
  classical
  let B : Matrix (Fin n) (Fin n) ℝ := A + W
  let M : Matrix (Fin n) (Fin n) ℝ := B - σ • Matrix.vecMulVec v v
  let d : ℝ := dotProduct v x
  let z : Fin n → ℝ := x + ε • y
  let G : SimpleGraph (Fin n) := SimpleGraph.fromRel (fun i j : Fin n => 0 < A i j)
  let Sset : Set (Fin n) := {i | 0 ≤ z i}
  let H : SimpleGraph Sset := G.induce Sset
  let SF : Finset (Fin n) := Finset.univ.filter fun i => i ∈ Sset
  have hd : 0 ≤ d := hx_sign
  have hB_symm : B.IsSymm := hA_symm.add hW_diag.isSymm
  have hM_symm : M.IsSymm := hB_symm.sub ((Matrix.vecMulVec_isSymm v).smul σ)
  have hMx : M.mulVec x = B.mulVec x - (σ * d) • v := by
    simp [M, B, d, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.vecMulVec_mulVec, smul_smul]
  have hBx : B.mulVec x = m • x + (σ * d) • v := by
    have h : B.mulVec x - (σ * d) • v = m • x := by
      rw [← hMx]
      exact hx_eigen
    funext i
    have hi := congr_fun h i
    simp at hi ⊢
    ring_nf at hi ⊢
    linarith
  have hBz_vec : B.mulVec z = m • z + (σ * d) • v + (ε * (l - m)) • y := by
    simp [z, B, Matrix.mulVec_add, Matrix.mulVec_smul, hBx, hy_eigen]
    funext i
    simp
    ring
  have hBz : ∀ i, (B.mulVec z) i =
      m * z i + σ * d * v i + ε * (l - m) * y i := by
    intro i
    have hi := congr_fun hBz_vec i
    simpa [mul_assoc] using hi
  have hSF : ∀ i, i ∈ SF ↔ 0 ≤ z i := by
    intro i
    simp [SF, Sset]
  by_cases hSuniv : Sset = Set.univ
  · change (G.induce Sset).Connected
    rw [hSuniv]
    exact G.induceUnivIso.connected_iff.mpr hG_conn
  · have hS_nonempty : Nonempty Sset := by
      have hvy : 0 < dotProduct v y :=
        dot_pos_of_nonneg_nonzero_pos hv_nonzero hv_nonneg hy_pos
      have hvz : 0 < dotProduct v z := by
        have h : dotProduct v z = d + ε * dotProduct v y := by
          simp [z, d, dotProduct_add, dotProduct_smul]
        rw [h]
        nlinarith
      have hex : ∃ i, 0 < v i * z i := by
        have hlt : (∑ i : Fin n, (0 : ℝ)) < ∑ i, v i * z i := by
          simpa [dotProduct] using hvz
        have := Finset.exists_lt_of_sum_lt (s := Finset.univ)
          (f := fun _ : Fin n => (0 : ℝ)) (g := fun i => v i * z i) hlt
        simpa using this
      rcases hex with ⟨i, hi⟩
      have hzi : 0 < z i := pos_of_mul_pos_right hi (hv_nonneg i)
      exact ⟨⟨i, hzi.le⟩⟩
    have hpre : H.Preconnected := by
      intro a b
      by_contra hab
      let Uset : Set (Fin n) := {i | ∃ hi : i ∈ Sset, H.Reachable a ⟨i, hi⟩}
      let Dset : Set (Fin n) := {i | ∃ hi : i ∈ Sset, H.Reachable b ⟨i, hi⟩}
      let U : Finset (Fin n) := Uset.toFinset
      let D : Finset (Fin n) := Dset.toFinset
      have haU : a.1 ∈ U := by
        simp [U, Uset, a.property]
      have hbD : b.1 ∈ D := by
        simp [D, Dset, b.property]
      have hUD_disjoint : ∀ i, ¬ (i ∈ U ∧ i ∈ D) := by
        intro i h
        rcases h with ⟨hiU, hiD⟩
        have hiU' : i ∈ Uset := by simpa [U] using hiU
        have hiD' : i ∈ Dset := by simpa [D] using hiD
        rcases hiU' with ⟨hiSU, hai⟩
        rcases hiD' with ⟨hiSD, hbi⟩
        have hbi' : H.Reachable b ⟨i, hiSU⟩ := by
          convert hbi
        exact hab (hai.trans hbi'.symm)
      have hclosedU : ∀ i ∈ U, ∀ j ∈ SF, j ∉ U → A i j = 0 := by
        intro i hi j hjS hjU
        by_contra hAne
        have hAij : 0 < A i j := lt_of_le_of_ne (hA_nonneg i j) (Ne.symm hAne)
        have hiU' : i ∈ Uset := by simpa [U] using hi
        rcases hiU' with ⟨hiS, hai⟩
        have hij : i ≠ j := by
          intro h
          subst h
          exact hjU hi
        have hGij : G.Adj i j := by
          show (SimpleGraph.fromRel (fun i j : Fin n => 0 < A i j)).Adj i j
          rw [SimpleGraph.fromRel_adj]
          exact ⟨hij, Or.inl hAij⟩
        have hjSset : j ∈ Sset := by simpa [SF, Sset] using hjS
        have hHij : H.Adj ⟨i, hiS⟩ ⟨j, hjSset⟩ := by
          show (G.induce Sset).Adj ⟨i, hiS⟩ ⟨j, hjSset⟩
          rw [SimpleGraph.induce_adj]
          exact hGij
        have haj : H.Reachable a ⟨j, hjSset⟩ :=
          hai.trans ⟨SimpleGraph.Walk.cons hHij SimpleGraph.Walk.nil⟩
        have hjUset : j ∈ Uset := ⟨hjSset, haj⟩
        exact hjU (by simpa [U] using hjUset)
      have hclosedD : ∀ i ∈ D, ∀ j ∈ SF, j ∉ D → A i j = 0 := by
        intro i hi j hjS hjD
        by_contra hAne
        have hAij : 0 < A i j := lt_of_le_of_ne (hA_nonneg i j) (Ne.symm hAne)
        have hiD' : i ∈ Dset := by simpa [D] using hi
        rcases hiD' with ⟨hiS, hbi⟩
        have hij : i ≠ j := by
          intro h
          subst h
          exact hjD hi
        have hGij : G.Adj i j := by
          show (SimpleGraph.fromRel (fun i j : Fin n => 0 < A i j)).Adj i j
          rw [SimpleGraph.fromRel_adj]
          exact ⟨hij, Or.inl hAij⟩
        have hjSset : j ∈ Sset := by simpa [SF, Sset] using hjS
        have hHij : H.Adj ⟨i, hiS⟩ ⟨j, hjSset⟩ := by
          show (G.induce Sset).Adj ⟨i, hiS⟩ ⟨j, hjSset⟩
          rw [SimpleGraph.induce_adj]
          exact hGij
        have hbj : H.Reachable b ⟨j, hjSset⟩ :=
          hbi.trans ⟨SimpleGraph.Walk.cons hHij SimpleGraph.Walk.nil⟩
        have hjDset : j ∈ Dset := ⟨hjSset, hbj⟩
        exact hjD (by simpa [D] using hjDset)
      have hUS : ∀ i ∈ U, i ∈ SF := by
        intro i hi
        have hiU' : i ∈ Uset := by simpa [U] using hi
        rcases hiU' with ⟨hiS, _⟩
        exact (hSF i).mpr hiS
      have hDS : ∀ i ∈ D, i ∈ SF := by
        intro i hi
        have hiD' : i ∈ Dset := by simpa [D] using hi
        rcases hiD' with ⟨hiS, _⟩
        exact (hSF i).mpr hiS
      have hMquad : ∀ r, dotProduct r (M.mulVec r) =
          dotProduct r ((A + W).mulVec r) - σ * (dotProduct v r)^2 := by
        intro r
        simpa [M, B] using rank_quad (A + W) v r σ
      have hm_largest' : ∀ μ : ℝ, (∃ r : Fin n → ℝ, r ≠ 0 ∧
          M.mulVec r = μ • r) → μ ≤ m := by
        intro μ hμ
        rcases hμ with ⟨r, hr, heig⟩
        exact hm_largest μ ⟨r, hr, by simpa [M, B] using heig⟩
      exact two_reach_components_contradiction A W M v y z σ d m l ε
        hA_nonneg hW_diag hB_symm hM_symm hMquad hm_largest'
        hσ hd hε hml_lt hv_nonneg hy_pos
        (by simpa [B] using hBz) SF U D hSF hUS hDS hclosedU hclosedD
        hUD_disjoint ⟨a.1, haU⟩ ⟨b.1, hbD⟩
    exact SimpleGraph.Connected.mk hpre

/- verified submission -/
theorem connected_nodal_domain_of_leading_eigenvector
    (n : ℕ) (hn : 1 ≤ n)
    (A W : Matrix (Fin n) (Fin n) ℝ)
    (v x y : Fin n → ℝ) (σ m l : ℝ)
    (hA_symm : A.IsSymm)
    (hA_nonneg : ∀ i j, 0 ≤ A i j)
    (hG_conn : (SimpleGraph.fromRel (fun i j : Fin n => 0 < A i j)).Connected)
    (hW_diag : W.IsDiag)
    (hv_nonzero : v ≠ 0)
    (hv_nonneg : ∀ i, 0 ≤ v i)
    (hσ : 0 < σ)
    (hx_nonzero : x ≠ 0)
    (hx_eigen : (A + W - σ • Matrix.vecMulVec v v).mulVec x = m • x)
    (hm_largest : ∀ μ : ℝ, (∃ u : Fin n → ℝ, u ≠ 0 ∧
      (A + W - σ • Matrix.vecMulVec v v).mulVec u = μ • u) → μ ≤ m)
    (hx_sign : 0 ≤ dotProduct v x)
    (hy_pos : ∀ i, 0 < y i)
    (hy_eigen : (A + W).mulVec y = l • y)
    (hl_largest : ∀ μ : ℝ, (∃ u : Fin n → ℝ, u ≠ 0 ∧
      (A + W).mulVec u = μ • u) → μ ≤ l) :
    ∀ ε : ℝ, 0 ≤ ε →
      ((SimpleGraph.fromRel (fun i j : Fin n => 0 < A i j)).induce
        {i | 0 ≤ x i + ε * y i}).Connected := by
  classical
  let B : Matrix (Fin n) (Fin n) ℝ := A + W
  let M : Matrix (Fin n) (Fin n) ℝ := B - σ • Matrix.vecMulVec v v
  let d : ℝ := dotProduct v x
  have hd : 0 ≤ d := hx_sign
  have hB_symm : B.IsSymm := hA_symm.add hW_diag.isSymm
  have hM_symm : M.IsSymm := hB_symm.sub ((Matrix.vecMulVec_isSymm v).smul σ)
  have hnormx : 0 < dotProduct x x := by
    have h := (Matrix.dotProduct_self_star_pos_iff (v := x)).mpr hx_nonzero
    simpa using h
  have hMx : M.mulVec x = B.mulVec x - (σ * d) • v := by
    simp [M, B, d, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.vecMulVec_mulVec, smul_smul]
  have hBx : B.mulVec x = m • x + (σ * d) • v := by
    have h : B.mulVec x - (σ * d) • v = m • x := by
      rw [← hMx]
      exact hx_eigen
    funext i
    have hi := congr_fun h i
    simp at hi ⊢
    ring_nf at hi ⊢
    linarith
  have hqBx : dotProduct x (B.mulVec x) =
      m * dotProduct x x + σ * d^2 := by
    rw [hBx]
    simp [dotProduct_add, dotProduct_smul, dotProduct_comm x v, d]
    ring
  have hBupper := quad_le_largest_of_symm hB_symm hl_largest x
  rw [hqBx] at hBupper
  have hml : m ≤ l := by
    nlinarith [sq_nonneg d, hσ.le, hnormx]
  by_cases hEq : l = m
  · have hdzero : d = 0 := by
      subst hEq
      have hsd : σ * d^2 ≤ 0 := by linarith
      have hs : d^2 ≤ 0 := nonpos_of_mul_nonpos_right hsd hσ
      nlinarith [sq_nonneg d]
    have hBx_top : B.mulVec x = l • x := by
      subst hEq
      rw [hdzero] at hBx
      simpa using hBx
    have hoffB : ∀ i j, i ≠ j → B i j = A i j := by
      intro i j hij
      simp [B, hW_diag hij]
    have hx_pos : ∀ i, 0 < x i :=
      top_eigenvector_positive_of_nonneg_connected v x hA_symm hA_nonneg
        hB_symm hoffB hG_conn hl_largest hx_nonzero hBx_top
        hv_nonzero hv_nonneg hx_sign
    intro ε hε
    have hS : {i : Fin n | 0 ≤ x i + ε * y i} = Set.univ := by
      ext i
      simp
      exact add_nonneg (hx_pos i).le (mul_nonneg hε (hy_pos i).le)
    rw [hS]
    exact (SimpleGraph.induceUnivIso
      (SimpleGraph.fromRel (fun i j : Fin n => 0 < A i j))).connected_iff.mpr hG_conn
  · have hml_lt : m < l := lt_of_le_of_ne hml (by
      intro h
      exact hEq h.symm)
    intro ε hε
    by_cases hεpos : 0 < ε
    · exact connected_nodal_positive_epsilon n hn A W v x y σ m l ε
        hA_symm hA_nonneg hG_conn hW_diag hv_nonzero hv_nonneg hσ
        hx_nonzero hx_eigen hm_largest hx_sign hy_pos hy_eigen hl_largest
        hml_lt hεpos
    · have hεzero : ε = 0 := le_antisymm (le_of_not_gt hεpos) hε
      let S0 : Set (Fin n) := {i | 0 ≤ x i}
      by_cases hS0univ : S0 = Set.univ
      · have hS : {i : Fin n | 0 ≤ x i + ε * y i} = Set.univ := by
          rw [hεzero]
          simpa [S0] using hS0univ
        rw [hS]
        exact (SimpleGraph.induceUnivIso
          (SimpleGraph.fromRel (fun i j : Fin n => 0 < A i j))).connected_iff.mpr hG_conn
      · obtain ⟨η, hηpos, hη⟩ : ∃ η > 0, ∀ i, x i < 0 → x i + η * y i < 0 := by
          let N : Set (Fin n) := {i | x i < 0}
          have hneg : ∀ p : N, (x p.1) / (y p.1) < 0 := by
            intro p
            exact div_neg_of_neg_of_pos p.property (hy_pos p.1)
          obtain ⟨η, hηpos, hη⟩ :=
            Pi.exists_forall_pos_add_lt (x := fun p : N => x p.1 / y p.1)
              (y := fun _ : N => (0 : ℝ)) hneg
          refine ⟨η, hηpos, ?_⟩
          intro i hi
          have hp := hη ⟨i, hi⟩
          have hmul := mul_neg_of_neg_of_pos hp (hy_pos i)
          have heq : (x i / y i + η) * y i = x i + η * y i := by
            field_simp [ne_of_gt (hy_pos i)]
          rw [heq] at hmul
          simpa using hmul
        have hconnη := connected_nodal_positive_epsilon n hn A W v x y σ m l η
          hA_symm hA_nonneg hG_conn hW_diag hv_nonzero hv_nonneg hσ
          hx_nonzero hx_eigen hm_largest hx_sign hy_pos hy_eigen hl_largest
          hml_lt hηpos
        have hSetEq : {i : Fin n | 0 ≤ x i + (0 : ℝ) * y i} =
            {i : Fin n | 0 ≤ x i + η * y i} := by
          ext i
          constructor
          · intro hi
            have hxi : 0 ≤ x i := by simpa using hi
            exact add_nonneg hxi (mul_nonneg hηpos.le (hy_pos i).le)
          · intro hi
            by_contra hnot
            have hxi : x i < 0 := lt_of_not_ge (by
              intro hxnonneg
              exact hnot (by simpa using hxnonneg))
            exact (hη i hxi).not_ge hi
        rw [hεzero, hSetEq]
        exact hconnη


#check_dependency_graph "connected_nodal_domain_of_leading_eigenvector" against "{\"edges\":[{\"conclusion\":{\"name\":\"hB_symm\",\"statement\":\"B.IsSymm\"},\"graphEdgeId\":\"h_002_hb_symm\",\"premises\":[{\"name\":\"hA_symm\",\"statement\":\"A.IsSymm\"},{\"name\":\"hW_diag\",\"statement\":\"W.IsDiag\"}],\"rawEdgeId\":\"telescope_28\"},{\"conclusion\":{\"name\":\"hnormx\",\"statement\":\"0 < x ⬝ᵥ x\"},\"graphEdgeId\":\"h_004_hnormx\",\"premises\":[{\"name\":\"hx_nonzero\",\"statement\":\"x ≠ 0\"}],\"rawEdgeId\":\"telescope_30\"},{\"conclusion\":{\"name\":\"hMx\",\"statement\":\"M.mulVec x = B.mulVec x - (σ * d) • v\"},\"graphEdgeId\":\"h_005_hmx\",\"premises\":[],\"rawEdgeId\":\"telescope_31\"},{\"conclusion\":{\"name\":\"hBx\",\"statement\":\"B.mulVec x = m • x + (σ * d) • v\"},\"graphEdgeId\":\"h_006_hbx\",\"premises\":[{\"name\":\"hx_eigen\",\"statement\":\"(A + W - σ • Matrix.vecMulVec v v).mulVec x = m • x\"},{\"name\":\"hMx\",\"statement\":\"M.mulVec x = B.mulVec x - (σ * d) • v\"}],\"rawEdgeId\":\"telescope_32\"},{\"conclusion\":{\"name\":\"hBupper\",\"statement\":\"x ⬝ᵥ B.mulVec x ≤ l * x ⬝ᵥ x\"},\"graphEdgeId\":\"h_008_hbupper\",\"premises\":[{\"name\":\"hl_largest\",\"statement\":\"∀ (μ : ℝ), (∃ u, u ≠ 0 ∧ (A + W).mulVec u = μ • u) → μ ≤ l\"},{\"name\":\"hB_symm\",\"statement\":\"B.IsSymm\"}],\"rawEdgeId\":\"telescope_34\"},{\"conclusion\":{\"name\":\"hqBx\",\"statement\":\"x ⬝ᵥ B.mulVec x = m * x ⬝ᵥ x + σ * d ^ 2\"},\"graphEdgeId\":\"h_007_hqbx\",\"premises\":[{\"name\":\"hBx\",\"statement\":\"B.mulVec x = m • x + (σ * d) • v\"}],\"rawEdgeId\":\"telescope_33\"},{\"conclusion\":{\"name\":\"hml\",\"statement\":\"m ≤ l\"},\"graphEdgeId\":\"h_009_hml\",\"premises\":[{\"name\":\"hσ\",\"statement\":\"0 < σ\"},{\"name\":\"hnormx\",\"statement\":\"0 < x ⬝ᵥ x\"},{\"name\":\"hqBx\",\"statement\":\"x ⬝ᵥ B.mulVec x = m * x ⬝ᵥ x + σ * d ^ 2\"},{\"name\":\"hBupper\",\"statement\":\"x ⬝ᵥ B.mulVec x ≤ l * x ⬝ᵥ x\"}],\"rawEdgeId\":\"telescope_35\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∀ (ε : ℝ), 0 ≤ ε → (SimpleGraph.induce {i | 0 ≤ x i + ε * y i} (SimpleGraph.fromRel fun i j => 0 < A i j)).Connected\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hn\",\"statement\":\"1 ≤ n\"},{\"name\":\"hA_symm\",\"statement\":\"A.IsSymm\"},{\"name\":\"hA_nonneg\",\"statement\":\"∀ (i j : Fin n), 0 ≤ A i j\"},{\"name\":\"hG_conn\",\"statement\":\"(SimpleGraph.fromRel fun i j => 0 < A i j).Connected\"},{\"name\":\"hW_diag\",\"statement\":\"W.IsDiag\"},{\"name\":\"hv_nonzero\",\"statement\":\"v ≠ 0\"},{\"name\":\"hv_nonneg\",\"statement\":\"∀ (i : Fin n), 0 ≤ v i\"},{\"name\":\"hσ\",\"statement\":\"0 < σ\"},{\"name\":\"hx_nonzero\",\"statement\":\"x ≠ 0\"},{\"name\":\"hx_eigen\",\"statement\":\"(A + W - σ • Matrix.vecMulVec v v).mulVec x = m • x\"},{\"name\":\"hm_largest\",\"statement\":\"∀ (μ : ℝ), (∃ u, u ≠ 0 ∧ (A + W - σ • Matrix.vecMulVec v v).mulVec u = μ • u) → μ ≤ m\"},{\"name\":\"hx_sign\",\"statement\":\"0 ≤ v ⬝ᵥ x\"},{\"name\":\"hy_pos\",\"statement\":\"∀ (i : Fin n), 0 < y i\"},{\"name\":\"hy_eigen\",\"statement\":\"(A + W).mulVec y = l • y\"},{\"name\":\"hl_largest\",\"statement\":\"∀ (μ : ℝ), (∃ u, u ≠ 0 ∧ (A + W).mulVec u = μ • u) → μ ≤ l\"},{\"name\":\"hB_symm\",\"statement\":\"B.IsSymm\"},{\"name\":\"hBx\",\"statement\":\"B.mulVec x = m • x + (σ * d) • v\"},{\"name\":\"hqBx\",\"statement\":\"x ⬝ᵥ B.mulVec x = m * x ⬝ᵥ x + σ * d ^ 2\"},{\"name\":\"hBupper\",\"statement\":\"x ⬝ᵥ B.mulVec x ≤ l * x ⬝ᵥ x\"},{\"name\":\"hml\",\"statement\":\"m ≤ l\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p3112_connected_nodal_domain_of_leading_eigenvec\",\"reconstructedProofSha256\":\"235e94dde3532449f95ea5f6668c983cfdbcd1de853e57639b4f5cb26ffe128e\",\"selectedEdgeCount\":8,\"theoremName\":\"connected_nodal_domain_of_leading_eigenvector\",\"topologySha256\":\"c39b7c8c6116dc2fd9aec5c5f12c8be8cfbb66665a78d6ee1e6b4f19fc34ca34\"}"
