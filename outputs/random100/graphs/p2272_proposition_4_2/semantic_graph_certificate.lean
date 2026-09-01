import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p2272_proposition_4_2
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 600b198cacdc3ae08bbac9a54879a718992687cf4b769380a7ffaa2e3faaa668
-- reconstructed_proof_sha256: b1141185f1b9f649d68bf75e20f59455a2c82fcca1cb1918e2f4b914ff3fcbe2
-- selected_edge_count: 1

/- accepted add_to_file helper 1 -/
lemma gsp_inv_aux {l : Type*} [DecidableEq l] [Fintype l] {R : Type*} [CommRing R]
    (g : Matrix.GeneralLinearGroup (l ⊕ l) R) {μ : Rˣ}
    (h : (g : Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
        (g : Matrix (l ⊕ l) (l ⊕ l) R) = (μ : R) • Matrix.J l R) :
    ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
        Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
        ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
          Matrix (l ⊕ l) (l ⊕ l) R) =
      ((μ⁻¹ : Rˣ) : R) • Matrix.J l R := by
  have hmul :
      (μ : R) •
        ((((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
            Matrix (l ⊕ l) (l ⊕ l) R).transpose) * Matrix.J l R *
          ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
            Matrix (l ⊕ l) (l ⊕ l) R)) = Matrix.J l R := by
    calc
      (μ : R) •
          ((((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R).transpose) * Matrix.J l R *
            ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R))
          =
          (((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R).transpose) *
            ((μ : R) • Matrix.J l R) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R) := by
            simp [Matrix.mul_smul, mul_assoc]
      _ =
          (((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R).transpose) *
            ((g : Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
              (g : Matrix (l ⊕ l) (l ⊕ l) R)) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R) := by rw [h]
      _ =
          ((((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R).transpose) *
            ((g : Matrix (l ⊕ l) (l ⊕ l) R).transpose)) *
            Matrix.J l R *
            ((g : Matrix (l ⊕ l) (l ⊕ l) R) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R)) := by
            simp [mul_assoc]
      _ = Matrix.J l R := by
            rw [← Matrix.transpose_mul]
            simp
  calc
    (((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
          Matrix (l ⊕ l) (l ⊕ l) R).transpose) * Matrix.J l R *
        ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
          Matrix (l ⊕ l) (l ⊕ l) R)
        = ((μ⁻¹ : Rˣ) : R) •
          ((μ : R) •
            ((((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
                Matrix (l ⊕ l) (l ⊕ l) R).transpose) * Matrix.J l R *
              ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
                Matrix (l ⊕ l) (l ⊕ l) R))) := by
          simp [smul_smul]
    _ = ((μ⁻¹ : Rˣ) : R) • Matrix.J l R := by rw [hmul]

/- accepted add_to_file helper 2 -/
lemma gsp_conj_aux {l : Type*} [DecidableEq l] [Fintype l] {R : Type*} [CommRing R]
    (g x : Matrix.GeneralLinearGroup (l ⊕ l) R)
    {μg μx : Rˣ}
    (hg : (g : Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
        (g : Matrix (l ⊕ l) (l ⊕ l) R) = (μg : R) • Matrix.J l R)
    (hx : (x : Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
        (x : Matrix (l ⊕ l) (l ⊕ l) R) = (μx : R) • Matrix.J l R) :
    ((g⁻¹ * x * g : Matrix.GeneralLinearGroup (l ⊕ l) R) :
        Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
        ((g⁻¹ * x * g : Matrix.GeneralLinearGroup (l ⊕ l) R) :
          Matrix (l ⊕ l) (l ⊕ l) R) =
      (μx : R) • Matrix.J l R := by
  have hgi := gsp_inv_aux g hg
  have hc : ((μg⁻¹ : Rˣ) : R) * ((μx : R) * (μg : R)) = μx := by
    simp [mul_assoc, mul_left_comm]
  calc
    ((g⁻¹ * x * g : Matrix.GeneralLinearGroup (l ⊕ l) R) :
        Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
        ((g⁻¹ * x * g : Matrix.GeneralLinearGroup (l ⊕ l) R) :
          Matrix (l ⊕ l) (l ⊕ l) R)
        =
        (g : Matrix (l ⊕ l) (l ⊕ l) R).transpose *
        ((x : Matrix (l ⊕ l) (l ⊕ l) R).transpose *
          ((((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R).transpose) * Matrix.J l R *
            ((g⁻¹ : Matrix.GeneralLinearGroup (l ⊕ l) R) :
              Matrix (l ⊕ l) (l ⊕ l) R))) *
        (x : Matrix (l ⊕ l) (l ⊕ l) R) *
        (g : Matrix (l ⊕ l) (l ⊕ l) R) := by
          simp [Matrix.transpose_mul, mul_assoc]
    _ =
        (g : Matrix (l ⊕ l) (l ⊕ l) R).transpose *
        ((x : Matrix (l ⊕ l) (l ⊕ l) R).transpose *
          (((μg⁻¹ : Rˣ) : R) • Matrix.J l R)) *
        (x : Matrix (l ⊕ l) (l ⊕ l) R) *
        (g : Matrix (l ⊕ l) (l ⊕ l) R) := by rw [hgi]
    _ =
        ((μg⁻¹ : Rˣ) : R) •
          ((g : Matrix (l ⊕ l) (l ⊕ l) R).transpose *
          ((x : Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
            (x : Matrix (l ⊕ l) (l ⊕ l) R)) *
          (g : Matrix (l ⊕ l) (l ⊕ l) R)) := by
          simp [Matrix.smul_mul, Matrix.mul_smul, mul_assoc]
    _ =
        ((μg⁻¹ : Rˣ) : R) •
          ((g : Matrix (l ⊕ l) (l ⊕ l) R).transpose *
          ((μx : R) • Matrix.J l R) *
          (g : Matrix (l ⊕ l) (l ⊕ l) R)) := by rw [hx]
    _ =
        (((μg⁻¹ : Rˣ) : R) * (μx : R)) •
          ((g : Matrix (l ⊕ l) (l ⊕ l) R).transpose * Matrix.J l R *
            (g : Matrix (l ⊕ l) (l ⊕ l) R)) := by
          simp [Matrix.smul_mul, Matrix.mul_smul, mul_assoc, smul_smul]
    _ =
        (((μg⁻¹ : Rˣ) : R) * (μx : R)) •
          ((μg : R) • Matrix.J l R) := by rw [hg]
    _ = (μx : R) • Matrix.J l R := by
          simp only [smul_eq_mul, smul_smul]
          rw [show ((μg⁻¹ : Rˣ) : R) * (μx : R) * (μg : R) = μx by
            simpa [mul_assoc] using hc]

/- accepted add_to_file helper 3 -/
def Hmat {R : Type*} [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R :=
  Matrix.fromBlocks
    (Matrix.diagonal ![A 0 0, B 0 0])
    (Matrix.diagonal ![A 0 1, B 0 1])
    (Matrix.diagonal ![A 1 0, B 1 0])
    (Matrix.diagonal ![A 1 1, B 1 1])

lemma Hmat_det {R : Type*} [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R) :
    (Hmat A B).det = A.det * B.det := by
  have hsub :
      (Hmat A B).submatrix
        (Equiv.swap (Sum.inl (1 : Fin 2)) (Sum.inr (0 : Fin 2)))
        (Equiv.swap (Sum.inl (1 : Fin 2)) (Sum.inr (0 : Fin 2))) =
      Matrix.fromBlocks A 0 0 B := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Hmat, Equiv.swap_apply_of_ne_of_ne]
  have hdet := Matrix.det_submatrix_equiv_self
    (Equiv.swap (Sum.inl (1 : Fin 2)) (Sum.inr (0 : Fin 2))) (Hmat A B)
  rw [hsub] at hdet
  rw [← hdet]
  exact Matrix.det_fromBlocks_zero₁₂ A 0 B

lemma Hmat_gsp {R : Type*} [CommRing R] (A B : Matrix (Fin 2) (Fin 2) R)
    (hd : A.det = B.det) :
    (Hmat A B).transpose * Matrix.J (Fin 2) R * Hmat A B =
      A.det • Matrix.J (Fin 2) R := by
  rw [Matrix.det_fin_two A, Matrix.det_fin_two B] at hd
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, Hmat, Matrix.J, Matrix.det_fin_two] <;>
    ring_nf <;> first | linear_combination hd | linear_combination -hd

/- accepted add_to_file helper 4 -/
lemma padic_algebraMap_injective (p : ℕ) [Fact p.Prime] :
    Function.Injective (algebraMap ℤ_[p] ℚ_[p]) :=
  IsFractionRing.injective ℤ_[p] ℚ_[p]

/- accepted add_to_file helper 5 -/
lemma conjugate_line_decomp {R : Type*} [CommRing R]
    (γ k : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) {N : R}
    (hγcol :
      Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
        ((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) =
      ((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) +
        ((Pi.single (Sum.inl (1 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)))
    (hk : ∀ i : Fin 2 ⊕ Fin 2, i ≠ Sum.inl (0 : Fin 2) →
      N ∣ (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) i (Sum.inl (0 : Fin 2))) :
    ∃ a : R, ∃ w : (Fin 2 ⊕ Fin 2) → R,
      Matrix.mulVec
        (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
        (((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) +
          ((Pi.single (Sum.inl (1 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R))) =
      a • (((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) +
          ((Pi.single (Sum.inl (1 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R))) +
        N • w := by
  let e : (Fin 2 ⊕ Fin 2) → R :=
    Pi.single (Sum.inl (0 : Fin 2)) (1 : R)
  let x : (Fin 2 ⊕ Fin 2) → R :=
    e + Pi.single (Sum.inl (1 : Fin 2)) (1 : R)
  have hγcol' : Matrix.mulVec
      (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e = x := by
    dsimp [e, x]
    exact hγcol
  let a : R := (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
    (Sum.inl (0 : Fin 2)) (Sum.inl (0 : Fin 2))
  let c : (Fin 2 ⊕ Fin 2) → R := fun i =>
    if hi : i = Sum.inl (0 : Fin 2) then 0 else Classical.choose (hk i hi)
  have hc : ∀ i : Fin 2 ⊕ Fin 2, i ≠ Sum.inl (0 : Fin 2) →
      (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) i (Sum.inl (0 : Fin 2)) =
        N * c i := by
    intro i hi
    simpa [c, hi] using Classical.choose_spec (hk i hi)
  have hkc : Matrix.mulVec (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e =
      a • e + N • c := by
    ext i
    by_cases hi : i = Sum.inl (0 : Fin 2)
    · subst i
      simp [e, a, c, Matrix.mulVec]
    · simp [e, Matrix.mulVec, hi, hc i hi]
  have hginvx :
      Matrix.mulVec
        ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x = e := by
    rw [← hγcol']
    calc
      Matrix.mulVec
          ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
          (Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e)
          =
          Matrix.mulVec
            (((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) *
              (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) e := by
            exact Matrix.mulVec_mulVec e _ _
      _ = e := by simp
  refine ⟨a, Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) c, ?_⟩
  calc
    Matrix.mulVec
        (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x
        =
        Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
          (Matrix.mulVec (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e) := by
          have h1 :
              Matrix.mulVec
                (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                  Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x =
              Matrix.mulVec
                (((γ * k : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                  Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                (Matrix.mulVec
                  ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
                    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x) := by
            calc
              Matrix.mulVec
                  (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x
                  =
                  Matrix.mulVec
                    ((((γ * k : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) *
                    ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
                      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) x := by
                    simp [mul_assoc]
              _ =
                  Matrix.mulVec
                    (((γ * k : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                    (Matrix.mulVec
                      ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
                        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x) := by
                    exact (Matrix.mulVec_mulVec x _ _).symm
          rw [hginvx] at h1
          rw [h1]
          calc
            Matrix.mulVec
                (((γ * k : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                  Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e
                =
                Matrix.mulVec
                  (((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) *
                    (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) e := by simp
            _ =
                Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                  (Matrix.mulVec (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e) := by
                  exact (Matrix.mulVec_mulVec e _ _).symm
    _ =
        Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
          (a • e + N • c) := by rw [hkc]
    _ = a • x + N • Matrix.mulVec
        (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) c := by
          rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hγcol']

/- accepted add_to_file helper 6 -/
def extractA {R : Type*} [CommRing R]
    (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) :
    Matrix (Fin 2) (Fin 2) R :=
  !![G (Sum.inl 0) (Sum.inl 0), G (Sum.inl 0) (Sum.inr 0);
     G (Sum.inr 0) (Sum.inl 0), G (Sum.inr 0) (Sum.inr 0)]

def extractB {R : Type*} [CommRing R]
    (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) :
    Matrix (Fin 2) (Fin 2) R :=
  !![G (Sum.inl 1) (Sum.inl 1), G (Sum.inl 1) (Sum.inr 1);
     G (Sum.inr 1) (Sum.inl 1), G (Sum.inr 1) (Sum.inr 1)]

/- accepted add_to_file helper 7 -/
lemma extractA_map_of_eq {R K : Type*} [CommRing R] [CommRing K] [Algebra R K]
    {h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    {A B : Matrix (Fin 2) (Fin 2) K}
    {G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (hh : h = Hmat A B) (hg : h = G.map (algebraMap R K)) :
    A = (extractA G).map (algebraMap R K) := by
  ext i j
  have heq : Hmat A B = G.map (algebraMap R K) := hh.symm.trans hg
  fin_cases i <;> fin_cases j
  · have eq := congr_fun (congr_fun heq (Sum.inl (0:Fin 2))) (Sum.inl (0:Fin 2))
    simpa [Hmat, extractA] using eq
  · have eq := congr_fun (congr_fun heq (Sum.inl (0:Fin 2))) (Sum.inr (0:Fin 2))
    simpa [Hmat, extractA] using eq
  · have eq := congr_fun (congr_fun heq (Sum.inr (0:Fin 2))) (Sum.inl (0:Fin 2))
    simpa [Hmat, extractA] using eq
  · have eq := congr_fun (congr_fun heq (Sum.inr (0:Fin 2))) (Sum.inr (0:Fin 2))
    simpa [Hmat, extractA] using eq

lemma extractB_map_of_eq {R K : Type*} [CommRing R] [CommRing K] [Algebra R K]
    {h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K}
    {A B : Matrix (Fin 2) (Fin 2) K}
    {G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R}
    (hh : h = Hmat A B) (hg : h = G.map (algebraMap R K)) :
    B = (extractB G).map (algebraMap R K) := by
  ext i j
  have heq : Hmat A B = G.map (algebraMap R K) := hh.symm.trans hg
  fin_cases i <;> fin_cases j
  · have eq := congr_fun (congr_fun heq (Sum.inl (1:Fin 2))) (Sum.inl (1:Fin 2))
    simpa [Hmat, extractB] using eq
  · have eq := congr_fun (congr_fun heq (Sum.inl (1:Fin 2))) (Sum.inr (1:Fin 2))
    simpa [Hmat, extractB] using eq
  · have eq := congr_fun (congr_fun heq (Sum.inr (1:Fin 2))) (Sum.inl (1:Fin 2))
    simpa [Hmat, extractB] using eq
  · have eq := congr_fun (congr_fun heq (Sum.inr (1:Fin 2))) (Sum.inr (1:Fin 2))
    simpa [Hmat, extractB] using eq

/- accepted add_to_file helper 8 -/
lemma extract_det_data (p : ℕ) [Fact p.Prime]
    {h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ_[p]}
    {A B : Matrix (Fin 2) (Fin 2) ℚ_[p]}
    {G : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]}
    (hh : h = Hmat A B)
    (hg : h = ((G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
      (algebraMap ℤ_[p] ℚ_[p])))
    (hdetAB : A.det = B.det) :
    IsUnit (extractA (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])).det ∧
      IsUnit (extractB (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])).det ∧
      (extractA (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])).det =
        (extractB (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])).det := by
  let AZ := extractA (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
  let BZ := extractB (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
  have hAmap : A = AZ.map (algebraMap ℤ_[p] ℚ_[p]) := by
    dsimp [AZ]
    exact extractA_map_of_eq hh hg
  have hBmap : B = BZ.map (algebraMap ℤ_[p] ℚ_[p]) := by
    dsimp [BZ]
    exact extractB_map_of_eq hh hg
  have hdetZ : AZ.det = BZ.det := by
    apply padic_algebraMap_injective p
    calc
      algebraMap ℤ_[p] ℚ_[p] AZ.det = (AZ.map (algebraMap ℤ_[p] ℚ_[p])).det := by
        exact RingHom.map_det (algebraMap ℤ_[p] ℚ_[p]) AZ
      _ = A.det := by rw [← hAmap]
      _ = B.det := hdetAB
      _ = (BZ.map (algebraMap ℤ_[p] ℚ_[p])).det := by rw [← hBmap]
      _ = algebraMap ℤ_[p] ℚ_[p] BZ.det := by
        exact (RingHom.map_det (algebraMap ℤ_[p] ℚ_[p]) BZ).symm
  have hGunit : IsUnit ((G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).det) := by
    simpa using (Matrix.GeneralLinearGroup.det G).isUnit
  have hGdet : (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).det =
      AZ.det * BZ.det := by
    apply padic_algebraMap_injective p
    calc
      algebraMap ℤ_[p] ℚ_[p]
          (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).det
          =
          (((G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
            (algebraMap ℤ_[p] ℚ_[p])).det) := by
            exact RingHom.map_det (algebraMap ℤ_[p] ℚ_[p])
              (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
      _ = (Hmat A B).det := by
            have heqmat :
                ((G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
                  (algebraMap ℤ_[p] ℚ_[p])) = Hmat A B := hg.symm.trans hh
            rw [heqmat]
      _ = A.det * B.det := Hmat_det A B
      _ = (AZ.map (algebraMap ℤ_[p] ℚ_[p])).det *
          (BZ.map (algebraMap ℤ_[p] ℚ_[p])).det := by rw [← hAmap, ← hBmap]
      _ = algebraMap ℤ_[p] ℚ_[p] (AZ.det * BZ.det) := by
        rw [RingHom.map_mul,
          RingHom.map_det (algebraMap ℤ_[p] ℚ_[p]) AZ,
          RingHom.map_det (algebraMap ℤ_[p] ℚ_[p]) BZ,
          RingHom.mapMatrix_apply, RingHom.mapMatrix_apply]
  have hprod : IsUnit (AZ.det * BZ.det) := by
    simpa [hGdet] using hGunit
  exact ⟨isUnit_of_mul_isUnit_left hprod, isUnit_of_mul_isUnit_right hprod, hdetZ⟩

/- accepted add_to_file helper 9 -/
lemma extract_congr_data (p m : ℕ) [Fact p.Prime]
    {h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ_[p]}
    {A B : Matrix (Fin 2) (Fin 2) ℚ_[p]}
    (γ k : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p])
    (hγe₁e₁ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inl 0) (Sum.inl 0) = 1)
    (hγe₁e₂ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inl 1) (Sum.inl 0) = 1)
    (hγe₁f₁ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inr 0) (Sum.inl 0) = 0)
    (hγe₁f₂ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inr 1) (Sum.inl 0) = 0)
    (hk : ∀ i : Fin 2 ⊕ Fin 2, i ≠ Sum.inl 0 →
      (p : ℤ_[p]) ^ m ∣
        (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) i (Sum.inl 0))
    (hh : h = Hmat A B)
    (hg : h = (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
      (algebraMap ℤ_[p] ℚ_[p]))) :
    (p : ℤ_[p]) ^ m ∣
      (extractA (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]))) 1 0 ∧
    (p : ℤ_[p]) ^ m ∣
      (extractB (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]))) 1 0 ∧
    (p : ℤ_[p]) ^ m ∣
      ((extractA (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]))) 0 0 -
        (extractB (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]))) 0 0) := by
  let e : (Fin 2 ⊕ Fin 2) → ℤ_[p] := Pi.single (Sum.inl (0 : Fin 2)) 1
  let x : (Fin 2 ⊕ Fin 2) → ℤ_[p] :=
    e + Pi.single (Sum.inl (1 : Fin 2)) 1
  have hγcol : Matrix.mulVec
      (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) e = x := by
    ext i
    fin_cases i <;> simp [e, x, Matrix.mulVec, hγe₁e₁, hγe₁e₂, hγe₁f₁, hγe₁f₂]
  obtain ⟨a, w, hdecomp⟩ := conjugate_line_decomp γ k hγcol hk
  have zero_entry : ∀ r c : Fin 2 ⊕ Fin 2, Hmat A B r c = 0 →
      (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) r c = 0 := by
    intro r c hr
    apply padic_algebraMap_injective p
    calc
      algebraMap ℤ_[p] ℚ_[p]
          ((((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) r c) = h r c := by
        exact (congr_fun (congr_fun hg r) c).symm
      _ = Hmat A B r c := congr_fun (congr_fun hh r) c
      _ = 0 := hr
  have z₁ : ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) *
      (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) *
      ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]))⁻¹)
      (Sum.inl (0:Fin 2)) (Sum.inl (1:Fin 2)) = 0 := by
    simpa using zero_entry _ _ (by simp [Hmat])
  have z₂ : ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) *
      (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) *
      ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]))⁻¹)
      (Sum.inl (1:Fin 2)) (Sum.inl (0:Fin 2)) = 0 := by
    simpa using zero_entry _ _ (by simp [Hmat])
  have z₃ : ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) *
      (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) *
      ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]))⁻¹)
      (Sum.inr (0:Fin 2)) (Sum.inl (1:Fin 2)) = 0 := by
    simpa using zero_entry _ _ (by simp [Hmat])
  have z₄ : ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) *
      (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) *
      ((γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]))⁻¹)
      (Sum.inr (1:Fin 2)) (Sum.inl (0:Fin 2)) = 0 := by
    simpa using zero_entry _ _ (by simp [Hmat])
  have hA00 : extractA (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) 0 0 =
      a + (p : ℤ_[p]) ^ m * w (Sum.inl (0:Fin 2)) := by
    have e0 := congr_fun hdecomp (Sum.inl (0:Fin 2))
    calc
      extractA (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) 0 0
        =
        Matrix.mulVec (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) x (Sum.inl (0:Fin 2)) := by
        symm
        simp [extractA, e, x, Matrix.mulVec, z₁]
      _ = a • x (Sum.inl (0:Fin 2)) + (p : ℤ_[p]) ^ m • w (Sum.inl (0:Fin 2)) := e0
      _ = a + (p : ℤ_[p]) ^ m * w (Sum.inl (0:Fin 2)) := by simp [e, x]
  have hB00 : extractB (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) 0 0 =
      a + (p : ℤ_[p]) ^ m * w (Sum.inl (1:Fin 2)) := by
    have e1 := congr_fun hdecomp (Sum.inl (1:Fin 2))
    calc
      extractB (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) 0 0
        =
        Matrix.mulVec (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) x (Sum.inl (1:Fin 2)) := by
        symm
        simp [extractB, e, x, Matrix.mulVec, z₂]
      _ = a • x (Sum.inl (1:Fin 2)) + (p : ℤ_[p]) ^ m • w (Sum.inl (1:Fin 2)) := e1
      _ = a + (p : ℤ_[p]) ^ m * w (Sum.inl (1:Fin 2)) := by simp [e, x]
  have hA10 : extractA (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) 1 0 =
      (p : ℤ_[p]) ^ m * w (Sum.inr (0:Fin 2)) := by
    have ef0 := congr_fun hdecomp (Sum.inr (0:Fin 2))
    calc
      extractA (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) 1 0
        =
        Matrix.mulVec (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) x (Sum.inr (0:Fin 2)) := by
        symm
        simp [extractA, e, x, Matrix.mulVec, z₃]
      _ = a • x (Sum.inr (0:Fin 2)) + (p : ℤ_[p]) ^ m • w (Sum.inr (0:Fin 2)) := ef0
      _ = (p : ℤ_[p]) ^ m * w (Sum.inr (0:Fin 2)) := by simp [e, x]
  have hB10 : extractB (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) 1 0 =
      (p : ℤ_[p]) ^ m * w (Sum.inr (1:Fin 2)) := by
    have ef1 := congr_fun hdecomp (Sum.inr (1:Fin 2))
    calc
      extractB (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) 1 0
        =
        Matrix.mulVec (((γ * k * γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p]) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])) x (Sum.inr (1:Fin 2)) := by
        symm
        simp [extractB, e, x, Matrix.mulVec, z₄]
      _ = a • x (Sum.inr (1:Fin 2)) + (p : ℤ_[p]) ^ m • w (Sum.inr (1:Fin 2)) := ef1
      _ = (p : ℤ_[p]) ^ m * w (Sum.inr (1:Fin 2)) := by simp [e, x]
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨w (Sum.inr (0:Fin 2)), hA10⟩
  · exact ⟨w (Sum.inr (1:Fin 2)), hB10⟩
  · refine ⟨w (Sum.inl (0:Fin 2)) - w (Sum.inl (1:Fin 2)), ?_⟩
    rw [hA00, hB00]
    ring

/- accepted add_to_file helper 10 -/
lemma Hmat_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A B : Matrix (Fin 2) (Fin 2) R) :
    Hmat (A.map f) (B.map f) = (Hmat A B).map f := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Hmat]

/- accepted add_to_file helper 11 -/
lemma Hmat_line_decomp {R : Type*} [CommRing R]
    (A B : Matrix (Fin 2) (Fin 2) R) {N : R}
    (hA10 : N ∣ A 1 0) (hB10 : N ∣ B 1 0)
    (hdiff : N ∣ (A 0 0 - B 0 0)) :
    ∃ w : (Fin 2 ⊕ Fin 2) → R,
      Matrix.mulVec (Hmat A B)
        (((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) +
          ((Pi.single (Sum.inl (1 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R))) =
      A 0 0 • (((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) +
          ((Pi.single (Sum.inl (1 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R))) +
        N • w := by
  obtain ⟨ca, hca⟩ := hA10
  obtain ⟨cb, hcb⟩ := hB10
  obtain ⟨cd, hcd⟩ := hdiff
  let w : (Fin 2 ⊕ Fin 2) → R := fun i =>
    if i = Sum.inl (0:Fin 2) then 0 else
    if i = Sum.inl (1:Fin 2) then -cd else
    if i = Sum.inr (0:Fin 2) then ca else cb
  refine ⟨w, ?_⟩
  ext i
  fin_cases i <;> simp [Hmat, Matrix.mulVec, w, hca, hcb, hcd] <;> ring <;>
    try linear_combination -hcd

/- accepted add_to_file helper 12 -/
lemma line_condition_of_decomp {R : Type*} [CommRing R]
    (γ H : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) {N a : R}
    (w : (Fin 2 ⊕ Fin 2) → R)
    (hγcol :
      Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
        ((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) =
      ((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) +
        ((Pi.single (Sum.inl (1 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)))
    (hHx :
      Matrix.mulVec (H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
        (((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) +
          ((Pi.single (Sum.inl (1 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R))) =
      a • (((Pi.single (Sum.inl (0 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R)) +
          ((Pi.single (Sum.inl (1 : Fin 2)) (1 : R) : (Fin 2 ⊕ Fin 2) → R))) +
        N • w) :
    ∀ i : Fin 2 ⊕ Fin 2, i ≠ Sum.inl (0 : Fin 2) →
      N ∣ (((γ⁻¹ * H * γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) i (Sum.inl (0 : Fin 2)) := by
  let e : (Fin 2 ⊕ Fin 2) → R := Pi.single (Sum.inl (0 : Fin 2)) 1
  let x : (Fin 2 ⊕ Fin 2) → R :=
    e + Pi.single (Sum.inl (1 : Fin 2)) 1
  have hγcol' : Matrix.mulVec
      (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e = x := by
    dsimp [e, x]
    exact hγcol
  have hHx' : Matrix.mulVec
      (H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x = a • x + N • w := by
    dsimp [e, x]
    exact hHx
  have hginvx :
      Matrix.mulVec
        ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x = e := by
    rw [← hγcol']
    calc
      Matrix.mulVec
          ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
          (Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e)
          =
          Matrix.mulVec
            (((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) *
              (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) e := by
            exact Matrix.mulVec_mulVec e _ _
      _ = e := by simp
  have hcol :
      Matrix.mulVec
        (((γ⁻¹ * H * γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) e =
      Matrix.mulVec
        ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
        (a • x + N • w) := by
    calc
      Matrix.mulVec
          (((γ⁻¹ * H * γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) e
          =
          Matrix.mulVec
            ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
            (Matrix.mulVec (H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
              (Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e)) := by
          calc
            Matrix.mulVec
                (((γ⁻¹ * H * γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
                  Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) e
                =
                Matrix.mulVec
                  ((((γ⁻¹ * H : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) *
                  (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) e := by
                  simp [mul_assoc]
            _ =
                Matrix.mulVec
                  (((γ⁻¹ * H : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                  (Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e) := by
                  exact (Matrix.mulVec_mulVec e _ _).symm
            _ =
                Matrix.mulVec
                  ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
                    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                  (Matrix.mulVec (H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                    (Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e)) := by
                  calc
                    Matrix.mulVec
                        (((γ⁻¹ * H : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                        (Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e)
                        =
                        Matrix.mulVec
                          ((((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R)) :
                            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) *
                          (H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R))
                          (Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e) := by
                          simp
                    _ =
                        Matrix.mulVec
                          ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
                            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                          (Matrix.mulVec (H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
                            (Matrix.mulVec (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) e)) := by
                          exact (Matrix.mulVec_mulVec _ _ _).symm
      _ =
          Matrix.mulVec
            ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
            (Matrix.mulVec (H : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) x) := by
            rw [hγcol']
      _ =
          Matrix.mulVec
            ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
              Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
            (a • x + N • w) := by rw [hHx']
  intro i hi
  refine ⟨Matrix.mulVec
    ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) w i, ?_⟩
  calc
    (((γ⁻¹ * H * γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) i (Sum.inl (0 : Fin 2))
        =
        Matrix.mulVec
          (((γ⁻¹ * H * γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)) e i := by
          simp [e, Matrix.mulVec]
    _ =
        Matrix.mulVec
          ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R)
          (a • x + N • w) i := by rw [hcol]
    _ = N * Matrix.mulVec
          ((γ⁻¹ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) R) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R) w i := by
          rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hginvx]
          simp [e, hi]

/- accepted add_to_file helper 13 -/
lemma Hmat_GL_map_eq {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A B : Matrix.GeneralLinearGroup (Fin 2) R) :
    (Hmat (A : Matrix (Fin 2) (Fin 2) R)
      (B : Matrix (Fin 2) (Fin 2) R)).map f =
    Hmat ((Matrix.GeneralLinearGroup.map f A :
      Matrix.GeneralLinearGroup (Fin 2) S) : Matrix (Fin 2) (Fin 2) S)
      ((Matrix.GeneralLinearGroup.map f B :
        Matrix.GeneralLinearGroup (Fin 2) S) : Matrix (Fin 2) (Fin 2) S) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Hmat, Matrix.GeneralLinearGroup.map_apply]

/- verified submission -/
theorem proposition_4_2
    (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m)
    (γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p])
    (hγGSp : ∃ μ : ℤ_[p]ˣ,
      (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).transpose *
          Matrix.J (Fin 2) ℤ_[p] *
          (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) =
        (μ : ℤ_[p]) • Matrix.J (Fin 2) ℤ_[p])
    (hγe₁e₁ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inl 0) (Sum.inl 0) = 1)
    (hγe₁e₂ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inl 1) (Sum.inl 0) = 1)
    (hγe₁f₁ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inr 0) (Sum.inl 0) = 0)
    (hγe₁f₂ : (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
        (Sum.inr 1) (Sum.inl 0) = 0) :
    {h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ_[p] |
      (∃ A B : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p],
        Matrix.det (A : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
            Matrix.det (B : Matrix (Fin 2) (Fin 2) ℚ_[p]) ∧
        h = Matrix.fromBlocks
          (Matrix.diagonal ![A 0 0, B 0 0])
          (Matrix.diagonal ![A 0 1, B 0 1])
          (Matrix.diagonal ![A 1 0, B 1 0])
          (Matrix.diagonal ![A 1 1, B 1 1])) ∧
      ∃ k : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p],
        (∃ μ : ℤ_[p]ˣ,
          (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).transpose *
              Matrix.J (Fin 2) ℤ_[p] *
              (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) =
            (μ : ℤ_[p]) • Matrix.J (Fin 2) ℤ_[p]) ∧
        (∀ i : Fin 2 ⊕ Fin 2, i ≠ Sum.inl 0 →
          (p : ℤ_[p]) ^ m ∣
            (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) i (Sum.inl 0)) ∧
        h = ((↑(γ * k * γ⁻¹) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
            (algebraMap ℤ_[p] ℚ_[p]))} =
    {h : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ_[p] |
      ∃ A B : Matrix.GeneralLinearGroup (Fin 2) ℤ_[p],
        Matrix.det (A : Matrix (Fin 2) (Fin 2) ℤ_[p]) =
            Matrix.det (B : Matrix (Fin 2) (Fin 2) ℤ_[p]) ∧
        (p : ℤ_[p]) ^ m ∣ (A : Matrix (Fin 2) (Fin 2) ℤ_[p]) 1 0 ∧
        (p : ℤ_[p]) ^ m ∣ (B : Matrix (Fin 2) (Fin 2) ℤ_[p]) 1 0 ∧
        (p : ℤ_[p]) ^ m ∣
          ((A : Matrix (Fin 2) (Fin 2) ℤ_[p]) 0 0 -
            (B : Matrix (Fin 2) (Fin 2) ℤ_[p]) 0 0) ∧
        h = (Matrix.fromBlocks
          (Matrix.diagonal ![A 0 0, B 0 0])
          (Matrix.diagonal ![A 0 1, B 0 1])
          (Matrix.diagonal ![A 1 0, B 1 0])
          (Matrix.diagonal ![A 1 1, B 1 1])).map
            (algebraMap ℤ_[p] ℚ_[p])} := by
  ext h
  constructor
  · rintro ⟨⟨A, B, hdet, hH⟩, k, _hkGSp, hk, hconj⟩
    change h = Hmat (A : Matrix (Fin 2) (Fin 2) ℚ_[p])
      (B : Matrix (Fin 2) (Fin 2) ℚ_[p]) at hH
    let G : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p] := γ * k * γ⁻¹
    have hconj' : h = ((G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
      (algebraMap ℤ_[p] ℚ_[p])) := by
      simpa [G] using hconj
    obtain ⟨huA, huB, hdetZ⟩ := extract_det_data p hH hconj' hdet
    let AZ : Matrix (Fin 2) (Fin 2) ℤ_[p] :=
      extractA (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
    let BZ : Matrix (Fin 2) (Fin 2) ℤ_[p] :=
      extractB (G : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
    let AGL : Matrix.GeneralLinearGroup (Fin 2) ℤ_[p] :=
      Matrix.GeneralLinearGroup.mk'' AZ huA
    let BGL : Matrix.GeneralLinearGroup (Fin 2) ℤ_[p] :=
      Matrix.GeneralLinearGroup.mk'' BZ huB
    obtain ⟨hcA, hcB, hdiff⟩ :=
      extract_congr_data p m γ k hγe₁e₁ hγe₁e₂ hγe₁f₁ hγe₁f₂ hk hH hconj'
    refine ⟨AGL, BGL, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [AGL, BGL, AZ, BZ, Matrix.GeneralLinearGroup.val_mk''] using hdetZ
    · simpa [AGL, AZ, G, Matrix.GeneralLinearGroup.val_mk''] using hcA
    · simpa [BGL, BZ, G, Matrix.GeneralLinearGroup.val_mk''] using hcB
    · simpa [AGL, BGL, AZ, BZ, G, Matrix.GeneralLinearGroup.val_mk''] using hdiff
    · have hAmap : (A : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
          AZ.map (algebraMap ℤ_[p] ℚ_[p]) := by
        dsimp [AZ]
        exact extractA_map_of_eq hH hconj'
      have hBmap : (B : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
          BZ.map (algebraMap ℤ_[p] ℚ_[p]) := by
        dsimp [BZ]
        exact extractB_map_of_eq hH hconj'
      calc
        h = Hmat (A : Matrix (Fin 2) (Fin 2) ℚ_[p])
            (B : Matrix (Fin 2) (Fin 2) ℚ_[p]) := hH
        _ = Hmat (AZ.map (algebraMap ℤ_[p] ℚ_[p]))
            (BZ.map (algebraMap ℤ_[p] ℚ_[p])) := by rw [hAmap, hBmap]
        _ = (Hmat AZ BZ).map (algebraMap ℤ_[p] ℚ_[p]) := Hmat_map _ _ _
        _ = (Hmat (AGL : Matrix (Fin 2) (Fin 2) ℤ_[p])
            (BGL : Matrix (Fin 2) (Fin 2) ℤ_[p])).map
            (algebraMap ℤ_[p] ℚ_[p]) := by
          simp [AGL, BGL, Matrix.GeneralLinearGroup.val_mk'']
  · rintro ⟨A, B, hdet, hcA, hcB, hdiff, hH⟩
    change h = (Hmat (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
      (B : Matrix (Fin 2) (Fin 2) ℤ_[p])).map (algebraMap ℤ_[p] ℚ_[p]) at hH
    let Aq : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p] :=
      Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) A
    let Bq : Matrix.GeneralLinearGroup (Fin 2) ℚ_[p] :=
      Matrix.GeneralLinearGroup.map (algebraMap ℤ_[p] ℚ_[p]) B
    have hdetq :
        Matrix.det (Aq : Matrix (Fin 2) (Fin 2) ℚ_[p]) =
          Matrix.det (Bq : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
      rw [Matrix.GeneralLinearGroup.val_map_apply,
        Matrix.GeneralLinearGroup.val_map_apply]
      rw [← RingHom.mapMatrix_apply (algebraMap ℤ_[p] ℚ_[p])
        (A : Matrix (Fin 2) (Fin 2) ℤ_[p]),
        ← RingHom.mapMatrix_apply (algebraMap ℤ_[p] ℚ_[p])
        (B : Matrix (Fin 2) (Fin 2) ℤ_[p])]
      rw [← RingHom.map_det (algebraMap ℤ_[p] ℚ_[p])
        (A : Matrix (Fin 2) (Fin 2) ℤ_[p]),
        ← RingHom.map_det (algebraMap ℤ_[p] ℚ_[p])
        (B : Matrix (Fin 2) (Fin 2) ℤ_[p])]
      rw [hdet]
    have hHq : h = Hmat (Aq : Matrix (Fin 2) (Fin 2) ℚ_[p])
        (Bq : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
      calc
        h = (Hmat (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
            (B : Matrix (Fin 2) (Fin 2) ℤ_[p])).map
            (algebraMap ℤ_[p] ℚ_[p]) := hH
        _ = Hmat (Aq : Matrix (Fin 2) (Fin 2) ℚ_[p])
            (Bq : Matrix (Fin 2) (Fin 2) ℚ_[p]) := by
          dsimp [Aq, Bq]
          exact Hmat_GL_map_eq (algebraMap ℤ_[p] ℚ_[p]) A B
    have hUA : IsUnit (A : Matrix (Fin 2) (Fin 2) ℤ_[p]).det := by
      simpa using (Matrix.GeneralLinearGroup.det A).isUnit
    have hUB : IsUnit (B : Matrix (Fin 2) (Fin 2) ℤ_[p]).det := by
      simpa using (Matrix.GeneralLinearGroup.det B).isUnit
    have hunitH : IsUnit (Hmat (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
        (B : Matrix (Fin 2) (Fin 2) ℤ_[p])).det := by
      rw [Hmat_det]
      exact hUA.mul hUB
    let HGL : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p] :=
      Matrix.GeneralLinearGroup.mk''
        (Hmat (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
          (B : Matrix (Fin 2) (Fin 2) ℤ_[p])) hunitH
    let k : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2) ℤ_[p] := γ⁻¹ * HGL * γ
    have hHGSp :
        (HGL : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).transpose *
            Matrix.J (Fin 2) ℤ_[p] *
          (HGL : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) =
        ((Matrix.GeneralLinearGroup.det A : ℤ_[p]ˣ) : ℤ_[p]) •
          Matrix.J (Fin 2) ℤ_[p] := by
      have base := Hmat_gsp (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
        (B : Matrix (Fin 2) (Fin 2) ℤ_[p]) hdet
      simpa [HGL, Matrix.GeneralLinearGroup.val_mk''] using base
    obtain ⟨μγ, hγeq⟩ := hγGSp
    have hkGSp :
        (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).transpose *
            Matrix.J (Fin 2) ℤ_[p] *
          (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) =
        ((Matrix.GeneralLinearGroup.det A : ℤ_[p]ˣ) : ℤ_[p]) •
          Matrix.J (Fin 2) ℤ_[p] := by
      have conj := gsp_conj_aux γ HGL hγeq hHGSp
      simpa [k] using conj
    let e : (Fin 2 ⊕ Fin 2) → ℤ_[p] := Pi.single (Sum.inl (0 : Fin 2)) 1
    let x : (Fin 2 ⊕ Fin 2) → ℤ_[p] :=
      e + Pi.single (Sum.inl (1 : Fin 2)) 1
    have hγcol : Matrix.mulVec
        (γ : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) e = x := by
      ext i
      fin_cases i <;> simp [e, x, Matrix.mulVec, hγe₁e₁, hγe₁e₂, hγe₁f₁, hγe₁f₂]
    obtain ⟨w, hHx⟩ := Hmat_line_decomp
      (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
      (B : Matrix (Fin 2) (Fin 2) ℤ_[p]) hcA hcB hdiff
    have hHxH :
        Matrix.mulVec (HGL : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p])
          (((Pi.single (Sum.inl (0 : Fin 2)) (1 : ℤ_[p]) : (Fin 2 ⊕ Fin 2) → ℤ_[p])) +
            ((Pi.single (Sum.inl (1 : Fin 2)) (1 : ℤ_[p]) : (Fin 2 ⊕ Fin 2) → ℤ_[p]))) =
        (A : Matrix (Fin 2) (Fin 2) ℤ_[p]) 0 0 •
          (((Pi.single (Sum.inl (0 : Fin 2)) (1 : ℤ_[p]) : (Fin 2 ⊕ Fin 2) → ℤ_[p])) +
            ((Pi.single (Sum.inl (1 : Fin 2)) (1 : ℤ_[p]) : (Fin 2 ⊕ Fin 2) → ℤ_[p]))) +
          (p : ℤ_[p]) ^ m • w := by
      simpa [HGL, Matrix.GeneralLinearGroup.val_mk''] using hHx
    have hkl : ∀ i : Fin 2 ⊕ Fin 2, i ≠ Sum.inl 0 →
        (p : ℤ_[p]) ^ m ∣
          (k : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]) i (Sum.inl 0) := by
      have line := line_condition_of_decomp γ HGL w hγcol hHxH
      simpa [k] using line
    have hconj : h = ((↑(γ * k * γ⁻¹) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
        (algebraMap ℤ_[p] ℚ_[p])) := by
      have hgroup : γ * k * γ⁻¹ = HGL := by
        dsimp [k]
        group
      calc
        h = (Hmat (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
            (B : Matrix (Fin 2) (Fin 2) ℤ_[p])).map
            (algebraMap ℤ_[p] ℚ_[p]) := hH
        _ = ((HGL : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
            (algebraMap ℤ_[p] ℚ_[p])) := by
          simp [HGL, Matrix.GeneralLinearGroup.val_mk'']
        _ = ((↑(γ * k * γ⁻¹) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ_[p]).map
            (algebraMap ℤ_[p] ℚ_[p])) := by rw [hgroup]
    exact ⟨⟨Aq, Bq, hdetq, hHq⟩, k,
      ⟨Matrix.GeneralLinearGroup.det A, hkGSp⟩, hkl, hconj⟩


#check_dependency_graph "proposition_4_2" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"{h | (∃ A B, (↑A).det = (↑B).det ∧ h = Matrix.fromBlocks (Matrix.diagonal ![↑A 0 0, ↑B 0 0]) (Matrix.diagonal ![↑A 0 1, ↑B 0 1]) (Matrix.diagonal ![↑A 1 0, ↑B 1 0]) (Matrix.diagonal ![↑A 1 1, ↑B 1 1])) ∧ ∃ k, (∃ μ, (↑k).transpose * Matrix.J (Fin 2) ℤ_[p] * ↑k = ↑μ • Matrix.J (Fin 2) ℤ_[p]) ∧ (∀ (i : Fin 2 ⊕ Fin 2), i ≠ Sum.inl 0 → ↑p ^ m ∣ ↑k i (Sum.inl 0)) ∧ h = (↑(γ * k * γ⁻¹)).map ⇑(algebraMap ℤ_[p] ℚ_[p])} = {h | ∃ A B, (↑A).det = (↑B).det ∧ ↑p ^ m ∣ ↑A 1 0 ∧ ↑p ^ m ∣ ↑B 1 0 ∧ ↑p ^ m ∣ ↑A 0 0 - ↑B 0 0 ∧ h = (Matrix.fromBlocks (Matrix.diagonal ![↑A 0 0, ↑B 0 0]) (Matrix.diagonal ![↑A 0 1, ↑B 0 1]) (Matrix.diagonal ![↑A 1 0, ↑B 1 0]) (Matrix.diagonal ![↑A 1 1, ↑B 1 1])).map ⇑(algebraMap ℤ_[p] ℚ_[p])}\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"Fact (Nat.Prime p)\"},{\"name\":\"hγGSp\",\"statement\":\"∃ μ, (↑γ).transpose * Matrix.J (Fin 2) ℤ_[p] * ↑γ = ↑μ • Matrix.J (Fin 2) ℤ_[p]\"},{\"name\":\"hγe₁e₁\",\"statement\":\"↑γ (Sum.inl 0) (Sum.inl 0) = 1\"},{\"name\":\"hγe₁e₂\",\"statement\":\"↑γ (Sum.inl 1) (Sum.inl 0) = 1\"},{\"name\":\"hγe₁f₁\",\"statement\":\"↑γ (Sum.inr 0) (Sum.inl 0) = 0\"},{\"name\":\"hγe₁f₂\",\"statement\":\"↑γ (Sum.inr 1) (Sum.inl 0) = 0\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2272_proposition_4_2\",\"reconstructedProofSha256\":\"b1141185f1b9f649d68bf75e20f59455a2c82fcca1cb1918e2f4b914ff3fcbe2\",\"selectedEdgeCount\":1,\"theoremName\":\"proposition_4_2\",\"topologySha256\":\"600b198cacdc3ae08bbac9a54879a718992687cf4b769380a7ffaa2e3faaa668\"}"
