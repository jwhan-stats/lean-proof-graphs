import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p2109_stable_equivalence_empty_subfield_points_i
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 83c1f3429a819d27d51092c231154faa95c7febde4ce81a49b36cda28c209492
-- reconstructed_proof_sha256: 0491507063df14fc42c2ac8996ab55388da578e868a0a8c896a2ea5e42e201c0
-- selected_edge_count: 2

/- accepted add_to_file helper 1 -/
lemma scalar_tower_subfield_real (A : Subfield ℝ) : IsScalarTower A ℝ ℝ :=
  Subfield.instIsScalarTowerSubtypeMem (K := ℝ) (X := ℝ) (Y := ℝ) A

noncomputable abbrev subfieldTensorPiEquiv (A : Subfield ℝ) (d : ℕ) :
    TensorProduct A ℝ (Fin d → A) ≃ₗ[ℝ] Fin d → ℝ :=
  @TensorProduct.piScalarRight A _ ℝ _ _ ℝ _ _ _ (scalar_tower_subfield_real A) (Fin d) _ _

noncomputable def subfieldLiftLinearMap {d s : ℕ} (A : Subfield ℝ)
    (b : Fin s → Fin d → A) : (Fin d → ℝ) →ₗ[ℝ] Fin s → ℝ where
  toFun x := fun i => ∑ j : Fin d, ((b i j : A) : ℝ) * x j
  map_add' x y := by
    ext i
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' c x := by
    ext i
    dsimp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_left_comm ((b i j : A) : ℝ) c (x j)

lemma subfieldTensorPiEquiv_lTensor {d s : ℕ} (A : Subfield ℝ)
    (b : Fin s → Fin d → A) :
    (subfieldTensorPiEquiv A s).toLinearMap.comp
      ((Matrix.toLin' (Matrix.of fun i j => b i j)).baseChange ℝ) =
      (subfieldLiftLinearMap A b).comp (subfieldTensorPiEquiv A d).toLinearMap := by
  refine LinearMap.ext ?_
  intro t
  refine TensorProduct.induction_on t ?_ ?_ ?_
  · simp
  · intro c y
    ext i
    let fA : (Fin d → A) →ₗ[A] Fin s → A :=
      Matrix.toLin' (Matrix.of fun i j => b i j)
    change ((subfieldTensorPiEquiv A s).toLinearMap (fA.baseChange ℝ (c ⊗ₜ[A] y))) i =
      ((subfieldLiftLinearMap A b).comp (subfieldTensorPiEquiv A d).toLinearMap) (c ⊗ₜ[A] y) i
    rw [LinearMap.baseChange_tmul]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, subfieldTensorPiEquiv]
    rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRight_apply]
    change (fA y i • c) =
      (subfieldLiftLinearMap A b) ((@TensorProduct.piScalarRightHom A _ ℝ _ _ ℝ _ _ _
        (scalar_tower_subfield_real A) (Fin d)) (c ⊗ₜ[A] y)) i
    change (fA y i • c) =
      (subfieldLiftLinearMap A b) (fun j => y j • c) i
    simp [fA, subfieldLiftLinearMap, Matrix.toLin'_apply, Matrix.mulVec,
      dotProduct]
    simp only [Subfield.smul_def, smul_eq_mul]
    change (A.subtype (∑ x, b i x * y x)) * c = ∑ x, ↑(b i x) * (↑(y x) * c)
    rw [map_sum A.subtype, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simp
    ring
  · intro u v hu hv
    simp [map_add, hu, hv]

lemma exists_rat_finset_approx
    {ι : Type*} [Fintype ι] (c : ι → ℝ) (U : Set (ι → ℝ))
    (hU : IsOpen U) (hc : c ∈ U) :
    ∃ q : ι → ℚ, (fun i => ((q i : ℚ) : ℝ)) ∈ U := by
  rcases (Metric.isOpen_iff.mp hU) c hc with ⟨ε, hε, hball⟩
  choose q hq using fun i => exists_rat_near (K := ℝ) (c i) hε
  refine ⟨q, hball ?_⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro i
  have h := hq i
  rw [Real.dist_eq, abs_sub_comm]
  simpa [Real.dist_eq] using h

lemma subfield_cast_sum_q_smul_apply {d : ℕ} {ι : Type} [Fintype ι]
    (A : Subfield ℝ) (q : ι → ℚ) (z : ι → Fin d → A) (j : Fin d) :
    (((∑ p : ι, (q p : A) • z p) j : A) : ℝ) =
      ∑ p : ι, ((q p : ℚ) : ℝ) * ((z p j : A) : ℝ) := by
  simp

lemma exists_subfield_linear_solution_from_rep {d r s : ℕ} (A : Subfield ℝ)
    (a : Fin r → Fin d → A) (b : Fin s → Fin d → A) (x : Fin d → ℝ)
    (S : Finset (ℝ × (Matrix.toLin' (Matrix.of fun i j => b i j)).ker))
    (hxrep : x = fun j => ∑ p ∈ S, p.1 * ((p.2.1 j : A) : ℝ))
    (hpos : ∀ i : Fin r, ∑ j : Fin d, ((a i j : A) : ℝ) * x j > 0) :
    ∃ y : Fin d → A,
      (∀ i : Fin r, ∑ j : Fin d, ((a i j : A) : ℝ) * ((y j : A) : ℝ) > 0) ∧
      ∀ i : Fin s, ∑ j : Fin d, ((b i j : A) : ℝ) * ((y j : A) : ℝ) = 0 := by
  let c : S → ℝ := fun p => p.1.1
  have hxrep' : x = fun j => ∑ p : S, c p * ((p.1.2.1 j : A) : ℝ) := by
    rw [hxrep]
    ext j
    rw [← Finset.sum_attach S (fun p => p.1 * ((p.2.1 j : A) : ℝ))]
    rfl
  let F : (S → ℝ) → Fin r → ℝ := fun u i =>
    ∑ j : Fin d, ((a i j : A) : ℝ) *
      ∑ p : S, u p * ((p.1.2.1 j : A) : ℝ)
  let U : Set (S → ℝ) := {u | ∀ i : Fin r, 0 < F u i}
  have hcont : ∀ i : Fin r, Continuous fun u : S → ℝ => F u i := by
    intro i
    dsimp [F]
    apply continuous_finset_sum Finset.univ
    intro j _
    apply Continuous.mul continuous_const
    apply continuous_finset_sum Finset.univ
    intro p _
    exact (continuous_apply p).mul continuous_const
  have hU : IsOpen U := by
    have hset : U = ⋂ i : Fin r, {u : S → ℝ | 0 < F u i} := by
      ext u
      simp [U]
    rw [hset]
    exact isOpen_iInter_of_finite fun i : Fin r => isOpen_Ioi.preimage (hcont i)
  have hc : c ∈ U := by
    intro i
    have hFx : F c i = ∑ j : Fin d, ((a i j : A) : ℝ) * x j := by
      calc
        F c i = ∑ j : Fin d, ((a i j : A) : ℝ) *
            (fun j => ∑ p : S, c p * ((p.1.2.1 j : A) : ℝ)) j := rfl
        _ = ∑ j : Fin d, ((a i j : A) : ℝ) * x j := by
          apply Finset.sum_congr rfl
          intro j _
          change ((a i j : A) : ℝ) *
              (∑ p : S, c p * ((p.1.2.1 j : A) : ℝ)) =
            ((a i j : A) : ℝ) * x j
          rw [← congrFun hxrep' j]
    simpa [U, hFx] using hpos i
  rcases exists_rat_finset_approx c U hU hc with ⟨q, hq⟩
  let y : Fin d → A := ∑ p : S, (q p : A) • p.1.2.1
  refine ⟨y, ?_, ?_⟩
  · intro i
    have hFy : F (fun p : S => ((q p : ℚ) : ℝ)) i =
        ∑ j : Fin d, ((a i j : A) : ℝ) * ((y j : A) : ℝ) := by
      calc
        F (fun p : S => ((q p : ℚ) : ℝ)) i
            = ∑ j : Fin d, ((a i j : A) : ℝ) *
                ∑ p : S, ((q p : ℚ) : ℝ) * ((p.1.2.1 j : A) : ℝ) := rfl
        _ = ∑ j : Fin d, ((a i j : A) : ℝ) * ((y j : A) : ℝ) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [subfield_cast_sum_q_smul_apply A q (fun p : S => p.1.2.1) j]
    rw [← hFy]
    exact hq i
  · have hyE : y ∈ (Matrix.toLin' (Matrix.of fun i j => b i j)).ker := by
      dsimp [y]
      apply Submodule.sum_smul_mem
      intro p hp
      exact p.1.2.property
    have hfy : Matrix.toLin' (Matrix.of fun i j => b i j) y = 0 :=
      LinearMap.mem_ker.mp hyE
    intro i
    have hi := congrFun hfy i
    have hiR := congrArg (fun z : A => (z : ℝ)) hi
    simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct] using hiR

lemma exists_subfield_linear_solution {d r s : ℕ} (A : Subfield ℝ)
    (a : Fin r → Fin d → A) (b : Fin s → Fin d → A) (x : Fin d → ℝ)
    (hpos : ∀ i : Fin r, ∑ j : Fin d, ((a i j : A) : ℝ) * x j > 0)
    (heq : ∀ i : Fin s, ∑ j : Fin d, ((b i j : A) : ℝ) * x j = 0) :
    ∃ y : Fin d → A,
      (∀ i : Fin r, ∑ j : Fin d, ((a i j : A) : ℝ) * ((y j : A) : ℝ) > 0) ∧
      ∀ i : Fin s, ∑ j : Fin d, ((b i j : A) : ℝ) * ((y j : A) : ℝ) = 0 := by
  let fA : (Fin d → A) →ₗ[A] Fin s → A :=
    Matrix.toLin' (Matrix.of fun i j => b i j)
  let E : Submodule A (Fin d → A) := fA.ker
  letI := fA.ker.module
  have hexact : Function.Exact ⇑E.subtype ⇑fA := by
    intro z
    constructor
    · intro hz
      exact ⟨⟨z, hz⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact z.property
  have hflat : Function.Exact ⇑(LinearMap.lTensor ℝ E.subtype) ⇑(LinearMap.lTensor ℝ fA) :=
    Module.Flat.lTensor_exact (R := A) (M := ℝ) hexact
  let t : TensorProduct A ℝ (Fin d → A) := (subfieldTensorPiEquiv A d).symm x
  have hkernel : LinearMap.lTensor ℝ fA t = 0 := by
    apply (subfieldTensorPiEquiv A s).injective
    have hmap := congrArg (fun F => F t) (subfieldTensorPiEquiv_lTensor A b)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, t] at hmap
    have hxzero : subfieldLiftLinearMap A b x = 0 := by
      ext i
      exact heq i
    change (subfieldTensorPiEquiv A s) (fA.baseChange ℝ t) = (subfieldTensorPiEquiv A s) 0
    change (subfieldTensorPiEquiv A s)
      ((Matrix.toLin' (Matrix.of fun i j => b i j)).baseChange ℝ
        ((subfieldTensorPiEquiv A d).symm x)) = (subfieldTensorPiEquiv A s) 0
    calc
      (subfieldTensorPiEquiv A s)
          ((Matrix.toLin' (Matrix.of fun i j => b i j)).baseChange ℝ
            ((subfieldTensorPiEquiv A d).symm x))
          = ((subfieldLiftLinearMap A b).comp (subfieldTensorPiEquiv A d).toLinearMap)
              ((subfieldTensorPiEquiv A d).symm x) := hmap
      _ = subfieldLiftLinearMap A b x := by simp
      _ = 0 := hxzero
      _ = (subfieldTensorPiEquiv A s) 0 := by simp
  rcases (hflat t).mp hkernel with ⟨zT, hzT⟩
  rcases TensorProduct.exists_finset zT with ⟨S, hS⟩
  have hxrep : x = fun j => ∑ p ∈ S, p.1 * ((p.2.1 j : A) : ℝ) := by
    have hfun : (subfieldTensorPiEquiv A d).toLinearMap (LinearMap.lTensor ℝ E.subtype zT) = x := by
      rw [hzT]
      simp [t]
    have hsum : (subfieldTensorPiEquiv A d).toLinearMap (LinearMap.lTensor ℝ E.subtype zT) =
        fun j => ∑ p ∈ S, p.1 * ((p.2.1 j : A) : ℝ) := by
      rw [hS]
      rw [map_sum (LinearMap.lTensor ℝ E.subtype)]
      rw [map_sum (subfieldTensorPiEquiv A d).toLinearMap]
      ext j
      rw [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro p hp
      rw [LinearMap.lTensor_tmul]
      simp [subfieldTensorPiEquiv, TensorProduct.piScalarRight, Subfield.smul_def,
        smul_eq_mul, mul_comm]
    exact hfun.symm.trans hsum
  exact exists_subfield_linear_solution_from_rep A a b x S hxrep hpos

/- accepted add_to_file helper 2 -/
lemma eval₂_int_subfield_cast {k : ℕ} (A : Subfield ℝ) (v : Fin k → A)
    (p : MvPolynomial (Fin k) ℤ) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) (fun i => ((v i : A) : ℝ)) p =
      ((MvPolynomial.eval₂ (Int.castRingHom A) (fun i => v i) p : A) : ℝ) := by
  symm
  change A.subtype (MvPolynomial.eval₂ (Int.castRingHom A) (fun i => v i) p) = _
  rw [MvPolynomial.eval₂_comp_left A.subtype (Int.castRingHom A) (fun i => v i) p]
  congr 1

/- accepted add_to_file helper 3 -/
lemma eval₂_rat_subfield_cast {k : ℕ} (A : Subfield ℝ) (v : Fin k → A)
    (p : MvPolynomial (Fin k) ℚ) :
    MvPolynomial.eval₂ (Rat.castHom ℝ) (fun i => ((v i : A) : ℝ)) p =
      ((MvPolynomial.eval₂ (Rat.castHom A) (fun i => v i) p : A) : ℝ) := by
  symm
  change A.subtype (MvPolynomial.eval₂ (Rat.castHom A) (fun i => v i) p) = _
  rw [MvPolynomial.eval₂_comp_left A.subtype (Rat.castHom A) (fun i => v i) p]
  congr 1

/- accepted add_to_file helper 4 -/
def HasSubfieldPoint (A : Subfield ℝ) :
    (Σ k : ℕ, Set (Fin k → ℝ)) → Prop
  | ⟨k, S⟩ => ∃ v : Fin k → A, (fun i => ((v i : A) : ℝ)) ∈ S

/- accepted add_to_file helper 5 -/
lemma fin_append_subfield_cast {k d : ℕ} (A : Subfield ℝ)
    (v : Fin k → A) (y : Fin d → A) :
    Fin.append (fun i => ((v i : A) : ℝ)) (fun i => ((y i : A) : ℝ)) =
      fun i => ((Fin.append v y i : A) : ℝ) := by
  funext i
  induction i using Fin.addCases with
  | left i => simp [Fin.append_left]
  | right i => simp [Fin.append_right]

/- accepted add_to_file helper 6 -/
lemma stable_projection_hasSubfieldPoint_iff
    (A : Subfield ℝ) {k d : ℕ}
    (S : Set (Fin k → ℝ)) (T : Set (Fin (k + d) → ℝ))
    (r s : ℕ)
    (φ : Fin r → Fin d → MvPolynomial (Fin k) ℤ)
    (ψ : Fin s → Fin d → MvPolynomial (Fin k) ℤ)
    (hsurj : ∀ v ∈ S, ∃ v' : Fin d → ℝ, Fin.append v v' ∈ T)
    (hchar : ∀ (v : Fin k → ℝ) (v' : Fin d → ℝ),
      Fin.append v v' ∈ T ↔
        v ∈ S ∧
        (∀ i : Fin r,
          ∑ j : Fin d,
            MvPolynomial.eval₂ (Int.castRingHom ℝ) v (φ i j) * v' j > 0) ∧
        (∀ i : Fin s,
          ∑ j : Fin d,
            MvPolynomial.eval₂ (Int.castRingHom ℝ) v (ψ i j) * v' j = 0)) :
    HasSubfieldPoint A ⟨k, S⟩ ↔ HasSubfieldPoint A ⟨k + d, T⟩ := by
  constructor
  · rintro ⟨v, hv⟩
    let vR : Fin k → ℝ := fun i => ((v i : A) : ℝ)
    rcases hsurj vR hv with ⟨x, hx⟩
    rcases (hchar vR x).mp hx with ⟨_, hineq, heq⟩
    let a : Fin r → Fin d → A := fun i j =>
      MvPolynomial.eval₂ (Int.castRingHom A) (fun l => v l) (φ i j)
    let b : Fin s → Fin d → A := fun i j =>
      MvPolynomial.eval₂ (Int.castRingHom A) (fun l => v l) (ψ i j)
    have hineq' : ∀ i : Fin r,
        ∑ j : Fin d, ((a i j : A) : ℝ) * x j > 0 := by
      intro i
      simpa [a, vR, eval₂_int_subfield_cast] using hineq i
    have heq' : ∀ i : Fin s,
        ∑ j : Fin d, ((b i j : A) : ℝ) * x j = 0 := by
      intro i
      simpa [b, vR, eval₂_int_subfield_cast] using heq i
    rcases exists_subfield_linear_solution A a b x hineq' heq' with ⟨y, hypos, hyeq⟩
    refine ⟨Fin.append v y, ?_⟩
    have hyposR : ∀ i : Fin r,
        ∑ j : Fin d,
          MvPolynomial.eval₂ (Int.castRingHom ℝ) vR (φ i j) *
            (((y j : A) : ℝ)) > 0 := by
      intro i
      simpa [a, vR, eval₂_int_subfield_cast] using hypos i
    have hyeqR : ∀ i : Fin s,
        ∑ j : Fin d,
          MvPolynomial.eval₂ (Int.castRingHom ℝ) vR (ψ i j) *
            (((y j : A) : ℝ)) = 0 := by
      intro i
      simpa [b, vR, eval₂_int_subfield_cast] using hyeq i
    have hmem : Fin.append vR (fun i => ((y i : A) : ℝ)) ∈ T := by
      exact (hchar vR (fun i => ((y i : A) : ℝ))).mpr ⟨hv, hyposR, hyeqR⟩
    rwa [fin_append_subfield_cast A v y] at hmem
  · rintro ⟨w, hw⟩
    let v : Fin k → A := fun i => w (Fin.castAdd d i)
    let y : Fin d → A := fun i => w (Fin.natAdd k i)
    let vR : Fin k → ℝ := fun i => ((v i : A) : ℝ)
    let yR : Fin d → ℝ := fun i => ((y i : A) : ℝ)
    have hmem : Fin.append vR yR ∈ T := by
      have hrestrict :=
        @Fin.append_castAdd_natAdd k d ℝ (fun i => ((w i : A) : ℝ))
      rw [hrestrict]
      exact hw
    rcases (hchar vR yR).mp hmem with ⟨hvS, _, _⟩
    exact ⟨v, hvS⟩

/- accepted add_to_file helper 7 -/
lemma stable_rational_hasSubfieldPoint_iff
    (A : Subfield ℝ) {k l : ℕ}
    (S : Set (Fin k → ℝ)) (T : Set (Fin l → ℝ))
    (h : S ≃ₜ T)
    (hfwd : ∀ i : Fin l, ∃ p q : MvPolynomial (Fin k) ℚ,
      ∀ v : S,
        MvPolynomial.eval₂ (Rat.castHom ℝ) (v : Fin k → ℝ) q ≠ 0 ∧
        (h v : Fin l → ℝ) i =
          MvPolynomial.eval₂ (Rat.castHom ℝ) (v : Fin k → ℝ) p /
            MvPolynomial.eval₂ (Rat.castHom ℝ) (v : Fin k → ℝ) q)
    (hinv : ∀ i : Fin k, ∃ p q : MvPolynomial (Fin l) ℚ,
      ∀ w : T,
        MvPolynomial.eval₂ (Rat.castHom ℝ) (w : Fin l → ℝ) q ≠ 0 ∧
        (h.symm w : Fin k → ℝ) i =
          MvPolynomial.eval₂ (Rat.castHom ℝ) (w : Fin l → ℝ) p /
            MvPolynomial.eval₂ (Rat.castHom ℝ) (w : Fin l → ℝ) q) :
    HasSubfieldPoint A ⟨k, S⟩ ↔ HasSubfieldPoint A ⟨l, T⟩ := by
  constructor
  · rintro ⟨v, hv⟩
    let vR : Fin k → ℝ := fun i => ((v i : A) : ℝ)
    let vS : S := ⟨vR, hv⟩
    choose p q hpq using hfwd
    let w : Fin l → A := fun i =>
      MvPolynomial.eval₂ (Rat.castHom A) (fun j => v j) (p i) /
        MvPolynomial.eval₂ (Rat.castHom A) (fun j => v j) (q i)
    refine ⟨w, ?_⟩
    have hcoord : (fun i => ((w i : A) : ℝ)) = (h vS : Fin l → ℝ) := by
      funext i
      rcases hpq i vS with ⟨_, hmap⟩
      rw [hmap]
      dsimp [w, vS, vR]
      norm_num [eval₂_rat_subfield_cast]
    rw [hcoord]
    exact (h vS).property
  · rintro ⟨w, hw⟩
    let wR : Fin l → ℝ := fun i => ((w i : A) : ℝ)
    let wT : T := ⟨wR, hw⟩
    choose p q hpq using hinv
    let v : Fin k → A := fun i =>
      MvPolynomial.eval₂ (Rat.castHom A) (fun j => w j) (p i) /
        MvPolynomial.eval₂ (Rat.castHom A) (fun j => w j) (q i)
    refine ⟨v, ?_⟩
    have hcoord : (fun i => ((v i : A) : ℝ)) = (h.symm wT : Fin k → ℝ) := by
      funext i
      rcases hpq i wT with ⟨_, hmap⟩
      rw [hmap]
      dsimp [v, wT, wR]
      norm_num [eval₂_rat_subfield_cast]
    rw [hcoord]
    exact (h.symm wT).property

/- accepted add_to_file helper 8 -/
lemma stable_elementary_hasSubfieldPoint_iff
    (A : Subfield ℝ) {X Y : Σ k : ℕ, Set (Fin k → ℝ)}
    (h : (∃ (k d : ℕ) (S : Set (Fin k → ℝ)) (T : Set (Fin (k + d) → ℝ)),
          X = ⟨k, S⟩ ∧ Y = ⟨k + d, T⟩ ∧
          ∃ (r s : ℕ)
            (φ : Fin r → Fin d → MvPolynomial (Fin k) ℤ)
            (ψ : Fin s → Fin d → MvPolynomial (Fin k) ℤ),
            (∀ v ∈ S, ∃ v' : Fin d → ℝ, Fin.append v v' ∈ T) ∧
            ∀ (v : Fin k → ℝ) (v' : Fin d → ℝ),
              Fin.append v v' ∈ T ↔
                v ∈ S ∧
                (∀ i : Fin r,
                  ∑ j : Fin d,
                    MvPolynomial.eval₂ (Int.castRingHom ℝ) v (φ i j) * v' j > 0) ∧
                (∀ i : Fin s,
                  ∑ j : Fin d,
                    MvPolynomial.eval₂ (Int.castRingHom ℝ) v (ψ i j) * v' j = 0)) ∨
        (∃ (k l : ℕ) (S : Set (Fin k → ℝ)) (T : Set (Fin l → ℝ)),
          X = ⟨k, S⟩ ∧ Y = ⟨l, T⟩ ∧
          ∃ h : S ≃ₜ T,
            (∀ i : Fin l, ∃ p q : MvPolynomial (Fin k) ℚ,
              ∀ v : S,
                MvPolynomial.eval₂ (Rat.castHom ℝ) (v : Fin k → ℝ) q ≠ 0 ∧
                (h v : Fin l → ℝ) i =
                  MvPolynomial.eval₂ (Rat.castHom ℝ) (v : Fin k → ℝ) p /
                    MvPolynomial.eval₂ (Rat.castHom ℝ) (v : Fin k → ℝ) q) ∧
            (∀ i : Fin k, ∃ p q : MvPolynomial (Fin l) ℚ,
              ∀ w : T,
                MvPolynomial.eval₂ (Rat.castHom ℝ) (w : Fin l → ℝ) q ≠ 0 ∧
                (h.symm w : Fin k → ℝ) i =
                  MvPolynomial.eval₂ (Rat.castHom ℝ) (w : Fin l → ℝ) p /
                    MvPolynomial.eval₂ (Rat.castHom ℝ) (w : Fin l → ℝ) q))) :
    HasSubfieldPoint A X ↔ HasSubfieldPoint A Y := by
  rcases h with hproj | hrat
  · rcases hproj with ⟨k, d, S, T, hX, hY, r, s, φ, ψ, hsurj, hchar⟩
    simpa [hX, hY] using
      stable_projection_hasSubfieldPoint_iff A S T r s φ ψ hsurj hchar
  · rcases hrat with ⟨k, l, S, T, hX, hY, h, hfwd, hinv⟩
    simpa [hX, hY] using
      stable_rational_hasSubfieldPoint_iff A S T h hfwd hinv

/- verified submission -/
theorem stable_equivalence_empty_subfield_points_iff
    (n m : ℕ) (V : Set (Fin n → ℝ)) (W : Set (Fin m → ℝ))
    (A : Subfield ℝ)
    (hA : Algebra.IsAlgebraic ℚ A)
    (hV : V ∈ BooleanSubalgebra.closure
      {s : Set (Fin n → ℝ) |
        ∃ p : MvPolynomial (Fin n) ℝ,
          s = {x | MvPolynomial.eval x p = 0} ∨
          s = {x | MvPolynomial.eval x p > 0}})
    (hW : W ∈ BooleanSubalgebra.closure
      {s : Set (Fin m → ℝ) |
        ∃ p : MvPolynomial (Fin m) ℝ,
          s = {x | MvPolynomial.eval x p = 0} ∨
          s = {x | MvPolynomial.eval x p > 0}})
    (hstable : Relation.EqvGen
      (fun X Y : Σ k : ℕ, Set (Fin k → ℝ) =>
        (∃ (k d : ℕ) (S : Set (Fin k → ℝ)) (T : Set (Fin (k + d) → ℝ)),
          X = ⟨k, S⟩ ∧ Y = ⟨k + d, T⟩ ∧
          ∃ (r s : ℕ)
            (φ : Fin r → Fin d → MvPolynomial (Fin k) ℤ)
            (ψ : Fin s → Fin d → MvPolynomial (Fin k) ℤ),
            (∀ v ∈ S, ∃ v' : Fin d → ℝ, Fin.append v v' ∈ T) ∧
            ∀ (v : Fin k → ℝ) (v' : Fin d → ℝ),
              Fin.append v v' ∈ T ↔
                v ∈ S ∧
                (∀ i : Fin r,
                  ∑ j : Fin d,
                    MvPolynomial.eval₂ (Int.castRingHom ℝ) v (φ i j) * v' j > 0) ∧
                (∀ i : Fin s,
                  ∑ j : Fin d,
                    MvPolynomial.eval₂ (Int.castRingHom ℝ) v (ψ i j) * v' j = 0)) ∨
        (∃ (k l : ℕ) (S : Set (Fin k → ℝ)) (T : Set (Fin l → ℝ)),
          X = ⟨k, S⟩ ∧ Y = ⟨l, T⟩ ∧
          ∃ h : S ≃ₜ T,
            (∀ i : Fin l, ∃ p q : MvPolynomial (Fin k) ℚ,
              ∀ v : S,
                MvPolynomial.eval₂ (Rat.castHom ℝ) (v : Fin k → ℝ) q ≠ 0 ∧
                (h v : Fin l → ℝ) i =
                  MvPolynomial.eval₂ (Rat.castHom ℝ) (v : Fin k → ℝ) p /
                    MvPolynomial.eval₂ (Rat.castHom ℝ) (v : Fin k → ℝ) q) ∧
            (∀ i : Fin k, ∃ p q : MvPolynomial (Fin l) ℚ,
              ∀ w : T,
                MvPolynomial.eval₂ (Rat.castHom ℝ) (w : Fin l → ℝ) q ≠ 0 ∧
                (h.symm w : Fin k → ℝ) i =
                  MvPolynomial.eval₂ (Rat.castHom ℝ) (w : Fin l → ℝ) p /
                    MvPolynomial.eval₂ (Rat.castHom ℝ) (w : Fin l → ℝ) q)))
      ⟨n, V⟩ ⟨m, W⟩) :
    (¬ ∃ v : Fin n → A, (fun i => ((v i : A) : ℝ)) ∈ V) ↔
      (¬ ∃ w : Fin m → A, (fun i => ((w i : A) : ℝ)) ∈ W) := by
  have hpoints : HasSubfieldPoint A ⟨n, V⟩ ↔ HasSubfieldPoint A ⟨m, W⟩ := by
    refine Relation.EqvGen.rec
      (motive := fun x y _ => HasSubfieldPoint A x ↔ HasSubfieldPoint A y)
      ?_ ?_ ?_ ?_ hstable
    · intro x y hxy
      exact stable_elementary_hasSubfieldPoint_iff A hxy
    · intro x
      rfl
    · intro x y hxy ih
      exact ih.symm
    · intro x y z hxy hyz ihxy ihyz
      exact ihxy.trans ihyz
  simpa [HasSubfieldPoint] using not_congr hpoints


#check_dependency_graph "stable_equivalence_empty_subfield_points_iff" against "{\"edges\":[{\"conclusion\":{\"name\":\"hpoints\",\"statement\":\"Rollout_p2109_stable_equivalence_empty_subfield_points_i.HasSubfieldPoint A ⟨n, V⟩ ↔ Rollout_p2109_stable_equivalence_empty_subfield_points_i.HasSubfieldPoint A ⟨m, W⟩\"},\"graphEdgeId\":\"h_001_hpoints\",\"premises\":[{\"name\":\"hstable\",\"statement\":\"Relation.EqvGen (fun X Y => (∃ k d S T, X = ⟨k, S⟩ ∧ Y = ⟨k + d, T⟩ ∧ ∃ r s φ ψ, (∀ v ∈ S, ∃ v', Fin.append v v' ∈ T) ∧ ∀ (v : Fin k → ℝ) (v' : Fin d → ℝ), Fin.append v v' ∈ T ↔ v ∈ S ∧ (∀ (i : Fin r), ∑ j, MvPolynomial.eval₂ (Int.castRingHom ℝ) v (φ i j) * v' j > 0) ∧ ∀ (i : Fin s), ∑ j, MvPolynomial.eval₂ (Int.castRingHom ℝ) v (ψ i j) * v' j = 0) ∨ ∃ k l S T, X = ⟨k, S⟩ ∧ Y = ⟨l, T⟩ ∧ ∃ h, (∀ (i : Fin l), ∃ p q, ∀ (v : ↑S), MvPolynomial.eval₂ (Rat.castHom ℝ) (↑v) q ≠ 0 ∧ ↑(h v) i = MvPolynomial.eval₂ (Rat.castHom ℝ) (↑v) p / MvPolynomial.eval₂ (Rat.castHom ℝ) (↑v) q) ∧ ∀ (i : Fin k), ∃ p q, ∀ (w : ↑T), MvPolynomial.eval₂ (Rat.castHom ℝ) (↑w) q ≠ 0 ∧ ↑(h.symm w) i = MvPolynomial.eval₂ (Rat.castHom ℝ) (↑w) p / MvPolynomial.eval₂ (Rat.castHom ℝ) (↑w) q) ⟨n, V⟩ ⟨m, W⟩\"}],\"rawEdgeId\":\"telescope_9\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(¬∃ v, (fun i => ↑(v i)) ∈ V) ↔ ¬∃ w, (fun i => ↑(w i)) ∈ W\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hpoints\",\"statement\":\"Rollout_p2109_stable_equivalence_empty_subfield_points_i.HasSubfieldPoint A ⟨n, V⟩ ↔ Rollout_p2109_stable_equivalence_empty_subfield_points_i.HasSubfieldPoint A ⟨m, W⟩\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2109_stable_equivalence_empty_subfield_points_i\",\"reconstructedProofSha256\":\"0491507063df14fc42c2ac8996ab55388da578e868a0a8c896a2ea5e42e201c0\",\"selectedEdgeCount\":2,\"theoremName\":\"stable_equivalence_empty_subfield_points_iff\",\"topologySha256\":\"83c1f3429a819d27d51092c231154faa95c7febde4ce81a49b36cda28c209492\"}"
