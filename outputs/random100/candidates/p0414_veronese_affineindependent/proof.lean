import Mathlib

/- accepted add_to_file helper 1 -/
noncomputable section

def VeroneseIndex (m p q : ℕ) := {ab : (Fin m →₀ ℕ) × (Fin m →₀ ℕ) //
  ab.1.sum (fun _ n => n) ≤ p ∧ ab.2.sum (fun _ n => n) ≤ q}

noncomputable def veroneseVector (m p q : ℕ) (z : Fin m → ℂ) : VeroneseIndex m p q → ℂ :=
  fun ab =>
    ab.1.1.prod (fun i n => z i ^ n) *
      ab.1.2.prod (fun i n => (starRingEnd ℂ (z i)) ^ n)

noncomputable def coordForNe {m : ℕ} {a b : Fin m → ℂ} (h : a ≠ b) : Fin m :=
  Classical.choose (Function.ne_iff.mp h)

lemma coordForNe_apply_ne {m : ℕ} {a b : Fin m → ℂ} (h : a ≠ b) :
    a (coordForNe h) ≠ b (coordForNe h) :=
  Classical.choose_spec (Function.ne_iff.mp h)

noncomputable def veroneseLagrangeFactor
    {m r : ℕ} (x : Fin r → (Fin m → ℂ)) {j k : Fin r} (hjk : x j ≠ x k) :
    MvPolynomial (Fin m) ℂ :=
  let i := coordForNe hjk
  (MvPolynomial.X i - MvPolynomial.C (x j i)) *
    MvPolynomial.C ((x k i - x j i)⁻¹)

lemma veroneseLagrangeFactor_totalDegree_le
    {m r : ℕ} (x : Fin r → (Fin m → ℂ)) {j k : Fin r} (hjk : x j ≠ x k) :
    (veroneseLagrangeFactor x hjk).totalDegree ≤ 1 := by
  unfold veroneseLagrangeFactor
  let i := coordForNe hjk
  have h₁ : (MvPolynomial.X i - MvPolynomial.C (x j i) :
      MvPolynomial (Fin m) ℂ).totalDegree ≤ 1 := by
    calc
      (MvPolynomial.X i - MvPolynomial.C (x j i) :
          MvPolynomial (Fin m) ℂ).totalDegree
          ≤ max (MvPolynomial.totalDegree (MvPolynomial.X i :
              MvPolynomial (Fin m) ℂ))
              (MvPolynomial.totalDegree (MvPolynomial.C (x j i) :
              MvPolynomial (Fin m) ℂ)) :=
        MvPolynomial.totalDegree_sub _ _
      _ = 1 := by simp [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
  calc
    ((MvPolynomial.X i - MvPolynomial.C (x j i)) *
        MvPolynomial.C ((x k i - x j i)⁻¹) :
        MvPolynomial (Fin m) ℂ).totalDegree
        ≤ (MvPolynomial.X i - MvPolynomial.C (x j i) :
            MvPolynomial (Fin m) ℂ).totalDegree +
          (MvPolynomial.C ((x k i - x j i)⁻¹) :
            MvPolynomial (Fin m) ℂ).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ ≤ 1 + 0 := Nat.add_le_add h₁ (by rw [MvPolynomial.totalDegree_C])
    _ = 1 := by norm_num

@[simp]
lemma veroneseLagrangeFactor_eval_left
    {m r : ℕ} (x : Fin r → (Fin m → ℂ)) {j k : Fin r} (hjk : x j ≠ x k) :
    MvPolynomial.eval (x j) (veroneseLagrangeFactor x hjk) = 0 := by
  simp [veroneseLagrangeFactor]

@[simp]
lemma veroneseLagrangeFactor_eval_right
    {m r : ℕ} (x : Fin r → (Fin m → ℂ)) {j k : Fin r} (hjk : x j ≠ x k) :
    MvPolynomial.eval (x k) (veroneseLagrangeFactor x hjk) = 1 := by
  let i := coordForNe hjk
  have hne : x k i - x j i ≠ 0 := by
    intro hzero
    apply coordForNe_apply_ne hjk
    exact (sub_eq_zero.mp (by simpa [i] using hzero)).symm
  simp [veroneseLagrangeFactor, i, hne]

noncomputable def veroneseLagrangePoly
    {m r : ℕ} (x : Fin r → (Fin m → ℂ)) (hx : Function.Injective x) (k : Fin r) :
    MvPolynomial (Fin m) ℂ :=
  (Finset.univ.erase k).attach.prod fun j =>
    veroneseLagrangeFactor x (hx.ne (Finset.mem_erase.mp j.2).1)

lemma veroneseLagrangePoly_totalDegree_le
    {m p r : ℕ} (hrp : r ≤ p + 1) (x : Fin r → (Fin m → ℂ))
    (hx : Function.Injective x) (k : Fin r) :
    (veroneseLagrangePoly x hx k).totalDegree ≤ p := by
  have hcard : (Finset.univ.erase k).card = r - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin]
  calc
    (veroneseLagrangePoly x hx k).totalDegree
        ≤ ∑ j ∈ (Finset.univ.erase k).attach,
            (veroneseLagrangeFactor x (hx.ne (Finset.mem_erase.mp j.2).1)).totalDegree := by
          simpa [veroneseLagrangePoly] using
            MvPolynomial.totalDegree_finset_prod (Finset.univ.erase k).attach
              (fun j => veroneseLagrangeFactor x (hx.ne (Finset.mem_erase.mp j.2).1))
    _ ≤ ∑ j ∈ (Finset.univ.erase k).attach, 1 := by
          exact Finset.sum_le_sum fun j hj =>
            veroneseLagrangeFactor_totalDegree_le x _
    _ = r - 1 := by simp [hcard]
    _ ≤ p := by omega

@[simp]
lemma veroneseLagrangePoly_eval_self
    {m r : ℕ} (x : Fin r → (Fin m → ℂ)) (hx : Function.Injective x) (k : Fin r) :
    MvPolynomial.eval (x k) (veroneseLagrangePoly x hx k) = 1 := by
  simp [veroneseLagrangePoly, MvPolynomial.eval_prod]

lemma veroneseLagrangePoly_eval_of_ne
    {m r : ℕ} (x : Fin r → (Fin m → ℂ)) (hx : Function.Injective x)
    {l k : Fin r} (hlk : l ≠ k) :
    MvPolynomial.eval (x l) (veroneseLagrangePoly x hx k) = 0 := by
  rw [veroneseLagrangePoly, MvPolynomial.eval_prod]
  let l' : ↥(Finset.univ.erase k) :=
    ⟨l, Finset.mem_erase.mpr ⟨hlk, Finset.mem_univ l⟩⟩
  have hmem : l' ∈ (Finset.univ.erase k).attach := Finset.mem_attach _ _
  have hzero : MvPolynomial.eval (x l)
      (veroneseLagrangeFactor x (hx.ne (Finset.mem_erase.mp l'.2).1)) = 0 := by
    simp [l']
  exact Finset.prod_eq_zero hmem hzero

end

/- accepted add_to_file helper 2 -/
noncomputable section

noncomputable def veronesePolyEval
    (m p q : ℕ) (Q : MvPolynomial (Fin m) ℂ) (hQ : Q.totalDegree ≤ p) :
    (VeroneseIndex m p q → ℂ) →ₗ[ℂ] ℂ where
  toFun w := Q.support.attach.sum fun a =>
    Q.coeff a.1 * w ⟨(a.1, 0),
      (MvPolynomial.le_totalDegree a.2).trans hQ,
      by simp⟩
  map_add' w u := by
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' c w := by
    simp [Finset.mul_sum, mul_left_comm, mul_assoc]

lemma veronesePolyEval_veroneseVector
    (m p q : ℕ) (Q : MvPolynomial (Fin m) ℂ) (hQ : Q.totalDegree ≤ p)
    (z : Fin m → ℂ) :
    veronesePolyEval m p q Q hQ (veroneseVector m p q z) =
      MvPolynomial.eval z Q := by
  rw [MvPolynomial.eval_eq']
  simpa [veronesePolyEval, veroneseVector] using
    (Finset.sum_attach Q.support
      (fun a => Q.coeff a * a.prod (fun i n => z i ^ n)))

end

/- accepted add_to_file helper 3 -/
theorem veronese_linearIndependent_complex
    (m p q r : ℕ) (hrp : r ≤ p + 1)
    (x : Fin r → (Fin m → ℂ)) (hx : Function.Injective x) :
    LinearIndependent ℂ (fun j : Fin r => veroneseVector m p q (x j)) := by
  rw [Fintype.linearIndependent_iff]
  intro g h k
  let Q := veroneseLagrangePoly x hx k
  have hQ : Q.totalDegree ≤ p := by
    exact veroneseLagrangePoly_totalDegree_le hrp x hx k
  let L := veronesePolyEval m p q Q hQ
  have hzero : L (∑ j, g j • veroneseVector m p q (x j)) = 0 := by
    simpa using congrArg L h
  have hcalc1 : L (∑ j, g j • veroneseVector m p q (x j)) =
      ∑ j, g j * MvPolynomial.eval (x j) Q := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp [L, veronesePolyEval_veroneseVector]
  have hsum : (∑ j, g j * MvPolynomial.eval (x j) Q) = g k := by
    rw [Finset.sum_eq_single k]
    · simp [Q]
    · intro j hj hjk
      rw [show MvPolynomial.eval (x j) Q = 0 from by
        simpa [Q] using veroneseLagrangePoly_eval_of_ne x hx hjk]
      simp
    · intro hk
      simp at hk
  exact (hcalc1.trans hsum).symm.trans hzero

/- verified submission -/
theorem veronese_affineIndependent
    (m p q r : ℕ) (hr : 1 ≤ r) (hrp : r ≤ p + 1)
    (x : Fin r → (Fin m → ℂ)) (hx : Function.Injective x) :
    let I := {ab : (Fin m →₀ ℕ) × (Fin m →₀ ℕ) //
      ab.1.sum (fun _ n => n) ≤ p ∧ ab.2.sum (fun _ n => n) ≤ q}
    let v : (Fin m → ℂ) → (I → ℂ) := fun z ab =>
      ab.1.1.prod (fun i n => z i ^ n) *
        ab.1.2.prod (fun i n => (starRingEnd ℂ (z i)) ^ n)
    AffineIndependent ℝ (fun j : Fin r => v (x j)) := by
  change AffineIndependent ℝ (fun j : Fin r => veroneseVector m p q (x j))
  have hC : LinearIndependent ℂ (fun j : Fin r => veroneseVector m p q (x j)) :=
    veronese_linearIndependent_complex m p q r hrp x hx
  have hinj : Function.Injective fun a : ℝ => a • (1 : ℂ) := by
    intro a b h
    exact Complex.ofReal_injective (by simpa using h)
  exact (hC.restrict_scalars hinj).affineIndependent
