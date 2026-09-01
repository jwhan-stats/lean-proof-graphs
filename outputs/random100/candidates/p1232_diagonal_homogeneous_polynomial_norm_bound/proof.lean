import Mathlib

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
