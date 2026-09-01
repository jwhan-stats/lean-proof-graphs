import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p0912_catlin_vertical_curve_is_geodesic
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: ff55e243bcb013b3bb1fe2d4b53943a217b77c71844ab85c4d3c84a7f12cdfd5
-- reconstructed_proof_sha256: cc6d4973114cc0c7a9784655505a6f48359de722e3a69ec905f1f7d26470c626
-- selected_edge_count: 8

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

#check_dependency_graph "catlin_vertical_curve_is_geodesic" against "{\"edges\":[{\"conclusion\":{\"name\":\"heval\",\"statement\":\"evalAt = Rollout_p0912_catlin_vertical_curve_is_geodesic.evalDiag\"},\"graphEdgeId\":\"h_001_heval\",\"premises\":[],\"rawEdgeId\":\"telescope_25\"},{\"conclusion\":{\"name\":\"hr\",\"statement\":\"r = Rollout_p0912_catlin_vertical_curve_is_geodesic.catlinR p\"},\"graphEdgeId\":\"h_006_hr\",\"premises\":[],\"rawEdgeId\":\"telescope_30\"},{\"conclusion\":{\"name\":\"hM\",\"statement\":\"M = Rollout_p0912_catlin_vertical_curve_is_geodesic.catlinM m p\"},\"graphEdgeId\":\"h_007_hm\",\"premises\":[],\"rawEdgeId\":\"telescope_31\"},{\"conclusion\":{\"name\":\"hPC\",\"statement\":\"PiecewiseC1 = Rollout_p0912_catlin_vertical_curve_is_geodesic.PiecewiseC1Curve\"},\"graphEdgeId\":\"h_008_hpc\",\"premises\":[],\"rawEdgeId\":\"telescope_32\"},{\"conclusion\":{\"name\":\"hrealG\",\"statement\":\"∀ (z : ℂ), (Rollout_p0912_catlin_vertical_curve_is_geodesic.evalDiag z p).im = 0\"},\"graphEdgeId\":\"h_009_hrealg\",\"premises\":[{\"name\":\"hreal\",\"statement\":\"∀ (z : ℂ), (evalAt z p).im = 0\"},{\"name\":\"heval\",\"statement\":\"evalAt = Rollout_p0912_catlin_vertical_curve_is_geodesic.evalDiag\"}],\"rawEdgeId\":\"telescope_33\"},{\"conclusion\":{\"name\":\"hΩdef\",\"statement\":\"Ω = {q | Rollout_p0912_catlin_vertical_curve_is_geodesic.catlinR p q < 0}\"},\"graphEdgeId\":\"h_010_h_def\",\"premises\":[{\"name\":\"hr\",\"statement\":\"r = Rollout_p0912_catlin_vertical_curve_is_geodesic.catlinR p\"}],\"rawEdgeId\":\"telescope_34\"},{\"conclusion\":{\"name\":\"hb\",\"statement\":\"Rollout_p0912_catlin_vertical_curve_is_geodesic.catlinR p (z₀, w₀) = 0\"},\"graphEdgeId\":\"h_011_hb\",\"premises\":[{\"name\":\"hfront\",\"statement\":\"(z₀, w₀) ∈ frontier Ω\"},{\"name\":\"hΩdef\",\"statement\":\"Ω = {q | Rollout_p0912_catlin_vertical_curve_is_geodesic.catlinR p q < 0}\"}],\"rawEdgeId\":\"telescope_35\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(∀ (t : ℝ), σ t ∈ Ω) ∧ ∀ (s t : ℝ), d (σ s) (σ t) = |s - t|\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"ha\",\"statement\":\"0 < a\"},{\"name\":\"hM\",\"statement\":\"M = Rollout_p0912_catlin_vertical_curve_is_geodesic.catlinM m p\"},{\"name\":\"hPC\",\"statement\":\"PiecewiseC1 = Rollout_p0912_catlin_vertical_curve_is_geodesic.PiecewiseC1Curve\"},{\"name\":\"hrealG\",\"statement\":\"∀ (z : ℂ), (Rollout_p0912_catlin_vertical_curve_is_geodesic.evalDiag z p).im = 0\"},{\"name\":\"hΩdef\",\"statement\":\"Ω = {q | Rollout_p0912_catlin_vertical_curve_is_geodesic.catlinR p q < 0}\"},{\"name\":\"hb\",\"statement\":\"Rollout_p0912_catlin_vertical_curve_is_geodesic.catlinR p (z₀, w₀) = 0\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0912_catlin_vertical_curve_is_geodesic\",\"reconstructedProofSha256\":\"cc6d4973114cc0c7a9784655505a6f48359de722e3a69ec905f1f7d26470c626\",\"selectedEdgeCount\":8,\"theoremName\":\"catlin_vertical_curve_is_geodesic\",\"topologySha256\":\"ff55e243bcb013b3bb1fe2d4b53943a217b77c71844ab85c4d3c84a7f12cdfd5\"}"
