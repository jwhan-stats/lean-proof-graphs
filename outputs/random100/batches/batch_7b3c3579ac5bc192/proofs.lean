import Mathlib

/- Generated only to amortize Mathlib loading during graph export. -/

namespace Rollout_p0414_veronese_affineindependent

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

end Rollout_p0414_veronese_affineindependent

namespace Rollout_p2247_sylow_rank_two_index_prime_subgroups

/- accepted add_to_file helper 1 -/
lemma comm_isComplement'_of_sup_top_inf_bot {G : Type*} [CommGroup G] {H K : Subgroup G}
    (hs : H ⊔ K = ⊤) (hi : H ⊓ K = ⊥) : H.IsComplement' K := by
  unfold Subgroup.IsComplement'
  constructor
  · intro a b hab
    change ((a.1 : G) * a.2) = ((b.1 : G) * b.2) at hab
    have heq : ((a.1 : G)⁻¹ * b.1) = ((a.2 : G) * (b.2 : G)⁻¹) := by
      calc
        ((a.1 : G)⁻¹ * b.1)
            = ((a.1 : G)⁻¹ * ((b.1 : G) * b.2) * (b.2 : G)⁻¹) := by group
        _ = ((a.1 : G)⁻¹ * ((a.1 : G) * a.2) * (b.2 : G)⁻¹) := by rw [hab]
        _ = ((a.2 : G) * (b.2 : G)⁻¹) := by group
    have hmem : ((a.1 : G)⁻¹ * b.1) ∈ H ⊓ K := by
      rw [Subgroup.mem_inf]
      constructor
      · exact H.mul_mem (H.inv_mem a.1.property) b.1.property
      · rw [heq]
        exact K.mul_mem a.2.property (K.inv_mem b.2.property)
    have hone : ((a.1 : G)⁻¹ * b.1) = 1 := by
      exact (Subgroup.eq_bot_iff_forall (H ⊓ K)).mp hi _ hmem
    have h1 : (a.1 : G) = b.1 := inv_mul_eq_one.mp hone
    have h2 : (a.2 : G) = b.2 := by
      have hone2 : ((a.2 : G) * (b.2 : G)⁻¹) = 1 := by rw [← heq, hone]
      exact mul_inv_eq_one.mp hone2
    ext <;> assumption
  · intro g
    have hg : (g : G) ∈ H ⊔ K := by rw [hs]; exact Subgroup.mem_top g
    rw [Subgroup.mem_sup] at hg
    rcases hg with ⟨h, hh, k, hk, hhk⟩
    exact ⟨⟨⟨h, hh⟩, ⟨k, hk⟩⟩, by simpa using hhk⟩

/- accepted add_to_file helper 2 -/
def commSubgroupProdHom {G : Type*} [CommGroup G] (H K : Subgroup G) :
    H × K →* G where
  toFun p := (p.1 : G) * p.2
  map_one' := by simp
  map_mul' := by
    intro a b
    simp [mul_left_comm, mul_comm]

/- accepted add_to_file helper 3 -/
lemma commSubgroupProdHom_range {G : Type*} [CommGroup G] (H K : Subgroup G) :
    (commSubgroupProdHom H K).range = H ⊔ K := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨p, rfl⟩
    exact Subgroup.mul_mem_sup p.1.property p.2.property
  · intro hz
    rw [Subgroup.mem_sup] at hz
    rcases hz with ⟨h, hh, k, hk, hhk⟩
    exact ⟨⟨⟨h, hh⟩, ⟨k, hk⟩⟩, by simpa [commSubgroupProdHom] using hhk⟩

lemma commSubgroupProdHom_injective {G : Type*} [CommGroup G] {H K : Subgroup G}
    (hi : H ⊓ K = ⊥) : Function.Injective (commSubgroupProdHom H K) := by
  intro a b hab
  change ((a.1 : G) * a.2) = ((b.1 : G) * b.2) at hab
  have heq : ((a.1 : G)⁻¹ * b.1) = ((a.2 : G) * (b.2 : G)⁻¹) := by
    calc
      ((a.1 : G)⁻¹ * b.1)
          = ((a.1 : G)⁻¹ * ((b.1 : G) * b.2) * (b.2 : G)⁻¹) := by group
      _ = ((a.1 : G)⁻¹ * ((a.1 : G) * a.2) * (b.2 : G)⁻¹) := by rw [hab]
      _ = ((a.2 : G) * (b.2 : G)⁻¹) := by group
  have hmem : ((a.1 : G)⁻¹ * b.1) ∈ H ⊓ K := by
    rw [Subgroup.mem_inf]
    constructor
    · exact H.mul_mem (H.inv_mem a.1.property) b.1.property
    · rw [heq]
      exact K.mul_mem a.2.property (K.inv_mem b.2.property)
  have hone : ((a.1 : G)⁻¹ * b.1) = 1 := by
    exact (Subgroup.eq_bot_iff_forall (H ⊓ K)).mp hi _ hmem
  have h1 : (a.1 : G) = b.1 := inv_mul_eq_one.mp hone
  have h2 : (a.2 : G) = b.2 := by
    have hone2 : ((a.2 : G) * (b.2 : G)⁻¹) = 1 := by rw [← heq, hone]
    exact mul_inv_eq_one.mp hone2
  ext <;> assumption

/- accepted add_to_file helper 4 -/
lemma Nat_card_sup_of_inf_bot {G : Type*} [CommGroup G] {H K : Subgroup G}
    (hi : H ⊓ K = ⊥) : Nat.card ↥(H ⊔ K) = Nat.card ↥H * Nat.card ↥K := by
  let f := commSubgroupProdHom H K
  have hinj : Function.Injective f.rangeRestrict := by
    rw [MonoidHom.rangeRestrict_injective_iff]
    exact commSubgroupProdHom_injective hi
  have hbij : Function.Bijective f.rangeRestrict :=
    ⟨hinj, MonoidHom.rangeRestrict_surjective f⟩
  let e : (↥H × ↥K) ≃* f.range := MulEquiv.ofBijective f.rangeRestrict hbij
  calc
    Nat.card ↥(H ⊔ K) = Nat.card ↥f.range := by rw [commSubgroupProdHom_range]
    _ = Nat.card (↥H × ↥K) := (Nat.card_congr e.toEquiv).symm
    _ = Nat.card ↥H * Nat.card ↥K := Nat.card_prod ↥H ↥K

/- accepted add_to_file helper 5 -/
lemma orderOf_prime_pow_pow {G : Type*} [Group G] {p u k : ℕ}
    (hp : p.Prime) {x : G} (hx : orderOf x = p ^ u) (hku : k ≤ u) :
    orderOf (x ^ (p ^ k)) = p ^ (u - k) := by
  have hdvd : p ^ k ∣ orderOf x := by
    rw [hx]
    exact pow_dvd_pow p hku
  rw [orderOf_pow_of_dvd (pow_ne_zero k hp.ne_zero) hdvd, hx]
  exact Nat.pow_div hku hp.pos

/- accepted add_to_file helper 6 -/
lemma zpowers_pow_inf_zpowers_pow_eq_bot {G : Type*} [Group G] {x y : G}
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) (m n : ℕ) :
    Subgroup.zpowers (x ^ m) ⊓ Subgroup.zpowers (y ^ n) = ⊥ := by
  have hxm : Subgroup.zpowers (x ^ m) ≤ Subgroup.zpowers x := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.pow_mem (Subgroup.zpowers x) (Subgroup.mem_zpowers x) m
  have hyn : Subgroup.zpowers (y ^ n) ≤ Subgroup.zpowers y := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.pow_mem (Subgroup.zpowers y) (Subgroup.mem_zpowers y) n
  apply le_antisymm
  · calc
      Subgroup.zpowers (x ^ m) ⊓ Subgroup.zpowers (y ^ n)
          ≤ Subgroup.zpowers x ⊓ Subgroup.zpowers y := inf_le_inf hxm hyn
      _ = ⊥ := hind
  · exact bot_le

/- accepted add_to_file helper 7 -/
lemma product_eq_one_of_inf_bot {G : Type*} [CommGroup G] {H K : Subgroup G}
    (hi : H ⊓ K = ⊥) {a b : G} (ha : a ∈ H) (hb : b ∈ K)
    (h : a * b = 1) : a = 1 ∧ b = 1 := by
  let f := commSubgroupProdHom H K
  have hpair : (⟨⟨a, ha⟩, ⟨b, hb⟩⟩ : H × K) = 1 := by
    apply commSubgroupProdHom_injective hi
    simp [commSubgroupProdHom, h]
  constructor
  · exact congrArg (fun p : H × K => (p.1 : G)) hpair
  · exact congrArg (fun p : H × K => (p.2 : G)) hpair

/- accepted add_to_file helper 8 -/
lemma int_prime_pow_mul_dvd_mul_iff {p u : ℕ} (hp : p.Prime) (hu : 0 < u) {i : ℤ} :
    ((p ^ u : ℕ) : ℤ) ∣ i * p ↔ ((p ^ (u - 1) : ℕ) : ℤ) ∣ i := by
  have hpow : ((p ^ u : ℕ) : ℤ) = (p ^ (u - 1) : ℕ) * p := by
    calc
      ((p ^ u : ℕ) : ℤ) = ((p ^ (u - 1 + 1) : ℕ) : ℤ) := by rw [Nat.sub_add_cancel hu]
      _ = (p ^ (u - 1) : ℕ) * p := by rw [pow_succ, Nat.cast_mul]
  have hpz : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [hpow, Int.mul_dvd_mul_iff_right hpz]

/- accepted add_to_file helper 9 -/
lemma zpow_mem_zpowers_pow_of_dvd {G : Type*} [Group G] (x : G) {n : ℕ} {i : ℤ}
    (hd : (n : ℤ) ∣ i) : x ^ i ∈ Subgroup.zpowers (x ^ n) := by
  rcases hd with ⟨t, rfl⟩
  rw [zpow_mul]
  convert Subgroup.zpow_mem _ (Subgroup.mem_zpowers (x ^ n)) t using 2
  exact zpow_natCast x n

/- accepted add_to_file helper 10 -/
lemma pow_ker_eq_zpowers_sup {G : Type*} [CommGroup G]
    {p u v : ℕ} (hp : p.Prime) (hu : 0 < u) (hv : 0 < v)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p ^ v)
    (hspan : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    (powMonoidHom p : G →* G).ker =
      Subgroup.zpowers (x ^ (p ^ (u - 1))) ⊔
        Subgroup.zpowers (y ^ (p ^ (v - 1))) := by
  ext z
  constructor
  · intro hzker
    have hzpow : z ^ p = 1 := by simpa [powMonoidHom] using hzker
    have htop : z ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
      rw [hspan]
      exact Subgroup.mem_top z
    rw [Subgroup.mem_sup] at htop
    rcases htop with ⟨a, ha, b, hb, hab⟩
    rw [Subgroup.mem_zpowers_iff] at ha hb
    rcases ha with ⟨i, rfl⟩
    rcases hb with ⟨j, rfl⟩
    subst z
    have hzpowprod : x ^ (i * p) * y ^ (j * p) = 1 := by
      calc
        x ^ (i * p) * y ^ (j * p) = (x ^ i * y ^ j) ^ p := by
          calc
            x ^ (i * p) * y ^ (j * p) = (x ^ i * y ^ j) ^ (p : ℤ) := by
              rw [mul_zpow, ← zpow_mul, ← zpow_mul]
            _ = (x ^ i * y ^ j) ^ p := by rw [zpow_natCast]
        _ = 1 := hzpow
    have hone := product_eq_one_of_inf_bot hind
      (Subgroup.zpow_mem (Subgroup.zpowers x) (Subgroup.mem_zpowers x) _)
      (Subgroup.zpow_mem (Subgroup.zpowers y) (Subgroup.mem_zpowers y) _) hzpowprod
    have hdix : (orderOf x : ℤ) ∣ i * p := orderOf_dvd_iff_zpow_eq_one.mpr hone.1
    have hdiy : (orderOf y : ℤ) ∣ j * p := orderOf_dvd_iff_zpow_eq_one.mpr hone.2
    rw [hx] at hdix
    rw [hy] at hdiy
    have hiq : ((p ^ (u - 1) : ℕ) : ℤ) ∣ i := (int_prime_pow_mul_dvd_mul_iff hp hu).mp hdix
    have hjq : ((p ^ (v - 1) : ℕ) : ℤ) ∣ j := (int_prime_pow_mul_dvd_mul_iff hp hv).mp hdiy
    exact Subgroup.mul_mem_sup
      (zpow_mem_zpowers_pow_of_dvd x hiq)
      (zpow_mem_zpowers_pow_of_dvd y hjq)
  · intro hz
    rw [Subgroup.mem_sup] at hz
    rcases hz with ⟨a, ha, b, hb, hab⟩
    subst z
    have hxqord : orderOf (x ^ (p ^ (u - 1))) = p := by
      rw [orderOf_prime_pow_pow hp hx (Nat.sub_le u 1)]
      rw [show u - (u - 1) = 1 by omega, pow_one]
    have hyqord : orderOf (y ^ (p ^ (v - 1))) = p := by
      rw [orderOf_prime_pow_pow hp hy (Nat.sub_le v 1)]
      rw [show v - (v - 1) = 1 by omega, pow_one]
    have hadvd : orderOf a ∣ p := by
      rw [← hxqord]
      exact orderOf_dvd_of_mem_zpowers ha
    have hbdvd : orderOf b ∣ p := by
      rw [← hyqord]
      exact orderOf_dvd_of_mem_zpowers hb
    have hap : a ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp hadvd
    have hbp : b ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp hbdvd
    change (a * b) ^ p = 1
    rw [mul_pow, hap, hbp, one_mul]

/- accepted add_to_file helper 11 -/
lemma Nat_card_pow_ker {G : Type*} [CommGroup G]
    {p u v : ℕ} (hp : p.Prime) (hu : 0 < u) (hv : 0 < v)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p ^ v)
    (hspan : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    Nat.card ↥((powMonoidHom p : G →* G).ker) = p ^ 2 := by
  rw [pow_ker_eq_zpowers_sup hp hu hv hx hy hspan hind]
  rw [Nat_card_sup_of_inf_bot (zpowers_pow_inf_zpowers_pow_eq_bot hind _ _)]
  rw [Nat.card_zpowers, Nat.card_zpowers]
  have hxqord : orderOf (x ^ (p ^ (u - 1))) = p := by
    rw [orderOf_prime_pow_pow hp hx (Nat.sub_le u 1)]
    rw [show u - (u - 1) = 1 by omega, pow_one]
  have hyqord : orderOf (y ^ (p ^ (v - 1))) = p := by
    rw [orderOf_prime_pow_pow hp hy (Nat.sub_le v 1)]
    rw [show v - (v - 1) = 1 by omega, pow_one]
  rw [hxqord, hyqord]
  exact (pow_two p).symm

/- accepted add_to_file helper 12 -/
lemma Nat_card_of_zpowers_sup_top_inf_bot {G : Type*} [CommGroup G] {x y : G}
    (hspan : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    Nat.card G = orderOf x * orderOf y := by
  have hcomp := comm_isComplement'_of_sup_top_inf_bot hspan hind
  calc
    Nat.card G = Nat.card ↥(Subgroup.zpowers x) * Nat.card ↥(Subgroup.zpowers y) :=
      hcomp.card_mul.symm
    _ = orderOf x * orderOf y := by rw [Nat.card_zpowers, Nat.card_zpowers]

/- accepted add_to_file helper 13 -/
lemma subgroup_index_prime_iff_card_prime_of_card_sq {G : Type*} [Group G]
    {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ 2) (U : Subgroup G) :
    U.index = p ↔ Nat.card U = p := by
  have h := U.card_mul_index
  rw [hG, pow_two] at h
  constructor
  · intro hindex
    rw [hindex, mul_comm] at h
    exact Nat.mul_left_cancel hp.pos h
  · intro hcard
    rw [hcard] at h
    exact Nat.mul_left_cancel hp.pos h

/- accepted add_to_file helper 14 -/
lemma pow_mem_subgroup_of_index_eq {G : Type*} [CommGroup G]
    (U : Subgroup G) {p : ℕ} (hindex : U.index = p) (g : G) :
    g ^ p ∈ U := by
  letI := Subgroup.normal_of_comm U
  let q := QuotientGroup.mk' U
  have hqpow : (q g) ^ p = 1 := by
    have h := pow_card_eq_one' (x := q g)
    rwa [← U.index_eq_card, hindex] at h
  have hker : g ^ p ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hqpow
  rwa [QuotientGroup.ker_mk'] at hker

/- accepted add_to_file helper 15 -/
lemma subgroup_index_prime_iff_card_eq_of_card_pow_succ {G : Type*} [Group G]
    {p u : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ (u + 1)) (U : Subgroup G) :
    U.index = p ↔ Nat.card ↥U = p ^ u := by
  have h := U.card_mul_index
  rw [hG, pow_succ] at h
  have hpu : 0 < p ^ u := pow_pos hp.pos u
  constructor
  · intro hindex
    rw [hindex] at h
    exact Nat.mul_right_cancel hp.pos h
  · intro hcard
    rw [hcard] at h
    exact Nat.mul_left_cancel hpu h

/- accepted add_to_file helper 16 -/
lemma zpowers_x_pow_pred_le_zpowers_x_pow {G : Type*} [Group G]
    {p u : ℕ} (hu : 1 < u) (x : G) :
    Subgroup.zpowers (x ^ (p ^ (u - 1))) ≤ Subgroup.zpowers (x ^ p) := by
  rw [Subgroup.zpowers_le]
  rw [show u - 1 = (u - 2) + 1 by omega, pow_succ, mul_comm, pow_mul]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers (x ^ p)) _

/- accepted add_to_file helper 17 -/
lemma N_index_mem_unique_v1 {G : Type*} [CommGroup G] [Finite G]
    {p u v : ℕ} (hp : p.Prime) (hu : 0 < u) (hv : 0 < v)
    (hu1 : 1 < u) (hv1 : v = 1)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p ^ v)
    (hspan : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    let E : Subgroup G := (powMonoidHom p : G →* G).ker
    let N : Subgroup G := Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y
    N.index = p ∧ E ≤ N ∧
      (∀ U : Subgroup G, U.index = p → E ≤ U → U = N) := by
  intro E N
  have hE : E = Subgroup.zpowers (x ^ (p ^ (u - 1))) ⊔
      Subgroup.zpowers (y ^ (p ^ (v - 1))) :=
    pow_ker_eq_zpowers_sup hp hu hv hx hy hspan hind
  have hPcard : Nat.card G = p ^ (u + 1) := by
    rw [Nat_card_of_zpowers_sup_top_inf_bot hspan hind, hx, hy, hv1, pow_one, ← pow_succ]
  have hNcard : Nat.card ↥N = p ^ u := by
    dsimp [N]
    have hNinf : Subgroup.zpowers (x ^ p) ⊓ Subgroup.zpowers y = ⊥ := by
      simpa using zpowers_pow_inf_zpowers_pow_eq_bot hind p 1
    rw [Nat_card_sup_of_inf_bot hNinf]
    rw [Nat.card_zpowers, Nat.card_zpowers]
    have hordxp : orderOf (x ^ p) = p ^ (u - 1) := by
      simpa using orderOf_prime_pow_pow hp hx (k := 1) (by omega : 1 ≤ u)
    rw [hordxp, hy, hv1, pow_one]
    rw [← pow_succ]
    congr 1
    omega
  have hNindex : N.index = p :=
    (subgroup_index_prime_iff_card_eq_of_card_pow_succ hp hPcard N).mpr hNcard
  refine ⟨hNindex, ?_, ?_⟩
  · rw [hE, hv1]
    simp only [Nat.reduceSub, pow_zero, pow_one]
    apply sup_le
    · exact le_trans (zpowers_x_pow_pred_le_zpowers_x_pow hu1 x) le_sup_left
    · exact (le_sup_right : Subgroup.zpowers y ≤
        Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y)
  · intro U hUindex hEU
    have hyE : y ∈ E := by
      rw [hE, hv1]
      simp only [Nat.reduceSub, pow_zero, pow_one]
      exact (le_sup_right : Subgroup.zpowers y ≤
        Subgroup.zpowers (x ^ (p ^ (u - 1))) ⊔ Subgroup.zpowers y) (Subgroup.mem_zpowers y)
    have hyU : y ∈ U := hEU hyE
    have hxpU : x ^ p ∈ U := pow_mem_subgroup_of_index_eq U hUindex x
    have hNU : N ≤ U := by
      dsimp [N]
      apply sup_le
      · rwa [Subgroup.zpowers_le]
      · rwa [Subgroup.zpowers_le]
    have hUcard : Nat.card ↥U = p ^ u :=
      (subgroup_index_prime_iff_card_eq_of_card_pow_succ hp hPcard U).mp hUindex
    apply Eq.symm
    apply Subgroup.eq_of_le_of_card_ge hNU
    rw [hUcard, hNcard]

/- accepted add_to_file helper 18 -/
lemma orderOf_mul_zpow_right_v1 {G : Type*} [CommGroup G] [Finite G]
    {p u : ℕ} (hp : p.Prime) (hu : 0 < u)
    {x y : G} (hx : orderOf x = p ^ u) (hy : orderOf y = p)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) (k : ℤ) :
    orderOf (x * y ^ k) = p ^ u := by
  let z := x * y ^ k
  have hpow_formula : ∀ n : ℕ, z ^ n = x ^ n * y ^ (k * n) := by
    intro n
    calc
      z ^ n = (x * y ^ k) ^ (n : ℤ) := by rw [zpow_natCast]
      _ = x ^ (n : ℤ) * (y ^ k) ^ (n : ℤ) := by rw [mul_zpow]
      _ = x ^ n * y ^ (k * n) := by rw [zpow_natCast, ← zpow_mul]
  have hxupper : x ^ p ^ u = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hyupper : y ^ (k * ((p ^ u : ℕ) : ℤ)) = 1 := by
    have hfac : k * (((p ^ u : ℕ) : ℤ)) = (p : ℤ) * (k * (((p ^ (u - 1) : ℕ) : ℤ))) := by
      have hpow : (((p ^ u : ℕ) : ℤ)) = (p : ℤ) * (((p ^ (u - 1) : ℕ) : ℤ)) := by
        calc
          (((p ^ u : ℕ) : ℤ)) = (((p ^ (u - 1 + 1) : ℕ) : ℤ)) := by rw [Nat.sub_add_cancel hu]
          _ = (p : ℤ) * (((p ^ (u - 1) : ℕ) : ℤ)) := by
            rw [pow_succ, Nat.cast_mul, mul_comm]
      rw [hpow]
      ring
    rw [hfac, zpow_mul]
    have hyp : y ^ (p : ℤ) = 1 := by
      rw [zpow_natCast, ← hy]
      exact pow_orderOf_eq_one y
    rw [hyp, one_zpow]
  have hupper : z ^ p ^ u = 1 := by
    rw [hpow_formula, hxupper, hyupper, one_mul]
  have hle : orderOf z ≤ p ^ u :=
    orderOf_le_of_pow_eq_one (pow_pos hp.pos u) hupper
  have hge : p ^ u ≤ orderOf z := by
    have hzd : z ^ orderOf z = 1 := pow_orderOf_eq_one z
    rw [hpow_formula] at hzd
    have hone := product_eq_one_of_inf_bot hind
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _)
      (Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) _) hzd
    have hdvd : orderOf x ∣ orderOf z := orderOf_dvd_iff_pow_eq_one.mpr hone.1
    rw [hx] at hdvd
    exact Nat.le_of_dvd (orderOf_pos z) hdvd
  exact le_antisymm hle hge

/- accepted add_to_file helper 19 -/
lemma mul_zpow_right_pow_pred_eq_left {G : Type*} [CommGroup G]
    {p u : ℕ} (hu : 1 < u) {x y : G} (hy : orderOf y = p) (k : ℤ) :
    (x * y ^ k) ^ (p ^ (u - 1)) = x ^ (p ^ (u - 1)) := by
  let z := x * y ^ k
  have hpow_formula : ∀ n : ℕ, z ^ n = x ^ n * y ^ (k * n) := by
    intro n
    calc
      z ^ n = (x * y ^ k) ^ (n : ℤ) := by rw [zpow_natCast]
      _ = x ^ (n : ℤ) * (y ^ k) ^ (n : ℤ) := by rw [mul_zpow]
      _ = x ^ n * y ^ (k * n) := by rw [zpow_natCast, ← zpow_mul]
  have hyq : y ^ (k * (((p ^ (u - 1) : ℕ) : ℤ))) = 1 := by
    have hfac : k * (((p ^ (u - 1) : ℕ) : ℤ)) =
        (p : ℤ) * (k * (((p ^ (u - 2) : ℕ) : ℤ))) := by
      have hpow : (((p ^ (u - 1) : ℕ) : ℤ)) =
          (p : ℤ) * (((p ^ (u - 2) : ℕ) : ℤ)) := by
        calc
          (((p ^ (u - 1) : ℕ) : ℤ)) = (((p ^ ((u - 2) + 1) : ℕ) : ℤ)) := by
            congr 2
            omega
          _ = (p : ℤ) * (((p ^ (u - 2) : ℕ) : ℤ)) := by
            rw [pow_succ, Nat.cast_mul, mul_comm]
      rw [hpow]
      ring
    rw [hfac, zpow_mul]
    have hyp : y ^ (p : ℤ) = 1 := by
      rw [zpow_natCast, ← hy]
      exact pow_orderOf_eq_one y
    rw [hyp, one_zpow]
  calc
    (x * y ^ k) ^ (p ^ (u - 1)) = z ^ (p ^ (u - 1)) := rfl
    _ = x ^ (p ^ (u - 1)) * y ^ (k * (((p ^ (u - 1) : ℕ) : ℤ))) := hpow_formula _
    _ = x ^ (p ^ (u - 1)) := by rw [hyq, mul_one]

/- accepted add_to_file helper 20 -/
lemma cyclic_nonN_v1 {G : Type*} [CommGroup G] [Finite G]
    {p u v : ℕ} (hp : p.Prime) (hu : 0 < u) (hv : 0 < v)
    (hu1 : 1 < u) (hv1 : v = 1)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p ^ v)
    (hspan : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥)
    {U : Subgroup G} (hU : U.index = p)
    (hUN : U ≠ Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y) :
    let E : Subgroup G := (powMonoidHom p : G →* G).ker
    IsCyclic U ∧ Nat.card ↥U = p ^ u ∧
      U ⊓ E = Subgroup.zpowers (x ^ (p ^ (u - 1))) := by
  intro E
  let N : Subgroup G := Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y
  have hN := N_index_mem_unique_v1 hp hu hv hu1 hv1 hx hy hspan hind
  change N.index = p ∧ E ≤ N ∧ (∀ V : Subgroup G, V.index = p → E ≤ V → V = N) at hN
  have hE : E = Subgroup.zpowers (x ^ (p ^ (u - 1))) ⊔
      Subgroup.zpowers (y ^ (p ^ (v - 1))) :=
    pow_ker_eq_zpowers_sup hp hu hv hx hy hspan hind
  have hPcard : Nat.card G = p ^ (u + 1) := by
    rw [Nat_card_of_zpowers_sup_top_inf_bot hspan hind, hx, hy, hv1, pow_one, ← pow_succ]
  have hUcard : Nat.card ↥U = p ^ u :=
    (subgroup_index_prime_iff_card_eq_of_card_pow_succ hp hPcard U).mp hU
  have hyU : y ∉ U := by
    intro h
    have hEU : E ≤ U := by
      rw [hE, hv1]
      simp only [Nat.reduceSub, pow_zero, pow_one]
      apply sup_le
      · have hxpU : x ^ p ∈ U := pow_mem_subgroup_of_index_eq U hU x
        exact le_trans (zpowers_x_pow_pred_le_zpowers_x_pow hu1 x)
          ((Subgroup.zpowers_le).mpr hxpU)
      · exact (Subgroup.zpowers_le).mpr h
    exact hUN (hN.2.2 U hU hEU)
  letI : Fact p.Prime := ⟨hp⟩
  letI := Subgroup.normal_of_comm U
  let q : G →* G ⧸ U := QuotientGroup.mk' U
  have hQcard : Nat.card (G ⧸ U) = p := by rw [← U.index_eq_card, hU]
  have hqy : q y ≠ 1 := by
    intro h
    have hyker : y ∈ q.ker := by rw [MonoidHom.mem_ker]; exact h
    rw [QuotientGroup.ker_mk'] at hyker
    exact hyU hyker
  have hqxmem : q x ∈ Subgroup.zpowers (q y) :=
    mem_zpowers_of_prime_card hQcard hqy
  rw [Subgroup.mem_zpowers_iff] at hqxmem
  rcases hqxmem with ⟨i, hiq⟩
  let k : ℤ := -i
  let z : G := x * y ^ k
  have hzq : q z = 1 := by
    change q (x * y ^ (-i)) = 1
    rw [map_mul, map_zpow, ← hiq]
    simp
  have hzU : z ∈ U := by
    have hzker : z ∈ q.ker := by rw [MonoidHom.mem_ker]; exact hzq
    rw [QuotientGroup.ker_mk'] at hzker
    exact hzker
  have hy' : orderOf y = p := by simpa [hv1] using hy
  have hzorder : orderOf z = p ^ u :=
    orderOf_mul_zpow_right_v1 hp hu hx hy' hind k
  have hHzU : Subgroup.zpowers z ≤ U := (Subgroup.zpowers_le).mpr hzU
  have hUeq : U = Subgroup.zpowers z := by
    apply Eq.symm
    apply Subgroup.eq_of_le_of_card_ge hHzU
    rw [hUcard, Nat.card_zpowers, hzorder]
  have hA : Subgroup.zpowers (x ^ (p ^ (u - 1))) ≤ U ⊓ E := by
    apply le_inf
    · rw [hUeq, Subgroup.zpowers_le]
      rw [← mul_zpow_right_pow_pred_eq_left hu1 hy' k]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers z) _
    · rw [hE, hv1]
      simp only [Nat.reduceSub, pow_zero, pow_one]
      exact le_sup_left
  have hinter : U ⊓ E = Subgroup.zpowers (x ^ (p ^ (u - 1))) := by
    apply le_antisymm
    · intro w hw
      have hwU : w ∈ U := hw.1
      have hwE : w ∈ E := hw.2
      rw [hUeq, Subgroup.mem_zpowers_iff] at hwU
      rcases hwU with ⟨t, hwt⟩
      have hwpow : w ^ p = 1 := by simpa [E, powMonoidHom] using hwE
      have hzpowtp : z ^ (t * p) = 1 := by
        calc
          z ^ (t * p) = (z ^ t) ^ (p : ℤ) := by rw [← zpow_mul]
          _ = (z ^ t) ^ p := by rw [zpow_natCast]
          _ = 1 := by rw [hwt]; exact hwpow
      have hdvd : (orderOf z : ℤ) ∣ t * p := orderOf_dvd_iff_zpow_eq_one.mpr hzpowtp
      rw [hzorder] at hdvd
      have hqdt : (((p ^ (u - 1) : ℕ) : ℤ)) ∣ t :=
        (int_prime_pow_mul_dvd_mul_iff hp hu).mp hdvd
      rcases hqdt with ⟨s, rfl⟩
      have hzqpow : z ^ (((p ^ (u - 1) : ℕ) : ℤ)) = x ^ (p ^ (u - 1)) := by
        rw [zpow_natCast]
        exact mul_zpow_right_pow_pred_eq_left hu1 hy' k
      have hweq : w = (x ^ (p ^ (u - 1))) ^ s := by
        calc
          w = z ^ ((((p ^ (u - 1) : ℕ) : ℤ)) * s) := hwt.symm
          _ = (z ^ (((p ^ (u - 1) : ℕ) : ℤ))) ^ s := by rw [zpow_mul]
          _ = (x ^ (p ^ (u - 1))) ^ s := by rw [hzqpow]
      rw [hweq]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers (x ^ (p ^ (u - 1)))) s
    · exact hA
  refine ⟨?_, hUcard, hinter⟩
  rw [hUeq]
  exact Subgroup.isCyclic_zpowers z

/- accepted add_to_file helper 21 -/
lemma H_fin_injective_v1 {G : Type*} [CommGroup G]
    {p u : ℕ} (hp : p.Prime) (hu : 0 < u)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    Function.Injective (fun r : Fin p =>
      Subgroup.zpowers (x * y ^ (r.val : ℕ))) := by
  intro r s hrs
  change Subgroup.zpowers (x * y ^ (r.val : ℕ)) =
    Subgroup.zpowers (x * y ^ (s.val : ℕ)) at hrs
  have hrs_mem : x * y ^ (s.val : ℕ) ∈
      Subgroup.zpowers (x * y ^ (r.val : ℕ)) := by
    rw [hrs]
    exact Subgroup.mem_zpowers _
  rw [Subgroup.mem_zpowers_iff] at hrs_mem
  rcases hrs_mem with ⟨t, ht⟩
  have hformula : ((x * y ^ (r.val : ℕ)) ^ t) =
      x ^ t * y ^ (((r.val : ℤ)) * t) := by
    calc
      ((x * y ^ (r.val : ℕ)) ^ t) = x ^ t * (y ^ (r.val : ℕ)) ^ t := by rw [mul_zpow]
      _ = x ^ t * (y ^ ((r.val : ℤ))) ^ t := by rw [zpow_natCast]
      _ = x ^ t * y ^ (((r.val : ℤ)) * t) := by rw [← zpow_mul]
  rw [hformula] at ht
  let X : Subgroup G := Subgroup.zpowers x
  let Y : Subgroup G := Subgroup.zpowers y
  have hpair :
      (⟨⟨x ^ t, Subgroup.zpow_mem X (Subgroup.mem_zpowers x) t⟩,
        ⟨y ^ (((r.val : ℤ)) * t), Subgroup.zpow_mem Y (Subgroup.mem_zpowers y) _⟩⟩ : X × Y) =
      ⟨⟨x, Subgroup.mem_zpowers x⟩,
        ⟨y ^ (s.val : ℕ), Subgroup.pow_mem Y (Subgroup.mem_zpowers y) _⟩⟩ := by
    apply commSubgroupProdHom_injective hind
    simpa [commSubgroupProdHom] using ht
  have hxt : x ^ t = x := congrArg (fun a : X × Y => (a.1 : G)) hpair
  have hyt : y ^ (((r.val : ℤ)) * t) = y ^ (s.val : ℕ) :=
    congrArg (fun a : X × Y => (a.2 : G)) hpair
  have hxone : x ^ (1 - t) = 1 := by
    calc
      x ^ (1 - t) = x * (x ^ t)⁻¹ := by group
      _ = x * x⁻¹ := by rw [hxt]
      _ = 1 := by simp
  have hyone : y ^ (((s.val : ℤ)) - ((r.val : ℤ)) * t) = 1 := by
    calc
      y ^ (((s.val : ℤ)) - ((r.val : ℤ)) * t)
          = y ^ (s.val : ℕ) * (y ^ (((r.val : ℤ)) * t))⁻¹ := by group
      _ = y ^ (s.val : ℕ) * (y ^ (s.val : ℕ))⁻¹ := by rw [hyt]
      _ = 1 := by simp
  have hdvdx : (orderOf x : ℤ) ∣ 1 - t := orderOf_dvd_iff_zpow_eq_one.mpr hxone
  have hdvdy : (orderOf y : ℤ) ∣ (((s.val : ℤ)) - ((r.val : ℤ)) * t) :=
    orderOf_dvd_iff_zpow_eq_one.mpr hyone
  rw [hx] at hdvdx
  rw [hy] at hdvdy
  have hp_dvd_orderx : (p : ℤ) ∣ ((p ^ u : ℕ) : ℤ) := by
    have hd : p ^ 1 ∣ p ^ u := pow_dvd_pow p (by omega : 1 ≤ u)
    have hdZ : (((p ^ 1 : ℕ) : ℤ)) ∣ (((p ^ u : ℕ) : ℤ)) := by exact_mod_cast hd
    simpa using hdZ
  have hpt : (p : ℤ) ∣ 1 - t := dvd_trans hp_dvd_orderx hdvdx
  rcases hpt with ⟨a, ha⟩
  rcases hdvdy with ⟨b, hb⟩
  have hpsr : (p : ℤ) ∣ (((s.val : ℤ)) - (r.val : ℤ)) := by
    refine ⟨b - (r.val : ℤ) * a, ?_⟩
    have hrewrite : (((s.val : ℤ)) - (r.val : ℤ)) =
        ((((s.val : ℤ)) - ((r.val : ℤ)) * t) - ((r.val : ℤ)) * (1 - t)) := by ring
    rw [hrewrite, hb, ha]
    ring
  have hzmod : (((s.val : ℤ) - (r.val : ℤ) : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (((s.val : ℤ) - (r.val : ℤ))) p).mpr hpsr
  have hzmods : (((s.val : ℤ)) : ZMod p) = (((r.val : ℤ)) : ZMod p) := by
    apply sub_eq_zero.mp
    simpa using hzmod
  have hzmodnat : ((s.val : ZMod p) = (r.val : ZMod p)) := by exact_mod_cast hzmods
  have hnatmod : s.val ≡ r.val [MOD p] :=
    (ZMod.natCast_eq_natCast_iff s.val r.val p).mp hzmodnat
  have hval : s.val = r.val :=
    Nat.ModEq.eq_of_lt_of_lt hnatmod s.isLt r.isLt
  exact Fin.ext hval.symm

/- accepted add_to_file helper 22 -/
lemma H_fin_ne_N_v1 {G : Type*} [CommGroup G]
    {p u : ℕ} (hp : p.Prime) (hu : 0 < u)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) (r : Fin p) :
    Subgroup.zpowers (x * y ^ (r.val : ℕ)) ≠
      Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y := by
  intro hHN
  have hyN : y ∈ Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y :=
    (le_sup_right : Subgroup.zpowers y ≤
      Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y) (Subgroup.mem_zpowers y)
  rw [← hHN] at hyN
  rw [Subgroup.mem_zpowers_iff] at hyN
  rcases hyN with ⟨t, ht⟩
  have hformula : ((x * y ^ (r.val : ℕ)) ^ t) =
      x ^ t * y ^ (((r.val : ℤ)) * t) := by
    calc
      ((x * y ^ (r.val : ℕ)) ^ t) = x ^ t * (y ^ (r.val : ℕ)) ^ t := by rw [mul_zpow]
      _ = x ^ t * (y ^ ((r.val : ℤ))) ^ t := by rw [zpow_natCast]
      _ = x ^ t * y ^ (((r.val : ℤ)) * t) := by rw [← zpow_mul]
  rw [hformula] at ht
  let X : Subgroup G := Subgroup.zpowers x
  let Y : Subgroup G := Subgroup.zpowers y
  have hpair :
      (⟨⟨x ^ t, Subgroup.zpow_mem X (Subgroup.mem_zpowers x) t⟩,
        ⟨y ^ (((r.val : ℤ)) * t), Subgroup.zpow_mem Y (Subgroup.mem_zpowers y) _⟩⟩ : X × Y) =
      ⟨⟨1, X.one_mem⟩, ⟨y, Subgroup.mem_zpowers y⟩⟩ := by
    apply commSubgroupProdHom_injective hind
    simpa [commSubgroupProdHom] using ht
  have hxt : x ^ t = 1 := congrArg (fun a : X × Y => (a.1 : G)) hpair
  have hyt : y ^ (((r.val : ℤ)) * t) = y := congrArg (fun a : X × Y => (a.2 : G)) hpair
  have hyone : y ^ (((r.val : ℤ)) * t - 1) = 1 := by
    calc
      y ^ (((r.val : ℤ)) * t - 1) = y ^ (((r.val : ℤ)) * t) * y⁻¹ := by group
      _ = y * y⁻¹ := by rw [hyt]
      _ = 1 := by simp
  have hdvdx : (orderOf x : ℤ) ∣ t := orderOf_dvd_iff_zpow_eq_one.mpr hxt
  have hdvdy : (orderOf y : ℤ) ∣ (((r.val : ℤ)) * t - 1) :=
    orderOf_dvd_iff_zpow_eq_one.mpr hyone
  rw [hx] at hdvdx
  rw [hy] at hdvdy
  have hp_dvd_orderx : (p : ℤ) ∣ ((p ^ u : ℕ) : ℤ) := by
    have hd : p ^ 1 ∣ p ^ u := pow_dvd_pow p (by omega : 1 ≤ u)
    have hdZ : (((p ^ 1 : ℕ) : ℤ)) ∣ (((p ^ u : ℕ) : ℤ)) := by exact_mod_cast hd
    simpa using hdZ
  have hpt : (p : ℤ) ∣ t := dvd_trans hp_dvd_orderx hdvdx
  have hprt : (p : ℤ) ∣ ((r.val : ℤ)) * t := dvd_mul_of_dvd_right hpt _
  rcases hprt with ⟨b, hb⟩
  rcases hdvdy with ⟨a, ha⟩
  have hdiv1 : (p : ℤ) ∣ 1 := by
    refine ⟨b - a, ?_⟩
    have hsub : (p : ℤ) * b - (p : ℤ) * a = 1 := by
      rw [← hb, ← ha]
      ring
    calc
      1 = (p : ℤ) * b - (p : ℤ) * a := hsub.symm
      _ = (p : ℤ) * (b - a) := by ring
  have hdiv1nat : p ∣ 1 := by exact_mod_cast hdiv1
  exact hp.not_dvd_one hdiv1nat

/- accepted add_to_file helper 23 -/
lemma nonN_eq_H_fin_v1 {G : Type*} [CommGroup G] [Finite G]
    {p u v : ℕ} (hp : p.Prime) (hu : 0 < u) (hv : 0 < v)
    (hu1 : 1 < u) (hv1 : v = 1)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p ^ v)
    (hspan : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥)
    {U : Subgroup G} (hU : U.index = p)
    (hUN : U ≠ Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y) :
    ∃ r : Fin p, U = Subgroup.zpowers (x * y ^ (r.val : ℕ)) := by
  let E : Subgroup G := (powMonoidHom p : G →* G).ker
  let N : Subgroup G := Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y
  have hN := N_index_mem_unique_v1 hp hu hv hu1 hv1 hx hy hspan hind
  change N.index = p ∧ E ≤ N ∧ (∀ V : Subgroup G, V.index = p → E ≤ V → V = N) at hN
  have hE : E = Subgroup.zpowers (x ^ (p ^ (u - 1))) ⊔
      Subgroup.zpowers (y ^ (p ^ (v - 1))) :=
    pow_ker_eq_zpowers_sup hp hu hv hx hy hspan hind
  have hyU : y ∉ U := by
    intro h
    have hEU : E ≤ U := by
      rw [hE, hv1]
      simp only [Nat.reduceSub, pow_zero, pow_one]
      apply sup_le
      · have hxpU : x ^ p ∈ U := pow_mem_subgroup_of_index_eq U hU x
        exact le_trans (zpowers_x_pow_pred_le_zpowers_x_pow hu1 x)
          ((Subgroup.zpowers_le).mpr hxpU)
      · exact (Subgroup.zpowers_le).mpr h
    exact hUN (hN.2.2 U hU hEU)
  letI : Fact p.Prime := ⟨hp⟩
  letI := Subgroup.normal_of_comm U
  let q : G →* G ⧸ U := QuotientGroup.mk' U
  have hQcard : Nat.card (G ⧸ U) = p := by rw [← U.index_eq_card, hU]
  have hqy : q y ≠ 1 := by
    intro h
    have hyker : y ∈ q.ker := by rw [MonoidHom.mem_ker]; exact h
    rw [QuotientGroup.ker_mk'] at hyker
    exact hyU hyker
  have hqxmem : q x ∈ Subgroup.zpowers (q y) :=
    mem_zpowers_of_prime_card hQcard hqy
  rw [Subgroup.mem_zpowers_iff] at hqxmem
  rcases hqxmem with ⟨i, hiq⟩
  let k : ℤ := -i
  let z : G := x * y ^ k
  have hzq : q z = 1 := by
    change q (x * y ^ (-i)) = 1
    rw [map_mul, map_zpow, ← hiq]
    simp
  have hzU : z ∈ U := by
    have hzker : z ∈ q.ker := by rw [MonoidHom.mem_ker]; exact hzq
    rw [QuotientGroup.ker_mk'] at hzker
    exact hzker
  have hPcard : Nat.card G = p ^ (u + 1) := by
    rw [Nat_card_of_zpowers_sup_top_inf_bot hspan hind, hx, hy, hv1, pow_one, ← pow_succ]
  have hUcard : Nat.card ↥U = p ^ u :=
    (subgroup_index_prime_iff_card_eq_of_card_pow_succ hp hPcard U).mp hU
  have hy' : orderOf y = p := by simpa [hv1] using hy
  have hzorder : orderOf z = p ^ u :=
    orderOf_mul_zpow_right_v1 hp hu hx hy' hind k
  have hHzU : Subgroup.zpowers z ≤ U := (Subgroup.zpowers_le).mpr hzU
  have hUeqz : U = Subgroup.zpowers z := by
    apply Eq.symm
    apply Subgroup.eq_of_le_of_card_ge hHzU
    rw [hUcard, Nat.card_zpowers, hzorder]
  have hknonneg : 0 ≤ k % (p : ℤ) :=
    Int.emod_nonneg k (by exact_mod_cast hp.ne_zero)
  have hklt : k % (p : ℤ) < (p : ℤ) :=
    Int.emod_lt_of_pos k (by exact_mod_cast hp.pos)
  let r : Fin p := ⟨(k % (p : ℤ)).toNat, by
    exact (Int.toNat_lt hknonneg).mpr hklt⟩
  have hmod : y ^ (k % ↑(orderOf y)) = y ^ k := zpow_mod_orderOf y k
  rw [hy'] at hmod
  have hrcast : ((r.val : ℤ)) = k % (p : ℤ) := Int.toNat_of_nonneg hknonneg
  have hykr : y ^ k = y ^ (r.val : ℕ) := by
    calc
      y ^ k = y ^ (k % (p : ℤ)) := hmod.symm
      _ = y ^ ((r.val : ℤ)) := by rw [← hrcast]
      _ = y ^ (r.val : ℕ) := by rw [zpow_natCast]
  have hzr : z = x * y ^ (r.val : ℕ) := by
    dsimp [z]
    rw [hykr]
  exact ⟨r, by rw [hUeqz, hzr]⟩

/- accepted add_to_file helper 24 -/
lemma card_nonN_index_prime_v1 {G : Type*} [CommGroup G] [Finite G]
    {p u v : ℕ} (hp : p.Prime) (hu : 0 < u) (hv : 0 < v)
    (hu1 : 1 < u) (hv1 : v = 1)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p ^ v)
    (hspan : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    Nat.card {U : Subgroup G // U.index = p ∧
      U ≠ Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y} = p := by
  let N : Subgroup G := Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y
  let H : Fin p → Subgroup G := fun r =>
    Subgroup.zpowers (x * y ^ (r.val : ℕ))
  have hPcard : Nat.card G = p ^ (u + 1) := by
    rw [Nat_card_of_zpowers_sup_top_inf_bot hspan hind, hx, hy, hv1, pow_one, ← pow_succ]
  have hy' : orderOf y = p := by simpa [hv1] using hy
  have hHindex : ∀ r : Fin p, (H r).index = p := by
    intro r
    have hzorder : orderOf (x * y ^ (r.val : ℕ)) = p ^ u := by
      simpa [zpow_natCast] using
        (orderOf_mul_zpow_right_v1 hp hu hx hy' hind (((r.val : ℤ))))
    have hHcard : Nat.card ↥(H r) = p ^ u := by
      dsimp [H]
      rw [Nat.card_zpowers, hzorder]
    exact (subgroup_index_prime_iff_card_eq_of_card_pow_succ hp hPcard (H r)).mpr hHcard
  have hHne : ∀ r : Fin p, H r ≠ N := by
    intro r
    exact H_fin_ne_N_v1 hp hu hx hy' hind r
  let S := {U : Subgroup G // U.index = p ∧ U ≠ N}
  let f : Fin p → S := fun r => ⟨H r, hHindex r, hHne r⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply H_fin_injective_v1 hp hu hx hy' hind
    exact congrArg Subtype.val hab
  have hsurj : Function.Surjective f := by
    intro UU
    rcases nonN_eq_H_fin_v1 hp hu hv hu1 hv1 hx hy hspan hind UU.2.1 UU.2.2 with ⟨r, hr⟩
    exact ⟨r, Subtype.ext hr.symm⟩
  let e : Fin p ≃ S := Equiv.ofBijective f ⟨hinj, hsurj⟩
  calc
    Nat.card S = Nat.card (Fin p) := (Nat.card_congr e).symm
    _ = p := Nat.card_fin p

/- accepted add_to_file helper 25 -/
lemma pow_pred_mem_subgroup_of_index_eq {G : Type*} [CommGroup G]
    (U : Subgroup G) {p n : ℕ} (hn : 1 < n) (hindex : U.index = p) (x : G) :
    x ^ (p ^ (n - 1)) ∈ U := by
  have h := pow_mem_subgroup_of_index_eq U hindex (x ^ (p ^ (n - 2)))
  convert h using 1
  rw [← pow_mul]
  congr 1
  rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]

/- accepted add_to_file helper 26 -/
lemma N_mulEquiv_v1 {G : Type*} [CommGroup G]
    {p u : ℕ} (hp : p.Prime) (hu : 0 < u)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    let N : Subgroup G := Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y
    Nonempty (N ≃* Multiplicative (ZMod (p ^ (u - 1))) × Multiplicative (ZMod p)) := by
  intro N
  let X : Subgroup G := Subgroup.zpowers (x ^ p)
  let Y : Subgroup G := Subgroup.zpowers y
  have hinf : X ⊓ Y = ⊥ := by
    dsimp [X, Y]
    simpa using zpowers_pow_inf_zpowers_pow_eq_bot hind p 1
  let f := commSubgroupProdHom X Y
  have hrange : f.range = N := by
    dsimp [f, N, X, Y]
    exact commSubgroupProdHom_range (Subgroup.zpowers (x ^ p)) (Subgroup.zpowers y)
  have hinj : Function.Injective f.rangeRestrict := by
    rw [MonoidHom.rangeRestrict_injective_iff]
    dsimp [f]
    exact commSubgroupProdHom_injective hinf
  have hbij : Function.Bijective f.rangeRestrict :=
    ⟨hinj, MonoidHom.rangeRestrict_surjective f⟩
  let eprod : (↥X × ↥Y) ≃* N := by
    let e : (↥X × ↥Y) ≃* f.range := MulEquiv.ofBijective f.rangeRestrict hbij
    rwa [hrange] at e
  have hXcard : Nat.card ↥X = p ^ (u - 1) := by
    dsimp [X]
    rw [Nat.card_zpowers]
    simpa using orderOf_prime_pow_pow hp hx (k := 1) (by omega : 1 ≤ u)
  have hYcard : Nat.card ↥Y = p := by
    dsimp [Y]
    rw [Nat.card_zpowers, hy]
  rcases IsCyclic.exists_generator (α := X) with ⟨gx, hgx⟩
  rcases IsCyclic.exists_generator (α := Y) with ⟨gy, hgy⟩
  let eX : Multiplicative (ZMod (p ^ (u - 1))) ≃* X :=
    zmodMulEquivOfGenerator hgx hXcard
  let eY : Multiplicative (ZMod p) ≃* Y := zmodMulEquivOfGenerator hgy hYcard
  exact ⟨eprod.symm.trans (MulEquiv.prodCongr eX.symm eY.symm)⟩

/- verified submission -/
theorem sylow_rank_two_index_prime_subgroups
    {A : Type*} [CommGroup A] [Finite A]
    {p u v : ℕ} (hp : p.Prime) (hu : 0 < u) (hv : 0 < v) (huv : v ≤ u)
    (P : Sylow p A) (x y : P)
    (hx : orderOf x = p ^ u) (hy : orderOf y = p ^ v)
    (hspan : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    let E : Subgroup P := (powMonoidHom p : P →* P).ker
    let N : Subgroup P := Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y
    E = Subgroup.zpowers (x ^ (p ^ (u - 1))) ⊔
          Subgroup.zpowers (y ^ (p ^ (v - 1))) ∧
    (u = 1 ∧ v = 1 →
      ∀ U : Subgroup P, U.index = p ↔ U ≤ E ∧ Nat.card U = p) ∧
    (v = 1 ∧ 1 < u →
      N.index = p ∧ E ≤ N ∧
      (∀ U : Subgroup P, U.index = p → E ≤ U → U = N) ∧
      Nonempty (N ≃* Multiplicative (ZMod (p ^ (u - 1))) × Multiplicative (ZMod p)) ∧
      Nat.card {U : Subgroup P // U.index = p ∧ U ≠ N} = p ∧
      (∀ U : Subgroup P, U.index = p → U ≠ N →
        IsCyclic U ∧ Nat.card U = p ^ u ∧
          U ⊓ E = Subgroup.zpowers (x ^ (p ^ (u - 1))))) ∧
    (1 < v → ∀ U : Subgroup P, U.index = p → E ≤ U) := by
  intro E N
  have hE : E = Subgroup.zpowers (x ^ (p ^ (u - 1))) ⊔
      Subgroup.zpowers (y ^ (p ^ (v - 1))) :=
    pow_ker_eq_zpowers_sup hp hu hv hx hy hspan hind
  refine ⟨hE, ?_, ?_, ?_⟩
  · rintro ⟨hu1, hv1⟩
    have hPcard : Nat.card P = p ^ 2 := by
      calc
        Nat.card P = orderOf x * orderOf y :=
          Nat_card_of_zpowers_sup_top_inf_bot hspan hind
        _ = p ^ 2 := by rw [hx, hy, hu1, hv1]; simpa using (pow_two p).symm
    have hEcard : Nat.card ↥E = p ^ 2 :=
      Nat_card_pow_ker hp hu hv hx hy hspan hind
    have hEtop : E = ⊤ := Subgroup.eq_top_of_card_eq E (by rw [hEcard, hPcard])
    intro U
    rw [hEtop]
    constructor
    · intro hU
      exact ⟨le_top, (subgroup_index_prime_iff_card_prime_of_card_sq hp hPcard U).mp hU⟩
    · intro hU
      exact (subgroup_index_prime_iff_card_prime_of_card_sq hp hPcard U).mpr hU.2
  · rintro ⟨hv1, hu1⟩
    have hNstruct := N_index_mem_unique_v1 hp hu hv hu1 hv1 hx hy hspan hind
    change N.index = p ∧ E ≤ N ∧
      (∀ U : Subgroup P, U.index = p → E ≤ U → U = N) at hNstruct
    have hy' : orderOf y = p := by simpa [hv1] using hy
    have hNiso : Nonempty (N ≃* Multiplicative (ZMod (p ^ (u - 1))) ×
        Multiplicative (ZMod p)) := by
      exact N_mulEquiv_v1 hp hu hx hy' hind
    have hcount : Nat.card {U : Subgroup P // U.index = p ∧ U ≠ N} = p := by
      exact card_nonN_index_prime_v1 hp hu hv hu1 hv1 hx hy hspan hind
    refine ⟨hNstruct.1, hNstruct.2.1, hNstruct.2.2, hNiso, hcount, ?_⟩
    intro U hU hUN
    exact cyclic_nonN_v1 hp hu hv hu1 hv1 hx hy hspan hind hU hUN
  · intro hv1
    intro U hU
    rw [hE]
    apply sup_le
    · rw [Subgroup.zpowers_le]
      exact pow_pred_mem_subgroup_of_index_eq U (by omega : 1 < u) hU x
    · rw [Subgroup.zpowers_le]
      exact pow_pred_mem_subgroup_of_index_eq U hv1 hU y

end Rollout_p2247_sylow_rank_two_index_prime_subgroups

namespace Rollout_p2227_strongmetricenvelopeofheight

/- accepted add_to_file helper 1 -/
lemma finprod_sum_elim {ι κ M : Type*} [CommMonoid M]
    (f : ι → M) (g : κ → M)
    (hf : Function.HasFiniteMulSupport f)
    (hg : Function.HasFiniteMulSupport g) :
    (∏ᶠ x : ι ⊕ κ, Sum.elim f g x) =
      (∏ᶠ i, f i) * ∏ᶠ j, g j := by
  classical
  let s := hf.toFinset
  let t := hg.toFinset
  have hsub : Function.mulSupport (Sum.elim f g) ⊆ ↑(s.disjSum t) := by
    intro x hx
    cases x with
    | inl i =>
        have hi : i ∈ s := by
          have hi' : i ∈ hf.toFinset := (hf.mem_toFinset).2 hx
          simpa [s] using hi'
        simp [Finset.mem_disjSum, hi]
    | inr j =>
        have hj : j ∈ t := by
          have hj' : j ∈ hg.toFinset := (hg.mem_toFinset).2 hx
          simpa [t] using hj'
        simp [Finset.mem_disjSum, hj]
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  rw [Finset.prod_sumElim]
  rw [finprod_eq_prod_of_mulSupport_subset f (s:=s) (by
    intro i hi
    have hi' : i ∈ hf.toFinset := by simpa [s] using hi
    simpa [s] using (hf.mem_toFinset).1 hi'),
    finprod_eq_prod_of_mulSupport_subset g (s:=t) (by
    intro j hj
    have hj' : j ∈ hg.toFinset := by simpa [t] using hj
    simpa [t] using (hg.mem_toFinset).1 hj')]

noncomputable def pnatInterleaveEquiv : ℕ+ ≃ ℕ+ ⊕ ℕ+ :=
  Equiv.pnatEquivNat.trans
    (Equiv.natSumNatEquivNat.symm.trans
      ((Equiv.pnatEquivNat.symm).sumCongr Equiv.pnatEquivNat.symm))

lemma hasFiniteMulSupport_interleave {M : Type*} [One M]
    {a b : ℕ+ → M}
    (ha : Function.HasFiniteMulSupport a)
    (hb : Function.HasFiniteMulSupport b) :
    Function.HasFiniteMulSupport
      (fun n : ℕ+ ↦ Sum.elim a b (pnatInterleaveEquiv n)) := by
  classical
  have hsum : Function.HasFiniteMulSupport (Sum.elim a b) := by
    apply (Set.Finite.union
      (Set.Finite.image (α:=ℕ+) (s:=Function.mulSupport a) Sum.inl ha)
      (Set.Finite.image (α:=ℕ+) (s:=Function.mulSupport b) Sum.inr hb)).subset
    intro x hx
    cases x with
    | inl i =>
        exact Set.mem_union_left _ ⟨i, (Function.mem_mulSupport).1 hx, rfl⟩
    | inr j =>
        exact Set.mem_union_right _ ⟨j, (Function.mem_mulSupport).1 hx, rfl⟩
  simpa [Function.comp_def] using hsum.fun_comp_of_injective pnatInterleaveEquiv.injective

lemma finprod_interleave {M : Type*} [CommMonoid M]
    {a b : ℕ+ → M}
    (ha : Function.HasFiniteMulSupport a)
    (hb : Function.HasFiniteMulSupport b) :
    (∏ᶠ n : ℕ+, Sum.elim a b (pnatInterleaveEquiv n)) =
      (∏ᶠ n, a n) * ∏ᶠ n, b n := by
  exact (finprod_comp (g := Sum.elim a b) pnatInterleaveEquiv
    pnatInterleaveEquiv.bijective).trans (finprod_sum_elim a b ha hb)

lemma finite_range_apply_of_hasFiniteMulSupport {M : Type*} [One M]
    {a : ℕ+ → M} (ha : Function.HasFiniteMulSupport a) (f : M → ℝ) :
    Set.Finite (Set.range fun n : ℕ+ ↦ f (a n)) := by
  classical
  apply (Set.Finite.union
    (Set.Finite.image (α:=ℕ+) (β:=ℝ) (s:=Function.mulSupport a)
      (fun n : ℕ+ ↦ f (a n)) ha)
    (Set.finite_singleton (f 1))).subset
  rintro y ⟨n, rfl⟩
  by_cases hn : a n = 1
  · exact Set.mem_union_right _ (by simpa [hn])
  · exact Set.mem_union_left _
      (Set.mem_image_of_mem (fun m : ℕ+ ↦ f (a m)) ((Function.mem_mulSupport).2 hn))

lemma bddAbove_range_apply_of_hasFiniteMulSupport {M : Type*} [One M]
    {a : ℕ+ → M} (ha : Function.HasFiniteMulSupport a) (f : M → ℝ) :
    BddAbove (Set.range fun n : ℕ+ ↦ f (a n)) :=
  (finite_range_apply_of_hasFiniteMulSupport ha f).bddAbove

/- accepted add_to_file helper 2 -/
lemma sSup_range_interleave {G : Type*} [One G]
    {a b : ℕ+ → G}
    (ha : Function.HasFiniteMulSupport a)
    (hb : Function.HasFiniteMulSupport b)
    (f : G → ℝ) :
    sSup (Set.range fun n : ℕ+ ↦
        f (Sum.elim a b (pnatInterleaveEquiv n))) =
      max (sSup (Set.range fun n : ℕ+ ↦ f (a n)))
        (sSup (Set.range fun n : ℕ+ ↦ f (b n))) := by
  classical
  let e := pnatInterleaveEquiv
  have hrange :
      Set.range (fun n : ℕ+ ↦ f (Sum.elim a b (e n))) =
        Set.range (fun n : ℕ+ ↦ f (a n)) ∪
          Set.range (fun n : ℕ+ ↦ f (b n)) := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      cases he : e n with
      | inl i =>
          exact Or.inl ⟨i, by simpa [he]⟩
      | inr j =>
          exact Or.inr ⟨j, by simpa [he]⟩
    · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩)
      · obtain ⟨n, hn⟩ := e.surjective (Sum.inl i)
        exact ⟨n, by simp [hn]⟩
      · obtain ⟨n, hn⟩ := e.surjective (Sum.inr j)
        exact ⟨n, by simp [hn]⟩
  rw [hrange]
  rw [csSup_union
    (bddAbove_range_apply_of_hasFiniteMulSupport ha f)
    (Set.range_nonempty _)
    (bddAbove_range_apply_of_hasFiniteMulSupport hb f)
    (Set.range_nonempty _)]

/- accepted add_to_file helper 3 -/
def pnatSingle {M : Type*} [One M] (x : M) : ℕ+ → M :=
  fun n ↦ if n = 1 then x else 1

lemma hasFiniteMulSupport_pnatSingle {M : Type*} [One M] (x : M) :
    Function.HasFiniteMulSupport (pnatSingle x) := by
  classical
  apply (Set.finite_singleton (1 : ℕ+)).subset
  intro n hn
  by_cases h : n = 1
  · simpa [h]
  · exfalso
    exact hn (by simp [pnatSingle, h])

lemma finprod_pnatSingle {M : Type*} [CommMonoid M] (x : M) :
    (∏ᶠ n : ℕ+, pnatSingle x n) = x := by
  classical
  have hsub : Function.mulSupport (pnatSingle x) ⊆ ↑({1} : Finset ℕ+) := by
    intro n hn
    by_cases h : n = 1
    · simpa [h]
    · exfalso
      exact hn (by simp [pnatSingle, h])
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  simp [pnatSingle]

lemma sSup_range_apply_pnatSingle {G : Type*} [One G]
    (f : G → ℝ) (x : G)
    (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) :
    sSup (Set.range fun n : ℕ+ ↦ f (pnatSingle x n)) = f x := by
  classical
  have hrange : Set.range (fun n : ℕ+ ↦ f (pnatSingle x n)) = {f x, f 1} := by
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      by_cases h : n = 1
      · simp [pnatSingle, h]
      · simp [pnatSingle, h]
    · rintro (rfl | rfl)
      · exact ⟨1, by simp [pnatSingle]⟩
      · exact ⟨2, by simp [pnatSingle]⟩
  rw [hrange, csSup_pair]
  have h : f 1 ≤ f x := by simpa [hf_one] using hf_lower x
  exact max_eq_left h

/- accepted add_to_file helper 4 -/
noncomputable abbrev heightEnvOne {G : Type*} [CommMonoid G] (f : G → ℝ) (α : G) : ℝ :=
  sInf {r : ℝ | ∃ a : ℕ+ → G,
    Function.HasFiniteMulSupport a ∧
    (∏ᶠ n, a n) = α ∧
    (∏ᶠ n, f (a n)) = r}

noncomputable abbrev heightEnvInf {G : Type*} [CommMonoid G] (f : G → ℝ) (α : G) : ℝ :=
  sInf {r : ℝ | ∃ a : ℕ+ → G,
    Function.HasFiniteMulSupport a ∧
    (∏ᶠ n, a n) = α ∧
    sSup (Set.range fun n : ℕ+ ↦ f (a n)) = r}

lemma one_le_finprod_apply_of_hasFiniteMulSupport {G : Type*} [One G]
    {a : ℕ+ → G} (ha : Function.HasFiniteMulSupport a)
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) :
    1 ≤ ∏ᶠ n : ℕ+, f (a n) := by
  classical
  let s := ha.toFinset
  have hsub : Function.mulSupport (fun n : ℕ+ ↦ f (a n)) ⊆ ↑s := by
    intro n hn
    have hnfa : f (a n) ≠ 1 := (Function.mem_mulSupport).1 hn
    by_contra hns
    have hna : a n = 1 := by
      by_contra hna
      exact hns (by
        have : n ∈ ha.toFinset := (ha.mem_toFinset).2 ((Function.mem_mulSupport).2 hna)
        simpa [s] using this)
    exact hnfa (by simp [hna, hf_one])
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  exact Finset.one_le_prod (fun n _ ↦ hf_lower (a n))

lemma one_le_sSup_range_apply_of_hasFiniteMulSupport {G : Type*} [One G]
    {a : ℕ+ → G} (ha : Function.HasFiniteMulSupport a)
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) :
    1 ≤ sSup (Set.range fun n : ℕ+ ↦ f (a n)) := by
  classical
  obtain ⟨n, hn⟩ := ha.exists_notMem
  have han : a n = 1 := by
    by_contra h
    exact hn ((Function.mem_mulSupport).2 h)
  have hmem : f (a n) ∈ Set.range fun n : ℕ+ ↦ f (a n) := ⟨n, rfl⟩
  have hle := le_csSup (bddAbove_range_apply_of_hasFiniteMulSupport ha f) hmem
  simpa [han, hf_one] using hle

lemma heightEnvOne_nonempty {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    {r : ℝ | ∃ a : ℕ+ → G,
      Function.HasFiniteMulSupport a ∧
      (∏ᶠ n, a n) = α ∧
      (∏ᶠ n, f (a n)) = r}.Nonempty := by
  classical
  refine ⟨f α, pnatSingle α, hasFiniteMulSupport_pnatSingle α,
    finprod_pnatSingle α, ?_⟩
  have hsub : Function.mulSupport (fun n : ℕ+ ↦ f (pnatSingle α n)) ⊆
      ↑({1} : Finset ℕ+) := by
    intro n hn
    by_cases h : n = 1
    · simpa [h]
    · exfalso
      exact (Function.mem_mulSupport).1 hn (by simp [pnatSingle, h, hf_one])
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  simp [pnatSingle]

lemma heightEnvInf_nonempty {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    {r : ℝ | ∃ a : ℕ+ → G,
      Function.HasFiniteMulSupport a ∧
      (∏ᶠ n, a n) = α ∧
      sSup (Set.range fun n : ℕ+ ↦ f (a n)) = r}.Nonempty := by
  exact ⟨f α, pnatSingle α, hasFiniteMulSupport_pnatSingle α,
    finprod_pnatSingle α, sSup_range_apply_pnatSingle f α hf_lower hf_one⟩

/- accepted add_to_file helper 5 -/
lemma heightEnvOne_bddBelow {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    BddBelow {r : ℝ | ∃ a : ℕ+ → G,
      Function.HasFiniteMulSupport a ∧
      (∏ᶠ n, a n) = α ∧
      (∏ᶠ n, f (a n)) = r} := by
  refine ⟨1, ?_⟩
  rintro r ⟨a, ha, -, hprod⟩
  rw [← hprod]
  exact one_le_finprod_apply_of_hasFiniteMulSupport ha f hf_lower hf_one

lemma heightEnvInf_bddBelow {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    BddBelow {r : ℝ | ∃ a : ℕ+ → G,
      Function.HasFiniteMulSupport a ∧
      (∏ᶠ n, a n) = α ∧
      sSup (Set.range fun n : ℕ+ ↦ f (a n)) = r} := by
  refine ⟨1, ?_⟩
  rintro r ⟨a, ha, -, hsup⟩
  rw [← hsup]
  exact one_le_sSup_range_apply_of_hasFiniteMulSupport ha f hf_lower hf_one

lemma one_le_heightEnvInf {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    1 ≤ heightEnvInf f α := by
  apply le_csInf (heightEnvInf_nonempty f hf_lower hf_one α)
  rintro r ⟨a, ha, -, hsup⟩
  rw [← hsup]
  exact one_le_sSup_range_apply_of_hasFiniteMulSupport ha f hf_lower hf_one

lemma heightEnvInf_le_self {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    heightEnvInf f α ≤ f α := by
  apply csInf_le (heightEnvInf_bddBelow f hf_lower hf_one α)
  exact ⟨pnatSingle α, hasFiniteMulSupport_pnatSingle α, finprod_pnatSingle α,
    sSup_range_apply_pnatSingle f α hf_lower hf_one⟩

/- accepted add_to_file helper 6 -/
lemma heightEnvInf_le_inv_of_inv {G : Type*} [CommGroup G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1)
    (hf_inv : ∀ α : G, f α⁻¹ = f α) (α : G) :
    heightEnvInf f α⁻¹ ≤ heightEnvInf f α := by
  apply le_csInf (heightEnvInf_nonempty f hf_lower hf_one α)
  rintro r ⟨a, ha, hprod, hsup⟩
  apply csInf_le (heightEnvInf_bddBelow f hf_lower hf_one α⁻¹)
  refine ⟨a⁻¹, ha.inv, ?_, ?_⟩
  · change (∏ᶠ n : ℕ+, (a n)⁻¹) = α⁻¹
    rw [finprod_inv_distrib, hprod]
  · rw [← hsup]
    congr 1
    ext y
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨n, by simp [hf_inv]⟩
    · rintro ⟨n, rfl⟩
      exact ⟨n, by simp [hf_inv]⟩

lemma heightEnvInf_inv {G : Type*} [CommGroup G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1)
    (hf_inv : ∀ α : G, f α⁻¹ = f α) (α : G) :
    heightEnvInf f α⁻¹ = heightEnvInf f α := by
  apply le_antisymm
  · exact heightEnvInf_le_inv_of_inv f hf_lower hf_one hf_inv α
  · simpa using heightEnvInf_le_inv_of_inv f hf_lower hf_one hf_inv α⁻¹

lemma heightEnvInf_one {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) :
    heightEnvInf f 1 = 1 := by
  apply le_antisymm
  · simpa [hf_one] using heightEnvInf_le_self f hf_lower hf_one (1 : G)
  · exact one_le_heightEnvInf f hf_lower hf_one 1

/- accepted add_to_file helper 7 -/
lemma heightEnvInf_mul {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1)
    (α β : G) :
    heightEnvInf f (α * β) ≤ max (heightEnvInf f α) (heightEnvInf f β) := by
  classical
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨r, ⟨a, ha, hpa, hsa⟩, hrlt⟩ :=
    exists_lt_of_csInf_lt (heightEnvInf_nonempty f hf_lower hf_one α)
      (lt_add_of_pos_right (heightEnvInf f α) hε)
  obtain ⟨s, ⟨b, hb, hpb, hsb⟩, hslt⟩ :=
    exists_lt_of_csInf_lt (heightEnvInf_nonempty f hf_lower hf_one β)
      (lt_add_of_pos_right (heightEnvInf f β) hε)
  let c : ℕ+ → G := fun n ↦ Sum.elim a b (pnatInterleaveEquiv n)
  have hc : Function.HasFiniteMulSupport c := hasFiniteMulSupport_interleave ha hb
  have hprod : (∏ᶠ n, c n) = α * β := by
    rw [finprod_interleave ha hb, hpa, hpb]
  have hsup : sSup (Set.range fun n : ℕ+ ↦ f (c n)) = max r s := by
    rw [← hsa, ← hsb]
    exact sSup_range_interleave ha hb f
  have hupper : heightEnvInf f (α * β) ≤ max r s := by
    apply csInf_le (heightEnvInf_bddBelow f hf_lower hf_one (α * β))
    exact ⟨c, hc, hprod, hsup⟩
  have hlt : max r s < max (heightEnvInf f α) (heightEnvInf f β) + ε := by
    calc
      max r s < max (heightEnvInf f α + ε) (heightEnvInf f β + ε) :=
        max_lt_max hrlt hslt
      _ = max (heightEnvInf f α) (heightEnvInf f β) + ε := max_add_add_right _ _ _
  exact hupper.trans hlt.le

/- accepted add_to_file helper 8 -/
lemma single_le_finset_prod_of_one_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → ℝ) (hg : ∀ i, 1 ≤ g i)
    {i : ι} (hi : i ∈ s) :
    g i ≤ ∏ j ∈ s, g j := by
  have hrest : 1 ≤ ∏ j ∈ s.erase i, g j :=
    Finset.one_le_prod (fun j _ ↦ hg j)
  have hgi0 : 0 ≤ g i := zero_le_one.trans (hg i)
  calc
    g i ≤ g i * ∏ j ∈ s.erase i, g j := le_mul_of_one_le_right hgi0 hrest
    _ = ∏ j ∈ s, g j := Finset.mul_prod_erase s g hi

lemma sSup_range_apply_le_finprod_apply_of_hasFiniteMulSupport {G : Type*} [One G]
    {a : ℕ+ → G} (ha : Function.HasFiniteMulSupport a)
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) :
    sSup (Set.range fun n : ℕ+ ↦ f (a n)) ≤ ∏ᶠ n : ℕ+, f (a n) := by
  classical
  let s := ha.toFinset
  have hsub : Function.mulSupport (fun n : ℕ+ ↦ f (a n)) ⊆ ↑s := by
    intro n hn
    have hnfa : f (a n) ≠ 1 := (Function.mem_mulSupport).1 hn
    by_contra hns
    have hna : a n = 1 := by
      by_contra hna
      exact hns (by
        have : n ∈ ha.toFinset := (ha.mem_toFinset).2 ((Function.mem_mulSupport).2 hna)
        simpa [s] using this)
    exact hnfa (by simp [hna, hf_one])
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨n, rfl⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  by_cases hn : a n = 1
  · change f (a n) ≤ ∏ i ∈ s, f (a i)
    rw [hn, hf_one]
    exact Finset.one_le_prod (fun m _ ↦ hf_lower (a m))
  · have hns : n ∈ s := by
      have : n ∈ ha.toFinset := (ha.mem_toFinset).2 ((Function.mem_mulSupport).2 hn)
      simpa [s] using this
    exact single_le_finset_prod_of_one_le s (fun m ↦ f (a m))
      (fun m ↦ hf_lower (a m)) hns

lemma heightEnvInf_le_heightEnvOne {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    heightEnvInf f α ≤ heightEnvOne f α := by
  apply le_csInf (heightEnvOne_nonempty f hf_lower hf_one α)
  rintro r ⟨a, ha, hprod, hval⟩
  rw [← hval]
  have hInf_le_sup : heightEnvInf f α ≤ sSup (Set.range fun n : ℕ+ ↦ f (a n)) := by
    apply csInf_le (heightEnvInf_bddBelow f hf_lower hf_one α)
    exact ⟨a, ha, hprod, rfl⟩
  exact hInf_le_sup.trans
    (sSup_range_apply_le_finprod_apply_of_hasFiniteMulSupport ha f hf_lower hf_one)

/- accepted add_to_file helper 9 -/
lemma strong_apply_finprod_le_sSup_range_apply {G : Type*} [CommMonoid G]
    {a : ℕ+ → G} (ha : Function.HasFiniteMulSupport a)
    (σ : G → ℝ) (hσ_lower : ∀ α : G, 1 ≤ σ α) (hσ_one : σ 1 = 1)
    (hσ_mul : ∀ α β : G, σ (α * β) ≤ max (σ α) (σ β)) :
    σ (∏ᶠ n : ℕ+, a n) ≤ sSup (Set.range fun n : ℕ+ ↦ σ (a n)) := by
  classical
  let s := ha.toFinset
  have hsub : Function.mulSupport a ⊆ ↑s := by
    intro n hn
    have : n ∈ ha.toFinset := (ha.mem_toFinset).2 hn
    simpa [s] using this
  rw [finprod_eq_prod_of_mulSupport_subset a hsub]
  have hbdd : BddAbove (Set.range fun n : ℕ+ ↦ σ (a n)) :=
    bddAbove_range_apply_of_hasFiniteMulSupport ha σ
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty]
      obtain ⟨n, hn⟩ := ha.exists_notMem
      have han : a n = 1 := by
        by_contra h
        exact hn ((Function.mem_mulSupport).2 h)
      exact le_csSup hbdd ⟨n, by simp [han]⟩
  | insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (hσ_mul (a i) (∏ x ∈ s, a x)).trans
        (max_le (le_csSup hbdd ⟨i, rfl⟩) ih)

lemma sSup_range_mono {G : Type*} [One G]
    {a : ℕ+ → G} (ha : Function.HasFiniteMulSupport a)
    {σ f : G → ℝ} (hσf : ∀ α : G, σ α ≤ f α) :
    sSup (Set.range fun n : ℕ+ ↦ σ (a n)) ≤
      sSup (Set.range fun n : ℕ+ ↦ f (a n)) := by
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨n, rfl⟩
  exact (hσf (a n)).trans
    (le_csSup (bddAbove_range_apply_of_hasFiniteMulSupport ha f) ⟨n, rfl⟩)

lemma strong_le_heightEnvInf {G : Type*} [CommMonoid G]
    (σ f : G → ℝ)
    (hσ_lower : ∀ α : G, 1 ≤ σ α) (hσ_one : σ 1 = 1)
    (hσ_mul : ∀ α β : G, σ (α * β) ≤ max (σ α) (σ β))
    (hσf : ∀ α : G, σ α ≤ f α)
    (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    σ α ≤ heightEnvInf f α := by
  apply le_csInf (heightEnvInf_nonempty f hf_lower hf_one α)
  rintro r ⟨a, ha, hprod, hsup⟩
  rw [← hsup]
  calc
    σ α = σ (∏ᶠ n : ℕ+, a n) := by rw [hprod]
    _ ≤ sSup (Set.range fun n : ℕ+ ↦ σ (a n)) :=
      strong_apply_finprod_le_sSup_range_apply ha σ hσ_lower hσ_one hσ_mul
    _ ≤ sSup (Set.range fun n : ℕ+ ↦ f (a n)) := sSup_range_mono ha hσf

/- accepted add_to_file helper 10 -/
lemma heightEnvOne_le_self {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    heightEnvOne f α ≤ f α := by
  classical
  apply csInf_le (heightEnvOne_bddBelow f hf_lower hf_one α)
  refine ⟨pnatSingle α, hasFiniteMulSupport_pnatSingle α, finprod_pnatSingle α, ?_⟩
  have hsub : Function.mulSupport (fun n : ℕ+ ↦ f (pnatSingle α n)) ⊆
      ↑({1} : Finset ℕ+) := by
    intro n hn
    by_cases h : n = 1
    · simpa [h]
    · exfalso
      exact (Function.mem_mulSupport).1 hn (by simp [pnatSingle, h, hf_one])
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  simp [pnatSingle]

lemma one_le_heightEnvOne {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) (α : G) :
    1 ≤ heightEnvOne f α := by
  apply le_csInf (heightEnvOne_nonempty f hf_lower hf_one α)
  rintro r ⟨a, ha, -, hprod⟩
  rw [← hprod]
  exact one_le_finprod_apply_of_hasFiniteMulSupport ha f hf_lower hf_one

lemma heightEnvOne_one {G : Type*} [CommMonoid G]
    (f : G → ℝ) (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) :
    heightEnvOne f 1 = 1 := by
  apply le_antisymm
  · simpa [hf_one] using heightEnvOne_le_self f hf_lower hf_one (1 : G)
  · exact one_le_heightEnvOne f hf_lower hf_one 1

lemma heightEnvInf_eq_self_of_strong {G : Type*} [CommMonoid G]
    (f : G → ℝ)
    (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1)
    (hf_mul : ∀ α β : G, f (α * β) ≤ max (f α) (f β)) :
    heightEnvInf f = f := by
  funext α
  apply le_antisymm
  · exact heightEnvInf_le_self f hf_lower hf_one α
  · exact strong_le_heightEnvInf f f hf_lower hf_one hf_mul
      (fun β ↦ le_rfl) hf_lower hf_one α

lemma heightEnvOne_eq_self_of_strong {G : Type*} [CommMonoid G]
    (f : G → ℝ)
    (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1)
    (hf_mul : ∀ α β : G, f (α * β) ≤ max (f α) (f β)) :
    heightEnvOne f = f := by
  funext α
  apply le_antisymm
  · exact heightEnvOne_le_self f hf_lower hf_one α
  · calc
      f α = heightEnvInf f α := by
        rw [heightEnvInf_eq_self_of_strong f hf_lower hf_one hf_mul]
      _ ≤ heightEnvOne f α := heightEnvInf_le_heightEnvOne f hf_lower hf_one α

lemma heightEnvInf_mono {G : Type*} [CommMonoid G]
    {f g : G → ℝ}
    (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1)
    (hg_lower : ∀ α : G, 1 ≤ g α) (hg_one : g 1 = 1)
    (hfg : ∀ α : G, f α ≤ g α) (α : G) :
    heightEnvInf f α ≤ heightEnvInf g α := by
  apply le_csInf (heightEnvInf_nonempty g hg_lower hg_one α)
  rintro r ⟨a, ha, hprod, hsup⟩
  rw [← hsup]
  have hleft : heightEnvInf f α ≤ sSup (Set.range fun n : ℕ+ ↦ f (a n)) := by
    apply csInf_le (heightEnvInf_bddBelow f hf_lower hf_one α)
    exact ⟨a, ha, hprod, rfl⟩
  exact hleft.trans (sSup_range_mono ha hfg)

lemma heightEnvInf_heightEnvOne_eq_heightEnvInf {G : Type*} [CommMonoid G]
    (f : G → ℝ)
    (hf_lower : ∀ α : G, 1 ≤ f α) (hf_one : f 1 = 1) :
    heightEnvInf f = heightEnvInf (heightEnvOne f) := by
  funext α
  apply le_antisymm
  · exact strong_le_heightEnvInf (heightEnvInf f) (heightEnvOne f)
      (one_le_heightEnvInf f hf_lower hf_one)
      (heightEnvInf_one f hf_lower hf_one)
      (heightEnvInf_mul f hf_lower hf_one)
      (heightEnvInf_le_heightEnvOne f hf_lower hf_one)
      (one_le_heightEnvOne f hf_lower hf_one)
      (heightEnvOne_one f hf_lower hf_one)
      α
  · exact heightEnvInf_mono
      (one_le_heightEnvOne f hf_lower hf_one)
      (heightEnvOne_one f hf_lower hf_one)
      hf_lower hf_one
      (heightEnvOne_le_self f hf_lower hf_one) α

/- verified submission -/
theorem strongMetricEnvelopeOfHeight
    {G : Type*} [CommGroup G] (ρ : G → ℝ)
    (hρ_lower : ∀ α : G, 1 ≤ ρ α)
    (hρ_one : ρ 1 = 1)
    (hρ_inv : ∀ α : G, ρ α⁻¹ = ρ α) :
    let envelopeOne : (G → ℝ) → G → ℝ := fun f α ↦
      sInf {r : ℝ | ∃ a : ℕ+ → G,
        Function.HasFiniteMulSupport a ∧
        (∏ᶠ n, a n) = α ∧
        (∏ᶠ n, f (a n)) = r}
    let envelopeInf : (G → ℝ) → G → ℝ := fun f α ↦
      sInf {r : ℝ | ∃ a : ℕ+ → G,
        Function.HasFiniteMulSupport a ∧
        (∏ᶠ n, a n) = α ∧
        sSup (Set.range fun n : ℕ+ ↦ f (a n)) = r}
    ((∀ α : G, 1 ≤ envelopeInf ρ α) ∧
      envelopeInf ρ 1 = 1 ∧
      (∀ α : G, envelopeInf ρ α⁻¹ = envelopeInf ρ α) ∧
      (∀ α β : G,
        envelopeInf ρ (α * β) ≤ max (envelopeInf ρ α) (envelopeInf ρ β))) ∧
    (∀ α : G, envelopeInf ρ α ≤ envelopeOne ρ α) ∧
    (∀ σ : G → ℝ,
      ((∀ α : G, 1 ≤ σ α) ∧
        σ 1 = 1 ∧
        (∀ α : G, σ α⁻¹ = σ α) ∧
        (∀ α β : G, σ (α * β) ≤ max (σ α) (σ β))) →
      (∀ α : G, σ α ≤ ρ α) →
      ∀ α : G, σ α ≤ envelopeInf ρ α) ∧
    (ρ = envelopeInf ρ ↔
      (∀ α : G, 1 ≤ ρ α) ∧
      ρ 1 = 1 ∧
      (∀ α : G, ρ α⁻¹ = ρ α) ∧
      (∀ α β : G, ρ (α * β) ≤ max (ρ α) (ρ β))) ∧
    (envelopeInf ρ = envelopeInf (envelopeOne ρ) ∧
      envelopeInf (envelopeOne ρ) = envelopeOne (envelopeInf ρ) ∧
      envelopeOne (envelopeInf ρ) = envelopeInf (envelopeInf ρ)) := by
  refine ⟨⟨one_le_heightEnvInf ρ hρ_lower hρ_one,
    heightEnvInf_one ρ hρ_lower hρ_one,
    heightEnvInf_inv ρ hρ_lower hρ_one hρ_inv,
    heightEnvInf_mul ρ hρ_lower hρ_one⟩,
    heightEnvInf_le_heightEnvOne ρ hρ_lower hρ_one,
    ?_, ?_, ?_⟩
  · intro σ hσ hσρ α
    rcases hσ with ⟨hσ_lower, hσ_one, -, hσ_mul⟩
    exact strong_le_heightEnvInf σ ρ hσ_lower hσ_one hσ_mul hσρ
      hρ_lower hρ_one α
  · constructor
    · intro h
      refine ⟨hρ_lower, hρ_one, hρ_inv, ?_⟩
      intro α β
      rw [h]
      exact heightEnvInf_mul ρ hρ_lower hρ_one α β
    · rintro ⟨hρ_lower', hρ_one', -, hρ_mul⟩
      exact (heightEnvInf_eq_self_of_strong ρ hρ_lower' hρ_one' hρ_mul).symm
  · refine ⟨heightEnvInf_heightEnvOne_eq_heightEnvInf ρ hρ_lower hρ_one, ?_, ?_⟩
    · have h₁ := heightEnvInf_heightEnvOne_eq_heightEnvInf ρ hρ_lower hρ_one
      have h₂ := heightEnvOne_eq_self_of_strong (heightEnvInf ρ)
        (one_le_heightEnvInf ρ hρ_lower hρ_one)
        (heightEnvInf_one ρ hρ_lower hρ_one)
        (heightEnvInf_mul ρ hρ_lower hρ_one)
      exact h₁.symm.trans h₂.symm
    · have h₁ := heightEnvOne_eq_self_of_strong (heightEnvInf ρ)
        (one_le_heightEnvInf ρ hρ_lower hρ_one)
        (heightEnvInf_one ρ hρ_lower hρ_one)
        (heightEnvInf_mul ρ hρ_lower hρ_one)
      have h₂ := heightEnvInf_eq_self_of_strong (heightEnvInf ρ)
        (one_le_heightEnvInf ρ hρ_lower hρ_one)
        (heightEnvInf_one ρ hρ_lower hρ_one)
        (heightEnvInf_mul ρ hρ_lower hρ_one)
      exact h₁.trans h₂.symm

end Rollout_p2227_strongmetricenvelopeofheight

namespace Rollout_p2109_stable_equivalence_empty_subfield_points_i

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

end Rollout_p2109_stable_equivalence_empty_subfield_points_i

namespace Rollout_p0786_projective_iff_projective_in_thick_subcate

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

namespace Rollout_p2771_pbw_filtered_quadratic_relations_unique

/- accepted add_to_file helper 1 -/
lemma graded_proj_eq_of_mem
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {m n : ℕ} {x : T} (hx : x ∈ 𝒯 m) :
    GradedAlgebra.proj 𝒯 n x = if m = n then x else 0 := by
  classical
  rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem 𝒯 hx]
  by_cases h : m = n
  · subst h
    simp
  · simp [DirectSum.of_apply, h]

lemma graded_proj_self
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {n : ℕ} {x : T} (hx : x ∈ 𝒯 n) :
    GradedAlgebra.proj 𝒯 n x = x := by
  simpa using graded_proj_eq_of_mem 𝒯 (m := n) (n := n) hx

lemma graded_proj_mem
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (n : ℕ) (x : T) :
    GradedAlgebra.proj 𝒯 n x ∈ 𝒯 n := by
  classical
  rw [GradedAlgebra.proj_apply]
  exact (((DirectSum.decompose 𝒯) x) n).property

/- accepted add_to_file helper 2 -/
lemma graded_proj_eq_zero_of_mem_iSup_fin
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {n m : ℕ} (hnm : n ≤ m) {x : T}
    (hx : x ∈ ⨆ i : Fin n, 𝒯 (i : ℕ)) :
    GradedAlgebra.proj 𝒯 m x = 0 := by
  classical
  rw [Submodule.mem_iSup] at hx
  apply hx (LinearMap.ker (GradedAlgebra.proj 𝒯 m))
  intro i y hy
  rw [LinearMap.mem_ker, graded_proj_eq_of_mem 𝒯 hy]
  have hne : (i : ℕ) ≠ m := by
    omega
  simp [hne]

/- accepted add_to_file helper 3 -/
lemma graded_mem_iSup_fin_of_proj_eq_zero
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {n : ℕ} {x : T}
    (hx : ∀ m : ℕ, n ≤ m → GradedAlgebra.proj 𝒯 m x = 0) :
    x ∈ ⨆ i : Fin n, 𝒯 (i : ℕ) := by
  classical
  let d := DirectSum.decompose 𝒯 x
  have hsum : (∑ i ∈ d.support, ((d i) : T)) = x := by
    simpa [d] using DirectSum.sum_support_decompose 𝒯 x
  rw [← hsum]
  apply Submodule.sum_mem
  intro i hi
  have hlt : i < n := by
    by_contra hnot
    have hni : n ≤ i := Nat.le_of_not_gt hnot
    have hproj : GradedAlgebra.proj 𝒯 i x = 0 := hx i hni
    have hdi : d i = 0 := by
      apply Subtype.ext
      simpa [d, GradedAlgebra.proj_apply] using hproj
    have : i ∉ d.support := (DFinsupp.notMem_support_iff).2 hdi
    exact this hi
  exact le_iSup (fun j : Fin n => 𝒯 (j : ℕ)) ⟨i, hlt⟩ ((d i).property)

/- accepted add_to_file helper 4 -/
lemma graded_sub_proj_two_mem_iSup_fin_two
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {x : T} (hx : x ∈ ⨆ i : Fin 3, 𝒯 (i : ℕ)) :
    x - GradedAlgebra.proj 𝒯 2 x ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ) := by
  classical
  apply graded_mem_iSup_fin_of_proj_eq_zero 𝒯 (n := 2)
  intro m hm
  by_cases h2 : m = 2
  · subst h2
    rw [map_sub, graded_proj_self 𝒯 (n := 2)
      (x := GradedAlgebra.proj 𝒯 2 x) (graded_proj_mem 𝒯 2 x)]
    simp
  · have hm3 : 3 ≤ m := by omega
    have hxm : GradedAlgebra.proj 𝒯 m x = 0 :=
      graded_proj_eq_zero_of_mem_iSup_fin 𝒯 hm3 hx
    have hpm : GradedAlgebra.proj 𝒯 m (GradedAlgebra.proj 𝒯 2 x) = 0 := by
      rw [graded_proj_eq_of_mem 𝒯 (graded_proj_mem 𝒯 2 x)]
      have h2' : 2 ≠ m := fun h => h2 h.symm
      simp [h2']
    rw [map_sub, hxm, hpm, sub_zero]

/- accepted add_to_file helper 5 -/
lemma graded_proj_two_mul_of_mem_two
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (a s b : T) (hs : s ∈ 𝒯 2) :
    GradedAlgebra.proj 𝒯 2 (a * s * b) =
      GradedAlgebra.proj 𝒯 0 a * s * GradedAlgebra.proj 𝒯 0 b := by
  classical
  let da := DirectSum.decompose 𝒯 a
  let db := DirectSum.decompose 𝒯 b
  have ha : (∑ i ∈ da.support, ((da i) : T)) = a := by
    simpa [da] using DirectSum.sum_support_decompose 𝒯 a
  have hb : (∑ j ∈ db.support, ((db j) : T)) = b := by
    simpa [db] using DirectSum.sum_support_decompose 𝒯 b
  have hterm (i j : ℕ) :
      GradedAlgebra.proj 𝒯 2 (((da i : T) * s) * (db j : T)) =
        if i = 0 ∧ j = 0 then ((da i : T) * s) * (db j : T) else 0 := by
    have hmem : ((da i : T) * s) * (db j : T) ∈ 𝒯 (i + 2 + j) := by
      exact SetLike.mul_mem_graded
        (SetLike.mul_mem_graded (da i).property hs) (db j).property
    rw [graded_proj_eq_of_mem 𝒯 hmem]
    by_cases hij : i + 2 + j = 2
    · have hi : i = 0 := by omega
      have hj : j = 0 := by omega
      simp [hij, hi, hj]
    · have hnot : ¬ (i = 0 ∧ j = 0) := by
        rintro ⟨hi, hj⟩
        omega
      simp [hij, hnot]
  have hsum :
      (∑ i ∈ da.support, ∑ j ∈ db.support,
          GradedAlgebra.proj 𝒯 2 (((da i : T) * s) * (db j : T))) =
        ((da 0 : T) * s) * (db 0 : T) := by
    simp_rw [hterm]
    let f := fun i : ℕ => ∑ j ∈ db.support,
      (if i = 0 ∧ j = 0 then ((da i : T) * s) * (db j : T) else 0)
    have hinner : f 0 = ((da 0 : T) * s) * (db 0 : T) := by
      dsimp [f]
      apply Finset.sum_eq_single 0
      · intro j hj hj0
        simp [hj0]
      · intro h0
        have hdb : db 0 = 0 := (DFinsupp.notMem_support_iff).1 h0
        simp [hdb]
    calc
      (∑ i ∈ da.support, ∑ j ∈ db.support,
          if i = 0 ∧ j = 0 then ((da i : T) * s) * (db j : T) else 0)
          = f 0 := by
        apply Finset.sum_eq_single 0
        · intro i hi hi0
          dsimp [f]
          apply Finset.sum_eq_zero
          intro j hj
          simp [hi0]
        · intro h0
          dsimp [f]
          apply Finset.sum_eq_zero
          intro j hj
          have hda : da 0 = 0 := (DFinsupp.notMem_support_iff).1 h0
          by_cases hj0 : j = 0
          · simp [hj0, hda]
          · simp [hj0]
      _ = ((da 0 : T) * s) * (db 0 : T) := hinner
  calc
    GradedAlgebra.proj 𝒯 2 (a * s * b)
        = GradedAlgebra.proj 𝒯 2
            (∑ i ∈ da.support, ∑ j ∈ db.support,
              ((da i : T) * s) * (db j : T)) := by
          rw [← ha, ← hb]
          rw [Finset.sum_mul, Finset.sum_mul_sum]
    _ = ∑ i ∈ da.support,
          GradedAlgebra.proj 𝒯 2
            (∑ j ∈ db.support, ((da i : T) * s) * (db j : T)) := by
          rw [map_sum]
    _ = ∑ i ∈ da.support, ∑ j ∈ db.support,
          GradedAlgebra.proj 𝒯 2 (((da i : T) * s) * (db j : T)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [map_sum]
    _ = ((da 0 : T) * s) * (db 0 : T) := hsum
    _ = GradedAlgebra.proj 𝒯 0 a * s * GradedAlgebra.proj 𝒯 0 b := by
          have ha0 : GradedAlgebra.proj 𝒯 0 a = (da 0 : T) := by
            simp [GradedAlgebra.proj_apply, da]
          have hb0 : GradedAlgebra.proj 𝒯 0 b = (db 0 : T) := by
            simp [GradedAlgebra.proj_apply, db]
          rw [ha0, hb0]

/- accepted add_to_file helper 6 -/
lemma graded_span_degree_two_low_components
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (S : Set T) (hS : S ⊆ 𝒯 2)
    {x : T} (hx : x ∈ TwoSidedIdeal.span S) :
    ∀ i < 2, (DirectSum.decompose 𝒯 x) i = 0 := by
  classical
  refine TwoSidedIdeal.span_induction
    (p := fun x _ => ∀ i < 2, (DirectSum.decompose 𝒯 x) i = 0)
    ?_ ?_ ?_ ?_ ?_ ?_ hx
  · intro x hx i hi
    rw [DirectSum.decompose_of_mem 𝒯 (hS hx)]
    have hne : 2 ≠ i := by omega
    simp [DirectSum.of_apply, hne]
  · intro i hi
    simp
  · intro x y hx hy ihx ihy i hi
    simp [ihx i hi, ihy i hi]
  · intro x hx ihx i hi
    rw [DirectSum.decompose_neg]
    change - (((DirectSum.decompose 𝒯) x) i) = 0
    rw [ihx i hi, neg_zero]
  · intro a x hx ihx i hi
    rw [DirectSum.decompose_mul]
    exact mul_apply_eq_zero (A := 𝒯)
      (m := 0) (n := 2)
      (by intro j hj; omega)
      ihx hi
  · intro b x hx ihx i hi
    rw [DirectSum.decompose_mul]
    exact mul_apply_eq_zero (A := 𝒯)
      (m := 2) (n := 0)
      ihx
      (by intro j hj; omega)
      (by simpa using hi)

/- accepted add_to_file helper 7 -/
lemma graded_proj_two_mul_left_eq_of_low
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (a x : T)
    (hlow : ∀ i < 2, (DirectSum.decompose 𝒯 x) i = 0) :
    GradedAlgebra.proj 𝒯 2 (a * x) =
      GradedAlgebra.proj 𝒯 2 (a * GradedAlgebra.proj 𝒯 2 x) := by
  classical
  let d := DirectSum.decompose 𝒯 x
  have hsum : (∑ i ∈ d.support, ((d i) : T)) = x := by
    simpa [d] using DirectSum.sum_support_decompose 𝒯 x
  have hterm_zero_of_ne (i : ℕ) (hi : i ≠ 2) :
      GradedAlgebra.proj 𝒯 2 (a * (d i : T)) = 0 := by
    by_cases hlt : i < 2
    · have hdi : d i = 0 := by
        simpa [d] using hlow i hlt
      simp [hdi]
    · have hgt : 2 < i := by omega
      have hcomp : ((DirectSum.decompose 𝒯) (a * (d i : T))) 2 = 0 := by
        rw [DirectSum.decompose_mul, DirectSum.decompose_of_mem 𝒯 (d i).property]
        exact mul_apply_eq_zero (A := 𝒯)
          (m := 0) (n := i)
          (by intro j hj; omega)
          (by
            intro j hj
            have hne : i ≠ j := by omega
            simp [DirectSum.of_apply, hne])
          (by simpa using hgt)
      rw [GradedAlgebra.proj_apply, hcomp]
      rfl
  have hsum_single :
      (∑ i ∈ d.support, GradedAlgebra.proj 𝒯 2 (a * (d i : T))) =
        GradedAlgebra.proj 𝒯 2 (a * (d 2 : T)) := by
    apply Finset.sum_eq_single 2
    · intro i hi hi2
      exact hterm_zero_of_ne i hi2
    · intro h2
      have hd2 : d 2 = 0 := (DFinsupp.notMem_support_iff).1 h2
      simp [hd2]
  calc
    GradedAlgebra.proj 𝒯 2 (a * x)
        = GradedAlgebra.proj 𝒯 2 (a * ∑ i ∈ d.support, ((d i) : T)) := by
          rw [hsum]
    _ = ∑ i ∈ d.support, GradedAlgebra.proj 𝒯 2 (a * (d i : T)) := by
          rw [Finset.mul_sum, map_sum]
    _ = GradedAlgebra.proj 𝒯 2 (a * (d 2 : T)) := hsum_single
    _ = GradedAlgebra.proj 𝒯 2 (a * GradedAlgebra.proj 𝒯 2 x) := by
          rw [GradedAlgebra.proj_apply]
          simp [d]

lemma graded_proj_two_mul_right_eq_of_low
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (x b : T)
    (hlow : ∀ i < 2, (DirectSum.decompose 𝒯 x) i = 0) :
    GradedAlgebra.proj 𝒯 2 (x * b) =
      GradedAlgebra.proj 𝒯 2 (GradedAlgebra.proj 𝒯 2 x * b) := by
  classical
  let d := DirectSum.decompose 𝒯 x
  have hsum : (∑ i ∈ d.support, ((d i) : T)) = x := by
    simpa [d] using DirectSum.sum_support_decompose 𝒯 x
  have hterm_zero_of_ne (i : ℕ) (hi : i ≠ 2) :
      GradedAlgebra.proj 𝒯 2 ((d i : T) * b) = 0 := by
    by_cases hlt : i < 2
    · have hdi : d i = 0 := by
        simpa [d] using hlow i hlt
      simp [hdi]
    · have hgt : 2 < i := by omega
      have hcomp : ((DirectSum.decompose 𝒯) ((d i : T) * b)) 2 = 0 := by
        rw [DirectSum.decompose_mul, DirectSum.decompose_of_mem 𝒯 (d i).property]
        exact mul_apply_eq_zero (A := 𝒯)
          (m := i) (n := 0)
          (by
            intro j hj
            have hne : i ≠ j := by omega
            simp [DirectSum.of_apply, hne])
          (by intro j hj; omega)
          (by simpa using hgt)
      rw [GradedAlgebra.proj_apply, hcomp]
      rfl
  have hsum_single :
      (∑ i ∈ d.support, GradedAlgebra.proj 𝒯 2 ((d i : T) * b)) =
        GradedAlgebra.proj 𝒯 2 ((d 2 : T) * b) := by
    apply Finset.sum_eq_single 2
    · intro i hi hi2
      exact hterm_zero_of_ne i hi2
    · intro h2
      have hd2 : d 2 = 0 := (DFinsupp.notMem_support_iff).1 h2
      simp [hd2]
  calc
    GradedAlgebra.proj 𝒯 2 (x * b)
        = GradedAlgebra.proj 𝒯 2 ((∑ i ∈ d.support, ((d i) : T)) * b) := by
          rw [hsum]
    _ = ∑ i ∈ d.support, GradedAlgebra.proj 𝒯 2 ((d i : T) * b) := by
          rw [Finset.sum_mul, map_sum]
    _ = GradedAlgebra.proj 𝒯 2 ((d 2 : T) * b) := hsum_single
    _ = GradedAlgebra.proj 𝒯 2 (GradedAlgebra.proj 𝒯 2 x * b) := by
          rw [GradedAlgebra.proj_apply]
          simp [d]

/- accepted add_to_file helper 8 -/
lemma graded_degree_two_mem_span_of_degree_two_generators
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (S : Set T) (hS : S ⊆ 𝒯 2)
    {z : T} (hz₂ : z ∈ 𝒯 2)
    (hz : z ∈ TwoSidedIdeal.span S) :
    z ∈ AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ s ∈ S, ∃ b ∈ 𝒯 0, x = a * s * b} := by
  classical
  let C : AddSubgroup T := AddSubgroup.closure
    {x : T | ∃ a ∈ 𝒯 0, ∃ s ∈ S, ∃ b ∈ 𝒯 0, x = a * s * b}
  have hproj_left (a c : T) (hc : c ∈ C) :
      GradedAlgebra.proj 𝒯 2 (a * c) ∈ C := by
    induction hc using AddSubgroup.closure_induction with
    | mem x hx =>
        rcases hx with ⟨u, hu, s, hsS, v, hv, rfl⟩
        have hrewrite :
            GradedAlgebra.proj 𝒯 2 (a * (u * s * v)) =
              GradedAlgebra.proj 𝒯 0 (a * u) * s * GradedAlgebra.proj 𝒯 0 v := by
          simpa [mul_assoc] using
            graded_proj_two_mul_of_mem_two 𝒯 (a * u) s v (hS hsS)
        rw [hrewrite]
        apply AddSubgroup.subset_closure
        exact ⟨GradedAlgebra.proj 𝒯 0 (a * u), graded_proj_mem 𝒯 0 (a * u),
          s, hsS, GradedAlgebra.proj 𝒯 0 v, graded_proj_mem 𝒯 0 v, rfl⟩
    | zero =>
        simp
    | add x y hx hy ihx ihy =>
        rw [mul_add, map_add]
        exact C.add_mem ihx ihy
    | neg x hx ihx =>
        rw [mul_neg, map_neg]
        exact C.neg_mem ihx
  have hproj_right (c b : T) (hc : c ∈ C) :
      GradedAlgebra.proj 𝒯 2 (c * b) ∈ C := by
    induction hc using AddSubgroup.closure_induction with
    | mem x hx =>
        rcases hx with ⟨u, hu, s, hsS, v, hv, rfl⟩
        have hrewrite :
            GradedAlgebra.proj 𝒯 2 ((u * s * v) * b) =
              GradedAlgebra.proj 𝒯 0 u * s * GradedAlgebra.proj 𝒯 0 (v * b) := by
          simpa [mul_assoc] using
            graded_proj_two_mul_of_mem_two 𝒯 u s (v * b) (hS hsS)
        rw [hrewrite]
        apply AddSubgroup.subset_closure
        exact ⟨GradedAlgebra.proj 𝒯 0 u, graded_proj_mem 𝒯 0 u,
          s, hsS, GradedAlgebra.proj 𝒯 0 (v * b), graded_proj_mem 𝒯 0 (v * b), rfl⟩
    | zero =>
        simp
    | add x y hx hy ihx ihy =>
        rw [add_mul, map_add]
        exact C.add_mem ihx ihy
    | neg x hx ihx =>
        rw [neg_mul, map_neg]
        exact C.neg_mem ihx
  have hproj : GradedAlgebra.proj 𝒯 2 z ∈ C := by
    refine TwoSidedIdeal.span_induction
      (p := fun x _ => GradedAlgebra.proj 𝒯 2 x ∈ C)
      ?_ ?_ ?_ ?_ ?_ ?_ hz
    · intro x hx
      rw [graded_proj_self 𝒯 (hS hx)]
      apply AddSubgroup.subset_closure
      exact ⟨1, SetLike.GradedOne.one_mem, x, hx, 1, SetLike.GradedOne.one_mem, by simp⟩
    · simp
    · intro x y hx hy ihx ihy
      rw [map_add]
      exact C.add_mem ihx ihy
    · intro x hx ihx
      rw [map_neg]
      exact C.neg_mem ihx
    · intro a x hx ihx
      rw [graded_proj_two_mul_left_eq_of_low 𝒯 a x
        (graded_span_degree_two_low_components 𝒯 S hS hx)]
      exact hproj_left a (GradedAlgebra.proj 𝒯 2 x) ihx
    · intro b x hx ihx
      rw [graded_proj_two_mul_right_eq_of_low 𝒯 x b
        (graded_span_degree_two_low_components 𝒯 S hS hx)]
      exact hproj_right (GradedAlgebra.proj 𝒯 2 x) b ihx
  rwa [graded_proj_self 𝒯 hz₂] at hproj

/- accepted add_to_file helper 9 -/
lemma graded_proj_mul_left_of_mem_zero
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {a b : T} (ha : a ∈ 𝒯 0) (i : ℕ) :
    GradedAlgebra.proj 𝒯 i (a * b) =
      a * GradedAlgebra.proj 𝒯 i b := by
  classical
  rw [GradedAlgebra.proj_apply, GradedAlgebra.proj_apply,
    DirectSum.coe_decompose_mul_of_left_mem_zero 𝒯 ha]

lemma graded_proj_mul_right_of_mem_zero
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {a b : T} (hb : b ∈ 𝒯 0) (i : ℕ) :
    GradedAlgebra.proj 𝒯 i (a * b) =
      GradedAlgebra.proj 𝒯 i a * b := by
  classical
  rw [GradedAlgebra.proj_apply, GradedAlgebra.proj_apply,
    DirectSum.coe_decompose_mul_of_right_mem_zero 𝒯 hb]

lemma graded_iSup_fin_two_mul_mem_zero
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {a d b : T} (ha : a ∈ 𝒯 0) (hb : b ∈ 𝒯 0)
    (hd : d ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ)) :
    a * d * b ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ) := by
  classical
  apply graded_mem_iSup_fin_of_proj_eq_zero 𝒯 (n := 2)
  intro m hm
  rw [graded_proj_mul_right_of_mem_zero 𝒯 hb,
    graded_proj_mul_left_of_mem_zero 𝒯 ha,
    graded_proj_eq_zero_of_mem_iSup_fin 𝒯 hm hd]
  simp

/- accepted add_to_file helper 10 -/
lemma graded_homogeneous_mem_span_degree_two_eq_zero_of_lt
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (S : Set T) (hS : S ⊆ 𝒯 2)
    {n : ℕ} (hn : n < 2) {x : T}
    (hxn : x ∈ 𝒯 n)
    (hx : x ∈ TwoSidedIdeal.span S) :
    x = 0 := by
  classical
  have hd : (DirectSum.decompose 𝒯 x) n = 0 :=
    graded_span_degree_two_low_components 𝒯 S hS hx n hn
  have hp : GradedAlgebra.proj 𝒯 n x = 0 := by
    rw [GradedAlgebra.proj_apply, hd]
    rfl
  rwa [graded_proj_self 𝒯 hxn] at hp

lemma graded_sub_proj_one_mem_iSup_fin_one
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {x : T} (hx : x ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ)) :
    x - GradedAlgebra.proj 𝒯 1 x ∈ ⨆ i : Fin 1, 𝒯 (i : ℕ) := by
  classical
  apply graded_mem_iSup_fin_of_proj_eq_zero 𝒯 (n := 1)
  intro m hm
  by_cases h1 : m = 1
  · subst h1
    rw [map_sub, graded_proj_self 𝒯 (n := 1)
      (x := GradedAlgebra.proj 𝒯 1 x) (graded_proj_mem 𝒯 1 x)]
    simp
  · have hm2 : 2 ≤ m := by omega
    have hxm : GradedAlgebra.proj 𝒯 m x = 0 :=
      graded_proj_eq_zero_of_mem_iSup_fin 𝒯 hm2 hx
    have hpm : GradedAlgebra.proj 𝒯 m (GradedAlgebra.proj 𝒯 1 x) = 0 := by
      rw [graded_proj_eq_of_mem 𝒯 (graded_proj_mem 𝒯 1 x)]
      have h1' : 1 ≠ m := fun h => h1 h.symm
      simp [h1']
    rw [map_sub, hxm, hpm, sub_zero]

lemma graded_mem_iSup_fin_one
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    {x : T} (hx : x ∈ ⨆ i : Fin 1, 𝒯 (i : ℕ)) :
    x ∈ 𝒯 0 := by
  rw [Submodule.mem_iSup] at hx
  apply hx (𝒯 0)
  intro i
  have hi : i = 0 := by omega
  subst hi
  exact le_rfl

/- accepted add_to_file helper 11 -/
lemma pbw_low_ideal_eq_zero
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (P : Set T) (I : TwoSidedIdeal T)
    (hPI : TwoSidedIdeal.span P = I)
    (hPpbw : ∀ (n : ℕ) (x : T), x ∈ 𝒯 n →
      (x ∈ TwoSidedIdeal.span ((GradedAlgebra.proj 𝒯 2) '' P) ↔
        ∃ y ∈ I, x - y ∈ (⨆ i : Fin n, 𝒯 (i : ℕ))))
    {z : T} (hzI : z ∈ I)
    (hzF : z ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ)) :
    z = 0 := by
  classical
  let J : TwoSidedIdeal T :=
    TwoSidedIdeal.span ((GradedAlgebra.proj 𝒯 2) '' P)
  have hJhom : ((GradedAlgebra.proj 𝒯 2) '' P : Set T) ⊆ 𝒯 2 := by
    rintro x ⟨p, hp, rfl⟩
    exact graded_proj_mem 𝒯 2 p
  have hz₁ : GradedAlgebra.proj 𝒯 1 z = 0 := by
    have hz₁mem : GradedAlgebra.proj 𝒯 1 z ∈ 𝒯 1 :=
      graded_proj_mem 𝒯 1 z
    have hsub : z - GradedAlgebra.proj 𝒯 1 z ∈ ⨆ i : Fin 1, 𝒯 (i : ℕ) :=
      graded_sub_proj_one_mem_iSup_fin_one 𝒯 hzF
    have hdiff : GradedAlgebra.proj 𝒯 1 z - z ∈ ⨆ i : Fin 1, 𝒯 (i : ℕ) := by
      have hneg := (⨆ i : Fin 1, 𝒯 (i : ℕ)).neg_mem hsub
      convert hneg using 1
      abel
    have hz₁J : GradedAlgebra.proj 𝒯 1 z ∈ J := by
      exact (hPpbw 1 (GradedAlgebra.proj 𝒯 1 z) hz₁mem).2 ⟨z, hzI, hdiff⟩
    exact graded_homogeneous_mem_span_degree_two_eq_zero_of_lt 𝒯
      ((GradedAlgebra.proj 𝒯 2) '' P) hJhom (by norm_num : 1 < 2)
      hz₁mem hz₁J
  have hzF₁ : z ∈ ⨆ i : Fin 1, 𝒯 (i : ℕ) := by
    have hsub : z - GradedAlgebra.proj 𝒯 1 z ∈ ⨆ i : Fin 1, 𝒯 (i : ℕ) :=
      graded_sub_proj_one_mem_iSup_fin_one 𝒯 hzF
    simpa [hz₁] using hsub
  have hz₀ : z ∈ 𝒯 0 := graded_mem_iSup_fin_one 𝒯 hzF₁
  have hzJ : z ∈ J := by
    exact (hPpbw 0 z hz₀).2 ⟨z, hzI, by simp⟩
  exact graded_homogeneous_mem_span_degree_two_eq_zero_of_lt 𝒯
    ((GradedAlgebra.proj 𝒯 2) '' P) hJhom (by norm_num : 0 < 2)
    hz₀ hzJ

/- accepted add_to_file helper 12 -/
lemma tzero_bimodule_closure_subset_ideal
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (S : Set T) (I : TwoSidedIdeal T) (hS : S ⊆ I)
    {x : T}
    (hx : x ∈ AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ s ∈ S, ∃ b ∈ 𝒯 0, x = a * s * b}) :
    x ∈ I := by
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
      rcases hx with ⟨a, ha, s, hs, b, hb, rfl⟩
      exact TwoSidedIdeal.mul_mem_right I (a * s) b
        (TwoSidedIdeal.mul_mem_left I a s (hS hs))
  | zero =>
      exact TwoSidedIdeal.zero_mem I
  | add x y hx hy ihx ihy =>
      exact TwoSidedIdeal.add_mem I ihx ihy
  | neg x hx ihx =>
      exact TwoSidedIdeal.neg_mem I ihx

/- accepted add_to_file helper 13 -/
lemma degree_two_generator_closure_approx
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (Q : Set T)
    (hQ₂ : Q ⊆ (⨆ i : Fin 3, 𝒯 (i : ℕ)))
    {x : T}
    (hx : x ∈ AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ ((GradedAlgebra.proj 𝒯 2) '' Q),
        ∃ b ∈ 𝒯 0, x = a * q * b}) :
    ∃ y ∈ AddSubgroup.closure
        {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b},
      x - y ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ) := by
  classical
  let B : AddSubgroup T := AddSubgroup.closure
    {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b}
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
      rcases hx with ⟨a, ha, r, hr, b, hb, rfl⟩
      rcases hr with ⟨q, hq, rfl⟩
      refine ⟨a * q * b, ?_, ?_⟩
      · apply AddSubgroup.subset_closure
        exact ⟨a, ha, q, hq, b, hb, rfl⟩
      · have hlow : GradedAlgebra.proj 𝒯 2 q - q ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ) := by
          have hqF : q ∈ ⨆ i : Fin 3, 𝒯 (i : ℕ) := by
            have hqFset := hQ₂ hq
            rw [Set.iSup_eq_iUnion] at hqFset
            rw [Set.mem_iUnion] at hqFset
            rcases hqFset with ⟨i, hqi⟩
            exact le_iSup (fun j : Fin 3 => 𝒯 (j : ℕ)) i hqi
          have h := graded_sub_proj_two_mem_iSup_fin_two 𝒯 hqF
          have hneg := (⨆ i : Fin 2, 𝒯 (i : ℕ)).neg_mem h
          convert hneg using 1
          abel
        have := graded_iSup_fin_two_mul_mem_zero 𝒯 ha hb hlow
        convert this using 1
        rw [mul_sub, sub_mul]
  | zero =>
      exact ⟨0, B.zero_mem, by simp⟩
  | add x y hx hy ihx ihy =>
      rcases ihx with ⟨x', hx'B, hxx'⟩
      rcases ihy with ⟨y', hy'B, hyy'⟩
      refine ⟨x' + y', B.add_mem hx'B hy'B, ?_⟩
      have hsum := (⨆ i : Fin 2, 𝒯 (i : ℕ)).add_mem hxx' hyy'
      convert hsum using 1
      abel
  | neg x hx ihx =>
      rcases ihx with ⟨x', hx'B, hxx'⟩
      refine ⟨-x', B.neg_mem hx'B, ?_⟩
      have hneg := (⨆ i : Fin 2, 𝒯 (i : ℕ)).neg_mem hxx'
      convert hneg using 1
      abel

/- accepted add_to_file helper 14 -/
lemma pbw_generators_subset_tzero_bimodule_closure
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (P Q : Set T) (I : TwoSidedIdeal T)
    (hP₂ : P ⊆ (⨆ i : Fin 3, 𝒯 (i : ℕ)))
    (hQ₂ : Q ⊆ (⨆ i : Fin 3, 𝒯 (i : ℕ)))
    (hPI : TwoSidedIdeal.span P = I)
    (hQI : TwoSidedIdeal.span Q = I)
    (hPpbw : ∀ (n : ℕ) (x : T), x ∈ 𝒯 n →
      (x ∈ TwoSidedIdeal.span ((GradedAlgebra.proj 𝒯 2) '' P) ↔
        ∃ y ∈ I, x - y ∈ (⨆ i : Fin n, 𝒯 (i : ℕ))))
    (hQpbw : ∀ (n : ℕ) (x : T), x ∈ 𝒯 n →
      (x ∈ TwoSidedIdeal.span ((GradedAlgebra.proj 𝒯 2) '' Q) ↔
        ∃ y ∈ I, x - y ∈ (⨆ i : Fin n, 𝒯 (i : ℕ)))) :
    P ⊆ AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b} := by
  classical
  intro p hp
  have hpFset := hP₂ hp
  have hpF : p ∈ ⨆ i : Fin 3, 𝒯 (i : ℕ) := by
    rw [Set.iSup_eq_iUnion] at hpFset
    rw [Set.mem_iUnion] at hpFset
    rcases hpFset with ⟨i, hpi⟩
    exact le_iSup (fun j : Fin 3 => 𝒯 (j : ℕ)) i hpi
  have hpI : p ∈ I := by
    have h : p ∈ TwoSidedIdeal.span P := TwoSidedIdeal.subset_span hp
    rwa [hPI] at h
  have hp₂mem : GradedAlgebra.proj 𝒯 2 p ∈ 𝒯 2 :=
    graded_proj_mem 𝒯 2 p
  have hp₂diff : GradedAlgebra.proj 𝒯 2 p - p ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ) := by
    have h := graded_sub_proj_two_mem_iSup_fin_two 𝒯 hpF
    have hneg := (⨆ i : Fin 2, 𝒯 (i : ℕ)).neg_mem h
    convert hneg using 1
    abel
  have hp₂J : GradedAlgebra.proj 𝒯 2 p ∈
      TwoSidedIdeal.span ((GradedAlgebra.proj 𝒯 2) '' Q) := by
    exact (hQpbw 2 (GradedAlgebra.proj 𝒯 2 p) hp₂mem).2 ⟨p, hpI, hp₂diff⟩
  have hQhom : ((GradedAlgebra.proj 𝒯 2) '' Q : Set T) ⊆ 𝒯 2 := by
    rintro x ⟨q, hq, rfl⟩
    exact graded_proj_mem 𝒯 2 q
  have hp₂C : GradedAlgebra.proj 𝒯 2 p ∈ AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ ((GradedAlgebra.proj 𝒯 2) '' Q),
        ∃ b ∈ 𝒯 0, x = a * q * b} := by
    exact graded_degree_two_mem_span_of_degree_two_generators 𝒯
      ((GradedAlgebra.proj 𝒯 2) '' Q) hQhom hp₂mem hp₂J
  rcases degree_two_generator_closure_approx 𝒯 Q hQ₂ hp₂C with
    ⟨y, hyB, hp₂y⟩
  have hpyF : p - y ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ) := by
    have hpminus : p - GradedAlgebra.proj 𝒯 2 p ∈ ⨆ i : Fin 2, 𝒯 (i : ℕ) :=
      graded_sub_proj_two_mem_iSup_fin_two 𝒯 hpF
    have hsum := (⨆ i : Fin 2, 𝒯 (i : ℕ)).add_mem hpminus hp₂y
    convert hsum using 1
    abel
  have hQIset : Q ⊆ I := by
    intro q hq
    have h : q ∈ TwoSidedIdeal.span Q := TwoSidedIdeal.subset_span hq
    rwa [hQI] at h
  have hyI : y ∈ I :=
    tzero_bimodule_closure_subset_ideal 𝒯 Q I hQIset hyB
  have hpyI : p - y ∈ I := TwoSidedIdeal.sub_mem I hpI hyI
  have hpy : p - y = 0 := pbw_low_ideal_eq_zero 𝒯 P I hPI hPpbw hpyI hpyF
  have hp_eq : p = y := sub_eq_zero.mp hpy
  rwa [hp_eq]

/- accepted add_to_file helper 15 -/
lemma tzero_bimodule_closure_mul_mem_zero
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (S : Set T) {a x b : T} (ha : a ∈ 𝒯 0) (hb : b ∈ 𝒯 0)
    (hx : x ∈ AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ s ∈ S, ∃ b ∈ 𝒯 0, x = a * s * b}) :
    a * x * b ∈ AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ s ∈ S, ∃ b ∈ 𝒯 0, x = a * s * b} := by
  let C : AddSubgroup T := AddSubgroup.closure
    {x : T | ∃ a ∈ 𝒯 0, ∃ s ∈ S, ∃ b ∈ 𝒯 0, x = a * s * b}
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
      rcases hx with ⟨u, hu, s, hs, v, hv, rfl⟩
      apply AddSubgroup.subset_closure
      refine ⟨a * u, ?_, s, hs, v * b, ?_, ?_⟩
      · exact SetLike.mul_mem_graded ha hu
      · exact SetLike.mul_mem_graded hv hb
      · simp [mul_assoc]
  | zero =>
      simp
  | add x y hx hy ihx ihy =>
      rw [mul_add, add_mul]
      exact C.add_mem ihx ihy
  | neg x hx ihx =>
      rw [mul_neg, neg_mul]
      exact C.neg_mem ihx

lemma tzero_bimodule_closure_le_of_generators_subset
    {k T : Type*} [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (P Q : Set T)
    (h : P ⊆ AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b}) :
    AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ p ∈ P, ∃ b ∈ 𝒯 0, x = a * p * b} ≤
    AddSubgroup.closure
      {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b} := by
  rw [AddSubgroup.closure_le]
  intro x hx
  rcases hx with ⟨a, ha, p, hp, b, hb, rfl⟩
  exact tzero_bimodule_closure_mul_mem_zero 𝒯 Q ha hb (h hp)

/- verified submission -/
theorem pbw_filtered_quadratic_relations_unique
    (k T : Type*) [Field k] [Ring T] [Algebra k T]
    (𝒯 : ℕ → Submodule k T) [GradedAlgebra 𝒯]
    (P Q : Set T) (I : TwoSidedIdeal T)
    (hP₂ : P ⊆ (⨆ i : Fin 3, 𝒯 (i : ℕ)))
    (hQ₂ : Q ⊆ (⨆ i : Fin 3, 𝒯 (i : ℕ)))
    (hPI : TwoSidedIdeal.span P = I)
    (hQI : TwoSidedIdeal.span Q = I)
    (hPpbw : ∀ (n : ℕ) (x : T), x ∈ 𝒯 n →
      (x ∈ TwoSidedIdeal.span ((GradedAlgebra.proj 𝒯 2) '' P) ↔
        ∃ y ∈ I, x - y ∈ (⨆ i : Fin n, 𝒯 (i : ℕ))))
    (hQpbw : ∀ (n : ℕ) (x : T), x ∈ 𝒯 n →
      (x ∈ TwoSidedIdeal.span ((GradedAlgebra.proj 𝒯 2) '' Q) ↔
        ∃ y ∈ I, x - y ∈ (⨆ i : Fin n, 𝒯 (i : ℕ)))) :
    AddSubgroup.closure {x : T | ∃ a ∈ 𝒯 0, ∃ p ∈ P, ∃ b ∈ 𝒯 0, x = a * p * b} =
        AddSubgroup.closure {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b} ∧
      (((∃ M : AddSubgroup T, (M : Set T) = P ∧
          (∀ (a : 𝒯 0) (x : T), x ∈ M → (a : T) * x ∈ M) ∧
          (∀ (a : 𝒯 0) (x : T), x ∈ M → x * (a : T) ∈ M)) ∧
        (∃ N : AddSubgroup T, (N : Set T) = Q ∧
          (∀ (a : 𝒯 0) (x : T), x ∈ N → (a : T) * x ∈ N) ∧
          (∀ (a : 𝒯 0) (x : T), x ∈ N → x * (a : T) ∈ N))) → P = Q) := by
  classical
  let A : AddSubgroup T := AddSubgroup.closure
    {x : T | ∃ a ∈ 𝒯 0, ∃ p ∈ P, ∃ b ∈ 𝒯 0, x = a * p * b}
  let B : AddSubgroup T := AddSubgroup.closure
    {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b}
  have hPsub : P ⊆ B := by
    simpa [B] using pbw_generators_subset_tzero_bimodule_closure
      𝒯 P Q I hP₂ hQ₂ hPI hQI hPpbw hQpbw
  have hQsub : Q ⊆ A := by
    simpa [A] using pbw_generators_subset_tzero_bimodule_closure
      𝒯 Q P I hQ₂ hP₂ hQI hPI hQpbw hPpbw
  have hAleB : A ≤ B := by
    simpa [A, B] using tzero_bimodule_closure_le_of_generators_subset 𝒯 P Q hPsub
  have hBleA : B ≤ A := by
    simpa [A, B] using tzero_bimodule_closure_le_of_generators_subset 𝒯 Q P hQsub
  have hAB : A = B := le_antisymm hAleB hBleA
  constructor
  · simpa [A, B] using hAB
  · intro hclosed
    rcases hclosed with ⟨hPclosed, hQclosed⟩
    rcases hPclosed with ⟨M, hMP, hMleft, hMright⟩
    rcases hQclosed with ⟨N, hNQ, hNleft, hNright⟩
    have hgenP : {x : T | ∃ a ∈ 𝒯 0, ∃ p ∈ P, ∃ b ∈ 𝒯 0, x = a * p * b} ⊆
        (M : Set T) := by
      intro x hx
      rcases hx with ⟨a, ha, p, hp, b, hb, rfl⟩
      have hpM : p ∈ M := by
        have hpMset : p ∈ (M : Set T) := by
          rw [hMP]
          exact hp
        exact hpMset
      exact hMright ⟨b, hb⟩ ((a : T) * p)
        (hMleft ⟨a, ha⟩ p hpM)
    have hAleM : A ≤ M := by
      have h : AddSubgroup.closure
          {x : T | ∃ a ∈ 𝒯 0, ∃ p ∈ P, ∃ b ∈ 𝒯 0, x = a * p * b} ≤ M :=
        (AddSubgroup.closure_le M).2 hgenP
      simpa [A] using h
    have hMleA : M ≤ A := by
      intro x hx
      have hxP : x ∈ P := by
        have hxset : x ∈ (M : Set T) := hx
        rw [hMP] at hxset
        exact hxset
      apply AddSubgroup.subset_closure
      exact ⟨1, SetLike.GradedOne.one_mem, x, hxP, 1,
        SetLike.GradedOne.one_mem, by simp⟩
    have hAM : A = M := le_antisymm hAleM hMleA
    have hgenQ : {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b} ⊆
        (N : Set T) := by
      intro x hx
      rcases hx with ⟨a, ha, q, hq, b, hb, rfl⟩
      have hqN : q ∈ N := by
        have hqNset : q ∈ (N : Set T) := by
          rw [hNQ]
          exact hq
        exact hqNset
      exact hNright ⟨b, hb⟩ ((a : T) * q)
        (hNleft ⟨a, ha⟩ q hqN)
    have hBleN : B ≤ N := by
      have h : AddSubgroup.closure
          {x : T | ∃ a ∈ 𝒯 0, ∃ q ∈ Q, ∃ b ∈ 𝒯 0, x = a * q * b} ≤ N :=
        (AddSubgroup.closure_le N).2 hgenQ
      simpa [B] using h
    have hNleB : N ≤ B := by
      intro x hx
      have hxQ : x ∈ Q := by
        have hxset : x ∈ (N : Set T) := hx
        rw [hNQ] at hxset
        exact hxset
      apply AddSubgroup.subset_closure
      exact ⟨1, SetLike.GradedOne.one_mem, x, hxQ, 1,
        SetLike.GradedOne.one_mem, by simp⟩
    have hBN : B = N := le_antisymm hBleN hNleB
    have hPAsets : P = (A : Set T) := by
      calc
        P = (M : Set T) := hMP.symm
        _ = (A : Set T) := congrArg (fun X : AddSubgroup T => (X : Set T)) hAM.symm
    have hQBsets : Q = (B : Set T) := by
      calc
        Q = (N : Set T) := hNQ.symm
        _ = (B : Set T) := congrArg (fun X : AddSubgroup T => (X : Set T)) hBN.symm
    calc
      P = (A : Set T) := hPAsets
      _ = (B : Set T) := congrArg (fun X : AddSubgroup T => (X : Set T)) hAB
      _ = Q := hQBsets.symm

end Rollout_p2771_pbw_filtered_quadratic_relations_unique

namespace Rollout_p3255_horseshoelikepenalty_strictconcave

/- accepted add_to_file helper 1 -/

open Set Real Filter

lemma h_hasDerivAt {a x : ℝ} (ha : 0 < a) (hx : x ≠ 0) :
    HasDerivAt (fun x => Real.log (1 + a / x ^ 2))
      (-2 * a / (x * (x ^ 2 + a))) x := by
  have hsq : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hdiv : HasDerivAt (fun x : ℝ => a / x ^ 2)
      ((0 * x ^ 2 - a * (2 * x)) / (x ^ 2) ^ 2) x := by
    exact (hasDerivAt_const x a).div hsq (pow_ne_zero 2 hx)
  have harg : HasDerivAt (fun x : ℝ => 1 + a / x ^ 2)
      (0 + (0 * x ^ 2 - a * (2 * x)) / (x ^ 2) ^ 2) x := by
    exact (hasDerivAt_const x 1).add hdiv
  have hne : (1 + a / x ^ 2) ≠ 0 := by
    positivity
  have hlog := harg.log hne
  convert hlog using 1
  field_simp [hx, ha.ne']
  ring

lemma h_deriv2_hasDerivAt {a x : ℝ} (ha : 0 < a) (hx : x ≠ 0) :
    HasDerivAt (fun x => -2 * a / (x * (x ^ 2 + a)))
      (2 * a * (3 * x ^ 2 + a) / (x ^ 2 * (x ^ 2 + a) ^ 2)) x := by
  have hinner : HasDerivAt (fun x : ℝ => x ^ 2 + a) (2 * x) x := by
    convert ((hasDerivAt_pow 2 x).add (hasDerivAt_const x a)) using 1
    ring
  have hd : HasDerivAt (fun x : ℝ => x * (x ^ 2 + a))
      (1 * (x ^ 2 + a) + x * (2 * x)) x := by
    exact (hasDerivAt_id x).mul hinner
  have hden : x * (x ^ 2 + a) ≠ 0 := by
    positivity
  have hdiv := (hasDerivAt_const x (-2 * a)).div hd hden
  convert hdiv using 1
  field_simp [hx, ha.ne']
  ring

/- accepted add_to_file helper 2 -/
lemma pen_hasDerivAt {a x : ℝ} (ha : 0 < a) (hx : x ≠ 0) :
    HasDerivAt (fun x => -Real.log (Real.log (1 + a / x ^ 2)))
      (2 * a / (x * (x ^ 2 + a) * Real.log (1 + a / x ^ 2))) x := by
  have hh := h_hasDerivAt ha hx
  have hpos : 0 < Real.log (1 + a / x ^ 2) := by
    apply Real.log_pos
    have hq : 0 < a / x ^ 2 := by positivity
    linarith
  have hlog := hh.log (ne_of_gt hpos)
  have hneg := hlog.neg
  convert hneg using 1
  field_simp [hx, ha.ne', ne_of_gt hpos]

/- accepted add_to_file helper 3 -/
lemma pen_deriv2_hasDerivAt {a x : ℝ} (ha : 0 < a) (hx : x ≠ 0) :
    HasDerivAt
      (fun x => 2 * a / (x * (x ^ 2 + a) * Real.log (1 + a / x ^ 2)))
      (-2 * a * ((3 * x ^ 2 + a) * Real.log (1 + a / x ^ 2) - 2 * a) /
        ((x * (x ^ 2 + a)) ^ 2 * (Real.log (1 + a / x ^ 2)) ^ 2)) x := by
  have hinner : HasDerivAt (fun x : ℝ => x ^ 2 + a) (2 * x) x := by
    convert ((hasDerivAt_pow 2 x).add (hasDerivAt_const x a)) using 1
    ring
  have hD : HasDerivAt (fun x : ℝ => x * (x ^ 2 + a))
      (1 * (x ^ 2 + a) + x * (2 * x)) x := by
    exact (hasDerivAt_id x).mul hinner
  have hH := h_hasDerivAt ha hx
  have hden : HasDerivAt
      (fun x : ℝ => x * (x ^ 2 + a) * Real.log (1 + a / x ^ 2))
      ((1 * (x ^ 2 + a) + x * (2 * x)) * Real.log (1 + a / x ^ 2) +
        x * (x ^ 2 + a) * (-2 * a / (x * (x ^ 2 + a)))) x := by
    exact hD.mul hH
  have hHpos : 0 < Real.log (1 + a / x ^ 2) := by
    apply Real.log_pos
    have hq : 0 < a / x ^ 2 := by positivity
    linarith
  have hDne : x * (x ^ 2 + a) ≠ 0 := by positivity
  have hdenne : x * (x ^ 2 + a) * Real.log (1 + a / x ^ 2) ≠ 0 :=
    mul_ne_zero hDne (ne_of_gt hHpos)
  have hdiv := (hasDerivAt_const x (2 * a)).div hden hdenne
  convert hdiv using 1
  field_simp [hx, ha.ne', ne_of_gt hHpos, hDne]
  ring

/- accepted add_to_file helper 4 -/
lemma pen_second_factor_pos {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    0 < (3 * x ^ 2 + a) * Real.log (1 + a / x ^ 2) - 2 * a := by
  let r : ℝ := a / x ^ 2
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hlog : 2 * r / (r + 2) < Real.log (1 + r) := Real.lt_log_one_add_of_pos hr
  have hfrac : 2 * r / (r + 3) < 2 * r / (r + 2) := by
    have hnum : 0 < 2 * r := by positivity
    have hd23 : 0 < r + 2 := by positivity
    have hdle : r + 2 < r + 3 := by linarith
    exact div_lt_div_of_pos_left hnum hd23 hdle
  have hlow : 2 * r / (r + 3) < Real.log (1 + r) := lt_trans hfrac hlog
  have hlow' : 2 * r < (r + 3) * Real.log (1 + r) := by
    rw [mul_comm (r + 3)]
    exact (div_lt_iff₀ (by positivity : 0 < r + 3)).mp hlow
  have hx2 : 0 < x ^ 2 := sq_pos_of_pos hx
  have hmul : 0 < x ^ 2 * ((r + 3) * Real.log (1 + r) - 2 * r) :=
    mul_pos hx2 (sub_pos.mpr hlow')
  have hreq : x ^ 2 * ((r + 3) * Real.log (1 + r) - 2 * r) =
      (3 * x ^ 2 + a) * Real.log (1 + a / x ^ 2) - 2 * a := by
    dsimp [r]
    field_simp [ne_of_gt hx]
    ring
  rwa [hreq] at hmul

/- accepted add_to_file helper 5 -/
lemma pen_strictConcaveOn_pos {a : ℝ} (ha : 0 < a) :
    StrictConcaveOn ℝ (Ioi 0)
      (fun x => -Real.log (Real.log (1 + a / x ^ 2))) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Ioi 0)
  · intro x hx
    exact (pen_hasDerivAt ha (ne_of_gt hx)).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ioi] at hx
    have hev : (fun y => deriv (fun x => -Real.log (Real.log (1 + a / x ^ 2))) y)
        =ᶠ[nhds x]
        fun y => 2 * a / (y * (y ^ 2 + a) * Real.log (1 + a / y ^ 2)) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact (pen_hasDerivAt ha (ne_of_gt hy)).deriv
    have h2 : deriv (deriv (fun x => -Real.log (Real.log (1 + a / x ^ 2)))) x =
        -2 * a * ((3 * x ^ 2 + a) * Real.log (1 + a / x ^ 2) - 2 * a) /
          ((x * (x ^ 2 + a)) ^ 2 * (Real.log (1 + a / x ^ 2)) ^ 2) := by
      rw [hev.deriv_eq]
      exact (pen_deriv2_hasDerivAt ha (ne_of_gt hx)).deriv
    have hiter : deriv^[2] (fun x => -Real.log (Real.log (1 + a / x ^ 2))) x =
        deriv (deriv (fun x => -Real.log (Real.log (1 + a / x ^ 2)))) x := rfl
    rw [hiter, h2]
    have hfactor := pen_second_factor_pos ha hx
    have hLpos : 0 < Real.log (1 + a / x ^ 2) := by
      apply Real.log_pos
      have hq : 0 < a / x ^ 2 := div_pos ha (sq_pos_of_pos hx)
      linarith
    have hnum : -2 * a *
        ((3 * x ^ 2 + a) * Real.log (1 + a / x ^ 2) - 2 * a) < 0 := by
      have hcoef : -2 * a < 0 := by nlinarith
      exact mul_neg_of_neg_of_pos hcoef hfactor
    have hden : 0 < (x * (x ^ 2 + a)) ^ 2 *
        (Real.log (1 + a / x ^ 2)) ^ 2 := by
      have hD : 0 < x * (x ^ 2 + a) := by
        exact mul_pos hx (add_pos (sq_pos_of_pos hx) ha)
      exact mul_pos (sq_pos_of_pos hD) (sq_pos_of_pos hLpos)
    exact div_neg_of_neg_of_pos hnum hden

/- verified submission -/
theorem horseshoeLikePenalty_strictConcave (a : ℝ) (ha : 0 < a) :
    let pen_a : ℝ → ℝ := fun x => -Real.log (Real.log (1 + a / x ^ 2))
    ∀ x y t : ℝ,
      x ≠ y →
      ((0 < x ∧ 0 < y) ∨ (x < 0 ∧ y < 0)) →
      0 < t →
      t < 1 →
      pen_a (t * x + (1 - t) * y) >
        t * pen_a x + (1 - t) * pen_a y := by
  dsimp
  intro x y t hxy hs ht ht1
  have hsc := pen_strictConcaveOn_pos ha
  have ht' : 0 < 1 - t := sub_pos.mpr ht1
  have hsum : t + (1 - t) = 1 := by ring
  rcases hs with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact hsc.2 hx hy hxy ht ht' hsum
  · let u : ℝ := -x
    let v : ℝ := -y
    have hu : 0 < u := by
      dsimp [u]
      linarith
    have hv : 0 < v := by
      dsimp [v]
      linarith
    have huv : u ≠ v := by
      intro huv_eq
      apply hxy
      dsimp [u, v] at huv_eq
      linarith
    have hmain := hsc.2 hu hv huv ht ht' hsum
    have hcomb : t * u + (1 - t) * v = -(t * x + (1 - t) * y) := by
      dsimp [u, v]
      ring
    have hsqcomb : (-(t * x + (1 - t) * y)) ^ 2 =
        (t * x + (1 - t) * y) ^ 2 := by ring
    have hsqx : (-x) ^ 2 = x ^ 2 := by ring
    have hsqy : (-y) ^ 2 = y ^ 2 := by ring
    dsimp [u, v] at hmain
    rw [hcomb, hsqcomb, hsqx, hsqy] at hmain
    exact hmain

end Rollout_p3255_horseshoelikepenalty_strictconcave

namespace Rollout_p1078_khexpansive_iff_separating_and_isopen_fixe

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

namespace Rollout_p0971_derivwithin_neg_of_positive_solution

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

namespace Rollout_p1874_proposition_4_9

/- accepted add_to_file helper 1 -/
lemma proposition_4_9_ordConnected_abs_sub_le
    (x : Set.Icc (0 : ℝ) 1) (r : ℝ) :
    ({y : Set.Icc (0 : ℝ) 1 | |(x : ℝ) - (y : ℝ)| ≤ r}).OrdConnected := by
  refine Set.OrdConnected.mk ?_
  intro y hy z hz w hw
  change |(x : ℝ) - (y : ℝ)| ≤ r at hy
  change |(x : ℝ) - (z : ℝ)| ≤ r at hz
  have hy' := abs_le.mp hy
  have hz' := abs_le.mp hz
  have hwy : (y : ℝ) ≤ w := hw.1
  have hwz : (w : ℝ) ≤ z := hw.2
  change |(x : ℝ) - (w : ℝ)| ≤ r
  apply abs_le.mpr
  constructor
  · nlinarith
  · nlinarith

lemma proposition_4_9_diam_abs_sub_le
    (x : Set.Icc (0 : ℝ) 1) (n : ℕ) :
    Metric.diam {y : Set.Icc (0 : ℝ) 1 |
      |(x : ℝ) - (y : ℝ)| ≤ (2 : ℝ) ^ (-(n + 1 : ℝ))} ≤
      (2 : ℝ) ^ (-(n : ℝ)) := by
  apply Metric.diam_le_of_forall_dist_le
  · positivity
  · intro y hy z hz
    change |(x : ℝ) - (y : ℝ)| ≤ (2 : ℝ) ^ (-(n + 1 : ℝ)) at hy
    change |(x : ℝ) - (z : ℝ)| ≤ (2 : ℝ) ^ (-(n + 1 : ℝ)) at hz
    calc
      dist y z = |(y : ℝ) - (z : ℝ)| := by
        rw [Subtype.dist_eq, Real.dist_eq]
      _ ≤ |(y : ℝ) - (x : ℝ)| + |(x : ℝ) - (z : ℝ)| := by
        exact abs_sub_le _ _ _
      _ = |(x : ℝ) - (y : ℝ)| + |(x : ℝ) - (z : ℝ)| := by
        rw [abs_sub_comm]
      _ ≤ (2 : ℝ) ^ (-(n + 1 : ℝ)) + (2 : ℝ) ^ (-(n + 1 : ℝ)) :=
        add_le_add hy hz
      _ = (2 : ℝ) ^ (-(n : ℝ)) := by
        rw [← two_mul]
        symm
        rw [show (-(n : ℝ)) = (-(n + 1 : ℝ)) + 1 by ring]
        rw [Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        rw [Real.rpow_one]
        ring

/- accepted add_to_file helper 2 -/
lemma proposition_4_9_ball_le
    (α : ℝ) (f : ℕ → ℕ)
    (μ : MeasureTheory.Measure (Set.Icc (0 : ℝ) 1))
    (hμ : ∀ n : ℕ, ∀ A : Set (Set.Icc (0 : ℝ) 1),
      A.OrdConnected →
      Metric.diam A ≤ Real.rpow 2 (-(n : ℝ)) →
      μ A ≤ ENNReal.ofReal (Real.rpow 2 (-(α * (n : ℝ) + (f n : ℝ)))))
    (x : Set.Icc (0 : ℝ) 1) (n : ℕ) :
    μ {y : Set.Icc (0 : ℝ) 1 |
      |(x : ℝ) - (y : ℝ)| ≤ (2 : ℝ) ^ (-(n + 1 : ℝ))} ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-(α * (n : ℝ) + (f n : ℝ)))) := by
  exact hμ n _ (proposition_4_9_ordConnected_abs_sub_le x _)
    (proposition_4_9_diam_abs_sub_le x n)

/- accepted add_to_file helper 3 -/
lemma proposition_4_9_diam_univ_le_one :
    Metric.diam (Set.univ : Set (Set.Icc (0 : ℝ) 1)) ≤ 1 := by
  apply Metric.diam_le_of_forall_dist_le zero_le_one
  intro x _ y _
  rw [Subtype.dist_eq, Real.dist_eq]
  have hx0 : (0:ℝ) ≤ x := x.property.1
  have hx1 : (x:ℝ) ≤ 1 := x.property.2
  have hy0 : (0:ℝ) ≤ y := y.property.1
  have hy1 : (y:ℝ) ≤ 1 := y.property.2
  apply abs_le.mpr
  constructor <;> nlinarith

/- accepted add_to_file helper 4 -/
lemma proposition_4_9_measure_univ_finite
    (α : ℝ) (f : ℕ → ℕ)
    (μ : MeasureTheory.Measure (Set.Icc (0 : ℝ) 1))
    (hμ : ∀ n : ℕ, ∀ A : Set (Set.Icc (0 : ℝ) 1),
      A.OrdConnected →
      Metric.diam A ≤ Real.rpow 2 (-(n : ℝ)) →
      μ A ≤ ENNReal.ofReal (Real.rpow 2 (-(α * (n : ℝ) + (f n : ℝ))))) :
    μ Set.univ < ⊤ := by
  have hb := hμ 0 Set.univ Set.ordConnected_univ
    (by simpa using proposition_4_9_diam_univ_le_one)
  have hr : Real.rpow (2 : ℝ) (-(α * ((0 : ℕ) : ℝ) + (f 0 : ℝ))) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1:ℝ) ≤ 2)
    have hnonneg : 0 ≤ α * ((0 : ℕ) : ℝ) + (f 0 : ℝ) := by simp
    linarith
  exact lt_of_le_of_lt hb (lt_of_le_of_lt (ENNReal.ofReal_le_one.mpr hr) ENNReal.one_lt_top)

/- accepted add_to_file helper 5 -/
lemma proposition_4_9_measure_singleton_eq_zero
    (α : ℝ) (hα : 0 ≤ α) (f : ℕ → ℕ)
    (hf : Summable (fun n : ℕ => Real.rpow 2 (-(f n : ℝ))))
    (μ : MeasureTheory.Measure (Set.Icc (0 : ℝ) 1))
    (hμ : ∀ n : ℕ, ∀ A : Set (Set.Icc (0 : ℝ) 1),
      A.OrdConnected →
      Metric.diam A ≤ Real.rpow 2 (-(n : ℝ)) →
      μ A ≤ ENNReal.ofReal (Real.rpow 2 (-(α * (n : ℝ) + (f n : ℝ)))))
    (x : Set.Icc (0 : ℝ) 1) :
    μ {x} = 0 := by
  have ht : Filter.Tendsto
      (fun n : ℕ => ENNReal.ofReal (Real.rpow 2 (-(f n : ℝ))))
      Filter.atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hf.tendsto_atTop_zero
  have hbound : ∀ n : ℕ, μ {x} ≤ ENNReal.ofReal (Real.rpow 2 (-(f n : ℝ))) := by
    intro n
    have hs := hμ n {x} Set.ordConnected_singleton (by
      rw [Metric.diam_singleton]
      exact Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)
    have hr : Real.rpow (2 : ℝ) (-(α * (n : ℝ) + (f n : ℝ))) ≤
        Real.rpow (2 : ℝ) (-(f n : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      have hn : (0:ℝ) ≤ n := by positivity
      nlinarith
    exact le_trans hs (ENNReal.ofReal_le_ofReal hr)
  have hle : μ {x} ≤ 0 := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hev := (ENNReal.tendsto_nhds_zero.mp ht) (ε : ENNReal) (by exact_mod_cast hε)
    rcases hev.exists with ⟨n, hn⟩
    exact le_trans (hbound n) (le_trans hn (by simp))
  exact nonpos_iff_eq_zero.mp hle

/- accepted add_to_file helper 6 -/
lemma proposition_4_9_measurable_abs_sub
    (x : Set.Icc (0 : ℝ) 1) :
    Measurable (fun y : Set.Icc (0 : ℝ) 1 => |(x : ℝ) - (y : ℝ)|) := by
  exact (measurable_const.sub measurable_subtype_coe).abs

def proposition_4_9_shell (x : Set.Icc (0 : ℝ) 1) (n : ℕ) :
    Set (Set.Icc (0 : ℝ) 1) :=
  {y | (2 : ℝ) ^ (-(n + 2 : ℝ)) < |(x : ℝ) - (y : ℝ)| ∧
    |(x : ℝ) - (y : ℝ)| ≤ (2 : ℝ) ^ (-(n + 1 : ℝ))}

def proposition_4_9_far (x : Set.Icc (0 : ℝ) 1) :
    Set (Set.Icc (0 : ℝ) 1) :=
  {y | (1 / 2 : ℝ) < |(x : ℝ) - (y : ℝ)|}

lemma proposition_4_9_measurable_shell
    (x : Set.Icc (0 : ℝ) 1) (n : ℕ) :
    MeasurableSet (proposition_4_9_shell x n) := by
  unfold proposition_4_9_shell
  exact (measurableSet_lt measurable_const (proposition_4_9_measurable_abs_sub x)).inter
    (measurableSet_le (proposition_4_9_measurable_abs_sub x) measurable_const)

lemma proposition_4_9_measurable_far
    (x : Set.Icc (0 : ℝ) 1) :
    MeasurableSet (proposition_4_9_far x) := by
  unfold proposition_4_9_far
  exact measurableSet_lt measurable_const (proposition_4_9_measurable_abs_sub x)

/- accepted add_to_file helper 7 -/
lemma proposition_4_9_half_pow (n : ℕ) :
    ((1 / 2 : ℝ) ^ n) = (2 : ℝ) ^ (-(n : ℝ)) := by
  rw [one_div, inv_pow, Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]

lemma proposition_4_9_energy_le_of_dist_ge
    {α d a : ℝ} (hα : 0 ≤ α) (ha : 0 < a) (had : a ≤ d) :
    (1 / ENNReal.ofReal d) ^ α ≤ ENNReal.ofReal ((1 / a) ^ α) := by
  have hd : 0 < d := lt_of_lt_of_le ha had
  have hbase : 1 / ENNReal.ofReal d ≤ ENNReal.ofReal (1 / a) := by
    have hdiv := ENNReal.ofReal_div_of_pos (x := (1 : ℝ)) (y := d) hd
    rw [ENNReal.ofReal_one] at hdiv
    rw [← hdiv]
    exact ENNReal.ofReal_le_ofReal (one_div_le_one_div_of_le ha had)
  calc
    (1 / ENNReal.ofReal d) ^ α ≤ (ENNReal.ofReal (1 / a)) ^ α :=
      ENNReal.rpow_le_rpow hbase hα
    _ = ENNReal.ofReal ((1 / a) ^ α) := by
      rw [ENNReal.ofReal_rpow_of_pos (one_div_pos.2 ha)]

/- accepted add_to_file helper 8 -/
lemma proposition_4_9_abs_sub_le_one
    (x y : Set.Icc (0 : ℝ) 1) :
    |(x : ℝ) - (y : ℝ)| ≤ 1 := by
  have hx0 : (0:ℝ) ≤ x := x.property.1
  have hx1 : (x:ℝ) ≤ 1 := x.property.2
  have hy0 : (0:ℝ) ≤ y := y.property.1
  have hy1 : (y:ℝ) ≤ 1 := y.property.2
  apply abs_le.mpr
  constructor <;> nlinarith

/- accepted add_to_file helper 9 -/
lemma proposition_4_9_energy_pointwise_le
    {α : ℝ} (hα : 0 ≤ α)
    (x y : Set.Icc (0 : ℝ) 1) (hxy : y ≠ x) :
    (1 / ENNReal.ofReal |(x : ℝ) - (y : ℝ)|) ^ α ≤
      ENNReal.ofReal ((2 : ℝ) ^ α) *
          (proposition_4_9_far x).indicator (fun _ => (1 : ENNReal)) y +
        ∑' n : ℕ,
          ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) ^ α) *
            (proposition_4_9_shell x n).indicator (fun _ => (1 : ENNReal)) y := by
  by_cases hfar : y ∈ proposition_4_9_far x
  · have hd : (1 / 2 : ℝ) ≤ |(x : ℝ) - (y : ℝ)| := le_of_lt hfar
    have hE := proposition_4_9_energy_le_of_dist_ge hα (by norm_num : (0:ℝ) < 1 / 2) hd
    have h2 : ((1 / (1 / 2 : ℝ)) ^ α) = (2 : ℝ) ^ α := by norm_num
    rw [h2] at hE
    calc
      (1 / ENNReal.ofReal |(x : ℝ) - (y : ℝ)|) ^ α ≤ ENNReal.ofReal ((2 : ℝ) ^ α) := hE
      _ = ENNReal.ofReal ((2 : ℝ) ^ α) *
          (proposition_4_9_far x).indicator (fun _ => (1 : ENNReal)) y := by
        simp [hfar]
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ α) *
            (proposition_4_9_far x).indicator (fun _ => (1 : ENNReal)) y +
          ∑' n : ℕ,
            ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) ^ α) *
              (proposition_4_9_shell x n).indicator (fun _ => (1 : ENNReal)) y :=
        le_add_of_nonneg_right (zero_le _)
  · have hdle_half : |(x : ℝ) - (y : ℝ)| ≤ 1 / 2 := by
      exact le_of_not_gt hfar
    have hcoord : (x : ℝ) ≠ y := by
      intro h
      apply hxy
      exact Subtype.ext h.symm
    have hdpos : 0 < |(x : ℝ) - (y : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr hcoord)
    rcases exists_nat_pow_near_of_lt_one hdpos (proposition_4_9_abs_sub_le_one x y)
        (by norm_num : (0:ℝ) < 1 / 2) (by norm_num : (1:ℝ) / 2 < 1) with
      ⟨m, hm_lower, hm_upper⟩
    have hm_ne : m ≠ 0 := by
      intro hm0
      subst m
      rw [pow_zero] at hm_upper
      rw [pow_one] at hm_lower
      exact hfar (by exact hm_lower)
    rcases Nat.exists_eq_succ_of_ne_zero hm_ne with ⟨n, rfl⟩
    have hm_lower' : ((1 / 2 : ℝ) ^ (n + 2)) < |(x : ℝ) - (y : ℝ)| := by
      simpa [Nat.succ_eq_add_one, add_assoc] using hm_lower
    have hm_upper' : |(x : ℝ) - (y : ℝ)| ≤ ((1 / 2 : ℝ) ^ (n + 1)) := by
      simpa [Nat.succ_eq_add_one] using hm_upper
    have hshell : y ∈ proposition_4_9_shell x n := by
      constructor
      · have h := hm_lower'
        rw [proposition_4_9_half_pow (n + 2)] at h
        convert h using 2
        norm_num [Nat.cast_add]
      · have h := hm_upper'
        rw [proposition_4_9_half_pow (n + 1)] at h
        convert h using 2
        norm_num [Nat.cast_add]
    have hE := proposition_4_9_energy_le_of_dist_ge hα
      (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _) hshell.1.le
    have hterm :
        ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) ^ α) ≤
          ∑' k : ℕ,
            ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(k + 2 : ℝ)))) ^ α) *
              (proposition_4_9_shell x k).indicator (fun _ => (1 : ENNReal)) y := by
      convert ENNReal.le_tsum (f := fun k : ℕ =>
          ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(k + 2 : ℝ)))) ^ α) *
            (proposition_4_9_shell x k).indicator (fun _ => (1 : ENNReal)) y) n using 2
      simp [hshell]
    calc
      (1 / ENNReal.ofReal |(x : ℝ) - (y : ℝ)|) ^ α ≤
          ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) ^ α) := hE
      _ ≤ ∑' k : ℕ,
            ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(k + 2 : ℝ)))) ^ α) *
              (proposition_4_9_shell x k).indicator (fun _ => (1 : ENNReal)) y := hterm
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ α) *
            (proposition_4_9_far x).indicator (fun _ => (1 : ENNReal)) y +
          ∑' k : ℕ,
            ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(k + 2 : ℝ)))) ^ α) *
              (proposition_4_9_shell x k).indicator (fun _ => (1 : ENNReal)) y :=
        le_add_of_nonneg_left (zero_le _)

/- accepted add_to_file helper 10 -/
lemma proposition_4_9_shell_weight_mul
    (α : ℝ) (f : ℕ → ℕ) (n : ℕ) :
    ((1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) ^ α) *
        (2 : ℝ) ^ (-(α * (n : ℝ) + (f n : ℝ))) =
      (2 : ℝ) ^ (2 * α) * (2 : ℝ) ^ (-(f n : ℝ)) := by
  have hA : (1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) ^ α =
      (2 : ℝ) ^ (α * ((n : ℝ) + 2)) := by
    have hbase : 1 / ((2 : ℝ) ^ (-(n + 2 : ℝ))) = (2 : ℝ) ^ ((n : ℝ) + 2) := by
      rw [one_div, ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
      ring_nf
    rw [hbase]
    rw [← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    ring_nf
  rw [hA]
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  congr 1
  ring

/- accepted add_to_file helper 11 -/
lemma proposition_4_9_shell_bound_eq
    (α : ℝ) (f : ℕ → ℕ) (n : ℕ) :
    ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) ^ α) *
        ENNReal.ofReal ((2 : ℝ) ^ (-(α * (n : ℝ) + (f n : ℝ)))) =
      ENNReal.ofReal ((2 : ℝ) ^ (2 * α)) *
        ENNReal.ofReal ((2 : ℝ) ^ (-(f n : ℝ))) := by
  rw [← ENNReal.ofReal_mul
    (p := (1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) ^ α)
    (Real.rpow_nonneg (by positivity : 0 ≤ 1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) _)]
  rw [proposition_4_9_shell_weight_mul]
  rw [ENNReal.ofReal_mul (p := (2 : ℝ) ^ (2 * α))
    (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _)]

/- accepted add_to_file helper 12 -/
lemma proposition_4_9_energy_le_of_dist_ge'
    {α d a : ℝ} (hα : 0 ≤ α) (ha : 0 < a) (had : a ≤ d) :
    1 / (ENNReal.ofReal d) ^ α ≤ ENNReal.ofReal ((1 / a) ^ α) := by
  simpa [ENNReal.inv_rpow] using
    (proposition_4_9_energy_le_of_dist_ge hα ha had)

/- accepted add_to_file helper 13 -/
lemma proposition_4_9_energy_pointwise_le'
    {α : ℝ} (hα : 0 ≤ α)
    (x y : Set.Icc (0 : ℝ) 1) (hxy : y ≠ x) :
    1 / (ENNReal.ofReal |(x : ℝ) - (y : ℝ)|) ^ α ≤
      ENNReal.ofReal ((2 : ℝ) ^ α) *
          (proposition_4_9_far x).indicator (fun _ => (1 : ENNReal)) y +
        ∑' n : ℕ,
          ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) ^ α) *
            (proposition_4_9_shell x n).indicator (fun _ => (1 : ENNReal)) y := by
  by_cases hfar : y ∈ proposition_4_9_far x
  · have hd : (1 / 2 : ℝ) ≤ |(x : ℝ) - (y : ℝ)| := le_of_lt hfar
    have hE := proposition_4_9_energy_le_of_dist_ge' hα (by norm_num : (0:ℝ) < 1 / 2) hd
    have h2 : ((1 / (1 / 2 : ℝ)) ^ α) = (2 : ℝ) ^ α := by norm_num
    rw [h2] at hE
    calc
      1 / (ENNReal.ofReal |(x : ℝ) - (y : ℝ)|) ^ α ≤ ENNReal.ofReal ((2 : ℝ) ^ α) := hE
      _ = ENNReal.ofReal ((2 : ℝ) ^ α) *
          (proposition_4_9_far x).indicator (fun _ => (1 : ENNReal)) y := by
        simp [hfar]
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ α) *
            (proposition_4_9_far x).indicator (fun _ => (1 : ENNReal)) y +
          ∑' n : ℕ,
            ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) ^ α) *
              (proposition_4_9_shell x n).indicator (fun _ => (1 : ENNReal)) y :=
        le_add_of_nonneg_right (zero_le _)
  · have hdle_half : |(x : ℝ) - (y : ℝ)| ≤ 1 / 2 := by
      exact le_of_not_gt hfar
    have hcoord : (x : ℝ) ≠ y := by
      intro h
      apply hxy
      exact Subtype.ext h.symm
    have hdpos : 0 < |(x : ℝ) - (y : ℝ)| := abs_pos.mpr (sub_ne_zero.mpr hcoord)
    rcases exists_nat_pow_near_of_lt_one hdpos (proposition_4_9_abs_sub_le_one x y)
        (by norm_num : (0:ℝ) < 1 / 2) (by norm_num : (1:ℝ) / 2 < 1) with
      ⟨m, hm_lower, hm_upper⟩
    have hm_ne : m ≠ 0 := by
      intro hm0
      subst m
      rw [pow_zero] at hm_upper
      rw [pow_one] at hm_lower
      exact hfar (by exact hm_lower)
    rcases Nat.exists_eq_succ_of_ne_zero hm_ne with ⟨n, rfl⟩
    have hm_lower' : ((1 / 2 : ℝ) ^ (n + 2)) < |(x : ℝ) - (y : ℝ)| := by
      simpa [Nat.succ_eq_add_one, add_assoc] using hm_lower
    have hm_upper' : |(x : ℝ) - (y : ℝ)| ≤ ((1 / 2 : ℝ) ^ (n + 1)) := by
      simpa [Nat.succ_eq_add_one] using hm_upper
    have hshell : y ∈ proposition_4_9_shell x n := by
      constructor
      · have h := hm_lower'
        rw [proposition_4_9_half_pow (n + 2)] at h
        convert h using 2
        norm_num [Nat.cast_add]
      · have h := hm_upper'
        rw [proposition_4_9_half_pow (n + 1)] at h
        convert h using 2
        norm_num [Nat.cast_add]
    have hE := proposition_4_9_energy_le_of_dist_ge' hα
      (Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) _) hshell.1.le
    have hterm :
        ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) ^ α) ≤
          ∑' k : ℕ,
            ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(k + 2 : ℝ)))) ^ α) *
              (proposition_4_9_shell x k).indicator (fun _ => (1 : ENNReal)) y := by
      convert ENNReal.le_tsum (f := fun k : ℕ =>
          ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(k + 2 : ℝ)))) ^ α) *
            (proposition_4_9_shell x k).indicator (fun _ => (1 : ENNReal)) y) n using 2
      simp [hshell]
    calc
      1 / (ENNReal.ofReal |(x : ℝ) - (y : ℝ)|) ^ α ≤
          ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) ^ α) := hE
      _ ≤ ∑' k : ℕ,
            ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(k + 2 : ℝ)))) ^ α) *
              (proposition_4_9_shell x k).indicator (fun _ => (1 : ENNReal)) y := hterm
      _ ≤ ENNReal.ofReal ((2 : ℝ) ^ α) *
            (proposition_4_9_far x).indicator (fun _ => (1 : ENNReal)) y +
          ∑' k : ℕ,
            ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(k + 2 : ℝ)))) ^ α) *
              (proposition_4_9_shell x k).indicator (fun _ => (1 : ENNReal)) y :=
        le_add_of_nonneg_left (zero_le _)

/- accepted add_to_file helper 14 -/
lemma proposition_4_9_inner_energy_le
    (α : ℝ) (hα : 0 ≤ α) (f : ℕ → ℕ)
    (hf : Summable (fun n : ℕ => Real.rpow 2 (-(f n : ℝ))))
    (μ : MeasureTheory.Measure (Set.Icc (0 : ℝ) 1))
    (hμ : ∀ n : ℕ, ∀ A : Set (Set.Icc (0 : ℝ) 1),
      A.OrdConnected →
      Metric.diam A ≤ Real.rpow 2 (-(n : ℝ)) →
      μ A ≤ ENNReal.ofReal (Real.rpow 2 (-(α * (n : ℝ) + (f n : ℝ)))))
    (x : Set.Icc (0 : ℝ) 1) :
    (∫⁻ y : Set.Icc (0 : ℝ) 1,
      1 / (ENNReal.ofReal |(x : ℝ) - (y : ℝ)|) ^ α ∂μ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ α) * μ Set.univ +
        ENNReal.ofReal ((2 : ℝ) ^ (2 * α)) *
          ∑' n : ℕ, ENNReal.ofReal (Real.rpow 2 (-(f n : ℝ))) := by
  let C0 : ENNReal := ENNReal.ofReal ((2 : ℝ) ^ α)
  let C : ℕ → ENNReal := fun n =>
    ENNReal.ofReal ((1 / ((2 : ℝ) ^ (-(n + 2 : ℝ)))) ^ α)
  have hmeas0 : Measurable (fun y : Set.Icc (0 : ℝ) 1 =>
      C0 * (proposition_4_9_far x).indicator (fun _ => (1 : ENNReal)) y) := by
    exact (measurable_const.indicator (proposition_4_9_measurable_far x)).const_mul C0
  have hmeass : ∀ n : ℕ, Measurable (fun y : Set.Icc (0 : ℝ) 1 =>
      C n * (proposition_4_9_shell x n).indicator (fun _ => (1 : ENNReal)) y) := by
    intro n
    exact (measurable_const.indicator (proposition_4_9_measurable_shell x n)).const_mul (C n)
  have hAEne : ∀ᵐ y : Set.Icc (0 : ℝ) 1 ∂μ, y ≠ x := by
    rw [MeasureTheory.ae_iff]
    have hset : {y : Set.Icc (0 : ℝ) 1 | ¬ y ≠ x} = {x} := by
      ext y
      simp [eq_comm]
    rw [hset]
    exact proposition_4_9_measure_singleton_eq_zero α hα f hf μ hμ x
  have hAE : ∀ᵐ y : Set.Icc (0 : ℝ) 1 ∂μ,
      1 / (ENNReal.ofReal |(x : ℝ) - (y : ℝ)|) ^ α ≤
        C0 * (proposition_4_9_far x).indicator (fun _ => (1 : ENNReal)) y +
          ∑' n : ℕ, C n *
            (proposition_4_9_shell x n).indicator (fun _ => (1 : ENNReal)) y := by
    filter_upwards [hAEne] with y hy
    simpa [C0, C] using proposition_4_9_energy_pointwise_le' hα x y hy
  have hFint :
      (∫⁻ y : Set.Icc (0 : ℝ) 1,
        C0 * (proposition_4_9_far x).indicator (fun _ => (1 : ENNReal)) y +
          ∑' n : ℕ, C n *
            (proposition_4_9_shell x n).indicator (fun _ => (1 : ENNReal)) y ∂μ) =
      C0 * μ (proposition_4_9_far x) +
        ∑' n : ℕ, C n * μ (proposition_4_9_shell x n) := by
    rw [MeasureTheory.lintegral_add_left hmeas0]
    congr 1
    · rw [MeasureTheory.lintegral_const_mul C0
        (measurable_const.indicator (proposition_4_9_measurable_far x))]
      rw [MeasureTheory.lintegral_indicator_const (proposition_4_9_measurable_far x) 1]
      simp
    · rw [MeasureTheory.lintegral_tsum (fun n => (hmeass n).aemeasurable)]
      congr 1
      funext n
      rw [MeasureTheory.lintegral_const_mul (C n)
        (measurable_const.indicator (proposition_4_9_measurable_shell x n))]
      rw [MeasureTheory.lintegral_indicator_const (proposition_4_9_measurable_shell x n) 1]
      simp
  calc
    (∫⁻ y : Set.Icc (0 : ℝ) 1,
        1 / (ENNReal.ofReal |(x : ℝ) - (y : ℝ)|) ^ α ∂μ)
        ≤ ∫⁻ y : Set.Icc (0 : ℝ) 1,
          C0 * (proposition_4_9_far x).indicator (fun _ => (1 : ENNReal)) y +
            ∑' n : ℕ, C n *
              (proposition_4_9_shell x n).indicator (fun _ => (1 : ENNReal)) y ∂μ :=
      MeasureTheory.lintegral_mono_ae hAE
    _ = C0 * μ (proposition_4_9_far x) +
        ∑' n : ℕ, C n * μ (proposition_4_9_shell x n) := hFint
    _ ≤ C0 * μ Set.univ +
        ENNReal.ofReal ((2 : ℝ) ^ (2 * α)) *
          ∑' n : ℕ, ENNReal.ofReal (Real.rpow 2 (-(f n : ℝ))) := by
      apply add_le_add
      · exact mul_le_mul_left' (MeasureTheory.measure_mono (Set.subset_univ _)) C0
      · calc
          (∑' n : ℕ, C n * μ (proposition_4_9_shell x n))
              ≤ ∑' n : ℕ, C n *
                ENNReal.ofReal (Real.rpow 2 (-(α * (n : ℝ) + (f n : ℝ)))) := by
            apply ENNReal.tsum_le_tsum
            intro n
            apply mul_le_mul_left'
            exact le_trans
              (MeasureTheory.measure_mono (by
                intro y hy
                exact hy.2))
              (proposition_4_9_ball_le α f μ hμ x n)
          _ = ∑' n : ℕ, ENNReal.ofReal ((2 : ℝ) ^ (2 * α)) *
              ENNReal.ofReal (Real.rpow 2 (-(f n : ℝ))) := by
            congr 1
            funext n
            simpa [C] using proposition_4_9_shell_bound_eq α f n
          _ = ENNReal.ofReal ((2 : ℝ) ^ (2 * α)) *
              ∑' n : ℕ, ENNReal.ofReal (Real.rpow 2 (-(f n : ℝ))) := by
            rw [ENNReal.tsum_mul_left]

/- verified submission -/
theorem proposition_4_9
    (α : ℝ) (hα : 0 ≤ α) (f : ℕ → ℕ)
    (hf : Summable (fun n : ℕ => Real.rpow 2 (-(f n : ℝ))))
    (μ : MeasureTheory.Measure (Set.Icc (0 : ℝ) 1))
    (hμ : ∀ n : ℕ, ∀ A : Set (Set.Icc (0 : ℝ) 1),
      A.OrdConnected →
      Metric.diam A ≤ Real.rpow 2 (-(n : ℝ)) →
      μ A ≤ ENNReal.ofReal (Real.rpow 2 (-(α * (n : ℝ) + (f n : ℝ))))) :
    (∫⁻ x, ∫⁻ y,
      1 / (ENNReal.ofReal |(x : ℝ) - (y : ℝ)|) ^ α ∂μ ∂μ) < ⊤ := by
  have hμu : μ Set.univ < ⊤ := proposition_4_9_measure_univ_finite α f μ hμ
  have htsum : (∑' n : ℕ, ENNReal.ofReal (Real.rpow 2 (-(f n : ℝ)))) < ⊤ := by
    have htsumEq := ENNReal.ofReal_tsum_of_nonneg
      (f := fun n : ℕ => Real.rpow 2 (-(f n : ℝ)))
      (fun n => Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _) hf
    rw [← htsumEq]
    exact ENNReal.ofReal_lt_top
  let K : ENNReal := ENNReal.ofReal ((2 : ℝ) ^ α) * μ Set.univ +
    ENNReal.ofReal ((2 : ℝ) ^ (2 * α)) *
      ∑' n : ℕ, ENNReal.ofReal (Real.rpow 2 (-(f n : ℝ)))
  have hK : K < ⊤ := by
    apply ENNReal.add_lt_top.mpr
    constructor
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμu
    · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top htsum
  calc
    (∫⁻ x, ∫⁻ y,
        1 / (ENNReal.ofReal |(x : ℝ) - (y : ℝ)|) ^ α ∂μ ∂μ)
        ≤ ∫⁻ x : Set.Icc (0 : ℝ) 1, K ∂μ := by
      apply MeasureTheory.lintegral_mono
      intro x
      exact proposition_4_9_inner_energy_le α hα f hf μ hμ x
    _ = K * μ Set.univ := MeasureTheory.lintegral_const K
    _ < ⊤ := ENNReal.mul_lt_top hK hμu

end Rollout_p1874_proposition_4_9

namespace Rollout_p1776_subgroup_isup_eq_boolean_isup

/- accepted add_to_file helper 1 -/
def booleanCoeffRank (n : ℤ) : ℕ := (2 * n - 1).natAbs

lemma booleanCoeffRank_reflect (n : ℤ) (hn : ¬ (n = 0 ∨ n = 1)) :
    booleanCoeffRank (if 2 ≤ n then 2 - n else -n) < booleanCoeffRank n := by
  by_cases h : 2 ≤ n
  · simp [booleanCoeffRank, h]
    have hl : ((2 * (2 - n) - 1).natAbs : ℤ) = -(2 * (2 - n) - 1) := by
      have hnon : 0 ≤ -(2 * (2 - n) - 1) := by omega
      have habs := Int.natAbs_of_nonneg hnon
      rwa [Int.natAbs_neg] at habs
    have hr : ((2 * n - 1).natAbs : ℤ) = 2 * n - 1 := by
      exact Int.natAbs_of_nonneg (by omega)
    omega
  · simp [booleanCoeffRank, h]
    have hnlt : n < 0 := by omega
    have hl : ((2 * -n - 1).natAbs : ℤ) = 2 * -n - 1 := by
      exact Int.natAbs_of_nonneg (by omega)
    have hr : ((2 * n - 1).natAbs : ℤ) = -(2 * n - 1) := by
      have hnon : 0 ≤ -(2 * n - 1) := by omega
      have habs := Int.natAbs_of_nonneg hnon
      rwa [Int.natAbs_neg] at habs
    omega

lemma subgroup_le_sup_of_set_prod {U A : Type*} [Group U] [AddCommGroup A]
    (W : A → Subgroup U)
    (hprod : ∀ x y : A,
      (W x : Set U) ⊆ Set.image2 (fun g h : U => g * h) (W y : Set U)
        (W (2 • y - x) : Set U))
    (x y : A) :
    W x ≤ W y ⊔ W (2 • y - x) := by
  rw [← SetLike.coe_subset_coe]
  intro g hg
  rcases hprod x y hg with ⟨g₁, hg₁, g₂, hg₂, rfl⟩
  exact Subgroup.mul_mem _
    (SetLike.le_def.mp le_sup_left hg₁)
    (SetLike.le_def.mp le_sup_right hg₂)

/- accepted add_to_file helper 2 -/
lemma subgroup_le_boolean_iSup_of_int_coeffs {U A : Type*} [Group U] [AddCommGroup A]
    {m : ℕ} (a : Fin m → A) (W : A → Subgroup U)
    (hprod : ∀ x y : A,
      (W x : Set U) ⊆ Set.image2 (fun g h : U => g * h) (W y : Set U)
        (W (2 • y - x) : Set U))
    (n : Fin m → ℤ) :
    W (∑ i, n i • a i) ≤ ⨆ s : Finset (Fin m), W (∑ i ∈ s, a i) := by
  let rank : (Fin m → ℤ) → ℕ := fun c => ∑ i, booleanCoeffRank (c i)
  refine (InvImage.wf rank Nat.lt_wfRel.wf).fix
    (C := fun c : Fin m → ℤ =>
      W (∑ i, c i • a i) ≤ ⨆ s : Finset (Fin m), W (∑ i ∈ s, a i))
    (fun n ih => ?_) n
  have base_of_boolean : ∀ c : Fin m → ℤ, (∀ i, c i = 0 ∨ c i = 1) →
      W (∑ i, c i • a i) ≤ ⨆ s : Finset (Fin m), W (∑ i ∈ s, a i) := by
    intro c hc
    have hsum : (∑ i, c i • a i) =
        ∑ i ∈ Finset.univ.filter (fun i => c i = 1), a i := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i hi
      rcases hc i with h | h <;> simp [h]
    rw [hsum]
    exact le_iSup (fun s : Finset (Fin m) => W (∑ i ∈ s, a i))
      (Finset.univ.filter fun i => c i = 1)
  by_cases hb : ∀ i, n i = 0 ∨ n i = 1
  · exact base_of_boolean n hb
  · push_neg at hb
    rcases hb with ⟨j, hj⟩
    have hjnot : ¬ (n j = 0 ∨ n j = 1) := by
      intro h
      rcases h with h | h
      · exact hj.1 h
      · exact hj.2 h
    let b : Fin m → ℤ := fun i =>
      if h : n i = 0 ∨ n i = 1 then n i else if 2 ≤ n i then 1 else 0
    let n' : Fin m → ℤ := fun i => 2 * b i - n i
    have hb01 : ∀ i, b i = 0 ∨ b i = 1 := by
      intro i
      by_cases hgood : n i = 0 ∨ n i = 1
      · simpa [b, hgood] using hgood
      · by_cases htwo : 2 ≤ n i
        · simp [b, hgood, htwo]
        · simp [b, hgood, htwo]
    have hcoord_le : ∀ i, booleanCoeffRank (n' i) ≤ booleanCoeffRank (n i) := by
      intro i
      by_cases hgood : n i = 0 ∨ n i = 1
      · have hn'i : n' i = n i := by
          simp [n', b, hgood]
          ring
        rw [hn'i]
      · have hlt := booleanCoeffRank_reflect (n i) hgood
        by_cases htwo : 2 ≤ n i
        · have hn'i : n' i = 2 - n i := by
            simp [n', b, hgood, htwo]
          rw [hn'i]
          simpa [htwo] using le_of_lt hlt
        · have hn'i : n' i = -n i := by
            simp [n', b, hgood, htwo]
          rw [hn'i]
          simpa [htwo] using le_of_lt hlt
    have hcoord_j : booleanCoeffRank (n' j) < booleanCoeffRank (n j) := by
      have hlt := booleanCoeffRank_reflect (n j) hjnot
      by_cases htwo : 2 ≤ n j
      · have hn'j : n' j = 2 - n j := by
          simp [n', b, hjnot, htwo]
        rw [hn'j]
        simpa [htwo] using hlt
      · have hn'j : n' j = -n j := by
          simp [n', b, hjnot, htwo]
        rw [hn'j]
        simpa [htwo] using hlt
    have hrank : rank n' < rank n := by
      dsimp [rank]
      exact Finset.sum_lt_sum (fun i hi => hcoord_le i) ⟨j, Finset.mem_univ j, hcoord_j⟩
    have hz : W (∑ i, n' i • a i) ≤ ⨆ s : Finset (Fin m), W (∑ i ∈ s, a i) :=
      ih n' hrank
    have hy : W (∑ i, b i • a i) ≤ ⨆ s : Finset (Fin m), W (∑ i ∈ s, a i) :=
      base_of_boolean b hb01
    have hlin : (∑ i, n' i • a i) =
        2 • (∑ i, b i • a i) - ∑ i, n i • a i := by
      trans ∑ i, ((2 * b i) • a i - n i • a i)
      · apply Finset.sum_congr rfl
        intro i hi
        rw [sub_smul]
      · rw [Finset.sum_sub_distrib]
        congr 1
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [show 2 * b i = b i + b i by ring, add_smul, two_nsmul]
    have hx_sup := subgroup_le_sup_of_set_prod W hprod
      (∑ i, n i • a i) (∑ i, b i • a i)
    rw [← hlin] at hx_sup
    exact hx_sup.trans (sup_le hy hz)

/- verified submission -/
theorem subgroup_iSup_eq_boolean_iSup
    {U A : Type*} [Group U] [AddCommGroup A] {m : ℕ}
    (a : Fin m → A) (W : A → Subgroup U)
    (hgen : AddSubgroup.closure (Set.range a) = ⊤)
    (hcomm : ∀ x : A, commutator U ≤ W x)
    (hprod : ∀ x y : A,
      (W x : Set U) ⊆ Set.image2 (fun g h : U => g * h) (W y : Set U)
        (W (2 • y - x) : Set U)) :
    (⨆ x : A, W x) = ⨆ s : Finset (Fin m), W (∑ i ∈ s, a i) := by
  apply le_antisymm
  · apply iSup_le
    intro x
    have hx : x ∈ AddSubgroup.closure (Set.range a) := by
      rw [hgen]
      trivial
    rcases AddSubgroup.mem_closure_range_iff.mp hx with ⟨c, hc⟩
    rw [Finsupp.sum_zsmul] at hc
    rw [hc]
    exact subgroup_le_boolean_iSup_of_int_coeffs a W hprod c
  · apply iSup_le
    intro s
    exact le_iSup (fun x : A => W x) (∑ i ∈ s, a i)

end Rollout_p1776_subgroup_isup_eq_boolean_isup

namespace Rollout_p1462_locallycompact_prod_ascoli

/- accepted add_to_file helper 1 -/

open Set

lemma continuous_sectionMap_real
    (Z X : Type*) [TopologicalSpace Z] [LocallyCompactSpace Z] [TopologicalSpace X] :
    Continuous
      (fun p : C(Z × X, ℝ) × Z =>
        (⟨fun x => p.1 (p.2, x),
          p.1.continuous.comp (Continuous.prodMk_right p.2)⟩ : C(X, ℝ))) := by
  rw [ContinuousMap.continuous_compactOpen]
  intro C hC U hU
  rw [isOpen_iff_forall_mem_open]
  rintro ⟨f, z⟩ hf
  have hn : IsOpen (f ⁻¹' U) := hU.preimage f.continuous
  have hprod : ({z} : Set Z) ×ˢ C ⊆ f ⁻¹' U := by
    rintro ⟨z', x⟩ ⟨hz', hx⟩
    simp at hz'
    subst z'
    exact hf hx
  obtain ⟨V, W, hV, hW, hzV, hCW, hVW⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := z)) hC hn hprod
  obtain ⟨L, hL, hzL, hLV⟩ := exists_compact_subset hV (hzV rfl)
  refine ⟨{g : C(Z × X, ℝ) | Set.MapsTo g (L ×ˢ C) U} ×ˢ interior L, ?_,
    (ContinuousMap.isOpen_setOf_mapsTo (hL.prod hC) hU).prod isOpen_interior,
    ⟨?_, hzL⟩⟩
  · rintro ⟨g, z'⟩ ⟨hg, hz'⟩
    intro x hx
    exact hg ⟨interior_subset hz', hx⟩
  · rintro ⟨z', x⟩ ⟨hz', hx⟩
    exact hVW ⟨hLV hz', hCW hx⟩

/- verified submission -/
theorem locallyCompact_prod_ascoli
    (Z X : Type*) [TopologicalSpace Z] [T35Space Z] [LocallyCompactSpace Z]
    [TopologicalSpace X] [T35Space X]
    (hX : ∀ K : Set C(X, ℝ), IsCompact K →
      Continuous (fun p : K × X => (p.1 : C(X, ℝ)) p.2)) :
    ∀ K : Set C(Z × X, ℝ), IsCompact K →
      Continuous (fun p : K × (Z × X) => (p.1 : C(Z × X, ℝ)) p.2) := by
  intro K hK
  let Φ : C(Z × X, ℝ) × Z → C(X, ℝ) := fun p =>
    ⟨fun x => p.1 (p.2, x),
      p.1.continuous.comp (Continuous.prodMk_right p.2)⟩
  have hΦ : Continuous Φ := continuous_sectionMap_real Z X
  rw [continuous_iff_continuousAt]
  rintro ⟨f, ⟨z, x⟩⟩
  obtain ⟨L, hL, hzL, -⟩ := exists_compact_subset isOpen_univ (Set.mem_univ z)
  let A : Set C(X, ℝ) := Φ '' (K ×ˢ L)
  have hA : IsCompact A := (hK.prod hL).image hΦ
  have hEv : Continuous (fun p : A × X => (p.1 : C(X, ℝ)) p.2) := hX A hA
  let S : Set (K × (Z × X)) := (fun p => p.2.1) ⁻¹' interior L
  have hS : IsOpen S := isOpen_interior.preimage (continuous_fst.comp continuous_snd)
  have hval : Continuous (Subtype.val : S → K × (Z × X)) := continuous_subtype_val
  have hCproj : Continuous (fun s : S => ((s.1.1 : K) : C(Z × X, ℝ))) := by
    exact continuous_subtype_val.comp (continuous_fst.comp hval)
  have hZproj : Continuous (fun s : S => s.1.2.1) := by
    exact continuous_fst.comp (continuous_snd.comp hval)
  have hXproj : Continuous (fun s : S => s.1.2.2) := by
    exact continuous_snd.comp (continuous_snd.comp hval)
  have hsec : Continuous (fun s : S => Φ (((s.1.1 : K) : C(Z × X, ℝ)), s.1.2.1)) :=
    hΦ.comp (hCproj.prodMk hZproj)
  have hmem : ∀ s : S, Φ (((s.1.1 : K) : C(Z × X, ℝ)), s.1.2.1) ∈ A := by
    intro s
    refine Set.mem_image_of_mem Φ ?_
    exact ⟨s.1.1.property, interior_subset s.2⟩
  have hsecA : Continuous
      (fun s : S => (⟨Φ (((s.1.1 : K) : C(Z × X, ℝ)), s.1.2.1), hmem s⟩ : A)) :=
    hsec.codRestrict hmem
  have hpair : Continuous
      (fun s : S =>
        ((⟨Φ (((s.1.1 : K) : C(Z × X, ℝ)), s.1.2.1), hmem s⟩ : A), s.1.2.2)) :=
    hsecA.prodMk hXproj
  have hloc : Continuous
      (fun s : S => ((⟨Φ (((s.1.1 : K) : C(Z × X, ℝ)), s.1.2.1), hmem s⟩ : A) : C(X, ℝ)) s.1.2.2) :=
    hEv.comp hpair
  have hloc' : Continuous
      ((fun p : K × (Z × X) => (p.1 : C(Z × X, ℝ)) p.2) ∘ (Subtype.val : S → K × (Z × X))) := by
    convert hloc using 1
  let ps : S := ⟨⟨f, ⟨z, x⟩⟩, hzL⟩
  exact (hS.isOpenEmbedding_subtypeVal.continuousAt_iff (x := ps)).mp
    (hloc'.continuousAt (x := ps))

end Rollout_p1462_locallycompact_prod_ascoli

namespace Rollout_p2763_graded_simple_mul_nonzero

/- accepted add_to_file helper 1 -/
lemma graded_exists_finset_decomp
    (G K A : Type*) [Group G] [Field K] [AddCommGroup A] [Module K A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤) (z : A) :
    ∃ s : Finset G, ∃ f : G → A,
      (∀ i ∈ s, f i ∈ 𝒜 i) ∧ ∑ i ∈ s, f i = z := by
  classical
  let e := h_direct.1.linearEquiv h_direct.2
  let d : Π₀ i : G, 𝒜 i := e.symm z
  refine ⟨d.support, fun i => (d i : A), ?_, ?_⟩
  · intro i hi
    exact (d i).property
  · have hz : e d = z := e.apply_symm_apply z
    rw [iSupIndep.linearEquiv_apply, DFinsupp.sumAddHom_apply] at hz
    simpa [DFinsupp.sum, d] using hz

/- accepted add_to_file helper 2 -/
namespace GradedSimpleProof

def sandwichLeftAnn
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A) (a : A) : Submodule K A where
  carrier := {y | ∀ (k : G) (x : A), x ∈ 𝒜 k → a * x * y = 0}
  zero_mem' := by
    intro k x hx
    simp
  add_mem' {y z} hy hz := by
    intro k x hx
    rw [mul_add, hy k x hx, hz k x hx, add_zero]
  smul_mem' c {y} hy := by
    intro k x hx
    rw [mul_smul_comm, hy k x hx, smul_zero]

end GradedSimpleProof

/- accepted add_to_file helper 3 -/
namespace GradedSimpleProof

lemma sandwichLeftAnn_graded
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤)
    (h_mul : ∀ {g h : G} {x y : A}, x ∈ 𝒜 g → y ∈ 𝒜 h → x * y ∈ 𝒜 (g * h))
    {g : G} {a : A} (ha : a ∈ 𝒜 g) :
    iSup (fun i : G => 𝒜 i ⊓ sandwichLeftAnn G K A 𝒜 a) =
      sandwichLeftAnn G K A 𝒜 a := by
  apply le_antisymm
  · apply iSup_le
    intro i
    exact inf_le_right
  · intro y hy
    obtain ⟨s, f, hf, hsum⟩ := graded_exists_finset_decomp G K A 𝒜 h_direct y
    rw [Submodule.mem_iSup]
    intro N hN
    have hcomp : ∀ i ∈ s, f i ∈ sandwichLeftAnn G K A 𝒜 a := by
      intro i hi k x hx
      let c : G := g * k
      have hq : iSupIndep (fun j : G => 𝒜 (c * j)) :=
        h_direct.1.comp (mul_right_injective c)
      have hzero : ∑ j ∈ s, a * x * f j = 0 := by
        calc
          ∑ j ∈ s, a * x * f j = (a * x) * (∑ j ∈ s, f j) := by
            rw [Finset.mul_sum]
          _ = a * x * y := by rw [hsum]
          _ = 0 := hy k x hx
      have hmem : ∀ j ∈ s, a * x * f j ∈ 𝒜 (c * j) := by
        intro j hj
        exact h_mul (h_mul ha hx) (hf j hj)
      exact (iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero
        (fun j : G => 𝒜 (c * j))).1 hq s (fun j => a * x * f j) hmem hzero i hi
    rw [← hsum]
    exact N.sum_mem (fun i hi => hN i ⟨hf i hi, hcomp i hi⟩)

end GradedSimpleProof

/- accepted add_to_file helper 4 -/
namespace GradedSimpleProof

lemma sandwichLeftAnn_left_ideal
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤)
    (a r : A) {y : A}
    (hy : y ∈ sandwichLeftAnn G K A 𝒜 a) :
    r * y ∈ sandwichLeftAnn G K A 𝒜 a := by
  intro k x hx
  obtain ⟨s, f, hf, hsum⟩ := graded_exists_finset_decomp G K A 𝒜 h_direct (x * r)
  calc
    a * x * (r * y) = a * (x * r) * y := by simp [mul_assoc]
    _ = a * (∑ i ∈ s, f i) * y := by rw [← hsum]
    _ = ∑ i ∈ s, a * f i * y := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact hy i (f i) (hf i hi)

lemma sandwichLeftAnn_right_ideal
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (a r : A) {y : A}
    (hy : y ∈ sandwichLeftAnn G K A 𝒜 a) :
    y * r ∈ sandwichLeftAnn G K A 𝒜 a := by
  intro k x hx
  rw [← mul_assoc (a * x) y r, hy k x hx, zero_mul]

end GradedSimpleProof

/- accepted add_to_file helper 5 -/
namespace GradedSimpleProof

def tripleLeftAnn
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A) : Submodule K A where
  carrier := {z | ∀ (k : G) (x : A), x ∈ 𝒜 k →
    ∀ (l : G) (y : A), y ∈ 𝒜 l → z * x * y = 0}
  zero_mem' := by
    intro k x hx l y hy
    simp
  add_mem' {z w} hz hw := by
    intro k x hx l y hy
    rw [add_mul, add_mul, hz k x hx l y hy, hw k x hx l y hy, add_zero]
  smul_mem' c {z} hz := by
    intro k x hx l y hy
    rw [smul_mul_assoc, smul_mul_assoc, hz k x hx l y hy, smul_zero]

end GradedSimpleProof

/- accepted add_to_file helper 6 -/
namespace GradedSimpleProof

lemma tripleLeftAnn_graded
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤)
    (h_mul : ∀ {g h : G} {x y : A}, x ∈ 𝒜 g → y ∈ 𝒜 h → x * y ∈ 𝒜 (g * h)) :
    iSup (fun i : G => 𝒜 i ⊓ tripleLeftAnn G K A 𝒜) =
      tripleLeftAnn G K A 𝒜 := by
  apply le_antisymm
  · apply iSup_le
    intro i
    exact inf_le_right
  · intro z hz
    obtain ⟨s, f, hf, hsum⟩ := graded_exists_finset_decomp G K A 𝒜 h_direct z
    rw [Submodule.mem_iSup]
    intro N hN
    have hcomp : ∀ i ∈ s, f i ∈ tripleLeftAnn G K A 𝒜 := by
      intro i hi k x hx l y hy
      have hinj : Function.Injective (fun j : G => (j * k) * l) :=
        (mul_left_injective l).comp (mul_left_injective k)
      have hq : iSupIndep (fun j : G => 𝒜 ((j * k) * l)) :=
        h_direct.1.comp hinj
      have hzero : ∑ j ∈ s, f j * x * y = 0 := by
        calc
          ∑ j ∈ s, f j * x * y = (∑ j ∈ s, f j) * x * y := by
            rw [Finset.sum_mul, Finset.sum_mul]
          _ = z * x * y := by rw [hsum]
          _ = 0 := hz k x hx l y hy
      have hmem : ∀ j ∈ s, f j * x * y ∈ 𝒜 ((j * k) * l) := by
        intro j hj
        exact h_mul (h_mul (hf j hj) hx) hy
      exact (iSupIndep_iff_finset_sum_eq_zero_imp_eq_zero
        (fun j : G => 𝒜 ((j * k) * l))).1 hq s
        (fun j => f j * x * y) hmem hzero i hi
    rw [← hsum]
    exact N.sum_mem (fun i hi => hN i ⟨hf i hi, hcomp i hi⟩)

end GradedSimpleProof

/- accepted add_to_file helper 7 -/
namespace GradedSimpleProof

lemma tripleLeftAnn_left_ideal
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A) (r : A) {z : A}
    (hz : z ∈ tripleLeftAnn G K A 𝒜) :
    r * z ∈ tripleLeftAnn G K A 𝒜 := by
  intro k x hx l y hy
  calc
    r * z * x * y = r * (z * x * y) := by simp [mul_assoc]
    _ = 0 := by rw [hz k x hx l y hy, mul_zero]

lemma tripleLeftAnn_right_ideal
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤)
    (r : A) {z : A}
    (hz : z ∈ tripleLeftAnn G K A 𝒜) :
    z * r ∈ tripleLeftAnn G K A 𝒜 := by
  intro k x hx l y hy
  obtain ⟨s, f, hf, hsum⟩ := graded_exists_finset_decomp G K A 𝒜 h_direct (r * x)
  calc
    z * r * x * y = z * (r * x) * y := by simp [mul_assoc]
    _ = z * (∑ i ∈ s, f i) * y := by rw [← hsum]
    _ = ∑ i ∈ s, z * f i * y := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact hz i (f i) (hf i hi) l y hy

end GradedSimpleProof

/- accepted add_to_file helper 8 -/
namespace GradedSimpleProof

def homogeneousProductSet
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A] [Module K A]
    (𝒜 : G → Submodule K A) : Set A :=
  {p | ∃ (i : G) (x : A), x ∈ 𝒜 i ∧ ∃ (j : G) (y : A), y ∈ 𝒜 j ∧ p = x * y}

def homogeneousProductSubmodule
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A] [Module K A]
    (𝒜 : G → Submodule K A) : Submodule K A :=
  Submodule.span K (homogeneousProductSet G K A 𝒜)

lemma mem_homogeneousProductSubmodule
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A] [Module K A]
    (𝒜 : G → Submodule K A)
    {i j : G} {x y : A} (hx : x ∈ 𝒜 i) (hy : y ∈ 𝒜 j) :
    x * y ∈ homogeneousProductSubmodule G K A 𝒜 := by
  apply Submodule.subset_span
  exact ⟨i, x, hx, j, y, hy, rfl⟩

end GradedSimpleProof

/- accepted add_to_file helper 9 -/
namespace GradedSimpleProof

lemma homogeneousProductSubmodule_left_ideal
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤)
    (r : A) {p : A} (hp : p ∈ homogeneousProductSubmodule G K A 𝒜) :
    r * p ∈ homogeneousProductSubmodule G K A 𝒜 := by
  unfold homogeneousProductSubmodule at hp ⊢
  refine Submodule.span_induction (fun q hq => ?_) ?_ ?_ ?_ hp
  · obtain ⟨i, x, hx, j, y, hy, rfl⟩ := hq
    obtain ⟨s, f, hf, hsum⟩ := graded_exists_finset_decomp G K A 𝒜 h_direct (r * x)
    have hEq : r * (x * y) = ∑ n ∈ s, f n * y := by
      calc
        r * (x * y) = (r * x) * y := by simp [mul_assoc]
        _ = (∑ n ∈ s, f n) * y := by rw [← hsum]
        _ = ∑ n ∈ s, f n * y := by rw [Finset.sum_mul]
    rw [hEq]
    apply Submodule.sum_mem
    intro n hn
    exact mem_homogeneousProductSubmodule G K A 𝒜 (hf n hn) hy
  · simp
  · intro q₁ q₂ hq₁ hq₂ h₁ h₂
    rw [mul_add]
    exact (Submodule.span K (homogeneousProductSet G K A 𝒜)).add_mem h₁ h₂
  · intro c q hq h
    rw [mul_smul_comm]
    exact (Submodule.span K (homogeneousProductSet G K A 𝒜)).smul_mem c h

end GradedSimpleProof

/- accepted add_to_file helper 10 -/
namespace GradedSimpleProof

lemma homogeneousProductSubmodule_right_ideal
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤)
    (r : A) {p : A} (hp : p ∈ homogeneousProductSubmodule G K A 𝒜) :
    p * r ∈ homogeneousProductSubmodule G K A 𝒜 := by
  unfold homogeneousProductSubmodule at hp ⊢
  refine Submodule.span_induction (fun q hq => ?_) ?_ ?_ ?_ hp
  · obtain ⟨i, x, hx, j, y, hy, rfl⟩ := hq
    obtain ⟨s, f, hf, hsum⟩ := graded_exists_finset_decomp G K A 𝒜 h_direct (y * r)
    have hEq : (x * y) * r = ∑ n ∈ s, x * f n := by
      calc
        (x * y) * r = x * (y * r) := by rw [mul_assoc]
        _ = x * (∑ n ∈ s, f n) := by rw [← hsum]
        _ = ∑ n ∈ s, x * f n := by rw [Finset.mul_sum]
    rw [hEq]
    apply Submodule.sum_mem
    intro n hn
    exact mem_homogeneousProductSubmodule G K A 𝒜 hx (hf n hn)
  · simp
  · intro q₁ q₂ hq₁ hq₂ h₁ h₂
    rw [add_mul]
    exact (Submodule.span K (homogeneousProductSet G K A 𝒜)).add_mem h₁ h₂
  · intro c q hq h
    rw [smul_mul_assoc]
    exact (Submodule.span K (homogeneousProductSet G K A 𝒜)).smul_mem c h

end GradedSimpleProof

/- accepted add_to_file helper 11 -/
namespace GradedSimpleProof

lemma homogeneousProductSubmodule_graded
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_mul : ∀ {g h : G} {x y : A}, x ∈ 𝒜 g → y ∈ 𝒜 h → x * y ∈ 𝒜 (g * h)) :
    iSup (fun i : G => 𝒜 i ⊓ homogeneousProductSubmodule G K A 𝒜) =
      homogeneousProductSubmodule G K A 𝒜 := by
  apply le_antisymm
  · apply iSup_le
    intro i
    exact inf_le_right
  · unfold homogeneousProductSubmodule
    rw [Submodule.span_le]
    intro p hp
    obtain ⟨i, x, hx, j, y, hy, rfl⟩ := hp
    apply Submodule.mem_iSup_of_mem (i * j)
    exact ⟨h_mul hx hy, mem_homogeneousProductSubmodule G K A 𝒜 hx hy⟩

end GradedSimpleProof

/- accepted add_to_file helper 12 -/
namespace GradedSimpleProof

lemma mul_eq_zero_of_mem_homogeneousProductSubmodule
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (hH : tripleLeftAnn G K A 𝒜 = ⊤)
    (u : A) {p : A} (hp : p ∈ homogeneousProductSubmodule G K A 𝒜) :
    u * p = 0 := by
  unfold homogeneousProductSubmodule at hp
  refine Submodule.span_induction (fun q hq => ?_) ?_ ?_ ?_ hp
  · obtain ⟨i, x, hx, j, y, hy, rfl⟩ := hq
    have huH : u ∈ tripleLeftAnn G K A 𝒜 := by
      rw [hH]
      exact Submodule.mem_top
    rw [← mul_assoc]
    exact huH i x hx j y hy
  · simp
  · intro q₁ q₂ hq₁ hq₂ h₁ h₂
    rw [mul_add, h₁, h₂, add_zero]
  · intro c q hq h
    rw [mul_smul_comm, h, smul_zero]

end GradedSimpleProof

/- accepted add_to_file helper 13 -/
namespace GradedSimpleProof

lemma exists_homogeneous_mul_ne_zero
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤)
    (h_nonzero_mul : ∃ x y : A, x * y ≠ 0) :
    ∃ (i : G) (x : A), x ∈ 𝒜 i ∧
      ∃ (j : G) (y : A), y ∈ 𝒜 j ∧ x * y ≠ 0 := by
  obtain ⟨u, v, huv⟩ := h_nonzero_mul
  obtain ⟨su, fu, hfu, hsumu⟩ := graded_exists_finset_decomp G K A 𝒜 h_direct u
  obtain ⟨sv, fv, hfv, hsumv⟩ := graded_exists_finset_decomp G K A 𝒜 h_direct v
  have hprod_sum : (∑ i ∈ su, ∑ j ∈ sv, fu i * fv j) = u * v := by
    calc
      (∑ i ∈ su, ∑ j ∈ sv, fu i * fv j) =
          (∑ i ∈ su, fu i) * (∑ j ∈ sv, fv j) := by
        symm
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = u * v := by rw [hsumu, hsumv]
  have hsum_ne : (∑ i ∈ su, ∑ j ∈ sv, fu i * fv j) ≠ 0 := by
    rwa [hprod_sum]
  obtain ⟨i, hi, hinner⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
  obtain ⟨j, hj, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hinner
  exact ⟨i, fu i, hfu i hi, j, fv j, hfv j hj, hp⟩

end GradedSimpleProof

/- verified submission -/
theorem graded_simple_mul_nonzero
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤)
    (h_mul : ∀ {g h : G} {x y : A}, x ∈ 𝒜 g → y ∈ 𝒜 h → x * y ∈ 𝒜 (g * h))
    (h_nonzero_mul : ∃ x y : A, x * y ≠ 0)
    (h_simple : ∀ I : Submodule K A,
      (∀ (r : A) {x : A}, x ∈ I → r * x ∈ I) →
      (∀ (r : A) {x : A}, x ∈ I → x * r ∈ I) →
      iSup (fun g => 𝒜 g ⊓ I) = I → I = ⊥ ∨ I = ⊤)
    {g h : G} {a b : A} (ha : a ∈ 𝒜 g) (hb : b ∈ 𝒜 h)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    ∃ k : G, ∃ x : A, x ∈ 𝒜 k ∧ a * x * b ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  let J : Submodule K A := GradedSimpleProof.sandwichLeftAnn G K A 𝒜 a
  have hbJ : b ∈ J := hcon
  have hJ := h_simple J
    (fun r {x} hx => GradedSimpleProof.sandwichLeftAnn_left_ideal G K A 𝒜 h_direct a r hx)
    (fun r {x} hx => GradedSimpleProof.sandwichLeftAnn_right_ideal G K A 𝒜 a r hx)
    (GradedSimpleProof.sandwichLeftAnn_graded G K A 𝒜 h_direct h_mul ha)
  have hJtop : J = ⊤ := by
    rcases hJ with hJbot | hJtop
    · have hbzero : b = 0 := by
        have hbJ' : b ∈ (⊥ : Submodule K A) := by
          rwa [← hJbot]
        simpa using hbJ'
      exact (hb0 hbzero).elim
    · exact hJtop
  let H : Submodule K A := GradedSimpleProof.tripleLeftAnn G K A 𝒜
  have haH : a ∈ H := by
    intro k x hx l y hy
    have hyJ : y ∈ J := by
      rw [hJtop]
      exact Submodule.mem_top
    exact hyJ k x hx
  have hH := h_simple H
    (fun r {x} hx => GradedSimpleProof.tripleLeftAnn_left_ideal G K A 𝒜 r hx)
    (fun r {x} hx => GradedSimpleProof.tripleLeftAnn_right_ideal G K A 𝒜 h_direct r hx)
    (GradedSimpleProof.tripleLeftAnn_graded G K A 𝒜 h_direct h_mul)
  have hHtop : H = ⊤ := by
    rcases hH with hHbot | hHtop
    · have hazero : a = 0 := by
        have haH' : a ∈ (⊥ : Submodule K A) := by
          rwa [← hHbot]
        simpa using haH'
      exact (ha0 hazero).elim
    · exact hHtop
  let P : Submodule K A := GradedSimpleProof.homogeneousProductSubmodule G K A 𝒜
  obtain ⟨i, x, hx, j, y, hy, hxy⟩ :=
    GradedSimpleProof.exists_homogeneous_mul_ne_zero G K A 𝒜 h_direct h_nonzero_mul
  have hxyP : x * y ∈ P :=
    GradedSimpleProof.mem_homogeneousProductSubmodule G K A 𝒜 hx hy
  have hP := h_simple P
    (fun r {z} hz => GradedSimpleProof.homogeneousProductSubmodule_left_ideal G K A 𝒜 h_direct r hz)
    (fun r {z} hz => GradedSimpleProof.homogeneousProductSubmodule_right_ideal G K A 𝒜 h_direct r hz)
    (GradedSimpleProof.homogeneousProductSubmodule_graded G K A 𝒜 h_mul)
  have hPtop : P = ⊤ := by
    rcases hP with hPbot | hPtop
    · have hxyzero : x * y = 0 := by
        have hxyP' : x * y ∈ (⊥ : Submodule K A) := by
          rwa [← hPbot]
        simpa using hxyP'
      exact (hxy hxyzero).elim
    · exact hPtop
  obtain ⟨u, v, huv⟩ := h_nonzero_mul
  have hvP : v ∈ P := by
    rw [hPtop]
    exact Submodule.mem_top
  have huvzero : u * v = 0 :=
    GradedSimpleProof.mul_eq_zero_of_mem_homogeneousProductSubmodule G K A 𝒜 hHtop u hvP
  exact huv huvzero

end Rollout_p2763_graded_simple_mul_nonzero

namespace Rollout_p2075_metric_amalgamation

/- accepted add_to_file helper 1 -/

noncomputable section

namespace MetricAmalgamation

variable {X : Type*} {I : Type*} [MetricSpace X]

def pieceIndex (B : I → Set X) (hB_cover : (⋃ i, B i) = Set.univ) (x : X) : I :=
  Classical.choose (by
    have hx : x ∈ (⋃ i, B i : Set X) := by
      rw [hB_cover]
      exact Set.mem_univ x
    exact Set.mem_iUnion.mp hx)

lemma mem_piece (B : I → Set X) (hB_cover : (⋃ i, B i) = Set.univ) (x : X) :
    x ∈ B (pieceIndex B hB_cover x) :=
  Classical.choose_spec (by
    have hx : x ∈ (⋃ i, B i : Set X) := by
      rw [hB_cover]
      exact Set.mem_univ x
    exact Set.mem_iUnion.mp hx)

lemma pieceIndex_eq_of_mem {B : I → Set X}
    (hB_disjoint : (Set.univ : Set I).PairwiseDisjoint B)
    (hB_cover : (⋃ i, B i) = Set.univ) {x : X} {i : I} (hx : x ∈ B i) :
    pieceIndex B hB_cover x = i := by
  classical
  by_contra hne
  have hd : Disjoint (B (pieceIndex B hB_cover x)) (B i) :=
    hB_disjoint (Set.mem_univ _) (Set.mem_univ _) hne
  exact Set.disjoint_iff_forall_ne.mp hd (mem_piece B hB_cover x) hx rfl

def piecePoint (B : I → Set X) (hB_cover : (⋃ i, B i) = Set.univ) (x : X) :
    B (pieceIndex B hB_cover x) :=
  ⟨x, mem_piece B hB_cover x⟩

def glueDist (B : I → Set X) (hB_cover : (⋃ i, B i) = Set.univ)
    (p : ∀ i, B i) (e : ∀ i, MetricSpace (B i)) (x y : X) : ℝ := by
  classical
  exact if h : pieceIndex B hB_cover x = pieceIndex B hB_cover y then
    @dist (B (pieceIndex B hB_cover x)) (e _).toPseudoMetricSpace.toDist
      (piecePoint B hB_cover x)
      ⟨y, by simpa [h] using mem_piece B hB_cover y⟩
  else
    @dist (B (pieceIndex B hB_cover x)) (e _).toPseudoMetricSpace.toDist
      (piecePoint B hB_cover x) (p _) +
    dist (p (pieceIndex B hB_cover x) : X) (p (pieceIndex B hB_cover y) : X) +
    @dist (B (pieceIndex B hB_cover y)) (e _).toPseudoMetricSpace.toDist
      (p _) (piecePoint B hB_cover y)

end MetricAmalgamation

end

/- accepted add_to_file helper 2 -/
namespace MetricAmalgamation

variable {X : Type*} {I : Type*} [MetricSpace X]
variable {B : I → Set X}
variable {p : ∀ i, B i}
variable {e : ∀ i, MetricSpace (B i)}

lemma glueDist_left_congr {a i : I} (h : a = i) {x : X} (hx : x ∈ B a) :
    @dist (B a) (e a).toPseudoMetricSpace.toDist (⟨x, hx⟩ : B a) (p a) =
      @dist (B i) (e i).toPseudoMetricSpace.toDist
        (⟨x, h ▸ hx⟩ : B i) (p i) := by
  cases h
  rfl

lemma glueDist_right_congr {b j : I} (h : b = j) {y : X} (hy : y ∈ B b) :
    @dist (B b) (e b).toPseudoMetricSpace.toDist (p b) (⟨y, hy⟩ : B b) =
      @dist (B j) (e j).toPseudoMetricSpace.toDist (p j)
        (⟨y, h ▸ hy⟩ : B j) := by
  cases h
  rfl

lemma glueDist_base_congr {a i b j : I} (ha : a = i) (hb : b = j) :
    dist (p a : X) (p b : X) = dist (p i : X) (p j : X) := by
  cases ha
  cases hb
  rfl

variable {hB_disjoint : (Set.univ : Set I).PairwiseDisjoint B}
variable {hB_cover : (⋃ i, B i) = Set.univ}

include hB_disjoint hB_cover in
lemma glueDist_subtype_same (i : I) (x y : B i) :
    glueDist B hB_cover p e (x : X) (y : X) =
      @dist (B i) (e i).toPseudoMetricSpace.toDist x y := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  have hxi := pieceIndex_eq_of_mem (B := B) hB_disjoint hB_cover hx
  have hyi := pieceIndex_eq_of_mem (B := B) hB_disjoint hB_cover hy
  have hi : i = pieceIndex B hB_cover x := hxi.symm
  subst hi
  simp [glueDist, hyi, piecePoint]

include hB_disjoint hB_cover in
lemma glueDist_subtype_ne {i j : I} (hij : i ≠ j) (x : B i) (y : B j) :
    glueDist B hB_cover p e (x : X) (y : X) =
      @dist (B i) (e i).toPseudoMetricSpace.toDist x (p i) +
        dist (p i : X) (p j : X) +
          @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) y := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  have hxi := pieceIndex_eq_of_mem (B := B) hB_disjoint hB_cover hx
  have hyj := pieceIndex_eq_of_mem (B := B) hB_disjoint hB_cover hy
  have hidx : pieceIndex B hB_cover x ≠ pieceIndex B hB_cover y := by
    simpa [hxi, hyj] using hij
  unfold glueDist
  rw [dif_neg hidx]
  simp only [piecePoint]
  rw [glueDist_left_congr (p := p) (e := e) hxi (mem_piece B hB_cover x)]
  rw [glueDist_right_congr (p := p) (e := e) hyj (mem_piece B hB_cover y)]
  rw [glueDist_base_congr (B := B) (p := p) hxi hyj]

end MetricAmalgamation

/- accepted add_to_file helper 3 -/
namespace MetricAmalgamation

variable {X : Type*} {I : Type*} [MetricSpace X]
variable {B : I → Set X}
variable {hB_disjoint : (Set.univ : Set I).PairwiseDisjoint B}
variable {hB_cover : (⋃ i, B i) = Set.univ}
variable {p : ∀ i, B i}
variable {e : ∀ i, MetricSpace (B i)}

include hB_disjoint hB_cover in
lemma glueDist_comm (x y : X) :
    glueDist B hB_cover p e x y = glueDist B hB_cover p e y x := by
  set i := pieceIndex B hB_cover x
  set j := pieceIndex B hB_cover y
  by_cases hij : i = j
  · let xb : B i := piecePoint B hB_cover x
    let yb : B i := ⟨y, by
      have hyj := mem_piece B hB_cover y
      change y ∈ B j at hyj
      simpa [hij] using hyj⟩
    have hxy0 := glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
      (hB_cover := hB_cover) (p := p) (e := e) i xb yb
    have hyx0 := glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
      (hB_cover := hB_cover) (p := p) (e := e) i yb xb
    have hxy : glueDist B hB_cover p e x y =
        @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb := by
      simpa [xb, yb, piecePoint] using hxy0
    have hyx : glueDist B hB_cover p e y x =
        @dist (B i) (e i).toPseudoMetricSpace.toDist yb xb := by
      simpa [xb, yb, piecePoint] using hyx0
    rw [hxy, hyx]
    exact @dist_comm (B i) (e i).toPseudoMetricSpace xb yb
  · let xb : B i := piecePoint B hB_cover x
    let yb : B j := piecePoint B hB_cover y
    have hxy0 := glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
      (hB_cover := hB_cover) (p := p) (e := e) hij xb yb
    have hyx0 := glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
      (hB_cover := hB_cover) (p := p) (e := e) (Ne.symm hij) yb xb
    have hxy : glueDist B hB_cover p e x y =
        @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
          dist (p i : X) (p j : X) +
            @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
      simpa [xb, yb, piecePoint] using hxy0
    have hyx : glueDist B hB_cover p e y x =
        @dist (B j) (e j).toPseudoMetricSpace.toDist yb (p j) +
          dist (p j : X) (p i : X) +
            @dist (B i) (e i).toPseudoMetricSpace.toDist (p i) xb := by
      simpa [xb, yb, piecePoint] using hyx0
    rw [hxy, hyx]
    rw [@dist_comm (B i) (e i).toPseudoMetricSpace xb (p i)]
    rw [dist_comm (p i : X) (p j : X)]
    rw [@dist_comm (B j) (e j).toPseudoMetricSpace (p j) yb]
    ring

include hB_disjoint hB_cover in
lemma glueDist_triangle (x y z : X) :
    glueDist B hB_cover p e x z ≤
      glueDist B hB_cover p e x y + glueDist B hB_cover p e y z := by
  set i := pieceIndex B hB_cover x
  set j := pieceIndex B hB_cover y
  set k := pieceIndex B hB_cover z
  let xb : B i := piecePoint B hB_cover x
  let yb : B j := piecePoint B hB_cover y
  let zb : B k := piecePoint B hB_cover z
  by_cases hik : i = k
  · let zb_i : B i := ⟨z, by
      have hz := mem_piece B hB_cover z
      change z ∈ B k at hz
      simpa [hik] using hz⟩
    by_cases hij : i = j
    · let yb_i : B i := ⟨y, by
        have hy := mem_piece B hB_cover y
        change y ∈ B j at hy
        simpa [hij] using hy⟩
      have hxz : glueDist B hB_cover p e x z =
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb zb_i := by
        simpa [xb, zb_i, piecePoint] using
          glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) i xb zb_i
      have hxy : glueDist B hB_cover p e x y =
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb_i := by
        simpa [xb, yb_i, piecePoint] using
          glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) i xb yb_i
      have hyz : glueDist B hB_cover p e y z =
          @dist (B i) (e i).toPseudoMetricSpace.toDist yb_i zb_i := by
        simpa [yb_i, zb_i, piecePoint] using
          glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) i yb_i zb_i
      rw [hxz, hxy, hyz]
      exact @dist_triangle (B i) (e i).toPseudoMetricSpace xb yb_i zb_i
    · have hxy : glueDist B hB_cover p e x y =
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
            dist (p i : X) (p j : X) +
              @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
        simpa [xb, yb, piecePoint] using
          glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) hij xb yb
      have hyz : glueDist B hB_cover p e y z =
          @dist (B j) (e j).toPseudoMetricSpace.toDist yb (p j) +
            dist (p j : X) (p i : X) +
              @dist (B i) (e i).toPseudoMetricSpace.toDist (p i) zb_i := by
        simpa [yb, zb_i, piecePoint] using
          glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) (Ne.symm hij) yb zb_i
      have hxz : glueDist B hB_cover p e x z =
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb zb_i := by
        simpa [xb, zb_i, piecePoint] using
          glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) i xb zb_i
      rw [hxz, hxy, hyz]
      have htri : @dist (B i) (e i).toPseudoMetricSpace.toDist xb zb_i ≤
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
            @dist (B i) (e i).toPseudoMetricSpace.toDist (p i) zb_i :=
        @dist_triangle (B i) (e i).toPseudoMetricSpace xb (p i) zb_i
      have h₁ : 0 ≤ dist (p i : X) (p j : X) := dist_nonneg
      have h₂ : 0 ≤ @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb :=
        @dist_nonneg (B j) (e j).toPseudoMetricSpace (p j) yb
      have h₃ : 0 ≤ @dist (B j) (e j).toPseudoMetricSpace.toDist yb (p j) :=
        @dist_nonneg (B j) (e j).toPseudoMetricSpace yb (p j)
      have h₄ : 0 ≤ dist (p j : X) (p i : X) := dist_nonneg
      nlinarith
  · by_cases hij : i = j
    · let yb_i : B i := ⟨y, by
        have hy := mem_piece B hB_cover y
        change y ∈ B j at hy
        simpa [hij] using hy⟩
      have hxz : glueDist B hB_cover p e x z =
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
            dist (p i : X) (p k : X) +
              @dist (B k) (e k).toPseudoMetricSpace.toDist (p k) zb := by
        simpa [xb, zb, piecePoint] using
          glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) hik xb zb
      have hxy : glueDist B hB_cover p e x y =
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb_i := by
        simpa [xb, yb_i, piecePoint] using
          glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) i xb yb_i
      have hyz : glueDist B hB_cover p e y z =
          @dist (B i) (e i).toPseudoMetricSpace.toDist yb_i (p i) +
            dist (p i : X) (p k : X) +
              @dist (B k) (e k).toPseudoMetricSpace.toDist (p k) zb := by
        simpa [yb_i, zb, piecePoint] using
          glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) hik yb_i zb
      rw [hxz, hxy, hyz]
      have htri : @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) ≤
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb_i +
            @dist (B i) (e i).toPseudoMetricSpace.toDist yb_i (p i) :=
        @dist_triangle (B i) (e i).toPseudoMetricSpace xb yb_i (p i)
      nlinarith
    · by_cases hjk : j = k
      · let zb_j : B j := ⟨z, by
          have hz := mem_piece B hB_cover z
          change z ∈ B k at hz
          simpa [hjk] using hz⟩
        have hxz : glueDist B hB_cover p e x z =
            @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
              dist (p i : X) (p j : X) +
                @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) zb_j := by
          have hij' : i ≠ j := by
            intro h
            exact hik (h.trans hjk)
          simpa [xb, zb_j, piecePoint] using
            glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
              (hB_cover := hB_cover) (p := p) (e := e) hij' xb zb_j
        have hxy : glueDist B hB_cover p e x y =
            @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
              dist (p i : X) (p j : X) +
                @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
          simpa [xb, yb, piecePoint] using
            glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
              (hB_cover := hB_cover) (p := p) (e := e) hij xb yb
        have hyz : glueDist B hB_cover p e y z =
            @dist (B j) (e j).toPseudoMetricSpace.toDist yb zb_j := by
          simpa [yb, zb_j, piecePoint] using
            glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
              (hB_cover := hB_cover) (p := p) (e := e) j yb zb_j
        rw [hxz, hxy, hyz]
        have htri : @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) zb_j ≤
            @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb +
              @dist (B j) (e j).toPseudoMetricSpace.toDist yb zb_j :=
          @dist_triangle (B j) (e j).toPseudoMetricSpace (p j) yb zb_j
        nlinarith
      · have hxz : glueDist B hB_cover p e x z =
            @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
              dist (p i : X) (p k : X) +
                @dist (B k) (e k).toPseudoMetricSpace.toDist (p k) zb := by
          simpa [xb, zb, piecePoint] using
            glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
              (hB_cover := hB_cover) (p := p) (e := e) hik xb zb
        have hxy : glueDist B hB_cover p e x y =
            @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
              dist (p i : X) (p j : X) +
                @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
          simpa [xb, yb, piecePoint] using
            glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
              (hB_cover := hB_cover) (p := p) (e := e) hij xb yb
        have hyz : glueDist B hB_cover p e y z =
            @dist (B j) (e j).toPseudoMetricSpace.toDist yb (p j) +
              dist (p j : X) (p k : X) +
                @dist (B k) (e k).toPseudoMetricSpace.toDist (p k) zb := by
          simpa [yb, zb, piecePoint] using
            glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
              (hB_cover := hB_cover) (p := p) (e := e) hjk yb zb
        rw [hxz, hxy, hyz]
        have hbase : dist (p i : X) (p k : X) ≤
            dist (p i : X) (p j : X) + dist (p j : X) (p k : X) :=
          dist_triangle (p i : X) (p j : X) (p k : X)
        have h₁ : 0 ≤ @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb :=
          @dist_nonneg (B j) (e j).toPseudoMetricSpace (p j) yb
        have h₂ : 0 ≤ @dist (B j) (e j).toPseudoMetricSpace.toDist yb (p j) :=
          @dist_nonneg (B j) (e j).toPseudoMetricSpace yb (p j)
        nlinarith

end MetricAmalgamation

/- accepted add_to_file helper 4 -/
namespace MetricAmalgamation

variable {X : Type*} {I : Type*} [MetricSpace X]
variable {B : I → Set X}
variable {hB_disjoint : (Set.univ : Set I).PairwiseDisjoint B}
variable {hB_cover : (⋃ i, B i) = Set.univ}
variable {p : ∀ i, B i}
variable {e : ∀ i, MetricSpace (B i)}

lemma glueDist_self (x : X) : glueDist B hB_cover p e x x = 0 := by
  simp [glueDist, piecePoint]

include hB_disjoint hB_cover in
lemma eq_of_glueDist_eq_zero {x y : X}
    (h : glueDist B hB_cover p e x y = 0) : x = y := by
  set i := pieceIndex B hB_cover x
  set j := pieceIndex B hB_cover y
  by_cases hij : i = j
  · let xb : B i := piecePoint B hB_cover x
    let yb : B i := ⟨y, by
      have hyj := mem_piece B hB_cover y
      change y ∈ B j at hyj
      simpa [hij] using hyj⟩
    have hxy : glueDist B hB_cover p e x y =
        @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb := by
      simpa [xb, yb, piecePoint] using
        glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
          (hB_cover := hB_cover) (p := p) (e := e) i xb yb
    rw [hxy] at h
    have hsub : xb = yb := @eq_of_dist_eq_zero (B i) (e i) xb yb h
    have hval : (xb : X) = (yb : X) := congrArg Subtype.val hsub
    simpa [xb, yb, piecePoint] using hval
  · let xb : B i := piecePoint B hB_cover x
    let yb : B j := piecePoint B hB_cover y
    have hxy : glueDist B hB_cover p e x y =
        @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
          dist (p i : X) (p j : X) +
            @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
      simpa [xb, yb, piecePoint] using
        glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
          (hB_cover := hB_cover) (p := p) (e := e) hij xb yb
    rw [hxy] at h
    have ha : 0 ≤ @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) :=
      @dist_nonneg (B i) (e i).toPseudoMetricSpace xb (p i)
    have hb : 0 ≤ @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb :=
      @dist_nonneg (B j) (e j).toPseudoMetricSpace (p j) yb
    have hc0 : dist (p i : X) (p j : X) ≤ 0 := by
      have hc : dist (p i : X) (p j : X) ≤
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
            dist (p i : X) (p j : X) +
              @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
        nlinarith
      rwa [h] at hc
    have hc : dist (p i : X) (p j : X) = 0 := le_antisymm hc0 dist_nonneg
    have hp : (p i : X) = (p j : X) := eq_of_dist_eq_zero hc
    have hd : Disjoint (B i) (B j) :=
      hB_disjoint (Set.mem_univ i) (Set.mem_univ j) hij
    exact False.elim
      (Set.disjoint_iff_forall_ne.mp hd (p i).property (p j).property hp)

end MetricAmalgamation

/- accepted add_to_file helper 5 -/
namespace MetricAmalgamation

variable {X : Type*} {I : Type*} [MetricSpace X]
variable {B : I → Set X}
variable {hB_disjoint : (Set.univ : Set I).PairwiseDisjoint B}
variable {hB_clopen : ∀ i, IsClopen (B i)}
variable {hB_cover : (⋃ i, B i) = Set.univ}
variable {p : ∀ i, B i}
variable {e : ∀ i, MetricSpace (B i)}
variable {he_top : ∀ i,
  (e i).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
    (inferInstance : TopologicalSpace (B i))}

include hB_disjoint hB_clopen hB_cover he_top in
lemma glueDist_topology (s : Set X) :
    IsOpen s ↔ ∀ x ∈ s, ∃ δ > 0, ∀ y,
      glueDist B hB_cover p e x y < δ → y ∈ s := by
  constructor
  · intro hs x hxs
    set i := pieceIndex B hB_cover x
    let xb : B i := piecePoint B hB_cover x
    let t : Set (B i) := Subtype.val ⁻¹' s
    have ht_old : IsOpen t := continuous_subtype_val.isOpen_preimage s hs
    have ht_e : @IsOpen (B i)
        (e i).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace t := by
      rw [he_top i]
      exact ht_old
    have hx_t : xb ∈ t := by
      change (xb : X) ∈ s
      simpa [xb, piecePoint] using hxs
    rcases (@Metric.isOpen_iff (B i) (e i).toPseudoMetricSpace t).mp ht_e xb hx_t with
      ⟨r, hr, hball⟩
    have hBi : IsOpen (B i) := (hB_clopen i).isOpen
    rcases Metric.isOpen_iff.mp hBi (p i : X) (p i).property with ⟨η, hη, hηsub⟩
    refine ⟨min r η, lt_min hr hη, ?_⟩
    intro y hyD
    set j := pieceIndex B hB_cover y
    let yb : B j := piecePoint B hB_cover y
    by_cases hij : i = j
    · let yb_i : B i := ⟨y, by
        have hyj := mem_piece B hB_cover y
        change y ∈ B j at hyj
        simpa [hij] using hyj⟩
      have hD : glueDist B hB_cover p e x y =
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb_i := by
        simpa [xb, yb_i, piecePoint] using
          glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) i xb yb_i
      have her : @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb_i < r := by
        rw [← hD]
        exact lt_of_lt_of_le hyD (min_le_left r η)
      have her' : @dist (B i) (e i).toPseudoMetricSpace.toDist yb_i xb < r := by
        rw [@dist_comm (B i) (e i).toPseudoMetricSpace yb_i xb]
        exact her
      have hyt : yb_i ∈ t := hball
        ((@Metric.mem_ball (B i) (e i).toPseudoMetricSpace xb yb_i r).mpr her')
      change (yb_i : X) ∈ s at hyt
      simpa [yb_i] using hyt
    · have hD : glueDist B hB_cover p e x y =
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
            dist (p i : X) (p j : X) +
              @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
        simpa [xb, yb, piecePoint] using
          glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) hij xb yb
      have ha : 0 ≤ @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) :=
        @dist_nonneg (B i) (e i).toPseudoMetricSpace xb (p i)
      have hb : 0 ≤ @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb :=
        @dist_nonneg (B j) (e j).toPseudoMetricSpace (p j) yb
      have hbase : dist (p i : X) (p j : X) < η := by
        have hle : dist (p i : X) (p j : X) ≤ glueDist B hB_cover p e x y := by
          rw [hD]
          nlinarith
        exact lt_of_le_of_lt hle (lt_of_lt_of_le hyD (min_le_right r η))
      have hbase' : dist (p j : X) (p i : X) < η := by
        rw [dist_comm]
        exact hbase
      have hpji : (p j : X) ∈ B i := hηsub (Metric.mem_ball.mpr hbase')
      have hd : Disjoint (B i) (B j) :=
        hB_disjoint (Set.mem_univ i) (Set.mem_univ j) hij
      exact False.elim
        (Set.disjoint_iff_forall_ne.mp hd hpji (p j).property rfl)
  · intro h
    rw [Metric.isOpen_iff]
    intro x hxs
    rcases h x hxs with ⟨δ, hδ, hδsub⟩
    set i := pieceIndex B hB_cover x
    let xb : B i := piecePoint B hB_cover x
    let t : Set (B i) := @Metric.ball (B i) (e i).toPseudoMetricSpace xb δ
    have ht_e : @IsOpen (B i)
        (e i).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace t := by
      exact @Metric.isOpen_ball (B i) (e i).toPseudoMetricSpace xb δ
    rw [he_top i] at ht_e
    rcases isOpen_induced_iff.mp ht_e with ⟨u, hu, hu_eq⟩
    have hx_dist : @dist (B i) (e i).toPseudoMetricSpace.toDist xb xb < δ := by
      rw [@dist_self (B i) (e i).toPseudoMetricSpace xb]
      exact hδ
    have hx_t : xb ∈ t :=
      (@Metric.mem_ball (B i) (e i).toPseudoMetricSpace xb xb δ).mpr hx_dist
    have hxu : (xb : X) ∈ u := by
      have : xb ∈ Subtype.val ⁻¹' u := by
        rw [hu_eq]
        exact hx_t
      exact this
    rcases Metric.isOpen_iff.mp hu (xb : X) hxu with ⟨ru, hru, hrusub⟩
    have hBi : IsOpen (B i) := (hB_clopen i).isOpen
    have hxBi : (xb : X) ∈ B i := by
      simpa [xb, piecePoint] using mem_piece B hB_cover x
    rcases Metric.isOpen_iff.mp hBi (xb : X) hxBi with ⟨rB, hrB, hrBsub⟩
    refine ⟨min ru rB, lt_min hru hrB, ?_⟩
    intro y hy
    have hyu : y ∈ u := hrusub (Metric.mem_ball.mpr
      (lt_of_lt_of_le hy (min_le_left ru rB)))
    have hyBi : y ∈ B i := hrBsub (Metric.mem_ball.mpr
      (lt_of_lt_of_le hy (min_le_right ru rB)))
    let yb : B i := ⟨y, hyBi⟩
    have hyt : yb ∈ t := by
      have : yb ∈ Subtype.val ⁻¹' u := hyu
      rwa [hu_eq] at this
    have helt : @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb < δ := by
      have hd : @dist (B i) (e i).toPseudoMetricSpace.toDist yb xb < δ :=
        (@Metric.mem_ball (B i) (e i).toPseudoMetricSpace xb yb δ).mp hyt
      rw [@dist_comm (B i) (e i).toPseudoMetricSpace yb xb] at hd
      exact hd
    have hD : glueDist B hB_cover p e x y =
        @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb := by
      simpa [xb, yb, piecePoint] using
        glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
          (hB_cover := hB_cover) (p := p) (e := e) i xb yb
    apply hδsub y
    rw [hD]
    exact helt

end MetricAmalgamation

/- accepted add_to_file helper 6 -/
namespace MetricAmalgamation

variable {X : Type*} {I : Type*} [MetricSpace X]
variable {B : I → Set X}
variable {hB_disjoint : (Set.univ : Set I).PairwiseDisjoint B}
variable {hB_clopen : ∀ i, IsClopen (B i)}
variable {hB_cover : (⋃ i, B i) = Set.univ}
variable {p : ∀ i, B i}
variable {e : ∀ i, MetricSpace (B i)}
variable {he_top : ∀ i,
  (e i).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
    (inferInstance : TopologicalSpace (B i))}

include hB_disjoint hB_clopen hB_cover he_top in
@[implicit_reducible] noncomputable def glueMetricSpace : MetricSpace X :=
  MetricSpace.ofDistTopology (glueDist B hB_cover p e)
    (glueDist_self (B := B) (hB_cover := hB_cover) (p := p) (e := e))
    (glueDist_comm (B := B) (hB_disjoint := hB_disjoint) (hB_cover := hB_cover)
      (p := p) (e := e))
    (glueDist_triangle (B := B) (hB_disjoint := hB_disjoint) (hB_cover := hB_cover)
      (p := p) (e := e))
    (glueDist_topology (B := B) (hB_disjoint := hB_disjoint)
      (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
      (he_top := he_top))
    (fun x y h => eq_of_glueDist_eq_zero (B := B) (hB_disjoint := hB_disjoint)
      (hB_cover := hB_cover) (p := p) (e := e) h)

include hB_disjoint hB_clopen hB_cover he_top in
lemma dist_glueMetricSpace (x y : X) :
    @dist X (glueMetricSpace (B := B) (hB_disjoint := hB_disjoint)
      (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
      (he_top := he_top)).toPseudoMetricSpace.toDist x y =
      glueDist B hB_cover p e x y :=
  rfl

include hB_disjoint hB_clopen hB_cover he_top in
lemma glueMetricSpace_topology :
    (glueMetricSpace (B := B) (hB_disjoint := hB_disjoint)
      (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
      (he_top := he_top)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace X) :=
  rfl

end MetricAmalgamation

/- accepted add_to_file helper 7 -/
namespace MetricAmalgamation

lemma dist_le_of_ediam_le_ofReal {α : Type*} [PseudoMetricSpace α]
    {s : Set α} {ε : ℝ} (hε : 0 ≤ ε)
    (hs : Metric.ediam s ≤ ENNReal.ofReal ε)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) : dist x y ≤ ε := by
  have hed : edist x y ≤ Metric.ediam s := Metric.edist_le_ediam_of_mem hx hy
  have hof : ENNReal.ofReal (dist x y) ≤ ENNReal.ofReal ε := by
    rw [← edist_dist]
    exact hed.trans hs
  exact (ENNReal.ofReal_le_ofReal_iff hε).mp hof

end MetricAmalgamation

/- accepted add_to_file helper 8 -/
namespace MetricAmalgamation

lemma dist_le_of_ediam_le_ofReal_explicit {α : Type*} (m : PseudoMetricSpace α)
    {s : Set α} {ε : ℝ} (hε : 0 ≤ ε)
    (hs : @Metric.ediam α m.toPseudoEMetricSpace s ≤ ENNReal.ofReal ε)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
    @dist α m.toDist x y ≤ ε := by
  have hed : @edist α m.toPseudoEMetricSpace.toEDist x y ≤
      @Metric.ediam α m.toPseudoEMetricSpace s :=
    @Metric.edist_le_ediam_of_mem α s x y m.toPseudoEMetricSpace hx hy
  have hof : ENNReal.ofReal (@dist α m.toDist x y) ≤ ENNReal.ofReal ε := by
    rw [← @edist_dist α m x y]
    exact hed.trans hs
  exact (ENNReal.ofReal_le_ofReal_iff hε).mp hof

end MetricAmalgamation

/- accepted add_to_file helper 9 -/
namespace MetricAmalgamation

variable {X : Type*} {I : Type*} [MetricSpace X]
variable {B : I → Set X}
variable {hB_disjoint : (Set.univ : Set I).PairwiseDisjoint B}
variable {hB_clopen : ∀ i, IsClopen (B i)}
variable {hB_cover : (⋃ i, B i) = Set.univ}
variable {p : ∀ i, B i}
variable {e : ∀ i, MetricSpace (B i)}
variable {he_top : ∀ i,
  (e i).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
    (inferInstance : TopologicalSpace (B i))}

include hB_disjoint hB_clopen hB_cover he_top in
lemma dist_glueMetricSpace_error_le (ε : ℝ) (hε : 0 ≤ ε)
    (hdiam : ∀ i, Metric.ediam (B i) ≤ ENNReal.ofReal ε)
    (hediam : ∀ i,
      @Metric.ediam (B i) (e i).toPseudoMetricSpace.toPseudoEMetricSpace
        Set.univ ≤ ENNReal.ofReal ε)
    (x y : X) :
    |@dist X (glueMetricSpace (B := B) (hB_disjoint := hB_disjoint)
      (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
      (he_top := he_top)).toPseudoMetricSpace.toDist x y - dist x y| ≤
        4 * ε := by
  set i := pieceIndex B hB_cover x
  set j := pieceIndex B hB_cover y
  let xb : B i := piecePoint B hB_cover x
  let yb : B j := piecePoint B hB_cover y
  have hD0 : @dist X (glueMetricSpace (B := B) (hB_disjoint := hB_disjoint)
      (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
      (he_top := he_top)).toPseudoMetricSpace.toDist x y =
      glueDist B hB_cover p e x y :=
    dist_glueMetricSpace (B := B) (hB_disjoint := hB_disjoint)
      (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
      (he_top := he_top) x y
  by_cases hij : i = j
  · let yb_i : B i := ⟨y, by
      have hyj := mem_piece B hB_cover y
      change y ∈ B j at hyj
      simpa [hij] using hyj⟩
    have hD : @dist X (glueMetricSpace (B := B) (hB_disjoint := hB_disjoint)
        (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
        (he_top := he_top)).toPseudoMetricSpace.toDist x y =
        @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb_i := by
      rw [hD0]
      simpa [xb, yb_i, piecePoint] using
        glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
          (hB_cover := hB_cover) (p := p) (e := e) i xb yb_i
    rw [hD]
    have hdxy : dist x y ≤ ε := by
      exact dist_le_of_ediam_le_ofReal (s := B i) hε (hdiam i)
        (by simpa [xb, piecePoint] using mem_piece B hB_cover x)
        (by simpa [yb_i] using yb_i.property)
    have hexy : @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb_i ≤ ε := by
      exact dist_le_of_ediam_le_ofReal_explicit (e i).toPseudoMetricSpace
        (s := Set.univ) hε (hediam i) (Set.mem_univ xb) (Set.mem_univ yb_i)
    have hd0 : 0 ≤ dist x y := dist_nonneg
    have he0 : 0 ≤ @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb_i :=
      @dist_nonneg (B i) (e i).toPseudoMetricSpace xb yb_i
    rw [abs_sub_le_iff]
    constructor <;> nlinarith
  · have hD : @dist X (glueMetricSpace (B := B) (hB_disjoint := hB_disjoint)
        (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
        (he_top := he_top)).toPseudoMetricSpace.toDist x y =
        @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
          dist (p i : X) (p j : X) +
            @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
      rw [hD0]
      simpa [xb, yb, piecePoint] using
        glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
          (hB_cover := hB_cover) (p := p) (e := e) hij xb yb
    rw [hD]
    have hd_xp : dist x (p i : X) ≤ ε :=
      dist_le_of_ediam_le_ofReal (s := B i) hε (hdiam i)
        (by simpa [xb, piecePoint] using mem_piece B hB_cover x) (p i).property
    have hd_py : dist (p j : X) y ≤ ε :=
      dist_le_of_ediam_le_ofReal (s := B j) hε (hdiam j)
        (p j).property (by simpa [yb, piecePoint] using mem_piece B hB_cover y)
    have he_xp : @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) ≤ ε :=
      dist_le_of_ediam_le_ofReal_explicit (e i).toPseudoMetricSpace
        (s := Set.univ) hε (hediam i) (Set.mem_univ xb) (Set.mem_univ (p i))
    have he_py : @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb ≤ ε :=
      dist_le_of_ediam_le_ofReal_explicit (e j).toPseudoMetricSpace
        (s := Set.univ) hε (hediam j) (Set.mem_univ (p j)) (Set.mem_univ yb)
    have hupper : @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
        dist (p i : X) (p j : X) +
          @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb -
            dist x y ≤ 4 * ε := by
      have hc : dist (p i : X) (p j : X) ≤
          dist (p i : X) x + dist x y + dist y (p j : X) := by
        calc
          dist (p i : X) (p j : X) ≤ dist (p i : X) x + dist x (p j : X) :=
            dist_triangle _ _ _
          _ ≤ (dist (p i : X) x + dist x y) + dist y (p j : X) := by
            have := dist_triangle x y (p j : X)
            nlinarith
      have hxpi : dist (p i : X) x ≤ ε := by simpa [dist_comm] using hd_xp
      have hypj : dist y (p j : X) ≤ ε := by simpa [dist_comm] using hd_py
      nlinarith
    have hlower : dist x y -
        (@dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
          dist (p i : X) (p j : X) +
            @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb) ≤
          4 * ε := by
      have hd : dist x y ≤
          dist x (p i : X) + dist (p i : X) (p j : X) + dist (p j : X) y := by
        calc
          dist x y ≤ dist x (p i : X) + dist (p i : X) y := dist_triangle _ _ _
          _ ≤ dist x (p i : X) +
              (dist (p i : X) (p j : X) + dist (p j : X) y) := by
            have := dist_triangle (p i : X) (p j : X) y
            nlinarith
          _ = dist x (p i : X) + dist (p i : X) (p j : X) +
              dist (p j : X) y := by ring
      have hc_nonneg : dist (p i : X) (p j : X) ≤
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
            dist (p i : X) (p j : X) +
              @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
        have h1 := @dist_nonneg (B i) (e i).toPseudoMetricSpace xb (p i)
        have h2 := @dist_nonneg (B j) (e j).toPseudoMetricSpace (p j) yb
        nlinarith
      nlinarith
    exact abs_sub_le_iff.mpr ⟨hupper, hlower⟩

end MetricAmalgamation

/- verified submission -/
theorem metric_amalgamation
    {X : Type*} {I : Type*} [MetricSpace X]
    (B : I → Set X)
    (hB_disjoint : (Set.univ : Set I).PairwiseDisjoint B)
    (hB_clopen : ∀ i, IsClopen (B i))
    (hB_cover : (⋃ i, B i) = Set.univ)
    (p : ∀ i, B i)
    (e : ∀ i, MetricSpace (B i))
    (he_top : ∀ i,
      (e i).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace (B i))) :
    ∃ mD : MetricSpace X,
      (∀ (i : I) (x y : B i),
        @dist X mD.toPseudoMetricSpace.toDist x y =
          @dist (B i) (e i).toPseudoMetricSpace.toDist x y) ∧
      (∀ (i j : I), i ≠ j → ∀ (x : B i) (y : B j),
        @dist X mD.toPseudoMetricSpace.toDist x y =
          @dist (B i) (e i).toPseudoMetricSpace.toDist x (p i) +
            dist (p i : X) (p j : X) +
              @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) y) ∧
      mD.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace X) ∧
      ∀ ε : ℝ, 0 ≤ ε →
        ((∀ i, Metric.ediam (B i) ≤ ENNReal.ofReal ε) ∧
          (∀ i, @Metric.ediam (B i)
            (e i).toPseudoMetricSpace.toPseudoEMetricSpace Set.univ ≤
              ENNReal.ofReal ε)) →
        sSup (Set.range (fun q : X × X =>
          |@dist X mD.toPseudoMetricSpace.toDist q.1 q.2 - dist q.1 q.2|)) ≤
            4 * ε := by
  classical
  refine ⟨MetricAmalgamation.glueMetricSpace (B := B) (hB_disjoint := hB_disjoint)
    (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
    (he_top := he_top), ?_, ?_, ?_, ?_⟩
  · intro i x y
    exact (MetricAmalgamation.dist_glueMetricSpace (B := B)
      (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
      (hB_cover := hB_cover) (p := p) (e := e) (he_top := he_top) x y).trans
      (MetricAmalgamation.glueDist_subtype_same (B := B)
        (hB_disjoint := hB_disjoint) (hB_cover := hB_cover) (p := p) (e := e) i x y)
  · intro i j hij x y
    have hmain := (MetricAmalgamation.dist_glueMetricSpace (B := B)
      (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
      (hB_cover := hB_cover) (p := p) (e := e) (he_top := he_top) x y).trans
      (MetricAmalgamation.glueDist_subtype_ne (B := B)
        (hB_disjoint := hB_disjoint) (hB_cover := hB_cover) (p := p) (e := e)
        hij x y)
    have hpp0 := (MetricAmalgamation.dist_glueMetricSpace (B := B)
      (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
      (hB_cover := hB_cover) (p := p) (e := e) (he_top := he_top)
      (p i) (p j)).trans
      (MetricAmalgamation.glueDist_subtype_ne (B := B)
        (hB_disjoint := hB_disjoint) (hB_cover := hB_cover) (p := p) (e := e)
        hij (p i) (p j))
    have hpp : @dist X (MetricAmalgamation.glueMetricSpace (B := B)
        (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
        (hB_cover := hB_cover) (p := p) (e := e)
        (he_top := he_top)).toPseudoMetricSpace.toDist (p i : X) (p j : X) =
        dist (p i : X) (p j : X) := by
      calc
        @dist X (MetricAmalgamation.glueMetricSpace (B := B)
          (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
          (hB_cover := hB_cover) (p := p) (e := e)
          (he_top := he_top)).toPseudoMetricSpace.toDist (p i : X) (p j : X)
            = @dist (B i) (e i).toPseudoMetricSpace.toDist (p i) (p i) +
              dist (p i : X) (p j : X) +
                @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) (p j) := hpp0
        _ = dist (p i : X) (p j : X) := by
          rw [@dist_self (B i) (e i).toPseudoMetricSpace (p i)]
          rw [@dist_self (B j) (e j).toPseudoMetricSpace (p j)]
          ring
    calc
      @dist X (MetricAmalgamation.glueMetricSpace (B := B)
        (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
        (hB_cover := hB_cover) (p := p) (e := e)
        (he_top := he_top)).toPseudoMetricSpace.toDist x y
          = @dist (B i) (e i).toPseudoMetricSpace.toDist x (p i) +
            dist (p i : X) (p j : X) +
              @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) y := hmain
      _ = @dist (B i) (e i).toPseudoMetricSpace.toDist x (p i) +
          @dist X (MetricAmalgamation.glueMetricSpace (B := B)
            (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
            (hB_cover := hB_cover) (p := p) (e := e)
            (he_top := he_top)).toPseudoMetricSpace.toDist (p i : X) (p j : X) +
          @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) y := by
        rw [hpp]
  · exact MetricAmalgamation.glueMetricSpace_topology (B := B)
      (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
      (hB_cover := hB_cover) (p := p) (e := e) (he_top := he_top)
  · intro ε hε hdiam
    let mD : MetricSpace X := MetricAmalgamation.glueMetricSpace (B := B)
      (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
      (hB_cover := hB_cover) (p := p) (e := e) (he_top := he_top)
    change sSup (Set.range (fun q : X × X =>
      |@dist X mD.toPseudoMetricSpace.toDist q.1 q.2 -
        @dist X mD.toPseudoMetricSpace.toDist q.1 q.2|)) ≤ 4 * ε
    by_cases hX : Nonempty X
    · rcases hX with ⟨x⟩
      apply csSup_le
      · exact ⟨|@dist X mD.toPseudoMetricSpace.toDist x x -
          @dist X mD.toPseudoMetricSpace.toDist x x|, ⟨(x, x), rfl⟩⟩
      · intro b hb
        rcases hb with ⟨q, rfl⟩
        simp
        nlinarith
    · haveI : IsEmpty X := not_nonempty_iff.mp hX
      haveI : IsEmpty (X × X) := inferInstance
      rw [Set.range_eq_empty, Real.sSup_empty]
      nlinarith

end Rollout_p2075_metric_amalgamation

namespace Rollout_p1530_inverse_along_mem_bicommutant

/- verified submission -/
theorem inverse_along_mem_bicommutant {S : Type*} [Semigroup S] {a d b : S}
    (hbad : b * a * d = d) (hdab : d * a * b = d)
    (hbd : ∃ x y : S, b = d * x ∧ b = y * d) :
    ∀ c : S, c * a = a * c → c * d = d * c → c * b = b * c := by
  rcases hbd with ⟨x, y, hbx, hby⟩
  intro c hca hcd
  have hyad : y * d * a * d = d := by
    simpa [hby] using hbad
  have hdadx : d * a * d * x = d := by
    simpa [hbx, mul_assoc] using hdab
  calc
    c * b = d * c * x := by
      calc
        c * b = c * (d * x) := by rw [hbx]
        _ = c * d * x := by rw [mul_assoc]
        _ = d * c * x := by rw [hcd]
    _ = y * d * a * d * c * x := by
      rw [hyad]
    _ = y * d * a * c * d * x := by
      have h : y * d * a * (d * c) * x = y * d * a * (c * d) * x := by
        rw [hcd]
      simpa [mul_assoc] using h
    _ = y * d * c * a * d * x := by
      have h : y * d * (a * c) * d * x = y * d * (c * a) * d * x := by
        rw [← hca]
      simpa [mul_assoc] using h
    _ = y * c * d * a * d * x := by
      have h : y * (d * c) * a * d * x = y * (c * d) * a * d * x := by
        rw [hcd]
      simpa [mul_assoc] using h
    _ = y * c * d := by
      have h : y * c * (d * a * d * x) = y * c * d := by
        rw [hdadx]
      simpa [mul_assoc] using h
    _ = y * d * c := by
      rw [mul_assoc, hcd, ← mul_assoc]
    _ = b * c := by
      rw [← hby]

end Rollout_p1530_inverse_along_mem_bicommutant

namespace Rollout_p0229_euclidean_decomposition_bound

/- verified submission -/
theorem euclidean_decomposition_bound (n e p : ℕ) (hn : 0 < n) (he : 0 < e)
    (hp : Nat.Prime p) (hsize : 4 * p ^ 2 ≤ n + 2) (hep : e ≤ p + 1) :
    ∃ d f : ℕ, f < p ∧ n + 2 = p * d + f + e ∧
      d ≥ e + f + (2 * p - 2) := by
  have hp0 : 0 < p := hp.pos
  have hp2 : 2 ≤ p := hp.two_le
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hp2
  have hm : e ≤ n + 2 := by
    have hp_sq : 2 + q + 1 ≤ 4 * (2 + q) ^ 2 := by
      nlinarith
    exact le_trans hep (le_trans hp_sq hsize)
  let d := (n + 2 - e) / (2 + q)
  let f := (n + 2 - e) % (2 + q)
  have hf : f < 2 + q := by
    dsimp [f]
    exact Nat.mod_lt _ (by omega)
  have hdiv : (2 + q) * d + f = n + 2 - e := by
    dsimp [d, f]
    exact Nat.div_add_mod (n + 2 - e) (2 + q)
  have hdecomp : n + 2 = (2 + q) * d + f + e := by
    calc
      n + 2 = (n + 2 - e) + e := (Nat.sub_add_cancel hm).symm
      _ = ((2 + q) * d + f) + e := by rw [hdiv]
      _ = (2 + q) * d + f + e := rfl
  have hd4 : 4 * (2 + q) - 2 ≤ d := by
    dsimp [d]
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2 + q)).mpr
    have hmul : (4 * (2 + q) - 2) * (2 + q) ≤ n + 2 - e := by
      apply (Nat.le_sub_iff_add_le hm).mpr
      have hsub : 4 * (2 + q) - 2 = 6 + 4 * q := by omega
      rw [hsub]
      nlinarith
    exact hmul
  refine ⟨d, f, hf, hdecomp, ?_⟩
  have htarget : e + f + (2 * (2 + q) - 2) ≤ 4 * (2 + q) - 2 := by
    omega
  exact le_trans htarget hd4

end Rollout_p0229_euclidean_decomposition_bound

namespace Rollout_p2112_diagonal_nonnegative_part_difference

/- verified submission -/
lemma positive_part_secant_aux (x y : ℝ) :
    ∃ ω : ℝ, 0 ≤ ω ∧ ω ≤ 1 ∧
      (if 0 ≤ x then (1 : ℝ) else 0) * x -
        (if 0 ≤ y then (1 : ℝ) else 0) * y = ω * (x - y) := by
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · refine ⟨1, by norm_num, by norm_num, ?_⟩
      simp [hx, hy]
    · have hy_lt : y < 0 := lt_of_not_ge hy
      have hden : 0 < x - y := sub_pos.mpr (lt_of_lt_of_le hy_lt hx)
      refine ⟨x / (x - y), ?_, ?_, ?_⟩
      · exact div_nonneg hx (le_of_lt hden)
      · rw [div_le_one hden]
        nlinarith
      · simp [hx, hy]
        exact (div_mul_cancel₀ x (ne_of_gt hden)).symm
  · have hx_lt : x < 0 := lt_of_not_ge hx
    by_cases hy : 0 ≤ y
    · have hden : 0 < y - x := sub_pos.mpr (lt_of_lt_of_le hx_lt hy)
      refine ⟨y / (y - x), ?_, ?_, ?_⟩
      · exact div_nonneg hy (le_of_lt hden)
      · rw [div_le_one hden]
        nlinarith
      · simp [hx, hy]
        field_simp [ne_of_gt hden]
        ring
    · refine ⟨0, by norm_num, by norm_num, ?_⟩
      simp [hx, hy]

theorem diagonal_nonnegative_part_difference
    (n : ℕ) (hn : 0 < n) (x y : Fin n → ℝ) :
    let P : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ :=
      fun z => Matrix.diagonal (fun i => if 0 ≤ z i then 1 else 0)
    ∃ ω : Fin n → ℝ,
      (∀ i, 0 ≤ ω i ∧ ω i ≤ 1) ∧
        Matrix.mulVec (P x) x - Matrix.mulVec (P y) y =
          Matrix.mulVec (Matrix.diagonal ω) (x - y) := by
  let P : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ :=
    fun z => Matrix.diagonal (fun i => if 0 ≤ z i then 1 else 0)
  let ω : Fin n → ℝ :=
    fun i => Classical.choose (positive_part_secant_aux (x i) (y i))
  have hω : ∀ i : Fin n,
      0 ≤ ω i ∧ ω i ≤ 1 ∧
        (if 0 ≤ x i then (1 : ℝ) else 0) * x i -
          (if 0 ≤ y i then (1 : ℝ) else 0) * y i = ω i * (x i - y i) := by
    intro i
    dsimp [ω]
    exact Classical.choose_spec (positive_part_secant_aux (x i) (y i))
  refine ⟨ω, ?_, ?_⟩
  · intro i
    exact ⟨(hω i).1, (hω i).2.1⟩
  · funext i
    exact (by
      simpa [P, Matrix.mulVec_diagonal, Pi.sub_apply] using (hω i).2.2 :
        (Matrix.mulVec (P x) x - Matrix.mulVec (P y) y) i =
          (Matrix.mulVec (Matrix.diagonal ω) (x - y)) i)

end Rollout_p2112_diagonal_nonnegative_part_difference

namespace Rollout_p0378_finite_g_set_subcategory_contains_all_mono

/- accepted add_to_file helper 1 -/
open CategoryTheory
open CategoryTheory.Limits
namespace FiniteGSetProof
universe u
@[reducible]
def trivialMulAction (G : Type u) [Monoid G] (A : Type) : MulAction G A where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
@[reducible]
def trivialObj (G : Type u) [Monoid G] (A : Type) [Finite A] : Action (FintypeCat.{0}) G := by
  letI : MulAction G A := trivialMulAction G A
  exact Action.FintypeCat.ofMulAction G (FintypeCat.of A)
def actionHomOfEquivariant {G : Type u} [Monoid G] {X Y : Action (FintypeCat.{0}) G}
    (φ : X.V.obj → Y.V.obj)
    (hφ : ∀ g x, φ (ConcreteCategory.hom (X.ρ g) x) = ConcreteCategory.hom (Y.ρ g) (φ x)) : X ⟶ Y where
  hom := FintypeCat.homMk φ
  comm := by intro g; ext x; exact hφ g x
lemma concreteCategoryHom_actionHomOfEquivariant {G : Type u} [Monoid G]
    {X Y : Action (FintypeCat.{0}) G} (φ : X.V.obj → Y.V.obj)
    (hφ : ∀ g x, φ (ConcreteCategory.hom (X.ρ g) x) = ConcreteCategory.hom (Y.ρ g) (φ x)) :
    ConcreteCategory.hom (actionHomOfEquivariant φ hφ : X ⟶ Y) = φ := rfl
noncomputable def toTrivialObj (G : Type u) [Monoid G] (A : Type) [Finite A] [Nonempty A]
    (X : Action (FintypeCat.{0}) G) : X ⟶ trivialObj G A :=
  let a : A := Classical.choice inferInstance
  actionHomOfEquivariant (fun _ => a) (by intro g x; rfl)
def trivialMap (G : Type u) [Monoid G] {A B : Type} [Finite A] [Finite B]
    (φ : A → B) : trivialObj G A ⟶ trivialObj G B :=
  actionHomOfEquivariant φ (by intro g x; rfl)
variable (G : Type u) [Group G]
def oneObj : Action (FintypeCat.{0}) G := trivialObj G PUnit
def twoObj : Action (FintypeCat.{0}) G := trivialObj G Bool
noncomputable def oneMap {X : Action (FintypeCat) G} : X ⟶ oneObj G := toTrivialObj G PUnit X
def truth : oneObj G ⟶ twoObj G := trivialMap G (fun _ => true)
def falsehood : oneObj G ⟶ twoObj G := trivialMap G (fun _ => false)
lemma concreteCategoryHom_truth :
    ⇑(ConcreteCategory.hom (truth G)) = (fun _ : PUnit => true) := rfl
lemma concreteCategoryHom_falsehood :
    ⇑(ConcreteCategory.hom (falsehood G)) = (fun _ : PUnit => false) := rfl
noncomputable instance oneUnique (X : Action (FintypeCat) G) : Unique (X ⟶ oneObj G) where
  default := oneMap G
  uniq f := by apply Action.hom_ext; ext x; cases f x; rfl
noncomputable def oneIsTerminal : Limits.IsTerminal (oneObj G) := Limits.IsTerminal.ofUnique (oneObj G)
noncomputable abbrev initialObj : Action (FintypeCat) G := ⊥_ _
noncomputable def truthSource : Bool → Action (FintypeCat) G
  | false => initialObj G
  | true => oneObj G
def truthTarget : Bool → Action (FintypeCat) G
  | false => oneObj G
  | true => oneObj G
noncomputable def sourceCofan : Cofan (truthSource G) where
  pt := oneObj G
  ι := Discrete.natTrans fun
    | ⟨false⟩ => initial.to (oneObj G)
    | ⟨true⟩ => 𝟙 (oneObj G)
noncomputable def sourceCofanIsColimit : IsColimit (sourceCofan G) := by
  refine IsColimit.mk (fun s => s.ι.app ⟨true⟩) ?_ ?_
  · intro s j
    cases j using Discrete.casesOn with
    | mk a =>
      cases a
      · exact initial.hom_ext _ _
      · exact Category.id_comp _
  · intro s m hm
    simpa [sourceCofan] using hm ⟨true⟩
lemma from_one_apply_action {W : Action (FintypeCat) G} (h : oneObj G ⟶ W) (g : G) :
    h PUnit.unit = ConcreteCategory.hom (W.ρ g) (h PUnit.unit) := by
  have hcomm := congrArg (fun φ : (oneObj G).V ⟶ W.V =>
      ConcreteCategory.hom φ PUnit.unit) (h.comm g)
  simpa using hcomm
noncomputable def targetCofan : Cofan (truthTarget G) where
  pt := twoObj G
  ι := Discrete.natTrans fun
    | ⟨false⟩ => truth G
    | ⟨true⟩ => falsehood G
noncomputable def targetCofanIsColimit : IsColimit (targetCofan G) := by
  let desc (s : Cocone (Discrete.functor (truthTarget G))) : twoObj G ⟶ s.pt :=
    actionHomOfEquivariant
      (fun b : (twoObj G).V.obj =>
        match (show Bool from b) with
        | true => s.ι.app ⟨false⟩ PUnit.unit
        | false => s.ι.app ⟨true⟩ PUnit.unit)
      (by
        intro g b
        cases (show Bool from b)
        · exact from_one_apply_action G (s.ι.app ⟨true⟩) g
        · exact from_one_apply_action G (s.ι.app ⟨false⟩) g)
  refine IsColimit.mk desc ?_ ?_
  · intro s j
    cases j using Discrete.casesOn with
    | mk a =>
      cases a
      · apply ConcreteCategory.ext_apply
        intro x
        cases x
        rw [ConcreteCategory.comp_apply]
        change (ConcreteCategory.hom (desc s)) ((ConcreteCategory.hom (truth G)) PUnit.unit) = _
        rw [concreteCategoryHom_actionHomOfEquivariant, concreteCategoryHom_truth]
        rfl
      · apply ConcreteCategory.ext_apply
        intro x
        cases x
        rw [ConcreteCategory.comp_apply]
        change (ConcreteCategory.hom (desc s)) ((ConcreteCategory.hom (falsehood G)) PUnit.unit) = _
        rw [concreteCategoryHom_actionHomOfEquivariant, concreteCategoryHom_falsehood]
        rfl
  · intro s m hm
    apply ConcreteCategory.ext_apply
    intro b
    cases (show Bool from b)
    · have h := ConcreteCategory.congr_hom (hm ⟨true⟩) PUnit.unit
      rw [ConcreteCategory.comp_apply] at h
      change (ConcreteCategory.hom m) ((ConcreteCategory.hom (falsehood G)) PUnit.unit) = _ at h
      rw [concreteCategoryHom_falsehood] at h
      simp only [] at h
      exact h
    · have h := ConcreteCategory.congr_hom (hm ⟨false⟩) PUnit.unit
      rw [ConcreteCategory.comp_apply] at h
      change (ConcreteCategory.hom m) ((ConcreteCategory.hom (truth G)) PUnit.unit) = _ at h
      rw [concreteCategoryHom_truth] at h
      simp only [] at h
      exact h
end FiniteGSetProof

/- accepted add_to_file helper 2 -/
namespace FiniteGSetProof

variable (G : Type u) [Group G]

noncomputable def targetCofanTrue : Cofan (truthTarget G) where
  pt := twoObj G
  ι := Discrete.natTrans fun
    | ⟨false⟩ => falsehood G
    | ⟨true⟩ => truth G

noncomputable def targetCofanTrueIsColimit : IsColimit (targetCofanTrue G) := by
  let desc (s : Cocone (Discrete.functor (truthTarget G))) : twoObj G ⟶ s.pt :=
    actionHomOfEquivariant
      (fun b : (twoObj G).V.obj =>
        match (show Bool from b) with
        | true => s.ι.app ⟨true⟩ PUnit.unit
        | false => s.ι.app ⟨false⟩ PUnit.unit)
      (by
        intro g b
        cases (show Bool from b)
        · exact from_one_apply_action G (s.ι.app ⟨false⟩) g
        · exact from_one_apply_action G (s.ι.app ⟨true⟩) g)
  refine IsColimit.mk desc ?_ ?_
  · intro s j
    cases j using Discrete.casesOn with
    | mk a =>
      cases a
      · apply ConcreteCategory.ext_apply
        intro x
        cases x
        rw [ConcreteCategory.comp_apply]
        change (ConcreteCategory.hom (desc s)) ((ConcreteCategory.hom (falsehood G)) PUnit.unit) = _
        rw [concreteCategoryHom_actionHomOfEquivariant, concreteCategoryHom_falsehood]
        rfl
      · apply ConcreteCategory.ext_apply
        intro x
        cases x
        rw [ConcreteCategory.comp_apply]
        change (ConcreteCategory.hom (desc s)) ((ConcreteCategory.hom (truth G)) PUnit.unit) = _
        rw [concreteCategoryHom_actionHomOfEquivariant, concreteCategoryHom_truth]
        rfl
  · intro s m hm
    apply ConcreteCategory.ext_apply
    intro b
    cases (show Bool from b)
    · have h := ConcreteCategory.congr_hom (hm ⟨false⟩) PUnit.unit
      rw [ConcreteCategory.comp_apply] at h
      change (ConcreteCategory.hom m) ((ConcreteCategory.hom (falsehood G)) PUnit.unit) = _ at h
      rw [concreteCategoryHom_falsehood] at h
      simp only [] at h
      exact h
    · have h := ConcreteCategory.congr_hom (hm ⟨true⟩) PUnit.unit
      rw [ConcreteCategory.comp_apply] at h
      change (ConcreteCategory.hom m) ((ConcreteCategory.hom (truth G)) PUnit.unit) = _ at h
      rw [concreteCategoryHom_truth] at h
      simp only [] at h
      exact h

end FiniteGSetProof

/- accepted add_to_file helper 3 -/
namespace FiniteGSetProof

variable (G : Type u) [Group G]

noncomputable def truthNat : Discrete.functor (truthSource G) ⟶ Discrete.functor (truthTarget G) :=
  Discrete.natTrans fun
    | ⟨false⟩ => initial.to (oneObj G)
    | ⟨true⟩ => 𝟙 (oneObj G)

lemma truthNat_comm (j : Discrete Bool) :
    (sourceCofan G).ι.app j ≫ truth G =
      (truthNat G).app j ≫ (targetCofanTrue G).ι.app j := by
  cases j using Discrete.casesOn with
  | mk a =>
    cases a
    · exact initial.hom_ext _ _
    · rfl

end FiniteGSetProof

/- accepted add_to_file helper 4 -/
namespace FiniteGSetProof

lemma morphismProperty_truth (G : Type*) [Group G] [Finite G]
    (D : CategoryTheory.MorphismProperty (Action (FintypeCat) G))
    (hD_id : {X Y : Action (FintypeCat) G} → (f : X ⟶ Y) →
      D f → D (CategoryTheory.CategoryStruct.id X) ∧
        D (CategoryTheory.CategoryStruct.id Y))
    (hD_pullback : D.IsStableUnderBaseChange)
    (hD_coproduct : D.IsStableUnderFiniteCoproducts)
    (hD_empty : D (CategoryTheory.Limits.initial.to
      (CategoryTheory.Limits.terminal (Action (FintypeCat) G)))) :
    D (truth G) := by
  classical
  haveI : D.IsStableUnderBaseChange := hD_pullback
  haveI : D.IsStableUnderFiniteCoproducts := hD_coproduct
  haveI : D.RespectsIso := hD_pullback.respectsIso
  let e := terminalIsoIsTerminal (oneIsTerminal G)
  have hInitOne' : D (initial.to (terminal (Action (FintypeCat) G)) ≫ e.hom) :=
    MorphismProperty.RespectsIso.postcomp D e.hom
      (initial.to (terminal (Action (FintypeCat) G))) hD_empty
  have hInitOne : D (initial.to (oneObj G)) := by
    convert hInitOne' using 1
  have hIdOne : D (𝟙 (oneObj G)) := (hD_id (initial.to (oneObj G)) hInitOne).2
  have hcomponents : D.functorCategory (Discrete Bool) (truthNat G) := by
    intro j
    cases j using Discrete.casesOn with
    | mk a =>
      cases a
      · exact hInitOne
      · exact hIdOne
  exact (hD_coproduct.isStableUnderCoproductsOfShape Bool).condition
    (Discrete.functor (truthSource G)) (Discrete.functor (truthTarget G))
    (sourceCofan G) (targetCofanTrue G)
    (sourceCofanIsColimit G) (targetCofanTrueIsColimit G)
    (truthNat G) hcomponents (truth G) (fun j => truthNat_comm G j)

end FiniteGSetProof

/- accepted add_to_file helper 5 -/
namespace FiniteGSetProof

variable (G : Type*) [Group G]

lemma rho_apply (X : Action (FintypeCat) G) (g : G) (x : X.V.obj) :
    ConcreteCategory.hom (X.ρ g) x = g • x := by
  rfl

lemma hom_apply_action {X Y : Action (FintypeCat) G} (f : X ⟶ Y) (g : G) (x : X.V.obj) :
    f (ConcreteCategory.hom (X.ρ g) x) = ConcreteCategory.hom (Y.ρ g) (f x) := by
  have h := congrArg (fun φ : X.V ⟶ Y.V => ConcreteCategory.hom φ x) (f.comm g)
  simpa [ConcreteCategory.comp_apply] using h

lemma hom_apply_smul {X Y : Action (FintypeCat) G} (f : X ⟶ Y) (g : G) (x : X.V.obj) :
    f (g • x) = g • f x := by
  simpa [rho_apply G] using hom_apply_action G f g x

end FiniteGSetProof

/- accepted add_to_file helper 6 -/
namespace FiniteGSetProof

variable (G : Type*) [Group G]

noncomputable def characteristicMap {X Y : Action (FintypeCat) G} (f : X ⟶ Y) :
    Y ⟶ twoObj G := by
  classical
  exact actionHomOfEquivariant
    (fun y => if ∃ x : X.V.obj, f x = y then true else false)
    (by
      intro g y
      change (if ∃ x : X.V.obj, f x = g • y then true else false) =
        (if ∃ x : X.V.obj, f x = y then true else false)
      have hiff : (∃ x : X.V.obj, f x = g • y) ↔ (∃ x : X.V.obj, f x = y) := by
        constructor
        · rintro ⟨x, hx⟩
          refine ⟨g⁻¹ • x, ?_⟩
          calc
            f (g⁻¹ • x) = g⁻¹ • f x := hom_apply_smul G f g⁻¹ x
            _ = g⁻¹ • (g • y) := by rw [hx]
            _ = y := inv_smul_smul g y
        · rintro ⟨x, hx⟩
          refine ⟨g • x, ?_⟩
          calc
            f (g • x) = g • f x := hom_apply_smul G f g x
            _ = g • y := by rw [hx]
      rw [propext hiff])

end FiniteGSetProof

/- accepted add_to_file helper 7 -/
namespace FiniteGSetProof

variable (G : Type*) [Group G]

lemma characteristicMap_apply {X Y : Action (FintypeCat) G} (f : X ⟶ Y) (y : Y.V.obj)
    [Decidable (∃ x : X.V.obj, f x = y)] :
    characteristicMap G f y = (if ∃ x : X.V.obj, f x = y then true else false) := by
  unfold characteristicMap
  rw [concreteCategoryHom_actionHomOfEquivariant]
  congr

end FiniteGSetProof

/- accepted add_to_file helper 8 -/
namespace FiniteGSetProof

variable (G : Type*) [Group G]

lemma oneMap_apply {X : Action (FintypeCat) G} (x : X.V.obj) :
    oneMap G x = PUnit.unit := by
  rfl

noncomputable def characteristicSquare {X Y : Action (FintypeCat) G} (f : X ⟶ Y) :
    Square (Action (FintypeCat) G) := by
  classical
  refine Square.mk (oneMap G) f (truth G) (characteristicMap G f) ?_
  apply ConcreteCategory.ext_apply
  intro x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  rw [oneMap_apply, concreteCategoryHom_truth]
  simp [characteristicMap_apply]

end FiniteGSetProof

/- accepted add_to_file helper 9 -/
namespace FiniteGSetProof

variable (G : Type*) [Group G]

lemma characteristicSquare_isPullback {X Y : Action (FintypeCat) G} (f : X ⟶ Y) [Mono f] :
    (characteristicSquare G f).IsPullback := by
  classical
  have hf_inj : Function.Injective (ConcreteCategory.hom f) :=
    (ConcreteCategory.mono_iff_injective_of_preservesPullback f).mp inferInstance
  let F := Action.forget (FintypeCat) G ⋙ FintypeCat.incl
  have hmap : ((characteristicSquare G f).map F).IsPullback := by
    refine (CategoryTheory.Limits.Types.isPullback_iff _ _ _ _).mpr ⟨?_, ?_, ?_⟩
    · exact ((characteristicSquare G f).map F).fac
    · intro x y h
      exact hf_inj h.2
    · intro p y hp
      cases p
      have hχ : characteristicMap G f y = true := hp.symm
      rw [characteristicMap_apply] at hχ
      split at hχ
      case isTrue hmem =>
        rcases hmem with ⟨x, hx⟩
        exact ⟨x, oneMap_apply G x, hx⟩
      case isFalse hnot =>
        simp at hχ
  exact Square.IsPullback.of_map F hmap

end FiniteGSetProof

/- accepted add_to_file helper 10 -/
namespace FiniteGSetProof

universe u v

@[reducible]
def trivialMulActionU (G : Type u) [Monoid G] (A : Type v) : MulAction G A where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

@[reducible]
def trivialObjU (G : Type u) [Monoid G] (A : Type v) [Finite A] : Action (FintypeCat.{v}) G := by
  letI : MulAction G A := trivialMulActionU G A
  exact Action.FintypeCat.ofMulAction G (FintypeCat.of A)

def actionHomOfEquivariantU {G : Type u} [Monoid G] {X Y : Action (FintypeCat.{v}) G}
    (φ : X.V.obj → Y.V.obj)
    (hφ : ∀ g x, φ (ConcreteCategory.hom (X.ρ g) x) = ConcreteCategory.hom (Y.ρ g) (φ x)) : X ⟶ Y where
  hom := FintypeCat.homMk φ
  comm := by intro g; ext x; exact hφ g x

lemma concreteCategoryHom_actionHomOfEquivariantU {G : Type u} [Monoid G]
    {X Y : Action (FintypeCat.{v}) G} (φ : X.V.obj → Y.V.obj)
    (hφ : ∀ g x, φ (ConcreteCategory.hom (X.ρ g) x) = ConcreteCategory.hom (Y.ρ g) (φ x)) :
    ConcreteCategory.hom (actionHomOfEquivariantU φ hφ : X ⟶ Y) = φ := rfl

noncomputable def toTrivialObjU (G : Type u) [Monoid G] (A : Type v) [Finite A] [Nonempty A]
    (X : Action (FintypeCat.{v}) G) : X ⟶ trivialObjU G A :=
  let a : A := Classical.choice inferInstance
  actionHomOfEquivariantU (fun _ => a) (by intro g x; rfl)

def trivialMapU (G : Type u) [Monoid G] {A B : Type v} [Finite A] [Finite B]
    (φ : A → B) : trivialObjU G A ⟶ trivialObjU G B :=
  actionHomOfEquivariantU φ (by intro g x; rfl)

variable (G : Type u) [Group G]

@[reducible]
def oneObjU : Action (FintypeCat.{v}) G := trivialObjU G (ULift.{v,0} PUnit.{1})
@[reducible]
def twoObjU : Action (FintypeCat.{v}) G := trivialObjU G (ULift.{v,0} Bool)
noncomputable def oneMapU {X : Action (FintypeCat.{v}) G} : X ⟶ oneObjU G :=
  toTrivialObjU G (ULift.{v,0} PUnit.{1}) X
def truthU : oneObjU G ⟶ twoObjU G :=
  trivialMapU G (fun _ : ULift.{v,0} PUnit.{1} => (ULift.up true : ULift.{v,0} Bool))
def falsehoodU : oneObjU G ⟶ twoObjU G :=
  trivialMapU G (fun _ : ULift.{v,0} PUnit.{1} => (ULift.up false : ULift.{v,0} Bool))

lemma concreteCategoryHom_truthU :
    (⇑(ConcreteCategory.hom (truthU G)) : (ULift.{v,0} PUnit.{1}) → ULift.{v,0} Bool) =
      (fun _ : ULift.{v,0} PUnit.{1} => (ULift.up true : ULift.{v,0} Bool)) := rfl
lemma concreteCategoryHom_falsehoodU :
    (⇑(ConcreteCategory.hom (falsehoodU G)) : (ULift.{v,0} PUnit.{1}) → ULift.{v,0} Bool) =
      (fun _ : ULift.{v,0} PUnit.{1} => (ULift.up false : ULift.{v,0} Bool)) := rfl

noncomputable instance oneUniqueU (X : Action (FintypeCat.{v}) G) : Unique (X ⟶ oneObjU G) where
  default := oneMapU G
  uniq f := by
    apply Action.hom_ext
    ext x
    cases f x with
    | up q =>
      cases q
      rfl

noncomputable def oneIsTerminalU : Limits.IsTerminal (oneObjU (G:=G)) :=
  Limits.IsTerminal.ofUnique _

noncomputable abbrev initialObjU : Action (FintypeCat.{v}) G := ⊥_ _

end FiniteGSetProof

/- accepted add_to_file helper 11 -/
namespace FiniteGSetProof
universe u v
variable (G : Type u) [Group G]

noncomputable def truthSourceU : Bool → Action (FintypeCat.{v}) G
  | false => initialObjU G
  | true => oneObjU G

def truthTargetU : Bool → Action (FintypeCat.{v}) G
  | false => oneObjU G
  | true => oneObjU G

noncomputable def sourceCofanU : Cofan (truthSourceU G) where
  pt := oneObjU G
  ι := Discrete.natTrans fun
    | ⟨false⟩ => initial.to (oneObjU G)
    | ⟨true⟩ => 𝟙 (oneObjU G)

noncomputable def sourceCofanUIsColimit : IsColimit (sourceCofanU G) := by
  refine IsColimit.mk (fun s => s.ι.app ⟨true⟩) ?_ ?_
  · intro s j
    cases j using Discrete.casesOn with
    | mk a =>
      cases a
      · exact initial.hom_ext _ _
      · exact Category.id_comp _
  · intro s m hm
    simpa [sourceCofanU] using hm ⟨true⟩

lemma from_one_apply_actionU {W : Action (FintypeCat.{v}) G} (h : oneObjU G ⟶ W) (g : G) :
    h (ULift.up PUnit.unit) = ConcreteCategory.hom (W.ρ g) (h (ULift.up PUnit.unit)) := by
  have hcomm := congrArg (fun φ : (oneObjU G).V ⟶ W.V =>
      ConcreteCategory.hom φ (ULift.up PUnit.unit)) (h.comm g)
  simpa using hcomm

noncomputable def targetCofanTrueU : Cofan (truthTargetU G) where
  pt := twoObjU G
  ι := Discrete.natTrans fun
    | ⟨false⟩ => falsehoodU G
    | ⟨true⟩ => truthU G

noncomputable def targetCofanTrueUIsColimit : IsColimit (targetCofanTrueU G) := by
  let desc (s : Cocone (Discrete.functor (truthTargetU G))) : twoObjU G ⟶ s.pt :=
    actionHomOfEquivariantU
      (fun b : (twoObjU G).V.obj =>
        if (show ULift.{v,0} Bool from b).down then
          s.ι.app ⟨true⟩ (ULift.up PUnit.unit)
        else
          s.ι.app ⟨false⟩ (ULift.up PUnit.unit))
      (by
        intro g b
        cases b with
        | up q =>
          cases q
          · exact from_one_apply_actionU G (s.ι.app ⟨false⟩) g
          · exact from_one_apply_actionU G (s.ι.app ⟨true⟩) g)
  refine IsColimit.mk desc ?_ ?_
  · intro s j
    cases j using Discrete.casesOn with
    | mk a =>
      cases a
      · apply ConcreteCategory.ext_apply
        intro x
        cases x with
        | up q =>
          cases q
          rw [ConcreteCategory.comp_apply]
          change (ConcreteCategory.hom (desc s)) ((ConcreteCategory.hom (falsehoodU G))
            (ULift.up PUnit.unit)) = _
          rw [concreteCategoryHom_actionHomOfEquivariantU, concreteCategoryHom_falsehoodU]
          rfl
      · apply ConcreteCategory.ext_apply
        intro x
        cases x with
        | up q =>
          cases q
          rw [ConcreteCategory.comp_apply]
          change (ConcreteCategory.hom (desc s)) ((ConcreteCategory.hom (truthU G))
            (ULift.up PUnit.unit)) = _
          rw [concreteCategoryHom_actionHomOfEquivariantU, concreteCategoryHom_truthU]
          rfl
  · intro s m hm
    apply ConcreteCategory.ext_apply
    intro b
    cases b with
    | up q =>
      cases q
      · have h := ConcreteCategory.congr_hom (hm ⟨false⟩) (ULift.up PUnit.unit)
        rw [ConcreteCategory.comp_apply] at h
        change (ConcreteCategory.hom m) ((ConcreteCategory.hom (falsehoodU G))
          (ULift.up PUnit.unit)) = _ at h
        rw [concreteCategoryHom_falsehoodU] at h
        simp only [] at h
        exact h
      · have h := ConcreteCategory.congr_hom (hm ⟨true⟩) (ULift.up PUnit.unit)
        rw [ConcreteCategory.comp_apply] at h
        change (ConcreteCategory.hom m) ((ConcreteCategory.hom (truthU G))
          (ULift.up PUnit.unit)) = _ at h
        rw [concreteCategoryHom_truthU] at h
        simp only [] at h
        exact h

end FiniteGSetProof

/- accepted add_to_file helper 12 -/
namespace FiniteGSetProof
universe u v
variable (G : Type u) [Group G]

noncomputable def truthNatU : Discrete.functor (truthSourceU G) ⟶ Discrete.functor (truthTargetU G) :=
  Discrete.natTrans fun
    | ⟨false⟩ => initial.to (oneObjU G)
    | ⟨true⟩ => 𝟙 (oneObjU G)

lemma truthNatU_comm (j : Discrete Bool) :
    (sourceCofanU G).ι.app j ≫ truthU G =
      (truthNatU G).app j ≫ (targetCofanTrueU G).ι.app j := by
  cases j using Discrete.casesOn with
  | mk a =>
    cases a
    · exact initial.hom_ext _ _
    · rfl

end FiniteGSetProof

/- accepted add_to_file helper 13 -/
namespace FiniteGSetProof
universe u v
lemma morphismProperty_truthU (G : Type u) [Group G] [Finite G]
    (D : CategoryTheory.MorphismProperty (Action (FintypeCat.{v}) G))
    (hD_id : {X Y : Action (FintypeCat.{v}) G} → (f : X ⟶ Y) →
      D f → D (CategoryTheory.CategoryStruct.id X) ∧
        D (CategoryTheory.CategoryStruct.id Y))
    (hD_pullback : D.IsStableUnderBaseChange)
    (hD_coproduct : D.IsStableUnderFiniteCoproducts)
    (hD_empty : D (CategoryTheory.Limits.initial.to
      (CategoryTheory.Limits.terminal (Action (FintypeCat.{v}) G)))) :
    D (truthU G) := by
  classical
  haveI : D.IsStableUnderBaseChange := hD_pullback
  haveI : D.IsStableUnderFiniteCoproducts := hD_coproduct
  haveI : D.RespectsIso := hD_pullback.respectsIso
  let e := terminalIsoIsTerminal (oneIsTerminalU (G:=G))
  have hInitOne' : D (initial.to (terminal (Action (FintypeCat.{v}) G)) ≫ e.hom) :=
    MorphismProperty.RespectsIso.postcomp D e.hom
      (initial.to (terminal (Action (FintypeCat.{v}) G))) hD_empty
  have hInitOne : D (initial.to (oneObjU G)) := by
    convert hInitOne' using 1
    exact initial.hom_ext _ _
  have hIdOne : D (𝟙 (oneObjU G)) := (hD_id (initial.to (oneObjU G)) hInitOne).2
  have hcomponents : D.functorCategory (Discrete Bool) (truthNatU G) := by
    intro j
    cases j using Discrete.casesOn with
    | mk a =>
      cases a
      · exact hInitOne
      · exact hIdOne
  exact (hD_coproduct.isStableUnderCoproductsOfShape Bool).condition
    (Discrete.functor (truthSourceU G)) (Discrete.functor (truthTargetU G))
    (sourceCofanU G) (targetCofanTrueU G)
    (sourceCofanUIsColimit G) (targetCofanTrueUIsColimit G)
    (truthNatU G) hcomponents (truthU G) (fun j => truthNatU_comm G j)
end FiniteGSetProof

/- accepted add_to_file helper 14 -/
namespace FiniteGSetProof
universe u v
variable (G : Type u) [Group G]

lemma rho_applyU (X : Action (FintypeCat.{v}) G) (g : G) (x : X.V.obj) :
    ConcreteCategory.hom (X.ρ g) x = g • x := by
  rfl

lemma hom_apply_actionU {X Y : Action (FintypeCat.{v}) G} (f : X ⟶ Y) (g : G) (x : X.V.obj) :
    f (ConcreteCategory.hom (X.ρ g) x) = ConcreteCategory.hom (Y.ρ g) (f x) := by
  have h := congrArg (fun φ : X.V ⟶ Y.V => ConcreteCategory.hom φ x) (f.comm g)
  simpa [ConcreteCategory.comp_apply] using h

lemma hom_apply_smulU {X Y : Action (FintypeCat.{v}) G} (f : X ⟶ Y) (g : G) (x : X.V.obj) :
    f (g • x) = g • f x := by
  simpa [rho_applyU G] using hom_apply_actionU G f g x

end FiniteGSetProof

/- accepted add_to_file helper 15 -/
namespace FiniteGSetProof
universe u v
variable (G : Type u) [Group G]

noncomputable def characteristicMapU {X Y : Action (FintypeCat.{v}) G} (f : X ⟶ Y) :
    Y ⟶ twoObjU G := by
  classical
  exact actionHomOfEquivariantU
    (fun y => if ∃ x : X.V.obj, f x = y then (ULift.up true : ULift.{v,0} Bool)
      else (ULift.up false : ULift.{v,0} Bool))
    (by
      intro g y
      change (if ∃ x : X.V.obj, f x = g • y then (ULift.up true : ULift.{v,0} Bool)
          else (ULift.up false : ULift.{v,0} Bool)) =
        (if ∃ x : X.V.obj, f x = y then (ULift.up true : ULift.{v,0} Bool)
          else (ULift.up false : ULift.{v,0} Bool))
      have hiff : (∃ x : X.V.obj, f x = g • y) ↔ (∃ x : X.V.obj, f x = y) := by
        constructor
        · rintro ⟨x, hx⟩
          refine ⟨g⁻¹ • x, ?_⟩
          calc
            f (g⁻¹ • x) = g⁻¹ • f x := hom_apply_smulU G f g⁻¹ x
            _ = g⁻¹ • (g • y) := by rw [hx]
            _ = y := inv_smul_smul g y
        · rintro ⟨x, hx⟩
          refine ⟨g • x, ?_⟩
          calc
            f (g • x) = g • f x := hom_apply_smulU G f g x
            _ = g • y := by rw [hx]
      rw [propext hiff])

lemma characteristicMapU_apply {X Y : Action (FintypeCat.{v}) G} (f : X ⟶ Y) (y : Y.V.obj)
    [Decidable (∃ x : X.V.obj, f x = y)] :
    characteristicMapU G f y =
      (if ∃ x : X.V.obj, f x = y then (ULift.up true : ULift.{v,0} Bool)
        else (ULift.up false : ULift.{v,0} Bool)) := by
  unfold characteristicMapU
  rw [concreteCategoryHom_actionHomOfEquivariantU]
  congr

lemma oneMapU_apply {X : Action (FintypeCat.{v}) G} (x : X.V.obj) :
    oneMapU G x = ULift.up PUnit.unit := by
  cases oneMapU G x with
  | up q =>
    cases q
    rfl

end FiniteGSetProof

/- accepted add_to_file helper 16 -/
namespace FiniteGSetProof
universe u v
variable (G : Type u) [Group G]

noncomputable def characteristicSquareU {X Y : Action (FintypeCat.{v}) G} (f : X ⟶ Y) :
    Square (Action (FintypeCat.{v}) G) := by
  classical
  refine Square.mk (oneMapU G) f (truthU G) (characteristicMapU G f) ?_
  apply ConcreteCategory.ext_apply
  intro x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  rw [oneMapU_apply, concreteCategoryHom_truthU]
  simp [characteristicMapU_apply]

lemma characteristicSquareU_isPullback {X Y : Action (FintypeCat.{v}) G} (f : X ⟶ Y) [Mono f] :
    (characteristicSquareU G f).IsPullback := by
  classical
  have hf_inj : Function.Injective (ConcreteCategory.hom f) :=
    (ConcreteCategory.mono_iff_injective_of_preservesPullback f).mp inferInstance
  let F := Action.forget (FintypeCat.{v}) G ⋙ FintypeCat.incl
  have hmap : ((characteristicSquareU G f).map F).IsPullback := by
    refine (CategoryTheory.Limits.Types.isPullback_iff _ _ _ _).mpr ⟨?_, ?_, ?_⟩
    · exact ((characteristicSquareU G f).map F).fac
    · intro x y h
      exact hf_inj h.2
    · intro p y hp
      cases p with
      | up q =>
        cases q
        have hχ : characteristicMapU G f y = ULift.up true := hp.symm
        rw [characteristicMapU_apply] at hχ
        split at hχ
        case isTrue hmem =>
          rcases hmem with ⟨x, hx⟩
          exact ⟨x, oneMapU_apply G x, hx⟩
        case isFalse hnot =>
          cases hχ
  exact Square.IsPullback.of_map F hmap

end FiniteGSetProof

/- verified submission -/
theorem finite_G_set_subcategory_contains_all_monomorphisms
    (G : Type*) [Group G] [Finite G]
    (D : CategoryTheory.MorphismProperty (Action (FintypeCat) G))
    (hD_id : {X Y : Action (FintypeCat) G} → (f : X ⟶ Y) →
      D f → D (CategoryTheory.CategoryStruct.id X) ∧
        D (CategoryTheory.CategoryStruct.id Y))
    (hD_comp : D.IsStableUnderComposition)
    (hD_pullback : D.IsStableUnderBaseChange)
    (hD_coproduct : D.IsStableUnderFiniteCoproducts)
    (hD_empty : D (CategoryTheory.Limits.initial.to
      (CategoryTheory.Limits.terminal (Action (FintypeCat) G)))) :
    CategoryTheory.MorphismProperty.monomorphisms (Action (FintypeCat) G) ≤ D := by
  intro X Y f hf
  haveI : Mono f := hf
  haveI : D.IsStableUnderBaseChange := hD_pullback
  have htruth : D (FiniteGSetProof.truthU G) :=
    FiniteGSetProof.morphismProperty_truthU G D hD_id hD_pullback hD_coproduct hD_empty
  exact CategoryTheory.MorphismProperty.of_isPullback
    (FiniteGSetProof.characteristicSquareU_isPullback G f) htruth

end Rollout_p0378_finite_g_set_subcategory_contains_all_mono

namespace Rollout_p3114_dimension_three_evaluation_of_asymptotic_c

/- accepted add_to_file helper 1 -/
lemma arccot_integrand_hasDerivAt (a x : ℝ) (ha : a ≠ 0) :
    HasDerivAt (fun y : ℝ => (1 + a ^ 2) * Real.arctan (y / a) - a * y)
      ((1 - x ^ 2) * a / (a ^ 2 + x ^ 2)) x := by
  have hden : a ^ 2 + x ^ 2 ≠ 0 := by
    positivity
  have hderiv_arctan : HasDerivAt (fun y : ℝ => Real.arctan (y / a)) (a / (a ^ 2 + x ^ 2)) x := by
    have hdiv : HasDerivAt (fun y : ℝ => y / a) (1 / a) x := by
      simpa [div_eq_mul_inv] using (hasDerivAt_id x).mul_const (a⁻¹)
    convert (Real.hasDerivAt_arctan (x / a)).comp x hdiv using 1
    field_simp [ha]
  have hconst := hderiv_arctan.const_mul (1 + a ^ 2)
  have hlin : HasDerivAt (fun y : ℝ => a * y) a x := by
    simpa using (hasDerivAt_id x).const_mul a
  convert hconst.sub hlin using 1
  field_simp [hden]
  ring

lemma asymptotic_integrand_integral_of_ne_zero (a : ℝ) (ha : a ≠ 0) :
    (∫ η in (-1 : ℝ)..1,
      if a = 0 ∧ η = 0 then 0
      else (1 - η ^ 2) * a / (a ^ 2 + η ^ 2)) =
      2 * (1 + a ^ 2) * Real.arctan (1 / a) - 2 * a := by
  let F : ℝ → ℝ := fun x => (1 + a ^ 2) * Real.arctan (x / a) - a * x
  let f' : ℝ → ℝ := fun x => (1 - x ^ 2) * a / (a ^ 2 + x ^ 2)
  have hder : deriv F = f' := by
    funext x
    exact (arccot_integrand_hasDerivAt a x ha).deriv
  have hdiff : ∀ x ∈ Set.uIcc (-1 : ℝ) 1, DifferentiableAt ℝ F x := by
    intro x hx
    exact (arccot_integrand_hasDerivAt a x ha).differentiableAt
  have hcont : ContinuousOn f' (Set.uIcc (-1 : ℝ) 1) := by
    intro x hx
    fun_prop (disch := positivity)
  have hftc := intervalIntegral.integral_deriv_eq_sub' F hder hdiff hcont
  simp [ha, F, f'] at hftc ⊢
  rw [hftc]
  have hneg : Real.arctan (-1 / a) = -Real.arctan (1 / a) := by
    rw [show -1 / a = -(1 / a) by ring, Real.arctan_neg]
  rw [hneg]
  ring

lemma asymptotic_integrand_integral_zero :
    (∫ η in (-1 : ℝ)..1,
      if (0 : ℝ) = 0 ∧ η = 0 then 0
      else (1 - η ^ 2) * (0 : ℝ) / ((0 : ℝ) ^ 2 + η ^ 2)) = 0 := by
  simp

/- verified submission -/
theorem dimension_three_evaluation_of_asymptotic_coefficient :
    let H : ℝ → ℝ := fun a => if a < 0 then 0 else if a = 0 then 1 / 2 else 1
    let arccot : ℝ → ℝ := fun a => Real.pi / 2 - Real.arctan a
    let κ : ℝ → ℝ := fun a =>
      (1 / (4 * Real.pi)) *
        (-(1 / (2 * Real.pi)) *
            (∫ η in (-1 : ℝ)..1,
              if a = 0 ∧ η = 0 then 0
              else (1 - η ^ 2) * a / (a ^ 2 + η ^ 2))
          - 1 / 4 + H a * (1 + a ^ 2))
    ∀ a : ℝ,
      κ a =
        (1 / (4 * Real.pi)) *
          (-1 / 4 - (1 + a ^ 2) * arccot a / Real.pi +
            (1 + a ^ 2) + a / Real.pi) := by
  dsimp only
  intro a
  by_cases ha0 : a = 0
  · subst a
    simp [asymptotic_integrand_integral_zero, Real.pi_ne_zero]
    field_simp [Real.pi_ne_zero]
    ring
  · by_cases hneg : a < 0
    · have hI := asymptotic_integrand_integral_of_ne_zero a ha0
      have hrec : Real.arctan (1 / a) = -(Real.pi / 2) - Real.arctan a := by
        simpa [one_div] using Real.arctan_inv_of_neg hneg
      rw [hI, hrec]
      simp [ha0, hneg, Real.pi_ne_zero]
      field_simp [Real.pi_ne_zero]
      ring
    · have hpos : 0 < a := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm ha0)
      have hI := asymptotic_integrand_integral_of_ne_zero a ha0
      have hrec : Real.arctan (1 / a) = Real.pi / 2 - Real.arctan a := by
        simpa [one_div] using Real.arctan_inv_of_pos hpos
      rw [hI, hrec]
      simp [ha0, hneg, Real.pi_ne_zero]
      field_simp [Real.pi_ne_zero]
      ring

end Rollout_p3114_dimension_three_evaluation_of_asymptotic_c

namespace Rollout_p1744_euler_congruence_for_counted_reduced_resid

/- verified submission -/
theorem euler_congruence_for_counted_reduced_residues
    (N x n : ℕ) (hN : 0 < N) (hx : 0 < x)
    (hcoprime : Nat.Coprime x N)
    (hn : n = ((Finset.Ico 1 N).filter fun a => Nat.Coprime a N).card) :
    Nat.ModEq N (x ^ n) 1 := by
  by_cases hN1 : N = 1
  · subst N
    exact Nat.modEq_one
  · have hNgt : 1 < N := by omega
    have hsets :
        ((Finset.Ico 1 N).filter fun a => Nat.Coprime a N) =
          {a ∈ Finset.Ico 1 (1 + N) | N.Coprime a} := by
      ext a
      constructor
      · intro ha
        simp only [Finset.mem_filter, Finset.mem_Ico] at ha ⊢
        exact ⟨⟨ha.1.1, by omega⟩, ha.2.symm⟩
      · intro ha
        simp only [Finset.mem_filter, Finset.mem_Ico] at ha ⊢
        have ha_ne_N : a ≠ N := by
          intro h
          subst a
          have : N = 1 := (Nat.coprime_self N).mp ha.2
          omega
        exact ⟨⟨ha.1.1, by omega⟩, ha.2.symm⟩
    have hcard :
        ((Finset.Ico 1 N).filter fun a => Nat.Coprime a N).card = N.totient := by
      rw [hsets]
      exact Nat.filter_coprime_Ico_eq_totient N 1
    rw [hn, hcard]
    exact Nat.ModEq.pow_totient hcoprime

end Rollout_p1744_euler_congruence_for_counted_reduced_resid

namespace Rollout_p0246_formalpowerseries_automorphism_exact_seque

/- accepted add_to_file helper 1 -/

noncomputable section

namespace FPSAut

abbrev PS := PowerSeries ℂ

instance : TopologicalSpace PS :=
  PowerSeries.WithPiTopology.instTopologicalSpace ℂ

instance : UniformSpace PS :=
  PowerSeries.WithPiTopology.instUniformSpace ℂ

instance : IsUniformAddGroup PS :=
  PowerSeries.WithPiTopology.instIsUniformAddGroup ℂ

instance : IsTopologicalRing PS :=
  PowerSeries.WithPiTopology.instIsTopologicalRing ℂ

instance : T2Space PS :=
  PowerSeries.WithPiTopology.instT2Space ℂ

instance : CompleteSpace PS :=
  PowerSeries.WithPiTopology.instCompleteSpace ℂ

instance : ContinuousSMul ℂ PS :=
  MvPowerSeries.WithPiTopology.instContinuousSMul (σ := Unit) (R := ℂ) (S := ℂ)

lemma algHom_constantCoeff_X (φ : PS →ₐ[ℂ] PS) :
    PowerSeries.constantCoeff (φ PowerSeries.X) = 0 := by
  by_contra hc
  let c : ℂ := PowerSeries.constantCoeff (φ PowerSeries.X)
  have hunit : IsUnit (PowerSeries.X - PowerSeries.C c : PS) := by
    rw [PowerSeries.isUnit_iff_constantCoeff]
    simp [c, hc]
  have hunit_image : IsUnit (φ (PowerSeries.X - PowerSeries.C c : PS)) :=
    hunit.map φ.toRingHom
  have hphiC : φ (PowerSeries.C c : PS) = PowerSeries.C c := by
    rw [PowerSeries.C_eq_algebraMap]
    exact φ.commutes c
  have hconst : PowerSeries.constantCoeff (φ (PowerSeries.X - PowerSeries.C c : PS)) = 0 := by
    calc
      PowerSeries.constantCoeff (φ (PowerSeries.X - PowerSeries.C c : PS))
          = PowerSeries.constantCoeff (φ PowerSeries.X - φ (PowerSeries.C c : PS)) := by
              rw [map_sub]
      _ = c - c := by simp [c, hphiC]
      _ = 0 := sub_self c
  rw [PowerSeries.isUnit_iff_constantCoeff, hconst] at hunit_image
  exact not_isUnit_zero hunit_image

lemma algHom_coeff_eq_sum (φ : PS →ₐ[ℂ] PS) (n : ℕ) (f : PS) :
    (PowerSeries.coeff n) (φ f) =
      ∑ i ∈ Finset.range (n + 1),
        (PowerSeries.coeff i) f * (PowerSeries.coeff n) ((φ PowerSeries.X) ^ i) := by
  let p : Polynomial ℂ := PowerSeries.trunc (n + 1) f
  have hdiv : PowerSeries.X ^ (n + 1) ∣ f - (p : PS) := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    simp [p, PowerSeries.coeff_trunc, hm]
  rcases hdiv with ⟨r, hr⟩
  have hXdvd : PowerSeries.X ∣ φ PowerSeries.X := by
    rw [PowerSeries.X_dvd_iff]
    exact algHom_constantCoeff_X φ
  have hpowdvd : PowerSeries.X ^ (n + 1) ∣ (φ PowerSeries.X) ^ (n + 1) :=
    pow_dvd_pow_of_dvd hXdvd (n + 1)
  have htaildvd : PowerSeries.X ^ (n + 1) ∣ (φ PowerSeries.X) ^ (n + 1) * φ r :=
    Dvd.dvd.mul_right hpowdvd (φ r)
  have htailcoeff :
      (PowerSeries.coeff n) ((φ PowerSeries.X) ^ (n + 1) * φ r) = 0 :=
    (PowerSeries.X_pow_dvd_iff.mp htaildvd) n (Nat.lt_succ_self n)
  have hsplit : φ f = φ (p : PS) + (φ PowerSeries.X) ^ (n + 1) * φ r := by
    calc
      φ f = φ ((f - (p : PS)) + (p : PS)) := by rw [sub_add_cancel]
      _ = φ (PowerSeries.X ^ (n + 1) * r + (p : PS)) := by rw [hr]
      _ = (φ PowerSeries.X) ^ (n + 1) * φ r + φ (p : PS) := by
        simp [map_add, map_mul, map_pow]
      _ = φ (p : PS) + (φ PowerSeries.X) ^ (n + 1) * φ r := add_comm _ _
  have hp : φ (p : PS) =
      Polynomial.eval₂ (algebraMap ℂ PS) (φ PowerSeries.X) p := by
    have h := Polynomial.aeval_algHom_apply φ (PowerSeries.X : PS) p
    have hXcoe : Polynomial.aeval (PowerSeries.X : PS) =
        (Polynomial.coeToPowerSeries.algHom (A := ℂ) : Polynomial ℂ →ₐ[ℂ] PS) := by
      apply Polynomial.algHom_ext
      simp
    calc
      φ (p : PS) = φ ((Polynomial.aeval (PowerSeries.X : PS)) p) := by
        rw [hXcoe]
        rfl
      _ = (Polynomial.aeval (φ PowerSeries.X)) p := h.symm
      _ = Polynomial.eval₂ (algebraMap ℂ PS) (φ PowerSeries.X) p := Polynomial.aeval_def _ _
  calc
    (PowerSeries.coeff n) (φ f)
        = (PowerSeries.coeff n) (φ (p : PS)) +
          (PowerSeries.coeff n) ((φ PowerSeries.X) ^ (n + 1) * φ r) := by
            rw [hsplit, map_add]
    _ = (PowerSeries.coeff n) (φ (p : PS)) := by simp [htailcoeff]
    _ = (PowerSeries.coeff n)
          (Polynomial.eval₂ (algebraMap ℂ PS) (φ PowerSeries.X) p) := by rw [hp]
    _ = ∑ i ∈ Finset.range (n + 1),
          (PowerSeries.coeff i) f * (PowerSeries.coeff n) ((φ PowerSeries.X) ^ i) := by
        rw [PowerSeries.eval₂_trunc_eq_sum_range]
        simp

lemma algHom_continuous (φ : PS →ₐ[ℂ] PS) :
    Continuous (φ : PS → PS) := by
  have hcoeff : ∀ n : ℕ, Continuous fun f : PS => (PowerSeries.coeff n) (φ f) := by
    intro n
    have hfun : (fun f : PS => (PowerSeries.coeff n) (φ f)) =
        (fun f : PS => ∑ i ∈ Finset.range (n + 1),
          (PowerSeries.coeff i) f * (PowerSeries.coeff n) ((φ PowerSeries.X) ^ i)) := by
      funext f
      exact algHom_coeff_eq_sum φ n f
    rw [hfun]
    apply continuous_finset_sum
    intro i hi
    exact (PowerSeries.WithPiTopology.continuous_coeff ℂ i).mul continuous_const
  have hmc : ∀ d : Unit →₀ ℕ, Continuous fun f : PS => MvPowerSeries.coeff d (φ f) := by
    intro d
    have deq : d = (Finsupp.single (α := Unit) () (d ())) := by
      apply Finsupp.ext
      intro x
      cases x
      simp
    have hd : (fun f : PS => MvPowerSeries.coeff d (φ f)) =
        (fun f : PS => PowerSeries.coeff (d ()) (φ f)) := by
      funext f
      rw [deq]
      simp [PowerSeries.coeff]
    rw [hd]
    exact hcoeff (d ())
  have hpi : Continuous (fun f : PS => fun d : Unit →₀ ℕ => MvPowerSeries.coeff d (φ f)) :=
    continuous_pi hmc
  change Continuous (fun f : PS => φ f)
  exact hpi

lemma algEquiv_continuous (ρ : PS ≃ₐ[ℂ] PS) :
    Continuous (ρ : PS → PS) ∧ Continuous (ρ.symm : PS → PS) :=
  ⟨algHom_continuous ρ.toAlgHom, algHom_continuous ρ.symm.toAlgHom⟩

/- accepted add_to_file helper 2 -/
lemma preservingSubgroup_one (S : Set PS) :
    (1 : PS ≃ₐ[ℂ] PS) '' S = S := by
  ext x
  simp

def preservingSubgroup (S : Set PS) : Subgroup (PS ≃ₐ[ℂ] PS) where
  carrier := {ρ | (ρ : PS → PS) '' S = S}
  one_mem' := preservingSubgroup_one S
  mul_mem' := by
    intro ρ σ hρ hσ
    calc
      ((ρ * σ : PS ≃ₐ[ℂ] PS) : PS → PS) '' S
          = (ρ : PS → PS) '' ((σ : PS → PS) '' S) := by
            ext x
            simp [Set.mem_image, AlgEquiv.mul_apply]
      _ = (ρ : PS → PS) '' S := by rw [hσ]
      _ = S := hρ
  inv_mem' := by
    intro ρ hρ
    have hpre : (ρ : PS → PS) ⁻¹' S = S := by
      calc
        (ρ : PS → PS) ⁻¹' S = (ρ : PS → PS) ⁻¹' ((ρ : PS → PS) '' S) := by rw [hρ]
        _ = S := Equiv.preimage_image ρ.toEquiv S
    calc
      ((ρ⁻¹ : PS ≃ₐ[ℂ] PS) : PS → PS) '' S = (ρ : PS → PS) ⁻¹' S := by
        change ρ.toEquiv.symm '' S = (ρ : PS → PS) ⁻¹' S
        exact Equiv.image_symm_eq_preimage ρ.toEquiv S
      _ = S := hpre

/- accepted add_to_file helper 3 -/
lemma expand_injective {p : ℕ} (hp : p ≠ 0) :
    Function.Injective (PowerSeries.expand p hp : PS →ₐ[ℂ] PS) := by
  intro f g h
  ext k
  have hk := congrArg (PowerSeries.coeff (p * k)) h
  have hpos : 0 < p := Nat.pos_of_ne_zero hp
  simpa [PowerSeries.coeff_expand, Nat.mul_div_cancel_left k hpos] using hk

/- accepted add_to_file helper 4 -/
noncomputable def restrictExpandAlgHom {p : ℕ} (hp : p ≠ 0)
    (ρ : PS ≃ₐ[ℂ] PS)
    (hρ : (ρ : PS → PS) '' Set.range (PowerSeries.expand p hp : PS →ₐ[ℂ] PS) =
      Set.range (PowerSeries.expand p hp : PS →ₐ[ℂ] PS)) :
    PS →ₐ[ℂ] PS :=
  let e : PS →ₐ[ℂ] PS := PowerSeries.expand p hp
  let S : Set PS := Set.range e
  let F : PS → PS := fun f =>
    Classical.choose (show ∃ g, e g = ρ (e f) from by
      have hmem : ρ (e f) ∈ S := by
        have him : ρ (e f) ∈ (ρ : PS → PS) '' S := by
          exact ⟨e f, ⟨f, rfl⟩, rfl⟩
        rwa [hρ] at him
      rcases hmem with ⟨g, hg⟩
      exact ⟨g, hg⟩)
  have hF : ∀ f, e (F f) = ρ (e f) := fun f =>
    Classical.choose_spec (show ∃ g, e g = ρ (e f) from by
      have hmem : ρ (e f) ∈ S := by
        have him : ρ (e f) ∈ (ρ : PS → PS) '' S := by
          exact ⟨e f, ⟨f, rfl⟩, rfl⟩
        rwa [hρ] at him
      rcases hmem with ⟨g, hg⟩
      exact ⟨g, hg⟩)
  { toFun := F
    map_one' := by
      apply expand_injective hp
      calc
        e (F 1) = ρ (e 1) := hF 1
        _ = 1 := by simp
        _ = e 1 := by simp
    map_mul' := by
      intro x y
      apply expand_injective hp
      calc
        e (F (x * y)) = ρ (e (x * y)) := hF (x * y)
        _ = ρ (e x) * ρ (e y) := by simp
        _ = e (F x) * e (F y) := by rw [hF x, hF y]
        _ = e (F x * F y) := by simp
    map_zero' := by
      apply expand_injective hp
      calc
        e (F 0) = ρ (e 0) := hF 0
        _ = 0 := by simp
        _ = e 0 := by simp
    map_add' := by
      intro x y
      apply expand_injective hp
      calc
        e (F (x + y)) = ρ (e (x + y)) := hF (x + y)
        _ = ρ (e x) + ρ (e y) := by simp
        _ = e (F x) + e (F y) := by rw [hF x, hF y]
        _ = e (F x + F y) := by simp
    commutes' := by
      intro r
      apply expand_injective hp
      calc
        e (F ((algebraMap ℂ PS) r)) = ρ (e ((algebraMap ℂ PS) r)) := hF _
        _ = (algebraMap ℂ PS) r := by
          simp [e, PowerSeries.C_eq_algebraMap]
        _ = e ((algebraMap ℂ PS) r) := by
          simp [e, PowerSeries.C_eq_algebraMap] }

/- accepted add_to_file helper 5 -/
lemma restrictExpandAlgHom_spec {p : ℕ} (hp : p ≠ 0)
    (ρ : PS ≃ₐ[ℂ] PS)
    (hρ : (ρ : PS → PS) '' Set.range (PowerSeries.expand p hp : PS →ₐ[ℂ] PS) =
      Set.range (PowerSeries.expand p hp : PS →ₐ[ℂ] PS)) (f : PS) :
    (PowerSeries.expand p hp) ((restrictExpandAlgHom hp ρ hρ) f) =
      ρ ((PowerSeries.expand p hp) f) := by
  unfold restrictExpandAlgHom
  simp only
  exact Classical.choose_spec (show ∃ g, (PowerSeries.expand p hp) g =
    ρ ((PowerSeries.expand p hp) f) from by
      have hmem : ρ ((PowerSeries.expand p hp) f) ∈
          Set.range (PowerSeries.expand p hp : PS →ₐ[ℂ] PS) := by
        have him : ρ ((PowerSeries.expand p hp) f) ∈ (ρ : PS → PS) ''
            Set.range (PowerSeries.expand p hp : PS →ₐ[ℂ] PS) := by
          exact ⟨(PowerSeries.expand p hp) f, ⟨f, rfl⟩, rfl⟩
        rwa [hρ] at him
      rcases hmem with ⟨g, hg⟩
      exact ⟨g, hg⟩)

/- accepted add_to_file helper 6 -/
lemma restrictExpandAlgHom_bijective {p : ℕ} (hp : p ≠ 0)
    (ρ : PS ≃ₐ[ℂ] PS)
    (hρ : (ρ : PS → PS) '' Set.range (PowerSeries.expand p hp : PS →ₐ[ℂ] PS) =
      Set.range (PowerSeries.expand p hp : PS →ₐ[ℂ] PS)) :
    Function.Bijective (restrictExpandAlgHom hp ρ hρ) := by
  let e : PS →ₐ[ℂ] PS := PowerSeries.expand p hp
  let S : Set PS := Set.range e
  constructor
  · intro x y hxy
    apply expand_injective hp
    have hx := restrictExpandAlgHom_spec hp ρ hρ x
    have hy := restrictExpandAlgHom_spec hp ρ hρ y
    have heq : ρ (e x) = ρ (e y) := by
      calc
        ρ (e x) = e ((restrictExpandAlgHom hp ρ hρ) x) := by
          simpa [e] using hx.symm
        _ = e ((restrictExpandAlgHom hp ρ hρ) y) := by rw [hxy]
        _ = ρ (e y) := by simpa [e] using hy
    exact ρ.injective heq
  · intro y
    have hyS : e y ∈ S := ⟨y, rfl⟩
    have him : e y ∈ (ρ : PS → PS) '' S := by
      rwa [hρ]
    rcases him with ⟨x, hxS, hρx⟩
    rcases hxS with ⟨f, rfl⟩
    refine ⟨f, ?_⟩
    apply expand_injective hp
    calc
      e ((restrictExpandAlgHom hp ρ hρ) f) = ρ (e f) := by
        simpa [e] using restrictExpandAlgHom_spec hp ρ hρ f
      _ = e y := hρx

noncomputable def restrictExpandEquiv {p : ℕ} (hp : p ≠ 0)
    (ρ : PS ≃ₐ[ℂ] PS)
    (hρ : (ρ : PS → PS) '' Set.range (PowerSeries.expand p hp : PS →ₐ[ℂ] PS) =
      Set.range (PowerSeries.expand p hp : PS →ₐ[ℂ] PS)) :
    PS ≃ₐ[ℂ] PS :=
  AlgEquiv.ofBijective (restrictExpandAlgHom hp ρ hρ)
    (restrictExpandAlgHom_bijective hp ρ hρ)

lemma restrictExpandEquiv_spec {p : ℕ} (hp : p ≠ 0)
    (ρ : PS ≃ₐ[ℂ] PS)
    (hρ : (ρ : PS → PS) '' Set.range (PowerSeries.expand p hp : PS →ₐ[ℂ] PS) =
      Set.range (PowerSeries.expand p hp : PS →ₐ[ℂ] PS)) (f : PS) :
    (PowerSeries.expand p hp) ((restrictExpandEquiv hp ρ hρ) f) =
      ρ ((PowerSeries.expand p hp) f) := by
  exact restrictExpandAlgHom_spec hp ρ hρ f

/- accepted add_to_file helper 7 -/
noncomputable def restrictExpandMonoidHom {p : ℕ} (hp : p ≠ 0) :
    preservingSubgroup (Set.range (PowerSeries.expand p hp : PS →ₐ[ℂ] PS)) →*
      (⊤ : Subgroup (PS ≃ₐ[ℂ] PS)) where
  toFun ρ := ⟨restrictExpandEquiv hp ρ.1 ρ.2, trivial⟩
  map_one' := by
    apply Subtype.ext
    apply AlgEquiv.ext
    intro f
    apply expand_injective hp
    calc
      (PowerSeries.expand p hp)
          ((restrictExpandEquiv hp (1 : PS ≃ₐ[ℂ] PS) (preservingSubgroup_one _)) f)
          = (1 : PS ≃ₐ[ℂ] PS) ((PowerSeries.expand p hp) f) := by
            exact restrictExpandEquiv_spec hp _ _ f
      _ = (PowerSeries.expand p hp) f := by simp
  map_mul' := by
    intro ρ σ
    apply Subtype.ext
    apply AlgEquiv.ext
    intro f
    apply expand_injective hp
    calc
      (PowerSeries.expand p hp) ((restrictExpandEquiv hp (ρ * σ).1 (ρ * σ).2) f)
          = ((ρ * σ).1 : PS ≃ₐ[ℂ] PS) ((PowerSeries.expand p hp) f) := by
            exact restrictExpandEquiv_spec hp _ _ f
      _ = ρ.1 (σ.1 ((PowerSeries.expand p hp) f)) := by
            simp [AlgEquiv.mul_apply]
      _ = ρ.1 ((PowerSeries.expand p hp) ((restrictExpandEquiv hp σ.1 σ.2) f)) := by
            rw [restrictExpandEquiv_spec hp σ.1 σ.2 f]
      _ = (PowerSeries.expand p hp)
          ((restrictExpandEquiv hp ρ.1 ρ.2) ((restrictExpandEquiv hp σ.1 σ.2) f)) := by
            rw [restrictExpandEquiv_spec hp ρ.1 ρ.2]
      _ = (PowerSeries.expand p hp)
          (((restrictExpandEquiv hp ρ.1 ρ.2) * (restrictExpandEquiv hp σ.1 σ.2) :
            PS ≃ₐ[ℂ] PS) f) := by
            simp [AlgEquiv.mul_apply]

/- accepted add_to_file helper 8 -/
lemma binomialSeries_pow_eq (n : ℕ) (r : ℚ) :
    (PowerSeries.binomialSeries ℂ r) ^ n =
      PowerSeries.binomialSeries ℂ ((n : ℚ) * r) := by
  induction n with
  | zero => simp [PowerSeries.binomialSeries_zero]
  | succ n ih =>
      calc
        (PowerSeries.binomialSeries ℂ r) ^ (n + 1)
            = (PowerSeries.binomialSeries ℂ r) ^ n * PowerSeries.binomialSeries ℂ r := by
                rw [pow_succ]
        _ = PowerSeries.binomialSeries ℂ ((n : ℚ) * r) *
            PowerSeries.binomialSeries ℂ r := by rw [ih]
        _ = PowerSeries.binomialSeries ℂ ((n : ℚ) * r + r) := by
                rw [← PowerSeries.binomialSeries_add]
        _ = PowerSeries.binomialSeries ℂ (((n + 1 : ℕ) : ℚ) * r) := by
                congr 1
                push_cast
                ring

lemma binomialSeries_inv_pow (n : ℕ) (hn : n ≠ 0) :
    (PowerSeries.binomialSeries ℂ ((n : ℚ)⁻¹)) ^ n = 1 + PowerSeries.X := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  calc
    (PowerSeries.binomialSeries ℂ ((n : ℚ)⁻¹)) ^ n
        = PowerSeries.binomialSeries ℂ ((n : ℚ) * (n : ℚ)⁻¹) :=
          binomialSeries_pow_eq n _
    _ = PowerSeries.binomialSeries ℂ (1 : ℚ) := by rw [mul_inv_cancel₀ hnq]
    _ = (1 + PowerSeries.X) ^ 1 := by
          exact PowerSeries.binomialSeries_nat (A := ℂ) (R := ℚ) 1
    _ = 1 + PowerSeries.X := by simp

/- accepted add_to_file helper 9 -/
lemma subst_one {a : PS} (ha : PowerSeries.HasSubst a) :
    PowerSeries.subst a (1 : PowerSeries ℂ) = 1 := by
  rw [← PowerSeries.coe_substAlgHom ha]
  exact map_one (PowerSeries.substAlgHom ha)

lemma subst_one_add_X {a : PS} (ha : PowerSeries.HasSubst a) :
    PowerSeries.subst a (1 + PowerSeries.X : PowerSeries ℂ) = 1 + a := by
  rw [PowerSeries.subst_add ha, subst_one ha, PowerSeries.subst_X ha]

lemma exists_pow_eq_of_constantCoeff_ne_zero {N : ℕ} (hN : 0 < N) (q : PS)
    (hq : PowerSeries.constantCoeff q ≠ 0) : ∃ r : PS, r ^ N = q := by
  classical
  let c : ℂ := PowerSeries.constantCoeff q
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (k := ℂ) c (n := N) hN
  have hb0 : b ≠ 0 := by
    intro hzero
    apply hq
    calc
      c = b ^ N := hb.symm
      _ = 0 := by rw [hzero, zero_pow (Nat.ne_of_gt hN)]
  let u : PS := q * PowerSeries.C c⁻¹
  have huconst : PowerSeries.constantCoeff u = 1 := by
    calc
      PowerSeries.constantCoeff u = c * c⁻¹ := by simp [u, c]
      _ = 1 := mul_inv_cancel₀ hq
  let x : PS := u - 1
  have hxconst : PowerSeries.constantCoeff x = 0 := by
    simp [x, huconst]
  have hx : PowerSeries.HasSubst x :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hxconst
  let B : PowerSeries ℂ := PowerSeries.binomialSeries ℂ ((N : ℚ)⁻¹)
  let t : PS := PowerSeries.subst x B
  have ht : t ^ N = u := by
    calc
      t ^ N = PowerSeries.subst x (B ^ N) := by
        rw [PowerSeries.subst_pow hx]
      _ = PowerSeries.subst x (1 + PowerSeries.X : PowerSeries ℂ) := by
        dsimp [B]
        rw [binomialSeries_inv_pow N (Nat.ne_of_gt hN)]
      _ = 1 + x := subst_one_add_X hx
      _ = u := by simp [x]
  refine ⟨PowerSeries.C b * t, ?_⟩
  calc
    (PowerSeries.C b * t) ^ N = (PowerSeries.C b) ^ N * t ^ N := by
      rw [mul_pow]
    _ = PowerSeries.C c * u := by
      rw [ht]
      congr 1
      calc
        (PowerSeries.C b) ^ N = PowerSeries.C (b ^ N) := by simp [map_pow]
        _ = PowerSeries.C c := by rw [hb]
    _ = q := by
      calc
        PowerSeries.C c * u = q * (PowerSeries.C c * PowerSeries.C c⁻¹) := by
          dsimp [u]
          ring
        _ = q * PowerSeries.C (c * c⁻¹) := by rw [← map_mul]
        _ = q * 1 := by rw [mul_inv_cancel₀ hq, map_one]
        _ = q := mul_one q

/- accepted add_to_file helper 10 -/
lemma algEquiv_constantCoeff_X (ρ : PS ≃ₐ[ℂ] PS) :
    PowerSeries.constantCoeff (ρ PowerSeries.X) = 0 :=
  algHom_constantCoeff_X ρ.toAlgHom

lemma algEquiv_coeff_one_X_ne_zero (ρ : PS ≃ₐ[ℂ] PS) :
    (PowerSeries.coeff 1) (ρ PowerSeries.X) ≠ 0 := by
  intro h1
  have h0 := algEquiv_constantCoeff_X ρ
  have h := algHom_coeff_eq_sum ρ.symm.toAlgHom 1 (ρ PowerSeries.X)
  have hzero : (PowerSeries.coeff 1) (ρ.symm (ρ PowerSeries.X)) = 0 := by
    simpa [Finset.sum_range_succ, h0, h1] using h
  have hone : (PowerSeries.coeff 1) (ρ.symm (ρ PowerSeries.X)) = 1 := by
    simp
  rw [hone] at hzero
  exact one_ne_zero hzero

/- accepted add_to_file helper 11 -/
lemma coeff_pow_eq_zero_of_constantCoeff_zero_of_lt {w : PS}
    (h0 : PowerSeries.constantCoeff w = 0) {i n : ℕ} (h : n < i) :
    (PowerSeries.coeff n) (w ^ i) = 0 := by
  have hXdvd : (PowerSeries.X : PS) ∣ w := by
    rw [PowerSeries.X_dvd_iff]
    exact h0
  have hi : (PowerSeries.X : PS) ^ i ∣ w ^ i := pow_dvd_pow_of_dvd hXdvd i
  have hs : (PowerSeries.X : PS) ^ (n + 1) ∣ (PowerSeries.X : PS) ^ i :=
    pow_dvd_pow (PowerSeries.X : PS) (Nat.succ_le_of_lt h)
  have htail : (PowerSeries.X : PS) ^ (n + 1) ∣ w ^ i := hs.trans hi
  exact (PowerSeries.X_pow_dvd_iff.mp htail) n (Nat.lt_succ_self n)

lemma order_eq_one_of_constantCoeff_zero {w : PS}
    (h0 : PowerSeries.constantCoeff w = 0)
    (h1 : (PowerSeries.coeff 1) w ≠ 0) : w.order = 1 := by
  change w.order = ((1 : ℕ) : ℕ∞)
  rw [PowerSeries.order_eq_nat]
  constructor
  · exact h1
  · intro i hi
    interval_cases i
    simpa [PowerSeries.coeff_zero_eq_constantCoeff] using h0

lemma coeff_self_pow_eq_coeff_one_pow {w : PS} (n : ℕ)
    (h0 : PowerSeries.constantCoeff w = 0)
    (h1 : (PowerSeries.coeff 1) w ≠ 0) :
    (PowerSeries.coeff n) (w ^ n) = ((PowerSeries.coeff 1) w) ^ n := by
  have horder : w.order = 1 := order_eq_one_of_constantCoeff_zero h0 h1
  have horderpow : (w ^ n).order = n := by
    rw [PowerSeries.order_pow, horder]
    simp
  have htoNat : (w ^ n).order.toNat = n := by
    rw [horderpow]
    rfl
  have hdecomp : PowerSeries.X ^ n * (w ^ n).divXPowOrder = w ^ n := by
    have h := PowerSeries.X_pow_order_mul_divXPowOrder (f := w ^ n)
    rwa [htoNat] at h
  have hcoeff_div :
      (PowerSeries.coeff n) (w ^ n) =
        PowerSeries.constantCoeff ((w ^ n).divXPowOrder) := by
    calc
      (PowerSeries.coeff n) (w ^ n)
          = (PowerSeries.coeff n) (PowerSeries.X ^ n * (w ^ n).divXPowOrder) := by
              rw [hdecomp]
      _ = (PowerSeries.coeff 0) ((w ^ n).divXPowOrder) := by
              convert PowerSeries.coeff_X_pow_mul ((w ^ n).divXPowOrder) n 0 using 2
              simp
      _ = PowerSeries.constantCoeff ((w ^ n).divXPowOrder) := by
              rw [PowerSeries.coeff_zero_eq_constantCoeff]
  have hlead : PowerSeries.constantCoeff w.divXPowOrder = (PowerSeries.coeff 1) w := by
    have hdecw : PowerSeries.X ^ 1 * w.divXPowOrder = w := by
      have h := PowerSeries.X_pow_order_mul_divXPowOrder (f := w)
      rwa [horder] at h
    calc
      PowerSeries.constantCoeff w.divXPowOrder
          = (PowerSeries.coeff 0) w.divXPowOrder := by
              rw [PowerSeries.coeff_zero_eq_constantCoeff]
      _ = (PowerSeries.coeff (0 + 1)) (PowerSeries.X ^ 1 * w.divXPowOrder) := by
              rw [PowerSeries.coeff_X_pow_mul]
      _ = (PowerSeries.coeff 1) w := by
              rw [hdecw]
  calc
    (PowerSeries.coeff n) (w ^ n)
        = PowerSeries.constantCoeff ((w ^ n).divXPowOrder) := hcoeff_div
    _ = PowerSeries.constantCoeff (w.divXPowOrder ^ n) := by
          rw [PowerSeries.divXPowOrder_pow]
    _ = (PowerSeries.constantCoeff w.divXPowOrder) ^ n := by simp
    _ = ((PowerSeries.coeff 1) w) ^ n := by rw [hlead]

/- accepted add_to_file helper 12 -/
noncomputable def substPreimage (w g : PS) : PS :=
  PowerSeries.mk fun n =>
    Nat.strongRec
      (fun n rec =>
        ((PowerSeries.coeff n) g -
          ∑ i ∈ Finset.range n,
            (if hi : i < n then rec i hi else 0) *
              (PowerSeries.coeff n) (w ^ i)) *
          (((PowerSeries.coeff 1) w) ^ n)⁻¹)
      n

lemma coeff_substPreimage (w g : PS) (n : ℕ) :
    (PowerSeries.coeff n) (substPreimage w g) =
      ((PowerSeries.coeff n) g -
        ∑ i ∈ Finset.range n,
          (PowerSeries.coeff i) (substPreimage w g) *
            (PowerSeries.coeff n) (w ^ i)) *
        (((PowerSeries.coeff 1) w) ^ n)⁻¹ := by
  rw [substPreimage, PowerSeries.coeff_mk, Nat.strongRec_eq]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i < n := Finset.mem_range.mp hi
  simp [hin]

lemma substAlgHom_surjective_of_constantCoeff_zero {w : PS}
    (h0 : PowerSeries.constantCoeff w = 0)
    (h1 : (PowerSeries.coeff 1) w ≠ 0) :
    Function.Surjective
      (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' h0) :
        PS →ₐ[ℂ] PS) := by
  intro g
  let hw := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  let subhom : PS →ₐ[ℂ] PS := PowerSeries.substAlgHom hw
  let f := substPreimage w g
  refine ⟨f, ?_⟩
  ext n
  have hX : subhom PowerSeries.X = w := by
    change (PowerSeries.substAlgHom hw) PowerSeries.X = w
    rw [PowerSeries.coe_substAlgHom]
    exact PowerSeries.subst_X hw
  have h := algHom_coeff_eq_sum subhom n f
  rw [hX] at h
  let a : ℂ := (PowerSeries.coeff 1) w
  have han : a ^ n ≠ 0 := pow_ne_zero n h1
  have hprev :
      (∑ i ∈ Finset.range (n + 1),
        (PowerSeries.coeff i) f * (PowerSeries.coeff n) (w ^ i)) =
      (∑ i ∈ Finset.range n,
        (PowerSeries.coeff i) f * (PowerSeries.coeff n) (w ^ i)) +
        (PowerSeries.coeff n) f * a ^ n := by
    rw [Finset.sum_range_succ]
    congr 1
    simp [a, coeff_self_pow_eq_coeff_one_pow n h0 h1]
  have hfn :
      (PowerSeries.coeff n) f =
        (((PowerSeries.coeff n) g -
          ∑ i ∈ Finset.range n,
            (PowerSeries.coeff i) f * (PowerSeries.coeff n) (w ^ i)) * (a ^ n)⁻¹) := by
    simpa [f, a] using coeff_substPreimage w g n
  calc
    (PowerSeries.coeff n) (subhom f)
        = ∑ i ∈ Finset.range (n + 1),
          (PowerSeries.coeff i) f * (PowerSeries.coeff n) (w ^ i) := h
    _ = (∑ i ∈ Finset.range n,
          (PowerSeries.coeff i) f * (PowerSeries.coeff n) (w ^ i)) +
          (PowerSeries.coeff n) f * a ^ n := hprev
    _ = (∑ i ∈ Finset.range n,
          (PowerSeries.coeff i) f * (PowerSeries.coeff n) (w ^ i)) +
          (((PowerSeries.coeff n) g -
            ∑ i ∈ Finset.range n,
              (PowerSeries.coeff i) f * (PowerSeries.coeff n) (w ^ i)) *
            (a ^ n)⁻¹) * a ^ n := by rw [hfn]
    _ = (PowerSeries.coeff n) g := by
      rw [mul_assoc, inv_mul_cancel₀ han, mul_one]
      simp

/- accepted add_to_file helper 13 -/
lemma substAlgHom_injective_of_constantCoeff_zero {w : PS}
    (h0 : PowerSeries.constantCoeff w = 0)
    (h1 : (PowerSeries.coeff 1) w ≠ 0) :
    Function.Injective
      (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' h0) :
        PS →ₐ[ℂ] PS) := by
  intro x y hxy
  let hw := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  let subhom : PS →ₐ[ℂ] PS := PowerSeries.substAlgHom hw
  have hX : subhom PowerSeries.X = w := by
    change (PowerSeries.substAlgHom hw) PowerSeries.X = w
    rw [PowerSeries.coe_substAlgHom]
    exact PowerSeries.subst_X hw
  have hd : subhom (x - y) = 0 := by
    calc
      subhom (x - y) = subhom x - subhom y := by simp
      _ = 0 := by simp [subhom, hxy]
  ext n
  have hcoeffzero : ∀ n, (PowerSeries.coeff n) (x - y) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      have h := algHom_coeff_eq_sum subhom n (x - y)
      rw [hX] at h
      have hsum :
          ∑ i ∈ Finset.range (n + 1),
            (PowerSeries.coeff i) (x - y) * (PowerSeries.coeff n) (w ^ i) = 0 := by
        calc
          ∑ i ∈ Finset.range (n + 1),
              (PowerSeries.coeff i) (x - y) * (PowerSeries.coeff n) (w ^ i)
              = (PowerSeries.coeff n) (subhom (x - y)) := h.symm
          _ = 0 := by rw [hd]; simp
      have hprev :
          (∑ i ∈ Finset.range n,
            (PowerSeries.coeff i) (x - y) * (PowerSeries.coeff n) (w ^ i)) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hn : i < n := Finset.mem_range.mp hi
        rw [ih i hn]
        simp
      have hlast :
          (PowerSeries.coeff n) (x - y) * ((PowerSeries.coeff 1) w) ^ n = 0 := by
        have hs := hsum
        rw [Finset.sum_range_succ, hprev, coeff_self_pow_eq_coeff_one_pow n h0 h1] at hs
        simpa using hs
      exact (mul_eq_zero.mp hlast).resolve_right (pow_ne_zero n h1)
  have hn := hcoeffzero n
  simpa [sub_eq_zero] using hn

noncomputable def substAlgEquivOfConstantCoeffZero {w : PS}
    (h0 : PowerSeries.constantCoeff w = 0)
    (h1 : (PowerSeries.coeff 1) w ≠ 0) : PS ≃ₐ[ℂ] PS :=
  AlgEquiv.ofBijective
    (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' h0) :
      PS →ₐ[ℂ] PS)
    ⟨substAlgHom_injective_of_constantCoeff_zero h0 h1,
      substAlgHom_surjective_of_constantCoeff_zero h0 h1⟩

/- accepted add_to_file helper 14 -/
lemma algHom_ext_of_X {φ ψ : PS →ₐ[ℂ] PS}
    (hX : φ PowerSeries.X = ψ PowerSeries.X) : φ = ψ := by
  ext f n
  rw [algHom_coeff_eq_sum φ n f, algHom_coeff_eq_sum ψ n f, hX]

lemma algEquiv_ext_of_X {ρ σ : PS ≃ₐ[ℂ] PS}
    (hX : ρ PowerSeries.X = σ PowerSeries.X) : ρ = σ := by
  apply AlgEquiv.ext
  intro f
  have h : ρ.toAlgHom = σ.toAlgHom := algHom_ext_of_X hX
  exact congrFun (congrArg (⇑) h) f

/- accepted add_to_file helper 15 -/
lemma algEquiv_order_X (ψ : PS ≃ₐ[ℂ] PS) :
    (ψ PowerSeries.X).order = 1 :=
  order_eq_one_of_constantCoeff_zero (algEquiv_constantCoeff_X ψ)
    (algEquiv_coeff_one_X_ne_zero ψ)

/- accepted add_to_file helper 16 -/
lemma expand_order_algEquiv_X {N : ℕ} (hN : N ≠ 0) (ψ : PS ≃ₐ[ℂ] PS) :
    ((PowerSeries.expand N hN) (ψ PowerSeries.X)).order = N := by
  rw [PowerSeries.order_expand, algEquiv_order_X]
  simp

/- accepted add_to_file helper 17 -/
lemma exists_lift_algEquiv_expand {N : ℕ} (hN : 0 < N) (ψ : PS ≃ₐ[ℂ] PS) :
    ∃ σ : PS ≃ₐ[ℂ] PS,
      (∀ f : PS, σ ((PowerSeries.expand N (Nat.ne_of_gt hN)) f) =
        (PowerSeries.expand N (Nat.ne_of_gt hN)) (ψ f)) := by
  classical
  let e : PS →ₐ[ℂ] PS := PowerSeries.expand N (Nat.ne_of_gt hN)
  let q : PS := e (ψ PowerSeries.X)
  have horderq : q.order = N := by
    dsimp [q, e]
    exact expand_order_algEquiv_X (Nat.ne_of_gt hN) ψ
  have hdiv : (PowerSeries.X : PS) ^ N ∣ q := by
    have h := PowerSeries.X_pow_order_dvd (φ := q)
    have hto : q.order.toNat = N := by
      rw [horderq]
      rfl
    rwa [hto] at h
  rcases hdiv with ⟨u, hu⟩
  have huconst : PowerSeries.constantCoeff u ≠ 0 := by
    intro hzero
    have hqN : (PowerSeries.coeff N) q = 0 := by
      calc
        (PowerSeries.coeff N) q = (PowerSeries.coeff N) ((PowerSeries.X : PS) ^ N * u) := by
          rw [hu]
        _ = (PowerSeries.coeff 0) u := by
          convert PowerSeries.coeff_X_pow_mul u N 0 using 2
          simp
        _ = PowerSeries.constantCoeff u := by
          rw [PowerSeries.coeff_zero_eq_constantCoeff]
        _ = 0 := hzero
    have hlead : (PowerSeries.coeff N) q = (PowerSeries.coeff 1) (ψ PowerSeries.X) := by
      dsimp [q, e]
      rw [PowerSeries.coeff_expand]
      have hdivN : N / N = 1 := Nat.div_self hN
      simp [hdivN]
    have hnon := algEquiv_coeff_one_X_ne_zero ψ
    exact hnon (hlead ▸ hqN)
  obtain ⟨r, hr⟩ := exists_pow_eq_of_constantCoeff_ne_zero hN u huconst
  have hrconst : PowerSeries.constantCoeff r ≠ 0 := by
    intro hzero
    apply huconst
    calc
      PowerSeries.constantCoeff u = PowerSeries.constantCoeff (r ^ N) := by rw [← hr]
      _ = (PowerSeries.constantCoeff r) ^ N := by simp
      _ = 0 := by rw [hzero, zero_pow (Nat.ne_of_gt hN)]
  let w : PS := PowerSeries.X * r
  have hw0 : PowerSeries.constantCoeff w = 0 := by
    simp [w]
  have hw1 : (PowerSeries.coeff 1) w ≠ 0 := by
    have hcoeff : (PowerSeries.coeff 1) w = PowerSeries.constantCoeff r := by
      calc
        (PowerSeries.coeff 1) w = (PowerSeries.coeff 1) (r * (PowerSeries.X : PS) ^ 1) := by
          simp [w, mul_comm]
        _ = (PowerSeries.coeff 0) r := by
          convert PowerSeries.coeff_mul_X_pow r 1 0 using 2
        _ = PowerSeries.constantCoeff r := by
          rw [PowerSeries.coeff_zero_eq_constantCoeff]
    rw [hcoeff]
    exact hrconst
  let σ : PS ≃ₐ[ℂ] PS := substAlgEquivOfConstantCoeffZero hw0 hw1
  have hσX : σ PowerSeries.X = w := by
    change (PowerSeries.substAlgHom (PowerSeries.HasSubst.of_constantCoeff_zero' hw0) :
      PS →ₐ[ℂ] PS) PowerSeries.X = w
    rw [PowerSeries.coe_substAlgHom]
    exact PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hw0)
  have hwN : w ^ N = q := by
    calc
      w ^ N = ((PowerSeries.X : PS) * r) ^ N := rfl
      _ = (PowerSeries.X : PS) ^ N * r ^ N := by rw [mul_pow]
      _ = (PowerSeries.X : PS) ^ N * u := by rw [hr]
      _ = q := hu.symm
  refine ⟨σ, ?_⟩
  intro f
  have hcomp : σ.toAlgHom.comp e = e.comp ψ.toAlgHom := by
    apply algHom_ext_of_X
    calc
      (σ.toAlgHom.comp e) PowerSeries.X = σ (e PowerSeries.X) := rfl
      _ = σ ((PowerSeries.X : PS) ^ N) := by
        rw [show e PowerSeries.X = (PowerSeries.X : PS) ^ N by
          dsimp [e]
          exact PowerSeries.expand_X N (Nat.ne_of_gt hN)]
      _ = (σ PowerSeries.X) ^ N := by simp
      _ = w ^ N := by rw [hσX]
      _ = q := hwN
      _ = (e.comp ψ.toAlgHom) PowerSeries.X := rfl
  calc
    σ (e f) = (σ.toAlgHom.comp e) f := rfl
    _ = (e.comp ψ.toAlgHom) f := by rw [hcomp]
    _ = e (ψ f) := rfl

/- accepted add_to_file helper 18 -/
lemma image_range_expand_eq_of_lift {N : ℕ} (hN : 0 < N)
    (σ ψ : PS ≃ₐ[ℂ] PS)
    (hcomm : ∀ f : PS, σ ((PowerSeries.expand N (Nat.ne_of_gt hN)) f) =
      (PowerSeries.expand N (Nat.ne_of_gt hN)) (ψ f)) :
    (σ : PS → PS) '' Set.range (PowerSeries.expand N (Nat.ne_of_gt hN) : PS →ₐ[ℂ] PS) =
      Set.range (PowerSeries.expand N (Nat.ne_of_gt hN) : PS →ₐ[ℂ] PS) := by
  let e : PS →ₐ[ℂ] PS := PowerSeries.expand N (Nat.ne_of_gt hN)
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, hx, rfl⟩
    rcases hx with ⟨f, rfl⟩
    exact ⟨ψ f, (hcomm f).symm⟩
  · intro hy
    rcases hy with ⟨f, rfl⟩
    refine ⟨e (ψ.symm f), ⟨ψ.symm f, rfl⟩, ?_⟩
    calc
      σ (e (ψ.symm f)) = e (ψ (ψ.symm f)) := hcomm _
      _ = e f := by simp

/- accepted add_to_file helper 19 -/
lemma restrictExpandMonoidHom_lift {N : ℕ} (hN : 0 < N)
    (σ ψ : PS ≃ₐ[ℂ] PS)
    (hcomm : ∀ f : PS, σ ((PowerSeries.expand N (Nat.ne_of_gt hN)) f) =
      (PowerSeries.expand N (Nat.ne_of_gt hN)) (ψ f)) :
    ((restrictExpandMonoidHom (Nat.ne_of_gt hN)
      ⟨σ, image_range_expand_eq_of_lift hN σ ψ hcomm⟩ :
        (⊤ : Subgroup (PS ≃ₐ[ℂ] PS))).1 : PS ≃ₐ[ℂ] PS) = ψ := by
  apply AlgEquiv.ext
  intro f
  apply expand_injective (Nat.ne_of_gt hN)
  calc
    (PowerSeries.expand N (Nat.ne_of_gt hN))
        (((restrictExpandMonoidHom (Nat.ne_of_gt hN)
          ⟨σ, image_range_expand_eq_of_lift hN σ ψ hcomm⟩ :
            (⊤ : Subgroup (PS ≃ₐ[ℂ] PS))).1 : PS ≃ₐ[ℂ] PS) f)
        = σ ((PowerSeries.expand N (Nat.ne_of_gt hN)) f) := by
          exact restrictExpandEquiv_spec _ _ _ f
    _ = (PowerSeries.expand N (Nat.ne_of_gt hN)) (ψ f) := hcomm f

/- accepted add_to_file helper 20 -/
lemma eq_one_of_pow_eq_one_of_constantCoeff_eq_one {N : ℕ} (hN : 0 < N) {u : PS}
    (huN : u ^ N = 1) (hu0 : PowerSeries.constantCoeff u = 1) : u = 1 := by
  have hfac : (u - 1) * ∑ i ∈ Finset.range N, u ^ i = 0 := by
    calc
      (u - 1) * ∑ i ∈ Finset.range N, u ^ i = u ^ N - 1 := mul_geom_sum u N
      _ = 0 := by rw [huN, sub_self]
  have hsum_ne : ∑ i ∈ Finset.range N, u ^ i ≠ 0 := by
    intro hzero
    have hconst : PowerSeries.constantCoeff (∑ i ∈ Finset.range N, u ^ i) = N := by
      simp [map_sum, map_pow, hu0]
    have hNzero : (N : ℂ) = 0 := by
      calc
        (N : ℂ) = PowerSeries.constantCoeff (∑ i ∈ Finset.range N, u ^ i) := by
          simp [hconst]
        _ = 0 := by rw [hzero]; simp
    exact (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)) hNzero
  have hsub : u - 1 = 0 := (mul_eq_zero.mp hfac).resolve_right hsum_ne
  exact sub_eq_zero.mp hsub

/- accepted add_to_file helper 21 -/
lemma coeff_one_ne_zero_of_pow_eq_X_pow {N : ℕ} (hN : 0 < N) {v : PS}
    (h0 : PowerSeries.constantCoeff v = 0) (hv : v ^ N = (PowerSeries.X : PS) ^ N) :
    (PowerSeries.coeff 1) v ≠ 0 := by
  intro h1
  have hX2 : (PowerSeries.X : PS) ^ 2 ∣ v := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · simpa [PowerSeries.coeff_zero_eq_constantCoeff] using h0
    · exact h1
  have hpow : (PowerSeries.X : PS) ^ (2 * N) ∣ v ^ N := by
    have h := pow_dvd_pow_of_dvd hX2 N
    simpa [pow_mul] using h
  have hXN : (PowerSeries.X : PS) ^ (N + 1) ∣ (PowerSeries.X : PS) ^ N := by
    have hs : (PowerSeries.X : PS) ^ (N + 1) ∣ (PowerSeries.X : PS) ^ (2 * N) := by
      apply pow_dvd_pow
      omega
    have ht : (PowerSeries.X : PS) ^ (2 * N) ∣ (PowerSeries.X : PS) ^ N := by
      rw [← hv]
      exact hpow
    exact hs.trans ht
  have hcoeff : (PowerSeries.coeff N) ((PowerSeries.X : PS) ^ N) = 0 :=
    (PowerSeries.X_pow_dvd_iff.mp hXN) N (Nat.lt_succ_self N)
  have hone : (PowerSeries.coeff N) ((PowerSeries.X : PS) ^ N) = 1 := by
    simp
  rw [hone] at hcoeff
  exact one_ne_zero hcoeff

/- accepted add_to_file helper 22 -/
lemma constantCoeff_divXPowOrder_of_order_eq_one {w : PS}
    (horder : w.order = 1) :
    PowerSeries.constantCoeff w.divXPowOrder = (PowerSeries.coeff 1) w := by
  have hdecw : PowerSeries.X ^ 1 * w.divXPowOrder = w := by
    have h := PowerSeries.X_pow_order_mul_divXPowOrder (f := w)
    rwa [horder] at h
  calc
    PowerSeries.constantCoeff w.divXPowOrder
        = (PowerSeries.coeff 0) w.divXPowOrder := by
            rw [PowerSeries.coeff_zero_eq_constantCoeff]
    _ = (PowerSeries.coeff (0 + 1)) (PowerSeries.X ^ 1 * w.divXPowOrder) := by
            rw [PowerSeries.coeff_X_pow_mul]
    _ = (PowerSeries.coeff 1) w := by
            rw [hdecw]

/- accepted add_to_file helper 23 -/
lemma exists_root_of_pow_eq_X_pow {N : ℕ} (hN : 0 < N) {v : PS}
    (h0 : PowerSeries.constantCoeff v = 0) (hv : v ^ N = (PowerSeries.X : PS) ^ N) :
    ∃ ε : rootsOfUnity N ℂ,
      v = algebraMap ℂ PS (((ε : ℂˣ) : ℂ)) * PowerSeries.X := by
  let a : ℂ := (PowerSeries.coeff 1) v
  have ha0 : a ≠ 0 := coeff_one_ne_zero_of_pow_eq_X_pow hN h0 hv
  have haN : a ^ N = 1 := by
    have hc := congrArg (PowerSeries.coeff N) hv
    rw [coeff_self_pow_eq_coeff_one_pow N h0 ha0] at hc
    simpa [a] using hc
  let εu : ℂˣ := Units.ofPowEqOne a N haN (Nat.ne_of_gt hN)
  have hεmem : εu ∈ rootsOfUnity N ℂ := by
    simp [rootsOfUnity, εu]
  let ε : rootsOfUnity N ℂ := ⟨εu, hεmem⟩
  have hεval : (((ε : ℂˣ) : ℂ)) = a := by
    simp [ε, εu]
  refine ⟨ε, ?_⟩
  let t : PS := PowerSeries.C a⁻¹ * v
  have htN : t ^ N = (PowerSeries.X : PS) ^ N := by
    calc
      t ^ N = (PowerSeries.C a⁻¹) ^ N * v ^ N := by
        dsimp [t]
        rw [mul_pow]
      _ = PowerSeries.C ((a⁻¹) ^ N) * (PowerSeries.X : PS) ^ N := by
        rw [hv]
        congr 1
        rw [← map_pow, inv_pow]
      _ = (PowerSeries.X : PS) ^ N := by
        rw [inv_pow, haN, inv_one, map_one, one_mul]
  have ht0 : PowerSeries.constantCoeff t = 0 := by
    simp [t, h0]
  have ht1 : (PowerSeries.coeff 1) t = 1 := by
    calc
      (PowerSeries.coeff 1) t = a⁻¹ * a := by simp [t, a]
      _ = 1 := inv_mul_cancel₀ ha0
  have htorder : t.order = 1 := by
    apply order_eq_one_of_constantCoeff_zero ht0
    rw [ht1]
    exact one_ne_zero
  let u : PS := t.divXPowOrder
  have htdecomp : (PowerSeries.X : PS) * u = t := by
    have h := PowerSeries.X_pow_order_mul_divXPowOrder (f := t)
    rw [htorder] at h
    simpa [u] using h
  have huN : u ^ N = 1 := by
    have hmul : (PowerSeries.X : PS) ^ N * u ^ N = (PowerSeries.X : PS) ^ N * 1 := by
      calc
        (PowerSeries.X : PS) ^ N * u ^ N = ((PowerSeries.X : PS) * u) ^ N := by
          rw [mul_pow]
        _ = t ^ N := by rw [htdecomp]
        _ = (PowerSeries.X : PS) ^ N := htN
        _ = (PowerSeries.X : PS) ^ N * 1 := by simp
    have hXne : (PowerSeries.X : PS) ^ N ≠ 0 := by simp
    exact mul_left_cancel₀ hXne hmul
  have hu0 : PowerSeries.constantCoeff u = 1 := by
    calc
      PowerSeries.constantCoeff u = (PowerSeries.coeff 1) t := by
        dsimp [u]
        exact constantCoeff_divXPowOrder_of_order_eq_one htorder
      _ = 1 := ht1
  have hu : u = 1 := eq_one_of_pow_eq_one_of_constantCoeff_eq_one hN huN hu0
  have htX : t = PowerSeries.X := by
    calc
      t = (PowerSeries.X : PS) * u := htdecomp.symm
      _ = PowerSeries.X := by rw [hu, mul_one]
  calc
    v = PowerSeries.C a * t := by
      dsimp [t]
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha0, map_one, one_mul]
    _ = PowerSeries.C a * PowerSeries.X := by rw [htX]
    _ = algebraMap ℂ PS (((ε : ℂˣ) : ℂ)) * PowerSeries.X := by
      rw [hεval, PowerSeries.C_eq_algebraMap]

/- accepted add_to_file helper 24 -/
noncomputable def rootScaleAlgEquiv {N : ℕ} (ε : rootsOfUnity N ℂ) : PS ≃ₐ[ℂ] PS :=
  let a : ℂ := ((ε : ℂˣ) : ℂ)
  substAlgEquivOfConstantCoeffZero (w := algebraMap ℂ PS a * PowerSeries.X)
    (by simp)
    (by
      have ha : a ≠ 0 := Units.ne_zero _
      simpa [a] using ha)

lemma rootScaleAlgEquiv_X {N : ℕ} (ε : rootsOfUnity N ℂ) :
    (rootScaleAlgEquiv ε) PowerSeries.X =
      algebraMap ℂ PS (((ε : ℂˣ) : ℂ)) * PowerSeries.X := by
  let a : ℂ := ((ε : ℂˣ) : ℂ)
  have h0 : PowerSeries.constantCoeff (algebraMap ℂ PS a * PowerSeries.X) = 0 := by
    simp
  change (PowerSeries.substAlgHom
      (PowerSeries.HasSubst.of_constantCoeff_zero' h0) :
      PS →ₐ[ℂ] PS) PowerSeries.X = _
  rw [PowerSeries.coe_substAlgHom]
  exact PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' h0)

/- accepted add_to_file helper 25 -/
lemma rootScaleAlgEquiv_expand {N : ℕ} (hN : 0 < N) (ε : rootsOfUnity N ℂ)
    (f : PS) :
    (rootScaleAlgEquiv ε) ((PowerSeries.expand N (Nat.ne_of_gt hN)) f) =
      (PowerSeries.expand N (Nat.ne_of_gt hN)) f := by
  let e : PS →ₐ[ℂ] PS := PowerSeries.expand N (Nat.ne_of_gt hN)
  have hcomp : (rootScaleAlgEquiv ε).toAlgHom.comp e = e := by
    apply algHom_ext_of_X
    calc
      ((rootScaleAlgEquiv ε).toAlgHom.comp e) PowerSeries.X
          = (rootScaleAlgEquiv ε) (e PowerSeries.X) := rfl
      _ = (rootScaleAlgEquiv ε) ((PowerSeries.X : PS) ^ N) := by
        rw [show e PowerSeries.X = (PowerSeries.X : PS) ^ N by
          dsimp [e]
          exact PowerSeries.expand_X N (Nat.ne_of_gt hN)]
      _ = ((rootScaleAlgEquiv ε) PowerSeries.X) ^ N := by simp
      _ = (algebraMap ℂ PS (((ε : ℂˣ) : ℂ)) * PowerSeries.X) ^ N := by
        rw [rootScaleAlgEquiv_X]
      _ = (PowerSeries.X : PS) ^ N := by
        have hu : (ε : ℂˣ) ^ N = 1 := ε.2
        have hroot : ((((ε : ℂˣ) : ℂ)) ^ N) = 1 := by
          have hv := congrArg Units.val hu
          simpa using hv
        calc
          (algebraMap ℂ PS (((ε : ℂˣ) : ℂ)) * PowerSeries.X) ^ N
              = (algebraMap ℂ PS (((ε : ℂˣ) : ℂ))) ^ N * PowerSeries.X ^ N := by
                  rw [mul_pow]
          _ = algebraMap ℂ PS ((((ε : ℂˣ) : ℂ)) ^ N) * PowerSeries.X ^ N := by
                  simp
          _ = (PowerSeries.X : PS) ^ N := by rw [hroot, map_one, one_mul]
      _ = e PowerSeries.X := by
        rw [show e PowerSeries.X = (PowerSeries.X : PS) ^ N by
          dsimp [e]
          exact PowerSeries.expand_X N (Nat.ne_of_gt hN)]
  calc
    (rootScaleAlgEquiv ε) (e f) = ((rootScaleAlgEquiv ε).toAlgHom.comp e) f := rfl
    _ = e f := by rw [hcomp]

/- accepted add_to_file helper 26 -/
noncomputable def rootScaleMonoidHom {N : ℕ} (hN : 0 < N) :
    rootsOfUnity N ℂ →*
      preservingSubgroup (Set.range (PowerSeries.expand N (Nat.ne_of_gt hN) : PS →ₐ[ℂ] PS)) where
  toFun ε :=
    ⟨rootScaleAlgEquiv ε,
      image_range_expand_eq_of_lift hN (rootScaleAlgEquiv ε) 1 (fun f => by
        simpa using rootScaleAlgEquiv_expand hN ε f)⟩
  map_one' := by
    apply Subtype.ext
    apply algEquiv_ext_of_X
    rw [rootScaleAlgEquiv_X]
    simp
  map_mul' := by
    intro ε δ
    apply Subtype.ext
    apply algEquiv_ext_of_X
    calc
      (rootScaleAlgEquiv (ε * δ)) PowerSeries.X
          = algebraMap ℂ PS ((((ε * δ : rootsOfUnity N ℂ) : ℂˣ) : ℂ)) * PowerSeries.X :=
            rootScaleAlgEquiv_X _
      _ = algebraMap ℂ PS (((ε : ℂˣ) : ℂ) * ((δ : ℂˣ) : ℂ)) * PowerSeries.X := by
            congr 2
      _ = (rootScaleAlgEquiv ε) ((rootScaleAlgEquiv δ) PowerSeries.X) := by
            rw [rootScaleAlgEquiv_X]
            calc
              algebraMap ℂ PS (((ε : ℂˣ) : ℂ) * ((δ : ℂˣ) : ℂ)) * PowerSeries.X
                  = (algebraMap ℂ PS (((ε : ℂˣ) : ℂ)) *
                      algebraMap ℂ PS (((δ : ℂˣ) : ℂ))) * PowerSeries.X := by
                      rw [map_mul]
              _ = algebraMap ℂ PS (((δ : ℂˣ) : ℂ)) *
                    (algebraMap ℂ PS (((ε : ℂˣ) : ℂ)) * PowerSeries.X) := by
                    ring
              _ = (rootScaleAlgEquiv ε)
                    (algebraMap ℂ PS (((δ : ℂˣ) : ℂ)) * PowerSeries.X) := by
                    rw [map_mul]
                    have hC : (rootScaleAlgEquiv ε)
                        ((algebraMap ℂ PS) (((δ : ℂˣ) : ℂ))) =
                      (algebraMap ℂ PS) (((δ : ℂˣ) : ℂ)) :=
                      (rootScaleAlgEquiv ε).commutes _
                    rw [hC, rootScaleAlgEquiv_X]
      _ = ((rootScaleAlgEquiv ε * rootScaleAlgEquiv δ : PS ≃ₐ[ℂ] PS)) PowerSeries.X := by
            rw [AlgEquiv.mul_apply]

/- accepted add_to_file helper 27 -/
lemma rootScaleMonoidHom_injective {N : ℕ} (hN : 0 < N) :
    Function.Injective (rootScaleMonoidHom hN) := by
  intro ε δ h
  have hX := congrArg (fun ρ :
      preservingSubgroup (Set.range (PowerSeries.expand N (Nat.ne_of_gt hN) : PS →ₐ[ℂ] PS)) =>
      (ρ.1 : PS ≃ₐ[ℂ] PS) PowerSeries.X) h
  change (rootScaleAlgEquiv ε) PowerSeries.X = (rootScaleAlgEquiv δ) PowerSeries.X at hX
  rw [rootScaleAlgEquiv_X, rootScaleAlgEquiv_X] at hX
  have hcoeff := congrArg (PowerSeries.coeff 1) hX
  simp at hcoeff
  apply Subtype.ext
  apply Units.ext
  exact hcoeff

/- accepted add_to_file helper 28 -/
lemma restrictExpandMonoidHom_rootScale {N : ℕ} (hN : 0 < N)
    (ε : rootsOfUnity N ℂ) :
    (restrictExpandMonoidHom (Nat.ne_of_gt hN)) ((rootScaleMonoidHom hN) ε) = 1 := by
  have h := restrictExpandMonoidHom_lift hN (rootScaleAlgEquiv ε) 1 (fun f => by
    simpa using rootScaleAlgEquiv_expand hN ε f)
  apply Subtype.ext
  exact h

/- accepted add_to_file helper 29 -/
lemma rootScaleMonoidHom_range_eq_restrictExpandMonoidHom_ker {N : ℕ} (hN : 0 < N) :
    (rootScaleMonoidHom hN).range =
      (restrictExpandMonoidHom (Nat.ne_of_gt hN)).ker := by
  apply le_antisymm
  · intro ρ hρ
    rcases hρ with ⟨ε, rfl⟩
    exact restrictExpandMonoidHom_rootScale hN ε
  · intro ρ hρ
    have hunder :
        (((restrictExpandMonoidHom (Nat.ne_of_gt hN)) ρ).1 :
          PS ≃ₐ[ℂ] PS) = 1 :=
      congrArg Subtype.val hρ
    let e : PS →ₐ[ℂ] PS := PowerSeries.expand N (Nat.ne_of_gt hN)
    have hspec := restrictExpandEquiv_spec (Nat.ne_of_gt hN) ρ.1 ρ.2 PowerSeries.X
    have hpow : (ρ.1 PowerSeries.X) ^ N = (PowerSeries.X : PS) ^ N := by
      calc
        (ρ.1 PowerSeries.X) ^ N = ρ.1 ((PowerSeries.X : PS) ^ N) := by simp
        _ = ρ.1 (e PowerSeries.X) := by
          rw [show e PowerSeries.X = (PowerSeries.X : PS) ^ N by
            dsimp [e]
            exact PowerSeries.expand_X N (Nat.ne_of_gt hN)]
        _ = e ((((restrictExpandMonoidHom (Nat.ne_of_gt hN)) ρ).1 :
            PS ≃ₐ[ℂ] PS) PowerSeries.X) := by
          dsimp [e] at hspec ⊢
          exact hspec.symm
        _ = e PowerSeries.X := by rw [hunder]; simp
        _ = (PowerSeries.X : PS) ^ N := by
          dsimp [e]
          exact PowerSeries.expand_X N (Nat.ne_of_gt hN)
    have h0 := algEquiv_constantCoeff_X ρ.1
    obtain ⟨ε, hε⟩ := exists_root_of_pow_eq_X_pow hN h0 hpow
    refine ⟨ε, ?_⟩
    apply Subtype.ext
    apply algEquiv_ext_of_X
    calc
      ((rootScaleMonoidHom hN) ε).1 PowerSeries.X =
          algebraMap ℂ PS (((ε : ℂˣ) : ℂ)) * PowerSeries.X := by
            change (rootScaleAlgEquiv ε) PowerSeries.X = _
            exact rootScaleAlgEquiv_X ε
      _ = ρ.1 PowerSeries.X := hε.symm

/- accepted add_to_file helper 30 -/
lemma algEquiv_coeff_one_mul_X (ρ σ : PS ≃ₐ[ℂ] PS) :
    (PowerSeries.coeff 1) ((ρ * σ) PowerSeries.X) =
      (PowerSeries.coeff 1) (ρ PowerSeries.X) *
        (PowerSeries.coeff 1) (σ PowerSeries.X) := by
  have h := algHom_coeff_eq_sum ρ.toAlgHom 1 (σ PowerSeries.X)
  have h0 := algEquiv_constantCoeff_X σ
  calc
    (PowerSeries.coeff 1) ((ρ * σ) PowerSeries.X)
        = (PowerSeries.coeff 1) (ρ (σ PowerSeries.X)) := by
          rw [AlgEquiv.mul_apply]
    _ = ∑ i ∈ Finset.range 2,
        (PowerSeries.coeff i) (σ PowerSeries.X) *
          (PowerSeries.coeff 1) ((ρ PowerSeries.X) ^ i) := by
          simpa using h
    _ = (PowerSeries.coeff 1) (ρ PowerSeries.X) *
        (PowerSeries.coeff 1) (σ PowerSeries.X) := by
          simp [Finset.sum_range_succ, h0, mul_comm]

noncomputable def algEquivLeadingUnit (ρ : PS ≃ₐ[ℂ] PS) : ℂˣ where
  val := (PowerSeries.coeff 1) (ρ PowerSeries.X)
  inv := (PowerSeries.coeff 1) (ρ.symm PowerSeries.X)
  val_inv := by
    have h := algEquiv_coeff_one_mul_X ρ ρ.symm
    rw [← h]
    simp
  inv_val := by
    have h := algEquiv_coeff_one_mul_X ρ.symm ρ
    rw [← h]
    simp

/- accepted add_to_file helper 31 -/
noncomputable def algEquivLeadingMonoidHom : (PS ≃ₐ[ℂ] PS) →* ℂˣ where
  toFun := algEquivLeadingUnit
  map_one' := by
    apply Units.ext
    simp [algEquivLeadingUnit]
  map_mul' := by
    intro ρ σ
    apply Units.ext
    change (PowerSeries.coeff 1) ((ρ * σ) PowerSeries.X) =
      (PowerSeries.coeff 1) (ρ PowerSeries.X) *
        (PowerSeries.coeff 1) (σ PowerSeries.X)
    exact algEquiv_coeff_one_mul_X ρ σ

/- accepted add_to_file helper 32 -/
lemma algEquivLeadingMonoidHom_rootScale {N : ℕ} (ε : rootsOfUnity N ℂ) :
    algEquivLeadingMonoidHom (rootScaleAlgEquiv ε) = (ε : ℂˣ) := by
  apply Units.ext
  change (PowerSeries.coeff 1) ((rootScaleAlgEquiv ε) PowerSeries.X) =
    (((ε : ℂˣ) : ℂ))
  rw [rootScaleAlgEquiv_X]
  simp

/- accepted add_to_file helper 33 -/
lemma rootScaleMonoidHom_range_le_center {N : ℕ} (hN : 0 < N) :
    (rootScaleMonoidHom hN).range ≤
      Subgroup.center
        (preservingSubgroup (Set.range (PowerSeries.expand N (Nat.ne_of_gt hN) :
          PS →ₐ[ℂ] PS))) := by
  intro x hx
  rcases hx with ⟨ε, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  let D := preservingSubgroup (Set.range (PowerSeries.expand N (Nat.ne_of_gt hN) :
    PS →ₐ[ℂ] PS))
  let a : D := (rootScaleMonoidHom hN) ε
  let τ : D := a * y * a⁻¹ * y⁻¹
  let μ : D →* (⊤ : Subgroup (PS ≃ₐ[ℂ] PS)) := restrictExpandMonoidHom (Nat.ne_of_gt hN)
  have hker : τ ∈ μ.ker := by
    rw [MonoidHom.mem_ker]
    have hcalc : μ τ = μ a * μ y * (μ a)⁻¹ * (μ y)⁻¹ := by
      dsimp [τ]
      rw [μ.map_mul, μ.map_mul, μ.map_mul, μ.map_inv, μ.map_inv]
    have haμ : μ a = 1 := restrictExpandMonoidHom_rootScale hN ε
    rw [hcalc, haμ]
    simp
  let L : (PS ≃ₐ[ℂ] PS) →* ℂˣ := algEquivLeadingMonoidHom
  have hleadcalc :
      L (τ.1 : PS ≃ₐ[ℂ] PS) =
        L (a.1 : PS ≃ₐ[ℂ] PS) * L (y.1 : PS ≃ₐ[ℂ] PS) *
          (L (a.1 : PS ≃ₐ[ℂ] PS))⁻¹ * (L (y.1 : PS ≃ₐ[ℂ] PS))⁻¹ := by
    dsimp [τ]
    rw [L.map_mul, L.map_mul, L.map_mul, L.map_inv, L.map_inv]
  have hlead : L (τ.1 : PS ≃ₐ[ℂ] PS) = 1 := by
    have ha : L (a.1 : PS ≃ₐ[ℂ] PS) = (ε : ℂˣ) := by
      change L (rootScaleAlgEquiv ε) = (ε : ℂˣ)
      exact algEquivLeadingMonoidHom_rootScale ε
    rw [hleadcalc, ha]
    simp
  have hrange : τ ∈ (rootScaleMonoidHom hN).range := by
    rw [rootScaleMonoidHom_range_eq_restrictExpandMonoidHom_ker hN]
    exact hker
  rcases hrange with ⟨δ, hδ⟩
  have hδunit : (δ : ℂˣ) = 1 := by
    calc
      (δ : ℂˣ) = L ((rootScaleAlgEquiv δ) : PS ≃ₐ[ℂ] PS) :=
        (algEquivLeadingMonoidHom_rootScale δ).symm
      _ = L (τ.1 : PS ≃ₐ[ℂ] PS) := by
        rw [← hδ]
        rfl
      _ = 1 := hlead
  have hδroot : δ = 1 := by
    apply Subtype.ext
    exact hδunit
  have hτ : τ = 1 := by
    rw [← hδ, hδroot, map_one]
  have hconj : a * y * a⁻¹ = y := by
    have h := congrArg (· * y) hτ
    simpa [τ, mul_assoc] using h
  have hcomm : a * y = y * a := by
    have h := congrArg (· * a) hconj
    simpa [mul_assoc] using h
  calc
    y * (rootScaleMonoidHom hN) ε = y * a := by rfl
    _ = a * y := hcomm.symm
    _ = (rootScaleMonoidHom hN) ε * y := by rfl

/- accepted add_to_file helper 34 -/
end FPSAut

open FPSAut

/- verified submission -/
theorem formalPowerSeries_automorphism_exact_sequence (N : ℕ) (hN : 2 ≤ N) :
  let A := PowerSeries ℂ
  let _ : TopologicalSpace A :=
    PowerSeries.WithPiTopology.instTopologicalSpace ℂ
  let e : A →ₐ[ℂ] A :=
    PowerSeries.expand N (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hN))
  let G := A ≃ₐ[ℂ] A
  let S : Set A := Set.range e
  ∃ (Aut : Subgroup G) (AutN : Subgroup G),
    (∀ ρ : G, ρ ∈ Aut ↔
      Continuous (ρ : A → A) ∧ Continuous (ρ.symm : A → A)) ∧
    (∀ ρ : G, ρ ∈ AutN ↔
      Continuous (ρ : A → A) ∧ Continuous (ρ.symm : A → A) ∧ ρ '' S = S) ∧
    ∃ (ι : rootsOfUnity N ℂ →* AutN) (μ : AutN →* Aut),
      (∀ (ρ : AutN) (f : A), e ((μ ρ : G) f) = (ρ : G) (e f)) ∧
      (∀ ρ : AutN,
        e ((μ ρ : G) PowerSeries.X) = ((ρ : G) PowerSeries.X) ^ N) ∧
      (∀ ε : rootsOfUnity N ℂ,
        (ι ε : G) PowerSeries.X =
          algebraMap ℂ A (((ε : ℂˣ) : ℂ)) * PowerSeries.X) ∧
      Function.Injective ι ∧
      Function.Surjective μ ∧
      ι.range = μ.ker ∧
      ι.range ≤ Subgroup.center AutN := by
  classical
  let hNpos : 0 < N := lt_of_lt_of_le Nat.zero_lt_two hN
  let A := PowerSeries ℂ
  let htop : TopologicalSpace A :=
    PowerSeries.WithPiTopology.instTopologicalSpace ℂ
  let e : A →ₐ[ℂ] A := PowerSeries.expand N (Nat.ne_of_gt hNpos)
  let G := A ≃ₐ[ℂ] A
  let S : Set A := Set.range e
  let Aut : Subgroup G := ⊤
  let AutN : Subgroup G := preservingSubgroup S
  refine ⟨Aut, AutN, ?_, ?_, ?_⟩
  · intro ρ
    constructor
    · intro _
      exact algEquiv_continuous ρ
    · intro _
      trivial
  · intro ρ
    constructor
    · intro hρ
      have hc := algEquiv_continuous ρ
      exact ⟨hc.1, hc.2, hρ⟩
    · intro hρ
      exact hρ.2.2
  · let ι : rootsOfUnity N ℂ →* AutN := rootScaleMonoidHom hNpos
    let μ : AutN →* Aut := restrictExpandMonoidHom (Nat.ne_of_gt hNpos)
    refine ⟨ι, μ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ρ f
      exact restrictExpandEquiv_spec (Nat.ne_of_gt hNpos) ρ.1 ρ.2 f
    · intro ρ
      calc
        e ((μ ρ : G) PowerSeries.X) = (ρ : G) (e PowerSeries.X) :=
          restrictExpandEquiv_spec (Nat.ne_of_gt hNpos) ρ.1 ρ.2 PowerSeries.X
        _ = ((ρ : G) PowerSeries.X) ^ N := by
          rw [show e PowerSeries.X = (PowerSeries.X : A) ^ N by
            dsimp [e]
            exact PowerSeries.expand_X N (Nat.ne_of_gt hNpos)]
          simp
    · intro ε
      exact rootScaleAlgEquiv_X ε
    · exact rootScaleMonoidHom_injective hNpos
    · intro y
      obtain ⟨σ, hcomm⟩ := exists_lift_algEquiv_expand hNpos (y.1 : G)
      let hmem : (σ : G) '' S = S :=
        image_range_expand_eq_of_lift hNpos σ y.1 hcomm
      refine ⟨⟨σ, hmem⟩, ?_⟩
      apply Subtype.ext
      exact restrictExpandMonoidHom_lift hNpos σ y.1 hcomm
    · exact rootScaleMonoidHom_range_eq_restrictExpandMonoidHom_ker hNpos
    · exact rootScaleMonoidHom_range_le_center hNpos

/- Scopes closed implicitly by EOF in the original file. -/
end

end Rollout_p0246_formalpowerseries_automorphism_exact_seque

namespace Rollout_p1971_finite_diversity_induces_metric

/- verified submission -/
lemma finite_diversity_singleton_zero
    {X : Type*} (δ : {A : Set X // A.Finite} → ℝ)
    (h_zero : ∀ A : {A : Set X // A.Finite}, δ A = 0 ↔ A.1.Subsingleton)
    (x : X) :
    δ ⟨{x}, Set.finite_singleton x⟩ = 0 := by
  exact (h_zero _).2 Set.subsingleton_singleton

lemma finite_diversity_pair_self
    {X : Type*} (δ : {A : Set X // A.Finite} → ℝ)
    (h_zero : ∀ A : {A : Set X // A.Finite}, δ A = 0 ↔ A.1.Subsingleton)
    (x : X) :
    δ ⟨{x, x}, (Set.finite_singleton x).insert x⟩ = 0 := by
  apply (h_zero _).2
  intro a ha b hb
  simp at ha hb
  subst a
  subst b
  rfl

lemma finite_diversity_pair_comm
    {X : Type*} (δ : {A : Set X // A.Finite} → ℝ)
    (x y : X) :
    δ ⟨{x, y}, (Set.finite_singleton y).insert x⟩ =
      δ ⟨{y, x}, (Set.finite_singleton x).insert y⟩ := by
  exact congrArg δ (Subtype.ext (Set.pair_comm x y))

lemma finite_diversity_pair_eq
    {X : Type*} (δ : {A : Set X // A.Finite} → ℝ)
    (h_zero : ∀ A : {A : Set X // A.Finite}, δ A = 0 ↔ A.1.Subsingleton)
    {x y : X}
    (h : δ ⟨{x, y}, (Set.finite_singleton y).insert x⟩ = 0) : x = y := by
  have hs : ({x, y} : Set X).Subsingleton := (h_zero _).1 h
  exact hs (by simp) (by simp)

lemma finite_diversity_pair_triangle
    {X : Type*} (δ : {A : Set X // A.Finite} → ℝ)
    (h_triangle : ∀ A B C : {A : Set X // A.Finite}, B.1.Nonempty →
      δ ⟨A.1 ∪ C.1, A.2.union C.2⟩ ≤
        δ ⟨A.1 ∪ B.1, A.2.union B.2⟩ + δ ⟨B.1 ∪ C.1, B.2.union C.2⟩)
    (x y z : X) :
    δ ⟨{x, z}, (Set.finite_singleton z).insert x⟩ ≤
      δ ⟨{x, y}, (Set.finite_singleton y).insert x⟩ +
        δ ⟨{y, z}, (Set.finite_singleton z).insert y⟩ := by
  have h := h_triangle ⟨{x}, Set.finite_singleton x⟩
    ⟨{y}, Set.finite_singleton y⟩ ⟨{z}, Set.finite_singleton z⟩
    (Set.singleton_nonempty y)
  simpa [Set.singleton_union, Set.pair_comm] using h

lemma finite_diversity_mono
    {X : Type*} (δ : {A : Set X // A.Finite} → ℝ)
    (h_zero : ∀ A : {A : Set X // A.Finite}, δ A = 0 ↔ A.1.Subsingleton)
    (h_triangle : ∀ A B C : {A : Set X // A.Finite}, B.1.Nonempty →
      δ ⟨A.1 ∪ C.1, A.2.union C.2⟩ ≤
        δ ⟨A.1 ∪ B.1, A.2.union B.2⟩ + δ ⟨B.1 ∪ C.1, B.2.union C.2⟩)
    (A B : {A : Set X // A.Finite}) (hAB : A.1 ⊆ B.1) :
    δ A ≤ δ B := by
  have hkey : ∀ D : Set X, ∀ hD : D.Finite,
      δ A ≤ δ ⟨A.1 ∪ D, A.2.union hD⟩ := by
    intro D hD
    induction D, hD using Set.Finite.induction_on with
    | empty =>
        simp
    | insert ha hs ih =>
        rename_i a s
        have htri := h_triangle ⟨∅, Set.finite_empty⟩ ⟨{a}, Set.finite_singleton a⟩
          ⟨A.1 ∪ s, A.2.union hs⟩ (Set.singleton_nonempty a)
        have hstep :
            δ ⟨A.1 ∪ s, A.2.union hs⟩ ≤
              δ ⟨A.1 ∪ insert a s, A.2.union (hs.insert a)⟩ := by
          have hzero := finite_diversity_singleton_zero δ h_zero a
          simpa [hzero, Set.empty_union, Set.singleton_union, Set.union_assoc,
            Set.union_comm, Set.union_left_comm] using htri
        exact le_trans ih hstep
  have hdiff : (B.1 \ A.1).Finite := B.2.diff
  have h := hkey (B.1 \ A.1) hdiff
  simpa [Set.union_diff_cancel hAB] using h

lemma finite_diversity_union_le
    {X : Type*} (δ : {A : Set X // A.Finite} → ℝ)
    (h_triangle : ∀ A B C : {A : Set X // A.Finite}, B.1.Nonempty →
      δ ⟨A.1 ∪ C.1, A.2.union C.2⟩ ≤
        δ ⟨A.1 ∪ B.1, A.2.union B.2⟩ + δ ⟨B.1 ∪ C.1, B.2.union C.2⟩)
    (A B : {A : Set X // A.Finite}) (hAB : (A.1 ∩ B.1).Nonempty) :
    δ ⟨A.1 ∪ B.1, A.2.union B.2⟩ ≤ δ A + δ B := by
  let I : {A : Set X // A.Finite} :=
    ⟨A.1 ∩ B.1, A.2.subset Set.inter_subset_left⟩
  have htri := h_triangle A I B hAB
  simpa [I, Set.union_eq_left.mpr Set.inter_subset_left,
    Set.union_eq_right.mpr Set.inter_subset_right] using htri

theorem finite_diversity_induces_metric
    {X : Type*} (δ : {A : Set X // A.Finite} → ℝ)
    (h_nonneg : ∀ A : {A : Set X // A.Finite}, 0 ≤ δ A)
    (h_zero : ∀ A : {A : Set X // A.Finite}, δ A = 0 ↔ A.1.Subsingleton)
    (h_triangle : ∀ A B C : {A : Set X // A.Finite}, B.1.Nonempty →
      δ ⟨A.1 ∪ C.1, A.2.union C.2⟩ ≤
        δ ⟨A.1 ∪ B.1, A.2.union B.2⟩ + δ ⟨B.1 ∪ C.1, B.2.union C.2⟩) :
    (∃ m : MetricSpace X, ∀ x y : X,
      m.dist x y = δ ⟨{x, y}, (Set.finite_singleton y).insert x⟩) ∧
      (∀ A B : {A : Set X // A.Finite}, A.1 ⊆ B.1 → δ A ≤ δ B) ∧
      (∀ A B : {A : Set X // A.Finite}, (A.1 ∩ B.1).Nonempty →
        δ ⟨A.1 ∪ B.1, A.2.union B.2⟩ ≤ δ A + δ B) := by
  let d : X → X → ℝ := fun x y =>
    δ ⟨{x, y}, (Set.finite_singleton y).insert x⟩
  letI : Dist X := ⟨d⟩
  let pm : PseudoMetricSpace X := {
    dist_self := by
      intro x
      exact finite_diversity_pair_self δ h_zero x
    dist_comm := by
      intro x y
      exact finite_diversity_pair_comm δ x y
    dist_triangle := by
      intro x y z
      exact finite_diversity_pair_triangle δ h_triangle x y z
  }
  letI : PseudoMetricSpace X := pm
  refine ⟨⟨MetricSpace.mk ?_, ?_⟩, ?_, ?_⟩
  · intro x y hxy
    change δ ⟨{x, y}, (Set.finite_singleton y).insert x⟩ = 0 at hxy
    exact finite_diversity_pair_eq δ h_zero hxy
  · intro x y
    rfl
  · intro A B hAB
    exact finite_diversity_mono δ h_zero h_triangle A B hAB
  · intro A B hAB
    exact finite_diversity_union_le δ h_triangle A B hAB

end Rollout_p1971_finite_diversity_induces_metric

namespace Rollout_p1808_uniform_excision_implies_coarse_excision

/- accepted add_to_file helper 1 -/
def ueRelPow {X : Type*} (W : SetRel X X) : ℕ → SetRel X X
  | 0 => SetRel.id
  | n + 1 => (ueRelPow W n).comp W

lemma ueRel_comp_mono {X : Type*} {R₁ R₂ S₁ S₂ : SetRel X X}
    (hR : R₁ ⊆ R₂) (hS : S₁ ⊆ S₂) : R₁.comp S₁ ⊆ R₂.comp S₂ := by
  intro p hp
  rcases hp with ⟨x, hpR, hpS⟩
  exact ⟨x, hR hpR, hS hpS⟩

lemma ueRel_inv_subset {X : Type*} {R S : SetRel X X} (h : R ⊆ S) : R.inv ⊆ S.inv := by
  intro p hp
  exact h hp

lemma ueRel_image_subset {X : Type*} {R S : SetRel X X} (h : R ⊆ S) (A : Set X) :
    R.image A ⊆ S.image A := by
  intro x hx
  rcases hx with ⟨a, haA, hax⟩
  exact ⟨a, haA, h hax⟩

lemma ueRelPow_id_subset {X : Type*} {W : SetRel X X} (hW : SetRel.id ⊆ W) :
    ∀ n : ℕ, SetRel.id ⊆ ueRelPow W n
  | 0 => by intro p hp; exact hp
  | n + 1 => by
      intro p hp
      have hp1 : p ∈ ueRelPow W n := ueRelPow_id_subset hW n hp
      rcases p with ⟨x, y⟩
      exact ⟨y, hp1, hW (by rfl : (y, y) ∈ SetRel.id)⟩

lemma ueRelPow_subset_succ {X : Type*} {W : SetRel X X} (hW : SetRel.id ⊆ W) (n : ℕ) :
    ueRelPow W n ⊆ ueRelPow W (n + 1) := by
  intro p hp
  rcases p with ⟨x, y⟩
  exact ⟨y, hp, hW (by rfl : (y, y) ∈ SetRel.id)⟩

lemma ueRelPow_mono {X : Type*} {W : SetRel X X} (hW : SetRel.id ⊆ W) :
    ∀ {m n : ℕ}, m ≤ n → ueRelPow W m ⊆ ueRelPow W n := by
  intro m n hmn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hadd : ∀ k : ℕ, ueRelPow W m ⊆ ueRelPow W (m + k) := by
    intro k
    induction k with
    | zero => intro p hp; exact hp
    | succ k ih =>
        intro p hp
        exact ueRelPow_subset_succ hW (m + k) (ih hp)
  exact hadd k

lemma ueRelPow_comp_subset {X : Type*} (W : SetRel X X) :
    ∀ m n : ℕ, (ueRelPow W m).comp (ueRelPow W n) ⊆ ueRelPow W (m + n) := by
  intro m n
  induction n with
  | zero =>
      intro p hp
      simpa [ueRelPow] using hp
  | succ n ih =>
      intro p hp
      have hp' : p ∈ ((ueRelPow W m).comp (ueRelPow W n)).comp W := by
        simpa [ueRelPow, SetRel.comp_assoc] using hp
      rcases hp' with ⟨y, hy₁, hy₂⟩
      exact ⟨y, ih hy₁, hy₂⟩

lemma ueRelPow_left_subset {X : Type*} (W : SetRel X X) :
    ∀ n : ℕ, W.comp (ueRelPow W n) ⊆ ueRelPow W (n + 1) := by
  intro n
  induction n with
  | zero =>
      intro p hp
      rcases hp with ⟨y, hyW, hyid⟩
      rcases p with ⟨x, z⟩
      change y = z at hyid
      subst z
      exact ⟨x, by rfl, hyW⟩
  | succ n ih =>
      intro p hp
      have hp' : p ∈ (W.comp (ueRelPow W n)).comp W := by
        simpa [ueRelPow, SetRel.comp_assoc] using hp
      rcases hp' with ⟨y, hy₁, hy₂⟩
      exact ⟨y, ih hy₁, hy₂⟩

lemma ueRelPow_inv_subset {X : Type*} {W : SetRel X X} (hW : W.inv ⊆ W) :
    ∀ n : ℕ, (ueRelPow W n).inv ⊆ ueRelPow W n := by
  intro n
  induction n with
  | zero =>
      intro p hp
      rcases p with ⟨x, y⟩
      change (y, x) ∈ SetRel.id at hp
      change y = x at hp
      subst x
      exact by rfl
  | succ n ih =>
      intro p hp
      have hp' : p ∈ W.inv.comp (ueRelPow W n).inv := by
        simpa [ueRelPow, SetRel.inv_comp] using hp
      have hp'' : p ∈ W.comp (ueRelPow W n) :=
        (ueRel_comp_mono hW ih) hp'
      exact ueRelPow_left_subset W n hp''

lemma ue_boundary {X : Type*} {A B : Set X} {W K : SetRel X X}
    (hAB : A ∪ B = Set.univ) (hrefl : SetRel.id ⊆ W)
    (hex : W.image A ∩ W.image B ⊆ K.image (A ∩ B)) :
    ∀ (n : ℕ) {a b : X}, a ∈ A → b ∈ B → (a, b) ∈ ueRelPow W n →
      b ∈ (K.comp (ueRelPow W n)).image (A ∩ B) := by
  intro n
  induction n with
  | zero =>
      intro a b ha hb hab
      change a = b at hab
      subst b
      have haW : a ∈ W.image A := ⟨a, ha, hrefl (by rfl : (a, a) ∈ SetRel.id)⟩
      have hbW : a ∈ W.image B := ⟨a, hb, hrefl (by rfl : (a, a) ∈ SetRel.id)⟩
      have hK : a ∈ K.image (A ∩ B) := hex ⟨haW, hbW⟩
      simpa [ueRelPow, SetRel.comp_id] using hK
  | succ n ih =>
      intro a b ha hb hab
      rcases hab with ⟨y, hay, hyb⟩
      have hyAB : y ∈ A ∪ B := by
        have : y ∈ (Set.univ : Set X) := Set.mem_univ y
        simpa [hAB] using this
      rcases hyAB with hyA | hyB
      · have hbWA : b ∈ W.image A := ⟨y, hyA, hyb⟩
        have hbWB : b ∈ W.image B := ⟨b, hb, hrefl (by rfl : (b, b) ∈ SetRel.id)⟩
        have hbK : b ∈ K.image (A ∩ B) := hex ⟨hbWA, hbWB⟩
        rcases hbK with ⟨c, hcAB, hcb⟩
        refine ⟨c, hcAB, ?_⟩
        exact ⟨b, hcb, ueRelPow_id_subset hrefl (n + 1) (by rfl : (b, b) ∈ SetRel.id)⟩
      · have hy : y ∈ (K.comp (ueRelPow W n)).image (A ∩ B) :=
          ih ha hyB hay
        rcases hy with ⟨c, hcAB, hcy⟩
        refine ⟨c, hcAB, ?_⟩
        have hcb : (c, b) ∈ (K.comp (ueRelPow W n)).comp W := ⟨y, hcy, hyb⟩
        simpa [ueRelPow, SetRel.comp_assoc] using hcb

def coarseGenerated {X : Type*} (R : SetRel X X) : Set (SetRel X X) :=
  {E | ∀ 𝒞 : Set (SetRel X X),
    R ∈ 𝒞 →
    SetRel.id ∈ 𝒞 →
    (∀ ⦃S T : SetRel X X⦄, S ∈ 𝒞 → T ⊆ S → T ∈ 𝒞) →
    (∀ ⦃S T : SetRel X X⦄, S ∈ 𝒞 → T ∈ 𝒞 → S ∪ T ∈ 𝒞) →
    (∀ ⦃S : SetRel X X⦄, S ∈ 𝒞 → S.inv ∈ 𝒞) →
    (∀ ⦃S T : SetRel X X⦄, S ∈ 𝒞 → T ∈ 𝒞 → S.comp T ∈ 𝒞) →
    E ∈ 𝒞}

def uniformCoarse (X : Type*) [UniformSpace X] : Set (SetRel X X) :=
  {E | ∀ R ∈ uniformity X, E ∈ coarseGenerated R}

lemma uniformCoarse_id {X : Type*} [UniformSpace X] :
    SetRel.id ∈ uniformCoarse X := by
  intro R hR 𝒞 hgen hid hsub hunion hinv hcomp
  exact hid

lemma uniformCoarse_subset {X : Type*} [UniformSpace X] {S T : SetRel X X}
    (hS : S ∈ uniformCoarse X) (hTS : T ⊆ S) : T ∈ uniformCoarse X := by
  intro R hR 𝒞 hgen hid hsub hunion hinv hcomp
  exact hsub (hS R hR 𝒞 hgen hid hsub hunion hinv hcomp) hTS

lemma uniformCoarse_comp {X : Type*} [UniformSpace X] {S T : SetRel X X}
    (hS : S ∈ uniformCoarse X) (hT : T ∈ uniformCoarse X) :
    S.comp T ∈ uniformCoarse X := by
  intro R hR 𝒞 hgen hid hsub hunion hinv hcomp
  exact hcomp (hS R hR 𝒞 hgen hid hsub hunion hinv hcomp)
    (hT R hR 𝒞 hgen hid hsub hunion hinv hcomp)

lemma coarseGenerated_relPow_bound {X : Type*} {V W : SetRel X X}
    (hrefl : SetRel.id ⊆ W) (hsymm : W.inv ⊆ W)
    (hV : V ∈ coarseGenerated W) :
    ∃ n : ℕ, V ⊆ ueRelPow W n := by
  refine hV {E : SetRel X X | ∃ n : ℕ, E ⊆ ueRelPow W n} ?_ ?_ ?_ ?_ ?_ ?_
  · exact ⟨1, by simpa [ueRelPow, SetRel.id_comp]⟩
  · exact ⟨0, by intro p hp; exact hp⟩
  · intro S T hS hTS
    rcases hS with ⟨n, hSn⟩
    exact ⟨n, hTS.trans hSn⟩
  · intro S T hS hT
    rcases hS with ⟨m, hSm⟩
    rcases hT with ⟨n, hTn⟩
    refine ⟨max m n, ?_⟩
    intro p hp
    rcases hp with hp | hp
    · exact ueRelPow_mono hrefl (Nat.le_max_left m n) (hSm hp)
    · exact ueRelPow_mono hrefl (Nat.le_max_right m n) (hTn hp)
  · intro S hS
    rcases hS with ⟨n, hSn⟩
    refine ⟨n, ?_⟩
    intro p hp
    exact ueRelPow_inv_subset hsymm n (ueRel_inv_subset hSn hp)
  · intro S T hS hT
    rcases hS with ⟨m, hSm⟩
    rcases hT with ⟨n, hTn⟩
    refine ⟨m + n, ?_⟩
    exact (ueRel_comp_mono hSm hTn).trans (ueRelPow_comp_subset W m n)

lemma ueSymmetrize_inv_subset {X : Type*} (R : SetRel X X) :
    R.symmetrize.inv ⊆ R.symmetrize := by
  intro p hp
  exact ⟨hp.2, hp.1⟩

/- verified submission -/
theorem uniform_excision_implies_coarse_excision
    {X : Type*} [UniformSpace X] (A B : Set X) :
    let generated : SetRel X X → Set (SetRel X X) := fun R =>
      {E | ∀ 𝒞 : Set (SetRel X X),
        R ∈ 𝒞 →
        SetRel.id ∈ 𝒞 →
        (∀ ⦃S T : SetRel X X⦄, S ∈ 𝒞 → T ⊆ S → T ∈ 𝒞) →
        (∀ ⦃S T : SetRel X X⦄, S ∈ 𝒞 → T ∈ 𝒞 → S ∪ T ∈ 𝒞) →
        (∀ ⦃S : SetRel X X⦄, S ∈ 𝒞 → S.inv ∈ 𝒞) →
        (∀ ⦃S T : SetRel X X⦄, S ∈ 𝒞 → T ∈ 𝒞 → S.comp T ∈ 𝒞) →
        E ∈ 𝒞}
    let coarse : Set (SetRel X X) :=
      {E | ∀ R ∈ uniformity X, E ∈ generated R}
    A ∪ B = Set.univ →
    (∃ E ∈ uniformity X, E ∈ coarse) →
    (∃ U ∈ uniformity X,
      ∃ κ : OrderDual {W : SetRel X X // W ⊆ U} → OrderDual (SetRel X X),
        Monotone κ ∧
        (∀ V ∈ uniformity X,
          ∃ W : {W : SetRel X X // W ⊆ U},
            W.1 ∈ uniformity X ∧
              OrderDual.ofDual (κ (OrderDual.toDual W)) ⊆ V) ∧
        (∀ W : {W : SetRel X X // W ⊆ U},
          W.1.image A ∩ W.1.image B ⊆
            (OrderDual.ofDual (κ (OrderDual.toDual W))).image (A ∩ B))) →
    ∀ V ∈ coarse, ∃ T ∈ coarse,
      V.image A ∩ V.image B ⊆ T.image (A ∩ B) := by
  intro generated coarse hAB hcompat hex V hV
  change V ∈ uniformCoarse X at hV
  change ∃ T ∈ uniformCoarse X, V.image A ∩ V.image B ⊆ T.image (A ∩ B)
  rcases hcompat with ⟨E, hEuniform, hEcoarse⟩
  change E ∈ uniformCoarse X at hEcoarse
  rcases hex with ⟨U, hUuniform, κ, hκmono, hκapprox, hκexc⟩
  rcases hκapprox E hEuniform with ⟨WE, hWEuniform, hκWE⟩
  let D : SetRel X X := WE.1 ∩ U ∩ E
  have hDuniform : D ∈ uniformity X := by
    exact Filter.inter_mem (Filter.inter_mem hWEuniform hUuniform) hEuniform
  let W : SetRel X X := D.symmetrize
  have hWuniform : W ∈ uniformity X := by
    exact symmetrize_mem_uniformity hDuniform
  have hW_subset_U : W ⊆ U := by
    intro p hp
    exact hp.1.1.2
  have hW_subset_E : W ⊆ E := by
    intro p hp
    exact hp.1.2
  have hW_subset_WE : W ⊆ WE.1 := by
    intro p hp
    exact hp.1.1.1
  let WU : {S : SetRel X X // S ⊆ U} := ⟨W, hW_subset_U⟩
  have hWrefl : SetRel.id ⊆ W := refl_le_uniformity hWuniform
  have hWsymm : W.inv ⊆ W := by
    exact ueSymmetrize_inv_subset D
  have hWcoarse : W ∈ uniformCoarse X :=
    uniformCoarse_subset hEcoarse hW_subset_E
  let K : SetRel X X := OrderDual.ofDual (κ (OrderDual.toDual WU))
  have hK_subset_E : K ⊆ E := by
    have hle : OrderDual.toDual WE ≤ OrderDual.toDual WU := by
      exact hW_subset_WE
    have hKWE : K ⊆ OrderDual.ofDual (κ (OrderDual.toDual WE)) := by
      exact hκmono hle
    exact hKWE.trans hκWE
  have hKcoarse : K ∈ uniformCoarse X :=
    uniformCoarse_subset hEcoarse hK_subset_E
  have hWexc : W.image A ∩ W.image B ⊆ K.image (A ∩ B) := by
    exact hκexc WU
  have hV_generated_W : V ∈ coarseGenerated W := hV W hWuniform
  rcases coarseGenerated_relPow_bound hWrefl hWsymm hV_generated_W with ⟨n, hVn⟩
  have hPowCoarse : ∀ m : ℕ, ueRelPow W m ∈ uniformCoarse X := by
    intro m
    induction m with
    | zero => exact uniformCoarse_id
    | succ m ih => exact uniformCoarse_comp ih hWcoarse
  refine ⟨K.comp (ueRelPow W (n + n + n)), ?_, ?_⟩
  · exact uniformCoarse_comp hKcoarse (hPowCoarse (n + n + n))
  · intro x hx
    have hxA : x ∈ (ueRelPow W n).image A := ueRel_image_subset hVn A hx.1
    have hxB : x ∈ (ueRelPow W n).image B := ueRel_image_subset hVn B hx.2
    rcases hxA with ⟨a, haA, hax⟩
    rcases hxB with ⟨b, hbB, hbx⟩
    have hxb : (x, b) ∈ ueRelPow W n :=
      ueRelPow_inv_subset hWsymm n hbx
    have hab₂ : (a, b) ∈ (ueRelPow W n).comp (ueRelPow W n) := ⟨x, hax, hxb⟩
    have habN : (a, b) ∈ ueRelPow W (n + n) :=
      ueRelPow_comp_subset W n n hab₂
    have hb_boundary : b ∈ (K.comp (ueRelPow W (n + n))).image (A ∩ B) :=
      ue_boundary hAB hWrefl hWexc (n + n) haA hbB habN
    rcases hb_boundary with ⟨c, hcAB, hcb⟩
    refine ⟨c, hcAB, ?_⟩
    have hcx₁ : (c, x) ∈ (K.comp (ueRelPow W (n + n))).comp (ueRelPow W n) :=
      ⟨b, hcb, hbx⟩
    have hcx₂ : (c, x) ∈ K.comp ((ueRelPow W (n + n)).comp (ueRelPow W n)) := by
      simpa [SetRel.comp_assoc] using hcx₁
    have htail : (ueRelPow W (n + n)).comp (ueRelPow W n) ⊆
        ueRelPow W (n + n + n) := by
      exact ueRelPow_comp_subset W (n + n) n
    exact (ueRel_comp_mono (by intro p hp; exact hp) htail) hcx₂

end Rollout_p1808_uniform_excision_implies_coarse_excision

namespace Rollout_p3094_finite_multiplicative_ratio_sums

/- verified submission -/
theorem finite_multiplicative_ratio_sums
    {I : Type*} [Fintype I] [Nonempty I]
    (r : I × I → ℝ)
    (hr_pos : ∀ e d : I, 0 < r (e, d))
    (hr_mul : ∀ e d b : I, r (e, d) = r (e, b) * r (b, d)) :
    ∀ b : I,
      (∑ e : I, (∑ d : I, r (d, e))⁻¹) =
          (∑ e : I, r (b, e)) / (∑ d : I, (r (d, b))⁻¹) ∧
      (∑ e : I, r (b, e)) / (∑ d : I, (r (d, b))⁻¹) =
          (∑ e : I, r (e, b)) / (∑ d : I, r (d, b)) ∧
      (∑ e : I, r (e, b)) / (∑ d : I, r (d, b)) = 1 := by
  intro b
  have hdiag : ∀ e : I, r (e, e) = 1 := by
    intro e
    have hz : r (e, e) ≠ 0 := ne_of_gt (hr_pos e e)
    have h : r (e, e) * r (e, e) = r (e, e) * 1 := by
      rw [mul_one]
      exact (hr_mul e e e).symm
    exact mul_left_cancel₀ hz h
  have hinv : ∀ e d : I, (r (e, d))⁻¹ = r (d, e) := by
    intro e d
    have hone : r (e, d) * r (d, e) = 1 := by
      rw [← hdiag e]
      exact (hr_mul e e d).symm
    exact inv_eq_of_mul_eq_one_right hone
  have hsum_pos : ∀ e : I, 0 < ∑ d : I, r (d, e) := by
    intro e
    exact Finset.sum_pos (fun d _ => hr_pos d e) Finset.univ_nonempty
  have hsum_ne : ∀ e : I, (∑ d : I, r (d, e)) ≠ 0 := by
    intro e
    exact ne_of_gt (hsum_pos e)
  have hA : (∑ e : I, (∑ d : I, r (d, e))⁻¹) = 1 := by
    have hterm : ∀ e : I,
        (∑ d : I, r (d, e))⁻¹ =
          r (e, b) / (∑ d : I, r (d, b)) := by
      intro e
      calc
        (∑ d : I, r (d, e))⁻¹
            = ((∑ d : I, r (d, b)) / r (e, b))⁻¹ := by
              congr 1
              rw [div_eq_mul_inv, Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro d _
              calc
                r (d, e) = r (d, b) * r (b, e) := hr_mul d e b
                _ = r (d, b) * (r (e, b))⁻¹ := by rw [hinv e b]
        _ = r (e, b) / (∑ d : I, r (d, b)) := inv_div _ _
    calc
      (∑ e : I, (∑ d : I, r (d, e))⁻¹)
          = ∑ e : I, r (e, b) / (∑ d : I, r (d, b)) := by
            apply Finset.sum_congr rfl
            intro e _
            exact hterm e
      _ = (∑ e : I, r (e, b)) / (∑ d : I, r (d, b)) := by
            rw [← Finset.sum_div]
      _ = (∑ d : I, r (d, b)) / (∑ d : I, r (d, b)) := rfl
      _ = 1 := div_self (hsum_ne b)
  have hB : (∑ e : I, r (b, e)) / (∑ d : I, (r (d, b))⁻¹) = 1 := by
    have hden : (∑ d : I, (r (d, b))⁻¹) = ∑ e : I, r (b, e) := by
      apply Finset.sum_congr rfl
      intro d _
      exact hinv d b
    have hnum_pos : 0 < ∑ e : I, r (b, e) :=
      Finset.sum_pos (fun e _ => hr_pos b e) Finset.univ_nonempty
    rw [hden]
    exact div_self (ne_of_gt hnum_pos)
  have hC : (∑ e : I, r (e, b)) / (∑ d : I, r (d, b)) = 1 := by
    have hnum : (∑ e : I, r (e, b)) = ∑ d : I, r (d, b) := rfl
    rw [hnum]
    exact div_self (hsum_ne b)
  exact ⟨hA.trans hB.symm, hB.trans hC.symm, hC⟩

end Rollout_p3094_finite_multiplicative_ratio_sums

namespace Rollout_p3013_finite_compatible_shrinking_lemma

/- accepted add_to_file helper 1 -/
lemma compatible_shrinking_closureInterOfRelClosed
    {X : Type*} [TopologicalSpace X] {O B : Set X}
    (hBsub : B ⊆ O)
    (hB : IsClosed (Subtype.val ⁻¹' B : Set O)) :
    closure B ∩ O = B := by
  apply Set.Subset.antisymm
  · intro x hx
    have h := isClosed_preimage_val.mp hB
    have hx' : x ∈ O ∩ closure (O ∩ B) := by
      refine ⟨hx.2, ?_⟩
      have hcl : closure (O ∩ B) = closure B := by
        rw [Set.inter_eq_right.mpr hBsub]
      simpa [hcl] using hx.1
    exact h hx'
  · intro x hx
    exact ⟨subset_closure hx, hBsub hx⟩

/- accepted add_to_file helper 2 -/
lemma compatible_shrinking_relClosedDiff
    {X : Type*} [TopologicalSpace X] {O Z A : Set X}
    (hZO : Z ⊆ O)
    (hZ : IsClosed (Subtype.val ⁻¹' Z : Set O))
    (hA : IsOpen (Subtype.val ⁻¹' A : Set Z)) :
    IsClosed (Subtype.val ⁻¹' (Z \ A) : Set O) := by
  let B : Set X := Z \ A
  have hBsub : B ⊆ O := fun x hx => hZO hx.1
  have hBsubZ : B ⊆ Z := fun x hx => hx.1
  rw [isClosed_preimage_val]
  intro x hx
  have hxO : x ∈ O := hx.1
  have hxclB : x ∈ closure B := by
    change x ∈ closure (Z \ A)
    have hcl : closure (O ∩ (Z \ A)) = closure (Z \ A) := by
      rw [Set.inter_eq_right.mpr (fun y hy => hZO hy.1)]
    simpa [hcl] using hx.2
  have hxZ : x ∈ Z := by
    have hZchar := isClosed_preimage_val.mp hZ
    have hx' : x ∈ O ∩ closure (O ∩ Z) := by
      refine ⟨hxO, ?_⟩
      have hclZ : closure (O ∩ Z) = closure Z := by
        rw [Set.inter_eq_right.mpr hZO]
      have hBcl : closure B ⊆ closure Z := closure_mono hBsubZ
      simpa [hclZ] using hBcl hxclB
    exact hZchar hx'
  have hxnotA : x ∉ A := by
    intro hxA
    rcases isOpen_induced_iff.mp hA with ⟨V, hVopen, hVA⟩
    have hxV : x ∈ V := by
      have hzV : (⟨x, hxZ⟩ : Z) ∈ Subtype.val ⁻¹' V := by
        rw [hVA]
        exact hxA
      exact hzV
    have hdis : V ∩ B = ∅ := by
      ext y
      constructor
      · intro hy
        have hyZ : y ∈ Z := hy.2.1
        have hyA : y ∈ A := by
          have hzV : (⟨y, hyZ⟩ : Z) ∈ Subtype.val ⁻¹' V := hy.1
          rwa [hVA] at hzV
        exact (hy.2.2 hyA).elim
      · intro hy
        cases hy
    have hmem := (mem_closure_iff.mp hxclB) V hVopen hxV
    exact hmem.ne_empty hdis
  exact ⟨hxZ, hxnotA⟩

/- accepted add_to_file helper 3 -/
noncomputable def testIf (A : Set ℕ) : ℕ := @ite ℕ A.Nonempty (Classical.dec _) 1 0

/- accepted add_to_file helper 4 -/
noncomputable def compatibleDistAux
    {X : Type*} [MetricSpace X] (A : Set X) (x : X) : ℝ :=
  @ite ℝ A.Nonempty (Classical.dec _) (min 1 (Metric.infDist x A)) 1

lemma compatibleDistAux_zero_iff
    {X : Type*} [MetricSpace X] (A : Set X) (x : X) :
    compatibleDistAux A x = 0 ↔ x ∈ closure A := by
  unfold compatibleDistAux
  by_cases hA : A.Nonempty
  · rw [if_pos hA]
    constructor
    · intro h0
      have hd0 : Metric.infDist x A = 0 := by
        by_cases hdle : Metric.infDist x A ≤ 1
        · have hmin := min_eq_right hdle
          rw [hmin] at h0
          exact h0
        · have hmin : min 1 (Metric.infDist x A) = 1 :=
            min_eq_left (le_of_lt (not_le.mp hdle))
          rw [hmin] at h0
          norm_num at h0
      exact (Metric.mem_closure_iff_infDist_zero hA).mpr hd0
    · intro hx
      rw [Metric.infDist_zero_of_mem_closure hx]
      norm_num
  · rw [if_neg hA]
    have hempty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    simp [hempty]

lemma continuous_compatibleDistAux
    {X : Type*} [MetricSpace X] (A : Set X) :
    Continuous fun x => compatibleDistAux A x := by
  unfold compatibleDistAux
  by_cases hA : A.Nonempty
  · have hfun : (fun x => @ite ℝ A.Nonempty (Classical.dec _)
        (min 1 (Metric.infDist x A)) 1) =
        fun x => min 1 (Metric.infDist x A) := by
      funext x
      exact if_pos hA
    rw [hfun]
    exact continuous_const.min (Metric.continuous_infDist_pt A)
  · have hfun : (fun x => @ite ℝ A.Nonempty (Classical.dec _)
        (min 1 (Metric.infDist x A)) 1) = fun _ => 1 := by
      funext x
      exact if_neg hA
    rw [hfun]
    exact continuous_const

/- accepted add_to_file helper 5 -/
lemma compatibleDistAux_nonneg
    {X : Type*} [MetricSpace X] (A : Set X) (x : X) :
    0 ≤ compatibleDistAux A x := by
  unfold compatibleDistAux
  by_cases hA : A.Nonempty
  · rw [if_pos hA]
    exact le_min zero_le_one Metric.infDist_nonneg
  · rw [if_neg hA]
    norm_num

/- accepted add_to_file helper 6 -/
lemma compatible_shrinking_exists_singletons
    {X : Type*} [MetricSpace X]
    {O Z : Set X} (N : ℕ)
    (Zi : Fin N → Set X) (W : Set (Fin N) → Set X)
    (hO : IsOpen O)
    (hZO : Z ⊆ O)
    (hZclosed : IsClosed (Subtype.val ⁻¹' Z : Set O))
    (hZi_subset : ∀ i, Zi i ⊆ Z)
    (hZi_open : ∀ i, IsOpen (Subtype.val ⁻¹' Zi i : Set Z))
    (hW : ∀ K : Set (Fin N), K.Nonempty →
      IsOpen (W K) ∧ W K ⊆ O ∧ W K ∩ Z = ⋂ i ∈ K, Zi i) :
    ∃ V : Fin N → Set X,
      (∀ i, IsOpen (V i) ∧ V i ∩ Z = Zi i) ∧
      ∀ K : Set (Fin N), K.Nonempty → (⋂ i ∈ K, V i) ⊆ W K := by
  classical
  let B : Fin N → Set X := fun i => Z \ Zi i
  let A : Fin N → Set X := fun i => closure (B i)
  let D : Set (Fin N) → Set X := fun K => closure (O \ W K) ∩ (W K)ᶜ
  let d : Fin N → X → ℝ := fun i x => compatibleDistAux (B i) x
  let P : Set (Fin N) → Fin N → Set X := fun K i =>
    {x | x ∈ D K ∧ ∀ j ∈ K, d i x ≤ d j x}
  let S : Fin N → Set (Set (Fin N)) := fun i => {K | K.Nonempty ∧ i ∈ K}
  let E : Fin N → Set X := fun i => A i ∪ ⋃ K ∈ S i, P K i
  have hBsub : ∀ i, B i ⊆ O := by
    intro i x hx
    exact hZO hx.1
  have hBrel : ∀ i, IsClosed (Subtype.val ⁻¹' B i : Set O) := by
    intro i
    exact compatible_shrinking_relClosedDiff hZO hZclosed (hZi_open i)
  have hAtrace : ∀ i, A i ∩ Z = B i := by
    intro i
    have h := compatible_shrinking_closureInterOfRelClosed (hBsub i) (hBrel i)
    apply Set.Subset.antisymm
    · intro x hx
      have hxO : x ∈ O := hZO hx.2
      have hx' : x ∈ A i ∩ O := ⟨hx.1, hxO⟩
      rwa [h] at hx'
    · intro x hx
      exact ⟨subset_closure hx, hx.1⟩
  have hPclosed : ∀ K : Set (Fin N), K.Nonempty → ∀ i, IsClosed (P K i) := by
    intro K hK i
    have hDclosed : IsClosed (D K) := by
      exact isClosed_closure.inter ((hW K hK).1.isClosed_compl)
    have hineq : ∀ j ∈ K, IsClosed {x : X | d i x ≤ d j x} := by
      intro j hj
      exact isClosed_le (continuous_compatibleDistAux (B i))
        (continuous_compatibleDistAux (B j))
    have hbi : IsClosed (⋂ j ∈ K, {x : X | d i x ≤ d j x}) :=
      isClosed_biInter hineq
    have hPeq : P K i = D K ∩ ⋂ j ∈ K, {x : X | d i x ≤ d j x} := by
      ext x
      simp [P]
    rw [hPeq]
    exact hDclosed.inter hbi
  have hSfinite : ∀ i, (S i).Finite := by
    intro i
    exact Set.finite_univ.subset (Set.subset_univ _)
  have hEclosed : ∀ i, IsClosed (E i) := by
    intro i
    apply isClosed_closure.union
    exact (hSfinite i).isClosed_biUnion (by
      intro K hK
      exact hPclosed K hK.1 i)
  have hPtrace : ∀ K : Set (Fin N), K.Nonempty → ∀ i, P K i ∩ Z ⊆ A i := by
    intro K hK i x hx
    have hxP : x ∈ P K i := hx.1
    have hxZ : x ∈ Z := hx.2
    have hxnotW : x ∉ W K := hxP.1.2
    have hnotinter : x ∉ ⋂ j ∈ K, Zi j := by
      intro hxinter
      have hxmem : x ∈ W K ∩ Z := by
        rw [(hW K hK).2.2]
        exact hxinter
      exact hxnotW hxmem.1
    have hnotforall : ¬ ∀ j, j ∈ K → x ∈ Zi j := by
      intro hall
      apply hnotinter
      simpa using hall
    rcases not_forall₂.mp hnotforall with ⟨j, hjK, hxnotj⟩
    have hxBj : x ∈ B j := ⟨hxZ, hxnotj⟩
    have hdj0 : d j x = 0 := by
      exact (compatibleDistAux_zero_iff (B j) x).mpr (subset_closure hxBj)
    have hle : d i x ≤ 0 := by
      simpa [hdj0] using hxP.2 j hjK
    have hdi0 : d i x = 0 := le_antisymm hle (compatibleDistAux_nonneg (B i) x)
    exact (compatibleDistAux_zero_iff (B i) x).mp hdi0
  have hEtrace : ∀ i, E i ∩ Z = B i := by
    intro i
    apply Set.Subset.antisymm
    · intro x hx
      have hxZ : x ∈ Z := hx.2
      have hxE : x ∈ E i := hx.1
      rcases hxE with hxA | hxU
      · have : x ∈ A i ∩ Z := ⟨hxA, hxZ⟩
        rwa [hAtrace i] at this
      · rcases Set.mem_iUnion.mp hxU with ⟨K, hKmem⟩
        rcases Set.mem_iUnion.mp hKmem with ⟨hKS, hxP⟩
        have : x ∈ P K i ∩ Z := ⟨hxP, hxZ⟩
        have hxA := hPtrace K hKS.1 i this
        have : x ∈ A i ∩ Z := ⟨hxA, hxZ⟩
        rwa [hAtrace i] at this
    · intro x hx
      exact ⟨Or.inl (subset_closure hx), hx.1⟩
  have hPcover : ∀ K : Set (Fin N), K.Nonempty → D K ⊆ ⋃ i ∈ K, P K i := by
    intro K hK x hxD
    let s : Finset (Fin N) := K.toFinset
    have hs : s.Nonempty := by
      simpa [s, Set.toFinset_nonempty] using hK
    rcases Finset.exists_min_image s (fun i => d i x) hs with ⟨i, his, hmin⟩
    have hiK : i ∈ K := by simpa [s] using his
    apply Set.mem_iUnion.mpr
    exists i
    apply Set.mem_iUnion.mpr
    exists hiK
    exact ⟨hxD, by
      intro j hjK
      exact hmin j (by simpa [s] using hjK)⟩
  have hEcover : ∀ K : Set (Fin N), K.Nonempty → O \ W K ⊆ ⋃ i ∈ K, E i := by
    intro K hK x hx
    have hxD : x ∈ D K := ⟨subset_closure hx, hx.2⟩
    have hxP := hPcover K hK hxD
    rcases Set.mem_iUnion.mp hxP with ⟨i, himem⟩
    rcases Set.mem_iUnion.mp himem with ⟨hiK, hxi⟩
    apply Set.mem_iUnion.mpr
    exists i
    apply Set.mem_iUnion.mpr
    exists hiK
    exact Or.inr (Set.mem_iUnion.mpr ⟨K,
      Set.mem_iUnion.mpr ⟨⟨hK, hiK⟩, hxi⟩⟩)
  let V : Fin N → Set X := fun i => O ∩ (E i)ᶜ
  refine ⟨V, ?_, ?_⟩
  · intro i
    constructor
    · exact hO.inter (hEclosed i).isOpen_compl
    · apply Set.Subset.antisymm
      · intro x hx
        have hxZ : x ∈ Z := hx.2
        have hxnotE : x ∉ E i := hx.1.2
        have hxnotB : x ∉ B i := by
          intro hxB
          apply hxnotE
          have hxEi : x ∈ E i := Or.inl (subset_closure hxB)
          exact hxEi
        by_contra hnot
        exact hxnotB ⟨hxZ, hnot⟩
      · intro x hx
        have hxZ : x ∈ Z := hZi_subset i hx
        have hxO : x ∈ O := hZO hxZ
        have hxnotE : x ∉ E i := by
          intro hxE
          have hxEZ : x ∈ E i ∩ Z := ⟨hxE, hxZ⟩
          rw [hEtrace i] at hxEZ
          exact hxEZ.2 hx
        exact ⟨⟨hxO, hxnotE⟩, hxZ⟩
  · intro K hK x hx
    rcases hK with ⟨i₀, hi₀⟩
    have hxVi₀ : x ∈ V i₀ := Set.mem_iInter₂.mp hx i₀ hi₀
    have hxO : x ∈ O := hxVi₀.1
    by_contra hxW
    have hxdiff : x ∈ O \ W K := ⟨hxO, hxW⟩
    have hxE := hEcover K ⟨i₀, hi₀⟩ hxdiff
    rcases Set.mem_iUnion.mp hxE with ⟨i, himem⟩
    rcases Set.mem_iUnion.mp himem with ⟨hiK, hxiE⟩
    have hxVi : x ∈ V i := Set.mem_iInter₂.mp hx i hiK
    exact hxVi.2 hxiE

/- verified submission -/
theorem finite_compatible_shrinking_lemma
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    {O Z : Set X} (N : ℕ) (hN : 0 < N)
    (Zi : Fin N → Set X) (W : Set (Fin N) → Set X)
    (hO : IsOpen O) (hOcompact : IsCompact (closure O))
    (hZO : Z ⊆ O)
    (hZclosed : IsClosed (Subtype.val ⁻¹' Z : Set O))
    (hZi_subset : ∀ i, Zi i ⊆ Z)
    (hZi_open : ∀ i, IsOpen (Subtype.val ⁻¹' Zi i : Set Z))
    (hW : ∀ K : Set (Fin N), K.Nonempty →
      IsOpen (W K) ∧ W K ⊆ O ∧ W K ∩ Z = ⋂ i ∈ K, Zi i) :
    ∃ U : Set (Fin N) → Set X,
      (∀ K : Set (Fin N), K.Nonempty →
        IsOpen (U K) ∧ U K ⊆ W K ∧ U K ∩ Z = ⋂ i ∈ K, Zi i) ∧
      ∀ J K : Set (Fin N), J.Nonempty → K.Nonempty →
        U J ∩ U K = U (J ∪ K) := by
  classical
  rcases compatible_shrinking_exists_singletons N Zi W hO hZO hZclosed
      hZi_subset hZi_open hW with ⟨V, hV, hVsub⟩
  let U : Set (Fin N) → Set X := fun K => ⋂ i ∈ K, V i
  refine ⟨U, ?_, ?_⟩
  · intro K hK
    refine ⟨?_, hVsub K hK, ?_⟩
    · exact K.toFinite.isOpen_biInter (fun i hi => (hV i).1)
    · calc
        U K ∩ Z = (⋂ i ∈ K, V i) ∩ Z := rfl
        _ = ⋂ i ∈ K, (V i ∩ Z) := by
          ext x
          constructor
          · intro hx
            have hmem := Set.mem_iInter₂.mp hx.1
            apply Set.mem_iInter₂.mpr
            intro i hi
            exact ⟨hmem i hi, hx.2⟩
          · intro hx
            have hall := Set.mem_iInter₂.mp hx
            rcases hK with ⟨i₀, hi₀⟩
            constructor
            · apply Set.mem_iInter₂.mpr
              intro i hi
              exact (hall i hi).1
            · exact (hall i₀ hi₀).2
        _ = ⋂ i ∈ K, Zi i := by
          simp [fun i => (hV i).2]
  · intro J K hJ hK
    ext x
    simp [U, Set.mem_union, or_imp, forall_and]

end Rollout_p3013_finite_compatible_shrinking_lemma
