import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p2920_proposition_3_8
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 072a6258b8a4599f09053e96ae1c5d3b4f28aeefb6ed9495f914f7e8c63fff72
-- reconstructed_proof_sha256: ebb92f473f54b0b7dd3e27eb1b4bb2884ae689e01a898cfc10167c756afb7838
-- selected_edge_count: 1

/- accepted add_to_file helper 1 -/
structure PW where
  val : Polynomial ℤ

def PW.equiv : PW ≃ Polynomial ℤ where
  toFun := PW.val
  invFun := PW.mk
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; rfl

noncomputable instance : CommRing PW := Equiv.commRing PW.equiv

noncomputable def PW.ringEquiv : PW ≃+* Polynomial ℤ := Equiv.ringEquiv PW.equiv

noncomputable def polyToPW : Polynomial ℤ →+* PW := PW.ringEquiv.symm.toRingHom

lemma polyToPW_injective : Function.Injective polyToPW :=
  RingEquiv.injective PW.ringEquiv.symm

noncomputable def weightK : ℕ → ℕ → PW :=
  fun _ j => if j = 1 then polyToPW (-Polynomial.X) else 0

noncomputable def weightE : ℕ → ℕ → PW :=
  fun _ j => if j = 1 then -1 else 0

noncomputable def weightP : ℕ → ℕ → PW :=
  fun _ _ => polyToPW (1 - Polynomial.X)

/- accepted add_to_file helper 2 -/
instance : TopologicalSpace PW := ⊥
instance : DiscreteTopology PW := ⟨rfl⟩

/- accepted add_to_file helper 3 -/
open PowerSeries.WithPiTopology

lemma partition_factor_E (i : ℕ) :
    (1 : PowerSeries PW) +
        ∑' j : ℕ, weightE (i + 1) (j + 1) •
          (PowerSeries.X : PowerSeries PW) ^ ((i + 1) * (j + 1))
      = 1 - (PowerSeries.X : PowerSeries PW) ^ (i + 1) := by
  rw [tsum_eq_single 0]
  · simp [weightE, pow_succ]
    rw [sub_eq_add_neg]
  · intro j hj
    have h : j + 1 ≠ 1 := by omega
    change ((if j + 1 = 1 then (-1 : PW) else 0) •
      (PowerSeries.X : PowerSeries PW) ^ ((i + 1) * (j + 1))) = 0
    rw [if_neg h, zero_smul]

/- accepted add_to_file helper 4 -/
lemma partition_factor_P (i : ℕ) :
    (1 : PowerSeries PW) +
        ∑' j : ℕ, weightP (i + 1) (j + 1) •
          (PowerSeries.X : PowerSeries PW) ^ ((i + 1) * (j + 1))
      =
    1 + polyToPW (1 - Polynomial.X) •
      ((PowerSeries.X : PowerSeries PW) ^ (i + 1) *
        ∑' j : ℕ, ((PowerSeries.X : PowerSeries PW) ^ (i + 1)) ^ j) := by
  let u : PowerSeries PW := PowerSeries.X ^ (i + 1)
  let c : PW := polyToPW (1 - Polynomial.X)
  have hu : PowerSeries.constantCoeff u = 0 := by
    simp [u]
  have hS : Summable fun j : ℕ => u ^ j :=
    PowerSeries.WithPiTopology.summable_pow_of_constantCoeff_eq_zero hu
  have hshift : ∑' j : ℕ, u * u ^ j = u * ∑' j : ℕ, u ^ j :=
    (hS.hasSum.mul_left u).tsum_eq
  have hscalar : ∑' j : ℕ, (PowerSeries.C c) * (u * u ^ j) =
      (PowerSeries.C c) * (u * ∑' j : ℕ, u ^ j) := by
    have hs : Summable fun j : ℕ => u * u ^ j := hS.mul_left u
    calc
      ∑' j : ℕ, (PowerSeries.C c) * (u * u ^ j)
          = (PowerSeries.C c) * ∑' j : ℕ, u * u ^ j :=
            (hs.hasSum.mul_left (PowerSeries.C c)).tsum_eq
      _ = (PowerSeries.C c) * (u * ∑' j : ℕ, u ^ j) := by rw [hshift]
  have hcongr : (∑' j : ℕ, weightP (i + 1) (j + 1) •
      (PowerSeries.X : PowerSeries PW) ^ ((i + 1) * (j + 1))) =
      ∑' j : ℕ, (PowerSeries.C c) * (u * u ^ j) := by
    apply tsum_congr
    intro j
    have hexp : (i + 1) * (j + 1) = (i + 1) + (i + 1) * j := by
      rw [Nat.mul_succ, Nat.add_comm]
    rw [weightP]
    rw [PowerSeries.smul_eq_C_mul]
    rw [hexp, pow_add, ← pow_mul]
  rw [hcongr, hscalar]
  change 1 + PowerSeries.C c * (u * ∑' j : ℕ, u ^ j) = _
  rw [PowerSeries.smul_eq_C_mul]

/- accepted add_to_file helper 5 -/
lemma partition_factor_K (i : ℕ) :
    (1 : PowerSeries PW) +
        ∑' j : ℕ, weightK (i + 1) (j + 1) •
          (PowerSeries.X : PowerSeries PW) ^ ((i + 1) * (j + 1))
      = 1 - polyToPW Polynomial.X •
          (PowerSeries.X : PowerSeries PW) ^ (i + 1) := by
  rw [tsum_eq_single 0]
  · simp [weightK, pow_succ]
    rw [sub_eq_add_neg]
  · intro j hj
    have h : j + 1 ≠ 1 := by omega
    change ((if j + 1 = 1 then polyToPW (-Polynomial.X) else 0) •
      (PowerSeries.X : PowerSeries PW) ^ ((i + 1) * (j + 1))) = 0
    rw [if_neg h, zero_smul]

/- accepted add_to_file helper 6 -/
lemma partition_factor_mul (i : ℕ) :
    ((1 : PowerSeries PW) +
        ∑' j : ℕ, weightE (i + 1) (j + 1) •
          (PowerSeries.X : PowerSeries PW) ^ ((i + 1) * (j + 1))) *
      ((1 : PowerSeries PW) +
        ∑' j : ℕ, weightP (i + 1) (j + 1) •
          (PowerSeries.X : PowerSeries PW) ^ ((i + 1) * (j + 1)))
    =
    (1 : PowerSeries PW) +
        ∑' j : ℕ, weightK (i + 1) (j + 1) •
          (PowerSeries.X : PowerSeries PW) ^ ((i + 1) * (j + 1)) := by
  rw [partition_factor_E, partition_factor_P, partition_factor_K]
  let u : PowerSeries PW := PowerSeries.X ^ (i + 1)
  let a : PowerSeries PW := PowerSeries.C (polyToPW Polynomial.X)
  let S : PowerSeries PW := ∑' j : ℕ, u ^ j
  have hu : PowerSeries.constantCoeff u = 0 := by simp [u]
  have hgeom : (1 - u) * S = 1 :=
    PowerSeries.WithPiTopology.one_sub_mul_tsum_pow_of_constantCoeff_eq_zero hu
  change (1 - u) * (1 + polyToPW (1 - Polynomial.X) • (u * S)) =
    1 - polyToPW Polynomial.X • u
  rw [PowerSeries.smul_eq_C_mul, PowerSeries.smul_eq_C_mul]
  have hc : PowerSeries.C (polyToPW (1 - Polynomial.X)) = 1 - a := by
    simp [a]
  rw [hc]
  change (1 - u) * (1 + (1 - a) * (u * S)) = 1 - a * u
  calc
    (1 - u) * (1 + (1 - a) * (u * S))
        = (1 - u) + (1 - a) * (u * ((1 - u) * S)) := by ring
    _ = (1 - u) + (1 - a) * u := by rw [hgeom]; ring
    _ = 1 - a * u := by ring

/- accepted add_to_file helper 7 -/
lemma genFun_weightK_eq :
    Nat.Partition.genFun weightK =
      Nat.Partition.genFun weightE * Nat.Partition.genFun weightP := by
  apply HasProd.unique (Nat.Partition.hasProd_genFun (R := PW) weightK)
  convert (Nat.Partition.hasProd_genFun (R := PW) weightE).mul
    (Nat.Partition.hasProd_genFun (R := PW) weightP) using 1
  funext i
  exact (partition_factor_mul i).symm

/- accepted add_to_file helper 8 -/
lemma toFinsupp_prod_weightK {m : ℕ} (ρ : Nat.Partition m) :
    (Multiset.toFinsupp ρ.parts).prod weightK =
      if ρ.parts.Nodup then
        polyToPW ((-Polynomial.X : Polynomial ℤ) ^ ρ.parts.toFinset.card)
      else 0 := by
  by_cases h : ρ.parts.Nodup
  · simp [h]
    rw [Finsupp.prod, Multiset.toFinsupp_support]
    rw [← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro a ha
    have hmem : a ∈ ρ.parts := by
      exact Multiset.mem_toFinset.mp ha
    have hcount : Multiset.count a ρ.parts = 1 :=
      Multiset.count_eq_one_of_mem h hmem
    simp [weightK, Multiset.toFinsupp_apply, hcount]
  · simp [h]
    rw [Finsupp.prod, Multiset.toFinsupp_support]
    rw [Multiset.nodup_iff_count_le_one] at h
    push_neg at h
    rcases h with ⟨a, ha⟩
    have hapos : a ∈ ρ.parts.toFinset := by
      rw [Multiset.mem_toFinset]
      by_contra hnot
      have hcount0 : Multiset.count a ρ.parts = 0 :=
        Multiset.count_eq_zero_of_notMem hnot
      omega
    have hcountne : Multiset.count a ρ.parts ≠ 1 := by omega
    apply Finset.prod_eq_zero hapos
    simp [weightK, Multiset.toFinsupp_apply, hcountne]

/- accepted add_to_file helper 9 -/
noncomputable def kappaPoly (m : ℕ) (ρ : Nat.Partition m) : Polynomial ℤ :=
  if ρ.parts.Nodup then (-Polynomial.X : Polynomial ℤ) ^ ρ.parts.toFinset.card else 0

lemma toFinsupp_prod_weightP {m : ℕ} (ρ : Nat.Partition m) :
    (Multiset.toFinsupp ρ.parts).prod weightP =
      polyToPW ((1 - Polynomial.X : Polynomial ℤ) ^ ρ.parts.toFinset.card) := by
  rw [Finsupp.prod, Multiset.toFinsupp_support]
  rw [← Finset.prod_const]
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro a ha
  simp [weightP]

/- accepted add_to_file helper 10 -/
lemma toFinsupp_prod_weightE {m : ℕ} (ρ : Nat.Partition m) :
    (Multiset.toFinsupp ρ.parts).prod weightE =
      polyToPW (Polynomial.C (Polynomial.eval 1 (kappaPoly m ρ))) := by
  by_cases h : ρ.parts.Nodup
  · simp [h, kappaPoly]
    rw [Finsupp.prod, Multiset.toFinsupp_support]
    rw [← Finset.prod_const]
    apply Finset.prod_congr rfl
    intro a ha
    have hmem : a ∈ ρ.parts := Multiset.mem_toFinset.mp ha
    have hcount : Multiset.count a ρ.parts = 1 :=
      Multiset.count_eq_one_of_mem h hmem
    simp [weightE, Multiset.toFinsupp_apply, hcount]
  · simp [h, kappaPoly]
    rw [Finsupp.prod, Multiset.toFinsupp_support]
    rw [Multiset.nodup_iff_count_le_one] at h
    push_neg at h
    rcases h with ⟨a, ha⟩
    have hapos : a ∈ ρ.parts.toFinset := by
      rw [Multiset.mem_toFinset]
      by_contra hnot
      have hcount0 : Multiset.count a ρ.parts = 0 :=
        Multiset.count_eq_zero_of_notMem hnot
      omega
    have hcountne : Multiset.count a ρ.parts ≠ 1 := by omega
    apply Finset.prod_eq_zero hapos
    simp [weightE, Multiset.toFinsupp_apply, hcountne]

/- accepted add_to_file helper 11 -/
lemma coeff_genFun_weightK (k : ℕ) :
    (PowerSeries.coeff k) (Nat.Partition.genFun weightK) =
      polyToPW (∑ ρ : Nat.Partition k, kappaPoly k ρ) := by
  simp [Nat.Partition.genFun, kappaPoly, toFinsupp_prod_weightK]
  apply Finset.sum_congr rfl
  intro ρ hρ
  by_cases h : ρ.parts.Nodup <;> simp [h]

lemma coeff_genFun_weightP (k : ℕ) :
    (PowerSeries.coeff k) (Nat.Partition.genFun weightP) =
      polyToPW (∑ ρ : Nat.Partition k,
        (1 - Polynomial.X : Polynomial ℤ) ^ ρ.parts.toFinset.card) := by
  simp [Nat.Partition.genFun, toFinsupp_prod_weightP]

lemma coeff_genFun_weightE (k : ℕ) :
    (PowerSeries.coeff k) (Nat.Partition.genFun weightE) =
      polyToPW (Polynomial.C (∑ ρ : Nat.Partition k,
        Polynomial.eval 1 (kappaPoly k ρ))) := by
  simp [Nat.Partition.genFun, toFinsupp_prod_weightE]

/- accepted add_to_file helper 12 -/
noncomputable def localK (k : ℕ) : Polynomial ℤ :=
  ∑ ρ : Nat.Partition k, kappaPoly k ρ

noncomputable def localP (k : ℕ) : Polynomial ℤ :=
  ∑ ρ : Nat.Partition k,
    (1 - Polynomial.X : Polynomial ℤ) ^ ρ.parts.toFinset.card

noncomputable def localE (k : ℕ) : ℤ :=
  ∑ ρ : Nat.Partition k, Polynomial.eval 1 (kappaPoly k ρ)

/- accepted add_to_file helper 13 -/
lemma local_identity (k : ℕ) :
    localK k =
      ∑ r ∈ Finset.range (k + 1),
        Polynomial.C (localE r) * localP (k - r) := by
  apply polyToPW_injective
  have hcoeff := congrArg (PowerSeries.coeff k) genFun_weightK_eq
  rw [coeff_genFun_weightK] at hcoeff
  rw [PowerSeries.coeff_mul] at hcoeff
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => (PowerSeries.coeff a) (Nat.Partition.genFun weightE) *
      (PowerSeries.coeff b) (Nat.Partition.genFun weightP)) k] at hcoeff
  simp_rw [coeff_genFun_weightE, coeff_genFun_weightP] at hcoeff
  simp only [localK]
  calc
    polyToPW (∑ ρ : Nat.Partition k, kappaPoly k ρ)
        = ∑ r ∈ Finset.range (k + 1),
          polyToPW (Polynomial.C (localE r)) * polyToPW (localP (k - r)) := by
          simpa [localE, localP] using hcoeff
    _ = polyToPW (∑ r ∈ Finset.range (k + 1),
          Polynomial.C (localE r) * localP (k - r)) := by
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro r hr
          simp

/- accepted add_to_file helper 14 -/
lemma bounded_sum_eq_antidiagonalTuple {M : Type*} [AddCommMonoid M]
    (n a : ℕ) (F : (Fin n → ℕ) → M) :
    (∑ s : Fin n → Fin (a + 1),
      if h : (∑ i, (s i : ℕ)) = a then F (fun i => (s i : ℕ)) else 0)
    =
    ∑ t ∈ Finset.Nat.antidiagonalTuple n a, F t := by
  rw [Finset.sum_dite]
  simp
  apply Finset.sum_bij
    (i := fun s _ => fun i => (s.1 i : ℕ))
  · intro s hs
    rw [Finset.Nat.mem_antidiagonalTuple]
    exact (Finset.mem_filter.mp s.2).2
  · intro s hs t ht hst
    apply Subtype.ext
    funext i
    apply Fin.ext
    exact congrFun hst i
  · intro t ht
    rw [Finset.Nat.mem_antidiagonalTuple] at ht
    have hle : ∀ i : Fin n, t i ≤ a := by
      intro i
      rw [← ht]
      exact Finset.single_le_sum (fun j _ => Nat.zero_le (t j)) (Finset.mem_univ i)
    refine ⟨⟨fun i => ⟨t i, Nat.lt_succ_of_le (hle i)⟩, ?_⟩, Finset.mem_attach _ _, ?_⟩
    · simpa using ht
    · rfl
  · intro s hs
    rfl

/- accepted add_to_file helper 15 -/
lemma finsuppAntidiag_range_sum_eq_antidiagonalTuple {M : Type*} [CommSemiring M]
    (n a : ℕ) (F : ℕ → M) :
    (∑ l ∈ (Finset.range n).finsuppAntidiag a,
      ∏ i ∈ Finset.range n, F (l i))
    =
    ∑ t ∈ Finset.Nat.antidiagonalTuple n a, ∏ i, F (t i) := by
  apply Finset.sum_bij
    (i := fun l _ => fun i : Fin n => l i)
  · intro l hl
    rw [Finset.Nat.mem_antidiagonalTuple]
    have hlm := (Finset.mem_finsuppAntidiag.mp hl).1
    rw [Fin.sum_univ_eq_sum_range (f := fun i : ℕ => l i) n]
    exact hlm
  · intro l₁ hl₁ l₂ hl₂ h
    apply Finsupp.ext
    intro m
    by_cases hm : m < n
    · exact congrFun h ⟨m, hm⟩
    · have hm1 : m ∉ l₁.support := by
        intro hmem
        exact hm (Finset.mem_range.mp ((Finset.mem_finsuppAntidiag.mp hl₁).2 hmem))
      have hm2 : m ∉ l₂.support := by
        intro hmem
        exact hm (Finset.mem_range.mp ((Finset.mem_finsuppAntidiag.mp hl₂).2 hmem))
      have hz1 : l₁ m = 0 := by
        by_contra hz
        exact hm1 ((Finsupp.mem_support_iff).2 hz)
      have hz2 : l₂ m = 0 := by
        by_contra hz
        exact hm2 ((Finsupp.mem_support_iff).2 hz)
      rw [hz1, hz2]
  · intro t ht
    let l : ℕ →₀ ℕ := Finsupp.onFinset (Finset.range n)
      (fun m => if hm : m < n then t ⟨m, hm⟩ else 0) (by
        intro m hm
        rw [Finset.mem_range]
        by_contra hmn
        simp [hmn] at hm)
    refine ⟨l, ?_, ?_⟩
    · rw [Finset.mem_finsuppAntidiag]
      constructor
      · rw [Finset.Nat.mem_antidiagonalTuple] at ht
        calc
          (Finset.range n).sum (⇑l)
              = ∑ m ∈ Finset.range n,
                  (if hm : m < n then t ⟨m, hm⟩ else 0) := by
                  apply Finset.sum_congr rfl
                  intro m hm
                  simp [l]
          _ = ∑ i : Fin n, t i :=
                (Finset.sum_fin_eq_sum_range (fun i : Fin n => t i)).symm
          _ = a := ht
      · exact Finsupp.support_onFinset_subset
    · funext i
      simp [l, i.2]
  · intro l hl
    rw [Fin.prod_univ_eq_prod_range (f := fun i : ℕ => F (l i)) n]

/- accepted add_to_file helper 16 -/
noncomputable def convPoly (F : ℕ → Polynomial ℤ) (n a : ℕ) : Polynomial ℤ :=
  ∑ s : Fin n → Fin (a + 1),
    if h : (∑ i, (s i : ℕ)) = a then
      ∏ i, F (s i : ℕ)
    else 0

noncomputable def convInt (E : ℕ → ℤ) (n a : ℕ) : ℤ :=
  ∑ s : Fin n → Fin (a + 1),
    if h : (∑ i, (s i : ℕ)) = a then
      ∏ i, E (s i : ℕ)
    else 0

/- accepted add_to_file helper 17 -/
lemma coeff_mk_pow (F : ℕ → Polynomial ℤ) (n a : ℕ) :
    (PowerSeries.coeff a)
      ((PowerSeries.mk F : PowerSeries (Polynomial ℤ)) ^ n)
      = convPoly F n a := by
  rw [PowerSeries.coeff_pow]
  simp_rw [PowerSeries.coeff_mk]
  rw [finsuppAntidiag_range_sum_eq_antidiagonalTuple]
  rw [← bounded_sum_eq_antidiagonalTuple n a
    (F := fun t => ∏ i : Fin n, F (t i))]
  rfl

lemma coeff_mkC_pow (E : ℕ → ℤ) (n a : ℕ) :
    (PowerSeries.coeff a)
      ((PowerSeries.mk (fun a => Polynomial.C (E a)) : PowerSeries (Polynomial ℤ)) ^ n)
      = Polynomial.C (convInt E n a) := by
  rw [PowerSeries.coeff_pow]
  simp_rw [PowerSeries.coeff_mk]
  rw [finsuppAntidiag_range_sum_eq_antidiagonalTuple n a
    (F := fun m => Polynomial.C (E m))]
  rw [← bounded_sum_eq_antidiagonalTuple n a
    (F := fun t => ∏ i : Fin n, Polynomial.C (E (t i)))]
  simp [convInt]

/- accepted add_to_file helper 18 -/
lemma series_local_identity :
    (PowerSeries.mk localK : PowerSeries (Polynomial ℤ)) =
      (PowerSeries.mk (fun a => Polynomial.C (localE a)) : PowerSeries (Polynomial ℤ)) *
        (PowerSeries.mk localP : PowerSeries (Polynomial ℤ)) := by
  apply PowerSeries.ext
  intro a
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun r b => (PowerSeries.coeff r)
      (PowerSeries.mk (fun a => Polynomial.C (localE a)) : PowerSeries (Polynomial ℤ)) *
      (PowerSeries.coeff b) (PowerSeries.mk localP : PowerSeries (Polynomial ℤ))) a]
  simp_rw [PowerSeries.coeff_mk]
  exact local_identity a

/- accepted add_to_file helper 19 -/
lemma conv_identity (n k : ℕ) :
    convPoly localK n k =
      ∑ r ∈ Finset.range (k + 1),
        Polynomial.C (convInt localE n r) * convPoly localP n (k - r) := by
  have h := congrArg (fun A : PowerSeries (Polynomial ℤ) => A ^ n) series_local_identity
  have hc := congrArg (PowerSeries.coeff k) h
  rw [coeff_mk_pow] at hc
  change convPoly localK n k =
    (PowerSeries.coeff k)
      (((PowerSeries.mk (fun a => Polynomial.C (localE a)) : PowerSeries (Polynomial ℤ)) *
        (PowerSeries.mk localP : PowerSeries (Polynomial ℤ))) ^ n) at hc
  rw [mul_pow] at hc
  rw [PowerSeries.coeff_mul] at hc
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun r b => (PowerSeries.coeff r)
      ((PowerSeries.mk (fun a => Polynomial.C (localE a)) : PowerSeries (Polynomial ℤ)) ^ n) *
      (PowerSeries.coeff b)
      ((PowerSeries.mk localP : PowerSeries (Polynomial ℤ)) ^ n)) k] at hc
  simp_rw [coeff_mkC_pow, coeff_mk_pow] at hc
  exact hc

/- accepted add_to_file helper 20 -/
lemma epsilon_eq_conv (n a : ℕ) :
    (∑ s : Fin n → Fin (a + 1),
      if h : (∑ i, (s i : ℕ)) = a then
        ∑ p : (i : Fin n) → Nat.Partition (s i : ℕ),
          ∏ i, kappaPoly (s i : ℕ) (p i)
      else 0)
    = convPoly localK n a := by
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h : (∑ i, (s i : ℕ)) = a
  · simp [h, localK]
    rw [Finset.prod_univ_sum]
    rw [Fintype.piFinset_univ]
  · simp [h]

lemma pp_eq_conv (n a : ℕ) :
    (∑ s : Fin n → Fin (a + 1),
      if h : (∑ i, (s i : ℕ)) = a then
        ∑ ρ : (i : Fin n) → Nat.Partition (s i : ℕ),
          (1 - Polynomial.X : Polynomial ℤ) ^
            (∑ i, (ρ i).parts.toFinset.card)
      else 0)
    = convPoly localP n a := by
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h : (∑ i, (s i : ℕ)) = a
  · simp [h, localP]
    rw [Finset.prod_univ_sum]
    rw [Fintype.piFinset_univ]
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [Finset.prod_pow_eq_pow_sum]
  · simp [h]

/- accepted add_to_file helper 21 -/
lemma eval_localK (a : ℕ) :
    Polynomial.eval 1 (localK a) = localE a := by
  change (Polynomial.evalRingHom 1) (∑ ρ : Nat.Partition a, kappaPoly a ρ) = localE a
  rw [map_sum]
  rfl

lemma eval_conv_localK (n a : ℕ) :
    Polynomial.eval 1 (convPoly localK n a) = convInt localE n a := by
  change (Polynomial.evalRingHom 1) (convPoly localK n a) = convInt localE n a
  rw [convPoly]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h : (∑ i, (s i : ℕ)) = a
  · simp [h]
    apply Finset.prod_congr rfl
    intro i hi
    exact eval_localK (s i : ℕ)
  · simp [h]

/- verified submission -/
theorem proposition_3_8 (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    let κ : (m : ℕ) → Nat.Partition m → Polynomial ℤ := fun _ ρ =>
      if ρ.parts.Nodup then
        (-Polynomial.X : Polynomial ℤ) ^ ρ.parts.toFinset.card
      else 0
    let ε : ℕ → Polynomial ℤ := fun a =>
      ∑ s : Fin n → Fin (a + 1),
        if h : (∑ i, (s i : ℕ)) = a then
          ∑ p : (i : Fin n) → Nat.Partition (s i : ℕ),
            ∏ i, κ (s i : ℕ) (p i)
        else 0
    let pp : ℕ → Polynomial ℤ := fun a =>
      ∑ s : Fin n → Fin (a + 1),
        if h : (∑ i, (s i : ℕ)) = a then
          ∑ ρ : (i : Fin n) → Nat.Partition (s i : ℕ),
            (1 - Polynomial.X : Polynomial ℤ) ^
              (∑ i, (ρ i).parts.toFinset.card)
        else 0
    let ε₁ : ℕ → ℤ := fun a => Polynomial.eval 1 (ε a)
    ε k = ∑ r ∈ Finset.range (k + 1), Polynomial.C (ε₁ r) * pp (k - r) := by
  dsimp only
  have heval : ∀ r : ℕ,
      Polynomial.eval 1
          (∑ s : Fin n → Fin (r + 1),
            if h : (∑ i, (s i : ℕ)) = r then
              ∑ p : (i : Fin n) → Nat.Partition (s i : ℕ),
                ∏ i, if (p i).parts.Nodup then
                  (-Polynomial.X : Polynomial ℤ) ^ (p i).parts.toFinset.card
                else 0
            else 0)
        = convInt localE n r := by
    intro r
    change Polynomial.eval 1
        (∑ s : Fin n → Fin (r + 1),
          if h : (∑ i, (s i : ℕ)) = r then
            ∑ p : (i : Fin n) → Nat.Partition (s i : ℕ),
              ∏ i, kappaPoly (s i : ℕ) (p i)
          else 0)
      = convInt localE n r
    rw [epsilon_eq_conv]
    exact eval_conv_localK n r
  change (∑ s : Fin n → Fin (k + 1),
      if h : (∑ i, (s i : ℕ)) = k then
        ∑ p : (i : Fin n) → Nat.Partition (s i : ℕ),
          ∏ i, kappaPoly (s i : ℕ) (p i)
      else 0)
    =
    ∑ r ∈ Finset.range (k + 1),
      Polynomial.C
          (Polynomial.eval 1
            (∑ s : Fin n → Fin (r + 1),
              if h : (∑ i, (s i : ℕ)) = r then
                ∑ p : (i : Fin n) → Nat.Partition (s i : ℕ),
                  ∏ i, kappaPoly (s i : ℕ) (p i)
              else 0)) *
        ∑ s : Fin n → Fin ((k - r) + 1),
          if h : (∑ i, (s i : ℕ)) = k - r then
            ∑ ρ : (i : Fin n) → Nat.Partition (s i : ℕ),
              (1 - Polynomial.X : Polynomial ℤ) ^
                (∑ i, (ρ i).parts.toFinset.card)
          else 0
  rw [epsilon_eq_conv]
  rw [conv_identity]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← heval r]
  congr 1
  exact (pp_eq_conv n (k - r)).symm


#check_dependency_graph "proposition_3_8" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let κ := fun x ρ => if ρ.parts.Nodup then (-Polynomial.X) ^ ρ.parts.toFinset.card else 0; let ε := fun a => ∑ s, if h : ∑ i, ↑(s i) = a then ∑ p, ∏ i, κ (↑(s i)) (p i) else 0; let pp := fun a => ∑ s, if h : ∑ i, ↑(s i) = a then ∑ ρ, (1 - Polynomial.X) ^ ∑ i, (ρ i).parts.toFinset.card else 0; let ε₁ := fun a => Polynomial.eval 1 (ε a); ε k = ∑ r ∈ Finset.range (k + 1), Polynomial.C (ε₁ r) * pp (k - r)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2920_proposition_3_8\",\"reconstructedProofSha256\":\"ebb92f473f54b0b7dd3e27eb1b4bb2884ae689e01a898cfc10167c756afb7838\",\"selectedEdgeCount\":1,\"theoremName\":\"proposition_3_8\",\"topologySha256\":\"072a6258b8a4599f09053e96ae1c5d3b4f28aeefb6ed9495f914f7e8c63fff72\"}"
