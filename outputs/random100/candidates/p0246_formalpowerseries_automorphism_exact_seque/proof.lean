import Mathlib

/- accepted add_to_file helper 1 -/
import Mathlib

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
