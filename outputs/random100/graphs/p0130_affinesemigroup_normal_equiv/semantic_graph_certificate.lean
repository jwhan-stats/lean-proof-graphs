import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p0130_affinesemigroup_normal_equiv
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: b6e0b51344ee410e1677d05af1a57204e4ffb055c0a46ace81c966c822d992e2
-- reconstructed_proof_sha256: cb7233a68a6118393aa37b189778a13ecbed506886a57b9eae26129aa1a45739
-- selected_edge_count: 1

/- accepted add_to_file helper 1 -/
noncomputable def affineSemigroupBasis
    (d : ℕ) (hd : 1 ≤ d) (a : Fin d → Fin d → ℕ)
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ))) :
    Module.Basis (Fin d) ℝ (Fin d → ℝ) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  exact @basisOfLinearIndependentOfCardEqFinrank ℝ (Fin d → ℝ) _ _ _ (Fin d) this _
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)) haLI (by
        rw [Module.finrank_pi, Fintype.card_fin])

lemma affineSemigroupBasis_apply
    (d : ℕ) (hd : 1 ≤ d) (a : Fin d → Fin d → ℕ)
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ))) (i : Fin d) :
    affineSemigroupBasis d hd a haLI i = fun j => (a i j : ℝ) := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  simp [affineSemigroupBasis]

lemma affineSemigroup_sum_coords
    {d : ℕ} {hd : 1 ≤ d} {a : Fin d → Fin d → ℕ}
    {haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ))}
    {x : Fin d → ℝ} {c : Fin d → ℝ}
    (hx : x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))) :
    ∀ i, (affineSemigroupBasis d hd a haLI).repr x i = c i := by
  intro i
  subst x
  let b := affineSemigroupBasis d hd a haLI
  have hb : ∀ k, b k = fun j : Fin d => (a k j : ℝ) := by
    intro k
    exact affineSemigroupBasis_apply d hd a haLI k
  have hsum : (∑ k, c k • (fun j : Fin d => (a k j : ℝ))) =
      (Finsupp.linearCombination ℝ (fun k => b k))
        (Finsupp.equivFunOnFinite.symm c) := by
    rw [Finsupp.linearCombination_apply]
    rw [Finsupp.sum_fintype]
    · simp [hb]
    · intro j
      simp
  rw [hsum, Module.Basis.repr_linearCombination]
  simp

abbrev affineSemigroupNatToInt (d : ℕ) : (Fin d → ℕ) → (Fin d → ℤ) :=
  fun u j => (u j : ℤ)

abbrev affineSemigroupNatToReal (d : ℕ) : (Fin d → ℕ) → (Fin d → ℝ) :=
  fun u j => (u j : ℝ)

abbrev affineSemigroupIntToReal (d : ℕ) : (Fin d → ℤ) → (Fin d → ℝ) :=
  fun u j => (u j : ℝ)

lemma affineSemigroup_S_coord_nonneg
    {d : ℕ} (hd : 1 ≤ d)
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    {haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ))}
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ)))
    {w : Fin d → ℕ} (hw : w ∈ S) (i : Fin d) :
    0 ≤ (affineSemigroupBasis d hd a haLI).repr
      (affineSemigroupNatToReal d w) i := by
  have hmem : affineSemigroupNatToReal d w ∈
      ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
        (S : Set (Fin d → ℕ))) := by
    exact ⟨w, hw, rfl⟩
  have hhull : affineSemigroupNatToReal d w ∈
      ConvexCone.hull ℝ
        ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
          (S : Set (Fin d → ℕ))) :=
    ConvexCone.subset_hull hmem
  rcases (hcone _ ).mp hhull with ⟨c, hc, hx⟩
  rw [affineSemigroup_sum_coords hx i]
  exact hc i

/- accepted add_to_file helper 2 -/
def affineSemigroupCone (d : ℕ) (a : Fin d → Fin d → ℕ) : Set (Fin d → ℝ) :=
  {x | ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
    x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))}

def affineSemigroupRelintCone (d : ℕ) (a : Fin d → Fin d → ℕ) : Set (Fin d → ℝ) :=
  {x | ∃ c : Fin d → ℝ, (∀ i, 0 < c i) ∧
    x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))}

def affineSemigroupFundamentalParallelepiped
    (d : ℕ) (a : Fin d → Fin d → ℕ) : Set (Fin d → ℝ) :=
  {x | ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i ∧ c i < 1) ∧
    x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))}

def affineSemigroupApery (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) (a : Fin d → Fin d → ℕ) :
    Set (Fin d → ℕ) :=
  {w | w ∈ S ∧ ∀ i, ¬∃ s : Fin d → ℕ, s ∈ S ∧ w = s + a i}

def affineSemigroupG (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) : Set (Fin d → ℤ) :=
  {z | ∃ u : Fin d → ℕ, u ∈ S ∧
    ∃ v : Fin d → ℕ, v ∈ S ∧
      z = affineSemigroupNatToInt d u - affineSemigroupNatToInt d v}

def affineSemigroupNormal (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) (a : Fin d → Fin d → ℕ) : Prop :=
  affineSemigroupNatToInt d '' (S : Set (Fin d → ℕ)) =
    affineSemigroupG d S ∩
      {z | affineSemigroupIntToReal d z ∈ affineSemigroupCone d a}

/- accepted add_to_file helper 3 -/
lemma affineSemigroup_normal_implies_condition4
    {d : ℕ} (hd : 1 ≤ d)
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haS : ∀ i, a i ∈ S)
    {haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ))}
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ)))
    (hnormal : affineSemigroupNormal d S a)
    {w : Fin d → ℕ} (hw : w ∈ affineSemigroupApery d S a) :
    affineSemigroupNatToReal d w ∈
      affineSemigroupFundamentalParallelepiped d a := by
  rcases hw with ⟨hwS, hnopred⟩
  have hmem : affineSemigroupNatToReal d w ∈
      ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
        (S : Set (Fin d → ℕ))) := by
    exact ⟨w, hwS, rfl⟩
  have hhull : affineSemigroupNatToReal d w ∈
      ConvexCone.hull ℝ
        ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
          (S : Set (Fin d → ℕ))) :=
    ConvexCone.subset_hull hmem
  rcases (hcone _ ).mp hhull with ⟨c, hc, hx⟩
  refine ⟨c, ?_, hx⟩
  intro i
  refine ⟨hc i, ?_⟩
  by_contra hlt
  have hci : 1 ≤ c i := le_of_not_gt hlt
  let z : Fin d → ℤ :=
    affineSemigroupNatToInt d w - affineSemigroupNatToInt d (a i)
  let dc : Fin d → ℝ := fun k => c k - (if k = i then 1 else 0)
  have hdc : ∀ k, 0 ≤ dc k := by
    intro k
    by_cases hk : k = i
    · simp [dc, hk, sub_nonneg.mpr hci]
    · simp [dc, hk, hc k]
  have hzreal : affineSemigroupIntToReal d z =
      affineSemigroupNatToReal d w - affineSemigroupNatToReal d (a i) := by
    funext j
    simp [z, affineSemigroupIntToReal, affineSemigroupNatToInt,
      affineSemigroupNatToReal, Int.cast_sub]
  have hzC : affineSemigroupIntToReal d z ∈ affineSemigroupCone d a := by
    refine ⟨dc, hdc, ?_⟩
    rw [hzreal, hx]
    simp [dc, Finset.sum_sub_distrib, sub_smul]
  have hzG : z ∈ affineSemigroupG d S := by
    refine ⟨w, hwS, a i, haS i, rfl⟩
  have hzimage : z ∈ affineSemigroupNatToInt d '' (S : Set (Fin d → ℕ)) := by
    change z ∈ affineSemigroupNatToInt d '' (S : Set (Fin d → ℕ))
    rw [hnormal]
    exact ⟨hzG, hzC⟩
  rcases hzimage with ⟨s, hsS, hsz⟩
  have hws : w = s + a i := by
    funext j
    have hpoint := congrFun hsz j
    change (s j : ℤ) = (w j : ℤ) - (a i j : ℤ) at hpoint
    have hnat : s j + a i j = w j := by
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_add]
      omega
    simpa [hnat]
  exact hnopred i ⟨s, hsS, hws⟩

/- accepted add_to_file helper 4 -/
def affineSemigroupLeS (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) :
    (Fin d → ℕ) → (Fin d → ℕ) → Prop :=
  fun u v => ∃ s : Fin d → ℕ, s ∈ S ∧ v = u + s

def affineSemigroupMaximalApery (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) (a : Fin d → Fin d → ℕ) :
    (Fin d → ℕ) → Prop :=
  fun m => m ∈ affineSemigroupApery d S a ∧
    ∀ w, w ∈ affineSemigroupApery d S a →
      affineSemigroupLeS d S m w → affineSemigroupLeS d S w m

def affineSemigroupQF (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) (a : Fin d → Fin d → ℕ) :
    Set (Fin d → ℤ) :=
  {f | ∃ m, affineSemigroupMaximalApery d S a m ∧
    f = affineSemigroupNatToInt d m -
      ∑ i, affineSemigroupNatToInt d (a i)}

def affineSemigroupCondition2 (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) (a : Fin d → Fin d → ℕ) : Prop :=
  ∀ f, f ∈ affineSemigroupQF d S a →
    -f ∈ affineSemigroupNatToInt d '' (S : Set (Fin d → ℕ)) ∧
      affineSemigroupIntToReal d (-f) ∈ affineSemigroupRelintCone d a

def affineSemigroupCondition3 (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) (a : Fin d → Fin d → ℕ) : Prop :=
  ∀ f, f ∈ affineSemigroupQF d S a →
    affineSemigroupIntToReal d (-f) ∈ affineSemigroupRelintCone d a

def affineSemigroupCondition4 (d : ℕ)
    (S : AddSubmonoid (Fin d → ℕ)) (a : Fin d → Fin d → ℕ) : Prop :=
  ∀ w, w ∈ affineSemigroupApery d S a →
    affineSemigroupNatToReal d w ∈
      affineSemigroupFundamentalParallelepiped d a

/- accepted add_to_file helper 5 -/
lemma affineSemigroup_normal_implies_condition2
    {d : ℕ} (hd : 1 ≤ d)
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haS : ∀ i, a i ∈ S)
    {haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ))}
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ)))
    (hnormal : affineSemigroupNormal d S a) :
    affineSemigroupCondition2 d S a := by
  intro f hf
  rcases hf with ⟨m, hm, rfl⟩
  rcases hm.1 with ⟨hmS, hmnopred⟩
  have hcond4 := affineSemigroup_normal_implies_condition4
    (d := d) (hd := hd) (S := S) (a := a) (haLI := haLI)
    haS hcone hnormal hm.1
  rcases hcond4 with ⟨c, hc, hxm⟩
  let q : Fin d → ℝ := fun i => 1 - c i
  have hq : ∀ i, 0 < q i := by
    intro i
    exact sub_pos.mpr (hc i).2
  have hsumaS : (∑ i, a i) ∈ S := by
    exact S.sum_mem (fun i hi => haS i)
  have hcastsum : affineSemigroupNatToInt d (∑ i, a i) =
      ∑ i, affineSemigroupNatToInt d (a i) := by
    funext j
    simp [affineSemigroupNatToInt]
  have hneg :
      -(affineSemigroupNatToInt d m - ∑ i, affineSemigroupNatToInt d (a i)) =
        ∑ i, affineSemigroupNatToInt d (a i) - affineSemigroupNatToInt d m := by
    abel
  have hG : -(affineSemigroupNatToInt d m -
      ∑ i, affineSemigroupNatToInt d (a i)) ∈ affineSemigroupG d S := by
    rw [hneg, ← hcastsum]
    exact ⟨∑ i, a i, hsumaS, m, hmS, rfl⟩
  have hreal :
      affineSemigroupIntToReal d
        (-(affineSemigroupNatToInt d m -
          ∑ i, affineSemigroupNatToInt d (a i))) =
        ∑ i, q i • (fun j : Fin d => (a i j : ℝ)) := by
    rw [hneg]
    funext j
    simp [affineSemigroupIntToReal, affineSemigroupNatToInt,
      affineSemigroupNatToReal, q]
    have hmcoord := congrFun hxm j
    simp [affineSemigroupNatToReal] at hmcoord
    rw [hmcoord]
    simp [Finset.sum_sub_distrib, sub_mul]
  have hrel :
      affineSemigroupIntToReal d
        (-(affineSemigroupNatToInt d m -
          ∑ i, affineSemigroupNatToInt d (a i))) ∈
        affineSemigroupRelintCone d a := by
    exact ⟨q, hq, hreal⟩
  have hC :
      affineSemigroupIntToReal d
        (-(affineSemigroupNatToInt d m -
          ∑ i, affineSemigroupNatToInt d (a i))) ∈
        affineSemigroupCone d a := by
    rcases hrel with ⟨r, hr, hx⟩
    exact ⟨r, fun i => le_of_lt (hr i), hx⟩
  have himage :
      -(affineSemigroupNatToInt d m -
        ∑ i, affineSemigroupNatToInt d (a i)) ∈
        affineSemigroupNatToInt d '' (S : Set (Fin d → ℕ)) := by
    change -(affineSemigroupNatToInt d m -
        ∑ i, affineSemigroupNatToInt d (a i)) ∈
      affineSemigroupNatToInt d '' (S : Set (Fin d → ℕ))
    rw [hnormal]
    exact ⟨hG, hC⟩
  exact ⟨himage, hrel⟩

/- accepted add_to_file helper 6 -/
lemma affineSemigroup_exists_apery_reduction
    {d : ℕ}
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    {s : Fin d → ℕ} (hs : s ∈ S) :
    ∃ w : Fin d → ℕ, ∃ n : Fin d → ℕ,
      w ∈ affineSemigroupApery d S a ∧
        s = w + ∑ i, n i • a i := by
  let total : (Fin d → ℕ) → ℕ := fun u => ∑ j, u j
  have step : ∀ N : ℕ, ∀ t : Fin d → ℕ, t ∈ S → total t = N →
      ∃ w : Fin d → ℕ, ∃ n : Fin d → ℕ,
        w ∈ affineSemigroupApery d S a ∧
          t = w + ∑ i, n i • a i := by
    intro N
    refine Nat.strong_induction_on N ?_
    intro N ih t htS htN
    by_cases hAp : ∀ i, ¬∃ p : Fin d → ℕ, p ∈ S ∧ t = p + a i
    · exact ⟨t, 0, ⟨htS, hAp⟩, by simp⟩
    · have hbad : ∃ i, ∃ p : Fin d → ℕ, p ∈ S ∧ t = p + a i := by
        push Not at hAp
        rcases hAp with ⟨i, hi⟩
        exact ⟨i, hi⟩
      rcases hbad with ⟨i, p, hpS, htp⟩
      have haneq : a i ≠ 0 := by
        intro hz
        have hrealne := haLI.ne_zero i
        apply hrealne
        funext j
        simp [hz]
      have hapos : 0 < total (a i) := by
        have hex : ∃ j, a i j ≠ 0 := by
          by_contra hnone
          push Not at hnone
          apply haneq
          funext j
          exact hnone j
        rcases hex with ⟨j, hj⟩
        exact Finset.sum_pos' (fun k hk => Nat.zero_le _)
          ⟨j, Finset.mem_univ j, Nat.pos_of_ne_zero hj⟩
      have htot : total t = total p + total (a i) := by
        rw [htp]
        simp [total, Finset.sum_add_distrib]
      have hlt : total p < N := by
        omega
      have hpN : total p = total p := rfl
      rcases ih (total p) hlt p hpS hpN with ⟨w, n, hw, hpw⟩
      refine ⟨w, fun k => n k + (if k = i then 1 else 0), hw, ?_⟩
      rw [htp, hpw]
      have hsumif : (∑ k, (if k = i then (1 : ℕ) else 0) • a k) = a i := by
        simp
      calc
        (w + ∑ k, n k • a k) + a i
            = w + (∑ k, n k • a k + a i) := by abel
        _ = w + (∑ k, n k • a k + ∑ k, (if k = i then (1 : ℕ) else 0) • a k) := by
          rw [hsumif]
        _ = w + ∑ k, (n k + (if k = i then 1 else 0)) • a k := by
          rw [← Finset.sum_add_distrib]
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          simp [add_smul]
  exact step (total s) s hs rfl

/- accepted add_to_file helper 7 -/
def affineSemigroupIntCastLinear (d : ℕ) :
    (Fin d → ℤ) →ₗ[ℤ] (Fin d → ℝ) where
  toFun := affineSemigroupIntToReal d
  map_add' := by
    intro x y
    funext j
    simp [affineSemigroupIntToReal]
  map_smul' := by
    intro z x
    funext j
    simp [affineSemigroupIntToReal]

/- accepted add_to_file helper 8 -/
lemma affineSemigroup_int_linearIndependent
    {d : ℕ} {a : Fin d → Fin d → ℕ}
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ))) :
    LinearIndependent ℤ
      (fun i : Fin d => affineSemigroupNatToInt d (a i)) := by
  have hzreal : LinearIndependent ℤ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)) := by
    refine LinearIndependent.restrict_scalars ?_ haLI
    simpa using (Int.cast_injective (α := ℝ))
  refine LinearIndependent.of_comp (affineSemigroupIntCastLinear d) ?_
  simpa [affineSemigroupIntCastLinear, affineSemigroupIntToReal,
    affineSemigroupNatToInt] using hzreal

/- accepted add_to_file helper 9 -/
def affineSemigroupIntegerLattice
    (d : ℕ) (a : Fin d → Fin d → ℕ) : Submodule ℤ (Fin d → ℤ) :=
  Submodule.span ℤ
    (Set.range (fun i : Fin d => affineSemigroupNatToInt d (a i)))

/- accepted add_to_file helper 10 -/
lemma affineSemigroup_finite_quotient_integerLattice
    {d : ℕ} {a : Fin d → Fin d → ℕ}
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ))) :
    Finite ((Fin d → ℤ) ⧸ affineSemigroupIntegerLattice d a) := by
  refine Submodule.finiteQuotientOfFreeOfRankEq
    (affineSemigroupIntegerLattice d a) ?_
  rw [affineSemigroupIntegerLattice,
    finrank_span_eq_card (affineSemigroup_int_linearIndependent haLI),
    Module.finrank_pi, Fintype.card_fin]

/- accepted add_to_file helper 11 -/
lemma affineSemigroup_exists_positive_nsmul_mem_integerLattice
    {d : ℕ} {a : Fin d → Fin d → ℕ}
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    (z : Fin d → ℤ) :
    ∃ n : ℕ, 0 < n ∧ n • z ∈ affineSemigroupIntegerLattice d a := by
  haveI : Finite ((Fin d → ℤ) ⧸ affineSemigroupIntegerLattice d a) :=
    affineSemigroup_finite_quotient_integerLattice haLI
  let q : (Fin d → ℤ) ⧸ affineSemigroupIntegerLattice d a :=
    Submodule.Quotient.mk (p := affineSemigroupIntegerLattice d a) z
  refine ⟨addOrderOf q, addOrderOf_pos q, ?_⟩
  have hq : addOrderOf q • q = 0 := addOrderOf_nsmul_eq_zero q
  have hmk : Submodule.Quotient.mk (p := affineSemigroupIntegerLattice d a)
      (addOrderOf q • z) =
      (0 : (Fin d → ℤ) ⧸ affineSemigroupIntegerLattice d a) := by
    change addOrderOf q •
        (Submodule.Quotient.mk (p := affineSemigroupIntegerLattice d a) z) = 0
    exact hq
  exact (Submodule.Quotient.mk_eq_zero (affineSemigroupIntegerLattice d a)).mp hmk

/- accepted add_to_file helper 12 -/
lemma affineSemigroup_exists_S_sub_mem_integerLattice
    {d : ℕ} {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    {z : Fin d → ℤ} (hz : z ∈ affineSemigroupG d S) :
    ∃ s : Fin d → ℕ, s ∈ S ∧
      z - affineSemigroupNatToInt d s ∈ affineSemigroupIntegerLattice d a := by
  rcases hz with ⟨u, huS, v, hvS, rfl⟩
  rcases affineSemigroup_exists_positive_nsmul_mem_integerLattice haLI
      (affineSemigroupNatToInt d v) with ⟨N, hNpos, hNH⟩
  let s : Fin d → ℕ := u + (N - 1) • v
  have hsS : s ∈ S := S.add_mem huS (S.nsmul_mem hvS (N - 1))
  refine ⟨s, hsS, ?_⟩
  have hcast : affineSemigroupNatToInt d s =
      affineSemigroupNatToInt d u +
        (N - 1) • affineSemigroupNatToInt d v := by
    funext j
    simp [s, affineSemigroupNatToInt]
  have hzcalc :
      (affineSemigroupNatToInt d u - affineSemigroupNatToInt d v) -
          affineSemigroupNatToInt d s =
        -(N • affineSemigroupNatToInt d v) := by
    rw [hcast]
    have hN : N - 1 + 1 = N := Nat.sub_one_add_one_eq_of_pos hNpos
    have hNv : N • affineSemigroupNatToInt d v =
        (N - 1) • affineSemigroupNatToInt d v +
          affineSemigroupNatToInt d v := by
      nth_rewrite 1 [← hN]
      rw [add_nsmul, one_nsmul]
    rw [hNv]
    abel
  rw [hzcalc]
  exact Submodule.neg_mem _ hNH

/- accepted add_to_file helper 13 -/
lemma affineSemigroup_nat_sum_a_mem_integerLattice
    {d : ℕ} {a : Fin d → Fin d → ℕ} (n : Fin d → ℕ) :
    affineSemigroupNatToInt d (∑ i, n i • a i) ∈
      affineSemigroupIntegerLattice d a := by
  rw [affineSemigroupIntegerLattice]
  have hsum : affineSemigroupNatToInt d (∑ i, n i • a i) =
      ∑ i, n i • affineSemigroupNatToInt d (a i) := by
    funext j
    simp [affineSemigroupNatToInt]
  rw [hsum]
  exact Submodule.sum_mem _ (fun i hi =>
    (Submodule.span ℤ
      (Set.range (fun i : Fin d => affineSemigroupNatToInt d (a i)))).toAddSubmonoid.nsmul_mem
      (Submodule.subset_span ⟨i, rfl⟩) (n i))

lemma affineSemigroup_exists_apery_int_coords_of_G
    {d : ℕ} {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    {z : Fin d → ℤ} (hz : z ∈ affineSemigroupG d S) :
    ∃ w : Fin d → ℕ, w ∈ affineSemigroupApery d S a ∧
      ∃ k : Fin d → ℤ,
        z - affineSemigroupNatToInt d w =
          ∑ i, k i • affineSemigroupNatToInt d (a i) := by
  rcases affineSemigroup_exists_S_sub_mem_integerLattice haLI hz with
    ⟨s, hsS, hzsub⟩
  rcases affineSemigroup_exists_apery_reduction haLI hsS with
    ⟨w, n, hw, hsw⟩
  have hsdiff :
      affineSemigroupNatToInt d s - affineSemigroupNatToInt d w ∈
        affineSemigroupIntegerLattice d a := by
    rw [hsw]
    have hcast :
        affineSemigroupNatToInt d (w + ∑ i, n i • a i) -
            affineSemigroupNatToInt d w =
          affineSemigroupNatToInt d (∑ i, n i • a i) := by
      funext j
      simp [affineSemigroupNatToInt]
    rw [hcast]
    exact affineSemigroup_nat_sum_a_mem_integerLattice n
  have hzw : z - affineSemigroupNatToInt d w ∈
      affineSemigroupIntegerLattice d a := by
    have hsum := Submodule.add_mem _ hzsub hsdiff
    convert hsum using 1
    abel
  rw [affineSemigroupIntegerLattice,
    Submodule.mem_span_range_iff_exists_fun] at hzw
  rcases hzw with ⟨k, hk⟩
  exact ⟨w, hw, k, hk.symm⟩

/- accepted add_to_file helper 14 -/
lemma affineSemigroup_image_subset_G_inter_cone
    {d : ℕ}
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))) :
    affineSemigroupNatToInt d '' (S : Set (Fin d → ℕ)) ⊆
      affineSemigroupG d S ∩
        {z | affineSemigroupIntToReal d z ∈ affineSemigroupCone d a} := by
  rintro z ⟨s, hsS, rfl⟩
  constructor
  · refine ⟨s, hsS, 0, S.zero_mem, ?_⟩
    funext j
    simp [affineSemigroupNatToInt]
  · have hmem : affineSemigroupNatToReal d s ∈
        ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
          (S : Set (Fin d → ℕ))) := by
      exact ⟨s, hsS, rfl⟩
    have hhull : affineSemigroupNatToReal d s ∈ ConvexCone.hull ℝ
        ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
          (S : Set (Fin d → ℕ))) :=
      ConvexCone.subset_hull hmem
    have hreal : affineSemigroupIntToReal d (affineSemigroupNatToInt d s) =
        affineSemigroupNatToReal d s := by
      funext j
      simp [affineSemigroupIntToReal, affineSemigroupNatToInt,
        affineSemigroupNatToReal]
    change affineSemigroupIntToReal d (affineSemigroupNatToInt d s) ∈
      affineSemigroupCone d a
    rw [hreal]
    exact (hcone _).mp hhull

/- accepted add_to_file helper 15 -/
lemma affineSemigroup_condition4_implies_normal
    {d : ℕ} (hd : 1 ≤ d)
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haS : ∀ i, a i ∈ S)
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ)))
    (hcond4 : affineSemigroupCondition4 d S a) :
    affineSemigroupNormal d S a := by
  apply Set.Subset.antisymm (affineSemigroup_image_subset_G_inter_cone hcone)
  rintro z ⟨hzG, hzC⟩
  rcases affineSemigroup_exists_apery_int_coords_of_G haLI hzG with
    ⟨w, hwAp, k, hzwk⟩
  rcases hcond4 w hwAp with ⟨c, hc, hxw⟩
  rcases hzC with ⟨q, hq, hxz⟩
  have hHreal : affineSemigroupIntToReal d
        (z - affineSemigroupNatToInt d w) =
      ∑ i, (k i : ℝ) • (fun j : Fin d => (a i j : ℝ)) := by
    rw [hzwk]
    funext j
    simp [affineSemigroupIntToReal, affineSemigroupNatToInt]
  have hknonneg : ∀ i, 0 ≤ k i := by
    intro i
    have hqcoord := affineSemigroup_sum_coords
      (d := d) (hd := hd) (a := a) (haLI := haLI) hxz i
    have hwcoord := affineSemigroup_sum_coords
      (d := d) (hd := hd) (a := a) (haLI := haLI) hxw i
    have hkcoord := affineSemigroup_sum_coords
      (d := d) (hd := hd) (a := a) (haLI := haLI) hHreal i
    have hdiffcast : affineSemigroupIntToReal d
          (z - affineSemigroupNatToInt d w) =
        affineSemigroupIntToReal d z - affineSemigroupNatToReal d w := by
      funext j
      simp [affineSemigroupIntToReal, affineSemigroupNatToInt,
        affineSemigroupNatToReal, Int.cast_sub]
    have hqck : q i - c i = (k i : ℝ) := by
      calc
        q i - c i
            = ((affineSemigroupBasis d hd a haLI).repr
                (affineSemigroupIntToReal d z) i) -
              ((affineSemigroupBasis d hd a haLI).repr
                (affineSemigroupNatToReal d w) i) := by
                  rw [hqcoord, hwcoord]
        _ = ((affineSemigroupBasis d hd a haLI).repr
              (affineSemigroupIntToReal d z -
                affineSemigroupNatToReal d w) i) := by
              simp
        _ = ((affineSemigroupBasis d hd a haLI).repr
              (affineSemigroupIntToReal d
                (z - affineSemigroupNatToInt d w)) i) := by
              rw [hdiffcast]
        _ = (k i : ℝ) := hkcoord
    have hkgt : (-1 : ℝ) < (k i : ℝ) := by
      rw [← hqck]
      have hq0 := hq i
      have hc1 := (hc i).2
      linarith
    have hkgtint : -1 < k i := by
      exact_mod_cast hkgt
    omega
  let n : Fin d → ℕ := fun i => Int.toNat (k i)
  have hnk : ∀ i, ((n i : ℤ) = k i) := by
    intro i
    exact Int.toNat_of_nonneg (hknonneg i)
  have hsumk : (∑ i, k i • affineSemigroupNatToInt d (a i)) =
      affineSemigroupNatToInt d (∑ i, n i • a i) := by
    funext j
    simp [n, affineSemigroupNatToInt, hnk]
  have hzeq : z =
      affineSemigroupNatToInt d (w + ∑ i, n i • a i) := by
    have hz1 : z = affineSemigroupNatToInt d w +
        ∑ i, k i • affineSemigroupNatToInt d (a i) := by
      calc
        z = (z - affineSemigroupNatToInt d w) +
            affineSemigroupNatToInt d w := by abel
        _ = (∑ i, k i • affineSemigroupNatToInt d (a i)) +
            affineSemigroupNatToInt d w := by rw [hzwk]
        _ = affineSemigroupNatToInt d w +
            ∑ i, k i • affineSemigroupNatToInt d (a i) := by abel
    rw [hz1, hsumk]
    funext j
    simp [affineSemigroupNatToInt]
  have hsumS : (∑ i, n i • a i) ∈ S := by
    exact S.sum_mem (fun i hi => S.nsmul_mem (haS i) (n i))
  have htS : w + ∑ i, n i • a i ∈ S :=
    S.add_mem hwAp.1 hsumS
  exact ⟨w + ∑ i, n i • a i, htS, hzeq.symm⟩

/- accepted add_to_file helper 16 -/
lemma affineSemigroup_eq_add_sum_a_of_int_sub
    {d : ℕ} {a : Fin d → Fin d → ℕ}
    {w₁ w₂ : Fin d → ℕ} {k : Fin d → ℤ}
    (hk : ∀ i, 0 ≤ k i)
    (h : affineSemigroupNatToInt d w₂ - affineSemigroupNatToInt d w₁ =
      ∑ i, k i • affineSemigroupNatToInt d (a i)) :
    w₂ = w₁ + ∑ i, Int.toNat (k i) • a i := by
  let n : Fin d → ℕ := fun i => Int.toNat (k i)
  have hnk : ∀ i, ((n i : ℤ) = k i) := by
    intro i
    exact Int.toNat_of_nonneg (hk i)
  have hsumk : (∑ i, k i • affineSemigroupNatToInt d (a i)) =
      affineSemigroupNatToInt d (∑ i, n i • a i) := by
    funext j
    simp [n, affineSemigroupNatToInt, hnk]
  have hzeq : affineSemigroupNatToInt d w₂ =
      affineSemigroupNatToInt d (w₁ + ∑ i, n i • a i) := by
    have hz1 : affineSemigroupNatToInt d w₂ =
        affineSemigroupNatToInt d w₁ +
          ∑ i, k i • affineSemigroupNatToInt d (a i) := by
      calc
        affineSemigroupNatToInt d w₂ =
            (affineSemigroupNatToInt d w₂ -
              affineSemigroupNatToInt d w₁) +
              affineSemigroupNatToInt d w₁ := by abel
        _ = (∑ i, k i • affineSemigroupNatToInt d (a i)) +
              affineSemigroupNatToInt d w₁ := by rw [h]
        _ = affineSemigroupNatToInt d w₁ +
              ∑ i, k i • affineSemigroupNatToInt d (a i) := by abel
    rw [hz1, hsumk]
    funext j
    simp [affineSemigroupNatToInt]
  funext j
  apply Nat.cast_injective (R := ℤ)
  change (w₂ j : ℤ) = ((w₁ + ∑ i, n i • a i) j : ℤ)
  simpa [affineSemigroupNatToInt] using congrFun hzeq j

/- accepted add_to_file helper 17 -/
lemma affineSemigroup_sum_nat_smul_eq_add_a
    {d : ℕ} {S : AddSubmonoid (Fin d → ℕ)}
    {a : Fin d → Fin d → ℕ}
    (haS : ∀ i, a i ∈ S) {n : Fin d → ℕ}
    {i : Fin d} (hi : 0 < n i) :
    ∃ t : Fin d → ℕ, t ∈ S ∧
      ∑ k, n k • a k = t + a i := by
  let m : Fin d → ℕ := fun k => if k = i then n k - 1 else n k
  refine ⟨∑ k, m k • a k, ?_, ?_⟩
  · exact S.sum_mem (fun k hk => S.nsmul_mem (haS k) (m k))
  · have hn : n = fun k => m k + (if k = i then 1 else 0) := by
      funext k
      by_cases hk : k = i
      · simp [m, hk, Nat.sub_add_cancel hi]
      · simp [m, hk]
    calc
      ∑ k, n k • a k
          = ∑ k, (m k + (if k = i then 1 else 0)) • a k := by rw [hn]
      _ = ∑ k, m k • a k + ∑ k, (if k = i then (1 : ℕ) else 0) • a k := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro k hk
          simp [add_smul]
      _ = ∑ k, m k • a k + a i := by simp

/- accepted add_to_file helper 18 -/
lemma affineSemigroup_apery_fiber_finite
    {d : ℕ} (hd : 1 ≤ d)
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haS : ∀ i, a i ∈ S)
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ)))
    (Q : (Fin d → ℤ) ⧸ affineSemigroupIntegerLattice d a) :
    {w : Fin d → ℕ | w ∈ affineSemigroupApery d S a ∧
      Submodule.Quotient.mk (p := affineSemigroupIntegerLattice d a)
        (affineSemigroupNatToInt d w) = Q}.Finite := by
  let F : Set (Fin d → ℕ) :=
    {w | w ∈ affineSemigroupApery d S a ∧
      Submodule.Quotient.mk (p := affineSemigroupIntegerLattice d a)
        (affineSemigroupNatToInt d w) = Q}
  change F.Finite
  obtain ⟨z₀, hz₀⟩ := Submodule.Quotient.mk_surjective
    (p := affineSemigroupIntegerLattice d a) Q
  have hkexists : ∀ w : F, ∃ k : Fin d → ℤ,
      affineSemigroupNatToInt d w - z₀ =
        ∑ i, k i • affineSemigroupNatToInt d (a i) := by
    intro w
    have hmk :
        Submodule.Quotient.mk (p := affineSemigroupIntegerLattice d a)
          (affineSemigroupNatToInt d w) =
        Submodule.Quotient.mk (p := affineSemigroupIntegerLattice d a) z₀ := by
      rw [w.2.2, hz₀]
    have hmem : affineSemigroupNatToInt d w - z₀ ∈
        affineSemigroupIntegerLattice d a :=
      (Submodule.Quotient.eq (affineSemigroupIntegerLattice d a)).mp hmk
    rw [affineSemigroupIntegerLattice,
      Submodule.mem_span_range_iff_exists_fun] at hmem
    rcases hmem with ⟨k, hk⟩
    exact ⟨k, hk.symm⟩
  let kfun : F → (Fin d → ℤ) := fun w => Classical.choose (hkexists w)
  have hkfun : ∀ w : F,
      affineSemigroupNatToInt d w - z₀ =
        ∑ i, kfun w i • affineSemigroupNatToInt d (a i) :=
    fun w => Classical.choose_spec (hkexists w)
  let b := affineSemigroupBasis d hd a haLI
  let q₀ : Fin d → ℝ := fun i =>
    b.repr (affineSemigroupIntToReal d z₀) i
  have hcoord : ∀ (w : F) (i : Fin d),
      b.repr (affineSemigroupIntToReal d (affineSemigroupNatToInt d w)) i =
        q₀ i + (kfun w i : ℝ) := by
    intro w i
    have hHreal : affineSemigroupIntToReal d
          (affineSemigroupNatToInt d w - z₀) =
        ∑ j, (kfun w j : ℝ) • (fun l : Fin d => (a j l : ℝ)) := by
      rw [hkfun w]
      funext j
      simp [affineSemigroupIntToReal, affineSemigroupNatToInt]
    have hkcoord := affineSemigroup_sum_coords
      (d := d) (hd := hd) (a := a) (haLI := haLI) hHreal i
    have hdiffcast : affineSemigroupIntToReal d
          (affineSemigroupNatToInt d w - z₀) =
        affineSemigroupIntToReal d (affineSemigroupNatToInt d w) -
          affineSemigroupIntToReal d z₀ := by
      funext j
      simp [affineSemigroupIntToReal, affineSemigroupNatToInt, Int.cast_sub]
    calc
      b.repr (affineSemigroupIntToReal d (affineSemigroupNatToInt d w)) i
          = (b.repr (affineSemigroupIntToReal d
              (affineSemigroupNatToInt d w - z₀)) i) +
            b.repr (affineSemigroupIntToReal d z₀) i := by
              rw [hdiffcast]
              simp
      _ = q₀ i + (kfun w i : ℝ) := by
              rw [hkcoord]
              simp [q₀, add_comm]
  have hlower : ∀ (w : F) (i : Fin d),
      Int.ceil (-(q₀ i)) ≤ kfun w i := by
    intro w i
    have hqnonneg := affineSemigroup_S_coord_nonneg
      (d := d) (hd := hd) (S := S) (a := a) (haLI := haLI) hcone
      w.2.1.1 i
    have hcast :
        affineSemigroupIntToReal d (affineSemigroupNatToInt d w) =
          affineSemigroupNatToReal d w := by
      funext j
      simp [affineSemigroupIntToReal, affineSemigroupNatToInt,
        affineSemigroupNatToReal]
    have hq : q₀ i + (kfun w i : ℝ) ≥ 0 := by
      rw [← hcoord w i, hcast]
      exact hqnonneg
    apply (Int.ceil_le).mpr
    linarith
  let mK : Fin d → ℤ := fun i => Int.ceil (-(q₀ i))
  let nfun : F → (Fin d → ℕ) := fun w i =>
    Int.toNat (kfun w i - mK i)
  have hnge : ∀ (w : F) (i : Fin d), 0 ≤ kfun w i - mK i := by
    intro w i
    exact sub_nonneg.mpr (hlower w i)
  have hnfun_cast : ∀ (w : F) (i : Fin d),
      ((nfun w i : ℤ) = kfun w i - mK i) := by
    intro w i
    exact Int.toNat_of_nonneg (hnge w i)
  have hninj : Function.Injective nfun := by
    intro x y hxy
    have hksame : kfun x = kfun y := by
      funext i
      have hi := congrFun hxy i
      have hx := hnfun_cast x i
      have hy := hnfun_cast y i
      have : ((nfun x i : ℤ) = (nfun y i : ℤ)) := by rw [hi]
      omega
    apply Subtype.ext
    have hint : affineSemigroupNatToInt d x = affineSemigroupNatToInt d y := by
      have hx := hkfun x
      have hy := hkfun y
      rw [hksame] at hx
      calc
        affineSemigroupNatToInt d x =
            (affineSemigroupNatToInt d x - z₀) + z₀ := by abel
        _ = (affineSemigroupNatToInt d y - z₀) + z₀ := by rw [hx, hy]
        _ = affineSemigroupNatToInt d y := by abel
    funext j
    have hj := congrFun hint j
    change ((x : Fin d → ℕ) j : ℤ) = ((y : Fin d → ℕ) j : ℤ) at hj
    exact Nat.cast_injective (R := ℤ) hj
  have hanti : IsAntichain (· ≤ ·) (Set.range nfun) := by
    intro x hx y hy hne hxy
    rcases hx with ⟨X, rfl⟩
    rcases hy with ⟨Y, rfl⟩
    have hkle : ∀ i, kfun X i ≤ kfun Y i := by
      intro i
      have hi := hxy i
      have hX := hnfun_cast X i
      have hY := hnfun_cast Y i
      have hcast : ((nfun X i : ℤ) ≤ (nfun Y i : ℤ)) := by exact_mod_cast hi
      omega
    by_cases hksame : kfun X = kfun Y
    · apply hne
      funext i
      have hX := hnfun_cast X i
      have hY := hnfun_cast Y i
      have hk : kfun X i - mK i = kfun Y i - mK i := by rw [hksame]
      have hcast :
          ((nfun X i : ℤ) = (nfun Y i : ℤ)) := by omega
      exact Nat.cast_injective (R := ℤ) hcast
    · have hex : ∃ i, kfun X i ≠ kfun Y i := by
        by_contra h
        push Not at h
        apply hksame
        funext i
        exact h i
      rcases hex with ⟨i, hi⟩
      have hlt : kfun X i < kfun Y i := lt_of_le_of_ne (hkle i) hi
      let kd : Fin d → ℤ := fun j => kfun Y j - kfun X j
      have hkd : ∀ j, 0 ≤ kd j := by
        intro j
        exact sub_nonneg.mpr (hkle j)
      have hdiff :
          affineSemigroupNatToInt d Y - affineSemigroupNatToInt d X =
            ∑ j, kd j • affineSemigroupNatToInt d (a j) := by
        have hXH := hkfun X
        have hYH := hkfun Y
        calc
          affineSemigroupNatToInt d Y - affineSemigroupNatToInt d X
              = (affineSemigroupNatToInt d Y - z₀) -
                (affineSemigroupNatToInt d X - z₀) := by abel
          _ = (∑ j, kfun Y j • affineSemigroupNatToInt d (a j)) -
              (∑ j, kfun X j • affineSemigroupNatToInt d (a j)) := by
                rw [hYH, hXH]
          _ = ∑ j, kd j • affineSemigroupNatToInt d (a j) := by
                simp [kd, Finset.sum_sub_distrib, sub_smul]
      have hnat := affineSemigroup_eq_add_sum_a_of_int_sub hkd hdiff
      let nd : Fin d → ℕ := fun j => Int.toNat (kd j)
      have hndi : 0 < nd i := by
        have hpos : 0 < kd i := sub_pos.mpr hlt
        change 0 < Int.toNat (kd i)
        have hcast := Int.toNat_of_nonneg (le_of_lt hpos)
        omega
      rcases affineSemigroup_sum_nat_smul_eq_add_a haS hndi with ⟨t, htS, hsumt⟩
      have hpre : (Y : Fin d → ℕ) = ((X : Fin d → ℕ) + t) + a i := by
        calc
          (Y : Fin d → ℕ) = (X : Fin d → ℕ) + ∑ j, nd j • a j := hnat
          _ = (X : Fin d → ℕ) + (t + a i) := by rw [hsumt]
          _ = ((X : Fin d → ℕ) + t) + a i := by abel
      exact Y.property.1.2 i ⟨X + t, S.add_mem X.property.1.1 htS, hpre⟩
  have hPWO : (Set.range nfun).PartiallyWellOrderedOn (· ≤ ·) :=
    Set.partiallyWellOrderedOn_of_wellQuasiOrdered wellQuasiOrdered_le
      (Set.range nfun)
  have hrange : (Set.range nfun).Finite :=
    hanti.finite_of_partiallyWellOrderedOn hPWO
  have hfinite : Finite F := (Set.finite_range_iff hninj).mp hrange
  exact Set.finite_coe_iff.mp hfinite

/- accepted add_to_file helper 19 -/
lemma affineSemigroup_apery_finite
    {d : ℕ} (hd : 1 ≤ d)
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haS : ∀ i, a i ∈ S)
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))) :
    (affineSemigroupApery d S a).Finite := by
  haveI : Finite ((Fin d → ℤ) ⧸ affineSemigroupIntegerLattice d a) :=
    affineSemigroup_finite_quotient_integerLattice haLI
  let F : ((Fin d → ℤ) ⧸ affineSemigroupIntegerLattice d a) →
      Set (Fin d → ℕ) :=
    fun Q => {w | w ∈ affineSemigroupApery d S a ∧
      Submodule.Quotient.mk (p := affineSemigroupIntegerLattice d a)
        (affineSemigroupNatToInt d w) = Q}
  have hAp : affineSemigroupApery d S a = ⋃ Q, F Q := by
    ext w
    constructor
    · intro hw
      refine Set.mem_iUnion.mpr ?_
      exact ⟨_, hw, rfl⟩
    · intro hw
      rcases Set.mem_iUnion.mp hw with ⟨Q, hwQ⟩
      exact hwQ.1
  rw [hAp]
  exact Set.finite_iUnion (fun Q =>
    affineSemigroup_apery_fiber_finite hd haS haLI hcone Q)

/- accepted add_to_file helper 20 -/
lemma affineSemigroup_exists_maximal_apery_above
    {d : ℕ} (hd : 1 ≤ d)
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haS : ∀ i, a i ∈ S)
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ)))
    {w : Fin d → ℕ} (hw : w ∈ affineSemigroupApery d S a) :
    ∃ m : Fin d → ℕ,
      affineSemigroupLeS d S w m ∧
        affineSemigroupMaximalApery d S a m := by
  letI : Preorder (Fin d → ℕ) :=
    { le := affineSemigroupLeS d S
      lt := fun u v => affineSemigroupLeS d S u v ∧
        ¬affineSemigroupLeS d S v u
      le_refl := by
        intro u
        exact ⟨0, S.zero_mem, by simp⟩
      le_trans := by
        intro u v t huv hvt
        rcases huv with ⟨s, hsS, hv⟩
        rcases hvt with ⟨r, hrS, ht⟩
        refine ⟨s + r, S.add_mem hsS hrS, ?_⟩
        rw [ht, hv]
        abel
      lt_iff_le_not_ge := by
        intro u v
        rfl }
  have hfinite := affineSemigroup_apery_finite hd haS haLI hcone
  rcases hfinite.exists_le_maximal hw with ⟨m, hwm, hm⟩
  refine ⟨m, hwm, hm.1, ?_⟩
  intro x hx hmx
  exact hm.2 hx hmx

/- accepted add_to_file helper 21 -/
lemma affineSemigroup_condition3_implies_condition4
    {d : ℕ} (hd : 1 ≤ d)
    {S : AddSubmonoid (Fin d → ℕ)} {a : Fin d → Fin d → ℕ}
    (haS : ∀ i, a i ∈ S)
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ)))
    (hcond3 : affineSemigroupCondition3 d S a) :
    affineSemigroupCondition4 d S a := by
  intro w hw
  rcases affineSemigroup_exists_maximal_apery_above
    (d := d) (hd := hd) (S := S) (a := a) (haLI := haLI)
    haS hcone hw with ⟨m, hwm, hmax⟩
  let f : Fin d → ℤ := affineSemigroupNatToInt d m -
    ∑ i, affineSemigroupNatToInt d (a i)
  have hfQF : f ∈ affineSemigroupQF d S a := by
    exact ⟨m, hmax, rfl⟩
  rcases hcond3 f hfQF with ⟨r, hr, hxr⟩
  let b := affineSemigroupBasis d hd a haLI
  have hm_lt_one : ∀ i,
      b.repr (affineSemigroupNatToReal d m) i < 1 := by
    intro i
    have hnegreal : affineSemigroupIntToReal d (-f) =
        (∑ k, (1 : ℝ) • (fun j : Fin d => (a k j : ℝ))) -
          affineSemigroupNatToReal d m := by
      funext j
      simp [f, affineSemigroupIntToReal, affineSemigroupNatToInt,
        affineSemigroupNatToReal]
    have hsumrepr :
        (∑ c, (b.repr (fun j : Fin d => (a c j : ℝ))) i) = 1 := by
      calc
        (∑ c, (b.repr (fun j : Fin d => (a c j : ℝ))) i)
            = ∑ c, (b.repr (b c)) i := by
              apply Finset.sum_congr rfl
              intro c hc
              rw [affineSemigroupBasis_apply d hd a haLI]
        _ = 1 := by simp
    have hcoordneg :
        b.repr (affineSemigroupIntToReal d (-f)) i =
          1 - b.repr (affineSemigroupNatToReal d m) i := by
      rw [hnegreal]
      simp [hsumrepr]
    have hrcoord := affineSemigroup_sum_coords
      (d := d) (hd := hd) (a := a) (haLI := haLI) hxr i
    rw [hcoordneg] at hrcoord
    have hri := hr i
    linarith
  have hw_nonneg : ∀ i,
      0 ≤ b.repr (affineSemigroupNatToReal d w) i := by
    intro i
    exact affineSemigroup_S_coord_nonneg
      (d := d) (hd := hd) (S := S) (a := a) (haLI := haLI) hcone hw.1 i
  have hw_le_m : ∀ i,
      b.repr (affineSemigroupNatToReal d w) i ≤
        b.repr (affineSemigroupNatToReal d m) i := by
    intro i
    rcases hwm with ⟨s, hsS, hm⟩
    have hs_nonneg := affineSemigroup_S_coord_nonneg
      (d := d) (hd := hd) (S := S) (a := a) (haLI := haLI) hcone hsS i
    have hmreal : affineSemigroupNatToReal d m =
        affineSemigroupNatToReal d w + affineSemigroupNatToReal d s := by
      rw [hm]
      funext j
      simp [affineSemigroupNatToReal]
    have hcoord := congrArg (fun x : Fin d → ℝ =>
        b.repr x i) hmreal
    simp at hcoord
    rw [hcoord]
    linarith
  let q : Fin d → ℝ := fun i =>
    b.repr (affineSemigroupNatToReal d w) i
  refine ⟨q, ?_, ?_⟩
  · intro i
    exact ⟨hw_nonneg i, lt_of_le_of_lt (hw_le_m i) (hm_lt_one i)⟩
  · calc
      affineSemigroupNatToReal d w =
          ∑ i, q i • b i := by
            symm
            exact b.sum_repr (affineSemigroupNatToReal d w)
      _ = ∑ i, q i • (fun j : Fin d => (a i j : ℝ)) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [affineSemigroupBasis_apply d hd a haLI]

/- verified submission -/
theorem affineSemigroup_normal_equiv
    (d : ℕ) (hd : 1 ≤ d)
    (S : AddSubmonoid (Fin d → ℕ)) (hSfg : S.FG)
    (a : Fin d → Fin d → ℕ)
    (haS : ∀ i, a i ∈ S)
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ)))
    (hminray : ∀ (i : Fin d) (u : Fin d → ℕ),
      u ∈ S → u ≠ 0 →
      (∃ r : ℝ, 0 ≤ r ∧
        (fun j : Fin d => (u j : ℝ)) =
          r • (fun j : Fin d => (a i j : ℝ))) →
      ∀ j, a i j ≤ u j) :
    let natToInt : (Fin d → ℕ) → (Fin d → ℤ) :=
      fun u j => (u j : ℤ)
    let natToReal : (Fin d → ℕ) → (Fin d → ℝ) :=
      fun u j => (u j : ℝ)
    let intToReal : (Fin d → ℤ) → (Fin d → ℝ) :=
      fun u j => (u j : ℝ)
    let C : Set (Fin d → ℝ) :=
      {x | ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
        x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))}
    let relintC : Set (Fin d → ℝ) :=
      {x | ∃ c : Fin d → ℝ, (∀ i, 0 < c i) ∧
        x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))}
    let fundamentalParallelepiped : Set (Fin d → ℝ) :=
      {x | ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i ∧ c i < 1) ∧
        x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))}
    let apery : Set (Fin d → ℕ) :=
      {w | w ∈ S ∧ ∀ i, ¬∃ s : Fin d → ℕ, s ∈ S ∧ w = s + a i}
    let leS : (Fin d → ℕ) → (Fin d → ℕ) → Prop :=
      fun u v => ∃ s : Fin d → ℕ, s ∈ S ∧ v = u + s
    let maximalApery : (Fin d → ℕ) → Prop :=
      fun m => m ∈ apery ∧
        ∀ w, w ∈ apery → leS m w → leS w m
    let QF : Set (Fin d → ℤ) :=
      {f | ∃ m, maximalApery m ∧
        f = natToInt m - ∑ i, natToInt (a i)}
    let G : Set (Fin d → ℤ) :=
      {z | ∃ u : Fin d → ℕ, u ∈ S ∧
        ∃ v : Fin d → ℕ, v ∈ S ∧ z = natToInt u - natToInt v}
    let normal : Prop :=
      natToInt '' (S : Set (Fin d → ℕ)) =
        G ∩ {z | intToReal z ∈ C}
    let condition2 : Prop :=
      ∀ f, f ∈ QF →
        -f ∈ natToInt '' (S : Set (Fin d → ℕ)) ∧
          intToReal (-f) ∈ relintC
    let condition3 : Prop :=
      ∀ f, f ∈ QF → intToReal (-f) ∈ relintC
    let condition4 : Prop :=
      ∀ w, w ∈ apery → natToReal w ∈ fundamentalParallelepiped
    (normal ↔ condition2) ∧ (normal ↔ condition3) ∧ (normal ↔ condition4) := by
  change (affineSemigroupNormal d S a ↔ affineSemigroupCondition2 d S a) ∧
    (affineSemigroupNormal d S a ↔ affineSemigroupCondition3 d S a) ∧
    (affineSemigroupNormal d S a ↔ affineSemigroupCondition4 d S a)
  have h34 : affineSemigroupCondition3 d S a →
      affineSemigroupCondition4 d S a := by
    intro h3
    exact affineSemigroup_condition3_implies_condition4
      (d := d) (hd := hd) (S := S) (a := a) (haLI := haLI)
      haS hcone h3
  have h4N : affineSemigroupCondition4 d S a →
      affineSemigroupNormal d S a := by
    intro h4
    exact affineSemigroup_condition4_implies_normal
      (d := d) (hd := hd) (S := S) (a := a)
      haS haLI hcone h4
  have hN2 : affineSemigroupNormal d S a →
      affineSemigroupCondition2 d S a := by
    intro hN
    exact affineSemigroup_normal_implies_condition2
      (d := d) (hd := hd) (S := S) (a := a) (haLI := haLI)
      haS hcone hN
  constructor
  · constructor
    · exact hN2
    · intro h2
      exact h4N (h34 (fun f hf => (h2 f hf).2))
  · constructor
    · constructor
      · intro hN f hf
        exact (hN2 hN f hf).2
      · intro h3
        exact h4N (h34 h3)
    · constructor
      · intro hN w hw
        exact affineSemigroup_normal_implies_condition4
          (d := d) (hd := hd) (S := S) (a := a) (haLI := haLI)
          haS hcone hN hw
      · exact h4N


#check_dependency_graph "affineSemigroup_normal_equiv" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let natToInt := fun u j => ↑(u j); let natToReal := fun u j => ↑(u j); let intToReal := fun u j => ↑(u j); let C := {x | ∃ c, (∀ (i : Fin d), 0 ≤ c i) ∧ x = ∑ i, c i • fun j => ↑(a i j)}; let relintC := {x | ∃ c, (∀ (i : Fin d), 0 < c i) ∧ x = ∑ i, c i • fun j => ↑(a i j)}; let fundamentalParallelepiped := {x | ∃ c, (∀ (i : Fin d), 0 ≤ c i ∧ c i < 1) ∧ x = ∑ i, c i • fun j => ↑(a i j)}; let apery := {w | w ∈ S ∧ ∀ (i : Fin d), ¬∃ s ∈ S, w = s + a i}; let leS := fun u v => ∃ s ∈ S, v = u + s; let maximalApery := fun m => m ∈ apery ∧ ∀ w ∈ apery, leS m w → leS w m; let QF := {f | ∃ m, maximalApery m ∧ f = natToInt m - ∑ i, natToInt (a i)}; let G := {z | ∃ u ∈ S, ∃ v ∈ S, z = natToInt u - natToInt v}; let normal := natToInt '' ↑S = G ∩ {z | intToReal z ∈ C}; let condition2 := ∀ f ∈ QF, -f ∈ natToInt '' ↑S ∧ intToReal (-f) ∈ relintC; let condition3 := ∀ f ∈ QF, intToReal (-f) ∈ relintC; let condition4 := ∀ w ∈ apery, natToReal w ∈ fundamentalParallelepiped; (normal ↔ condition2) ∧ (normal ↔ condition3) ∧ (normal ↔ condition4)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hd\",\"statement\":\"1 ≤ d\"},{\"name\":\"haS\",\"statement\":\"∀ (i : Fin d), a i ∈ S\"},{\"name\":\"haLI\",\"statement\":\"LinearIndependent ℝ fun i j => ↑(a i j)\"},{\"name\":\"hcone\",\"statement\":\"∀ (x : Fin d → ℝ), x ∈ ConvexCone.hull ℝ ((fun u j => ↑(u j)) '' ↑S) ↔ ∃ c, (∀ (i : Fin d), 0 ≤ c i) ∧ x = ∑ i, c i • fun j => ↑(a i j)\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0130_affinesemigroup_normal_equiv\",\"reconstructedProofSha256\":\"cb7233a68a6118393aa37b189778a13ecbed506886a57b9eae26129aa1a45739\",\"selectedEdgeCount\":1,\"theoremName\":\"affineSemigroup_normal_equiv\",\"topologySha256\":\"b6e0b51344ee410e1677d05af1a57204e4ffb055c0a46ace81c966c822d992e2\"}"
