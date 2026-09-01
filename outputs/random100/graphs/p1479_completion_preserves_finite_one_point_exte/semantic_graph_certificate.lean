import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1479_completion_preserves_finite_one_point_exte
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 39b1009545f4bff0a670c51396fb742561c861c05ae85f94cd168a4c403d40dc
-- reconstructed_proof_sha256: f502da8ed39d6421ae6092cb084ca49db2da3d85286746dc885524a997d1bd54
-- selected_edge_count: 2

/- accepted add_to_file helper 1 -/
lemma completion_diam_eq
    (A : Type*) [MetricSpace A] :
    Metric.diam (Set.univ : Set (UniformSpace.Completion A)) =
      Metric.diam (Set.univ : Set A) := by
  have hclosure : closure (Set.range (UniformSpace.Completion.coe' : A → UniformSpace.Completion A)) = Set.univ :=
    UniformSpace.Completion.denseRange_coe.closure_range
  calc
    Metric.diam (Set.univ : Set (UniformSpace.Completion A))
        = Metric.diam (closure (Set.range (UniformSpace.Completion.coe' : A → UniformSpace.Completion A))) := by
          rw [hclosure]
    _ = Metric.diam (Set.range (UniformSpace.Completion.coe' : A → UniformSpace.Completion A)) :=
          Metric.diam_closure _
    _ = Metric.diam (Set.univ : Set A) :=
          UniformSpace.Completion.coe_isometry.diam_range

lemma dist_le_one_of_diam_one
    {X : Type*} [PseudoMetricSpace X]
    (h : Metric.diam (Set.univ : Set X) = 1) (x y : X) :
    dist x y ≤ 1 := by
  have hed : Metric.ediam (Set.univ : Set X) ≠ ⊤ := by
    intro he
    simp [Metric.diam, he] at h
  exact (Metric.dist_le_diam_of_mem' hed (Set.mem_univ x) (Set.mem_univ y)).trans_eq h

lemma exists_extension_on_range
    {A : Type*} [MetricSpace A]
    (hext : ∀ (F : Set A), F.Finite →
      ∀ f : F → Set.Icc (0 : ℝ) 1,
        (∀ x y : F,
          |(f x : ℝ) - (f y : ℝ)| ≤ dist (x : A) (y : A) ∧
            dist (x : A) (y : A) ≤ (f x : ℝ) + (f y : ℝ)) →
        ∃ z : A, ∀ x : F, dist z (x : A) = (f x : ℝ))
    {ι : Type*} [Finite ι] {a : ι → A} (ha : Function.Injective a)
    (r : ι → Set.Icc (0 : ℝ) 1)
    (hcompat : ∀ i j : ι,
      |(r i : ℝ) - (r j : ℝ)| ≤ dist (a i) (a j) ∧
        dist (a i) (a j) ≤ (r i : ℝ) + (r j : ℝ)) :
    ∃ z : A, ∀ i : ι, dist z (a i) = (r i : ℝ) := by
  classical
  let idx : Set.range a → ι := fun y => Classical.choose y.2
  let rr : Set.range a → Set.Icc (0 : ℝ) 1 := fun y => r (idx y)
  have hidx : ∀ y : Set.range a, a (idx y) = y.1 := by
    intro y
    exact Classical.choose_spec y.2
  obtain ⟨z, hz⟩ := hext (Set.range a) (Set.finite_range a) rr (by
    intro x y
    simpa [rr, idx, hidx x, hidx y] using hcompat (idx x) (idx y))
  refine ⟨z, fun i => ?_⟩
  have hmem : a i ∈ Set.range a := Set.mem_range_self i
  have hz' := hz ⟨a i, hmem⟩
  have hid : idx ⟨a i, hmem⟩ = i := ha (hidx ⟨a i, hmem⟩)
  simpa [rr, hid] using hz'

/- accepted add_to_file helper 2 -/
lemma exists_isometric_approx_fin
    {A : Type*} [MetricSpace A]
    (hext : ∀ (F : Set A), F.Finite →
      ∀ f : F → Set.Icc (0 : ℝ) 1,
        (∀ x y : F,
          |(f x : ℝ) - (f y : ℝ)| ≤ dist (x : A) (y : A) ∧
            dist (x : A) (y : A) ≤ (f x : ℝ) + (f y : ℝ)) →
        ∃ z : A, ∀ x : F, dist z (x : A) = (f x : ℝ))
    (hdiamX : Metric.diam (Set.univ : Set (UniformSpace.Completion A)) = 1) :
    ∀ (n : ℕ) (x : Fin n → UniformSpace.Completion A),
      Function.Injective x → ∀ {ε : ℝ}, 0 < ε →
        ∃ a : Fin n → A,
          (∀ i, dist ((a i : UniformSpace.Completion A)) (x i) < ε) ∧
          (∀ i j, dist (a i) (a j) = dist (x i) (x j)) := by
  intro n
  induction n with
  | zero =>
      intro x hx ε hε
      refine ⟨fun i => i.elim0, ?_, ?_⟩
      · intro i; exact i.elim0
      · intro i; exact i.elim0
  | succ n ih =>
      intro x hx ε hε
      by_cases hn : n = 0
      · subst n
        obtain ⟨b, hb⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt
          (x 0) hε
        refine ⟨fun _ => b, ?_, ?_⟩
        · intro i
          have hi : i = 0 := by
            ext
            omega
          subst i
          rw [dist_comm ((b : UniformSpace.Completion A)) (x 0)]
          exact hb
        · intro i j
          have hi : i = 0 := by
            ext
            omega
          have hj : j = 0 := by
            ext
            omega
          subst i
          subst j
          simp
      · haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
        let D : Fin n → ℝ := fun j => dist (x j.castSucc) (x (Fin.last n))
        obtain ⟨j0, -, hmin⟩ := Finset.exists_min_image Finset.univ D Finset.univ_nonempty
        let m : ℝ := D j0
        have hmpos : 0 < m := by
          dsimp [m, D]
          rw [dist_pos]
          intro hxy
          exact Fin.castSucc_ne_last j0 (hx hxy)
        have hmle : ∀ j : Fin n, m ≤ D j := fun j => hmin j (Finset.mem_univ j)
        have hmle_one : m ≤ 1 := by
          dsimp [m, D]
          exact dist_le_one_of_diam_one hdiamX (x j0.castSucc) (x (Fin.last n))
        let ρ : ℝ := min (m / 2) (ε / 2)
        have hρpos : 0 < ρ := by positivity
        have hρle_mhalf : ρ ≤ m / 2 := min_le_left _ _
        have hρle_ehalf : ρ ≤ ε / 2 := min_le_right _ _
        have hρle_one : ρ ≤ 1 := by linarith
        let c : ℝ := ρ / 4
        have hcpos : 0 < c := by positivity
        have hxres : Function.Injective (fun j : Fin n => x j.castSucc) := by
          intro i j h
          exact Fin.castSucc_injective n (hx h)
        obtain ⟨aold, haold_approx, haold_dist⟩ := ih
          (fun j : Fin n => x j.castSucc) hxres hcpos
        obtain ⟨b, hb⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt
          (x (Fin.last n)) hcpos
        have haold_inj : Function.Injective aold := by
          intro i j h
          have hd : dist (x i.castSucc) (x j.castSucc) = 0 := by
            rw [← haold_dist i j, h, dist_self]
          have hxij : x i.castSucc = x j.castSucc := dist_eq_zero.mp hd
          exact Fin.castSucc_injective n (hx hxij)
        have herr : ∀ j : Fin n,
            |dist (aold j) b - D j| < ρ / 2 := by
          intro j
          have hupper : dist (aold j) b < D j + ρ / 2 := by
            have h1 : dist ((aold j : UniformSpace.Completion A)) ((b : UniformSpace.Completion A)) ≤
                dist ((aold j : UniformSpace.Completion A)) (x j.castSucc) +
                  dist (x j.castSucc) ((b : UniformSpace.Completion A)) :=
              dist_triangle _ _ _
            have h2 : dist (x j.castSucc) ((b : UniformSpace.Completion A)) ≤
                dist (x j.castSucc) (x (Fin.last n)) +
                  dist (x (Fin.last n)) ((b : UniformSpace.Completion A)) :=
              dist_triangle _ _ _
            have hA := haold_approx j
            rw [UniformSpace.Completion.dist_eq (aold j) b] at h1
            dsimp [D, c] at *
            linarith
          have hlower : D j < dist (aold j) b + ρ / 2 := by
            have h1 : dist (x j.castSucc) (x (Fin.last n)) ≤
                dist (x j.castSucc) ((aold j : UniformSpace.Completion A)) +
                  dist ((aold j : UniformSpace.Completion A)) (x (Fin.last n)) :=
              dist_triangle _ _ _
            have h2 : dist ((aold j : UniformSpace.Completion A)) (x (Fin.last n)) ≤
                dist ((aold j : UniformSpace.Completion A)) ((b : UniformSpace.Completion A)) +
                  dist ((b : UniformSpace.Completion A)) (x (Fin.last n)) :=
              dist_triangle _ _ _
            have hA := haold_approx j
            have hA' : dist (x j.castSucc) ((aold j : UniformSpace.Completion A)) < c := by
              rw [dist_comm (x j.castSucc) ((aold j : UniformSpace.Completion A))]
              exact hA
            have hB' : dist ((b : UniformSpace.Completion A)) (x (Fin.last n)) < c := by
              rw [dist_comm ((b : UniformSpace.Completion A)) (x (Fin.last n))]
              exact hb
            rw [UniformSpace.Completion.dist_eq (aold j) b] at h2
            dsimp [D, c] at *
            linarith
          rw [abs_lt]
          constructor <;> linarith
        have hρle_Dhalf : ∀ j : Fin n, ρ ≤ D j / 2 := by
          intro j
          have hmj := hmle j
          linarith
        have hab_pos : ∀ j : Fin n, 0 < dist (aold j) b := by
          intro j
          have hlt := (abs_lt.mp (herr j)).1
          have hDj : 0 < D j := lt_of_lt_of_le hmpos (hmle j)
          have hρD := hρle_Dhalf j
          linarith
        let g : Option (Fin n) → A := fun
          | none => b
          | some j => aold j
        have hg_inj : Function.Injective g := by
          intro p q hpq
          cases p with
          | none =>
              cases q with
              | none => rfl
              | some j =>
                  have h : dist (aold j) b = 0 := by
                    dsimp [g] at hpq
                    rw [← hpq, dist_self]
                  exact False.elim ((ne_of_gt (hab_pos j)) h)
          | some i =>
              cases q with
              | none =>
                  have h : dist (aold i) b = 0 := by
                    dsimp [g] at hpq
                    rw [hpq, dist_self]
                  exact False.elim ((ne_of_gt (hab_pos i)) h)
              | some j =>
                  dsimp [g] at hpq
                  exact congrArg some (haold_inj hpq)
        let r : Option (Fin n) → Set.Icc (0 : ℝ) 1 := fun
          | none => ⟨ρ, ⟨le_of_lt hρpos, hρle_one⟩⟩
          | some j => ⟨D j, ⟨dist_nonneg, dist_le_one_of_diam_one hdiamX _ _⟩⟩
        have hcompat : ∀ p q : Option (Fin n),
            |(r p : ℝ) - (r q : ℝ)| ≤ dist (g p) (g q) ∧
              dist (g p) (g q) ≤ (r p : ℝ) + (r q : ℝ) := by
          intro p q
          cases p with
          | none =>
              cases q with
              | none =>
                  simp [g, r, hρpos.le]
              | some j =>
                  have herr' : |dist b (aold j) - D j| < ρ / 2 := by
                    rw [dist_comm b (aold j)]
                    exact herr j
                  have hlt := abs_lt.mp herr'
                  have hρD := hρle_Dhalf j
                  constructor
                  · rw [abs_sub_le_iff]
                    change ρ - D j ≤ dist b (aold j) ∧ D j - ρ ≤ dist b (aold j)
                    constructor <;> linarith [hlt.1, hlt.2, hρD, hρpos.le,
                      (dist_nonneg : 0 ≤ dist b (aold j))]
                  · change dist b (aold j) ≤ ρ + D j
                    linarith
          | some i =>
              cases q with
              | none =>
                  have hlt := abs_lt.mp (herr i)
                  have hρD := hρle_Dhalf i
                  constructor
                  · rw [abs_sub_le_iff]
                    change D i - ρ ≤ dist (aold i) b ∧ ρ - D i ≤ dist (aold i) b
                    constructor <;> linarith [hlt.1, hlt.2, hρD, hρpos.le,
                      (dist_nonneg : 0 ≤ dist (aold i) b)]
                  · change dist (aold i) b ≤ D i + ρ
                    linarith
              | some j =>
                  constructor
                  · rw [abs_sub_le_iff]
                    change D i - D j ≤ dist (aold i) (aold j) ∧
                      D j - D i ≤ dist (aold i) (aold j)
                    rw [haold_dist i j]
                    constructor
                    · have htri := dist_triangle (x i.castSucc) (x j.castSucc) (x (Fin.last n))
                      dsimp [D] at htri ⊢
                      linarith
                    · have htri := dist_triangle (x j.castSucc) (x i.castSucc) (x (Fin.last n))
                      have htri' : dist (x j.castSucc) (x (Fin.last n)) ≤
                          dist (x i.castSucc) (x j.castSucc) +
                            dist (x i.castSucc) (x (Fin.last n)) := by
                        rw [dist_comm (x j.castSucc) (x i.castSucc)] at htri
                        exact htri
                      dsimp [D] at htri' ⊢
                      linarith
                  · change dist (aold i) (aold j) ≤ D i + D j
                    rw [haold_dist i j]
                    have htri := dist_triangle (x i.castSucc) (x (Fin.last n)) (x j.castSucc)
                    have htri' : dist (x i.castSucc) (x j.castSucc) ≤
                        dist (x i.castSucc) (x (Fin.last n)) +
                          dist (x j.castSucc) (x (Fin.last n)) := by
                      rw [dist_comm (x (Fin.last n)) (x j.castSucc)] at htri
                      exact htri
                    dsimp [D] at htri' ⊢
                    linarith
        obtain ⟨z, hz⟩ := exists_extension_on_range hext hg_inj r hcompat
        let anew : Fin (n + 1) → A := Fin.lastCases z aold
        have hanew_approx : ∀ i : Fin (n + 1),
            dist ((anew i : UniformSpace.Completion A)) (x i) < ε := by
          intro i
          refine Fin.lastCases ?_ ?_ i
          · have hzb : dist z b = ρ := by
              simpa [r] using hz none
            have h1 : dist ((z : UniformSpace.Completion A)) (x (Fin.last n)) ≤
                dist ((z : UniformSpace.Completion A)) ((b : UniformSpace.Completion A)) +
                  dist ((b : UniformSpace.Completion A)) (x (Fin.last n)) :=
              dist_triangle _ _ _
            rw [UniformSpace.Completion.dist_eq z b] at h1
            have hb' : dist ((b : UniformSpace.Completion A)) (x (Fin.last n)) < c := by
              rw [dist_comm ((b : UniformSpace.Completion A)) (x (Fin.last n))]
              exact hb
            have hgoal : dist ((z : UniformSpace.Completion A)) (x (Fin.last n)) < ε := by
              dsimp [c] at *
              linarith
            simpa only [anew, Fin.lastCases_last] using hgoal
          · intro j
            have hA := haold_approx j
            have hgoal : dist ((aold j : UniformSpace.Completion A)) (x j.castSucc) < ε := by
              dsimp [c] at hA
              linarith
            simpa only [anew, Fin.lastCases_castSucc] using hgoal
        have hanew_dist : ∀ i j : Fin (n + 1),
            dist (anew i) (anew j) = dist (x i) (x j) := by
          intro i j
          refine Fin.lastCases ?_ ?_ i
          · refine Fin.lastCases ?_ ?_ j
            · simp only [anew, Fin.lastCases_last, dist_self]
            · intro k
              have hzk : dist z (aold k) = D k := by
                simpa [r] using hz (some k)
              simp only [anew, Fin.lastCases_last, Fin.lastCases_castSucc]
              rw [hzk]
              exact dist_comm (x k.castSucc) (x (Fin.last n))
          · intro k
            refine Fin.lastCases ?_ ?_ j
            · have hzk : dist z (aold k) = D k := by
                simpa [r] using hz (some k)
              simp only [anew, Fin.lastCases_last, Fin.lastCases_castSucc]
              rw [dist_comm (aold k) z, hzk]
            · intro l
              simp only [anew, Fin.lastCases_castSucc]
              exact haold_dist k l
        refine ⟨anew, hanew_approx, hanew_dist⟩

/- accepted add_to_file helper 3 -/
lemma completion_extension_fin
    {A : Type*} [MetricSpace A]
    (hext : ∀ (F : Set A), F.Finite →
      ∀ f : F → Set.Icc (0 : ℝ) 1,
        (∀ x y : F,
          |(f x : ℝ) - (f y : ℝ)| ≤ dist (x : A) (y : A) ∧
            dist (x : A) (y : A) ≤ (f x : ℝ) + (f y : ℝ)) →
        ∃ z : A, ∀ x : F, dist z (x : A) = (f x : ℝ))
    (hdiamX : Metric.diam (Set.univ : Set (UniformSpace.Completion A)) = 1)
    {n : ℕ} (x : Fin n → UniformSpace.Completion A) (hx : Function.Injective x)
    (r : Fin n → Set.Icc (0 : ℝ) 1)
    (hcompat : ∀ i j : Fin n,
      |(r i : ℝ) - (r j : ℝ)| ≤ dist (x i) (x j) ∧
        dist (x i) (x j) ≤ (r i : ℝ) + (r j : ℝ)) :
    ∃ z : UniformSpace.Completion A, ∀ i : Fin n,
      dist z (x i) = (r i : ℝ) := by
  classical
  by_cases hn : n = 0
  · subst n
    let e : (∅ : Set A) → Set.Icc (0 : ℝ) 1 := fun y => ⟨0, by norm_num⟩
    obtain ⟨a, -⟩ := hext ∅ Set.finite_empty e (by
      intro y
      exact False.elim y.2)
    exact ⟨(a : UniformSpace.Completion A), fun i => i.elim0⟩
  · haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    by_cases hzero : ∃ i : Fin n, (r i : ℝ) = 0
    · obtain ⟨i, hi⟩ := hzero
      refine ⟨x i, fun j => ?_⟩
      have hpair := hcompat i j
      have hle : (r j : ℝ) ≤ dist (x i) (x j) := by
        have h := hpair.1
        rw [hi, zero_sub, abs_neg, abs_of_nonneg (r j).2.1] at h
        exact h
      have hge : dist (x i) (x j) ≤ (r j : ℝ) := by
        simpa [hi] using hpair.2
      exact le_antisymm hge hle
    · have hrpos : ∀ i : Fin n, 0 < (r i : ℝ) := by
        intro i
        exact lt_of_le_of_ne (r i).2.1 (by
          intro h
          exact hzero ⟨i, h.symm⟩)
      obtain ⟨i0, hi0⟩ := Finite.exists_min (fun i : Fin n => (r i : ℝ))
      let R : ℝ := r i0
      have hRpos : 0 < R := hrpos i0
      have hRle : ∀ i : Fin n, R ≤ (r i : ℝ) := hi0
      have hRle_one : R ≤ 1 := (r i0).2.2
      let δ : ℕ → ℝ := fun k => R / 2 / 2 ^ k
      have hδpos : ∀ k, 0 < δ k := by
        intro k
        dsimp [δ]
        positivity
      have hδsucc : ∀ k, δ (k + 1) = δ k / 2 := by
        intro k
        dsimp [δ]
        ring_nf
      have hδle_halfR : ∀ k, δ k ≤ R / 2 := by
        intro k
        induction k with
        | zero =>
            dsimp [δ]
            linarith
        | succ k ih =>
            rw [hδsucc]
            linarith
      have hδlt_r : ∀ k i, δ k < (r i : ℝ) := by
        intro k i
        have h1 := hδle_halfR k
        have h2 := hRle i
        have h3 := hrpos i
        linarith
      have hδle_one : ∀ k, δ k ≤ 1 := by
        intro k
        have h1 := hδle_halfR k
        linarith
      let ε : ℕ → ℝ := fun k => δ k / 8
      have hεpos : ∀ k, 0 < ε k := fun k => by positivity
      have hex : ∀ k : ℕ, ∃ a : Fin n → A,
          (∀ i, dist ((a i : UniformSpace.Completion A)) (x i) < ε k) ∧
          (∀ i j, dist (a i) (a j) = dist (x i) (x j)) := by
        intro k
        exact exists_isometric_approx_fin hext hdiamX n x hx (hεpos k)
      let a : ℕ → Fin n → A := fun k => Classical.choose (hex k)
      have ha : ∀ k,
          (∀ i, dist (((a k) i : UniformSpace.Completion A)) (x i) < ε k) ∧
          (∀ i j, dist ((a k) i) ((a k) j) = dist (x i) (x j)) := by
        intro k
        exact Classical.choose_spec (hex k)
      have ha_inj : ∀ k, Function.Injective (a k) := by
        intro k i j h
        have hd : dist (x i) (x j) = 0 := by
          rw [← (ha k).2 i j, h, dist_self]
        exact hx (dist_eq_zero.mp hd)
      have hcompatA : ∀ k i j,
          |(r i : ℝ) - (r j : ℝ)| ≤ dist ((a k) i) ((a k) j) ∧
            dist ((a k) i) ((a k) j) ≤ (r i : ℝ) + (r j : ℝ) := by
        intro k i j
        simpa [(ha k).2 i j] using hcompat i j
      obtain ⟨z0, hz0⟩ := exists_extension_on_range hext (ha_inj 0) r (hcompatA 0)
      have step : ∀ k (z : A), (∀ i, dist z ((a k) i) = (r i : ℝ)) →
          ∃ w : A, dist w z = δ k ∧
            ∀ i, dist w ((a (k + 1)) i) = (r i : ℝ) := by
        intro k z hz
        have herr : ∀ i, |dist z ((a (k + 1)) i) - (r i : ℝ)| < δ k / 4 := by
          intro i
          have hold : dist ((z : UniformSpace.Completion A)) (((a k) i : UniformSpace.Completion A)) =
              (r i : ℝ) := by
            rw [UniformSpace.Completion.dist_eq]
            exact hz i
          have hupper : dist z ((a (k + 1)) i) < (r i : ℝ) + δ k / 4 := by
            have h1 : dist ((z : UniformSpace.Completion A)) (((a (k + 1)) i : UniformSpace.Completion A)) ≤
                dist ((z : UniformSpace.Completion A)) (x i) +
                  dist (x i) (((a (k + 1)) i : UniformSpace.Completion A)) :=
              dist_triangle _ _ _
            have h2 : dist ((z : UniformSpace.Completion A)) (x i) ≤
                dist ((z : UniformSpace.Completion A)) (((a k) i : UniformSpace.Completion A)) +
                  dist (((a k) i : UniformSpace.Completion A)) (x i) :=
              dist_triangle _ _ _
            have hnew' : dist (x i) (((a (k + 1)) i : UniformSpace.Completion A)) < ε (k+1) := by
              rw [dist_comm (x i) (((a (k+1)) i : UniformSpace.Completion A))]
              exact (ha (k+1)).1 i
            have hold' : dist (((a k) i : UniformSpace.Completion A)) (x i) < ε k :=
              (ha k).1 i
            rw [UniformSpace.Completion.dist_eq z ((a (k+1)) i)] at h1
            rw [hold] at h2
            have hs := hδsucc k
            have hδp := hδpos k
            dsimp [ε] at *
            linarith
          have hlower : (r i : ℝ) < dist z ((a (k + 1)) i) + δ k / 4 := by
            have h1 : dist ((z : UniformSpace.Completion A)) (((a k) i : UniformSpace.Completion A)) ≤
                dist ((z : UniformSpace.Completion A)) (x i) +
                  dist (x i) (((a k) i : UniformSpace.Completion A)) :=
              dist_triangle _ _ _
            have h2 : dist ((z : UniformSpace.Completion A)) (x i) ≤
                dist ((z : UniformSpace.Completion A)) (((a (k + 1)) i : UniformSpace.Completion A)) +
                  dist (((a (k + 1)) i : UniformSpace.Completion A)) (x i) :=
              dist_triangle _ _ _
            have hold' : dist (x i) (((a k) i : UniformSpace.Completion A)) < ε k := by
              rw [dist_comm (x i) (((a k) i : UniformSpace.Completion A))]
              exact (ha k).1 i
            have hnew' : dist (((a (k + 1)) i : UniformSpace.Completion A)) (x i) < ε (k+1) :=
              (ha (k+1)).1 i
            rw [hold] at h1
            rw [UniformSpace.Completion.dist_eq z ((a (k+1)) i)] at h2
            have hs := hδsucc k
            have hδp := hδpos k
            dsimp [ε] at *
            linarith
          rw [abs_lt]
          constructor <;> linarith
        have hdistpos : ∀ i, 0 < dist z ((a (k + 1)) i) := by
          intro i
          have hlt := (abs_lt.mp (herr i)).1
          have hδr := hδlt_r k i
          have hδp := hδpos k
          linarith
        let g : Option (Fin n) → A := fun
          | none => z
          | some i => (a (k + 1)) i
        have hg_inj : Function.Injective g := by
          intro p q hpq
          cases p with
          | none =>
              cases q with
              | none => rfl
              | some i =>
                  have h : dist z ((a (k+1)) i) = 0 := by
                    dsimp [g] at hpq
                    rw [← hpq, dist_self]
                  exact False.elim ((ne_of_gt (hdistpos i)) h)
          | some i =>
              cases q with
              | none =>
                  have h : dist z ((a (k+1)) i) = 0 := by
                    dsimp [g] at hpq
                    rw [hpq, dist_self]
                  exact False.elim ((ne_of_gt (hdistpos i)) h)
              | some j =>
                  dsimp [g] at hpq
                  exact congrArg some ((ha_inj (k+1)) hpq)
        let rr : Option (Fin n) → Set.Icc (0 : ℝ) 1 := fun
          | none => ⟨δ k, ⟨(hδpos k).le, hδle_one k⟩⟩
          | some i => r i
        have hcompg : ∀ p q : Option (Fin n),
            |(rr p : ℝ) - (rr q : ℝ)| ≤ dist (g p) (g q) ∧
              dist (g p) (g q) ≤ (rr p : ℝ) + (rr q : ℝ) := by
          intro p q
          cases p with
          | none =>
              cases q with
              | none =>
                  simp [g, rr, (hδpos k).le]
              | some i =>
                  have hlt := abs_lt.mp (herr i)
                  have hδr := hδlt_r k i
                  constructor
                  · rw [abs_sub_le_iff]
                    change δ k - (r i : ℝ) ≤ dist z ((a (k+1)) i) ∧
                      (r i : ℝ) - δ k ≤ dist z ((a (k+1)) i)
                    constructor <;> linarith [hlt.1, hlt.2, hδr,
                      (dist_nonneg : 0 ≤ dist z ((a (k+1)) i))]
                  · change dist z ((a (k+1)) i) ≤ δ k + (r i : ℝ)
                    linarith
          | some i =>
              cases q with
              | none =>
                  have herr' : |dist ((a (k+1)) i) z - (r i : ℝ)| < δ k / 4 := by
                    rw [dist_comm ((a (k+1)) i) z]
                    exact herr i
                  have hlt := abs_lt.mp herr'
                  have hδr := hδlt_r k i
                  constructor
                  · rw [abs_sub_le_iff]
                    change (r i : ℝ) - δ k ≤ dist ((a (k+1)) i) z ∧
                      δ k - (r i : ℝ) ≤ dist ((a (k+1)) i) z
                    constructor <;> linarith [hlt.1, hlt.2, hδr,
                      (dist_nonneg : 0 ≤ dist ((a (k+1)) i) z)]
                  · change dist ((a (k+1)) i) z ≤ (r i : ℝ) + δ k
                    linarith
              | some j =>
                  simpa [g, rr, (ha (k+1)).2 i j] using hcompat i j
        obtain ⟨w, hw⟩ := exists_extension_on_range hext hg_inj rr hcompg
        refine ⟨w, ?_, ?_⟩
        · simpa [rr] using hw none
        · intro i
          simpa [rr] using hw (some i)
      let next : ℕ → A → A := fun k z =>
        if hz : (∀ i, dist z ((a k) i) = (r i : ℝ)) then
          Classical.choose (step k z hz)
        else z
      let zseq : ℕ → A := Nat.rec (motive := fun _ => A) z0 (fun k z => next k z)
      have hzsolves : ∀ k i, dist (zseq k) ((a k) i) = (r i : ℝ) := by
        intro k
        induction k with
        | zero =>
            intro i
            exact hz0 i
        | succ k ih =>
            change ∀ i, dist (next k (zseq k)) ((a (k+1)) i) = (r i : ℝ)
            dsimp [next]
            rw [dif_pos ih]
            exact (Classical.choose_spec (step k (zseq k) ih)).2
      have hzstep : ∀ k, dist (zseq (k + 1)) (zseq k) = δ k := by
        intro k
        change dist (next k (zseq k)) (zseq k) = δ k
        dsimp [next]
        rw [dif_pos (hzsolves k)]
        exact (Classical.choose_spec (step k (zseq k) (hzsolves k))).1
      have hsummableδ : Summable δ := by
        dsimp [δ]
        exact summable_geometric_two' R
      let y : ℕ → UniformSpace.Completion A := fun k => (zseq k : UniformSpace.Completion A)
      have hsummableY : Summable (fun k => dist (y k) (y (k+1))) := by
        have hfun : (fun k => dist (y k) (y (k+1))) = δ := by
          funext k
          calc dist (y k) (y (k+1))
              = dist (zseq k) (zseq (k+1)) := by
                  dsimp [y]
                  exact UniformSpace.Completion.dist_eq _ _
          _ = dist (zseq (k+1)) (zseq k) := dist_comm _ _
          _ = δ k := hzstep k
        rw [hfun]
        exact hsummableδ
      have hcauchy : CauchySeq y := cauchySeq_of_summable_dist hsummableY
      obtain ⟨z, hzlim⟩ := cauchySeq_tendsto_of_complete hcauchy
      refine ⟨z, fun i => ?_⟩
      have hδzero : Filter.Tendsto δ Filter.atTop (nhds 0) :=
        hsummableδ.tendsto_atTop_zero
      have hεzero : Filter.Tendsto ε Filter.atTop (nhds 0) := by
        simpa [ε] using hδzero.div_const 8
      have happrox_tendsto : Filter.Tendsto
          (fun k => (((a k) i : UniformSpace.Completion A))) Filter.atTop (nhds (x i)) := by
        rw [tendsto_iff_dist_tendsto_zero]
        exact squeeze_zero (fun k => dist_nonneg) (fun k => ((ha k).1 i).le) hεzero
      have hdist_tendsto : Filter.Tendsto
          (fun k => dist (y k) (((a k) i : UniformSpace.Completion A)))
          Filter.atTop (nhds (dist z (x i))) :=
        hzlim.dist happrox_tendsto
      have hterm_tendsto : Filter.Tendsto
          (fun k => dist (y k) (((a k) i : UniformSpace.Completion A)))
          Filter.atTop (nhds (r i : ℝ)) := by
        apply Filter.Tendsto.congr' _ tendsto_const_nhds
        exact Filter.Eventually.of_forall (fun k => by
          have heq : dist (y k) (((a k) i : UniformSpace.Completion A)) = (r i : ℝ) := by
            calc dist (y k) (((a k) i : UniformSpace.Completion A))
                = dist (zseq k) ((a k) i) := by
                    dsimp [y]
                    exact UniformSpace.Completion.dist_eq _ _
            _ = (r i : ℝ) := hzsolves k i
          exact heq.symm)
      exact tendsto_nhds_unique hdist_tendsto hterm_tendsto

/- verified submission -/
theorem completion_preserves_finite_one_point_extension
    (A : Type*) [MetricSpace A]
    (hdiam : Metric.diam (Set.univ : Set A) = 1)
    (hext : ∀ (F : Set A), F.Finite →
      ∀ f : F → Set.Icc (0 : ℝ) 1,
        (∀ x y : F,
          |(f x : ℝ) - (f y : ℝ)| ≤ dist (x : A) (y : A) ∧
            dist (x : A) (y : A) ≤ (f x : ℝ) + (f y : ℝ)) →
        ∃ z : A, ∀ x : F, dist z (x : A) = (f x : ℝ)) :
    Metric.diam (Set.univ : Set (UniformSpace.Completion A)) = 1 ∧
      ∀ (F : Set (UniformSpace.Completion A)), F.Finite →
        ∀ f : F → Set.Icc (0 : ℝ) 1,
          (∀ x y : F,
            |(f x : ℝ) - (f y : ℝ)| ≤
                dist (x : UniformSpace.Completion A) (y : UniformSpace.Completion A) ∧
              dist (x : UniformSpace.Completion A) (y : UniformSpace.Completion A) ≤
                (f x : ℝ) + (f y : ℝ)) →
          ∃ z : UniformSpace.Completion A, ∀ x : F,
            dist z (x : UniformSpace.Completion A) = (f x : ℝ) := by
  classical
  have hdiamX : Metric.diam (Set.univ : Set (UniformSpace.Completion A)) = 1 := by
    rw [completion_diam_eq A, hdiam]
  refine ⟨hdiamX, ?_⟩
  intro F hF f hcompat
  letI := hF.fintype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin F
  let x : Fin n → UniformSpace.Completion A := fun i => (e.symm i : UniformSpace.Completion A)
  have hx : Function.Injective x := by
    intro i j h
    apply e.symm.injective
    exact Subtype.ext h
  let r : Fin n → Set.Icc (0 : ℝ) 1 := fun i => f (e.symm i)
  have hcompatFin : ∀ i j : Fin n,
      |(r i : ℝ) - (r j : ℝ)| ≤ dist (x i) (x j) ∧
        dist (x i) (x j) ≤ (r i : ℝ) + (r j : ℝ) := by
    intro i j
    exact hcompat (e.symm i) (e.symm j)
  obtain ⟨z, hz⟩ := completion_extension_fin hext hdiamX x hx r hcompatFin
  refine ⟨z, fun y => ?_⟩
  have hy := hz (e y)
  simpa [x, r] using hy


#check_dependency_graph "completion_preserves_finite_one_point_extension" against "{\"edges\":[{\"conclusion\":{\"name\":\"hdiamX\",\"statement\":\"Metric.diam Set.univ = 1\"},\"graphEdgeId\":\"h_001_hdiamx\",\"premises\":[{\"name\":\"hdiam\",\"statement\":\"Metric.diam Set.univ = 1\"}],\"rawEdgeId\":\"telescope_4\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"Metric.diam Set.univ = 1 ∧ ∀ (F : Set (UniformSpace.Completion A)), F.Finite → ∀ (f : ↑F → ↑(Set.Icc 0 1)), (∀ (x y : ↑F), |↑(f x) - ↑(f y)| ≤ dist ↑x ↑y ∧ dist ↑x ↑y ≤ ↑(f x) + ↑(f y)) → ∃ z, ∀ (x : ↑F), dist z ↑x = ↑(f x)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hext\",\"statement\":\"∀ (F : Set A), F.Finite → ∀ (f : ↑F → ↑(Set.Icc 0 1)), (∀ (x y : ↑F), |↑(f x) - ↑(f y)| ≤ dist ↑x ↑y ∧ dist ↑x ↑y ≤ ↑(f x) + ↑(f y)) → ∃ z, ∀ (x : ↑F), dist z ↑x = ↑(f x)\"},{\"name\":\"hdiamX\",\"statement\":\"Metric.diam Set.univ = 1\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1479_completion_preserves_finite_one_point_exte\",\"reconstructedProofSha256\":\"f502da8ed39d6421ae6092cb084ca49db2da3d85286746dc885524a997d1bd54\",\"selectedEdgeCount\":2,\"theoremName\":\"completion_preserves_finite_one_point_extension\",\"topologySha256\":\"39b1009545f4bff0a670c51396fb742561c861c05ae85f94cd168a4c403d40dc\"}"
