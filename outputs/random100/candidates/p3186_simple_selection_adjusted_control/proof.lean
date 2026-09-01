import Mathlib

/- accepted add_to_file helper 1 -/
noncomputable section

namespace SimpleSelectionAdjustedControl

abbrev PTuple (m : ℕ) (n : Fin m → ℕ) : Type :=
  (i : Fin m) → (Fin (n i) → Set.Icc (0 : ℝ) 1)

def contribution
    (m : ℕ) (q : ℝ) (n : Fin m → ℕ)
    (S : PTuple m n → Finset (Fin m))
    (C : (i : Fin m) → ℝ → (Fin (n i) → Set.Icc (0 : ℝ) 1) → ℝ)
    (i : Fin m) (x : PTuple m n) : ℝ :=
  if i ∈ S x then
    C i (((S x).card : ℝ) * q / (m : ℝ)) (x i) / ((S x).card : ℝ)
  else 0

def totalContribution
    (m : ℕ) (q : ℝ) (n : Fin m → ℕ)
    (S : PTuple m n → Finset (Fin m))
    (C : (i : Fin m) → ℝ → (Fin (n i) → Set.Icc (0 : ℝ) 1) → ℝ)
    (x : PTuple m n) : ℝ :=
  ∑ i : Fin m, contribution m q n S C i x

def selectedAverage
    (m : ℕ) (q : ℝ) (n : Fin m → ℕ)
    (S : PTuple m n → Finset (Fin m))
    (C : (i : Fin m) → ℝ → (Fin (n i) → Set.Icc (0 : ℝ) 1) → ℝ)
    (x : PTuple m n) : ℝ :=
  if (S x).card = 0 then 0
  else
    (∑ i ∈ S x,
      C i (((S x).card : ℝ) * q / (m : ℝ)) (x i)) /
      ((S x).card : ℝ)

lemma measurable_selection
    {m : ℕ} {n : Fin m → ℕ}
    [MeasurableSpace (Finset (Fin m))] [MeasurableSingletonClass (Finset (Fin m))]
    {S : PTuple m n → Finset (Fin m)}
    (hS : ∀ s, MeasurableSet (S ⁻¹' {s})) : Measurable S := by
  intro t _ht
  have ht : t.Finite := Set.toFinite t
  have hpre : S ⁻¹' t = ⋃ s ∈ t, S ⁻¹' {s} := by
    ext x
    simp
  rw [hpre]
  exact MeasurableSet.biUnion ht.countable (fun s _ => hS s)

lemma contribution_measurable
    {m : ℕ} {q : ℝ} {n : Fin m → ℕ}
    [MeasurableSpace (Finset (Fin m))] [MeasurableSingletonClass (Finset (Fin m))]
    {S : PTuple m n → Finset (Fin m)}
    {C : (i : Fin m) → ℝ → (Fin (n i) → Set.Icc (0 : ℝ) 1) → ℝ}
    (hS : ∀ s, MeasurableSet (S ⁻¹' {s}))
    (hC : ∀ i α, Measurable (C i α))
    (i : Fin m) :
    Measurable (contribution m q n S C i) := by
  classical
  let level : ℕ → ℝ := fun r => (r : ℝ) * q / (m : ℝ)
  let term : ℕ → PTuple m n → ℝ := fun r x =>
    if i ∈ S x ∧ (S x).card = r then C i (level r) (x i) / (r : ℝ) else 0
  have hSm : Measurable S := measurable_selection hS
  have hterm : ∀ r, Measurable (term r) := by
    intro r
    have hset : MeasurableSet {x : PTuple m n | i ∈ S x ∧ (S x).card = r} := by
      have hmem : MeasurableSet {x : PTuple m n | i ∈ S x} :=
        hSm (Set.Finite.measurableSet (Set.toFinite {s : Finset (Fin m) | i ∈ s}))
      have hcard : MeasurableSet {x : PTuple m n | (S x).card = r} :=
        hSm (Set.Finite.measurableSet (Set.toFinite {s : Finset (Fin m) | s.card = r}))
      exact hmem.inter hcard
    have hCi : Measurable fun x : PTuple m n => C i (level r) (x i) :=
      (hC i (level r)).comp (measurable_pi_apply i)
    exact Measurable.ite hset (hCi.div_const (r : ℝ)) measurable_const
  have hsum : Measurable fun x : PTuple m n =>
      ∑ r ∈ Finset.range (m + 1), term r x :=
    Finset.measurable_sum _ (fun r _ => hterm r)
  have hEq : ∀ x : PTuple m n,
      contribution m q n S C i x = ∑ r ∈ Finset.range (m + 1), term r x := by
    intro x
    by_cases hi : i ∈ S x
    · have hle : (S x).card ≤ m := by
        simpa using Finset.card_le_univ (S x)
      have hmem : (S x).card ∈ Finset.range (m + 1) := by
        exact Finset.mem_range_succ_iff.mpr hle
      rw [Finset.sum_eq_single ((S x).card)]
      · simp [contribution, term, level, hi]
      · intro r _hr hne
        by_cases hr : (S x).card = r
        · exact False.elim (hne hr.symm)
        · simp [term, hr]
      · intro hnot
        exact False.elim (hnot hmem)
    · simp [contribution, term, hi]
  have hfun : contribution m q n S C i = fun x : PTuple m n =>
      ∑ r ∈ Finset.range (m + 1), term r x := funext hEq
  rw [hfun]
  exact hsum

lemma contribution_nonneg
    {m : ℕ} {q : ℝ} {n : Fin m → ℕ}
    {S : PTuple m n → Finset (Fin m)}
    {C : (i : Fin m) → ℝ → (Fin (n i) → Set.Icc (0 : ℝ) 1) → ℝ}
    (hC_nonneg : ∀ i α p, 0 ≤ C i α p)
    (i : Fin m) (x : PTuple m n) :
    0 ≤ contribution m q n S C i x := by
  by_cases hi : i ∈ S x
  · have hcard : 0 < ((S x).card : ℝ) := by
      exact Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨i, hi⟩)
    simp [contribution, hi]
    exact div_nonneg (hC_nonneg i _ _) hcard.le
  · simp [contribution, hi]

lemma totalContribution_nonneg
    {m : ℕ} {q : ℝ} {n : Fin m → ℕ}
    {S : PTuple m n → Finset (Fin m)}
    {C : (i : Fin m) → ℝ → (Fin (n i) → Set.Icc (0 : ℝ) 1) → ℝ}
    (hC_nonneg : ∀ i α p, 0 ≤ C i α p)
    (x : PTuple m n) :
    0 ≤ totalContribution m q n S C x := by
  exact Finset.sum_nonneg (fun i _ => contribution_nonneg hC_nonneg i x)

lemma totalContribution_measurable
    {m : ℕ} {q : ℝ} {n : Fin m → ℕ}
    [MeasurableSpace (Finset (Fin m))] [MeasurableSingletonClass (Finset (Fin m))]
    {S : PTuple m n → Finset (Fin m)}
    {C : (i : Fin m) → ℝ → (Fin (n i) → Set.Icc (0 : ℝ) 1) → ℝ}
    (hS : ∀ s, MeasurableSet (S ⁻¹' {s}))
    (hC : ∀ i α, Measurable (C i α)) :
    Measurable (totalContribution m q n S C) := by
  exact Finset.measurable_sum _ (fun i _ => contribution_measurable hS hC i)

lemma selectedAverage_eq_totalContribution
    {m : ℕ} {q : ℝ} {n : Fin m → ℕ}
    {S : PTuple m n → Finset (Fin m)}
    {C : (i : Fin m) → ℝ → (Fin (n i) → Set.Icc (0 : ℝ) 1) → ℝ}
    (x : PTuple m n) :
    selectedAverage m q n S C x = totalContribution m q n S C x := by
  classical
  by_cases h0 : (S x).card = 0
  · have hs : S x = ∅ := Finset.card_eq_zero.mp h0
    simp [selectedAverage, totalContribution, contribution, hs]
  · let f : Fin m → ℝ := fun i =>
      if i ∈ S x then
        C i (((S x).card : ℝ) * q / (m : ℝ)) (x i) / ((S x).card : ℝ)
      else 0
    have hA : (∑ i ∈ S x, f i) = ∑ i : Fin m, f i := by
      refine Finset.sum_subset (Finset.subset_univ (S x)) ?_
      intro i _hi_univ hi_not
      simp [f, hi_not]
    have hB : (∑ i ∈ S x, f i) =
        ∑ i ∈ S x,
          C i (((S x).card : ℝ) * q / (m : ℝ)) (x i) / ((S x).card : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [f, hi]
    have hsum : totalContribution m q n S C x =
        ∑ i ∈ S x,
          C i (((S x).card : ℝ) * q / (m : ℝ)) (x i) / ((S x).card : ℝ) := by
      exact hA.symm.trans hB
    rw [selectedAverage, if_neg h0, hsum]
    exact Finset.sum_div (S x)
      (fun i => C i (((S x).card : ℝ) * q / (m : ℝ)) (x i))
      ((S x).card : ℝ)

end SimpleSelectionAdjustedControl

end

/- accepted add_to_file helper 2 -/
namespace SimpleSelectionAdjustedControl

lemma lintegral_contribution_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0 < m)
    (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (n : Fin m → ℕ)
    (P : (i : Fin m) → Ω → (Fin (n i) → Set.Icc (0 : ℝ) 1))
    (hP_measurable : ∀ i, Measurable (P i))
    (S : PTuple m n → Finset (Fin m))
    (hS_measurable : ∀ s, MeasurableSet (S ⁻¹' {s}))
    (hS_simple : ∀ (i : Fin m) x y,
      (∀ j, j ≠ i → x j = y j) →
        i ∈ S x → i ∈ S y → (S x).card = (S y).card)
    (C : (i : Fin m) → ℝ → (Fin (n i) → Set.Icc (0 : ℝ) 1) → ℝ)
    (hC_measurable : ∀ i α, Measurable (C i α))
    (hC_nonnegative : ∀ i α p, 0 ≤ C i α p)
    (hC_valid : ∀ (i : Fin m) (α : ℝ), α ∈ Set.Icc (0 : ℝ) 1 →
      MeasureTheory.Integrable (fun ω => C i α (P i ω)) μ ∧
        ∫ ω, C i α (P i ω) ∂μ ≤ α)
    (i : Fin m) :
    ∫⁻ x, ENNReal.ofReal (contribution m q n S C i x)
      ∂MeasureTheory.Measure.pi (fun j => μ.map (P j)) ≤ ENNReal.ofReal (q / (m : ℝ)) := by
  classical
  letI : MeasurableSpace (Finset (Fin m)) := ⊤
  letI : MeasurableSingletonClass (Finset (Fin m)) :=
    ⟨fun s => by simp⟩
  let ν : (j : Fin m) → MeasureTheory.Measure (Fin (n j) → Set.Icc (0 : ℝ) 1) :=
    fun j => μ.map (P j)
  have hνprob : ∀ j, MeasureTheory.IsProbabilityMeasure (ν j) := by
    intro j
    exact MeasureTheory.Measure.isProbabilityMeasure_map (hP_measurable j).aemeasurable
  haveI : ∀ j, MeasureTheory.IsProbabilityMeasure (ν j) := hνprob
  haveI : ∀ j, MeasureTheory.SigmaFinite (ν j) := fun j => inferInstance
  have hf : Measurable fun x : PTuple m n =>
      ENNReal.ofReal (contribution m q n S C i x) :=
    ENNReal.measurable_ofReal.comp (contribution_measurable hS_measurable hC_measurable i)
  have hg : Measurable fun _ : PTuple m n => ENNReal.ofReal (q / (m : ℝ)) :=
    measurable_const
  have hconst_lint :
      (∫⁻ _p, ENNReal.ofReal (q / (m : ℝ)) ∂ν i) =
        ENNReal.ofReal (q / (m : ℝ)) := by
    calc
      (∫⁻ _p, ENNReal.ofReal (q / (m : ℝ)) ∂ν i)
          = ENNReal.ofReal (q / (m : ℝ)) * (ν i) Set.univ :=
            MeasureTheory.lintegral_const _
      _ = ENNReal.ofReal (q / (m : ℝ)) := by simp
  have hfg :
      (∫⋯∫⁻_{i},
          (fun x : PTuple m n => ENNReal.ofReal (contribution m q n S C i x)) ∂ν) ≤
        ∫⋯∫⁻_{i}, (fun _ : PTuple m n => ENNReal.ofReal (q / (m : ℝ))) ∂ν := by
    rw [MeasureTheory.lmarginal_singleton, MeasureTheory.lmarginal_singleton]
    intro x
    by_cases hsel : ∃ p : Fin (n i) → Set.Icc (0 : ℝ) 1,
        i ∈ S (Function.update x i p)
    · rcases hsel with ⟨p0, hp0⟩
      let r : ℕ := (S (Function.update x i p0)).card
      let α : ℝ := (r : ℝ) * q / (m : ℝ)
      have hrpos_nat : 0 < r := Finset.card_pos.mpr ⟨i, hp0⟩
      have hrpos : 0 < (r : ℝ) := Nat.cast_pos.mpr hrpos_nat
      have hrle : (r : ℝ) ≤ (m : ℝ) := by
        have hle : r ≤ m := by
          simpa [r] using Finset.card_le_univ (S (Function.update x i p0))
        exact_mod_cast hle
      rcases Set.mem_Icc.mp hq with ⟨hq0, hq1⟩
      have hmpos : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
      have hα : α ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg (mul_nonneg (Nat.cast_nonneg r) hq0) (Nat.cast_nonneg m)
        · rw [div_le_iff₀ hmpos]
          nlinarith
      have hconst_card : ∀ p,
          i ∈ S (Function.update x i p) →
          (S (Function.update x i p)).card = r := by
        intro p hp
        have hout : ∀ j, j ≠ i →
            Function.update x i p0 j = Function.update x i p j := by
          intro j hj
          simp [Function.update, hj]
        exact (hS_simple i (Function.update x i p0) (Function.update x i p)
          hout hp0 hp).symm
      have hpoint : ∀ p : Fin (n i) → Set.Icc (0 : ℝ) 1,
          contribution m q n S C i (Function.update x i p) ≤ C i α p / (r : ℝ) := by
        intro p
        by_cases hp : i ∈ S (Function.update x i p)
        · have hcard := hconst_card p hp
          have hlevel : (((S (Function.update x i p)).card : ℝ) * q / (m : ℝ)) = α := by
            simp [α, hcard]
          have heq :
              contribution m q n S C i (Function.update x i p) =
                C i α p / (r : ℝ) := by
            calc
              contribution m q n S C i (Function.update x i p)
                  = if i ∈ S (Function.update x i p) then
                      C i (((S (Function.update x i p)).card : ℝ) * q / (m : ℝ))
                        (Function.update x i p i) /
                        ((S (Function.update x i p)).card : ℝ)
                    else 0 := rfl
              _ = C i (((S (Function.update x i p)).card : ℝ) * q / (m : ℝ))
                    (Function.update x i p i) /
                    ((S (Function.update x i p)).card : ℝ) := if_pos hp
              _ = C i α p / ((S (Function.update x i p)).card : ℝ) := by
                    rw [hlevel, Function.update_self]
              _ = C i α p / (r : ℝ) := by rw [hcard]
          exact le_of_eq heq
        · have hCnonneg : 0 ≤ C i α p / (r : ℝ) :=
            div_nonneg (hC_nonnegative i α p) hrpos.le
          simp [contribution, hp, hCnonneg]
      have hvalid_source := hC_valid i α hα
      have hCint : MeasureTheory.Integrable (fun p => C i α p) (ν i) := by
        dsimp [ν]
        exact (MeasureTheory.integrable_map_measure
          (hC_measurable i α).aestronglyMeasurable
          (hP_measurable i).aemeasurable).2 hvalid_source.1
      have hint_eq :
          (∫ p, C i α p ∂ν i) = ∫ ω, C i α (P i ω) ∂μ := by
        dsimp [ν]
        exact MeasureTheory.integral_map (hP_measurable i).aemeasurable
          (hC_measurable i α).aestronglyMeasurable
      have hCbound : (∫ p, C i α p ∂ν i) ≤ α := by
        rw [hint_eq]
        exact hvalid_source.2
      have hCdiv_int : MeasureTheory.Integrable (fun p => C i α p / (r : ℝ)) (ν i) :=
        hCint.div_const (r : ℝ)
      have hCdiv_nonneg : 0 ≤ᵐ[ν i] fun p => C i α p / (r : ℝ) :=
        Filter.Eventually.of_forall (fun p =>
          div_nonneg (hC_nonnegative i α p) hrpos.le)
      have hlin_eq :
          (∫⁻ p, ENNReal.ofReal (C i α p / (r : ℝ)) ∂ν i) =
            ENNReal.ofReal (∫ p, C i α p / (r : ℝ) ∂ν i) := by
        exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hCdiv_int hCdiv_nonneg).symm
      have hreal_bound : (∫ p, C i α p / (r : ℝ) ∂ν i) ≤ α / (r : ℝ) := by
        rw [MeasureTheory.integral_div]
        exact div_le_div_of_nonneg_right hCbound hrpos.le
      have hαeq : α / (r : ℝ) = q / (m : ℝ) := by
        have hrm : (r : ℝ) ≠ 0 := hrpos.ne'
        have hmm : (m : ℝ) ≠ 0 := hmpos.ne'
        dsimp [α]
        field_simp [hrm, hmm]
      have hinner_le :
          (∫⁻ p, ENNReal.ofReal (contribution m q n S C i (Function.update x i p)) ∂ν i) ≤
            ENNReal.ofReal (q / (m : ℝ)) := by
        calc
          (∫⁻ p, ENNReal.ofReal (contribution m q n S C i (Function.update x i p)) ∂ν i)
              ≤ ∫⁻ p, ENNReal.ofReal (C i α p / (r : ℝ)) ∂ν i := by
                exact MeasureTheory.lintegral_mono (fun p =>
                  ENNReal.ofReal_le_ofReal (hpoint p))
          _ = ENNReal.ofReal (∫ p, C i α p / (r : ℝ) ∂ν i) := hlin_eq
          _ ≤ ENNReal.ofReal (α / (r : ℝ)) := ENNReal.ofReal_le_ofReal hreal_bound
          _ = ENNReal.ofReal (q / (m : ℝ)) := by rw [hαeq]
      calc
        (∫⁻ p, ENNReal.ofReal (contribution m q n S C i (Function.update x i p)) ∂ν i)
            ≤ ENNReal.ofReal (q / (m : ℝ)) := hinner_le
        _ = ∫⁻ _p, ENNReal.ofReal (q / (m : ℝ)) ∂ν i := hconst_lint.symm
    · have hzero : ∀ p : Fin (n i) → Set.Icc (0 : ℝ) 1,
          contribution m q n S C i (Function.update x i p) = 0 := by
        intro p
        have hp : ¬ i ∈ S (Function.update x i p) := by
          intro hp
          exact hsel ⟨p, hp⟩
        simp [contribution, hp]
      calc
        (∫⁻ p, ENNReal.ofReal (contribution m q n S C i (Function.update x i p)) ∂ν i)
            ≤ ENNReal.ofReal (q / (m : ℝ)) := by simp [hzero]
        _ = ∫⁻ _p, ENNReal.ofReal (q / (m : ℝ)) ∂ν i := hconst_lint.symm
  simpa [ν] using
    MeasureTheory.lintegral_le_of_lmarginal_le {i} hf hg hfg

end SimpleSelectionAdjustedControl

/- accepted add_to_file helper 3 -/
namespace SimpleSelectionAdjustedControl

lemma lintegral_totalContribution_le
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0 < m)
    (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (n : Fin m → ℕ)
    (P : (i : Fin m) → Ω → (Fin (n i) → Set.Icc (0 : ℝ) 1))
    (hP_measurable : ∀ i, Measurable (P i))
    (S : PTuple m n → Finset (Fin m))
    (hS_measurable : ∀ s, MeasurableSet (S ⁻¹' {s}))
    (hS_simple : ∀ (i : Fin m) x y,
      (∀ j, j ≠ i → x j = y j) →
        i ∈ S x → i ∈ S y → (S x).card = (S y).card)
    (C : (i : Fin m) → ℝ → (Fin (n i) → Set.Icc (0 : ℝ) 1) → ℝ)
    (hC_measurable : ∀ i α, Measurable (C i α))
    (hC_nonnegative : ∀ i α p, 0 ≤ C i α p)
    (hC_valid : ∀ (i : Fin m) (α : ℝ), α ∈ Set.Icc (0 : ℝ) 1 →
      MeasureTheory.Integrable (fun ω => C i α (P i ω)) μ ∧
        ∫ ω, C i α (P i ω) ∂μ ≤ α) :
    ∫⁻ x, ENNReal.ofReal (totalContribution m q n S C x)
      ∂MeasureTheory.Measure.pi (fun j => μ.map (P j)) ≤ ENNReal.ofReal q := by
  classical
  letI : MeasurableSpace (Finset (Fin m)) := ⊤
  letI : MeasurableSingletonClass (Finset (Fin m)) :=
    ⟨fun s => by simp⟩
  have hofsum : ∀ x : PTuple m n,
      ENNReal.ofReal (totalContribution m q n S C x) =
        ∑ i : Fin m, ENNReal.ofReal (contribution m q n S C i x) := by
    intro x
    exact ENNReal.ofReal_sum_of_nonneg (fun i _ =>
      contribution_nonneg hC_nonnegative i x)
  have hfun_eq :
      (fun x : PTuple m n => ENNReal.ofReal (totalContribution m q n S C x)) =
        fun x => ∑ i : Fin m, ENNReal.ofReal (contribution m q n S C i x) :=
    funext hofsum
  have hmeas : ∀ i ∈ Finset.univ,
      Measurable fun x : PTuple m n =>
        ENNReal.ofReal (contribution m q n S C i x) := by
    intro i _hi
    exact ENNReal.measurable_ofReal.comp
      (contribution_measurable hS_measurable hC_measurable i)
  have hle : ∀ i : Fin m,
      ∫⁻ x, ENNReal.ofReal (contribution m q n S C i x)
        ∂MeasureTheory.Measure.pi (fun j => μ.map (P j)) ≤
          ENNReal.ofReal (q / (m : ℝ)) := by
    intro i
    exact lintegral_contribution_le μ m hm q hq n P hP_measurable S
      hS_measurable hS_simple C hC_measurable hC_nonnegative hC_valid i
  rcases Set.mem_Icc.mp hq with ⟨hq0, _hq1⟩
  have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hmne : (m : ℝ) ≠ 0 := (Nat.cast_pos.mpr hm).ne'
  have hsumq : (∑ _i : Fin m, q / (m : ℝ)) = q := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [nsmul_eq_mul]
    field_simp [hmne]
  have hconst_sum :
      (∑ _i : Fin m, ENNReal.ofReal (q / (m : ℝ))) = ENNReal.ofReal q := by
    calc
      (∑ _i : Fin m, ENNReal.ofReal (q / (m : ℝ)))
          = ENNReal.ofReal (∑ _i : Fin m, q / (m : ℝ)) := by
              symm
              exact ENNReal.ofReal_sum_of_nonneg (fun _ _ =>
                div_nonneg hq0 hmnonneg)
      _ = ENNReal.ofReal q := by rw [hsumq]
  rw [hfun_eq, MeasureTheory.lintegral_finset_sum Finset.univ hmeas]
  calc
    (∑ i : Fin m,
        ∫⁻ x, ENNReal.ofReal (contribution m q n S C i x)
          ∂MeasureTheory.Measure.pi (fun j => μ.map (P j)))
        ≤ ∑ _i : Fin m, ENNReal.ofReal (q / (m : ℝ)) :=
          Finset.sum_le_sum (fun i _ => hle i)
    _ = ENNReal.ofReal q := hconst_sum

end SimpleSelectionAdjustedControl

/- verified submission -/
theorem simple_selection_adjusted_control
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0 < m)
    (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (n : Fin m → ℕ)
    (P : (i : Fin m) → Ω → (Fin (n i) → Set.Icc (0 : ℝ) 1))
    (hP_measurable : ∀ i, Measurable (P i))
    (hP_independent : ProbabilityTheory.iIndepFun P μ)
    (S : ((i : Fin m) → (Fin (n i) → Set.Icc (0 : ℝ) 1)) → Finset (Fin m))
    (hS_measurable : ∀ s, MeasurableSet (S ⁻¹' {s}))
    (hS_simple : ∀ (i : Fin m) x y,
      (∀ j, j ≠ i → x j = y j) →
        i ∈ S x → i ∈ S y → (S x).card = (S y).card)
    (C : (i : Fin m) → ℝ → (Fin (n i) → Set.Icc (0 : ℝ) 1) → ℝ)
    (hC_measurable : ∀ i α, Measurable (C i α))
    (hC_nonnegative : ∀ i α p, 0 ≤ C i α p)
    (hC_countable : (Set.range
      (fun z : Σ i : Fin m, ℝ × (Fin (n i) → Set.Icc (0 : ℝ) 1) =>
        C z.1 z.2.1 z.2.2)).Countable)
    (hC_valid : ∀ (i : Fin m) (α : ℝ), α ∈ Set.Icc (0 : ℝ) 1 →
      MeasureTheory.Integrable (fun ω => C i α (P i ω)) μ ∧
        ∫ ω, C i α (P i ω) ∂μ ≤ α) :
    ∫ ω,
      if (S (fun i => P i ω)).card = 0 then 0
      else
        (∑ i ∈ S (fun j => P j ω),
          C i (((S (fun j => P j ω)).card : ℝ) * q / (m : ℝ)) (P i ω)) /
          ((S (fun i => P i ω)).card : ℝ) ∂μ ≤ q := by
  classical
  letI : MeasurableSpace (Finset (Fin m)) := ⊤
  letI : MeasurableSingletonClass (Finset (Fin m)) :=
    ⟨fun s => by simp⟩
  let F : Ω → SimpleSelectionAdjustedControl.PTuple m n := fun ω i => P i ω
  let Y : SimpleSelectionAdjustedControl.PTuple m n → ℝ :=
    SimpleSelectionAdjustedControl.totalContribution m q n S C
  have hF_measurable : Measurable F := by
    exact measurable_pi_lambda _ hP_measurable
  have hY_measurable : Measurable Y := by
    exact SimpleSelectionAdjustedControl.totalContribution_measurable
      hS_measurable hC_measurable
  have hYF_measurable : Measurable fun ω => Y (F ω) :=
    hY_measurable.comp hF_measurable
  have hY_nonneg : 0 ≤ᵐ[μ] fun ω => Y (F ω) :=
    Filter.Eventually.of_forall (fun ω =>
      SimpleSelectionAdjustedControl.totalContribution_nonneg hC_nonnegative (F ω))
  have hintegral_eq :
      (∫ ω, Y (F ω) ∂μ) =
        (∫⁻ ω, ENNReal.ofReal (Y (F ω)) ∂μ).toReal := by
    exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae hY_nonneg
      hYF_measurable.aestronglyMeasurable
  have hfun :
      (fun ω =>
        if (S (fun i => P i ω)).card = 0 then 0
        else
          (∑ i ∈ S (fun j => P j ω),
            C i (((S (fun j => P j ω)).card : ℝ) * q / (m : ℝ)) (P i ω)) /
            ((S (fun i => P i ω)).card : ℝ)) =
        fun ω => Y (F ω) := by
    funext ω
    change SimpleSelectionAdjustedControl.selectedAverage m q n S C (F ω) = Y (F ω)
    exact SimpleSelectionAdjustedControl.selectedAverage_eq_totalContribution (F ω)
  have hνprob : ∀ j,
      MeasureTheory.IsProbabilityMeasure (μ.map (P j)) := by
    intro j
    exact MeasureTheory.Measure.isProbabilityMeasure_map
      (hP_measurable j).aemeasurable
  haveI : ∀ j, MeasureTheory.IsProbabilityMeasure (μ.map (P j)) := hνprob
  have hjoint_infinite :
      μ.map F = MeasureTheory.Measure.infinitePi fun j => μ.map (P j) := by
    exact (ProbabilityTheory.iIndepFun_iff_map_fun_eq_infinitePi_map
      hP_measurable).mp hP_independent
  have hjoint :
      μ.map F = MeasureTheory.Measure.pi fun j => μ.map (P j) := by
    calc
      μ.map F = MeasureTheory.Measure.infinitePi fun j => μ.map (P j) :=
        hjoint_infinite
      _ = MeasureTheory.Measure.pi fun j => μ.map (P j) :=
        MeasureTheory.Measure.infinitePi_eq_pi _
  have hYenn_measurable : Measurable fun x => ENNReal.ofReal (Y x) :=
    ENNReal.measurable_ofReal.comp hY_measurable
  have hlintegral_map :
      (∫⁻ x, ENNReal.ofReal (Y x) ∂μ.map F) =
        ∫⁻ ω, ENNReal.ofReal (Y (F ω)) ∂μ := by
    exact MeasureTheory.lintegral_map hYenn_measurable hF_measurable
  have hlintegral_source_pi :
      (∫⁻ ω, ENNReal.ofReal (Y (F ω)) ∂μ) =
        ∫⁻ x, ENNReal.ofReal (Y x)
          ∂MeasureTheory.Measure.pi (fun j => μ.map (P j)) := by
    rw [← hlintegral_map, hjoint]
  have hpi_bound :
      (∫⁻ x, ENNReal.ofReal (Y x)
        ∂MeasureTheory.Measure.pi (fun j => μ.map (P j))) ≤ ENNReal.ofReal q := by
    exact SimpleSelectionAdjustedControl.lintegral_totalContribution_le
      μ m hm q hq n P hP_measurable S hS_measurable hS_simple C
      hC_measurable hC_nonnegative hC_valid
  rcases Set.mem_Icc.mp hq with ⟨hq0, _hq1⟩
  have htoReal_bound :
      (∫⁻ ω, ENNReal.ofReal (Y (F ω)) ∂μ).toReal ≤ q := by
    calc
      (∫⁻ ω, ENNReal.ofReal (Y (F ω)) ∂μ).toReal
          = (∫⁻ x, ENNReal.ofReal (Y x)
              ∂MeasureTheory.Measure.pi (fun j => μ.map (P j))).toReal := by
              rw [hlintegral_source_pi]
      _ ≤ (ENNReal.ofReal q).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hpi_bound
      _ = q := ENNReal.toReal_ofReal hq0
  rw [hfun, hintegral_eq]
  exact htoReal_bound
