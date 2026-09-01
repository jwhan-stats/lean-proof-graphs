import Mathlib

/- verified submission -/
import Mathlib

open scoped Pointwise

lemma smul_eq_of_smul_eq_smul_of_stabilizer_bot
    {G X : Type*} [Group G] [MulAction G X]
    (hfree : ∀ x : X, MulAction.stabilizer G x = ⊥)
    {x : X} {a b : G} (h : a • x = b • x) : a = b := by
  have hmem : b⁻¹ * a ∈ MulAction.stabilizer G x := by
    rw [MulAction.mem_stabilizer_iff]
    calc
      (b⁻¹ * a) • x = b⁻¹ • (a • x) := by simp [mul_smul]
      _ = b⁻¹ • (b • x) := by rw [h]
      _ = x := by simp
  rw [hfree x] at hmem
  have hone : b⁻¹ * a = 1 := Subgroup.mem_bot.mp hmem
  exact (inv_mul_eq_one.mp hone).symm

theorem orbit_contained_free_action_restrict_measure_preserving
    {Γ Δ Y : Type*} [Group Γ] [Group Δ] [Countable Γ] [Countable Δ]
    [MeasurableSpace Y] [StandardBorelSpace Y]
    [MulAction Γ Y] [MulAction Δ Y]
    [MeasurableConstSMul Γ Y] [MeasurableConstSMul Δ Y]
    (hc_free : ∀ y : Y, MulAction.stabilizer Γ y = ⊥)
    (hd_free : ∀ y : Y, MulAction.stabilizer Δ y = ⊥)
    (horbit : ∀ (δ : Δ) (y : Y), ∃ γ : Γ, δ • y = γ • y)
    (A : Set Y) (hA_meas : MeasurableSet A)
    (hA_inv : ∀ δ : Δ, (fun y : Y => δ • y) '' A = A)
    (μ : MeasureTheory.Measure Y) [MeasureTheory.IsProbabilityMeasure μ]
    [MeasureTheory.SMulInvariantMeasure Γ Y μ]
    (hμA : μ A = 1) :
    ∀ (δ : Δ) (B : Set Y), MeasurableSet B → B ⊆ A →
      μ ((fun y : Y => δ • y) '' B) = μ B := by
  letI := upgradeStandardBorel Y
  intro δ B hB hBA
  let S : Γ → Set Y := fun γ ↦ {y | δ • y = γ • y}
  have hS_meas : ∀ γ : Γ, MeasurableSet (S γ) := by
    intro γ
    exact measurableSet_eq_fun
      (MeasurableConstSMul.measurable_const_smul δ)
      (MeasurableConstSMul.measurable_const_smul γ)
  have hB_eq : B = ⋃ γ : Γ, B ∩ S γ := by
    ext y
    constructor
    · intro hy
      rcases horbit δ y with ⟨γ, hγ⟩
      exact Set.mem_iUnion.2 ⟨γ, hy, hγ⟩
    · intro hy
      rcases Set.mem_iUnion.1 hy with ⟨γ, hy⟩
      exact hy.1
  have hC_meas : ∀ γ : Γ, MeasurableSet (B ∩ S γ) := by
    intro γ
    exact hB.inter (hS_meas γ)
  have hC_disjoint : Pairwise (Function.onFun Disjoint fun γ : Γ ↦ B ∩ S γ) := by
    intro γ₁ γ₂ hne
    rw [Function.onFun, Set.disjoint_left]
    intro y hy₁ hy₂
    apply hne
    exact smul_eq_of_smul_eq_smul_of_stabilizer_bot hc_free
      (hy₁.2.symm.trans hy₂.2)
  have himage_eq :
      (fun y : Y ↦ δ • y) '' B = ⋃ γ : Γ, γ • (B ∩ S γ) := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hyB, hyx⟩
      rcases horbit δ y with ⟨γ, hγ⟩
      apply Set.mem_iUnion.2
      use γ
      rw [Set.mem_smul_set]
      exact ⟨y, ⟨hyB, hγ⟩, hγ ▸ hyx⟩
    · intro hx
      rcases Set.mem_iUnion.1 hx with ⟨γ, hxγ⟩
      rw [Set.mem_smul_set] at hxγ
      rcases hxγ with ⟨y, hy, hyx⟩
      exact ⟨y, hy.1, hy.2.trans hyx⟩
  have hT_meas : ∀ γ : Γ, MeasurableSet (γ • (B ∩ S γ)) := by
    intro γ
    exact (hC_meas γ).const_smul γ
  have hT_disjoint :
      Pairwise (Function.onFun Disjoint fun γ : Γ ↦ γ • (B ∩ S γ)) := by
    intro γ₁ γ₂ hne
    rw [Function.onFun, Set.disjoint_left]
    intro x hx₁ hx₂
    rw [Set.mem_smul_set] at hx₁ hx₂
    rcases hx₁ with ⟨y₁, hy₁, hx₁⟩
    rcases hx₂ with ⟨y₂, hy₂, hx₂⟩
    have hy : y₁ = y₂ := by
      apply smul_left_cancel δ
      calc
        δ • y₁ = γ₁ • y₁ := hy₁.2
        _ = x := hx₁
        _ = γ₂ • y₂ := hx₂.symm
        _ = δ • y₂ := hy₂.2.symm
    apply hne
    subst y₂
    exact smul_eq_of_smul_eq_smul_of_stabilizer_bot hc_free
      (by
        calc
          γ₁ • y₁ = x := hx₁
          _ = γ₂ • y₁ := hx₂.symm)
  calc
    μ ((fun y : Y ↦ δ • y) '' B)
        = μ (⋃ γ : Γ, γ • (B ∩ S γ)) := by rw [himage_eq]
    _ = ∑' γ : Γ, μ (γ • (B ∩ S γ)) :=
        MeasureTheory.measure_iUnion hT_disjoint hT_meas
    _ = ∑' γ : Γ, μ (B ∩ S γ) := by
        simp [MeasureTheory.measure_smul]
    _ = μ (⋃ γ : Γ, B ∩ S γ) :=
        (MeasureTheory.measure_iUnion hC_disjoint hC_meas).symm
    _ = μ B := by rw [← hB_eq]
