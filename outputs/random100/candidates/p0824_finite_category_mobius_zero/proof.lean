import Mathlib

/- verified submission -/
import Mathlib

open CategoryTheory

theorem finite_category_mobius_zero
    {A : Type u} [CategoryTheory.Category.{v, u} A] [Fintype A]
    [DecidableEq A] [∀ a b : A, Fintype (a ⟶ b)]
    (μ : A → A → ℚ)
    (hμζ : ∀ a c : A,
      ∑ b : A, μ a b * (Fintype.card (b ⟶ c) : ℚ) =
        if a = c then 1 else 0)
    (hζμ : ∀ a c : A,
      ∑ b : A, (Fintype.card (a ⟶ b) : ℚ) * μ b c =
        if a = c then 1 else 0)
    {a b : A} (hab : IsEmpty (a ⟶ b)) :
    μ a b = 0 := by
  let ζ : Matrix A A ℚ := fun i j => (Fintype.card (i ⟶ j) : ℚ)
  let M : Matrix A A ℚ := fun i j => μ i j
  have hMZ : M * ζ = 1 := by
    ext i j
    simpa [M, ζ, Matrix.mul_apply] using hμζ i j
  have hZM : ζ * M = 1 := by
    ext i j
    simpa [M, ζ, Matrix.mul_apply] using hζμ i j
  letI : Invertible ζ := invertibleOfRightInverse ζ M hZM
  let label : A → Bool := fun x => decide (Fintype.card (x ⟶ b) = 0)
  have hζtri : ζ.BlockTriangular label := by
    intro i j hlt
    by_contra hijζ
    have hcard : Fintype.card (i ⟶ j) ≠ 0 := by
      intro hcard
      apply hijζ
      simp [ζ, hcard]
    have hij : Nonempty (i ⟶ j) :=
      Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hcard)
    have hjfalse : label j = false := (Bool.lt_iff.mp hlt).1
    have hitrue : label i = true := (Bool.lt_iff.mp hlt).2
    have hjcard : Fintype.card (j ⟶ b) ≠ 0 := by
      intro hjcard
      simp [label, hjcard] at hjfalse
    have hjreach : Nonempty (j ⟶ b) :=
      Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hjcard)
    have hicard : Fintype.card (i ⟶ b) = 0 := by
      by_contra hicard
      simp [label, hicard] at hitrue
    have hinreach : ¬ Nonempty (i ⟶ b) := by
      intro hi
      have hpos : 0 < Fintype.card (i ⟶ b) := Fintype.card_pos
      omega
    exact hinreach ⟨hij.some ≫ hjreach.some⟩
  have hμtri : (ζ⁻¹).BlockTriangular label :=
    Matrix.blockTriangular_inv_of_blockTriangular hζtri
  have hinv : ζ⁻¹ = M := Matrix.inv_eq_left_inv hMZ
  have hbcard : Fintype.card (b ⟶ b) ≠ 0 := by
    have hb : Nonempty (b ⟶ b) := ⟨𝟙 b⟩
    exact Fintype.card_ne_zero
  have hlt : label b < label a := by
    rw [Bool.lt_iff]
    constructor
    · simp [label, hbcard]
    · simp [label]
  have hzero : (ζ⁻¹) a b = 0 := hμtri hlt
  have : M a b = 0 := by
    simpa [hinv] using hzero
  simpa [M] using this
