theorem parbelos_area_and_vertex_parallelogram
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b < 2 * a) :
    let C₁ : ℝ × ℝ := (0, 0)
    let C₂ : ℝ × ℝ := (2 * b, 0)
    let C₃ : ℝ × ℝ := (4 * a, 0)
    let U : ℝ → ℝ := fun x => a - (x - 2 * a) ^ 2 / (4 * a)
    let L : ℝ → ℝ := fun x => b / 2 - (x - b) ^ 2 / (2 * b)
    let R : ℝ → ℝ := fun x => (2 * a - b) / 2 - (x - (2 * a + b)) ^ 2 / (2 * (2 * a - b))
    let P : Set (ℝ × ℝ) := {p | (0 ≤ p.1 ∧ p.1 ≤ 2 * b ∧ L p.1 ≤ p.2 ∧ p.2 ≤ U p.1) ∨
      (2 * b ≤ p.1 ∧ p.1 ≤ 4 * a ∧ R p.1 ≤ p.2 ∧ p.2 ≤ U p.1)}
    let V₁ : ℝ × ℝ := (b, b / 2)
    let V₂ : ℝ × ℝ := (2 * a, a)
    let V₃ : ℝ × ℝ := (2 * a + b, a - b / 2)
    (V₁ - C₂ = V₂ - V₃ ∧ V₂ - V₁ = V₃ - C₂) ∧
      MeasureTheory.volume P = (4 / 3 : ENNReal) * MeasureTheory.volume (convexHull ℝ ({C₂, V₁, V₂, V₃} : Set (ℝ × ℝ))) := by sorry
