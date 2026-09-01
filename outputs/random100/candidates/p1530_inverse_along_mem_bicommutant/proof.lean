import Mathlib

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
