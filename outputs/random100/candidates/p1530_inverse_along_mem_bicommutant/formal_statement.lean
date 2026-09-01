theorem inverse_along_mem_bicommutant {S : Type*} [Semigroup S] {a d b : S}
    (hbad : b * a * d = d) (hdab : d * a * b = d)
    (hbd : ∃ x y : S, b = d * x ∧ b = y * d) :
    ∀ c : S, c * a = a * c → c * d = d * c → c * b = b * c := by sorry
