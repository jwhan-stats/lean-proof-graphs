theorem slope_composition_equivalent
    (α α' β β' : ℤ → ℤ)
    (hα : (Set.range (fun p : ℤ × ℤ =>
      α (p.1 + p.2) - α p.1 - α p.2)).Finite)
    (hα' : (Set.range (fun p : ℤ × ℤ =>
      α' (p.1 + p.2) - α' p.1 - α' p.2)).Finite)
    (hβ : (Set.range (fun p : ℤ × ℤ =>
      β (p.1 + p.2) - β p.1 - β p.2)).Finite)
    (hβ' : (Set.range (fun p : ℤ × ℤ =>
      β' (p.1 + p.2) - β' p.1 - β' p.2)).Finite)
    (hαα' : (Set.range (fun n : ℤ => α n - α' n)).Finite)
    (hββ' : (Set.range (fun n : ℤ => β n - β' n)).Finite) :
    (Set.range (fun p : ℤ × ℤ =>
      α (β (p.1 + p.2)) - α (β p.1) - α (β p.2))).Finite ∧
    (Set.range (fun p : ℤ × ℤ =>
      α' (β' (p.1 + p.2)) - α' (β' p.1) - α' (β' p.2))).Finite ∧
    (Set.range (fun n : ℤ => α (β n) - α' (β' n))).Finite := by sorry
