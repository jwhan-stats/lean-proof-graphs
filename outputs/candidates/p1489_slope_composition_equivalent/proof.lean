import Mathlib

/- accepted add_to_file helper 1 -/
lemma finite_range_apply_eq_of_finite_defect
    (f g g' : ℤ → ℤ)
    (hf : (Set.range (fun p : ℤ × ℤ =>
      f (p.1 + p.2) - f p.1 - f p.2)).Finite)
    (hgg' : (Set.range (fun n : ℤ => g n - g' n)).Finite) :
    (Set.range (fun n : ℤ => f (g n) - f (g' n))).Finite := by
  let A : Set ℤ := Set.range (fun n : ℤ => g n - g' n)
  let B : Set ℤ := Set.range (fun p : ℤ × ℤ =>
    f (p.1 + p.2) - f p.1 - f p.2)
  have hA : A.Finite := hgg'
  have hB : B.Finite := hf
  refine ((hA.prod hB).image (fun q : ℤ × ℤ => q.2 + f q.1)).subset ?_
  rw [Set.range_subset_iff]
  intro n
  refine ⟨(g n - g' n,
      f (g' n + (g n - g' n)) - f (g' n) - f (g n - g' n)), ?_, ?_⟩
  · rw [Set.mem_prod]
    constructor
    · exact ⟨n, rfl⟩
    · exact ⟨(g' n, g n - g' n), by ring⟩
  · dsimp
    ring

lemma finite_range_defect_comp
    (f g : ℤ → ℤ)
    (hf : (Set.range (fun p : ℤ × ℤ =>
      f (p.1 + p.2) - f p.1 - f p.2)).Finite)
    (hg : (Set.range (fun p : ℤ × ℤ =>
      g (p.1 + p.2) - g p.1 - g p.2)).Finite) :
    (Set.range (fun p : ℤ × ℤ =>
      f (g (p.1 + p.2)) - f (g p.1) - f (g p.2))).Finite := by
  let A : Set ℤ := Set.range (fun p : ℤ × ℤ =>
    g (p.1 + p.2) - g p.1 - g p.2)
  let B : Set ℤ := Set.range (fun p : ℤ × ℤ =>
    f (p.1 + p.2) - f p.1 - f p.2)
  have hA : A.Finite := hg
  have hB : B.Finite := hf
  refine (((hA.prod hB).prod hB).image
    (fun q : (ℤ × ℤ) × ℤ => q.1.2 + f q.1.1 + q.2)).subset ?_
  rw [Set.range_subset_iff]
  intro p
  let d : ℤ := g (p.1 + p.2) - g p.1 - g p.2
  let u : ℤ := f ((g p.1 + g p.2) + d) - f (g p.1 + g p.2) - f d
  let v : ℤ := f (g p.1 + g p.2) - f (g p.1) - f (g p.2)
  have hd : g (p.1 + p.2) = (g p.1 + g p.2) + d := by
    dsimp [d]
    ring
  refine ⟨((d, u), v), ?_, ?_⟩
  · rw [Set.mem_prod, Set.mem_prod]
    refine ⟨⟨⟨p, rfl⟩, ⟨(g p.1 + g p.2, d), by ring⟩⟩,
      ⟨(g p.1, g p.2), rfl⟩⟩
  · dsimp
    rw [hd]
    ring

/- verified submission -/
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
    (Set.range (fun n : ℤ => α (β n) - α' (β' n))).Finite := by
  refine ⟨finite_range_defect_comp α β hα hβ,
    finite_range_defect_comp α' β' hα' hβ', ?_⟩
  have htranslate : (Set.range (fun n : ℤ =>
      α' (β n) - α' (β' n))).Finite :=
    finite_range_apply_eq_of_finite_defect α' β β' hα' hββ'
  refine ((hαα'.prod htranslate).image
    (fun q : ℤ × ℤ => q.1 + q.2)).subset ?_
  rw [Set.range_subset_iff]
  intro n
  refine ⟨(α (β n) - α' (β n),
      α' (β n) - α' (β' n)), ?_, ?_⟩
  · rw [Set.mem_prod]
    exact ⟨⟨β n, rfl⟩, ⟨n, rfl⟩⟩
  · dsimp
    ring
