import Mathlib

/- verified submission -/
theorem two_minimal_missing_faces_deletion
    (m : ℕ) (K : Set (Set ℕ)) (I J : Set ℕ)
    (hK_downward : IsLowerSet K)
    (hK_vertices : ∀ ⦃S : Set ℕ⦄, S ∈ K → S ⊆ Set.Icc 1 m)
    (hIJ : I ≠ J)
    (hmissing : ∀ S : Set ℕ,
      Minimal (fun T : Set ℕ => T ⊆ Set.Icc 1 m ∧ T ∉ K) S ↔
        S = I ∨ S = J)
    (hunion : I ∪ J = Set.Icc 1 m)
    (hinter : (I ∩ J).Nonempty)
    {w : ℕ} (hw : w ∈ I ∩ J) :
    ∀ S : Set ℕ, S ⊆ Set.Icc 1 m \ {w} → S ∈ K := by
  intro S hS
  by_contra hSK
  let C : Set (Set ℕ) :=
    {T : Set ℕ | T ⊆ Set.Icc 1 m ∧ T ∉ K ∧ T ⊆ S}
  have hSV : S ⊆ Set.Icc 1 m := hS.trans Set.diff_subset
  have hCfinite : C.Finite := by
    exact (Set.finite_Icc 1 m).powerset.subset (by
      intro T hT
      exact hT.1)
  have hCnonempty : C.Nonempty := by
    exact ⟨S, hSV, hSK, subset_rfl⟩
  obtain ⟨L, hLminC⟩ := hCfinite.exists_minimal hCnonempty
  have hLmin : Minimal (fun T : Set ℕ => T ⊆ Set.Icc 1 m ∧ T ∉ K) L := by
    constructor
    · exact ⟨hLminC.1.1, hLminC.1.2.1⟩
    · intro T hT hTL
      have hTC : T ∈ C := by
        exact ⟨hT.1, hT.2, hTL.trans hLminC.1.2.2⟩
      exact hLminC.2 hTC hTL
  rcases (hmissing L).mp hLmin with hLI | hLJ
  · have hwL : w ∈ L := by
      rw [hLI]
      exact hw.1
    have hwS : w ∈ S := hLminC.1.2.2 hwL
    exact (hS hwS).2 rfl
  · have hwL : w ∈ L := by
      rw [hLJ]
      exact hw.2
    have hwS : w ∈ S := hLminC.1.2.2 hwL
    exact (hS hwS).2 rfl
