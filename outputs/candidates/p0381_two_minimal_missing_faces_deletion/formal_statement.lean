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
    ∀ S : Set ℕ, S ⊆ Set.Icc 1 m \ {w} → S ∈ K := by sorry
