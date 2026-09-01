theorem subgroup_iSup_eq_boolean_iSup
    {U A : Type*} [Group U] [AddCommGroup A] {m : ℕ}
    (a : Fin m → A) (W : A → Subgroup U)
    (hgen : AddSubgroup.closure (Set.range a) = ⊤)
    (hcomm : ∀ x : A, commutator U ≤ W x)
    (hprod : ∀ x y : A,
      (W x : Set U) ⊆ Set.image2 (fun g h : U => g * h) (W y : Set U)
        (W (2 • y - x) : Set U)) :
    (⨆ x : A, W x) = ⨆ s : Finset (Fin m), W (∑ i ∈ s, a i) := by sorry
