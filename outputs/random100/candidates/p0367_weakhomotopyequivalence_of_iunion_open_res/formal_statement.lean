theorem weakHomotopyEquivalence_of_iUnion_open_restrictions
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y))
    (U : {n : ℕ // 1 ≤ n} → Set X)
    (hU_open : ∀ n, IsOpen (U n))
    (hU_mono : Monotone U)
    (hU_cover : ⋃ n, U n = Set.univ)
    (hf : ∀ n,
      let g : C(U n, Y) :=
        ⟨fun x => f x.1, f.continuous.comp continuous_subtype_val⟩
      Function.Bijective
          (Quotient.map g (by
            intro a b h
            exact h.map (fun p => p.map g.continuous)) :
            ZerothHomotopy (U n) → ZerothHomotopy Y) ∧
        ∀ (k : ℕ) (x : U n), Function.Bijective
          (Quotient.map
            (fun p : GenLoop (Fin (k + 1)) (U n) x =>
              (⟨g.comp p.1, by
                intro y hy
                rw [ContinuousMap.comp_apply, p.2 y hy]⟩ :
                GenLoop (Fin (k + 1)) Y (g x)))
            (by
              intro p q h
              exact h.map (fun H => H.compContinuousMap g)) :
            HomotopyGroup.Pi (k + 1) (U n) x →
              HomotopyGroup.Pi (k + 1) Y (g x))) :
    Function.Bijective
        (Quotient.map f (by
          intro a b h
          exact h.map (fun p => p.map f.continuous)) :
          ZerothHomotopy X → ZerothHomotopy Y) ∧
      ∀ (k : ℕ) (x : X), Function.Bijective
        (Quotient.map
          (fun p : GenLoop (Fin (k + 1)) X x =>
            (⟨f.comp p.1, by
              intro y hy
              rw [ContinuousMap.comp_apply, p.2 y hy]⟩ :
              GenLoop (Fin (k + 1)) Y (f x)))
          (by
            intro p q h
            exact h.map (fun H => H.compContinuousMap f)) :
          HomotopyGroup.Pi (k + 1) X x → HomotopyGroup.Pi (k + 1) Y (f x)) := by sorry
