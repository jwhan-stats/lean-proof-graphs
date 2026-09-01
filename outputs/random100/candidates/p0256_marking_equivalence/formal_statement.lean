theorem marking_equivalence
    (n d k r : ℕ) (hn : 0 < n) :
    let V := Fin d ⊕ Fin k
    let E := ({p : Fin d × Fin d // p.1 < p.2} × Fin n) ⊕ (Fin d × Fin k)
    let ends : E → Sym2 V := fun e =>
      match e with
      | Sum.inl x => Sym2.mk (Sum.inl x.1.val.1 : V) (Sum.inl x.1.val.2 : V)
      | Sum.inr x => Sym2.mk (Sum.inl x.1 : V) (Sum.inr x.2 : V)
    let Marking := {μ : Fin r → E // Function.Injective μ}
    let irreducible : Marking → Prop := fun μ =>
      (SimpleGraph.fromRel (fun u v : V =>
        ∃ e : E, e ∉ Set.range μ.1 ∧ ends e = Sym2.mk u v)).Connected
    let DMove : Marking → Marking → Prop := fun μ ν =>
      ∃ a b : E, a ≠ b ∧ ends a = ends b ∧
        ν.1 = fun i => Equiv.swap a b (μ.1 i)
    let TMove : Marking → Marking → Prop := fun μ ν =>
      ∃ D D' D'' : V,
        D ≠ D' ∧ D ≠ D'' ∧ D' ≠ D'' ∧
        ∃ q q' q'' : E,
          ends q = Sym2.mk D' D'' ∧
          ends q' = Sym2.mk D D'' ∧
          ends q'' = Sym2.mk D D' ∧
          ν.1 = if q' ∈ Set.range μ.1 then μ.1
            else fun i => Equiv.swap q q'' (μ.1 i)
    let Move : Marking → Marking → Prop := fun μ ν => DMove μ ν ∨ TMove μ ν
    ∀ μ ν : Marking, irreducible μ → irreducible ν →
      Relation.ReflTransGen Move μ ν := by sorry
