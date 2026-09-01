theorem directed_closure_singleton_iff_chain_closure_singleton
    (X : Type*) [TopologicalSpace X] [T0Space X] :
    (∀ D : Set X, D.Nonempty →
      DirectedOn (specializationPreorder X).le D →
      ∃! x : X, closure D = closure ({x} : Set X)) ↔
    (∀ C : Set X, C.Nonempty →
      IsChain (specializationPreorder X).le C →
      ∃! x : X, closure C = closure ({x} : Set X)) := by sorry
