theorem scale_prod
    {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [TotallyDisconnectedSpace H]
    (φ : G ≃ₜ* G) (ψ : H ≃ₜ* H) :
    sInf {n : ℕ | ∃ U : Subgroup (G × H),
      IsCompact (U : Set (G × H)) ∧ IsOpen (U : Set (G × H)) ∧
        n = U.relIndex (U.map (φ.toMulEquiv.toMonoidHom.prodMap ψ.toMulEquiv.toMonoidHom))} =
      sInf {n : ℕ | ∃ V : Subgroup G,
        IsCompact (V : Set G) ∧ IsOpen (V : Set G) ∧
          n = V.relIndex (V.map φ.toMulEquiv.toMonoidHom)} *
      sInf {n : ℕ | ∃ W : Subgroup H,
        IsCompact (W : Set H) ∧ IsOpen (W : Set H) ∧
          n = W.relIndex (W.map ψ.toMulEquiv.toMonoidHom)} := by sorry
