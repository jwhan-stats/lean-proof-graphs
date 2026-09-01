theorem relative_commuting_probability_le
    {G : Type*} [Group G] [Finite G]
    (N K : Subgroup G) [N.Normal] :
    let π : G →* G ⧸ N := QuotientGroup.mk' N
    let Kbar : Subgroup (G ⧸ N) := K.map π
    (Nat.card {p : K × G // Commute (p.1 : G) p.2} : ℚ) /
        ((Nat.card K : ℚ) * (Nat.card G : ℚ)) ≤
      ((Nat.card {p : Kbar × (G ⧸ N) // Commute (p.1 : G ⧸ N) p.2} : ℚ) /
          ((Nat.card Kbar : ℚ) * (Nat.card (G ⧸ N) : ℚ))) *
        ((Nat.card {p : (K.comap N.subtype) × N // Commute (p.1 : N) p.2} : ℚ) /
          ((Nat.card (K.comap N.subtype) : ℚ) * (Nat.card N : ℚ))) := by sorry
