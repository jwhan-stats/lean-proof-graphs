theorem affineSemigroup_normal_equiv
    (d : ℕ) (hd : 1 ≤ d)
    (S : AddSubmonoid (Fin d → ℕ)) (hSfg : S.FG)
    (a : Fin d → Fin d → ℕ)
    (haS : ∀ i, a i ∈ S)
    (haLI : LinearIndependent ℝ
      (fun i : Fin d => fun j : Fin d => (a i j : ℝ)))
    (hcone : ∀ x : Fin d → ℝ,
      x ∈ ConvexCone.hull ℝ
          ((fun u : Fin d → ℕ => fun j : Fin d => (u j : ℝ)) ''
            (S : Set (Fin d → ℕ))) ↔
        ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
          x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ)))
    (hminray : ∀ (i : Fin d) (u : Fin d → ℕ),
      u ∈ S → u ≠ 0 →
      (∃ r : ℝ, 0 ≤ r ∧
        (fun j : Fin d => (u j : ℝ)) =
          r • (fun j : Fin d => (a i j : ℝ))) →
      ∀ j, a i j ≤ u j) :
    let natToInt : (Fin d → ℕ) → (Fin d → ℤ) :=
      fun u j => (u j : ℤ)
    let natToReal : (Fin d → ℕ) → (Fin d → ℝ) :=
      fun u j => (u j : ℝ)
    let intToReal : (Fin d → ℤ) → (Fin d → ℝ) :=
      fun u j => (u j : ℝ)
    let C : Set (Fin d → ℝ) :=
      {x | ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i) ∧
        x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))}
    let relintC : Set (Fin d → ℝ) :=
      {x | ∃ c : Fin d → ℝ, (∀ i, 0 < c i) ∧
        x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))}
    let fundamentalParallelepiped : Set (Fin d → ℝ) :=
      {x | ∃ c : Fin d → ℝ, (∀ i, 0 ≤ c i ∧ c i < 1) ∧
        x = ∑ i, c i • (fun j : Fin d => (a i j : ℝ))}
    let apery : Set (Fin d → ℕ) :=
      {w | w ∈ S ∧ ∀ i, ¬∃ s : Fin d → ℕ, s ∈ S ∧ w = s + a i}
    let leS : (Fin d → ℕ) → (Fin d → ℕ) → Prop :=
      fun u v => ∃ s : Fin d → ℕ, s ∈ S ∧ v = u + s
    let maximalApery : (Fin d → ℕ) → Prop :=
      fun m => m ∈ apery ∧
        ∀ w, w ∈ apery → leS m w → leS w m
    let QF : Set (Fin d → ℤ) :=
      {f | ∃ m, maximalApery m ∧
        f = natToInt m - ∑ i, natToInt (a i)}
    let G : Set (Fin d → ℤ) :=
      {z | ∃ u : Fin d → ℕ, u ∈ S ∧
        ∃ v : Fin d → ℕ, v ∈ S ∧ z = natToInt u - natToInt v}
    let normal : Prop :=
      natToInt '' (S : Set (Fin d → ℕ)) =
        G ∩ {z | intToReal z ∈ C}
    let condition2 : Prop :=
      ∀ f, f ∈ QF →
        -f ∈ natToInt '' (S : Set (Fin d → ℕ)) ∧
          intToReal (-f) ∈ relintC
    let condition3 : Prop :=
      ∀ f, f ∈ QF → intToReal (-f) ∈ relintC
    let condition4 : Prop :=
      ∀ w, w ∈ apery → natToReal w ∈ fundamentalParallelepiped
    (normal ↔ condition2) ∧ (normal ↔ condition3) ∧ (normal ↔ condition4) := by sorry
