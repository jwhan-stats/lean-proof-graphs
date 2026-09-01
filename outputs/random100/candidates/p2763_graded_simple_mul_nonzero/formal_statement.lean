theorem graded_simple_mul_nonzero
    (G K A : Type*) [Group G] [Field K] [NonUnitalRing A]
    [Module K A] [IsScalarTower K A A] [SMulCommClass K A A]
    (𝒜 : G → Submodule K A)
    (h_direct : iSupIndep 𝒜 ∧ iSup 𝒜 = ⊤)
    (h_mul : ∀ {g h : G} {x y : A}, x ∈ 𝒜 g → y ∈ 𝒜 h → x * y ∈ 𝒜 (g * h))
    (h_nonzero_mul : ∃ x y : A, x * y ≠ 0)
    (h_simple : ∀ I : Submodule K A,
      (∀ (r : A) {x : A}, x ∈ I → r * x ∈ I) →
      (∀ (r : A) {x : A}, x ∈ I → x * r ∈ I) →
      iSup (fun g => 𝒜 g ⊓ I) = I → I = ⊥ ∨ I = ⊤)
    {g h : G} {a b : A} (ha : a ∈ 𝒜 g) (hb : b ∈ 𝒜 h)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    ∃ k : G, ∃ x : A, x ∈ 𝒜 k ∧ a * x * b ≠ 0 := by sorry
