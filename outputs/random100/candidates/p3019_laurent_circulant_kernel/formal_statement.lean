theorem laurent_circulant_kernel
    (a b n : ℕ) (ha : 0 < a) (hab : a < b) (hab_coprime : Nat.Coprime a b)
    (hn : 3 ≤ n) :
    let _ : NeZero (a + b) := ⟨Nat.ne_of_gt (Nat.add_pos_left ha b)⟩
    let R := LaurentPolynomial ℤ
    let ε : ℤ := (-1) ^ n
    let q : R := LaurentPolynomial.T 1
    let B : Matrix (ZMod (a + b)) (ZMod (a + b)) R := fun i j =>
      if i - j = ((-(a : ℤ) : ℤ) : ZMod (a + b)) then
        LaurentPolynomial.C ε * q
      else if i - j ∈ (Finset.Ico 1 a).image
          (fun k : ℕ => (((k : ℤ) - (a : ℤ) : ℤ) : ZMod (a + b))) then
        1 + LaurentPolynomial.C ε * q
      else if i - j = 0 then
        1 - LaurentPolynomial.C ε * q
      else if i - j ∈ (Finset.Ico 1 a).image
          (fun k : ℕ => (k : ZMod (a + b))) then
        -1 - LaurentPolynomial.C ε * q
      else if i - j = (a : ZMod (a + b)) then
        -1
      else
        0
    ∀ v : ZMod (a + b) → R, B.mulVec v = 0 → ∀ i j, v i = v j := by sorry
