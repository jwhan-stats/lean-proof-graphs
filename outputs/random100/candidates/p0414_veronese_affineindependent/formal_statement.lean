theorem veronese_affineIndependent
    (m p q r : ℕ) (hr : 1 ≤ r) (hrp : r ≤ p + 1)
    (x : Fin r → (Fin m → ℂ)) (hx : Function.Injective x) :
    let I := {ab : (Fin m →₀ ℕ) × (Fin m →₀ ℕ) //
      ab.1.sum (fun _ n => n) ≤ p ∧ ab.2.sum (fun _ n => n) ≤ q}
    let v : (Fin m → ℂ) → (I → ℂ) := fun z ab =>
      ab.1.1.prod (fun i n => z i ^ n) *
        ab.1.2.prod (fun i n => (starRingEnd ℂ (z i)) ^ n)
    AffineIndependent ℝ (fun j : Fin r => v (x j)) := by sorry
