theorem finite_field_normalized_one_cocycle_iff
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≡ 1 [MOD q])
    (ν : (ZMod p)ˣ) (hν : orderOf ν = q)
    (α : ZMod q → GaloisField p 2) (hα : α ≠ 0) :
    (α 0 = 0 ∧
      ∀ x y : ZMod q,
        α (x + y) =
          α x + (algebraMap (ZMod p) (GaloisField p 2) (ν : ZMod p)) ^ x.val * α y) ↔
      ∃ r : GaloisField p 2, r ≠ 0 ∧ α 0 = 0 ∧
        ∀ x : ZMod q, x ≠ 0 →
          α x = r * ∑ j ∈ Finset.range x.val,
            (algebraMap (ZMod p) (GaloisField p 2) (ν : ZMod p)) ^ j := by sorry
