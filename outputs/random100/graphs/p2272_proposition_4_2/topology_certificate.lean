import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2272_proposition_4_2
-- topology_sha256: 600b198cacdc3ae08bbac9a54879a718992687cf4b769380a7ffaa2e3faaa668
namespace TopologyCertificate_p2272_proposition_4_2

-- N001 = hγe₁e₁: ↑γ (Sum.inl 0) (Sum.inl 0) = 1
-- N002 = hγe₁e₂: ↑γ (Sum.inl 1) (Sum.inl 0) = 1
-- N003 = hγe₁f₁: ↑γ (Sum.inr 0) (Sum.inl 0) = 0
-- N004 = hγe₁f₂: ↑γ (Sum.inr 1) (Sum.inl 0) = 0
-- N005 = hγGSp: ∃ μ, (↑γ).transpose * Matrix.J (Fin 2) ℤ_[p] * ↑γ = ↑μ • Matrix.J (Fin 2) ℤ_[p]
-- N006 = inst._@.proofs.1926733331._hygCtx._hyg.8: Fact (Nat.Prime p)
-- N007 = goal: {h | (∃ A B, (↑A).det = (↑B).det ∧ h = Matrix.fromBlocks (Matrix.diagonal ![↑A 0 0, ↑B 0 0]) (Matrix.diagonal ![↑A 0 1, ↑B 0 1]) (Matrix.diagonal ![↑A 1 0, ↑B 1 0]) (Matrix.diagonal ![↑A 1 1, ↑B 1 1])) ∧ ∃ k, (∃ μ, (↑k).transpose * Matrix.J (Fin 2) ℤ_[p] * ↑k = ↑μ • Matrix.J (Fin 2) ℤ_[p]) ∧ (∀ (i : Fin 2 ⊕ Fin 2), i ≠ Sum.inl 0 → ↑p ^ m ∣ ↑k i (Sum.inl 0)) ∧ h = (↑(γ * k * γ⁻¹)).map ⇑(algebraMap ℤ_[p] ℚ_[p])} = {h | ∃ A B, (↑A).det = (↑B).det ∧ ↑p ^ m ∣ ↑A 1 0 ∧ ↑p ^ m ∣ ↑B 1 0 ∧ ↑p ^ m ∣ ↑A 0 0 - ↑B 0 0 ∧ h = (Matrix.fromBlocks (Matrix.diagonal ![↑A 0 0, ↑B 0 0]) (Matrix.diagonal ![↑A 0 1, ↑B 0 1]) (Matrix.diagonal ![↑A 1 0, ↑B 1 0]) (Matrix.diagonal ![↑A 1 1, ↑B 1 1])).map ⇑(algebraMap ℤ_[p] ℚ_[p])}

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (E001 : N006 → N005 → N001 → N002 → N003 → N004 → N007)
    : N007 := by
  have H_N007 : N007 := E001 B006 B005 B001 B002 B003 B004
  exact H_N007

end TopologyCertificate_p2272_proposition_4_2
