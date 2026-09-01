import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0818_intertwining_orbit_cocycle
-- topology_sha256: 7c24cee0092f3df02efea7f89fb4a675db6848999deb567605152a521cf9f3f3
namespace TopologyCertificate_p0818_intertwining_orbit_cocycle

-- N001 = hc₂: ∀ (g : Γ) (i : Fin n), c g 1 i = 1
-- N002 = hc'₁: ∀ (g : Γ) (i' : Fin n'), c' 1 g i' = 1
-- N003 = hc'₂: ∀ (g : Γ) (i' : Fin n'), c' g 1 i' = 1
-- N004 = hc₁: ∀ (g : Γ) (i : Fin n), c 1 g i = 1
-- N005 = hcob': ∀ (g h k : Γ) (i' : Fin n'), c' h k ((ρ' g)⁻¹ i') * (c' (g * h) k i')⁻¹ * c' g (h * k) i' * (c' g h i')⁻¹ = Additive.toMul (β' (α g h k) i')
-- N006 = hcob: ∀ (g h k : Γ) (i : Fin n), c h k ((ρ g)⁻¹ i) * (c (g * h) k i)⁻¹ * c g (h * k) i * (c g h i)⁻¹ = Additive.toMul (β (α g h k) i)
-- N007 = hintertwine: ∀ p ∈ O, ∀ (u : A), β' u p.1 = β u p.2
-- N008 = goal: let z := fun g h p => c' g h (↑p).1 * (c g h (↑p).2)⁻¹; (∀ (g : Γ) (p : ↑O), z 1 g p = 1 ∧ z g 1 p = 1) ∧ (∀ (g h k : Γ) (p : ↑O), c' h k ((ρ' g)⁻¹ (↑p).1) * (c h k ((ρ g)⁻¹ (↑p).2))⁻¹ * (z (g * h) k p)⁻¹ * z g (h * k) p * (z g h p)⁻¹ = 1) ∧ ∀ (x : Γ → Fin n → ℂˣ) (x' : Γ → Fin n' → ℂˣ), (∀ (i : Fin n), x 1 i = 1) → (∀ (i' : Fin n'), x' 1 i' = 1) → let δx := fun g h i => x h ((ρ g)⁻¹ i) * (x (g * h) i)⁻¹ * x g i; let δx' := fun g h i' => x' h ((ρ' g)⁻¹ i') * (x' (g * h) i')⁻¹ * x' g i'; let y := fun g p => x' g (↑p).1 * (x g (↑p).2)⁻¹; ∀ (g h : Γ) (p : ↑O), c' g h (↑p).1 * δx' g h (↑p).1 * (c g h (↑p).2 * δx g h (↑p).2)⁻¹ = z g h p * (x' h ((ρ' g)⁻¹ (↑p).1) * (x h ((ρ g)⁻¹ (↑p).2))⁻¹ * (y (g * h) p)⁻¹ * y g p)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (N008 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (B007 : N007)
    (E001 : N004 → N001 → N002 → N003 → N006 → N005 → N007 → N008)
    : N008 := by
  have H_N008 : N008 := E001 B004 B001 B002 B003 B006 B005 B007
  exact H_N008

end TopologyCertificate_p0818_intertwining_orbit_cocycle
