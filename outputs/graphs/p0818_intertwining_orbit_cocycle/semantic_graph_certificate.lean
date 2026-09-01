import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p0818_intertwining_orbit_cocycle
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 7c24cee0092f3df02efea7f89fb4a675db6848999deb567605152a521cf9f3f3
-- reconstructed_proof_sha256: 9be86f99c61a6854a7b02c50afff54eb32bfd23a779654cc953a427e092b96ec
-- selected_edge_count: 1

/- accepted add_to_file helper 1 -/
lemma orbit_factor_identity {G : Type*} [CommGroup G]
    (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : G) :
    (a₁ * b₁⁻¹) * (a₂ * b₂⁻¹)⁻¹ * (a₃ * b₃⁻¹) * (a₄ * b₄⁻¹)⁻¹ =
      (a₁ * a₂⁻¹ * a₃ * a₄⁻¹) * (b₁ * b₂⁻¹ * b₃ * b₄⁻¹)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/- accepted add_to_file helper 2 -/
lemma coboundary_factor_identity {G : Type*} [CommGroup G]
    (C' C x₁ x₂ x₃ y₁ y₂ y₃ : G) :
    (C' * (x₁ * x₂⁻¹ * x₃)) * (C * (y₁ * y₂⁻¹ * y₃))⁻¹ =
      (C' * C⁻¹) *
        ((x₁ * y₁⁻¹) * (x₂ * y₂⁻¹)⁻¹ * (x₃ * y₃⁻¹)) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/- verified submission -/
theorem intertwining_orbit_cocycle
    {Γ A : Type*} [Group Γ] [AddCommGroup A] [DistribMulAction Γ A]
    {n n' : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n')
    (ρ : Γ →* Equiv.Perm (Fin n)) (ρ' : Γ →* Equiv.Perm (Fin n'))
    (α : Γ → Γ → Γ → A)
    (hα₁ : ∀ g h : Γ, α 1 g h = 0)
    (hα₂ : ∀ g h : Γ, α g 1 h = 0)
    (hα₃ : ∀ g h : Γ, α g h 1 = 0)
    (hαcocycle : ∀ g h k l : Γ,
      g • α h k l - α (g * h) k l + α g (h * k) l -
          α g h (k * l) + α g h k = 0)
    (β : A →+ (Fin n → Additive ℂˣ))
    (β' : A →+ (Fin n' → Additive ℂˣ))
    (hβequiv : ∀ (g : Γ) (u : A) (i : Fin n),
      β (g • u) i = β u ((ρ g)⁻¹ i))
    (hβ'equiv : ∀ (g : Γ) (u : A) (i' : Fin n'),
      β' (g • u) i' = β' u ((ρ' g)⁻¹ i'))
    (c : Γ → Γ → Fin n → ℂˣ)
    (c' : Γ → Γ → Fin n' → ℂˣ)
    (hc₁ : ∀ (g : Γ) (i : Fin n), c 1 g i = 1)
    (hc₂ : ∀ (g : Γ) (i : Fin n), c g 1 i = 1)
    (hc'₁ : ∀ (g : Γ) (i' : Fin n'), c' 1 g i' = 1)
    (hc'₂ : ∀ (g : Γ) (i' : Fin n'), c' g 1 i' = 1)
    (hcob : ∀ (g h k : Γ) (i : Fin n),
      c h k ((ρ g)⁻¹ i) * (c (g * h) k i)⁻¹ * c g (h * k) i *
          (c g h i)⁻¹ = Additive.toMul (β (α g h k) i))
    (hcob' : ∀ (g h k : Γ) (i' : Fin n'),
      c' h k ((ρ' g)⁻¹ i') * (c' (g * h) k i')⁻¹ * c' g (h * k) i' *
          (c' g h i')⁻¹ = Additive.toMul (β' (α g h k) i'))
    (O : Set (Fin n' × Fin n))
    (hO : ∃ p₀ : Fin n' × Fin n,
      O = {p | ∃ g : Γ, p = ((ρ' g)⁻¹ p₀.1, (ρ g)⁻¹ p₀.2)})
    (hintertwine : ∀ (p : Fin n' × Fin n), p ∈ O → ∀ u : A,
      β' u p.1 = β u p.2) :
    let z : Γ → Γ → O → ℂˣ := fun g h p =>
      c' g h p.1.1 * (c g h p.1.2)⁻¹;
    (∀ (g : Γ) (p : O), z 1 g p = 1 ∧ z g 1 p = 1) ∧
    (∀ (g h k : Γ) (p : O),
      (c' h k ((ρ' g)⁻¹ p.1.1) * (c h k ((ρ g)⁻¹ p.1.2))⁻¹) *
          (z (g * h) k p)⁻¹ * z g (h * k) p * (z g h p)⁻¹ = 1) ∧
    (∀ (x : Γ → Fin n → ℂˣ) (x' : Γ → Fin n' → ℂˣ),
      (∀ i : Fin n, x 1 i = 1) →
      (∀ i' : Fin n', x' 1 i' = 1) →
      let δx : Γ → Γ → Fin n → ℂˣ := fun g h i =>
        x h ((ρ g)⁻¹ i) * (x (g * h) i)⁻¹ * x g i;
      let δx' : Γ → Γ → Fin n' → ℂˣ := fun g h i' =>
        x' h ((ρ' g)⁻¹ i') * (x' (g * h) i')⁻¹ * x' g i';
      let y : Γ → O → ℂˣ := fun g p => x' g p.1.1 * (x g p.1.2)⁻¹;
      ∀ (g h : Γ) (p : O),
        (c' g h p.1.1 * δx' g h p.1.1) *
            (c g h p.1.2 * δx g h p.1.2)⁻¹ =
          z g h p *
            ((x' h ((ρ' g)⁻¹ p.1.1) *
                (x h ((ρ g)⁻¹ p.1.2))⁻¹) *
              (y (g * h) p)⁻¹ * y g p)) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro g p
    constructor
    · simp [hc'₁, hc₁]
    · simp [hc'₂, hc₂]
  · intro g h k p
    rw [orbit_factor_identity]
    rw [hcob' g h k p.1.1, hcob g h k p.1.2]
    have hβ := congrArg Additive.toMul (hintertwine p.1 p.2 (α g h k))
    simp [hβ]
  · intro x x' hx hx' g h p
    exact coboundary_factor_identity _ _ _ _ _ _ _ _


#check_dependency_graph "intertwining_orbit_cocycle" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let z := fun g h p => c' g h (↑p).1 * (c g h (↑p).2)⁻¹; (∀ (g : Γ) (p : ↑O), z 1 g p = 1 ∧ z g 1 p = 1) ∧ (∀ (g h k : Γ) (p : ↑O), c' h k ((ρ' g)⁻¹ (↑p).1) * (c h k ((ρ g)⁻¹ (↑p).2))⁻¹ * (z (g * h) k p)⁻¹ * z g (h * k) p * (z g h p)⁻¹ = 1) ∧ ∀ (x : Γ → Fin n → ℂˣ) (x' : Γ → Fin n' → ℂˣ), (∀ (i : Fin n), x 1 i = 1) → (∀ (i' : Fin n'), x' 1 i' = 1) → let δx := fun g h i => x h ((ρ g)⁻¹ i) * (x (g * h) i)⁻¹ * x g i; let δx' := fun g h i' => x' h ((ρ' g)⁻¹ i') * (x' (g * h) i')⁻¹ * x' g i'; let y := fun g p => x' g (↑p).1 * (x g (↑p).2)⁻¹; ∀ (g h : Γ) (p : ↑O), c' g h (↑p).1 * δx' g h (↑p).1 * (c g h (↑p).2 * δx g h (↑p).2)⁻¹ = z g h p * (x' h ((ρ' g)⁻¹ (↑p).1) * (x h ((ρ g)⁻¹ (↑p).2))⁻¹ * (y (g * h) p)⁻¹ * y g p)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hc₁\",\"statement\":\"∀ (g : Γ) (i : Fin n), c 1 g i = 1\"},{\"name\":\"hc₂\",\"statement\":\"∀ (g : Γ) (i : Fin n), c g 1 i = 1\"},{\"name\":\"hc'₁\",\"statement\":\"∀ (g : Γ) (i' : Fin n'), c' 1 g i' = 1\"},{\"name\":\"hc'₂\",\"statement\":\"∀ (g : Γ) (i' : Fin n'), c' g 1 i' = 1\"},{\"name\":\"hcob\",\"statement\":\"∀ (g h k : Γ) (i : Fin n), c h k ((ρ g)⁻¹ i) * (c (g * h) k i)⁻¹ * c g (h * k) i * (c g h i)⁻¹ = Additive.toMul (β (α g h k) i)\"},{\"name\":\"hcob'\",\"statement\":\"∀ (g h k : Γ) (i' : Fin n'), c' h k ((ρ' g)⁻¹ i') * (c' (g * h) k i')⁻¹ * c' g (h * k) i' * (c' g h i')⁻¹ = Additive.toMul (β' (α g h k) i')\"},{\"name\":\"hintertwine\",\"statement\":\"∀ p ∈ O, ∀ (u : A), β' u p.1 = β u p.2\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0818_intertwining_orbit_cocycle\",\"reconstructedProofSha256\":\"9be86f99c61a6854a7b02c50afff54eb32bfd23a779654cc953a427e092b96ec\",\"selectedEdgeCount\":1,\"theoremName\":\"intertwining_orbit_cocycle\",\"topologySha256\":\"7c24cee0092f3df02efea7f89fb4a675db6848999deb567605152a521cf9f3f3\"}"
