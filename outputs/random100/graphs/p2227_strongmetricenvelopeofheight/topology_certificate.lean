import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2227_strongmetricenvelopeofheight
-- topology_sha256: 0c7a7e1ae1d7e6f1a427f32a3d41f791bd3bd2dbc65bf4ed5fae4de7739626f6
namespace TopologyCertificate_p2227_strongmetricenvelopeofheight

-- N001 = hρ_inv: ∀ (α : G), ρ α⁻¹ = ρ α
-- N002 = hρ_lower: ∀ (α : G), 1 ≤ ρ α
-- N003 = hρ_one: ρ 1 = 1
-- N004 = goal: ((∀ (α : G), 1 ≤ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ α) ∧ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ 1 = 1 ∧ (∀ (α : G), (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ α⁻¹ = (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ α) ∧ ∀ (α β : G), (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ (α * β) ≤ max ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ α) ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ β)) ∧ (∀ (α : G), (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ α ≤ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ ∏ᶠ (n : ℕ+), f (a n) = r}) ρ α) ∧ (∀ (σ : G → ℝ), ((∀ (α : G), 1 ≤ σ α) ∧ σ 1 = 1 ∧ (∀ (α : G), σ α⁻¹ = σ α) ∧ ∀ (α β : G), σ (α * β) ≤ max (σ α) (σ β)) → (∀ (α : G), σ α ≤ ρ α) → ∀ (α : G), σ α ≤ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ α) ∧ (ρ = (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ ↔ (∀ (α : G), 1 ≤ ρ α) ∧ ρ 1 = 1 ∧ (∀ (α : G), ρ α⁻¹ = ρ α) ∧ ∀ (α β : G), ρ (α * β) ≤ max (ρ α) (ρ β)) ∧ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ = (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ ∏ᶠ (n : ℕ+), f (a n) = r}) ρ) ∧ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ ∏ᶠ (n : ℕ+), f (a n) = r}) ρ) = (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ ∏ᶠ (n : ℕ+), f (a n) = r}) ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ) ∧ (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ ∏ᶠ (n : ℕ+), f (a n) = r}) ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ) = (fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ((fun f α => sInf {r | ∃ a, Function.HasFiniteMulSupport a ∧ ∏ᶠ (n : ℕ+), a n = α ∧ sSup (Set.range fun n => f (a n)) = r}) ρ)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N002 → N003 → N001 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B002 B003 B001
  exact H_N004

end TopologyCertificate_p2227_strongmetricenvelopeofheight
