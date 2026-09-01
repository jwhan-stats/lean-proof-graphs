import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0246_formalpowerseries_automorphism_exact_seque
-- topology_sha256: 8fca2d9d47864411a13fe5cf51fc66dc9cb51f610c367e248277ea0507cb00dc
namespace TopologyCertificate_p0246_formalpowerseries_automorphism_exact_seque

-- N001 = hN: 2 ≤ N
-- N002 = hNpos: 0 < N
-- N003 = goal: ∃ Aut AutN, (∀ (ρ : PowerSeries ℂ ≃ₐ[ℂ] PowerSeries ℂ), ρ ∈ Aut ↔ Continuous ⇑ρ ∧ Continuous ⇑ρ.symm) ∧ (∀ (ρ : PowerSeries ℂ ≃ₐ[ℂ] PowerSeries ℂ), ρ ∈ AutN ↔ Continuous ⇑ρ ∧ Continuous ⇑ρ.symm ∧ ⇑ρ '' Set.range ⇑(PowerSeries.expand N ⋯) = Set.range ⇑(PowerSeries.expand N ⋯)) ∧ ∃ ι μ, (∀ (ρ : ↥AutN) (f : PowerSeries ℂ), (PowerSeries.expand N ⋯) (↑(μ ρ) f) = ↑ρ ((PowerSeries.expand N ⋯) f)) ∧ (∀ (ρ : ↥AutN), (PowerSeries.expand N ⋯) (↑(μ ρ) PowerSeries.X) = ↑ρ PowerSeries.X ^ N) ∧ (∀ (ε : ↥(rootsOfUnity N ℂ)), ↑(ι ε) PowerSeries.X = (algebraMap ℂ (PowerSeries ℂ)) ↑↑ε * PowerSeries.X) ∧ Function.Injective ⇑ι ∧ Function.Surjective ⇑μ ∧ ι.range = μ.ker ∧ ι.range ≤ Subgroup.center ↥AutN

-- E001 represents h_001_hnpos
-- E002 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    (E002 : N001 → N002 → N003)
    : N003 := by
  have H_N002 : N002 := E001 B001
  have H_N003 : N003 := E002 B001 H_N002
  exact H_N003

end TopologyCertificate_p0246_formalpowerseries_automorphism_exact_seque
