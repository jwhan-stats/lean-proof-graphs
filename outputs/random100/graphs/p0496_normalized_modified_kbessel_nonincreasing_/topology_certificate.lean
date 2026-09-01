import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0496_normalized_modified_kbessel_nonincreasing_
-- topology_sha256: 76e85da9bebe4ed58125c383835dd52ecbe6599bc93f9169392c1b938160e0ad
namespace TopologyCertificate_p0496_normalized_modified_kbessel_nonincreasing

-- N001 = hk: 0 < k
-- N002 = hx: 0 < x
-- N003 = goal: let Γk := fun z => k ^ (z / k - 1) * Real.Gamma (z / k); let 𝓘 := fun ν => ∑' (r : ℕ), Γk (ν + k) / (Γk (↑r * k + ν + k) * 4 ^ r * ↑r.factorial) * x ^ (2 * r); (∀ ⦃ν μ : ℝ⦄, -k < ν → ν ≤ μ → 𝓘 μ ≤ 𝓘 ν) ∧ ∀ ⦃ν₁ ν₂ α : ℝ⦄, -k < ν₁ → -k < ν₂ → 0 ≤ α → α ≤ 1 → 𝓘 (α * ν₁ + (1 - α) * ν₂) ≤ 𝓘 ν₁ ^ α * 𝓘 ν₂ ^ (1 - α)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (B001 : N001)
    (B002 : N002)
    (E001 : N001 → N002 → N003)
    : N003 := by
  have H_N003 : N003 := E001 B001 B002
  exact H_N003

end TopologyCertificate_p0496_normalized_modified_kbessel_nonincreasing
