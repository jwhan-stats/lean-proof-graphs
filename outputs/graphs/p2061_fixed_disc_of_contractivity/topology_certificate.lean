import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2061_fixed_disc_of_contractivity
-- topology_sha256: cdaf7feb9a824a85005a206c49841c05ff511f246426e3bdb3992b5cb809e336
namespace TopologyCertificate_p2061_fixed_disc_of_contractivity

-- N001 = hc₁: c < 1
-- N002 = hcontractive: ∀ (x : X), dist (T x) x ≤ c * dist (T x) x₀
-- N003 = goal: let ρ := sInf {r | ∃ x, T x ≠ x ∧ r = dist x (T x)}; (∀ (x : X), dist x x₀ ≤ ρ → x ≠ x₀ → 0 < dist (T x) x₀ ∧ dist (T x) x₀ ≤ ρ) → ∀ (x : X), dist x x₀ ≤ ρ → T x = x

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

end TopologyCertificate_p2061_fixed_disc_of_contractivity
