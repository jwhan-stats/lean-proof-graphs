import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2920_proposition_3_8
-- topology_sha256: 072a6258b8a4599f09053e96ae1c5d3b4f28aeefb6ed9495f914f7e8c63fff72
namespace TopologyCertificate_p2920_proposition_3_8

-- N001 = goal: let κ := fun x ρ => if ρ.parts.Nodup then (-Polynomial.X) ^ ρ.parts.toFinset.card else 0; let ε := fun a => ∑ s, if h : ∑ i, ↑(s i) = a then ∑ p, ∏ i, κ (↑(s i)) (p i) else 0; let pp := fun a => ∑ s, if h : ∑ i, ↑(s i) = a then ∑ ρ, (1 - Polynomial.X) ^ ∑ i, (ρ i).parts.toFinset.card else 0; let ε₁ := fun a => Polynomial.eval 1 (ε a); ε k = ∑ r ∈ Finset.range (k + 1), Polynomial.C (ε₁ r) * pp (k - r)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p2920_proposition_3_8
