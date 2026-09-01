import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1874_proposition_4_9
-- topology_sha256: bcec890446f03ce91c83154fc3473ac279905ed22afa855c356ec184c9c9a442
namespace TopologyCertificate_p1874_proposition_4_9

-- N001 = hμ: ∀ (n : ℕ) (A : Set ↑(Set.Icc 0 1)), A.OrdConnected → Metric.diam A ≤ Real.rpow 2 (-↑n) → μ A ≤ ENNReal.ofReal (Real.rpow 2 (-(α * ↑n + ↑(f n))))
-- N002 = hα: 0 ≤ α
-- N003 = hf: Summable fun n => Real.rpow 2 (-↑(f n))
-- N004 = hμu: μ Set.univ < ⊤
-- N005 = htsum: ∑' (n : ℕ), ENNReal.ofReal (Real.rpow 2 (-↑(f n))) < ⊤
-- N006 = hK: K < ⊤
-- N007 = goal: ∫⁻ (x : ↑(Set.Icc 0 1)), ∫⁻ (y : ↑(Set.Icc 0 1)), 1 / ENNReal.ofReal |↑x - ↑y| ^ α ∂μ ∂μ < ⊤

-- E001 represents h_001_h_u
-- E002 represents h_002_htsum
-- E003 represents h_003_hk
-- E004 represents h_goal

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
    (E001 : N001 → N004)
    (E002 : N003 → N005)
    (E003 : N004 → N005 → N006)
    (E004 : N002 → N003 → N001 → N004 → N006 → N007)
    : N007 := by
  have H_N004 : N004 := E001 B001
  have H_N005 : N005 := E002 B003
  have H_N006 : N006 := E003 H_N004 H_N005
  have H_N007 : N007 := E004 B002 B003 B001 H_N004 H_N006
  exact H_N007

end TopologyCertificate_p1874_proposition_4_9
