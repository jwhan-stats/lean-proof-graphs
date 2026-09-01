import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2161_cell_entropy_inequality_for_semidiscrete_f
-- topology_sha256: 914bb69b48bd25703fb73fec441a26a5ec4704a2b1e65300ddb0beca72209839
namespace TopologyCertificate_p2161_cell_entropy_inequality_for_semidiscrete_f

-- N001 = hδ: ∀ r ∈ N, 0 < δ r
-- N002 = hε: ∀ r ∈ N, 0 ≤ ε r
-- N003 = hA: ∀ r ∈ N, 0 ≤ A r
-- N004 = hd: dρSdt = 1 / V * ∑ r ∈ N, A r * (-D r + g r + entropyProduction r)
-- N005 = hH: ∀ r ∈ N, (H r).PosSemidef
-- N006 = hT: 0 < T
-- N007 = hV: 0 < V
-- N008 = hprod: ∀ r ∈ N, 0 ≤ entropyProduction r
-- N009 = hsum: ∑ r ∈ N, A r * (-D r + g r + entropyProduction r) = -∑ r ∈ N, A r * D r + ∑ r ∈ N, A r * g r + ∑ r ∈ N, A r * entropyProduction r
-- N010 = goal: dρSdt + 1 / V * ∑ r ∈ N, A r * D r - 1 / V * ∑ r ∈ N, A r * g r ≥ 0

-- E001 represents h_001_hprod
-- E002 represents h_002_hsum
-- E003 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (N008 : Prop)
    (N009 : Prop)
    (N010 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (B007 : N007)
    (E001 : N001 → N002 → N006 → N005 → N008)
    (E002 : N009)
    (E003 : N007 → N003 → N004 → N008 → N009 → N010)
    : N010 := by
  have H_N008 : N008 := E001 B001 B002 B006 B005
  have H_N009 : N009 := E002
  have H_N010 : N010 := E003 B007 B003 B004 H_N008 H_N009
  exact H_N010

end TopologyCertificate_p2161_cell_entropy_inequality_for_semidiscrete_f
