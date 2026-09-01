import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0613_chromaticnumber_cartesianpower
-- topology_sha256: ae22701a4b328287dc620e363fc049b384035cf483673f85fda6131a05a68d18
namespace TopologyCertificate_p0613_chromaticnumber_cartesianpower

-- N001 = hk: 1 ≤ k
-- N002 = hn: 0 < n
-- N003 = hcG: G.Colorable q
-- N004 = hq: q ≠ 0
-- N005 = htop: G.chromaticNumber ≠ ⊤
-- N006 = hcolor: (SimpleGraph.fromRel fun x y => ∃ i, G.Adj (x i) (y i) ∧ ∀ (j : Fin k), j ≠ i → x j = y j).Colorable q
-- N007 = upper: (SimpleGraph.fromRel fun x y => ∃ i, G.Adj (x i) (y i) ∧ ∀ (j : Fin k), j ≠ i → x j = y j).chromaticNumber ≤ G.chromaticNumber
-- N008 = goal: (SimpleGraph.fromRel fun x y => ∃ i, G.Adj (x i) (y i) ∧ ∀ (j : Fin k), j ≠ i → x j = y j).chromaticNumber = G.chromaticNumber

-- E001 represents h_001_hcg
-- E002 represents h_002_hq
-- E003 represents h_004_htop
-- E004 represents h_003_hcolor
-- E005 represents h_005_upper
-- E006 represents h_goal

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
    (E001 : N003)
    (E002 : N002 → N003 → N004)
    (E003 : N003 → N005)
    (E004 : N003 → N004 → N006)
    (E005 : N006 → N005 → N007)
    (E006 : N002 → N001 → N007 → N008)
    : N008 := by
  have H_N003 : N003 := E001
  have H_N004 : N004 := E002 B002 H_N003
  have H_N005 : N005 := E003 H_N003
  have H_N006 : N006 := E004 H_N003 H_N004
  have H_N007 : N007 := E005 H_N006 H_N005
  have H_N008 : N008 := E006 B002 B001 H_N007
  exact H_N008

end TopologyCertificate_p0613_chromaticnumber_cartesianpower
