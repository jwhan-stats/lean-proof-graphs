import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0043_independentdominationnumber_eq_dominationn
-- topology_sha256: c61f4a83bcbad58f8e02ac4870c2a4154fb38a1c4798a2c300e2500f89251222
namespace TopologyCertificate_p0043_independentdominationnumber_eq_dominationn

-- N001 = hhigh: G.IsIndepSet {v | 2 < (G.neighborSet v).ncard}
-- N002 = goal: sInf {n | ∃ D, D.card = n ∧ G.IsIndepSet ↑D ∧ ∀ v ∉ D, ∃ w ∈ D, G.Adj v w} = sInf {n | ∃ D, D.card = n ∧ ∀ v ∉ D, ∃ w ∈ D, G.Adj v w}

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    : N002 := by
  have H_N002 : N002 := E001 B001
  exact H_N002

end TopologyCertificate_p0043_independentdominationnumber_eq_dominationn
