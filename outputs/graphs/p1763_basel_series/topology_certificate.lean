import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1763_basel_series
-- topology_sha256: 2f0bedcf54f8c11e6853d12d594dd879fa3f5a8a0457c32c42442f518da051ce
namespace TopologyCertificate_p1763_basel_series

-- N001 = h: HasSum (fun n => 1 / ↑(n + 1) ^ 2) (Real.pi ^ 2 / 6)
-- N002 = goal: HasSum (fun n => 1 / ↑(n + 1) ^ 2) (Real.pi ^ 2 / 6)

-- E001 represents h_001_h
-- E002 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (E001 : N001)
    (E002 : N001 → N002)
    : N002 := by
  have H_N001 : N001 := E001
  have H_N002 : N002 := E002 H_N001
  exact H_N002

end TopologyCertificate_p1763_basel_series
