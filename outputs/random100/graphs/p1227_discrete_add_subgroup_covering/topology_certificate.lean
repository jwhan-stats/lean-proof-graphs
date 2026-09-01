import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1227_discrete_add_subgroup_covering
-- topology_sha256: 37dc515db3c9a5abba24bc857578d4649ea4d16bcd42ddc2a2cc4e5fe39fc62d
namespace TopologyCertificate_p1227_discrete_add_subgroup_covering

-- N001 = hε₀_lt_one: ε₀ < 1
-- N002 = hε₀_pos: 0 < ε₀
-- N003 = hcover: K ⊆ Set.image2 (fun x1 x2 => x1 + x2) (↑L) ((fun x => ε₀ • x) '' K)
-- N004 = hK_nhds: 0 ∈ interior K
-- N005 = hK_star: StarConvex ℝ 0 K
-- N006 = goal: let ε₁ := ↑(⌊ε₀ / (1 - ε₀)⌋ + 1) * ε₀; Set.univ = Set.image2 (fun x1 x2 => x1 + x2) (↑L) ((fun x => ε₁ • x) '' K)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (E001 : N004 → N005 → N002 → N001 → N003 → N006)
    : N006 := by
  have H_N006 : N006 := E001 B004 B005 B002 B001 B003
  exact H_N006

end TopologyCertificate_p1227_discrete_add_subgroup_covering
