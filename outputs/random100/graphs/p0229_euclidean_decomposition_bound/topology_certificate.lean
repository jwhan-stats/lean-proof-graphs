import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0229_euclidean_decomposition_bound
-- topology_sha256: 60d8d4e289aa2948542a900b0644473c2588737e01bfa65a0a429d00fc12a92b
namespace TopologyCertificate_p0229_euclidean_decomposition_bound

-- N001 = hep: e ≤ p + 1
-- N002 = hp: Nat.Prime p
-- N003 = hsize: 4 * p ^ 2 ≤ n + 2
-- N004 = hp0: 0 < p
-- N005 = hp2: 2 ≤ p
-- N006 = goal: ∃ d, ∃ f < p, n + 2 = p * d + f + e ∧ d ≥ e + f + (2 * p - 2)

-- E001 represents h_001_hp0
-- E002 represents h_002_hp2
-- E003 represents h_goal

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
    (E001 : N002 → N004)
    (E002 : N002 → N005)
    (E003 : N002 → N003 → N001 → N004 → N005 → N006)
    : N006 := by
  have H_N004 : N004 := E001 B002
  have H_N005 : N005 := E002 B002
  have H_N006 : N006 := E003 B002 B003 B001 H_N004 H_N005
  exact H_N006

end TopologyCertificate_p0229_euclidean_decomposition_bound
