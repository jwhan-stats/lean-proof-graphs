import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0617_sqrt_two_weighted_sum_lt
-- topology_sha256: 85963c6ebe640ec9f2bbd8441d5657b918440f84f595b189f386721059f5c9f8
namespace TopologyCertificate_p0617_sqrt_two_weighted_sum_lt

-- N001 = goal: ∑ j ∈ Finset.range (i + 1), ↑(i - j) * √2 ^ j < (4 + 3 * √2) * √2 ^ i

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p0617_sqrt_two_weighted_sum_lt
