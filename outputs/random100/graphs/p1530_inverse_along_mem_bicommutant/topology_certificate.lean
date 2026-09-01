import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1530_inverse_along_mem_bicommutant
-- topology_sha256: b46fcaa3152d6c46b1095bf53141771c7e60801a5c82e999fd8954042fb790bd
namespace TopologyCertificate_p1530_inverse_along_mem_bicommutant

-- N001 = hbad: b * a * d = d
-- N002 = hbd: ∃ x y, b = d * x ∧ b = y * d
-- N003 = hdab: d * a * b = d
-- N004 = goal: ∀ (c : S), c * a = a * c → c * d = d * c → c * b = b * c

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N001 → N003 → N002 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B001 B003 B002
  exact H_N004

end TopologyCertificate_p1530_inverse_along_mem_bicommutant
