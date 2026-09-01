import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1180_inversealong_units
-- topology_sha256: 14da5c37624322edd95e16aea21e85ecc3ac5185160255fc6420240c3d494907
namespace TopologyCertificate_p1180_inversealong_units

-- N001 = h_inner: b * a * b = b
-- N002 = h_left: (Set.range fun y => y * b) = Set.range fun y => y * d
-- N003 = h_right: (Set.range fun y => b * y) = Set.range fun y => d * y
-- N004 = goal: ↑r * b * ↑s⁻¹ * (↑s * a * ↑r⁻¹) * (↑r * b * ↑s⁻¹) = ↑r * b * ↑s⁻¹ ∧ ((Set.range fun y => ↑r * b * ↑s⁻¹ * y) = Set.range fun y => ↑r * d * ↑s⁻¹ * y) ∧ (Set.range fun y => y * (↑r * b * ↑s⁻¹)) = Set.range fun y => y * (↑r * d * ↑s⁻¹)

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

end TopologyCertificate_p1180_inversealong_units
