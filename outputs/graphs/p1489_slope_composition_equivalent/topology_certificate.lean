import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1489_slope_composition_equivalent
-- topology_sha256: 7a474cd4744979179ba1711124439a6e82dead9ccc91bf25655d868fb3d61174
namespace TopologyCertificate_p1489_slope_composition_equivalent

-- N001 = hββ': (Set.range fun n => β n - β' n).Finite
-- N002 = hα': (Set.range fun p => α' (p.1 + p.2) - α' p.1 - α' p.2).Finite
-- N003 = hβ': (Set.range fun p => β' (p.1 + p.2) - β' p.1 - β' p.2).Finite
-- N004 = hα: (Set.range fun p => α (p.1 + p.2) - α p.1 - α p.2).Finite
-- N005 = hβ: (Set.range fun p => β (p.1 + p.2) - β p.1 - β p.2).Finite
-- N006 = hαα': (Set.range fun n => α n - α' n).Finite
-- N007 = goal: (Set.range fun p => α (β (p.1 + p.2)) - α (β p.1) - α (β p.2)).Finite ∧ (Set.range fun p => α' (β' (p.1 + p.2)) - α' (β' p.1) - α' (β' p.2)).Finite ∧ (Set.range fun n => α (β n) - α' (β' n)).Finite

-- E001 represents h_goal

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
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (E001 : N004 → N002 → N005 → N003 → N006 → N001 → N007)
    : N007 := by
  have H_N007 : N007 := E001 B004 B002 B005 B003 B006 B001
  exact H_N007

end TopologyCertificate_p1489_slope_composition_equivalent
