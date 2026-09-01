import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0414_veronese_affineindependent
-- topology_sha256: f61763d7c3c5fc654d7efba8545fcae2b44416562e2f20714ee9fb6cc89e5284
namespace TopologyCertificate_p0414_veronese_affineindependent

-- N001 = hrp: r ≤ p + 1
-- N002 = hx: Function.Injective x
-- N003 = goal: let I := { ab // (ab.1.sum fun x n => n) ≤ p ∧ (ab.2.sum fun x n => n) ≤ q }; let v := fun z ab => ((↑ab).1.prod fun i n => z i ^ n) * (↑ab).2.prod fun i n => (starRingEnd ℂ) (z i) ^ n; AffineIndependent ℝ fun j => v (x j)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (B001 : N001)
    (B002 : N002)
    (E001 : N001 → N002 → N003)
    : N003 := by
  have H_N003 : N003 := E001 B001 B002
  exact H_N003

end TopologyCertificate_p0414_veronese_affineindependent
