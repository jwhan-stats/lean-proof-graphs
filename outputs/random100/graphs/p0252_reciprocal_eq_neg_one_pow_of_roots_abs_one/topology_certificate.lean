import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0252_reciprocal_eq_neg_one_pow_of_roots_abs_one
-- topology_sha256: 8135949077b0fb96d1c6fae3bccdb4227c53b9d315b1129708d80ccc0e0481f7
namespace TopologyCertificate_p0252_reciprocal_eq_neg_one_pow_of_roots_abs_one

-- N001 = hf: f ≠ 0
-- N002 = hn: Polynomial.rootMultiplicity 1 f = n
-- N003 = hroots: ∀ (z : ℂ), (Polynomial.map (algebraMap ℝ ℂ) f).IsRoot z → ‖z‖ = 1
-- N004 = hdvd: A ^ n ∣ f
-- N005 = goal: f.reverse = (-1) ^ n • f

-- E001 represents h_001_hdvd
-- E002 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N002 → N004)
    (E002 : N001 → N003 → N002 → N004 → N005)
    : N005 := by
  have H_N004 : N004 := E001 B002
  have H_N005 : N005 := E002 B001 B003 B002 H_N004
  exact H_N005

end TopologyCertificate_p0252_reciprocal_eq_neg_one_pow_of_roots_abs_one
