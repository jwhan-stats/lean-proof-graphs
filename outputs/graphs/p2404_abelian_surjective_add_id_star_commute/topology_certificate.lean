import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2404_abelian_surjective_add_id_star_commute
-- topology_sha256: 69f2cf3836ce8fc06e2967a6e32e72fdd62ebbb926a939b0967eab84873aa4af
namespace TopologyCertificate_p2404_abelian_surjective_add_id_star_commute

-- N001 = goal: (Function.Commute ⇑φ fun a => φ a + a) ∧ ∀ (x y : A), (fun a => φ a + a) x = φ y → ∃! z, φ z = x ∧ (fun a => φ a + a) z = y

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p2404_abelian_surjective_add_id_star_commute
