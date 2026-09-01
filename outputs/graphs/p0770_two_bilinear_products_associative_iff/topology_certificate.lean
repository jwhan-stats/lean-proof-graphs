import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0770_two_bilinear_products_associative_iff
-- topology_sha256: 03737d53c077ded934bac5dc575473f2664b4ae966ca594aa2a3036fff53279b
namespace TopologyCertificate_p0770_two_bilinear_products_associative_iff

-- N001 = goal: let dot := fun x x_1 => match x with | (a, b) => match x_1 with | (c, d) => ((mul₁ a) c + (mul₂ a) d, (mul₂ b) d + (mul₁ b) c); let diamond := fun x x_1 => match x with | (a, b) => match x_1 with | (c, d) => ((mul₁ a) c + (mul₂ b) c, (mul₂ b) d + (mul₁ a) d); let compatibility := (Std.Associative fun x y => (mul₁ x) y) ∧ (Std.Associative fun x y => (mul₂ x) y) ∧ (∀ (x y z : A), (mul₂ ((mul₁ x) y)) z = (mul₁ x) ((mul₂ y) z)) ∧ ∀ (x y z : A), (mul₁ ((mul₂ x) y)) z = (mul₂ x) ((mul₁ y) z); (compatibility ↔ Std.Associative dot) ∧ (Std.Associative dot ↔ Std.Associative diamond)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p0770_two_bilinear_products_associative_iff
