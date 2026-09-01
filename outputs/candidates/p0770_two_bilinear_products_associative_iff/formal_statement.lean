theorem two_bilinear_products_associative_iff
    (k A : Type*) [Field k] [AddCommGroup A] [Module k A]
    (mul₁ mul₂ : A →ₗ[k] A →ₗ[k] A) :
    let dot : A × A → A × A → A × A :=
      fun (a, b) (c, d) =>
        (mul₁ a c + mul₂ a d, mul₂ b d + mul₁ b c)
    let diamond : A × A → A × A → A × A :=
      fun (a, b) (c, d) =>
        (mul₁ a c + mul₂ b c, mul₂ b d + mul₁ a d)
    let compatibility : Prop :=
      Std.Associative (fun x y => mul₁ x y) ∧
      Std.Associative (fun x y => mul₂ x y) ∧
      (∀ x y z, mul₂ (mul₁ x y) z = mul₁ x (mul₂ y z)) ∧
      (∀ x y z, mul₁ (mul₂ x y) z = mul₂ x (mul₁ y z))
    (compatibility ↔ Std.Associative dot) ∧
      (Std.Associative dot ↔ Std.Associative diamond) := by sorry
