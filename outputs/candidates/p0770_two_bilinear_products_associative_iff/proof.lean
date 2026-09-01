import Mathlib

/- accepted add_to_file helper 1 -/
lemma bilinear_dot_assoc_iff
    (k A : Type*) [Field k] [AddCommGroup A] [Module k A]
    (mul₁ mul₂ : A →ₗ[k] A →ₗ[k] A) :
    (Std.Associative (fun x y => mul₁ x y) ∧
      Std.Associative (fun x y => mul₂ x y) ∧
      (∀ x y z, mul₂ (mul₁ x y) z = mul₁ x (mul₂ y z)) ∧
      (∀ x y z, mul₁ (mul₂ x y) z = mul₂ x (mul₁ y z)))
      ↔
    Std.Associative
      (fun u v : A × A =>
        (mul₁ u.1 v.1 + mul₂ u.1 v.2,
          mul₂ u.2 v.2 + mul₁ u.2 v.1)) := by
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    refine Std.Associative.mk ?_
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    ext
    · simp only [map_add, LinearMap.add_apply]
      rw [h₁.assoc a c e, h₄ a d e, h₃ a c f, h₂.assoc a d f]
      abel
    · simp only [map_add, LinearMap.add_apply]
      rw [h₂.assoc b d f, h₃ b c f, h₄ b d e, h₁.assoc b c e]
      abel
  · intro h
    have fst_assoc {a b c d e f : A}
        (hh := Std.Associative.assoc (self := h) (a, b) (c, d) (e, f)) :
        mul₁ (mul₁ a c + mul₂ a d) e + mul₂ (mul₁ a c + mul₂ a d) f =
          mul₁ a (mul₁ c e + mul₂ c f) + mul₂ a (mul₂ d f + mul₁ d e) := by
      exact congrArg Prod.fst hh
    constructor
    · refine Std.Associative.mk ?_
      intro x y z
      have hh := fst_assoc (a := x) (b := 0) (c := y) (d := 0) (e := z) (f := 0)
      simpa using hh
    constructor
    · refine Std.Associative.mk ?_
      intro x y z
      have hh := fst_assoc (a := x) (b := 0) (c := 0) (d := y) (e := 0) (f := z)
      simpa using hh
    constructor
    · intro x y z
      have hh := fst_assoc (a := x) (b := 0) (c := y) (d := 0) (e := 0) (f := z)
      simpa using hh
    · intro x y z
      have hh := fst_assoc (a := x) (b := 0) (c := 0) (d := y) (e := z) (f := 0)
      simpa using hh

/- accepted add_to_file helper 2 -/
lemma bilinear_diamond_assoc_iff
    (k A : Type*) [Field k] [AddCommGroup A] [Module k A]
    (mul₁ mul₂ : A →ₗ[k] A →ₗ[k] A) :
    (Std.Associative (fun x y => mul₁ x y) ∧
      Std.Associative (fun x y => mul₂ x y) ∧
      (∀ x y z, mul₂ (mul₁ x y) z = mul₁ x (mul₂ y z)) ∧
      (∀ x y z, mul₁ (mul₂ x y) z = mul₂ x (mul₁ y z)))
      ↔
    Std.Associative
      (fun u v : A × A =>
        (mul₁ u.1 v.1 + mul₂ u.2 v.1,
          mul₂ u.2 v.2 + mul₁ u.1 v.2)) := by
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    refine Std.Associative.mk ?_
    rintro ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩
    ext
    · simp only [map_add, LinearMap.add_apply]
      rw [h₁.assoc a c e, h₄ b c e, h₂.assoc b d e, h₃ a d e]
      abel
    · simp only [map_add, LinearMap.add_apply]
      rw [h₂.assoc b d f, h₃ a d f, h₁.assoc a c f, h₄ b c f]
      abel
  · intro h
    have fst_assoc {a b c d e f : A}
        (hh := Std.Associative.assoc (self := h) (a, b) (c, d) (e, f)) :
        mul₁ (mul₁ a c + mul₂ b c) e + mul₂ (mul₂ b d + mul₁ a d) e =
          mul₁ a (mul₁ c e + mul₂ d e) + mul₂ b (mul₁ c e + mul₂ d e) := by
      exact congrArg Prod.fst hh
    constructor
    · refine Std.Associative.mk ?_
      intro x y z
      have hh := fst_assoc (a := x) (b := 0) (c := y) (d := 0) (e := z) (f := 0)
      simpa using hh
    constructor
    · refine Std.Associative.mk ?_
      intro x y z
      have hh := fst_assoc (a := 0) (b := x) (c := 0) (d := y) (e := z) (f := 0)
      simpa using hh
    constructor
    · intro x y z
      have hh := fst_assoc (a := x) (b := 0) (c := 0) (d := y) (e := z) (f := 0)
      simpa using hh
    · intro x y z
      have hh := fst_assoc (a := 0) (b := x) (c := y) (d := 0) (e := z) (f := 0)
      simpa using hh

/- verified submission -/
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
      (Std.Associative dot ↔ Std.Associative diamond) := by
  dsimp only
  have hdot := bilinear_dot_assoc_iff k A mul₁ mul₂
  have hdiamond := bilinear_diamond_assoc_iff k A mul₁ mul₂
  constructor
  · exact hdot
  · exact hdot.symm.trans hdiamond
