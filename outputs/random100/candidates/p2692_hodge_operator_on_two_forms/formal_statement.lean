theorem hodge_operator_on_two_forms
    (q : ℂ) (hq0 : q ≠ 0) (hq_one : q ^ 2 ≠ (1 : ℂ))
    (hq_neg_one : q ^ 2 ≠ (-1 : ℂ))
    (V : Type*) [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis (Fin 6) ℂ V) (star : V →ₗ[ℂ] V) :
    let μ : ℂ := 1 - (q ^ 2)⁻¹
    let e_ab : V := b 0
    let e_ac : V := b 1
    let e_ad : V := b 2
    let e_bc : V := b 3
    let e_bd : V := b 4
    let e_cd : V := b 5
    (star e_ab = -e_ab + (2 * μ) • e_bd ∧
      star e_ac = e_ac ∧
      star e_ad = (1 / (1 + q ^ 2)) •
        ((2 : ℂ) • e_bc - (q ^ 2 * μ) • e_ad) ∧
      star e_bc = (q ^ 2 / (1 + q ^ 2)) •
        ((2 : ℂ) • e_ad + μ • e_bc) ∧
      star e_bd = e_bd ∧
      star e_cd = -e_cd) →
    star.comp star = LinearMap.id ∧
      LinearMap.ker (star - LinearMap.id) =
        Submodule.span ℂ {e_bd, e_ac, e_ad + e_bc} ∧
      LinearMap.ker (star + LinearMap.id) =
        Submodule.span ℂ
          {e_cd, e_ab - μ • e_bd, e_ad - (q ^ 2)⁻¹ • e_bc} ∧
      Module.finrank ℂ (LinearMap.ker (star - LinearMap.id)) = 3 ∧
      Module.finrank ℂ (LinearMap.ker (star + LinearMap.id)) = 3 := by sorry
