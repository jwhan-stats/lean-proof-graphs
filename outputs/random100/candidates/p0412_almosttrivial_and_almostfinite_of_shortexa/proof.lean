import Mathlib

/- accepted add_to_file helper 1 -/
lemma torsion_map_le {R A B : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
    (u : A →ₗ[R] B) :
    Submodule.torsion R A ≤ Submodule.comap u (Submodule.torsion R B) := by
  intro a ha
  change u a ∈ Submodule.torsion R B
  rw [Submodule.mem_torsion_iff] at ha ⊢
  rcases ha with ⟨r, hr⟩
  use r
  rw [Submonoid.smul_def] at hr ⊢
  rw [← map_smul, hr, map_zero]

lemma torsion_reflect_of_injective {R A B : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
    (u : A →ₗ[R] B) (hu : Function.Injective u) {a : A}
    (ha : u a ∈ Submodule.torsion R B) : a ∈ Submodule.torsion R A := by
  rw [Submodule.mem_torsion_iff] at ha ⊢
  rcases ha with ⟨r, hr⟩
  use r
  rw [Submonoid.smul_def] at hr ⊢
  apply hu
  rw [map_smul, hr, map_zero]

/- accepted add_to_file helper 2 -/
lemma exists_nonzero_annihilates_torsion_of_isNoetherian
    {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [IsNoetherian R M] :
    ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M, r • m = 0 := by
  have hfin : Module.Finite R (Submodule.torsion R M) :=
    Module.IsNoetherian.finite R (Submodule.torsion R M)
  rcases Submodule.annihilator_top_inter_nonZeroDivisors
      (M := Submodule.torsion R M) (Submodule.torsion_isTorsion (R := R) (M := M)) with ⟨r, hrann, hrnz⟩
  refine ⟨r, nonZeroDivisors.ne_zero hrnz, ?_⟩
  intro m
  exact Module.isTorsionBySet_annihilator_top R (Submodule.torsion R M)
    (a := ⟨r, hrann⟩) (x := m)

/- accepted add_to_file helper 3 -/
lemma torsion_right_annihilated_of_shortExact
    {R M₀ M₁ M₂ : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₀] [Module R M₁] [Module R M₂]
    (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂)
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hT₁ : ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₁, r • m = 0)
    [Module.Finite R (M₁ ⧸ Submodule.torsion R M₁)] [IsNoetherianRing R] :
    ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₂, r • m = 0 := by
  let Q₀ := M₀ ⧸ Submodule.torsion R M₀
  let Q₁ := M₁ ⧸ Submodule.torsion R M₁
  let qF : Q₀ →ₗ[R] Q₁ :=
    Submodule.mapQ (Submodule.torsion R M₀) (Submodule.torsion R M₁) f (torsion_map_le f)
  let C := Q₁ ⧸ qF.range
  haveI : Module.Finite R C := by
    exact Module.Finite.quotient R qF.range
  haveI : IsNoetherian R C := isNoetherian_of_isNoetherianRing_of_finite R C
  rcases exists_nonzero_annihilates_torsion_of_isNoetherian (R := R) (M := C) with ⟨b, hb0, hb⟩
  rcases hT₁ with ⟨a, ha0, ha⟩
  refine ⟨a * b, mul_ne_zero ha0 hb0, ?_⟩
  intro z
  rcases hg (z : M₂) with ⟨x, hx⟩
  have hclass : Submodule.Quotient.mk (Submodule.Quotient.mk x : Q₁) ∈ Submodule.torsion R C := by
    rw [Submodule.mem_torsion_iff]
    have hzmem : (z : M₂) ∈ Submodule.torsion R M₂ := z.property
    rw [Submodule.mem_torsion_iff] at hzmem
    rcases hzmem with ⟨c, hc⟩
    use c
    rw [Submonoid.smul_def] at hc ⊢
    have hgx : g ((c : R) • x) = 0 := by
      rw [map_smul, hx, hc]
    rcases ((hfg ((c : R) • x)).mp hgx) with ⟨y, hy⟩
    have hinner : (c : R) • (Submodule.Quotient.mk x : Q₁) =
        Submodule.Quotient.mk ((c : R) • x : M₁) := by
      calc
        (c : R) • (Submodule.Quotient.mk x : Q₁)
            = (c : R) • (Submodule.mkQ (Submodule.torsion R M₁)) x := rfl
        _ = (Submodule.mkQ (Submodule.torsion R M₁)) ((c : R) • x) := by
              exact (map_smul (Submodule.mkQ (Submodule.torsion R M₁)) (c : R) x).symm
        _ = Submodule.Quotient.mk ((c : R) • x : M₁) := rfl
    have houter : (c : R) • (Submodule.Quotient.mk (Submodule.Quotient.mk x : Q₁) : C) =
        Submodule.Quotient.mk ((c : R) • (Submodule.Quotient.mk x : Q₁) : Q₁) := by
      calc
        (c : R) • (Submodule.Quotient.mk (Submodule.Quotient.mk x : Q₁) : C)
            = (c : R) • (Submodule.mkQ qF.range) (Submodule.Quotient.mk x : Q₁) := rfl
        _ = (Submodule.mkQ qF.range) ((c : R) • (Submodule.Quotient.mk x : Q₁)) := by
              exact (map_smul (Submodule.mkQ qF.range) (c : R)
                (Submodule.Quotient.mk x : Q₁)).symm
        _ = Submodule.Quotient.mk ((c : R) • (Submodule.Quotient.mk x : Q₁) : Q₁) := rfl
    have hq : (c : R) • (Submodule.Quotient.mk (Submodule.Quotient.mk x : Q₁) : C) =
        (Submodule.Quotient.mk (qF (Submodule.Quotient.mk y : Q₀) : Q₁) : C) := by
      rw [houter, hinner, ← hy]
      exact congrArg (fun u : Q₁ => (Submodule.Quotient.mk u : C))
        (Submodule.mapQ_apply (Submodule.torsion R M₀)
          (Submodule.torsion R M₁) f y).symm
    rw [hq]
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  have hbclass := hb ⟨Submodule.Quotient.mk (Submodule.Quotient.mk x : Q₁), hclass⟩
  have hbmem : Submodule.Quotient.mk (b • x : M₁) ∈ qF.range := by
    have hbclass' : Submodule.Quotient.mk (Submodule.Quotient.mk (b • x : M₁) : Q₁) = (0 : C) := by
      have hv : b • (Submodule.Quotient.mk (Submodule.Quotient.mk x : Q₁) : C) = 0 := by
        exact congrArg Subtype.val hbclass
      have hinner : b • (Submodule.Quotient.mk x : Q₁) =
          Submodule.Quotient.mk (b • x : M₁) := by
        calc
          b • (Submodule.Quotient.mk x : Q₁)
              = b • (Submodule.mkQ (Submodule.torsion R M₁)) x := rfl
          _ = (Submodule.mkQ (Submodule.torsion R M₁)) (b • x) := by
                exact (map_smul (Submodule.mkQ (Submodule.torsion R M₁)) b x).symm
          _ = Submodule.Quotient.mk (b • x : M₁) := rfl
      have houter : b • (Submodule.Quotient.mk (Submodule.Quotient.mk x : Q₁) : C) =
          Submodule.Quotient.mk (b • (Submodule.Quotient.mk x : Q₁) : Q₁) := by
        calc
          b • (Submodule.Quotient.mk (Submodule.Quotient.mk x : Q₁) : C)
              = b • (Submodule.mkQ qF.range) (Submodule.Quotient.mk x : Q₁) := rfl
          _ = (Submodule.mkQ qF.range) (b • (Submodule.Quotient.mk x : Q₁)) := by
                exact (map_smul (Submodule.mkQ qF.range) b
                  (Submodule.Quotient.mk x : Q₁)).symm
          _ = Submodule.Quotient.mk (b • (Submodule.Quotient.mk x : Q₁) : Q₁) := rfl
      rw [houter, hinner] at hv
      exact hv
    rw [Submodule.Quotient.mk_eq_zero] at hbclass'
    exact hbclass'
  rcases hbmem with ⟨q₀, hq₀⟩
  rcases Submodule.Quotient.mk_surjective (Submodule.torsion R M₀) q₀ with ⟨y, rfl⟩
  have hqmap : qF (Submodule.Quotient.mk y : Q₀) = Submodule.Quotient.mk (f y : M₁) := by
    change (Submodule.mapQ (Submodule.torsion R M₀) (Submodule.torsion R M₁) f
      (torsion_map_le f)) (Submodule.Quotient.mk y) = Submodule.Quotient.mk (f y)
    exact Submodule.mapQ_apply (Submodule.torsion R M₀) (Submodule.torsion R M₁) f y
  have hq₀' : Submodule.Quotient.mk (b • x : M₁) = Submodule.Quotient.mk (f y : M₁) :=
    hq₀.symm.trans hqmap
  have hdiff : b • x - f y ∈ Submodule.torsion R M₁ := by
    exact (Submodule.Quotient.eq (Submodule.torsion R M₁)).mp hq₀'
  have hakill : a • (b • x - f y) = 0 := by
    have := congrArg Subtype.val (ha ⟨b • x - f y, hdiff⟩)
    simpa using this
  have hgkill : g (a • (b • x - f y)) = 0 := by
    rw [hakill, map_zero]
  have hgf : g (f y) = 0 := by
    exact (hfg (f y)).mpr ⟨y, rfl⟩
  have hmain : (a * b) • g x = 0 := by
    rw [map_smul, map_sub, map_smul, hgf, sub_zero] at hgkill
    rw [smul_smul] at hgkill
    exact hgkill
  ext
  rw [hx] at hmain
  exact hmain

/- accepted add_to_file helper 4 -/
lemma finite_quotient_middle_of_shortExact
    {R M₀ M₁ M₂ : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₀] [Module R M₁] [Module R M₂]
    (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂)
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hT₂ : ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₂, r • m = 0)
    [Module.Finite R (M₀ ⧸ Submodule.torsion R M₀)]
    [Module.Finite R (M₂ ⧸ Submodule.torsion R M₂)] [IsNoetherianRing R] :
    Module.Finite R (M₁ ⧸ Submodule.torsion R M₁) := by
  let Q₀ := M₀ ⧸ Submodule.torsion R M₀
  let Q₁ := M₁ ⧸ Submodule.torsion R M₁
  let Q₂ := M₂ ⧸ Submodule.torsion R M₂
  let qF : Q₀ →ₗ[R] Q₁ :=
    Submodule.mapQ (Submodule.torsion R M₀) (Submodule.torsion R M₁) f (torsion_map_le f)
  let qG : Q₁ →ₗ[R] Q₂ :=
    Submodule.mapQ (Submodule.torsion R M₁) (Submodule.torsion R M₂) g (torsion_map_le g)
  have hqG_surj : Function.Surjective qG := by
    intro z
    rcases Submodule.Quotient.mk_surjective (Submodule.torsion R M₂) z with ⟨m, rfl⟩
    rcases hg m with ⟨x, hx⟩
    use Submodule.Quotient.mk x
    have hmap : qG (Submodule.Quotient.mk x : Q₁) = Submodule.Quotient.mk (g x : M₂) := by
      change (Submodule.mapQ (Submodule.torsion R M₁) (Submodule.torsion R M₂) g
        (torsion_map_le g)) (Submodule.Quotient.mk x) = Submodule.Quotient.mk (g x)
      exact Submodule.mapQ_apply (Submodule.torsion R M₁) (Submodule.torsion R M₂) g x
    rw [hmap, hx]
  rcases hT₂ with ⟨b, hb0, hb⟩
  let bm : Q₁ →ₗ[R] Q₁ := b • LinearMap.id
  have hLfg : qF.range.FG := by
    exact Module.Finite.iff_fg.mp (Module.Finite.range qF)
  have hmaple : Submodule.map bm qG.ker ≤ qF.range := by
    intro y hy
    rw [Submodule.mem_map] at hy
    rcases hy with ⟨x, hxK, rfl⟩
    rcases Submodule.Quotient.mk_surjective (Submodule.torsion R M₁) x with ⟨m, rfl⟩
    have hzero : qG (Submodule.Quotient.mk m : Q₁) = 0 := LinearMap.mem_ker.mp hxK
    have hqGmap : qG (Submodule.Quotient.mk m : Q₁) = Submodule.Quotient.mk (g m : M₂) := by
      change (Submodule.mapQ (Submodule.torsion R M₁) (Submodule.torsion R M₂) g
        (torsion_map_le g)) (Submodule.Quotient.mk m) = Submodule.Quotient.mk (g m)
      exact Submodule.mapQ_apply (Submodule.torsion R M₁) (Submodule.torsion R M₂) g m
    have hgtors : g m ∈ Submodule.torsion R M₂ := by
      rw [hqGmap, Submodule.Quotient.mk_eq_zero] at hzero
      exact hzero
    have hbkill : b • g m = 0 := by
      have := congrArg Subtype.val (hb ⟨g m, hgtors⟩)
      simpa using this
    have hgb : g (b • m) = 0 := by
      rw [map_smul, hbkill]
    rcases ((hfg (b • m)).mp hgb) with ⟨y, hy⟩
    change b • (Submodule.Quotient.mk m : Q₁) ∈ qF.range
    refine ⟨Submodule.Quotient.mk y, ?_⟩
    have hqFmap : qF (Submodule.Quotient.mk y : Q₀) = Submodule.Quotient.mk (f y : M₁) := by
      change (Submodule.mapQ (Submodule.torsion R M₀) (Submodule.torsion R M₁) f
        (torsion_map_le f)) (Submodule.Quotient.mk y) = Submodule.Quotient.mk (f y)
      exact Submodule.mapQ_apply (Submodule.torsion R M₀) (Submodule.torsion R M₁) f y
    rw [hqFmap, hy]
    calc
      Submodule.Quotient.mk (b • m : M₁)
          = b • (Submodule.mkQ (Submodule.torsion R M₁)) m := by
            exact map_smul (Submodule.mkQ (Submodule.torsion R M₁)) b m
      _ = b • (Submodule.Quotient.mk m : Q₁) := rfl
  have hmapfg : (Submodule.map bm qG.ker).FG :=
    Submodule.FG.of_le hLfg hmaple
  have hkerbot : qG.ker ⊓ bm.ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rcases hx with ⟨-, hxb⟩
    have hbzero : bm x = 0 := LinearMap.mem_ker.mp hxb
    change b • x = 0 at hbzero
    apply smul_right_injective Q₁ hb0
    change b • x = b • (0 : Q₁)
    rw [hbzero, smul_zero]
  have hkerfg : (qG.ker ⊓ bm.ker).FG := by
    rw [hkerbot]
    exact Submodule.fg_bot
  have hKfg : qG.ker.FG := Submodule.fg_of_fg_map_of_fg_inf_ker bm hmapfg hkerfg
  haveI : Module.Finite R qG.ker := Module.Finite.iff_fg.mpr hKfg
  have hexact : Function.Exact qG.ker.subtype qG := by
    intro x
    constructor
    · intro hx
      exact ⟨⟨x, LinearMap.mem_ker.mpr hx⟩, rfl⟩
    · intro hx
      rcases hx with ⟨y, hy⟩
      have : qG (y : Q₁) = 0 := LinearMap.mem_ker.mp y.property
      rw [← hy]
      exact this
  exact Module.Finite.of_exact hexact hqG_surj

/- accepted add_to_file helper 5 -/
lemma torsion_middle_annihilated_of_shortExact
    {R M₀ M₁ M₂ : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₀] [Module R M₁] [Module R M₂]
    (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂)
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hT₀ : ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₀, r • m = 0)
    (hT₂ : ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₂, r • m = 0) :
    ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₁, r • m = 0 := by
  rcases hT₀ with ⟨a, ha0, ha⟩
  rcases hT₂ with ⟨b, hb0, hb⟩
  refine ⟨a * b, mul_ne_zero ha0 hb0, ?_⟩
  intro z
  have hgz : g (z : M₁) ∈ Submodule.torsion R M₂ := torsion_map_le g z.property
  have hbkill : b • g (z : M₁) = 0 := by
    have := congrArg Subtype.val (hb ⟨g (z : M₁), hgz⟩)
    simpa using this
  have hgb : g (b • (z : M₁)) = 0 := by
    rw [map_smul, hbkill]
  rcases ((hfg (b • (z : M₁))).mp hgb) with ⟨y, hy⟩
  have hfy : f y ∈ Submodule.torsion R M₁ := by
    rw [hy]
    exact (Submodule.torsion R M₁).smul_mem b z.property
  have hytor : y ∈ Submodule.torsion R M₀ :=
    torsion_reflect_of_injective f hf hfy
  have hakill : a • y = 0 := by
    have := congrArg Subtype.val (ha ⟨y, hytor⟩)
    simpa using this
  have hfzero : f (a • y) = 0 := by
    rw [hakill, map_zero]
  have hmain : (a * b) • (z : M₁) = 0 := by
    rw [map_smul, hy] at hfzero
    rw [smul_smul] at hfzero
    exact hfzero
  ext
  exact hmain

/- accepted add_to_file helper 6 -/
lemma finite_quotient_left_of_shortExact
    {R M₀ M₁ : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M₀] [AddCommGroup M₁]
    [Module R M₀] [Module R M₁]
    (f : M₀ →ₗ[R] M₁) (hf : Function.Injective f)
    [Module.Finite R (M₁ ⧸ Submodule.torsion R M₁)] [IsNoetherianRing R] :
    Module.Finite R (M₀ ⧸ Submodule.torsion R M₀) := by
  let Q₀ := M₀ ⧸ Submodule.torsion R M₀
  let Q₁ := M₁ ⧸ Submodule.torsion R M₁
  let qF : Q₀ →ₗ[R] Q₁ :=
    Submodule.mapQ (Submodule.torsion R M₀) (Submodule.torsion R M₁) f (torsion_map_le f)
  have hqF_inj : Function.Injective qF := by
    intro x y hxy
    rcases Submodule.Quotient.mk_surjective (Submodule.torsion R M₀) x with ⟨x, rfl⟩
    rcases Submodule.Quotient.mk_surjective (Submodule.torsion R M₀) y with ⟨y, rfl⟩
    have hxmap : qF (Submodule.Quotient.mk x : Q₀) = Submodule.Quotient.mk (f x : M₁) := by
      change (Submodule.mapQ (Submodule.torsion R M₀) (Submodule.torsion R M₁) f
        (torsion_map_le f)) (Submodule.Quotient.mk x) = Submodule.Quotient.mk (f x)
      exact Submodule.mapQ_apply (Submodule.torsion R M₀) (Submodule.torsion R M₁) f x
    have hymap : qF (Submodule.Quotient.mk y : Q₀) = Submodule.Quotient.mk (f y : M₁) := by
      change (Submodule.mapQ (Submodule.torsion R M₀) (Submodule.torsion R M₁) f
        (torsion_map_le f)) (Submodule.Quotient.mk y) = Submodule.Quotient.mk (f y)
      exact Submodule.mapQ_apply (Submodule.torsion R M₀) (Submodule.torsion R M₁) f y
    rw [hxmap, hymap] at hxy
    have hdiff : f x - f y ∈ Submodule.torsion R M₁ :=
      (Submodule.Quotient.eq (Submodule.torsion R M₁)).mp hxy
    have hfdiff : f (x - y) ∈ Submodule.torsion R M₁ := by
      rw [map_sub]
      exact hdiff
    have htor : x - y ∈ Submodule.torsion R M₀ :=
      torsion_reflect_of_injective f hf hfdiff
    exact (Submodule.Quotient.eq (Submodule.torsion R M₀)).mpr htor
  haveI : IsNoetherian R Q₁ := isNoetherian_of_isNoetherianRing_of_finite R Q₁
  exact Module.Finite.of_injective qF hqF_inj

/- accepted add_to_file helper 7 -/
lemma finite_quotient_right_of_shortExact
    {R M₁ M₂ : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₁] [Module R M₂]
    (g : M₁ →ₗ[R] M₂) (hg : Function.Surjective g)
    [Module.Finite R (M₁ ⧸ Submodule.torsion R M₁)] :
    Module.Finite R (M₂ ⧸ Submodule.torsion R M₂) := by
  let Q₁ := M₁ ⧸ Submodule.torsion R M₁
  let Q₂ := M₂ ⧸ Submodule.torsion R M₂
  let qG : Q₁ →ₗ[R] Q₂ :=
    Submodule.mapQ (Submodule.torsion R M₁) (Submodule.torsion R M₂) g (torsion_map_le g)
  have hqG_surj : Function.Surjective qG := by
    intro z
    rcases Submodule.Quotient.mk_surjective (Submodule.torsion R M₂) z with ⟨m, rfl⟩
    rcases hg m with ⟨x, hx⟩
    use Submodule.Quotient.mk x
    have hmap : qG (Submodule.Quotient.mk x : Q₁) = Submodule.Quotient.mk (g x : M₂) := by
      change (Submodule.mapQ (Submodule.torsion R M₁) (Submodule.torsion R M₂) g
        (torsion_map_le g)) (Submodule.Quotient.mk x) = Submodule.Quotient.mk (g x)
      exact Submodule.mapQ_apply (Submodule.torsion R M₁) (Submodule.torsion R M₂) g x
    rw [hmap, hx]
  exact Module.Finite.of_surjective qG hqG_surj

/- accepted add_to_file helper 8 -/
lemma torsion_left_annihilated_of_shortExact
    {R M₀ M₁ : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M₀] [AddCommGroup M₁]
    [Module R M₀] [Module R M₁]
    (f : M₀ →ₗ[R] M₁) (hf : Function.Injective f)
    (hT₁ : ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₁, r • m = 0) :
    ∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₀, r • m = 0 := by
  rcases hT₁ with ⟨a, ha0, ha⟩
  refine ⟨a, ha0, ?_⟩
  intro z
  have hfz : f (z : M₀) ∈ Submodule.torsion R M₁ := torsion_map_le f z.property
  have hkill : a • f (z : M₀) = 0 := by
    have := congrArg Subtype.val (ha ⟨f (z : M₀), hfz⟩)
    simpa using this
  have hfkill : f (a • (z : M₀)) = 0 := by
    rw [map_smul, hkill]
  have hmain : a • (z : M₀) = 0 := hf (by rw [hfkill, map_zero])
  ext
  exact hmain

/- verified submission -/
theorem almostTrivial_and_almostFinite_of_shortExact
    {R : Type*} [CommRing R] [IsDomain R]
    {M₀ M₁ M₂ : Type*}
    [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₀] [Module R M₁] [Module R M₂]
    (f : M₀ →ₗ[R] M₁) (g : M₁ →ₗ[R] M₂)
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    ((∃ r : R, r ≠ 0 ∧ ∀ m : M₁, r • m = 0) ↔
      (∃ r : R, r ≠ 0 ∧ ∀ m : M₀, r • m = 0) ∧
      (∃ r : R, r ≠ 0 ∧ ∀ m : M₂, r • m = 0)) ∧
    (IsNoetherianRing R →
      (((∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₁, r • m = 0) ∧
          Module.Finite R (M₁ ⧸ Submodule.torsion R M₁)) ↔
        ((∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₀, r • m = 0) ∧
          Module.Finite R (M₀ ⧸ Submodule.torsion R M₀)) ∧
        ((∃ r : R, r ≠ 0 ∧ ∀ m : Submodule.torsion R M₂, r • m = 0) ∧
          Module.Finite R (M₂ ⧸ Submodule.torsion R M₂)))) := by
  constructor
  · constructor
    · intro h
      rcases h with ⟨r, hr0, hr⟩
      constructor
      · refine ⟨r, hr0, ?_⟩
        intro m
        apply hf
        rw [map_smul, hr (f m), map_zero]
      · refine ⟨r, hr0, ?_⟩
        intro z
        rcases hg z with ⟨m, rfl⟩
        rw [← map_smul, hr m, map_zero]
    · intro h
      rcases h with ⟨⟨a, ha0, ha⟩, ⟨b, hb0, hb⟩⟩
      refine ⟨a * b, mul_ne_zero ha0 hb0, ?_⟩
      intro m
      have hgb : g (b • m) = 0 := by
        rw [map_smul, hb (g m)]
      rcases ((hfg (b • m)).mp hgb) with ⟨y, hy⟩
      have hfy : f (a • y) = 0 := by
        rw [ha y, map_zero]
      rw [map_smul, hy] at hfy
      rw [smul_smul] at hfy
      exact hfy
  · intro hNoeth
    haveI : IsNoetherianRing R := hNoeth
    constructor
    · intro hA
      rcases hA with ⟨hT₁, hF₁⟩
      haveI : Module.Finite R (M₁ ⧸ Submodule.torsion R M₁) := hF₁
      have hT₀ := torsion_left_annihilated_of_shortExact f hf hT₁
      have hF₀ := finite_quotient_left_of_shortExact f hf
      have hF₂ := finite_quotient_right_of_shortExact g hg
      have hT₂ := torsion_right_annihilated_of_shortExact f g hfg hg hT₁
      exact ⟨⟨hT₀, hF₀⟩, ⟨hT₂, hF₂⟩⟩
    · intro hA
      rcases hA with ⟨⟨hT₀, hF₀⟩, ⟨hT₂, hF₂⟩⟩
      haveI : Module.Finite R (M₀ ⧸ Submodule.torsion R M₀) := hF₀
      haveI : Module.Finite R (M₂ ⧸ Submodule.torsion R M₂) := hF₂
      have hT₁ := torsion_middle_annihilated_of_shortExact f g hf hfg hT₀ hT₂
      have hF₁ := finite_quotient_middle_of_shortExact f g hfg hg hT₂
      exact ⟨hT₁, hF₁⟩
