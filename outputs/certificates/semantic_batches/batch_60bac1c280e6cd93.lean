import GraphCertificate
import Mathlib

namespace Rollout_p0381_two_minimal_missing_faces_deletion

-- graph_id: p0381_two_minimal_missing_faces_deletion
-- topology_sha256: 05d1d90c7d2ac7843a9bc9fde3759270e612281999887e2da50afe8bd3dbe0bf
/- verified submission -/
theorem two_minimal_missing_faces_deletion
    (m : ℕ) (K : Set (Set ℕ)) (I J : Set ℕ)
    (hK_downward : IsLowerSet K)
    (hK_vertices : ∀ ⦃S : Set ℕ⦄, S ∈ K → S ⊆ Set.Icc 1 m)
    (hIJ : I ≠ J)
    (hmissing : ∀ S : Set ℕ,
      Minimal (fun T : Set ℕ => T ⊆ Set.Icc 1 m ∧ T ∉ K) S ↔
        S = I ∨ S = J)
    (hunion : I ∪ J = Set.Icc 1 m)
    (hinter : (I ∩ J).Nonempty)
    {w : ℕ} (hw : w ∈ I ∩ J) :
    ∀ S : Set ℕ, S ⊆ Set.Icc 1 m \ {w} → S ∈ K := by
  intro S hS
  by_contra hSK
  let C : Set (Set ℕ) :=
    {T : Set ℕ | T ⊆ Set.Icc 1 m ∧ T ∉ K ∧ T ⊆ S}
  have hSV : S ⊆ Set.Icc 1 m := hS.trans Set.diff_subset
  have hCfinite : C.Finite := by
    exact (Set.finite_Icc 1 m).powerset.subset (by
      intro T hT
      exact hT.1)
  have hCnonempty : C.Nonempty := by
    exact ⟨S, hSV, hSK, subset_rfl⟩
  obtain ⟨L, hLminC⟩ := hCfinite.exists_minimal hCnonempty
  have hLmin : Minimal (fun T : Set ℕ => T ⊆ Set.Icc 1 m ∧ T ∉ K) L := by
    constructor
    · exact ⟨hLminC.1.1, hLminC.1.2.1⟩
    · intro T hT hTL
      have hTC : T ∈ C := by
        exact ⟨hT.1, hT.2, hTL.trans hLminC.1.2.2⟩
      exact hLminC.2 hTC hTL
  rcases (hmissing L).mp hLmin with hLI | hLJ
  · have hwL : w ∈ L := by
      rw [hLI]
      exact hw.1
    have hwS : w ∈ S := hLminC.1.2.2 hwL
    exact (hS hwS).2 rfl
  · have hwL : w ∈ L := by
      rw [hLJ]
      exact hw.2
    have hwS : w ∈ S := hLminC.1.2.2 hwL
    exact (hS hwS).2 rfl

end Rollout_p0381_two_minimal_missing_faces_deletion

#check_dependency_graph "Rollout_p0381_two_minimal_missing_faces_deletion.two_minimal_missing_faces_deletion" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"S ∈ K\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hmissing\",\"statement\":\"∀ (S : Set ℕ), Minimal (fun T => T ⊆ Set.Icc 1 m ∧ T ∉ K) S ↔ S = I ∨ S = J\"},{\"name\":\"hw\",\"statement\":\"w ∈ I ∩ J\"},{\"name\":\"hS\",\"statement\":\"S ⊆ Set.Icc 1 m \\\\ {w}\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0381_two_minimal_missing_faces_deletion\",\"reconstructedProofSha256\":\"688574ff63a98dba3908ff93b2258bc637f331384487238fbd5f3a16f1a161d8\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p0381_two_minimal_missing_faces_deletion.two_minimal_missing_faces_deletion\",\"topologySha256\":\"05d1d90c7d2ac7843a9bc9fde3759270e612281999887e2da50afe8bd3dbe0bf\"}"

namespace Rollout_p0390_linfty_eq_erosion_distance

-- graph_id: p0390_linfty_eq_erosion_distance
-- topology_sha256: 7169e0ab7d33b8a0fb0a4a39cd644007ca5765397d525bbf754de2f861f69f8d
/- accepted add_to_file helper 1 -/
lemma erosion_iff_pointwise {X : Type*} (f g : X → ℝ) (ε : NNReal) :
    (∀ a b : ℝ, a < b →
      g ⁻¹' Set.Icc a b ⊆ f ⁻¹' Set.Icc (a - (ε : ℝ)) (b + (ε : ℝ)) ∧
      f ⁻¹' Set.Icc a b ⊆ g ⁻¹' Set.Icc (a - (ε : ℝ)) (b + (ε : ℝ))) ↔
    ∀ x : X, |f x - g x| ≤ (ε : ℝ) := by
  constructor
  · intro h x
    apply le_of_forall_pos_le_add
    intro δ hδ
    have hg : x ∈ g ⁻¹' Set.Icc (g x - δ) (g x + δ) := by
      constructor <;> linarith
    have hf := ((h (g x - δ) (g x + δ) (by linarith)).1 hg)
    rw [abs_le]
    constructor <;> linarith [hf.1, hf.2]
  · intro h a b hab
    constructor
    · intro x hx
      have hfg := (abs_sub_le_iff.mp (h x))
      constructor <;> linarith [hx.1, hx.2, hfg.1, hfg.2]
    · intro x hx
      have hfg := (abs_sub_le_iff.mp (h x))
      constructor <;> linarith [hx.1, hx.2, hfg.1, hfg.2]

/- verified submission -/
theorem linfty_eq_erosion_distance {X : Type*} (f g : X → ℝ) :
    (⨆ x : X, ENNReal.ofReal |f x - g x|) =
      sInf {d : ENNReal | ∃ ε : NNReal,
        d = (ε : ENNReal) ∧
        ∀ a b : ℝ, a < b →
          g ⁻¹' Set.Icc a b ⊆
              f ⁻¹' Set.Icc (a - (ε : ℝ)) (b + (ε : ℝ)) ∧
          f ⁻¹' Set.Icc a b ⊆
              g ⁻¹' Set.Icc (a - (ε : ℝ)) (b + (ε : ℝ)) } := by
  let L : ENNReal := ⨆ x : X, ENNReal.ofReal |f x - g x|
  let D : Set ENNReal := {d : ENNReal | ∃ ε : NNReal,
        d = (ε : ENNReal) ∧
        ∀ a b : ℝ, a < b →
          g ⁻¹' Set.Icc a b ⊆
              f ⁻¹' Set.Icc (a - (ε : ℝ)) (b + (ε : ℝ)) ∧
          f ⁻¹' Set.Icc a b ⊆
              g ⁻¹' Set.Icc (a - (ε : ℝ)) (b + (ε : ℝ)) }
  change L = sInf D
  apply le_antisymm
  · apply le_sInf
    intro d hd
    rcases hd with ⟨ε, rfl, hE⟩
    apply iSup_le
    intro x
    have hx : |f x - g x| ≤ (ε : ℝ) :=
      (erosion_iff_pointwise f g ε).mp hE x
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hx
  · by_cases hL : L = ⊤
    · rw [hL]
      exact le_top
    · apply sInf_le
      refine ⟨L.toNNReal, (ENNReal.coe_toNNReal hL).symm, ?_⟩
      apply (erosion_iff_pointwise f g L.toNNReal).mpr
      intro x
      have hxE : ENNReal.ofReal |f x - g x| ≤ (L.toNNReal : ENNReal) := by
        rw [ENNReal.coe_toNNReal hL]
        exact le_iSup (fun x : X => ENNReal.ofReal |f x - g x|) x
      exact (ENNReal.ofReal_le_coe.mp hxE)

end Rollout_p0390_linfty_eq_erosion_distance

#check_dependency_graph "Rollout_p0390_linfty_eq_erosion_distance.linfty_eq_erosion_distance" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"⨆ x, ENNReal.ofReal |f x - g x| = sInf {d | ∃ ε, d = ↑ε ∧ ∀ (a b : ℝ), a < b → g ⁻¹' Set.Icc a b ⊆ f ⁻¹' Set.Icc (a - ↑ε) (b + ↑ε) ∧ f ⁻¹' Set.Icc a b ⊆ g ⁻¹' Set.Icc (a - ↑ε) (b + ↑ε)}\"},\"graphEdgeId\":\"h_goal\",\"premises\":[],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0390_linfty_eq_erosion_distance\",\"reconstructedProofSha256\":\"deefde5b92869d0933b3be406052bb581b3cd1d21e4d80c11cfb23781d849cf0\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p0390_linfty_eq_erosion_distance.linfty_eq_erosion_distance\",\"topologySha256\":\"7169e0ab7d33b8a0fb0a4a39cd644007ca5765397d525bbf754de2f861f69f8d\"}"

namespace Rollout_p0411_finite_product_grid_cell_properties

-- graph_id: p0411_finite_product_grid_cell_properties
-- topology_sha256: 0432853c1183bcd36cea3e1bb024047f35166319b34df2e909ba2c44786a23f2
/- accepted add_to_file helper 1 -/
lemma isGreatest_grid_lower_sup_right {α : Type*} [LinearOrder α]
    {Q : Finset α} {x y y' : α}
    (hx : IsGreatest {a : α | a ∈ Q ∧ a ≤ x} y)
    (hy' : y' ∈ Q) (hyy' : y ≤ y') :
    IsGreatest {a : α | a ∈ Q ∧ a ≤ y' ⊔ x} y' := by
  constructor
  · exact ⟨hy', le_sup_left⟩
  · intro a ha
    rcases ha with ⟨haQ, hle⟩
    rcases (le_sup_iff.mp hle) with hay' | hax
    · exact hay'
    · exact (hx.2 ⟨haQ, hax⟩).trans hyy'

lemma isGreatest_grid_lower_sup {α : Type*} [LinearOrder α]
    {Q : Finset α} {x z y : α}
    (hx : IsGreatest {a : α | a ∈ Q ∧ a ≤ x} y)
    (hz : IsGreatest {a : α | a ∈ Q ∧ a ≤ z} y) :
    IsGreatest {a : α | a ∈ Q ∧ a ≤ x ⊔ z} y := by
  constructor
  · exact ⟨hx.1.1, le_trans hx.1.2 le_sup_left⟩
  · intro a ha
    rcases ha with ⟨haQ, hle⟩
    rcases (le_sup_iff.mp hle) with hax | haz
    · exact hx.2 ⟨haQ, hax⟩
    · exact hz.2 ⟨haQ, haz⟩

lemma isGreatest_grid_lower_inf {α : Type*} [LinearOrder α]
    {Q : Finset α} {x z y : α}
    (hx : IsGreatest {a : α | a ∈ Q ∧ a ≤ x} y)
    (hz : IsGreatest {a : α | a ∈ Q ∧ a ≤ z} y) :
    IsGreatest {a : α | a ∈ Q ∧ a ≤ x ⊓ z} y := by
  constructor
  · exact ⟨hx.1.1, le_inf hx.1.2 hz.1.2⟩
  · intro a ha
    rcases ha with ⟨haQ, hle⟩
    exact hx.2 ⟨haQ, le_trans hle inf_le_left⟩

/- verified submission -/
theorem finite_product_grid_cell_properties
    (n : ℕ) (T : Fin n → Type*) [∀ i, LinearOrder (T i)]
    [∀ i, Nontrivial (T i)] (Q : ∀ i, Finset (T i)) :
    let P := ∀ i, T i
    let grid : Set P := {q | ∀ i, q i ∈ Q i}
    let upper : Set P := {x | ∃ q ∈ grid, q ≤ x}
    let cell (y : P) : Set P :=
      {x | x ∈ upper ∧ ∀ i, IsGreatest {a : T i | a ∈ Q i ∧ a ≤ x i} (y i)}
    (∀ ⦃x y y' : P⦄, x ∈ cell y → y' ∈ grid → y ≤ y' →
        y' ⊔ x ∈ cell y' ∧ ∃ x' ∈ cell y', x ≤ x') ∧
      ∀ y ∈ grid, IsSublattice (cell y) := by
  dsimp only
  constructor
  · intro x y y' hx hy' hyy'
    have hjoin : y' ⊔ x ∈
        {x | (∃ q ∈ ({q | ∀ i, q i ∈ Q i} : Set (∀ i, T i)), q ≤ x) ∧
          ∀ i, IsGreatest {a : T i | a ∈ Q i ∧ a ≤ x i} (y' i)} := by
      constructor
      · rcases hx.1 with ⟨q, hq, hqx⟩
        exact ⟨q, hq, hqx.trans le_sup_right⟩
      · intro i
        exact isGreatest_grid_lower_sup_right (hx.2 i) (hy' i) (hyy' i)
    exact ⟨hjoin, y' ⊔ x, hjoin, le_sup_right⟩
  · intro y hy
    refine IsSublattice.mk ?_ ?_
    · intro x hx z hz
      constructor
      · rcases hx.1 with ⟨q, hq, hqx⟩
        rcases hz.1 with ⟨r, hr, hrz⟩
        refine ⟨q ⊔ r, ?_, ?_⟩
        · intro i
          rcases max_choice (q i) (r i) with hmax | hmax
          · rw [Pi.sup_apply, hmax]
            exact hq i
          · rw [Pi.sup_apply, hmax]
            exact hr i
        · exact sup_le (hqx.trans le_sup_left) (hrz.trans le_sup_right)
      · intro i
        exact isGreatest_grid_lower_sup (hx.2 i) (hz.2 i)
    · intro x hx z hz
      constructor
      · rcases hx.1 with ⟨q, hq, hqx⟩
        rcases hz.1 with ⟨r, hr, hrz⟩
        refine ⟨q ⊓ r, ?_, ?_⟩
        · intro i
          rcases min_choice (q i) (r i) with hmin | hmin
          · rw [Pi.inf_apply, hmin]
            exact hq i
          · rw [Pi.inf_apply, hmin]
            exact hr i
        · exact le_inf (inf_le_left.trans hqx) (inf_le_right.trans hrz)
      · intro i
        exact isGreatest_grid_lower_inf (hx.2 i) (hz.2 i)

end Rollout_p0411_finite_product_grid_cell_properties

#check_dependency_graph "Rollout_p0411_finite_product_grid_cell_properties.finite_product_grid_cell_properties" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let P := (i : Fin n) → T i; let grid := {q | ∀ (i : Fin n), q i ∈ Q i}; let upper := {x | ∃ q ∈ grid, q ≤ x}; let cell := fun y => {x | x ∈ upper ∧ ∀ (i : Fin n), IsGreatest {a | a ∈ Q i ∧ a ≤ x i} (y i)}; (∀ ⦃x y y' : P⦄, x ∈ cell y → y' ∈ grid → y ≤ y' → y' ⊔ x ∈ cell y' ∧ ∃ x' ∈ cell y', x ≤ x') ∧ ∀ y ∈ grid, IsSublattice (cell y)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0411_finite_product_grid_cell_properties\",\"reconstructedProofSha256\":\"dbfe863f469f94092932c3af15c892979142ffb530a96d4ab84b3be8be7d0f1a\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p0411_finite_product_grid_cell_properties.finite_product_grid_cell_properties\",\"topologySha256\":\"0432853c1183bcd36cea3e1bb024047f35166319b34df2e909ba2c44786a23f2\"}"

namespace Rollout_p0770_two_bilinear_products_associative_iff

-- graph_id: p0770_two_bilinear_products_associative_iff
-- topology_sha256: 03737d53c077ded934bac5dc575473f2664b4ae966ca594aa2a3036fff53279b
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

end Rollout_p0770_two_bilinear_products_associative_iff

#check_dependency_graph "Rollout_p0770_two_bilinear_products_associative_iff.two_bilinear_products_associative_iff" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let dot := fun x x_1 => match x with | (a, b) => match x_1 with | (c, d) => ((mul₁ a) c + (mul₂ a) d, (mul₂ b) d + (mul₁ b) c); let diamond := fun x x_1 => match x with | (a, b) => match x_1 with | (c, d) => ((mul₁ a) c + (mul₂ b) c, (mul₂ b) d + (mul₁ a) d); let compatibility := (Std.Associative fun x y => (mul₁ x) y) ∧ (Std.Associative fun x y => (mul₂ x) y) ∧ (∀ (x y z : A), (mul₂ ((mul₁ x) y)) z = (mul₁ x) ((mul₂ y) z)) ∧ ∀ (x y z : A), (mul₁ ((mul₂ x) y)) z = (mul₂ x) ((mul₁ y) z); (compatibility ↔ Std.Associative dot) ∧ (Std.Associative dot ↔ Std.Associative diamond)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0770_two_bilinear_products_associative_iff\",\"reconstructedProofSha256\":\"0bbf4e9c50fcbee4d833d82105e89734461c1a88baeeed92d8bf81803c21a5c2\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p0770_two_bilinear_products_associative_iff.two_bilinear_products_associative_iff\",\"topologySha256\":\"03737d53c077ded934bac5dc575473f2664b4ae966ca594aa2a3036fff53279b\"}"

namespace Rollout_p0818_intertwining_orbit_cocycle

-- graph_id: p0818_intertwining_orbit_cocycle
-- topology_sha256: 7c24cee0092f3df02efea7f89fb4a675db6848999deb567605152a521cf9f3f3
/- accepted add_to_file helper 1 -/
lemma orbit_factor_identity {G : Type*} [CommGroup G]
    (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : G) :
    (a₁ * b₁⁻¹) * (a₂ * b₂⁻¹)⁻¹ * (a₃ * b₃⁻¹) * (a₄ * b₄⁻¹)⁻¹ =
      (a₁ * a₂⁻¹ * a₃ * a₄⁻¹) * (b₁ * b₂⁻¹ * b₃ * b₄⁻¹)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/- accepted add_to_file helper 2 -/
lemma coboundary_factor_identity {G : Type*} [CommGroup G]
    (C' C x₁ x₂ x₃ y₁ y₂ y₃ : G) :
    (C' * (x₁ * x₂⁻¹ * x₃)) * (C * (y₁ * y₂⁻¹ * y₃))⁻¹ =
      (C' * C⁻¹) *
        ((x₁ * y₁⁻¹) * (x₂ * y₂⁻¹)⁻¹ * (x₃ * y₃⁻¹)) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

/- verified submission -/
theorem intertwining_orbit_cocycle
    {Γ A : Type*} [Group Γ] [AddCommGroup A] [DistribMulAction Γ A]
    {n n' : ℕ} (hn : 1 ≤ n) (hn' : 1 ≤ n')
    (ρ : Γ →* Equiv.Perm (Fin n)) (ρ' : Γ →* Equiv.Perm (Fin n'))
    (α : Γ → Γ → Γ → A)
    (hα₁ : ∀ g h : Γ, α 1 g h = 0)
    (hα₂ : ∀ g h : Γ, α g 1 h = 0)
    (hα₃ : ∀ g h : Γ, α g h 1 = 0)
    (hαcocycle : ∀ g h k l : Γ,
      g • α h k l - α (g * h) k l + α g (h * k) l -
          α g h (k * l) + α g h k = 0)
    (β : A →+ (Fin n → Additive ℂˣ))
    (β' : A →+ (Fin n' → Additive ℂˣ))
    (hβequiv : ∀ (g : Γ) (u : A) (i : Fin n),
      β (g • u) i = β u ((ρ g)⁻¹ i))
    (hβ'equiv : ∀ (g : Γ) (u : A) (i' : Fin n'),
      β' (g • u) i' = β' u ((ρ' g)⁻¹ i'))
    (c : Γ → Γ → Fin n → ℂˣ)
    (c' : Γ → Γ → Fin n' → ℂˣ)
    (hc₁ : ∀ (g : Γ) (i : Fin n), c 1 g i = 1)
    (hc₂ : ∀ (g : Γ) (i : Fin n), c g 1 i = 1)
    (hc'₁ : ∀ (g : Γ) (i' : Fin n'), c' 1 g i' = 1)
    (hc'₂ : ∀ (g : Γ) (i' : Fin n'), c' g 1 i' = 1)
    (hcob : ∀ (g h k : Γ) (i : Fin n),
      c h k ((ρ g)⁻¹ i) * (c (g * h) k i)⁻¹ * c g (h * k) i *
          (c g h i)⁻¹ = Additive.toMul (β (α g h k) i))
    (hcob' : ∀ (g h k : Γ) (i' : Fin n'),
      c' h k ((ρ' g)⁻¹ i') * (c' (g * h) k i')⁻¹ * c' g (h * k) i' *
          (c' g h i')⁻¹ = Additive.toMul (β' (α g h k) i'))
    (O : Set (Fin n' × Fin n))
    (hO : ∃ p₀ : Fin n' × Fin n,
      O = {p | ∃ g : Γ, p = ((ρ' g)⁻¹ p₀.1, (ρ g)⁻¹ p₀.2)})
    (hintertwine : ∀ (p : Fin n' × Fin n), p ∈ O → ∀ u : A,
      β' u p.1 = β u p.2) :
    let z : Γ → Γ → O → ℂˣ := fun g h p =>
      c' g h p.1.1 * (c g h p.1.2)⁻¹;
    (∀ (g : Γ) (p : O), z 1 g p = 1 ∧ z g 1 p = 1) ∧
    (∀ (g h k : Γ) (p : O),
      (c' h k ((ρ' g)⁻¹ p.1.1) * (c h k ((ρ g)⁻¹ p.1.2))⁻¹) *
          (z (g * h) k p)⁻¹ * z g (h * k) p * (z g h p)⁻¹ = 1) ∧
    (∀ (x : Γ → Fin n → ℂˣ) (x' : Γ → Fin n' → ℂˣ),
      (∀ i : Fin n, x 1 i = 1) →
      (∀ i' : Fin n', x' 1 i' = 1) →
      let δx : Γ → Γ → Fin n → ℂˣ := fun g h i =>
        x h ((ρ g)⁻¹ i) * (x (g * h) i)⁻¹ * x g i;
      let δx' : Γ → Γ → Fin n' → ℂˣ := fun g h i' =>
        x' h ((ρ' g)⁻¹ i') * (x' (g * h) i')⁻¹ * x' g i';
      let y : Γ → O → ℂˣ := fun g p => x' g p.1.1 * (x g p.1.2)⁻¹;
      ∀ (g h : Γ) (p : O),
        (c' g h p.1.1 * δx' g h p.1.1) *
            (c g h p.1.2 * δx g h p.1.2)⁻¹ =
          z g h p *
            ((x' h ((ρ' g)⁻¹ p.1.1) *
                (x h ((ρ g)⁻¹ p.1.2))⁻¹) *
              (y (g * h) p)⁻¹ * y g p)) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro g p
    constructor
    · simp [hc'₁, hc₁]
    · simp [hc'₂, hc₂]
  · intro g h k p
    rw [orbit_factor_identity]
    rw [hcob' g h k p.1.1, hcob g h k p.1.2]
    have hβ := congrArg Additive.toMul (hintertwine p.1 p.2 (α g h k))
    simp [hβ]
  · intro x x' hx hx' g h p
    exact coboundary_factor_identity _ _ _ _ _ _ _ _

end Rollout_p0818_intertwining_orbit_cocycle

#check_dependency_graph "Rollout_p0818_intertwining_orbit_cocycle.intertwining_orbit_cocycle" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let z := fun g h p => c' g h (↑p).1 * (c g h (↑p).2)⁻¹; (∀ (g : Γ) (p : ↑O), z 1 g p = 1 ∧ z g 1 p = 1) ∧ (∀ (g h k : Γ) (p : ↑O), c' h k ((ρ' g)⁻¹ (↑p).1) * (c h k ((ρ g)⁻¹ (↑p).2))⁻¹ * (z (g * h) k p)⁻¹ * z g (h * k) p * (z g h p)⁻¹ = 1) ∧ ∀ (x : Γ → Fin n → ℂˣ) (x' : Γ → Fin n' → ℂˣ), (∀ (i : Fin n), x 1 i = 1) → (∀ (i' : Fin n'), x' 1 i' = 1) → let δx := fun g h i => x h ((ρ g)⁻¹ i) * (x (g * h) i)⁻¹ * x g i; let δx' := fun g h i' => x' h ((ρ' g)⁻¹ i') * (x' (g * h) i')⁻¹ * x' g i'; let y := fun g p => x' g (↑p).1 * (x g (↑p).2)⁻¹; ∀ (g h : Γ) (p : ↑O), c' g h (↑p).1 * δx' g h (↑p).1 * (c g h (↑p).2 * δx g h (↑p).2)⁻¹ = z g h p * (x' h ((ρ' g)⁻¹ (↑p).1) * (x h ((ρ g)⁻¹ (↑p).2))⁻¹ * (y (g * h) p)⁻¹ * y g p)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hc₁\",\"statement\":\"∀ (g : Γ) (i : Fin n), c 1 g i = 1\"},{\"name\":\"hc₂\",\"statement\":\"∀ (g : Γ) (i : Fin n), c g 1 i = 1\"},{\"name\":\"hc'₁\",\"statement\":\"∀ (g : Γ) (i' : Fin n'), c' 1 g i' = 1\"},{\"name\":\"hc'₂\",\"statement\":\"∀ (g : Γ) (i' : Fin n'), c' g 1 i' = 1\"},{\"name\":\"hcob\",\"statement\":\"∀ (g h k : Γ) (i : Fin n), c h k ((ρ g)⁻¹ i) * (c (g * h) k i)⁻¹ * c g (h * k) i * (c g h i)⁻¹ = Additive.toMul (β (α g h k) i)\"},{\"name\":\"hcob'\",\"statement\":\"∀ (g h k : Γ) (i' : Fin n'), c' h k ((ρ' g)⁻¹ i') * (c' (g * h) k i')⁻¹ * c' g (h * k) i' * (c' g h i')⁻¹ = Additive.toMul (β' (α g h k) i')\"},{\"name\":\"hintertwine\",\"statement\":\"∀ p ∈ O, ∀ (u : A), β' u p.1 = β u p.2\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0818_intertwining_orbit_cocycle\",\"reconstructedProofSha256\":\"9be86f99c61a6854a7b02c50afff54eb32bfd23a779654cc953a427e092b96ec\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p0818_intertwining_orbit_cocycle.intertwining_orbit_cocycle\",\"topologySha256\":\"7c24cee0092f3df02efea7f89fb4a675db6848999deb567605152a521cf9f3f3\"}"

namespace Rollout_p0925_tanh_ge_one_sub_exp_neg

-- graph_id: p0925_tanh_ge_one_sub_exp_neg
-- topology_sha256: c31c7ef38ac30d758d597727d77d1f890e731380163812056eec74da2d1acdf6
/- verified submission -/
theorem tanh_ge_one_sub_exp_neg (x : ℝ) (hx : 0 ≤ x) :
    Real.tanh x ≥ 1 - Real.exp (-x) := by
  rw [Real.tanh_eq, Real.exp_neg]
  let t : ℝ := Real.exp x
  change (t - t⁻¹) / (t + t⁻¹) ≥ 1 - t⁻¹
  have ht : 0 < t := by
    dsimp [t]
    exact Real.exp_pos x
  have ht1 : 1 ≤ t := by
    dsimp [t]
    exact Real.one_le_exp hx
  field_simp [ht.ne']
  ring_nf
  nlinarith [sq_nonneg (t - 1)]

end Rollout_p0925_tanh_ge_one_sub_exp_neg

#check_dependency_graph "Rollout_p0925_tanh_ge_one_sub_exp_neg.tanh_ge_one_sub_exp_neg" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"Real.tanh x ≥ 1 - Real.exp (-x)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hx\",\"statement\":\"0 ≤ x\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0925_tanh_ge_one_sub_exp_neg\",\"reconstructedProofSha256\":\"117b93ca571d859736b43fcd6aa91945b68ca73b359c57f9f260dff6354470fb\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p0925_tanh_ge_one_sub_exp_neg.tanh_ge_one_sub_exp_neg\",\"topologySha256\":\"c31c7ef38ac30d758d597727d77d1f890e731380163812056eec74da2d1acdf6\"}"

namespace Rollout_p0960_antitone_monotone_power_sum_inequality

-- graph_id: p0960_antitone_monotone_power_sum_inequality
-- topology_sha256: e4cd917d0aebd07d32c97b0a51e0e5210516236764cf68793d96a95ef4c7844f
/- accepted add_to_file helper 1 -/
lemma antitone_monotone_power_sum_pair_nonneg
    {x y u v : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) (hu : 0 ≤ u) (huv : u ≤ v)
    {s : ℝ} (hs : 1 ≤ s) :
    0 ≤ x ^ (s + 1) * (y * v) + y ^ (s + 1) * (x * u) -
        x ^ s * (y ^ 2 * v) - y ^ s * (x ^ 2 * u) := by
  rcases eq_or_lt_of_le hy with rfl | hypos
  · have hs0 : s ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hs)
    have hs10 : s + 1 ≠ 0 := by positivity
    simp [Real.zero_rpow hs0, Real.zero_rpow hs10]
  · have hxpos : 0 < x := lt_of_lt_of_le hypos hxy
    have hx : 0 ≤ x := le_of_lt hxpos
    have hs1 : s - 1 + 1 = s := by ring
    have hxsp : x ^ (s + 1) = x ^ s * x := Real.rpow_add_one (ne_of_gt hxpos) s
    have hysp : y ^ (s + 1) = y ^ s * y := Real.rpow_add_one (ne_of_gt hypos) s
    have hxs : x ^ s = x * x ^ (s - 1) := by
      calc
        x ^ s = x ^ (s - 1 + 1) := by rw [hs1]
        _ = x ^ (s - 1) * x := Real.rpow_add_one (ne_of_gt hxpos) (s - 1)
        _ = x * x ^ (s - 1) := by ring
    have hys : y ^ s = y * y ^ (s - 1) := by
      calc
        y ^ s = y ^ (s - 1 + 1) := by rw [hs1]
        _ = y ^ (s - 1) * y := Real.rpow_add_one (ne_of_gt hypos) (s - 1)
        _ = y * y ^ (s - 1) := by ring
    have hfactor :
        x ^ (s + 1) * (y * v) + y ^ (s + 1) * (x * u) -
            x ^ s * (y ^ 2 * v) - y ^ s * (x ^ 2 * u)
          = x * y * (x - y) * (v * x ^ (s - 1) - u * y ^ (s - 1)) := by
      rw [hxsp, hysp, hxs, hys]
      ring
    rw [hfactor]
    have hxydiff : 0 ≤ x - y := sub_nonneg.mpr hxy
    have hsexp : 0 ≤ s - 1 := sub_nonneg.mpr hs
    have hpow : y ^ (s - 1) ≤ x ^ (s - 1) := Real.rpow_le_rpow hy hxy hsexp
    have hpownonneg : 0 ≤ y ^ (s - 1) := Real.rpow_nonneg hy (s - 1)
    have hv : 0 ≤ v := le_trans hu huv
    have hweighted : u * y ^ (s - 1) ≤ v * x ^ (s - 1) :=
      mul_le_mul huv hpow hpownonneg hv
    have hdiff : 0 ≤ v * x ^ (s - 1) - u * y ^ (s - 1) := sub_nonneg.mpr hweighted
    exact mul_nonneg (mul_nonneg (mul_nonneg hx hy) hxydiff) hdiff

/- verified submission -/
theorem antitone_monotone_power_sum_inequality
    (k : ℕ) (hk : 0 < k)
    (s : ℝ) (hs : 1 ≤ s)
    (a b : Fin k → ℝ)
    (ha : ∀ i, 0 ≤ a i)
    (hb : ∀ i, 0 ≤ b i)
    (ha_antitone : Antitone a)
    (hb_monotone : Monotone b) :
    (∑ i : Fin k, Real.rpow (a i) s) * (∑ i : Fin k, (a i) ^ 2 * b i) ≤
      (∑ i : Fin k, Real.rpow (a i) (s + 1)) * (∑ i : Fin k, a i * b i) := by
  let A : ℝ := ∑ i : Fin k, (a i) ^ s
  let B : ℝ := ∑ i : Fin k, (a i) ^ 2 * b i
  let C : ℝ := ∑ i : Fin k, (a i) ^ (s + 1)
  let D : ℝ := ∑ i : Fin k, a i * b i
  let U : Fin k → Fin k → ℝ := fun i j => (a i) ^ (s + 1) * (a j * b j)
  let V : Fin k → Fin k → ℝ := fun i j => (a i) ^ s * ((a j) ^ 2 * b j)
  let W : Fin k → Fin k → ℝ := fun i j => U i j + U j i - V i j - V j i
  have hWnonneg : ∀ i j : Fin k, 0 ≤ W i j := by
    intro i j
    rcases le_total i j with hij | hji
    · exact antitone_monotone_power_sum_pair_nonneg
        (hy := ha j) (hxy := ha_antitone hij) (hu := hb i)
        (huv := hb_monotone hij) hs
    · have hswap := antitone_monotone_power_sum_pair_nonneg
        (hy := ha i) (hxy := ha_antitone hji) (hu := hb j)
        (huv := hb_monotone hji) hs
      dsimp [W, U, V]
      convert hswap using 1
      ring
  have hsumW : 0 ≤ ∑ i : Fin k, ∑ j : Fin k, W i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hWnonneg i j
  have hU : (∑ i : Fin k, ∑ j : Fin k, U i j) = C * D := by
    simpa [U, C, D] using
      (Fintype.sum_mul_sum (fun i : Fin k => (a i) ^ (s + 1))
        (fun j : Fin k => a j * b j)).symm
  have hUs : (∑ i : Fin k, ∑ j : Fin k, U j i) = C * D := by
    calc
      (∑ i : Fin k, ∑ j : Fin k, U j i)
          = ∑ j : Fin k, ∑ i : Fin k, U j i := Finset.sum_comm
      _ = C * D := hU
  have hV : (∑ i : Fin k, ∑ j : Fin k, V i j) = A * B := by
    simpa [V, A, B] using
      (Fintype.sum_mul_sum (fun i : Fin k => (a i) ^ s)
        (fun j : Fin k => (a j) ^ 2 * b j)).symm
  have hVs : (∑ i : Fin k, ∑ j : Fin k, V j i) = A * B := by
    calc
      (∑ i : Fin k, ∑ j : Fin k, V j i)
          = ∑ j : Fin k, ∑ i : Fin k, V j i := Finset.sum_comm
      _ = A * B := hV
  have hsumEq : (∑ i : Fin k, ∑ j : Fin k, W i j) = 2 * (C * D - A * B) := by
    calc
      (∑ i : Fin k, ∑ j : Fin k, W i j)
          = (∑ i : Fin k, ∑ j : Fin k, U i j) +
              (∑ i : Fin k, ∑ j : Fin k, U j i) -
              (∑ i : Fin k, ∑ j : Fin k, V i j) -
              (∑ i : Fin k, ∑ j : Fin k, V j i) := by
            simp [W, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = 2 * (C * D - A * B) := by
            rw [hU, hUs, hV, hVs]
            ring
  have hdiff : 0 ≤ C * D - A * B := by
    nlinarith
  have hle : A * B ≤ C * D := sub_nonneg.mp hdiff
  simpa [A, B, C, D] using hle

end Rollout_p0960_antitone_monotone_power_sum_inequality

#check_dependency_graph "Rollout_p0960_antitone_monotone_power_sum_inequality.antitone_monotone_power_sum_inequality" against "{\"edges\":[{\"conclusion\":{\"name\":\"hWnonneg\",\"statement\":\"∀ (i j : Fin k), 0 ≤ W i j\"},\"graphEdgeId\":\"h_001_hwnonneg\",\"premises\":[{\"name\":\"hs\",\"statement\":\"1 ≤ s\"},{\"name\":\"ha\",\"statement\":\"∀ (i : Fin k), 0 ≤ a i\"},{\"name\":\"hb\",\"statement\":\"∀ (i : Fin k), 0 ≤ b i\"},{\"name\":\"ha_antitone\",\"statement\":\"Antitone a\"},{\"name\":\"hb_monotone\",\"statement\":\"Monotone b\"}],\"rawEdgeId\":\"telescope_17\"},{\"conclusion\":{\"name\":\"hU\",\"statement\":\"∑ i, ∑ j, U i j = C * D\"},\"graphEdgeId\":\"h_003_hu\",\"premises\":[],\"rawEdgeId\":\"telescope_19\"},{\"conclusion\":{\"name\":\"hV\",\"statement\":\"∑ i, ∑ j, V i j = A * B\"},\"graphEdgeId\":\"h_005_hv\",\"premises\":[],\"rawEdgeId\":\"telescope_21\"},{\"conclusion\":{\"name\":\"hsumW\",\"statement\":\"0 ≤ ∑ i, ∑ j, W i j\"},\"graphEdgeId\":\"h_002_hsumw\",\"premises\":[{\"name\":\"hWnonneg\",\"statement\":\"∀ (i j : Fin k), 0 ≤ W i j\"}],\"rawEdgeId\":\"telescope_18\"},{\"conclusion\":{\"name\":\"hUs\",\"statement\":\"∑ i, ∑ j, U j i = C * D\"},\"graphEdgeId\":\"h_004_hus\",\"premises\":[{\"name\":\"hU\",\"statement\":\"∑ i, ∑ j, U i j = C * D\"}],\"rawEdgeId\":\"telescope_20\"},{\"conclusion\":{\"name\":\"hVs\",\"statement\":\"∑ i, ∑ j, V j i = A * B\"},\"graphEdgeId\":\"h_006_hvs\",\"premises\":[{\"name\":\"hV\",\"statement\":\"∑ i, ∑ j, V i j = A * B\"}],\"rawEdgeId\":\"telescope_22\"},{\"conclusion\":{\"name\":\"hsumEq\",\"statement\":\"∑ i, ∑ j, W i j = 2 * (C * D - A * B)\"},\"graphEdgeId\":\"h_007_hsumeq\",\"premises\":[{\"name\":\"hU\",\"statement\":\"∑ i, ∑ j, U i j = C * D\"},{\"name\":\"hUs\",\"statement\":\"∑ i, ∑ j, U j i = C * D\"},{\"name\":\"hV\",\"statement\":\"∑ i, ∑ j, V i j = A * B\"},{\"name\":\"hVs\",\"statement\":\"∑ i, ∑ j, V j i = A * B\"}],\"rawEdgeId\":\"telescope_23\"},{\"conclusion\":{\"name\":\"hdiff\",\"statement\":\"0 ≤ C * D - A * B\"},\"graphEdgeId\":\"h_008_hdiff\",\"premises\":[{\"name\":\"hsumW\",\"statement\":\"0 ≤ ∑ i, ∑ j, W i j\"},{\"name\":\"hsumEq\",\"statement\":\"∑ i, ∑ j, W i j = 2 * (C * D - A * B)\"}],\"rawEdgeId\":\"telescope_24\"},{\"conclusion\":{\"name\":\"hle\",\"statement\":\"A * B ≤ C * D\"},\"graphEdgeId\":\"h_009_hle\",\"premises\":[{\"name\":\"hdiff\",\"statement\":\"0 ≤ C * D - A * B\"}],\"rawEdgeId\":\"telescope_25\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(∑ i, (a i).rpow s) * ∑ i, a i ^ 2 * b i ≤ (∑ i, (a i).rpow (s + 1)) * ∑ i, a i * b i\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hle\",\"statement\":\"A * B ≤ C * D\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0960_antitone_monotone_power_sum_inequality\",\"reconstructedProofSha256\":\"571ab4248c4ae6b0931865d1da9639561fffc74480b2bc19df7cf281c6bbb8c7\",\"selectedEdgeCount\":10,\"theoremName\":\"Rollout_p0960_antitone_monotone_power_sum_inequality.antitone_monotone_power_sum_inequality\",\"topologySha256\":\"e4cd917d0aebd07d32c97b0a51e0e5210516236764cf68793d96a95ef4c7844f\"}"

namespace Rollout_p1242_finite_support_derivation

-- graph_id: p1242_finite_support_derivation
-- topology_sha256: bc281170dffb87d8109f2c024ade7a9d553845452e30202f67d3936dd79f381c
/- accepted add_to_file helper 1 -/
lemma derivation_mono_of_finite_generation
    {W : Type*} (D : Set W → Set W)
    (hD : ∀ (S : Set W) (x : W),
      x ∈ D S ↔ ∃ F : Set W, F.Finite ∧ F ⊆ S ∧ x ∈ D F)
    {S T : Set W} (hST : S ⊆ T) : D S ⊆ D T := by
  intro x hx
  rw [hD S x] at hx
  rw [hD T x]
  rcases hx with ⟨F, hFfin, hFS, hxF⟩
  exact ⟨F, hFfin, hFS.trans hST, hxF⟩

lemma finite_support_of_derivation
    {W : Type*} (D : Set W → Set W)
    (hD : ∀ (S : Set W) (x : W),
      x ∈ D S ↔ ∃ F : Set W, F.Finite ∧ F ⊆ S ∧ x ∈ D F)
    {U B : Set W} (hB : B.Finite) (hsub : B ⊆ D U) :
    ∃ C : Set W, C.Finite ∧ C ⊆ U ∧ B ⊆ D C := by
  classical
  have hchoice : ∀ x : B, ∃ F : Set W,
      F.Finite ∧ F ⊆ U ∧ (x : W) ∈ D F := by
    intro x
    exact (hD U (x : W)).1 (hsub x.property)
  choose F hF using hchoice
  letI : Fintype B := hB.fintype
  refine ⟨⋃ x : B, F x, Set.finite_iUnion (fun x : B => (hF x).1), ?_, ?_⟩
  · intro y hy
    rw [Set.mem_iUnion] at hy
    rcases hy with ⟨x, hyx⟩
    exact (hF x).2.1 hyx
  · intro x hx
    exact derivation_mono_of_finite_generation D hD
      (Set.subset_iUnion (fun x : B => F x) ⟨x, hx⟩)
      (hF ⟨x, hx⟩).2.2

/- accepted add_to_file helper 2 -/
lemma finite_support_chain_forall
    {W : Type*} (D : Set W → Set W)
    (hD : ∀ (S : Set W) (x : W),
      x ∈ D S ↔ ∃ F : Set W, F.Finite ∧ F ⊆ S ∧ x ∈ D F)
    (A : Set W) :
    ∀ n : ℕ, 1 ≤ n → ∀ B : Set W, B.Finite → B ⊆ (D^[n]) A →
      ∃ S : ℕ → Set W,
        (∀ k < n, (S k).Finite) ∧
        (∀ k < n, S k ⊆ (D^[k]) A) ∧
        B ⊆ D (S (n - 1)) ∧
        ∀ k, k + 1 < n → S (k + 1) ⊆ D (S k) := by
  intro n
  induction n with
  | zero =>
      intro hn
      omega
  | succ m ihm =>
      intro hm B hB hsub
      have hsubD : B ⊆ D ((D^[m]) A) := by
        simpa [Function.iterate_succ_apply'] using hsub
      rcases finite_support_of_derivation D hD hB hsubD with
        ⟨C, hCfin, hCsub, hBDC⟩
      cases m with
      | zero =>
          refine ⟨fun _ => C, ?_, ?_, ?_, ?_⟩
          · intro k hk
            exact hCfin
          · intro k hk
            have hk0 : k = 0 := by omega
            subst k
            simpa using hCsub
          · simpa using hBDC
          · intro k hk
            exfalso
            omega
      | succ r =>
          rcases ihm (by omega) C hCfin hCsub with
            ⟨T, hTfin, hTsub, hCT, hTchain⟩
          let S : ℕ → Set W := fun k => if k ≤ r then T k else C
          refine ⟨S, ?_, ?_, ?_, ?_⟩
          · intro k hk
            by_cases hkr : k ≤ r
            · have hklt : k < r + 1 := Nat.lt_succ_of_le hkr
              simp [S, hkr, hTfin k hklt]
            · have hkeq : k = r + 1 := by omega
              subst k
              simp [S, hCfin]
          · intro k hk
            by_cases hkr : k ≤ r
            · have hklt : k < r + 1 := Nat.lt_succ_of_le hkr
              simp [S, hkr, hTsub k hklt]
            · have hkeq : k = r + 1 := by omega
              subst k
              simp [S]
              simpa [Function.iterate_succ_apply] using hCsub
          · simp [S, hBDC]
          · intro k hk
            by_cases hkr : k + 1 ≤ r
            · have hk1lt : k + 1 < r + 1 := Nat.lt_succ_of_le hkr
              have hklt : k ≤ r := by omega
              simpa [S, hkr, hklt] using hTchain k hk1lt
            · have hk1 : k + 1 = r + 1 := by omega
              have hkeq : k = r := by omega
              subst k
              have hrle : r ≤ r := le_rfl
              simpa [S, hrle] using hCT

/- verified submission -/
theorem finite_support_derivation
    {W : Type*} (D : Set W → Set W)
    (hD : ∀ (S : Set W) (x : W),
      x ∈ D S ↔ ∃ F : Set W, F.Finite ∧ F ⊆ S ∧ x ∈ D F)
    (A : Set W) (n : ℕ) (P : W)
    (hn : 1 ≤ n) (hP : P ∈ (D^[n]) A) :
    ∃ S : ℕ → Set W,
      (∀ k < n, (S k).Finite) ∧
      (∀ k < n, S k ⊆ (D^[k]) A) ∧
      P ∈ D (S (n - 1)) ∧
      ∀ k, k + 1 < n → S (k + 1) ⊆ D (S k) := by
  have hsub : {P} ⊆ (D^[n]) A := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hP
  rcases finite_support_chain_forall D hD A n hn {P} (Set.finite_singleton P) hsub with
    ⟨S, hSfin, hSsub, hStop, hSchain⟩
  exact ⟨S, hSfin, hSsub, hStop rfl, hSchain⟩

end Rollout_p1242_finite_support_derivation

#check_dependency_graph "Rollout_p1242_finite_support_derivation.finite_support_derivation" against "{\"edges\":[{\"conclusion\":{\"name\":\"hsub\",\"statement\":\"{P} ⊆ D^[n] A\"},\"graphEdgeId\":\"h_001_hsub\",\"premises\":[{\"name\":\"hP\",\"statement\":\"P ∈ D^[n] A\"}],\"rawEdgeId\":\"telescope_8\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∃ S, (∀ k < n, (S k).Finite) ∧ (∀ k < n, S k ⊆ D^[k] A) ∧ P ∈ D (S (n - 1)) ∧ ∀ (k : ℕ), k + 1 < n → S (k + 1) ⊆ D (S k)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hD\",\"statement\":\"∀ (S : Set W) (x : W), x ∈ D S ↔ ∃ F, F.Finite ∧ F ⊆ S ∧ x ∈ D F\"},{\"name\":\"hn\",\"statement\":\"1 ≤ n\"},{\"name\":\"hsub\",\"statement\":\"{P} ⊆ D^[n] A\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1242_finite_support_derivation\",\"reconstructedProofSha256\":\"cd077f49996aa525d5cdf2484fab8b5fd17d638ce423e2f4faaf24a12c98125f\",\"selectedEdgeCount\":2,\"theoremName\":\"Rollout_p1242_finite_support_derivation.finite_support_derivation\",\"topologySha256\":\"bc281170dffb87d8109f2c024ade7a9d553845452e30202f67d3936dd79f381c\"}"

namespace Rollout_p1318_sequence_triangular_formula

-- graph_id: p1318_sequence_triangular_formula
-- topology_sha256: e12f68c590d052a3252704376bcc8420bd334abba0895d8d9e6f14d69b56ebc6
/- accepted add_to_file helper 1 -/
lemma triangular_pair (m : ℕ) :
    2 * m ^ 2 = 2 * ((m - 1) * m / 2 + m * (m + 1) / 2) := by
  have hsum :
      2 * m ^ 2 = (m - 1) * m + m * (m + 1) := by
    cases m with
    | zero => norm_num
    | succ a =>
        simp
        ring
  have hA : 2 ∣ (m - 1) * m := by
    rw [Nat.mul_comm]
    exact Nat.two_dvd_mul_sub_one m
  have hB : 2 ∣ m * (m + 1) := Nat.two_dvd_mul_add_one m
  have hAback : 2 * ((m - 1) * m / 2) = (m - 1) * m := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel hA
  have hBback : 2 * (m * (m + 1) / 2) = m * (m + 1) := by
    rw [Nat.mul_comm]
    exact Nat.div_mul_cancel hB
  have hdouble :
      2 * ((m - 1) * m / 2 + m * (m + 1) / 2)
        = (m - 1) * m + m * (m + 1) := by
    rw [Nat.mul_add, hAback, hBback]
  exact hsum.trans hdouble.symm

/- verified submission -/
theorem sequence_triangular_formula
    (c : ℕ → ℕ)
    (hc₁ : c 1 = 2)
    (hc : ∀ k : ℕ, 0 < k →
      c (2 * k) = 2 * (k + 1) ^ 2 ∧
      c (2 * k + 1) = 2 * (k + 1) ^ 2) :
    ∀ n : ℕ, 0 < n →
      let m := (n + 2) / 2
      let t : ℕ → ℕ := fun r => r * (r + 1) / 2
      c n = 2 * m ^ 2 ∧ 2 * m ^ 2 = 2 * (t (m - 1) + t m) := by
  intro n hn
  by_cases h1 : n = 1
  · subst n
    simp [hc₁]
  · let k := n / 2
    have hk : 0 < k := by
      omega
    have hrec := hc k hk
    have hmod := Nat.mod_two_eq_zero_or_one n
    rcases hmod with heven | hodd
    · have hn_eq : n = 2 * k := by
        omega
      have hm : (n + 2) / 2 = k + 1 := by
        omega
      have hcn : c n = 2 * (k + 1) ^ 2 := by
        rw [hn_eq]
        exact hrec.1
      dsimp
      constructor
      · rw [hm]
        exact hcn
      · rw [hm]
        exact triangular_pair (k + 1)
    · have hn_eq : n = 2 * k + 1 := by
        omega
      have hm : (n + 2) / 2 = k + 1 := by
        omega
      have hcn : c n = 2 * (k + 1) ^ 2 := by
        rw [hn_eq]
        exact hrec.2
      dsimp
      constructor
      · rw [hm]
        exact hcn
      · rw [hm]
        exact triangular_pair (k + 1)

end Rollout_p1318_sequence_triangular_formula

#check_dependency_graph "Rollout_p1318_sequence_triangular_formula.sequence_triangular_formula" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let m := (n + 2) / 2; let t := fun r => r * (r + 1) / 2; c n = 2 * m ^ 2 ∧ 2 * m ^ 2 = 2 * (t (m - 1) + t m)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hc₁\",\"statement\":\"c 1 = 2\"},{\"name\":\"hc\",\"statement\":\"∀ (k : ℕ), 0 < k → c (2 * k) = 2 * (k + 1) ^ 2 ∧ c (2 * k + 1) = 2 * (k + 1) ^ 2\"},{\"name\":\"hn\",\"statement\":\"0 < n\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1318_sequence_triangular_formula\",\"reconstructedProofSha256\":\"94256b8599ca55d28ef24ab5fc82b764a624b7fdfd52212f74a43478178ddd1f\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1318_sequence_triangular_formula.sequence_triangular_formula\",\"topologySha256\":\"e12f68c590d052a3252704376bcc8420bd334abba0895d8d9e6f14d69b56ebc6\"}"

namespace Rollout_p1335_quarter_stratifiable_diagonal_isgdelta_and

-- graph_id: p1335_quarter_stratifiable_diagonal_isgdelta_and
-- topology_sha256: f6d5f2b5cdd3ab71e8e47d685829467cee1447f2787f921b97cf0a3b7dda70a0
/- verified submission -/
theorem quarter_stratifiable_diagonal_isGDelta_and_countable_pseudocharacter
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (g : ℕ → X → Set X)
    (hg_open : ∀ n a, IsOpen (g n a))
    (hg_cover : ∀ n, ⋃ a, g n a = Set.univ)
    (hg_converges : ∀ (x : X) (a : ℕ → X),
      (∀ n, x ∈ g n (a n)) → Filter.Tendsto a Filter.atTop (nhds x)) :
    (∃ G : ℕ → Set (X × X),
      (∀ n, IsOpen (G n)) ∧
      Set.diagonal X = ⋂ n, G n) ∧
    ∀ x : X, ∃ V : ℕ → Set X,
      (∀ n, IsOpen (V n) ∧ x ∈ V n) ∧
      ⋂ n, V n = {x} := by
  classical
  constructor
  · refine ⟨fun n => ⋃ a, (g n a) ×ˢ (g n a), ?_, ?_⟩
    · intro n
      exact isOpen_iUnion fun a => (hg_open n a).prod (hg_open n a)
    · ext p
      constructor
      · intro hp
        rw [Set.mem_diagonal_iff] at hp
        rw [Set.mem_iInter]
        intro n
        have hc : p.1 ∈ ⋃ a, g n a := by
          rw [hg_cover n]
          trivial
        rw [Set.mem_iUnion] at hc
        rcases hc with ⟨a, hpa⟩
        rw [Set.mem_iUnion]
        exact ⟨a, by
          rw [Set.mem_prod]
          exact ⟨hpa, by simpa [hp] using hpa⟩⟩
      · intro hp
        rw [Set.mem_diagonal_iff]
        have hchoice : ∀ n, ∃ a, p.1 ∈ g n a ∧ p.2 ∈ g n a := by
          intro n
          have hpn : p ∈ ⋃ a, (g n a) ×ˢ (g n a) := Set.mem_iInter.mp hp n
          rw [Set.mem_iUnion] at hpn
          rcases hpn with ⟨a, hpa⟩
          exact ⟨a, Set.mem_prod.mp hpa⟩
        choose a ha using hchoice
        have hlim₁ := hg_converges p.1 a fun n => (ha n).1
        have hlim₂ := hg_converges p.2 a fun n => (ha n).2
        exact tendsto_nhds_unique hlim₁ hlim₂
  · intro x
    have hchoice : ∀ n, ∃ a, x ∈ g n a := by
      intro n
      have hx : x ∈ ⋃ a, g n a := by
        rw [hg_cover n]
        trivial
      rw [Set.mem_iUnion] at hx
      exact hx
    choose a ha using hchoice
    refine ⟨fun n => g n (a n), ?_, ?_⟩
    · intro n
      exact ⟨hg_open n (a n), ha n⟩
    · ext y
      constructor
      · intro hy
        have hy' : ∀ n, y ∈ g n (a n) := Set.mem_iInter.mp hy
        have hlimy := hg_converges y a hy'
        have hlimx := hg_converges x a ha
        have hyx : y = x := tendsto_nhds_unique hlimy hlimx
        simpa [hyx]
      · intro hy
        have hyx : y = x := by simpa using hy
        rw [Set.mem_iInter]
        intro n
        simpa [hyx] using ha n

end Rollout_p1335_quarter_stratifiable_diagonal_isgdelta_and

#check_dependency_graph "Rollout_p1335_quarter_stratifiable_diagonal_isgdelta_and.quarter_stratifiable_diagonal_isGDelta_and_countable_pseudocharacter" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(∃ G, (∀ (n : ℕ), IsOpen (G n)) ∧ Set.diagonal X = ⋂ n, G n) ∧ ∀ (x : X), ∃ V, (∀ (n : ℕ), IsOpen (V n) ∧ x ∈ V n) ∧ ⋂ n, V n = {x}\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"T2Space X\"},{\"name\":\"hg_open\",\"statement\":\"∀ (n : ℕ) (a : X), IsOpen (g n a)\"},{\"name\":\"hg_cover\",\"statement\":\"∀ (n : ℕ), ⋃ a, g n a = Set.univ\"},{\"name\":\"hg_converges\",\"statement\":\"∀ (x : X) (a : ℕ → X), (∀ (n : ℕ), x ∈ g n (a n)) → Filter.Tendsto a Filter.atTop (nhds x)\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1335_quarter_stratifiable_diagonal_isgdelta_and\",\"reconstructedProofSha256\":\"f30b800ea441ff0858d2c732e8184e5df22da3d512019b72e53f35ae716c25a0\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1335_quarter_stratifiable_diagonal_isgdelta_and.quarter_stratifiable_diagonal_isGDelta_and_countable_pseudocharacter\",\"topologySha256\":\"f6d5f2b5cdd3ab71e8e47d685829467cee1447f2787f921b97cf0a3b7dda70a0\"}"

namespace Rollout_p1489_slope_composition_equivalent

-- graph_id: p1489_slope_composition_equivalent
-- topology_sha256: 7a474cd4744979179ba1711124439a6e82dead9ccc91bf25655d868fb3d61174
/- accepted add_to_file helper 1 -/
lemma finite_range_apply_eq_of_finite_defect
    (f g g' : ℤ → ℤ)
    (hf : (Set.range (fun p : ℤ × ℤ =>
      f (p.1 + p.2) - f p.1 - f p.2)).Finite)
    (hgg' : (Set.range (fun n : ℤ => g n - g' n)).Finite) :
    (Set.range (fun n : ℤ => f (g n) - f (g' n))).Finite := by
  let A : Set ℤ := Set.range (fun n : ℤ => g n - g' n)
  let B : Set ℤ := Set.range (fun p : ℤ × ℤ =>
    f (p.1 + p.2) - f p.1 - f p.2)
  have hA : A.Finite := hgg'
  have hB : B.Finite := hf
  refine ((hA.prod hB).image (fun q : ℤ × ℤ => q.2 + f q.1)).subset ?_
  rw [Set.range_subset_iff]
  intro n
  refine ⟨(g n - g' n,
      f (g' n + (g n - g' n)) - f (g' n) - f (g n - g' n)), ?_, ?_⟩
  · rw [Set.mem_prod]
    constructor
    · exact ⟨n, rfl⟩
    · exact ⟨(g' n, g n - g' n), by ring⟩
  · dsimp
    ring

lemma finite_range_defect_comp
    (f g : ℤ → ℤ)
    (hf : (Set.range (fun p : ℤ × ℤ =>
      f (p.1 + p.2) - f p.1 - f p.2)).Finite)
    (hg : (Set.range (fun p : ℤ × ℤ =>
      g (p.1 + p.2) - g p.1 - g p.2)).Finite) :
    (Set.range (fun p : ℤ × ℤ =>
      f (g (p.1 + p.2)) - f (g p.1) - f (g p.2))).Finite := by
  let A : Set ℤ := Set.range (fun p : ℤ × ℤ =>
    g (p.1 + p.2) - g p.1 - g p.2)
  let B : Set ℤ := Set.range (fun p : ℤ × ℤ =>
    f (p.1 + p.2) - f p.1 - f p.2)
  have hA : A.Finite := hg
  have hB : B.Finite := hf
  refine (((hA.prod hB).prod hB).image
    (fun q : (ℤ × ℤ) × ℤ => q.1.2 + f q.1.1 + q.2)).subset ?_
  rw [Set.range_subset_iff]
  intro p
  let d : ℤ := g (p.1 + p.2) - g p.1 - g p.2
  let u : ℤ := f ((g p.1 + g p.2) + d) - f (g p.1 + g p.2) - f d
  let v : ℤ := f (g p.1 + g p.2) - f (g p.1) - f (g p.2)
  have hd : g (p.1 + p.2) = (g p.1 + g p.2) + d := by
    dsimp [d]
    ring
  refine ⟨((d, u), v), ?_, ?_⟩
  · rw [Set.mem_prod, Set.mem_prod]
    refine ⟨⟨⟨p, rfl⟩, ⟨(g p.1 + g p.2, d), by ring⟩⟩,
      ⟨(g p.1, g p.2), rfl⟩⟩
  · dsimp
    rw [hd]
    ring

/- verified submission -/
theorem slope_composition_equivalent
    (α α' β β' : ℤ → ℤ)
    (hα : (Set.range (fun p : ℤ × ℤ =>
      α (p.1 + p.2) - α p.1 - α p.2)).Finite)
    (hα' : (Set.range (fun p : ℤ × ℤ =>
      α' (p.1 + p.2) - α' p.1 - α' p.2)).Finite)
    (hβ : (Set.range (fun p : ℤ × ℤ =>
      β (p.1 + p.2) - β p.1 - β p.2)).Finite)
    (hβ' : (Set.range (fun p : ℤ × ℤ =>
      β' (p.1 + p.2) - β' p.1 - β' p.2)).Finite)
    (hαα' : (Set.range (fun n : ℤ => α n - α' n)).Finite)
    (hββ' : (Set.range (fun n : ℤ => β n - β' n)).Finite) :
    (Set.range (fun p : ℤ × ℤ =>
      α (β (p.1 + p.2)) - α (β p.1) - α (β p.2))).Finite ∧
    (Set.range (fun p : ℤ × ℤ =>
      α' (β' (p.1 + p.2)) - α' (β' p.1) - α' (β' p.2))).Finite ∧
    (Set.range (fun n : ℤ => α (β n) - α' (β' n))).Finite := by
  refine ⟨finite_range_defect_comp α β hα hβ,
    finite_range_defect_comp α' β' hα' hβ', ?_⟩
  have htranslate : (Set.range (fun n : ℤ =>
      α' (β n) - α' (β' n))).Finite :=
    finite_range_apply_eq_of_finite_defect α' β β' hα' hββ'
  refine ((hαα'.prod htranslate).image
    (fun q : ℤ × ℤ => q.1 + q.2)).subset ?_
  rw [Set.range_subset_iff]
  intro n
  refine ⟨(α (β n) - α' (β n),
      α' (β n) - α' (β' n)), ?_, ?_⟩
  · rw [Set.mem_prod]
    exact ⟨⟨β n, rfl⟩, ⟨n, rfl⟩⟩
  · dsimp
    ring

end Rollout_p1489_slope_composition_equivalent

#check_dependency_graph "Rollout_p1489_slope_composition_equivalent.slope_composition_equivalent" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(Set.range fun p => α (β (p.1 + p.2)) - α (β p.1) - α (β p.2)).Finite ∧ (Set.range fun p => α' (β' (p.1 + p.2)) - α' (β' p.1) - α' (β' p.2)).Finite ∧ (Set.range fun n => α (β n) - α' (β' n)).Finite\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hα\",\"statement\":\"(Set.range fun p => α (p.1 + p.2) - α p.1 - α p.2).Finite\"},{\"name\":\"hα'\",\"statement\":\"(Set.range fun p => α' (p.1 + p.2) - α' p.1 - α' p.2).Finite\"},{\"name\":\"hβ\",\"statement\":\"(Set.range fun p => β (p.1 + p.2) - β p.1 - β p.2).Finite\"},{\"name\":\"hβ'\",\"statement\":\"(Set.range fun p => β' (p.1 + p.2) - β' p.1 - β' p.2).Finite\"},{\"name\":\"hαα'\",\"statement\":\"(Set.range fun n => α n - α' n).Finite\"},{\"name\":\"hββ'\",\"statement\":\"(Set.range fun n => β n - β' n).Finite\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1489_slope_composition_equivalent\",\"reconstructedProofSha256\":\"edc19592d7558ea2f201c55e89147d2d9c5dc509df8cd60baa1bfe68e285a9d6\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1489_slope_composition_equivalent.slope_composition_equivalent\",\"topologySha256\":\"7a474cd4744979179ba1711124439a6e82dead9ccc91bf25655d868fb3d61174\"}"

namespace Rollout_p1572_not_biorderable_of_product_conjugates_eq_o

-- graph_id: p1572_not_biorderable_of_product_conjugates_eq_o
-- topology_sha256: 5ada9e25b8527e7bb3ae0d80bab4d4a3d543f5311c77d5c36a9536ad537bc67f
/- accepted add_to_file helper 1 -/
lemma list_prod_one_lt_of_forall_one_lt
    {G : Type*} [Group G] {r : G → G → Prop}
    (hsto : IsStrictTotalOrder G r)
    (hright : ∀ a b c : G, r a b ↔ r (a * c) (b * c))
    {l : List G} (hne : l ≠ []) (hpos : ∀ a ∈ l, r 1 a) :
    r 1 l.prod := by
  induction l with
  | nil => exact (hne rfl).elim
  | cons a l ih =>
      by_cases hl : l = []
      · subst l
        simpa using hpos a (by simp)
      · have ha : r 1 a := hpos a (by simp)
        have htail : r 1 l.prod := ih hl (fun b hb => hpos b (List.mem_cons_of_mem a hb))
        have hmul : r l.prod (a * l.prod) := by
          have h := (hright 1 a l.prod).mp ha
          simpa using h
        have hprod : r 1 (a * l.prod) := hsto.trans 1 l.prod (a * l.prod) htail hmul
        simpa [List.prod_cons] using hprod

lemma list_prod_lt_one_of_forall_lt_one
    {G : Type*} [Group G] {r : G → G → Prop}
    (hsto : IsStrictTotalOrder G r)
    (hright : ∀ a b c : G, r a b ↔ r (a * c) (b * c))
    {l : List G} (hne : l ≠ []) (hneg : ∀ a ∈ l, r a 1) :
    r l.prod 1 := by
  induction l with
  | nil => exact (hne rfl).elim
  | cons a l ih =>
      by_cases hl : l = []
      · subst l
        simpa using hneg a (by simp)
      · have ha : r a 1 := hneg a (by simp)
        have htail : r l.prod 1 := ih hl (fun b hb => hneg b (List.mem_cons_of_mem a hb))
        have hmul : r (a * l.prod) l.prod := by
          have h := (hright a 1 l.prod).mp ha
          simpa using h
        have hprod : r (a * l.prod) 1 := hsto.trans (a * l.prod) l.prod 1 hmul htail
        simpa [List.prod_cons] using hprod

/- accepted add_to_file helper 2 -/
lemma conj_mul_iff
    {G : Type*} [Group G] {r : G → G → Prop}
    (hleft : ∀ a b c : G, r a b ↔ r (c * a) (c * b))
    (hright : ∀ a b c : G, r a b ↔ r (a * c) (b * c))
    (x a b : G) :
    r (x⁻¹ * a * x) (x⁻¹ * b * x) ↔ r a b := by
  constructor
  · intro h
    have hmiddle : r (a * x) (b * x) := by
      have htransformed : r (x⁻¹ * (a * x)) (x⁻¹ * (b * x)) := by
        simpa [mul_assoc] using h
      exact (hleft (a * x) (b * x) x⁻¹).mpr htransformed
    exact (hright a b x).mpr hmiddle
  · intro h
    have hmiddle : r (a * x) (b * x) := (hright a b x).mp h
    have htransformed : r (x⁻¹ * (a * x)) (x⁻¹ * (b * x)) :=
      (hleft (a * x) (b * x) x⁻¹).mp hmiddle
    simpa [mul_assoc] using htransformed

/- verified submission -/
theorem not_biorderable_of_product_conjugates_eq_one
    {G : Type*} [Group G]
    (h : ∃ (g : G) (k : ℕ) (x : Fin k → G),
      g ≠ 1 ∧ 1 ≤ k ∧ (List.ofFn (fun i => (x i)⁻¹ * g * x i)).prod = 1) :
    ¬ ∃ r : G → G → Prop,
      IsStrictTotalOrder G r ∧
        (∀ a b c : G, r a b ↔ r (c * a) (c * b)) ∧
        (∀ a b c : G, r a b ↔ r (a * c) (b * c)) := by
  rintro ⟨r, hsto, hleft, hright⟩
  rcases h with ⟨g, k, x, hg, hk, hprod⟩
  let l : List G := List.ofFn (fun i => (x i)⁻¹ * g * x i)
  have hne : l ≠ [] := by
    dsimp [l]
    rw [List.ofFn_eq_nil_iff]
    omega
  have hside : r 1 g ∨ r g 1 := by
    by_cases hpos : r 1 g
    · exact Or.inl hpos
    · right
      by_contra hneg
      have heq : 1 = g := hsto.trichotomous 1 g hpos hneg
      exact hg heq.symm
  cases hside with
  | inl hpos =>
      have hall : ∀ a ∈ l, r 1 a := by
        intro a ha
        rcases List.mem_ofFn.mp ha with ⟨i, hi⟩
        have hci : r 1 ((x i)⁻¹ * g * x i) := by
          have hc := conj_mul_iff hleft hright (x i) 1 g
          simpa using hc.mpr hpos
        simpa [l, hi] using hci
      have hprodside : r 1 l.prod :=
        list_prod_one_lt_of_forall_one_lt hsto hright hne hall
      rw [show l.prod = 1 from hprod] at hprodside
      exact hsto.irrefl 1 hprodside
  | inr hneg =>
      have hall : ∀ a ∈ l, r a 1 := by
        intro a ha
        rcases List.mem_ofFn.mp ha with ⟨i, hi⟩
        have hci : r ((x i)⁻¹ * g * x i) 1 := by
          have hc := conj_mul_iff hleft hright (x i) g 1
          simpa using hc.mpr hneg
        simpa [l, hi] using hci
      have hprodside : r l.prod 1 :=
        list_prod_lt_one_of_forall_lt_one hsto hright hne hall
      rw [show l.prod = 1 from hprod] at hprodside
      exact hsto.irrefl 1 hprodside

end Rollout_p1572_not_biorderable_of_product_conjugates_eq_o

#check_dependency_graph "Rollout_p1572_not_biorderable_of_product_conjugates_eq_o.not_biorderable_of_product_conjugates_eq_one" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"False\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"h\",\"statement\":\"∃ g k x, g ≠ 1 ∧ 1 ≤ k ∧ (List.ofFn fun i => (x i)⁻¹ * g * x i).prod = 1\"},{\"name\":\"<generated-internal>\",\"statement\":\"∃ r, IsStrictTotalOrder G r ∧ (∀ (a b c : G), r a b ↔ r (c * a) (c * b)) ∧ ∀ (a b c : G), r a b ↔ r (a * c) (b * c)\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1572_not_biorderable_of_product_conjugates_eq_o\",\"reconstructedProofSha256\":\"60bc70dc6b1f49b2ddf30d1711286557dc83383f559e5352dd6b45603efdc2dd\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1572_not_biorderable_of_product_conjugates_eq_o.not_biorderable_of_product_conjugates_eq_one\",\"topologySha256\":\"5ada9e25b8527e7bb3ae0d80bab4d4a3d543f5311c77d5c36a9536ad537bc67f\"}"

namespace Rollout_p1664_paired_complex_tuple_set_convex

-- graph_id: p1664_paired_complex_tuple_set_convex
-- topology_sha256: b4be8d3735c355ac6e653e0f9dd5a2845135be269c517bc5360bd2601e64ce1b
/- accepted add_to_file helper 1 -/
lemma strict_combination_pos {a b x y : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : 0 < x) (hy : 0 < y) :
    0 < a * x + b * y := by
  by_cases h : a = 0
  · have hb' : b = 1 := by linarith
    rw [h, hb']
    simpa using hy
  · have ha' : 0 < a := lt_of_le_of_ne ha (fun hzero => h hzero.symm)
    exact add_pos_of_pos_of_nonneg (mul_pos ha' hx)
      (mul_nonneg hb (le_of_lt hy))

lemma strict_combination_neg {a b x y : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : x < 0) (hy : y < 0) :
    a * x + b * y < 0 := by
  have hpos : 0 < a * (-x) + b * (-y) :=
    strict_combination_pos ha hb hab (neg_pos.mpr hx) (neg_pos.mpr hy)
  linarith

/- verified submission -/
theorem paired_complex_tuple_set_convex
    (l m : ℕ) (hl : 0 < l) (hm : 0 < m)
    (σ : Fin (l + m) → Fin (l + m))
    (hσ_involutive : Function.Involutive σ)
    (hσ_fixedPointFree : ∀ i, σ i ≠ i) :
    Convex ℝ {ζ : Fin (l + m) → ℂ |
      (∀ i, ζ i = ζ (σ i)) ∧
      (∀ i, 0 < (ζ i).re) ∧
      (∀ i : ℕ, 1 ≤ i → i < l →
        0 < (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => k.val < i), ζ k).im) ∧
      (∀ j : ℕ, 1 ≤ j → j < m →
        (∑ k ∈ Finset.univ.filter
          (fun k : Fin (l + m) => l ≤ k.val ∧ k.val < l + j), ζ k).im < 0) ∧
      (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => k.val < l), ζ k) =
        ∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => l ≤ k.val), ζ k} := by
  intro ζ hζ η hη a b ha hb hab
  constructor
  · intro i
    have hzi := hζ.1 i
    have hei := hη.1 i
    simp [Pi.add_apply, Pi.smul_apply, hzi, hei]
  · constructor
    · intro i
      simpa [Pi.add_apply, Pi.smul_apply] using
        strict_combination_pos ha hb hab (hζ.2.1 i) (hη.2.1 i)
    · constructor
      · intro i hi1 hil
        simpa [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, Finset.mul_sum] using
          strict_combination_pos ha hb hab
            (hζ.2.2.1 i hi1 hil) (hη.2.2.1 i hi1 hil)
      · constructor
        · intro j hj1 hjm
          simpa [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, Finset.mul_sum] using
            strict_combination_neg ha hb hab
              (hζ.2.2.2.1 j hj1 hjm) (hη.2.2.2.1 j hj1 hjm)
        · have hzsum := hζ.2.2.2.2
          have hηsum := hη.2.2.2.2
          have hleft :
              (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => k.val < l),
                  (a • ζ + b • η) k) =
                a * (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => k.val < l), ζ k) +
                  b * (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => k.val < l), η k) := by
            simp [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, Finset.mul_sum]
          have hright :
              (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => l ≤ k.val),
                  (a • ζ + b • η) k) =
                a * (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => l ≤ k.val), ζ k) +
                  b * (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => l ≤ k.val), η k) := by
            simp [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib, Finset.mul_sum]
          calc
            (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => k.val < l),
                (a • ζ + b • η) k)
                = a * (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => k.val < l), ζ k) +
                    b * (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => k.val < l), η k) :=
              hleft
            _ = a * (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => l ≤ k.val), ζ k) +
                    b * (∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => l ≤ k.val), η k) := by
              rw [hzsum, hηsum]
            _ = ∑ k ∈ Finset.univ.filter (fun k : Fin (l + m) => l ≤ k.val),
                    (a • ζ + b • η) k :=
              hright.symm

end Rollout_p1664_paired_complex_tuple_set_convex

#check_dependency_graph "Rollout_p1664_paired_complex_tuple_set_convex.paired_complex_tuple_set_convex" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(∀ (i : Fin (l + m)), (a • ζ + b • η) i = (a • ζ + b • η) (σ i)) ∧ (∀ (i : Fin (l + m)), 0 < ((a • ζ + b • η) i).re) ∧ (∀ (i : ℕ), 1 ≤ i → i < l → 0 < (∑ k with ↑k < i, (a • ζ + b • η) k).im) ∧ (∀ (j : ℕ), 1 ≤ j → j < m → (∑ k with l ≤ ↑k ∧ ↑k < l + j, (a • ζ + b • η) k).im < 0) ∧ ∑ k with ↑k < l, (a • ζ + b • η) k = ∑ k with l ≤ ↑k, (a • ζ + b • η) k\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hζ\",\"statement\":\"ζ ∈ {ζ | (∀ (i : Fin (l + m)), ζ i = ζ (σ i)) ∧ (∀ (i : Fin (l + m)), 0 < (ζ i).re) ∧ (∀ (i : ℕ), 1 ≤ i → i < l → 0 < (∑ k with ↑k < i, ζ k).im) ∧ (∀ (j : ℕ), 1 ≤ j → j < m → (∑ k with l ≤ ↑k ∧ ↑k < l + j, ζ k).im < 0) ∧ ∑ k with ↑k < l, ζ k = ∑ k with l ≤ ↑k, ζ k}\"},{\"name\":\"hη\",\"statement\":\"η ∈ {ζ | (∀ (i : Fin (l + m)), ζ i = ζ (σ i)) ∧ (∀ (i : Fin (l + m)), 0 < (ζ i).re) ∧ (∀ (i : ℕ), 1 ≤ i → i < l → 0 < (∑ k with ↑k < i, ζ k).im) ∧ (∀ (j : ℕ), 1 ≤ j → j < m → (∑ k with l ≤ ↑k ∧ ↑k < l + j, ζ k).im < 0) ∧ ∑ k with ↑k < l, ζ k = ∑ k with l ≤ ↑k, ζ k}\"},{\"name\":\"ha\",\"statement\":\"0 ≤ a\"},{\"name\":\"hb\",\"statement\":\"0 ≤ b\"},{\"name\":\"hab\",\"statement\":\"a + b = 1\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1664_paired_complex_tuple_set_convex\",\"reconstructedProofSha256\":\"3a40aae3bbd5d18b0cace7dde1732824229edf593609c335fcbdcc29088f16e5\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1664_paired_complex_tuple_set_convex.paired_complex_tuple_set_convex\",\"topologySha256\":\"b4be8d3735c355ac6e653e0f9dd5a2845135be269c517bc5360bd2601e64ce1b\"}"

namespace Rollout_p1763_basel_series

-- graph_id: p1763_basel_series
-- topology_sha256: 2f0bedcf54f8c11e6853d12d594dd879fa3f5a8a0457c32c42442f518da051ce
/- verified submission -/
theorem basel_series : HasSum (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) (Real.pi ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (g := Real.pi ^ 2 / 6) 1).mpr (by
    simpa using hasSum_zeta_two)
  simpa using h

end Rollout_p1763_basel_series

#check_dependency_graph "Rollout_p1763_basel_series.basel_series" against "{\"edges\":[{\"conclusion\":{\"name\":\"h\",\"statement\":\"HasSum (fun n => 1 / ↑(n + 1) ^ 2) (Real.pi ^ 2 / 6)\"},\"graphEdgeId\":\"h_001_h\",\"premises\":[],\"rawEdgeId\":\"telescope_0\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"HasSum (fun n => 1 / ↑(n + 1) ^ 2) (Real.pi ^ 2 / 6)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"h\",\"statement\":\"HasSum (fun n => 1 / ↑(n + 1) ^ 2) (Real.pi ^ 2 / 6)\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1763_basel_series\",\"reconstructedProofSha256\":\"5cbe8371261b27b8dde866f5a57d66458163a40c7ca4693e6ee3bdecfe02a04e\",\"selectedEdgeCount\":2,\"theoremName\":\"Rollout_p1763_basel_series.basel_series\",\"topologySha256\":\"2f0bedcf54f8c11e6853d12d594dd879fa3f5a8a0457c32c42442f518da051ce\"}"

namespace Rollout_p1789_seminormal_reesquotient_iff_radical

-- graph_id: p1789_seminormal_reesquotient_iff_radical
-- topology_sha256: ba053d0b8197efdea1b134528fc3518ef2231a2339087641ccb0f7b7557bbc6b
/- accepted add_to_file helper 1 -/
lemma pow_eq_zero_of_le_pow_eq_zero {M : Type*} [MonoidWithZero M] {x : M} {n k : ℕ}
    (h : n ≤ k) (hx : x ^ n = 0) : x ^ k = 0 := by
  rw [← Nat.add_sub_of_le h, pow_add, hx, zero_mul]

lemma pow_eq_zero_of_reduced {M : Type*} [CommMonoidWithZero M]
    (hred : ∀ a b : M, a ^ 2 = b ^ 2 → a ^ 3 = b ^ 3 → a = b)
    {x : M} : ∀ {n : ℕ}, 1 ≤ n → x ^ n = 0 → x = 0 := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih h1 hx
  by_cases hn : n ≤ 1
  · have hn_eq : n = 1 := by omega
    subst n
    simpa using hx
  · let m := (n + 1) / 2
    have hn2 : 2 ≤ n := by omega
    have hm1 : 1 ≤ m := by
      dsimp [m]
      omega
    have hmn : m < n := by
      dsimp [m]
      omega
    have hn2m : n ≤ 2 * m := by
      dsimp [m]
      omega
    have hn3m : n ≤ 3 * m := by
      dsimp [m]
      omega
    have hx2m : x ^ (2 * m) = 0 := pow_eq_zero_of_le_pow_eq_zero hn2m hx
    have hx3m : x ^ (3 * m) = 0 := pow_eq_zero_of_le_pow_eq_zero hn3m hx
    have hsq : (x ^ m) ^ 2 = (0 : M) ^ 2 := by
      calc
        (x ^ m) ^ 2 = x ^ (m * 2) := by rw [pow_mul]
        _ = x ^ (2 * m) := by rw [Nat.mul_comm]
        _ = 0 := hx2m
        _ = (0 : M) ^ 2 := by simp
    have hcube : (x ^ m) ^ 3 = (0 : M) ^ 3 := by
      calc
        (x ^ m) ^ 3 = x ^ (m * 3) := by rw [pow_mul]
        _ = x ^ (3 * m) := by rw [Nat.mul_comm]
        _ = 0 := hx3m
        _ = (0 : M) ^ 3 := by simp
    exact ih m hmn hm1 (hred (x ^ m) 0 hsq hcube)

/- accepted add_to_file helper 2 -/
lemma monoidWithZeroHom_eq_zero_iff_mem_of_fiber {A B : Type*}
    [CommMonoidWithZero A] [CommMonoidWithZero B]
    (q : A →*₀ B) (I : SemigroupIdeal A) (hI_zero : (0 : A) ∈ I)
    (hq_fiber : ∀ a b : A, q a = q b ↔ a = b ∨ (a ∈ I ∧ b ∈ I))
    (a : A) : q a = 0 ↔ a ∈ I := by
  constructor
  · intro ha
    have hfiber : q a = q 0 := by simpa using ha
    rcases (hq_fiber a 0).mp hfiber with rfl | hmem
    · exact hI_zero
    · exact hmem.1
  · intro ha
    have hfiber : q a = q 0 :=
      (hq_fiber a 0).mpr (Or.inr ⟨ha, hI_zero⟩)
    simpa using hfiber

/- verified submission -/
theorem seminormal_reesQuotient_iff_radical
    {A C B : Type*}
    [CommMonoidWithZero A] [CommMonoidWithZero C] [IsCancelMulZero C]
    [CommMonoidWithZero B]
    (J : SemigroupIdeal C)
    (hJ_zero : (0 : C) ∈ J)
    (p : C →*₀ A)
    (hp_surjective : Function.Surjective p)
    (hp_fiber : ∀ c d : C, p c = p d ↔ c = d ∨ (c ∈ J ∧ d ∈ J))
    (hA :
      (∀ a b : A, a ^ 2 = b ^ 2 → a ^ 3 = b ^ 3 → a = b) ∧
      (∀ x y : A, x ^ 3 = y ^ 2 → ∃ z : A, x = z ^ 2 ∧ y = z ^ 3))
    (I : SemigroupIdeal A)
    (hI_zero : (0 : A) ∈ I)
    (q : A →*₀ B)
    (hq_surjective : Function.Surjective q)
    (hq_fiber : ∀ a b : A, q a = q b ↔ a = b ∨ (a ∈ I ∧ b ∈ I)) :
    ((∀ a b : B, a ^ 2 = b ^ 2 → a ^ 3 = b ^ 3 → a = b) ∧
        (∀ x y : B, x ^ 3 = y ^ 2 → ∃ z : B, x = z ^ 2 ∧ y = z ^ 3)) ↔
      ∀ a : A, (∃ n : ℕ, 1 ≤ n ∧ a ^ n ∈ I) → a ∈ I := by
  let qzero : ∀ a : A, q a = 0 ↔ a ∈ I :=
    fun a => monoidWithZeroHom_eq_zero_iff_mem_of_fiber q I hI_zero hq_fiber a
  constructor
  · intro hB a ha
    rcases ha with ⟨n, hn, han⟩
    have hqan : q (a ^ n) = 0 := (qzero (a ^ n)).mpr han
    have hpow : (q a) ^ n = 0 := by
      calc
        (q a) ^ n = q (a ^ n) := by rw [map_pow]
        _ = 0 := hqan
    have hqa : q a = 0 := pow_eq_zero_of_reduced hB.1 hn hpow
    exact (qzero a).mp hqa
  · intro hrad
    have q_eq_of_mem : ∀ {a b : A}, a ∈ I → b ∈ I → q a = q b := by
      intro a b ha hb
      exact (hq_fiber a b).mpr (Or.inr ⟨ha, hb⟩)
    have cube_mem_of_sq_mem : ∀ {a : A}, a ^ 2 ∈ I → a ^ 3 ∈ I := by
      intro a ha
      have hmul := I.mul_mem a ha
      simpa [pow_two, pow_three] using hmul
    constructor
    · intro x y h2 h3
      obtain ⟨a, rfl⟩ := hq_surjective x
      obtain ⟨b, rfl⟩ := hq_surjective y
      have h2A : q (a ^ 2) = q (b ^ 2) := by
        simpa [map_pow] using h2
      have h3A : q (a ^ 3) = q (b ^ 3) := by
        simpa [map_pow] using h3
      rcases (hq_fiber (a ^ 2) (b ^ 2)).mp h2A with hpow2 | hpow2I
      · rcases (hq_fiber (a ^ 3) (b ^ 3)).mp h3A with hpow3 | hpow3I
        · have hab : a = b := hA.1 a b hpow2 hpow3
          simpa [hab]
        · have haI : a ∈ I := hrad a ⟨3, by norm_num, hpow3I.1⟩
          have hbI : b ∈ I := hrad b ⟨3, by norm_num, hpow3I.2⟩
          exact q_eq_of_mem haI hbI
      · have ha3I : a ^ 3 ∈ I := cube_mem_of_sq_mem hpow2I.1
        have hb3I : b ^ 3 ∈ I := cube_mem_of_sq_mem hpow2I.2
        have haI : a ∈ I := hrad a ⟨3, by norm_num, ha3I⟩
        have hbI : b ∈ I := hrad b ⟨3, by norm_num, hb3I⟩
        exact q_eq_of_mem haI hbI
    · intro x y hxy
      obtain ⟨a, rfl⟩ := hq_surjective x
      obtain ⟨b, rfl⟩ := hq_surjective y
      have hxyA : q (a ^ 3) = q (b ^ 2) := by
        simpa [map_pow] using hxy
      rcases (hq_fiber (a ^ 3) (b ^ 2)).mp hxyA with hpow | hpowI
      · obtain ⟨z, haz, hbz⟩ := hA.2 a b hpow
        refine ⟨q z, ?_, ?_⟩
        · calc
            q a = q (z ^ 2) := congrArg q haz
            _ = (q z) ^ 2 := by rw [map_pow]
        · calc
            q b = q (z ^ 3) := congrArg q hbz
            _ = (q z) ^ 3 := by rw [map_pow]
      · have haI : a ∈ I := hrad a ⟨3, by norm_num, hpowI.1⟩
        have hbI : b ∈ I := hrad b ⟨2, by norm_num, hpowI.2⟩
        have hqa : q a = 0 := (qzero a).mpr haI
        have hqb : q b = 0 := (qzero b).mpr hbI
        refine ⟨0, ?_, ?_⟩
        · simpa using hqa
        · simpa using hqb

end Rollout_p1789_seminormal_reesquotient_iff_radical

#check_dependency_graph "Rollout_p1789_seminormal_reesquotient_iff_radical.seminormal_reesQuotient_iff_radical" against "{\"edges\":[{\"conclusion\":{\"name\":\"qzero\",\"statement\":\"∀ (a : A), q a = 0 ↔ a ∈ I\"},\"graphEdgeId\":\"h_001_qzero\",\"premises\":[{\"name\":\"hI_zero\",\"statement\":\"0 ∈ I\"},{\"name\":\"hq_fiber\",\"statement\":\"∀ (a b : A), q a = q b ↔ a = b ∨ a ∈ I ∧ b ∈ I\"}],\"rawEdgeId\":\"telescope_18\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"((∀ (a b : B), a ^ 2 = b ^ 2 → a ^ 3 = b ^ 3 → a = b) ∧ ∀ (x y : B), x ^ 3 = y ^ 2 → ∃ z, x = z ^ 2 ∧ y = z ^ 3) ↔ ∀ (a : A), (∃ n, 1 ≤ n ∧ a ^ n ∈ I) → a ∈ I\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hA\",\"statement\":\"(∀ (a b : A), a ^ 2 = b ^ 2 → a ^ 3 = b ^ 3 → a = b) ∧ ∀ (x y : A), x ^ 3 = y ^ 2 → ∃ z, x = z ^ 2 ∧ y = z ^ 3\"},{\"name\":\"hq_surjective\",\"statement\":\"Function.Surjective ⇑q\"},{\"name\":\"hq_fiber\",\"statement\":\"∀ (a b : A), q a = q b ↔ a = b ∨ a ∈ I ∧ b ∈ I\"},{\"name\":\"qzero\",\"statement\":\"∀ (a : A), q a = 0 ↔ a ∈ I\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1789_seminormal_reesquotient_iff_radical\",\"reconstructedProofSha256\":\"379973a697649061a081e28af55a3be7336dc113ceab4cda492ba0301a90d144\",\"selectedEdgeCount\":2,\"theoremName\":\"Rollout_p1789_seminormal_reesquotient_iff_radical.seminormal_reesQuotient_iff_radical\",\"topologySha256\":\"ba053d0b8197efdea1b134528fc3518ef2231a2339087641ccb0f7b7557bbc6b\"}"

namespace Rollout_p1925_exists_coloring_increasing_pairs

-- graph_id: p1925_exists_coloring_increasing_pairs
-- topology_sha256: 3f6427c70203b3e4c6d2749063d02e365dd26f2c1c125c6c882c4d8315e787fc
/- verified submission -/
theorem exists_coloring_increasing_pairs :
    ∃ c : ℕ × ℕ → ℕ,
      (∀ n m : ℕ, n < m → c (n, m) < m) ∧
      ∀ n k : ℕ, ∀ B : Set ℕ, B.Infinite →
        ∃ m ∈ B, n < m ∧ k ≤ c (n, m) := by
  use fun p => p.2 - 1
  constructor
  · intro n m h
    show m - 1 < m
    omega
  · intro n k B hB
    obtain ⟨m, hmB, hm⟩ := hB.exists_gt (max n k)
    refine ⟨m, hmB, lt_of_le_of_lt (Nat.le_max_left n k) hm, ?_⟩
    show k ≤ m - 1
    have := Nat.le_max_right n k
    omega

end Rollout_p1925_exists_coloring_increasing_pairs

#check_dependency_graph "Rollout_p1925_exists_coloring_increasing_pairs.exists_coloring_increasing_pairs" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∃ c, (∀ (n m : ℕ), n < m → c (n, m) < m) ∧ ∀ (n k : ℕ) (B : Set ℕ), B.Infinite → ∃ m ∈ B, n < m ∧ k ≤ c (n, m)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1925_exists_coloring_increasing_pairs\",\"reconstructedProofSha256\":\"be917624507e7ca877bbb0ccdf84a7409e55d13a709a8e6be08d7646f947c77f\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p1925_exists_coloring_increasing_pairs.exists_coloring_increasing_pairs\",\"topologySha256\":\"3f6427c70203b3e4c6d2749063d02e365dd26f2c1c125c6c882c4d8315e787fc\"}"

namespace Rollout_p2061_fixed_disc_of_contractivity

-- graph_id: p2061_fixed_disc_of_contractivity
-- topology_sha256: cdaf7feb9a824a85005a206c49841c05ff511f246426e3bdb3992b5cb809e336
/- verified submission -/
theorem fixed_disc_of_contractivity
    {X : Type*} [MetricSpace X]
    (T : X → X) (x₀ : X) (c : ℝ)
    (hc₀ : 0 ≤ c) (hc₁ : c < 1)
    (hcontractive : ∀ x : X, dist (T x) x ≤ c * dist (T x) x₀) :
    let ρ : ℝ := sInf {r : ℝ | ∃ x : X, T x ≠ x ∧ r = dist x (T x)}
    (∀ x : X, dist x x₀ ≤ ρ → x ≠ x₀ →
      0 < dist (T x) x₀ ∧ dist (T x) x₀ ≤ ρ) →
    ∀ x : X, dist x x₀ ≤ ρ → T x = x := by
  dsimp only
  intro h x hx
  by_cases hx0 : x = x₀
  · subst x
    by_cases hdpos : 0 < dist (T x₀) x₀
    · have hlt : c * dist (T x₀) x₀ < dist (T x₀) x₀ := by
        simpa using mul_lt_mul_of_pos_right hc₁ hdpos
      exact (not_lt_of_ge (hcontractive x₀) hlt).elim
    · have hd : dist (T x₀) x₀ = 0 := by
        exact le_antisymm (not_lt.mp hdpos) dist_nonneg
      exact dist_eq_zero.mp hd
  · by_contra hTx
    let S : Set ℝ := {r : ℝ | ∃ y : X, T y ≠ y ∧ r = dist y (T y)}
    have hSbdd : BddBelow S := by
      refine ⟨0, ?_⟩
      intro r hr
      rcases hr with ⟨y, hy, rfl⟩
      exact dist_nonneg
    have hSmem : dist x (T x) ∈ S := ⟨x, hTx, rfl⟩
    have hρ_le : sInf S ≤ dist x (T x) := csInf_le hSbdd hSmem
    have ha := h x hx hx0
    have hcon : dist x (T x) ≤ c * dist (T x) x₀ := by
      simpa [dist_comm] using hcontractive x
    have hlt : c * dist (T x) x₀ < dist (T x) x₀ := by
      simpa using mul_lt_mul_of_pos_right hc₁ ha.1
    have : sInf S < sInf S := by
      exact lt_of_lt_of_le
        (lt_of_le_of_lt (le_trans hρ_le hcon) hlt)
        ha.2
    exact (lt_irrefl (sInf S) this).elim

end Rollout_p2061_fixed_disc_of_contractivity

#check_dependency_graph "Rollout_p2061_fixed_disc_of_contractivity.fixed_disc_of_contractivity" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let ρ := sInf {r | ∃ x, T x ≠ x ∧ r = dist x (T x)}; (∀ (x : X), dist x x₀ ≤ ρ → x ≠ x₀ → 0 < dist (T x) x₀ ∧ dist (T x) x₀ ≤ ρ) → ∀ (x : X), dist x x₀ ≤ ρ → T x = x\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hc₁\",\"statement\":\"c < 1\"},{\"name\":\"hcontractive\",\"statement\":\"∀ (x : X), dist (T x) x ≤ c * dist (T x) x₀\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2061_fixed_disc_of_contractivity\",\"reconstructedProofSha256\":\"14a2e8f7c45aef925550aa76973c623083cf4d281916d470461e3b14635aefec\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p2061_fixed_disc_of_contractivity.fixed_disc_of_contractivity\",\"topologySha256\":\"cdaf7feb9a824a85005a206c49841c05ff511f246426e3bdb3992b5cb809e336\"}"

namespace Rollout_p2404_abelian_surjective_add_id_star_commute

-- graph_id: p2404_abelian_surjective_add_id_star_commute
-- topology_sha256: 69f2cf3836ce8fc06e2967a6e32e72fdd62ebbb926a939b0967eab84873aa4af
/- verified submission -/
theorem abelian_surjective_add_id_star_commute
    {A : Type*} [AddCommGroup A] (φ : A →+ A)
    (hφ : Function.Surjective φ) :
    let ψ : A → A := fun a ↦ φ a + a
    Function.Commute φ ψ ∧
      ∀ x y : A, ψ x = φ y → ∃! z : A, φ z = x ∧ ψ z = y := by
  let ψ : A → A := fun a ↦ φ a + a
  constructor
  · intro a
    change φ (ψ a) = ψ (φ a)
    dsimp [ψ]
    simp [map_add, add_comm]
  · intro x y hxy
    have hxy' : ψ x = φ y := hxy
    refine ⟨y - x, ?_, ?_⟩
    · constructor
      · calc
          φ (y - x) = φ y - φ x := AddMonoidHom.map_sub φ y x
          _ = ψ x - φ x := by rw [← hxy']
          _ = x := by
            dsimp [ψ]
            abel
      · calc
          ψ (y - x) = φ (y - x) + (y - x) := rfl
          _ = x + (y - x) := by
            congr 1
            calc
              φ (y - x) = φ y - φ x := AddMonoidHom.map_sub φ y x
              _ = ψ x - φ x := by rw [← hxy']
              _ = x := by
                dsimp [ψ]
                abel
          _ = y := by abel
    · intro z hz
      have hzψ : ψ z = y := hz.2
      calc
        z = ψ z - φ z := by
          dsimp [ψ]
          abel
        _ = y - x := by rw [hzψ, hz.1]

end Rollout_p2404_abelian_surjective_add_id_star_commute

#check_dependency_graph "Rollout_p2404_abelian_surjective_add_id_star_commute.abelian_surjective_add_id_star_commute" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(Function.Commute ⇑φ fun a => φ a + a) ∧ ∀ (x y : A), (fun a => φ a + a) x = φ y → ∃! z, φ z = x ∧ (fun a => φ a + a) z = y\"},\"graphEdgeId\":\"h_goal\",\"premises\":[],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2404_abelian_surjective_add_id_star_commute\",\"reconstructedProofSha256\":\"5ad69869682c42ad676a89f591ed465ee0f23afa9a66d3ddad067fbbb9523b3b\",\"selectedEdgeCount\":1,\"theoremName\":\"Rollout_p2404_abelian_surjective_add_id_star_commute.abelian_surjective_add_id_star_commute\",\"topologySha256\":\"69f2cf3836ce8fc06e2967a6e32e72fdd62ebbb926a939b0967eab84873aa4af\"}"

namespace Rollout_p3210_substochastic_row_update_product

-- graph_id: p3210_substochastic_row_update_product
-- topology_sha256: db50fe190604d05227612447bcc66f9ea76bc24aec9dacd3acf69bb671db2c27
/- accepted add_to_file helper 1 -/
lemma row_update_prod_invariant
    (N : ℕ)
    (C : Matrix (Fin N) (Fin N) ℝ)
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (r : ℝ)
    (hr : IsGreatest (Set.range (fun i : Fin N => ∑ j : Fin N, C i j)) r)
    (hr_lt_one : r < 1)
    (l : List (Fin N)) :
    (∀ x : Fin N,
      (∑ j : Fin N,
        (l.map (fun a : Fin N =>
          Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) a (C a))).prod x j) ≤ 1) ∧
    (∀ i : Fin N, i ∈ l →
      (∑ j : Fin N,
        (l.map (fun a : Fin N =>
          Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) a (C a))).prod i j) ≤ r) := by
  classical
  induction l with
  | nil =>
      constructor
      · intro x
        simp [Matrix.one_apply]
      · intro i hi
        simp at hi
  | cons a t ih =>
      obtain ⟨ih_one, ih_r⟩ := ih
      have hCa : (∑ j : Fin N, C a j) ≤ r := by
        exact hr.2 (by exact ⟨a, rfl⟩)
      have hrow_a :
          (∑ j : Fin N,
            ((Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) a (C a)) *
              (t.map (fun b : Fin N =>
                Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) b (C b))).prod) a j) ≤ r := by
        calc
          (∑ j : Fin N,
            ((Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) a (C a)) *
              (t.map (fun b : Fin N =>
                Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) b (C b))).prod) a j)
              = ∑ k : Fin N, C a k *
                (∑ j : Fin N,
                  (t.map (fun b : Fin N =>
                    Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) b (C b))).prod k j) := by
                rw [Matrix.updateRow_mul, Matrix.one_mul]
                simp [Matrix.vecMul, dotProduct, Finset.mul_sum]
                rw [Finset.sum_comm]
          _ ≤ ∑ k : Fin N, C a k * 1 := by
                exact Finset.sum_le_sum (fun k _ =>
                  mul_le_mul_of_nonneg_left (ih_one k) (hC_nonneg a k))
          _ = ∑ k : Fin N, C a k := by simp
          _ ≤ r := hCa
      constructor
      · intro x
        simp only [List.map_cons, List.prod_cons]
        by_cases hxa : x = a
        · subst x
          exact le_trans hrow_a (le_of_lt hr_lt_one)
        · have hrow_eq :
              (∑ j : Fin N,
                ((Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) a (C a)) *
                  (t.map (fun b : Fin N =>
                    Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) b (C b))).prod) x j)
                = ∑ j : Fin N,
                  (t.map (fun b : Fin N =>
                    Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) b (C b))).prod x j := by
            rw [Matrix.updateRow_mul, Matrix.one_mul]
            simp [Matrix.updateRow_ne hxa]
          rw [hrow_eq]
          exact ih_one x
      · intro i hi
        simp only [List.map_cons, List.prod_cons]
        by_cases hia : i = a
        · subst i
          exact hrow_a
        · have hit : i ∈ t := by
            simp [hia] at hi
            exact hi
          have hrow_eq :
              (∑ j : Fin N,
                ((Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) a (C a)) *
                  (t.map (fun b : Fin N =>
                    Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) b (C b))).prod) i j)
                = ∑ j : Fin N,
                  (t.map (fun b : Fin N =>
                    Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) b (C b))).prod i j := by
            rw [Matrix.updateRow_mul, Matrix.one_mul]
            simp [Matrix.updateRow_ne hia]
          rw [hrow_eq]
          exact ih_r i hit

/- verified submission -/
theorem substochastic_row_update_product
    (N : ℕ) (hN : 1 ≤ N)
    (C : Matrix (Fin N) (Fin N) ℝ)
    (hC_nonneg : ∀ i j, 0 ≤ C i j)
    (hC_diag : ∀ i, C i i = 0)
    (r : ℝ)
    (hr : IsGreatest (Set.range (fun i : Fin N => ∑ j : Fin N, C i j)) r)
    (hr_lt_one : r < 1)
    (Q : Matrix (Fin N) (Fin N) ℝ)
    (hQ : Q = (List.ofFn (fun i : Fin N =>
      Matrix.updateRow (1 : Matrix (Fin N) (Fin N) ℝ) i (C i))).reverse.prod) :
    ∀ i : Fin N, (∑ j : Fin N, Q i j) ≤ r := by
  classical
  intro i
  let idx : List (Fin N) := List.ofFn (fun i : Fin N => i)
  have hinvariant := row_update_prod_invariant N C hC_nonneg r hr hr_lt_one idx.reverse
  have hi_idx : i ∈ idx := by
    dsimp [idx]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  have hi : i ∈ idx.reverse := by
    exact List.mem_reverse.mpr hi_idx
  have hbound := hinvariant.2 i hi
  rw [hQ]
  simpa [idx, List.map_reverse] using hbound

end Rollout_p3210_substochastic_row_update_product

#check_dependency_graph "Rollout_p3210_substochastic_row_update_product.substochastic_row_update_product" against "{\"edges\":[{\"conclusion\":{\"name\":\"hinvariant\",\"statement\":\"(∀ (x : Fin N), ∑ j, (List.map (fun a => Matrix.updateRow 1 a (C a)) idx.reverse).prod x j ≤ 1) ∧ ∀ i ∈ idx.reverse, ∑ j, (List.map (fun a => Matrix.updateRow 1 a (C a)) idx.reverse).prod i j ≤ r\"},\"graphEdgeId\":\"h_001_hinvariant\",\"premises\":[{\"name\":\"hC_nonneg\",\"statement\":\"∀ (i j : Fin N), 0 ≤ C i j\"},{\"name\":\"hr\",\"statement\":\"IsGreatest (Set.range fun i => ∑ j, C i j) r\"},{\"name\":\"hr_lt_one\",\"statement\":\"r < 1\"}],\"rawEdgeId\":\"telescope_12\"},{\"conclusion\":{\"name\":\"hi_idx\",\"statement\":\"i ∈ idx\"},\"graphEdgeId\":\"h_002_hi_idx\",\"premises\":[],\"rawEdgeId\":\"telescope_13\"},{\"conclusion\":{\"name\":\"hi\",\"statement\":\"i ∈ idx.reverse\"},\"graphEdgeId\":\"h_003_hi\",\"premises\":[{\"name\":\"hi_idx\",\"statement\":\"i ∈ idx\"}],\"rawEdgeId\":\"telescope_14\"},{\"conclusion\":{\"name\":\"hbound\",\"statement\":\"∑ j, (List.map (fun a => Matrix.updateRow 1 a (C a)) idx.reverse).prod i j ≤ r\"},\"graphEdgeId\":\"h_004_hbound\",\"premises\":[{\"name\":\"hinvariant\",\"statement\":\"(∀ (x : Fin N), ∑ j, (List.map (fun a => Matrix.updateRow 1 a (C a)) idx.reverse).prod x j ≤ 1) ∧ ∀ i ∈ idx.reverse, ∑ j, (List.map (fun a => Matrix.updateRow 1 a (C a)) idx.reverse).prod i j ≤ r\"},{\"name\":\"hi\",\"statement\":\"i ∈ idx.reverse\"}],\"rawEdgeId\":\"telescope_15\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∑ j, Q i j ≤ r\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hQ\",\"statement\":\"Q = (List.ofFn fun i => Matrix.updateRow 1 i (C i)).reverse.prod\"},{\"name\":\"hbound\",\"statement\":\"∑ j, (List.map (fun a => Matrix.updateRow 1 a (C a)) idx.reverse).prod i j ≤ r\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p3210_substochastic_row_update_product\",\"reconstructedProofSha256\":\"586b32f872bf55ac03d029f74b950b2711def373c5f545730f7a1858a3a88969\",\"selectedEdgeCount\":5,\"theoremName\":\"Rollout_p3210_substochastic_row_update_product.substochastic_row_update_product\",\"topologySha256\":\"db50fe190604d05227612447bcc66f9ea76bc24aec9dacd3acf69bb671db2c27\"}"

namespace Rollout_p3260_group_symmetrization_lipschitz

-- graph_id: p3260_group_symmetrization_lipschitz
-- topology_sha256: 98cc2ec8af7eb795746b45890d773629394f9177fe3dbdba47ff1373fbbd3200
/- verified submission -/
theorem group_symmetrization_lipschitz
    (D : ℕ)
    (X : Set (EuclideanSpace ℝ (Fin D)))
    (G : Type*) [Group G] [Fintype G] [MulAction G X]
    (hact : ∀ (g : G) (x y : X),
      ‖(↑(g • x) : EuclideanSpace ℝ (Fin D)) - ↑(g • y)‖ ≤
        ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖)
    (L : ℝ) (hL : 0 ≤ L)
    (f : X → ℝ)
    (hf : ∀ x y : X,
      |f x - f y| ≤ L * ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖) :
    ∀ x y : X,
      |((∑ g : G, f (g • x)) / (Fintype.card G : ℝ)) -
          ((∑ g : G, f (g • y)) / (Fintype.card G : ℝ))| ≤
        L * ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖ := by
  intro x y
  let C : ℝ := Fintype.card G
  have hCpos : 0 < C := by
    dsimp [C]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hterm : ∀ g : G,
      |f (g • x) - f (g • y)| ≤
        L * ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖ := by
    intro g
    calc
      |f (g • x) - f (g • y)| ≤
          L * ‖(↑(g • x) : EuclideanSpace ℝ (Fin D)) - ↑(g • y)‖ :=
        hf (g • x) (g • y)
      _ ≤ L * ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖ :=
        mul_le_mul_of_nonneg_left (hact g x y) hL
  have hsum :
      |(∑ g : G, f (g • x)) - (∑ g : G, f (g • y))| ≤
        C * (L * ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖) := by
    calc
      |(∑ g : G, f (g • x)) - (∑ g : G, f (g • y))|
          = |∑ g : G, (f (g • x) - f (g • y))| := by
            rw [← Finset.sum_sub_distrib]
      _ ≤ ∑ g : G, |f (g • x) - f (g • y)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ g : G, L * ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖ := by
        exact Finset.sum_le_sum fun g _ => hterm g
      _ = C * (L * ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖) := by
        dsimp [C]
        rw [Finset.sum_const, Finset.card_univ]
        norm_num
  have hdiv :
      |((∑ g : G, f (g • x)) / C) - ((∑ g : G, f (g • y)) / C)| ≤
        L * ‖(↑x : EuclideanSpace ℝ (Fin D)) - ↑y‖ := by
    rw [← sub_div, abs_div, abs_of_nonneg hCpos.le]
    exact (div_le_iff₀ hCpos).2 (by simpa [mul_comm] using hsum)
  dsimp [C] at hdiv
  exact hdiv

end Rollout_p3260_group_symmetrization_lipschitz

#check_dependency_graph "Rollout_p3260_group_symmetrization_lipschitz.group_symmetrization_lipschitz" against "{\"edges\":[{\"conclusion\":{\"name\":\"hCpos\",\"statement\":\"0 < C\"},\"graphEdgeId\":\"h_001_hcpos\",\"premises\":[],\"rawEdgeId\":\"telescope_14\"},{\"conclusion\":{\"name\":\"hterm\",\"statement\":\"∀ (g : G), |f (g • x) - f (g • y)| ≤ L * ‖↑x - ↑y‖\"},\"graphEdgeId\":\"h_002_hterm\",\"premises\":[{\"name\":\"hact\",\"statement\":\"∀ (g : G) (x y : ↑X), ‖↑(g • x) - ↑(g • y)‖ ≤ ‖↑x - ↑y‖\"},{\"name\":\"hL\",\"statement\":\"0 ≤ L\"},{\"name\":\"hf\",\"statement\":\"∀ (x y : ↑X), |f x - f y| ≤ L * ‖↑x - ↑y‖\"}],\"rawEdgeId\":\"telescope_15\"},{\"conclusion\":{\"name\":\"hsum\",\"statement\":\"|∑ g, f (g • x) - ∑ g, f (g • y)| ≤ C * (L * ‖↑x - ↑y‖)\"},\"graphEdgeId\":\"h_003_hsum\",\"premises\":[{\"name\":\"hterm\",\"statement\":\"∀ (g : G), |f (g • x) - f (g • y)| ≤ L * ‖↑x - ↑y‖\"}],\"rawEdgeId\":\"telescope_16\"},{\"conclusion\":{\"name\":\"hdiv\",\"statement\":\"|(∑ g, f (g • x)) / C - (∑ g, f (g • y)) / C| ≤ L * ‖↑x - ↑y‖\"},\"graphEdgeId\":\"h_004_hdiv\",\"premises\":[{\"name\":\"hCpos\",\"statement\":\"0 < C\"},{\"name\":\"hsum\",\"statement\":\"|∑ g, f (g • x) - ∑ g, f (g • y)| ≤ C * (L * ‖↑x - ↑y‖)\"}],\"rawEdgeId\":\"telescope_17\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"|(∑ g, f (g • x)) / C - (∑ g, f (g • y)) / C| ≤ L * ‖↑x - ↑y‖\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hdiv\",\"statement\":\"|(∑ g, f (g • x)) / C - (∑ g, f (g • y)) / C| ≤ L * ‖↑x - ↑y‖\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p3260_group_symmetrization_lipschitz\",\"reconstructedProofSha256\":\"f5049a81a77e55fb08e36e0e068ba58d49266977f925d0df7cc9e25e4e6c8bb4\",\"selectedEdgeCount\":5,\"theoremName\":\"Rollout_p3260_group_symmetrization_lipschitz.group_symmetrization_lipschitz\",\"topologySha256\":\"98cc2ec8af7eb795746b45890d773629394f9177fe3dbdba47ff1373fbbd3200\"}"
