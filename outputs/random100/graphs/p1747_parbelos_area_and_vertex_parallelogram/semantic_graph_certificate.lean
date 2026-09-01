import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1747_parbelos_area_and_vertex_parallelogram
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 37863b4fd33cabcaee6b1186d21487043328016f8acaea5ea618c19db6ea265c
-- reconstructed_proof_sha256: fb64baee342f6ca6046425f908f95376c7ec5e66a944a656042694d75f63beed
-- selected_edge_count: 1

/- accepted add_to_file helper 1 -/

open MeasureTheory Set

noncomputable def parbelosParallelogramMap (u w : ℝ × ℝ) : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
  (LinearMap.fst ℝ ℝ ℝ).smulRight u + (LinearMap.snd ℝ ℝ ℝ).smulRight w

noncomputable def parbelosParallelogramAffineMap (C u w : ℝ × ℝ) : (ℝ × ℝ) →ᵃ[ℝ] (ℝ × ℝ) :=
  AffineMap.const ℝ (ℝ × ℝ) C + (parbelosParallelogramMap u w).toAffineMap

lemma parbelosParallelogramMap_det (u w : ℝ × ℝ) :
    LinearMap.det (parbelosParallelogramMap u w) = u.1 * w.2 - w.1 * u.2 := by
  rw [← LinearMap.det_toMatrix (Module.Basis.finTwoProd ℝ)]
  rw [Matrix.det_fin_two]
  simp [parbelosParallelogramMap, LinearMap.toMatrix_apply, Module.Basis.finTwoProd_zero,
    Module.Basis.finTwoProd_one]

lemma parbelos_unit_square_hull_eq_Icc :
    convexHull ℝ ({(0 : ℝ × ℝ), (1, 0), (1, 1), (0, 1)} : Set (ℝ × ℝ)) =
      Set.Icc (0, 0) (1, 1) := by
  have hprod :
      ({(0 : ℝ × ℝ), (1, 0), (1, 1), (0, 1)} : Set (ℝ × ℝ)) =
        ({(0 : ℝ), (1 : ℝ)} : Set ℝ) ×ˢ ({(0 : ℝ), (1 : ℝ)} : Set ℝ) := by
    ext p
    constructor
    · intro hp
      rcases hp with rfl | rfl | rfl | rfl <;> simp
    · intro hp
      rcases hp with ⟨hp1, hp2⟩
      simp at hp1 hp2
      rcases hp1 with h1 | h1 <;> rcases hp2 with h2 | h2
      · left; ext <;> simp [h1, h2]
      · right; right; right; ext <;> simp [h1, h2]
      · right; left; ext <;> simp [h1, h2]
      · right; right; left; ext <;> simp [h1, h2]
  rw [hprod, convexHull_prod, convexHull_pair,
    segment_eq_Icc (zero_le_one : (0 : ℝ) ≤ 1), Set.Icc_prod_Icc]

lemma parbelos_volume_unit_square_hull :
    volume (convexHull ℝ ({(0 : ℝ × ℝ), (1, 0), (1, 1), (0, 1)} : Set (ℝ × ℝ))) = 1 := by
  rw [parbelos_unit_square_hull_eq_Icc]
  rw [← Set.Icc_prod_Icc]
  rw [Measure.volume_eq_prod]
  rw [Measure.prod_prod]
  simp [Real.volume_Icc]

lemma parbelosParallelogramAffineMap_image_hull (C u w : ℝ × ℝ) :
    parbelosParallelogramAffineMap C u w ''
      convexHull ℝ ({(0 : ℝ × ℝ), (1, 0), (1, 1), (0, 1)} : Set (ℝ × ℝ)) =
      convexHull ℝ ({C, C + u, C + u + w, C + w} : Set (ℝ × ℝ)) := by
  rw [AffineMap.image_convexHull]
  congr 1
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases hq with rfl | rfl | rfl | rfl <;>
      simp [parbelosParallelogramAffineMap, parbelosParallelogramMap, add_assoc]
  · intro hp
    rcases hp with rfl | rfl | rfl | rfl
    · refine ⟨(0, 0), by simp, ?_⟩
      simp [parbelosParallelogramAffineMap, parbelosParallelogramMap]
    · refine ⟨(1, 0), by simp, ?_⟩
      simp [parbelosParallelogramAffineMap, parbelosParallelogramMap]
    · refine ⟨(1, 1), by simp, ?_⟩
      simp [parbelosParallelogramAffineMap, parbelosParallelogramMap, add_assoc]
    · refine ⟨(0, 1), by simp, ?_⟩
      simp [parbelosParallelogramAffineMap, parbelosParallelogramMap]

lemma parbelos_volume_hull_parallelogram (C u w : ℝ × ℝ) :
    volume (convexHull ℝ ({C, C + u, C + u + w, C + w} : Set (ℝ × ℝ))) =
      ENNReal.ofReal |u.1 * w.2 - w.1 * u.2| := by
  let Q : Set (ℝ × ℝ) :=
    convexHull ℝ ({(0 : ℝ × ℝ), (1, 0), (1, 1), (0, 1)} : Set (ℝ × ℝ))
  let A : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) := parbelosParallelogramMap u w
  have hset : convexHull ℝ ({C, C + u, C + u + w, C + w} : Set (ℝ × ℝ)) =
      (AffineMap.const ℝ (ℝ × ℝ) C + A.toAffineMap) '' Q := by
    symm
    exact parbelosParallelogramAffineMap_image_hull C u w
  rw [hset]
  have hcomp :
      (AffineMap.const ℝ (ℝ × ℝ) C + A.toAffineMap) '' Q =
        (fun p => C + p) '' (A '' Q) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨A q, ⟨q, hq, rfl⟩, by rfl⟩
    · rintro ⟨q, ⟨r, hr, rfl⟩, rfl⟩
      exact ⟨r, hr, by rfl⟩
  rw [hcomp]
  have htrans : volume ((fun p : ℝ × ℝ => C + p) '' (A '' Q)) = volume (A '' Q) := by
    have h := measure_preimage_add (μ := volume) C ((fun p : ℝ × ℝ => C + p) '' (A '' Q))
    have hpre : (fun p : ℝ × ℝ => C + p) ⁻¹'
        ((fun p : ℝ × ℝ => C + p) '' (A '' Q)) = A '' Q := by
      exact Set.preimage_image_eq _ (add_right_injective C)
    rw [hpre] at h
    exact h.symm
  rw [htrans]
  rw [Measure.addHaar_image_linearMap]
  have hA : LinearMap.det A = u.1 * w.2 - w.1 * u.2 := by
    exact parbelosParallelogramMap_det u w
  have hQ : volume Q = 1 := by
    exact parbelos_volume_unit_square_hull
  rw [hA, hQ]
  simp

lemma parbelos_volume_between_Icc
    {l u : ℝ} (hlu : l ≤ u) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x ∈ Set.Icc l u, f x ≤ g x) :
    volume {p : ℝ × ℝ | l ≤ p.1 ∧ p.1 ≤ u ∧ f p.1 ≤ p.2 ∧ p.2 ≤ g p.1} =
      ENNReal.ofReal (∫ x in l..u, g x - f x) := by
  let S : Set (ℝ × ℝ) := {p | l ≤ p.1 ∧ p.1 ≤ u ∧ f p.1 ≤ p.2 ∧ p.2 ≤ g p.1}
  have hS : MeasurableSet S := by
    dsimp [S]
    measurability
  change volume S = ENNReal.ofReal (∫ x in l..u, g x - f x)
  rw [Measure.volume_eq_prod]
  rw [Measure.prod_apply hS]
  have hsec : ∀ x : ℝ,
      volume (Prod.mk x ⁻¹' S) =
        (Set.Icc l u).indicator (fun x => ENNReal.ofReal (g x - f x)) x := by
    intro x
    by_cases hx : x ∈ Set.Icc l u
    · have hpre : Prod.mk x ⁻¹' S = Set.Icc (f x) (g x) := by
        ext y
        constructor
        · intro hy
          exact hy.2.2
        · intro hy
          exact ⟨hx.1, hx.2, hy⟩
      rw [hpre, Set.indicator_of_mem hx, Real.volume_Icc]
    · have hpre : Prod.mk x ⁻¹' S = (∅ : Set ℝ) := by
        ext y
        constructor
        · intro hy
          exact (hx ⟨hy.1, hy.2.1⟩).elim
        · intro hy
          cases hy
      rw [hpre, Set.indicator_of_notMem hx]
      simp
  rw [lintegral_congr hsec]
  rw [lintegral_indicator measurableSet_Icc]
  have hfi : Integrable (fun x => g x - f x) (volume.restrict (Set.Icc l u)) := by
    exact (hg.sub hf).integrableOn_Icc
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc l u)] fun x => g x - f x := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact sub_nonneg.mpr (hfg x hx)
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfi hnn]
  congr 1
  have hintegral :
      (∫ x, g x - f x ∂(volume.restrict (Set.Icc l u))) =
        ∫ x in l..u, g x - f x := by
    calc
      (∫ x, g x - f x ∂(volume.restrict (Set.Icc l u))) =
          ∫ x in Set.Icc l u, g x - f x := by rfl
      _ = ∫ x in Set.Ioc l u, g x - f x := by
        exact integral_Icc_eq_integral_Ioc' (μ := volume) (by simp)
      _ = ∫ x in l..u, g x - f x := by
        exact (intervalIntegral.integral_of_le hlu).symm
  exact hintegral

/- accepted add_to_file helper 2 -/
lemma parbelos_region_volume_explicit
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b < 2 * a) :
    volume {p : ℝ × ℝ |
      (0 ≤ p.1 ∧ p.1 ≤ 2 * b ∧
        b / 2 - (p.1 - b) ^ 2 / (2 * b) ≤ p.2 ∧
        p.2 ≤ a - (p.1 - 2 * a) ^ 2 / (4 * a)) ∨
      (2 * b ≤ p.1 ∧ p.1 ≤ 4 * a ∧
        (2 * a - b) / 2 - (p.1 - (2 * a + b)) ^ 2 / (2 * (2 * a - b)) ≤ p.2 ∧
        p.2 ≤ a - (p.1 - 2 * a) ^ 2 / (4 * a))} =
      ENNReal.ofReal (4 * b * (2 * a - b) / 3) := by
  let U : ℝ → ℝ := fun x => a - (x - 2 * a) ^ 2 / (4 * a)
  let L : ℝ → ℝ := fun x => b / 2 - (x - b) ^ 2 / (2 * b)
  let R : ℝ → ℝ := fun x =>
    (2 * a - b) / 2 - (x - (2 * a + b)) ^ 2 / (2 * (2 * a - b))
  let P₁ : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ 2 * b ∧ L p.1 ≤ p.2 ∧ p.2 ≤ U p.1}
  let P₂ : Set (ℝ × ℝ) :=
    {p | 2 * b ≤ p.1 ∧ p.1 ≤ 4 * a ∧ R p.1 ≤ p.2 ∧ p.2 ≤ U p.1}
  set c : ℝ := 2 * a - b
  have hcpos : 0 < c := by
    dsimp [c]
    exact sub_pos.mpr hba
  have hc : c ≠ 0 := ne_of_gt hcpos
  have hcdef : c = 2 * a - b := rfl
  have hUcont : Continuous U := by
    dsimp [U]
    continuity
  have hLcont : Continuous L := by
    dsimp [L]
    continuity
  have hRcont : Continuous R := by
    dsimp [R]
    continuity
  have hUL : ∀ x : ℝ, U x - L x = (c / (4 * a * b)) * x ^ 2 := by
    intro x
    dsimp [U, L]
    field_simp [ha.ne', hb.ne']
    rw [hcdef]
    ring
  have hUR : ∀ x : ℝ, U x - R x = (b / (4 * a * c)) * (4 * a - x) ^ 2 := by
    intro x
    dsimp [U, R]
    rw [← hcdef]
    field_simp [ha.ne', hc]
    rw [hcdef]
    ring
  have hUL_nonneg : ∀ x : ℝ, 0 ≤ U x - L x := by
    intro x
    rw [hUL x]
    positivity
  have hUR_nonneg : ∀ x : ℝ, 0 ≤ U x - R x := by
    intro x
    rw [hUR x]
    positivity
  have hI₁ : ∫ x in (0 : ℝ)..(2 * b), U x - L x = 2 * b ^ 2 * c / (3 * a) := by
    calc
      ∫ x in (0 : ℝ)..(2 * b), U x - L x
          = ∫ x in (0 : ℝ)..(2 * b), (c / (4 * a * b)) * x ^ 2 := by
            apply intervalIntegral.integral_congr
            intro x hx
            exact hUL x
      _ = 2 * b ^ 2 * c / (3 * a) := by
            rw [intervalIntegral.integral_const_mul, integral_pow]
            field_simp [ha.ne', hb.ne']
            ring
  have hI₂ : ∫ x in (2 * b)..(4 * a), U x - R x = 2 * b * c ^ 2 / (3 * a) := by
    calc
      ∫ x in (2 * b)..(4 * a), U x - R x
          = ∫ x in (2 * b)..(4 * a), (b / (4 * a * c)) * (4 * a - x) ^ 2 := by
            apply intervalIntegral.integral_congr
            intro x hx
            exact hUR x
      _ = ∫ x in (0 : ℝ)..(4 * a - 2 * b), (b / (4 * a * c)) * x ^ 2 := by
            have hsub :=
              intervalIntegral.integral_comp_sub_left
                (a := 2 * b) (b := 4 * a)
                (f := fun x : ℝ => (b / (4 * a * c)) * x ^ 2) (d := 4 * a)
            convert hsub using 2 <;> ring
      _ = 2 * b * c ^ 2 / (3 * a) := by
            rw [intervalIntegral.integral_const_mul, integral_pow]
            field_simp [ha.ne', hc]
            rw [hcdef]
            ring
  have hP₁vol : volume P₁ = ENNReal.ofReal (∫ x in (0 : ℝ)..(2 * b), U x - L x) := by
    apply parbelos_volume_between_Icc
    · positivity
    · exact hLcont
    · exact hUcont
    · intro x hx
      exact sub_nonneg.mp (hUL_nonneg x)
  have hP₂vol : volume P₂ = ENNReal.ofReal (∫ x in (2 * b)..(4 * a), U x - R x) := by
    apply parbelos_volume_between_Icc
    · nlinarith
    · exact hRcont
    · exact hUcont
    · intro x hx
      exact sub_nonneg.mp (hUR_nonneg x)
  have hP₂meas : MeasurableSet P₂ := by
    dsimp [P₂, U, R]
    measurability
  have hline : volume ({p : ℝ × ℝ | p.1 = 2 * b}) = 0 := by
    have hset : ({p : ℝ × ℝ | p.1 = 2 * b}) = ({2 * b} : Set ℝ) ×ˢ Set.univ := by
      ext p
      simp
    rw [hset, Measure.volume_eq_prod, Measure.prod_prod]
    simp
  have hinter : volume (P₁ ∩ P₂) = 0 := by
    apply measure_mono_null _ hline
    intro p hp
    exact le_antisymm hp.1.2.1 hp.2.1
  have hPunion : volume (P₁ ∪ P₂) = volume P₁ + volume P₂ := by
    have h := measure_union_add_inter (μ := volume) P₁ hP₂meas
    rw [hinter, add_zero] at h
    exact h
  change volume (P₁ ∪ P₂) = ENNReal.ofReal (4 * b * (2 * a - b) / 3)
  rw [hPunion, hP₁vol, hP₂vol, hI₁, hI₂]
  have hI₁_nonneg : 0 ≤ 2 * b ^ 2 * c / (3 * a) := by positivity
  have hI₂_nonneg : 0 ≤ 2 * b * c ^ 2 / (3 * a) := by positivity
  rw [← ENNReal.ofReal_add hI₁_nonneg hI₂_nonneg]
  congr 1
  rw [hcdef]
  field_simp [ha.ne']
  ring

/- verified submission -/
theorem parbelos_area_and_vertex_parallelogram
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hba : b < 2 * a) :
    let C₁ : ℝ × ℝ := (0, 0)
    let C₂ : ℝ × ℝ := (2 * b, 0)
    let C₃ : ℝ × ℝ := (4 * a, 0)
    let U : ℝ → ℝ := fun x => a - (x - 2 * a) ^ 2 / (4 * a)
    let L : ℝ → ℝ := fun x => b / 2 - (x - b) ^ 2 / (2 * b)
    let R : ℝ → ℝ := fun x => (2 * a - b) / 2 - (x - (2 * a + b)) ^ 2 / (2 * (2 * a - b))
    let P : Set (ℝ × ℝ) := {p | (0 ≤ p.1 ∧ p.1 ≤ 2 * b ∧ L p.1 ≤ p.2 ∧ p.2 ≤ U p.1) ∨
      (2 * b ≤ p.1 ∧ p.1 ≤ 4 * a ∧ R p.1 ≤ p.2 ∧ p.2 ≤ U p.1)}
    let V₁ : ℝ × ℝ := (b, b / 2)
    let V₂ : ℝ × ℝ := (2 * a, a)
    let V₃ : ℝ × ℝ := (2 * a + b, a - b / 2)
    (V₁ - C₂ = V₂ - V₃ ∧ V₂ - V₁ = V₃ - C₂) ∧
      MeasureTheory.volume P = (4 / 3 : ENNReal) * MeasureTheory.volume (convexHull ℝ ({C₂, V₁, V₂, V₃} : Set (ℝ × ℝ))) := by
  dsimp
  constructor
  · constructor
    · ext <;> ring
    · ext <;> ring
  · rw [parbelos_region_volume_explicit a b ha hb hba]
    let C : ℝ × ℝ := (2 * b, 0)
    let u : ℝ × ℝ := (2 * a + b, a - b / 2) - (2 * b, 0)
    let w : ℝ × ℝ := (b, b / 2) - (2 * b, 0)
    have hpoints :
        ({(2 * b, 0), (b, b / 2), (2 * a, a), (2 * a + b, a - b / 2)} : Set (ℝ × ℝ)) =
          ({C, C + u, C + u + w, C + w} : Set (ℝ × ℝ)) := by
      ext p
      simp [C, u, w]
      constructor
      · intro hp
        rcases hp with rfl | rfl | rfl | rfl
        · left; rfl
        · right; right; right; ext <;> ring
        · right; right; left; ext <;> ring
        · right; left; ext <;> ring
      · intro hp
        rcases hp with rfl | rfl | rfl | rfl
        · left; rfl
        · right; right; right; ext <;> ring
        · right; right; left; ext <;> ring
        · right; left; ext <;> ring
    rw [hpoints, parbelos_volume_hull_parallelogram C u w]
    have hc : 0 ≤ b * (2 * a - b) := by
      have hcpos : 0 ≤ 2 * a - b := le_of_lt (sub_pos.mpr hba)
      exact mul_nonneg (le_of_lt hb) hcpos
    have hdet : u.1 * w.2 - w.1 * u.2 = b * (2 * a - b) := by
      dsimp [u, w]
      ring
    rw [hdet, abs_of_nonneg hc]
    have h43 : (4 / 3 : ENNReal) = ENNReal.ofReal ((4 / 3 : ℝ)) := by
      rw [ENNReal.ofReal_div_of_pos (show (0 : ℝ) < 3 by norm_num)]
      norm_num
    rw [h43, (ENNReal.ofReal_mul (show (0 : ℝ) ≤ (4 / 3) by norm_num)).symm]
    congr 1
    ring


#check_dependency_graph "parbelos_area_and_vertex_parallelogram" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let C₁ := (0, 0); let C₂ := (2 * b, 0); let C₃ := (4 * a, 0); let U := fun x => a - (x - 2 * a) ^ 2 / (4 * a); let L := fun x => b / 2 - (x - b) ^ 2 / (2 * b); let R := fun x => (2 * a - b) / 2 - (x - (2 * a + b)) ^ 2 / (2 * (2 * a - b)); let P := {p | 0 ≤ p.1 ∧ p.1 ≤ 2 * b ∧ L p.1 ≤ p.2 ∧ p.2 ≤ U p.1 ∨ 2 * b ≤ p.1 ∧ p.1 ≤ 4 * a ∧ R p.1 ≤ p.2 ∧ p.2 ≤ U p.1}; let V₁ := (b, b / 2); let V₂ := (2 * a, a); let V₃ := (2 * a + b, a - b / 2); (V₁ - C₂ = V₂ - V₃ ∧ V₂ - V₁ = V₃ - C₂) ∧ MeasureTheory.volume P = 4 / 3 * MeasureTheory.volume ((convexHull ℝ) {C₂, V₁, V₂, V₃})\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"ha\",\"statement\":\"0 < a\"},{\"name\":\"hb\",\"statement\":\"0 < b\"},{\"name\":\"hba\",\"statement\":\"b < 2 * a\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1747_parbelos_area_and_vertex_parallelogram\",\"reconstructedProofSha256\":\"fb64baee342f6ca6046425f908f95376c7ec5e66a944a656042694d75f63beed\",\"selectedEdgeCount\":1,\"theoremName\":\"parbelos_area_and_vertex_parallelogram\",\"topologySha256\":\"37863b4fd33cabcaee6b1186d21487043328016f8acaea5ea618c19db6ea265c\"}"
