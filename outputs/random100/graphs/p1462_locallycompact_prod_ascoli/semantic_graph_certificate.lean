import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1462_locallycompact_prod_ascoli
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 2ae746cbc6be46666faafa2b65013d41608ef6d88274e4b722e55de0f80ebd1f
-- reconstructed_proof_sha256: 222fec63c4a43f24385f508de85fa4cc7571db5e728cc922a31fc7e30836e17c
-- selected_edge_count: 2

/- accepted add_to_file helper 1 -/

open Set

lemma continuous_sectionMap_real
    (Z X : Type*) [TopologicalSpace Z] [LocallyCompactSpace Z] [TopologicalSpace X] :
    Continuous
      (fun p : C(Z × X, ℝ) × Z =>
        (⟨fun x => p.1 (p.2, x),
          p.1.continuous.comp (Continuous.prodMk_right p.2)⟩ : C(X, ℝ))) := by
  rw [ContinuousMap.continuous_compactOpen]
  intro C hC U hU
  rw [isOpen_iff_forall_mem_open]
  rintro ⟨f, z⟩ hf
  have hn : IsOpen (f ⁻¹' U) := hU.preimage f.continuous
  have hprod : ({z} : Set Z) ×ˢ C ⊆ f ⁻¹' U := by
    rintro ⟨z', x⟩ ⟨hz', hx⟩
    simp at hz'
    subst z'
    exact hf hx
  obtain ⟨V, W, hV, hW, hzV, hCW, hVW⟩ :=
    generalized_tube_lemma (isCompact_singleton (x := z)) hC hn hprod
  obtain ⟨L, hL, hzL, hLV⟩ := exists_compact_subset hV (hzV rfl)
  refine ⟨{g : C(Z × X, ℝ) | Set.MapsTo g (L ×ˢ C) U} ×ˢ interior L, ?_,
    (ContinuousMap.isOpen_setOf_mapsTo (hL.prod hC) hU).prod isOpen_interior,
    ⟨?_, hzL⟩⟩
  · rintro ⟨g, z'⟩ ⟨hg, hz'⟩
    intro x hx
    exact hg ⟨interior_subset hz', hx⟩
  · rintro ⟨z', x⟩ ⟨hz', hx⟩
    exact hVW ⟨hLV hz', hCW hx⟩

/- verified submission -/
theorem locallyCompact_prod_ascoli
    (Z X : Type*) [TopologicalSpace Z] [T35Space Z] [LocallyCompactSpace Z]
    [TopologicalSpace X] [T35Space X]
    (hX : ∀ K : Set C(X, ℝ), IsCompact K →
      Continuous (fun p : K × X => (p.1 : C(X, ℝ)) p.2)) :
    ∀ K : Set C(Z × X, ℝ), IsCompact K →
      Continuous (fun p : K × (Z × X) => (p.1 : C(Z × X, ℝ)) p.2) := by
  intro K hK
  let Φ : C(Z × X, ℝ) × Z → C(X, ℝ) := fun p =>
    ⟨fun x => p.1 (p.2, x),
      p.1.continuous.comp (Continuous.prodMk_right p.2)⟩
  have hΦ : Continuous Φ := continuous_sectionMap_real Z X
  rw [continuous_iff_continuousAt]
  rintro ⟨f, ⟨z, x⟩⟩
  obtain ⟨L, hL, hzL, -⟩ := exists_compact_subset isOpen_univ (Set.mem_univ z)
  let A : Set C(X, ℝ) := Φ '' (K ×ˢ L)
  have hA : IsCompact A := (hK.prod hL).image hΦ
  have hEv : Continuous (fun p : A × X => (p.1 : C(X, ℝ)) p.2) := hX A hA
  let S : Set (K × (Z × X)) := (fun p => p.2.1) ⁻¹' interior L
  have hS : IsOpen S := isOpen_interior.preimage (continuous_fst.comp continuous_snd)
  have hval : Continuous (Subtype.val : S → K × (Z × X)) := continuous_subtype_val
  have hCproj : Continuous (fun s : S => ((s.1.1 : K) : C(Z × X, ℝ))) := by
    exact continuous_subtype_val.comp (continuous_fst.comp hval)
  have hZproj : Continuous (fun s : S => s.1.2.1) := by
    exact continuous_fst.comp (continuous_snd.comp hval)
  have hXproj : Continuous (fun s : S => s.1.2.2) := by
    exact continuous_snd.comp (continuous_snd.comp hval)
  have hsec : Continuous (fun s : S => Φ (((s.1.1 : K) : C(Z × X, ℝ)), s.1.2.1)) :=
    hΦ.comp (hCproj.prodMk hZproj)
  have hmem : ∀ s : S, Φ (((s.1.1 : K) : C(Z × X, ℝ)), s.1.2.1) ∈ A := by
    intro s
    refine Set.mem_image_of_mem Φ ?_
    exact ⟨s.1.1.property, interior_subset s.2⟩
  have hsecA : Continuous
      (fun s : S => (⟨Φ (((s.1.1 : K) : C(Z × X, ℝ)), s.1.2.1), hmem s⟩ : A)) :=
    hsec.codRestrict hmem
  have hpair : Continuous
      (fun s : S =>
        ((⟨Φ (((s.1.1 : K) : C(Z × X, ℝ)), s.1.2.1), hmem s⟩ : A), s.1.2.2)) :=
    hsecA.prodMk hXproj
  have hloc : Continuous
      (fun s : S => ((⟨Φ (((s.1.1 : K) : C(Z × X, ℝ)), s.1.2.1), hmem s⟩ : A) : C(X, ℝ)) s.1.2.2) :=
    hEv.comp hpair
  have hloc' : Continuous
      ((fun p : K × (Z × X) => (p.1 : C(Z × X, ℝ)) p.2) ∘ (Subtype.val : S → K × (Z × X))) := by
    convert hloc using 1
  let ps : S := ⟨⟨f, ⟨z, x⟩⟩, hzL⟩
  exact (hS.isOpenEmbedding_subtypeVal.continuousAt_iff (x := ps)).mp
    (hloc'.continuousAt (x := ps))


#check_dependency_graph "locallyCompact_prod_ascoli" against "{\"edges\":[{\"conclusion\":{\"name\":\"hΦ\",\"statement\":\"Continuous Φ\"},\"graphEdgeId\":\"h_001_h\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"LocallyCompactSpace Z\"}],\"rawEdgeId\":\"telescope_11\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"Continuous fun p => ↑p.1 p.2\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"LocallyCompactSpace Z\"},{\"name\":\"hX\",\"statement\":\"∀ (K : Set C(X, ℝ)), IsCompact K → Continuous fun p => ↑p.1 p.2\"},{\"name\":\"hK\",\"statement\":\"IsCompact K\"},{\"name\":\"hΦ\",\"statement\":\"Continuous Φ\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1462_locallycompact_prod_ascoli\",\"reconstructedProofSha256\":\"222fec63c4a43f24385f508de85fa4cc7571db5e728cc922a31fc7e30836e17c\",\"selectedEdgeCount\":2,\"theoremName\":\"locallyCompact_prod_ascoli\",\"topologySha256\":\"2ae746cbc6be46666faafa2b65013d41608ef6d88274e4b722e55de0f80ebd1f\"}"
