import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1499_countablytight_iff_prod_firstcountable
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 6d791668e76419bbfe9379e31a02f72cf68e3d1b1e9e38d859c818bd9a9bb10a
-- reconstructed_proof_sha256: 9758ee59b088a34d5fae47675ab257a7179614cc5e931f5eda41c99d0c62f89d
-- selected_edge_count: 1

/- accepted add_to_file helper 1 -/
lemma countablyTight_prod_firstCountable
    {X : Type u} [TopologicalSpace X]
    (hX : ∀ (A : Set X) (x : X), x ∈ closure A →
      ∃ B : Set X, B ⊆ A ∧ B.Countable ∧ x ∈ closure B)
    {Y : Type v} [TopologicalSpace Y] [FirstCountableTopology Y] :
    ∀ (A : Set (X × Y)) (p : X × Y), p ∈ closure A →
      ∃ B : Set (X × Y), B ⊆ A ∧ B.Countable ∧ p ∈ closure B := by
  intro A p hp
  obtain ⟨V, hV⟩ := (Filter.isCountablyGenerated_iff_exists_antitone_basis.mp
    (FirstCountableTopology.nhds_generated_countable p.2))
  let C : ℕ → Set X := fun n => Prod.fst '' (A ∩ (Set.univ ×ˢ V n))
  have hVn : ∀ n, V n ∈ nhds p.2 := by
    intro n
    exact hV.mem_iff.mpr ⟨n, subset_rfl⟩
  have hpC : ∀ n, p.1 ∈ closure (C n) := by
    intro n
    rw [mem_closure_iff_nhds]
    intro U hU
    have hprod : U ×ˢ V n ∈ nhds p := by
      rw [mem_nhds_prod_iff]
      exact ⟨U, hU, V n, hVn n, subset_rfl⟩
    obtain ⟨q, hqprod, hqA⟩ := (mem_closure_iff_nhds.mp hp) (U ×ˢ V n) hprod
    rcases hqprod with ⟨hqU, hqV⟩
    refine ⟨q.1, hqU, ?_⟩
    exact ⟨q, ⟨hqA, ⟨trivial, hqV⟩⟩, rfl⟩
  choose BX hBXsub hBXcount hpBX using fun n => hX (C n) p.1 (hpC n)
  have hchoose : ∀ n, ∀ x : BX n, ∃ q : X × Y, q ∈ A ∧ q.2 ∈ V n ∧ q.1 = x.1 := by
    intro n x
    have hxC : (x : X) ∈ C n := hBXsub n x.2
    rcases hxC with ⟨q, hq, hq1⟩
    rcases hq with ⟨hqA, hqprod⟩
    rcases hqprod with ⟨-, hqV⟩
    exact ⟨q, hqA, hqV, hq1⟩
  choose f hfA hfV hf1 using hchoose
  let D : ℕ → Set (X × Y) := fun n => Set.range (f n)
  let Bset : Set (X × Y) := ⋃ n, D n
  refine ⟨Bset, ?_, ?_, ?_⟩
  · intro q hq
    rw [Set.mem_iUnion] at hq
    rcases hq with ⟨n, hn⟩
    rcases hn with ⟨x, rfl⟩
    exact hfA n x
  · have hDcount : ∀ n, (D n).Countable := by
      intro n
      haveI : Countable (BX n) := (hBXcount n).to_subtype
      exact Set.countable_range (f n)
    exact Set.countable_iUnion hDcount
  · rw [mem_closure_iff_nhds]
    intro W hW
    obtain ⟨U, hU, T, hT, hUT⟩ := mem_nhds_prod_iff.mp hW
    obtain ⟨n, hnVT⟩ := hV.mem_iff.mp hT
    obtain ⟨z, hzU, hzB⟩ := (mem_closure_iff_nhds.mp (hpBX n)) U hU
    refine ⟨f n ⟨z, hzB⟩, hUT ?_, ?_⟩
    · constructor
      · rw [hf1 n ⟨z, hzB⟩]
        exact hzU
      · exact hnVT (hfV n ⟨z, hzB⟩)
    · rw [Set.mem_iUnion]
      exact ⟨n, ⟨⟨z, hzB⟩, rfl⟩⟩

/- verified submission -/
theorem countablyTight_iff_prod_firstCountable {X : Type u} [TopologicalSpace X] :
    (∀ (A : Set X) (x : X), x ∈ closure A →
      ∃ B : Set X, B ⊆ A ∧ B.Countable ∧ x ∈ closure B) ↔
      ∀ (Y : Type v) [TopologicalSpace Y] [FirstCountableTopology Y],
        ∀ (A : Set (X × Y)) (p : X × Y), p ∈ closure A →
          ∃ B : Set (X × Y), B ⊆ A ∧ B.Countable ∧ p ∈ closure B := by
  constructor
  · intro hX Y _ _
    exact countablyTight_prod_firstCountable hX
  · intro hprod A x hx
    let Z : Type v := ULift.{v} PUnit
    let h : X × Z ≃ₜ X := Homeomorph.prodUnique X Z
    have hp : h.symm x ∈ closure (⇑h ⁻¹' A) := by
      have hmem : h.symm x ∈ ⇑h ⁻¹' closure A := by
        simpa using hx
      rwa [h.preimage_closure A] at hmem
    obtain ⟨B0, hB0A, hB0count, hB0cl⟩ := hprod Z (⇑h ⁻¹' A) (h.symm x) hp
    refine ⟨⇑h '' B0, ?_, hB0count.image ⇑h, ?_⟩
    · intro z hz
      rcases hz with ⟨q, hqB0, rfl⟩
      exact hB0A hqB0
    · have hxcl : h (h.symm x) ∈ closure (⇑h '' B0) := by
        rw [← h.image_closure B0]
        exact ⟨h.symm x, hB0cl, rfl⟩
      simpa using hxcl


#check_dependency_graph "countablyTight_iff_prod_firstCountable" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(∀ (A : Set X), ∀ x ∈ closure A, ∃ B ⊆ A, B.Countable ∧ x ∈ closure B) ↔ ∀ (Y : Type v) [inst : TopologicalSpace Y] [FirstCountableTopology Y] (A : Set (X × Y)), ∀ p ∈ closure A, ∃ B ⊆ A, B.Countable ∧ p ∈ closure B\"},\"graphEdgeId\":\"h_goal\",\"premises\":[],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1499_countablytight_iff_prod_firstcountable\",\"reconstructedProofSha256\":\"9758ee59b088a34d5fae47675ab257a7179614cc5e931f5eda41c99d0c62f89d\",\"selectedEdgeCount\":1,\"theoremName\":\"countablyTight_iff_prod_firstCountable\",\"topologySha256\":\"6d791668e76419bbfe9379e31a02f72cf68e3d1b1e9e38d859c818bd9a9bb10a\"}"
