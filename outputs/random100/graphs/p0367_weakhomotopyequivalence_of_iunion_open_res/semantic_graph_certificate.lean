import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p0367_weakhomotopyequivalence_of_iunion_open_res
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: d8054a5027501cba618538efb0a26a4cda17a805880f39cd49477c4e14fe5b91
-- reconstructed_proof_sha256: 021b5d859c09bf217def9d432e626804cba028c718e90a5d7d260509c806db5b
-- selected_edge_count: 1

/- accepted add_to_file helper 1 -/
lemma exists_cover_stage_of_isCompact
    {X : Type*} [TopologicalSpace X] {ι : Type*} [Nonempty ι]
    [Preorder ι] [IsDirectedOrder ι]
    {K : Set X} (hK : IsCompact K)
    (U : ι → Set X)
    (hU_open : ∀ n, IsOpen (U n))
    (hU_mono : Monotone U)
    (hU_cover : ⋃ n, U n = Set.univ) :
    ∃ n, K ⊆ U n := by
  refine hK.elim_directed_cover U hU_open ?_ hU_mono.directed_le
  rw [hU_cover]
  exact Set.subset_univ K

/-- Restrict a generalized loop to a subset containing its range. -/
def genLoopRestrict
    {N X : Type*} [TopologicalSpace N] [TopologicalSpace X]
    (s : Set X) {x : X} (hx : x ∈ s)
    (p : GenLoop N X x) (hp : Set.range p.1 ⊆ s) :
    GenLoop N s ⟨x, hx⟩ := by
  refine ⟨⟨fun y => ⟨p.1 y, hp ⟨y, rfl⟩⟩, ?_⟩, ?_⟩
  · exact p.1.continuous.subtype_mk (fun y => hp ⟨y, rfl⟩)
  · intro y hy
    apply Subtype.ext
    exact p.2 y hy

/-- Extend a generalized loop from a subset to the ambient space. -/
def genLoopExtend
    {N X : Type*} [TopologicalSpace N] [TopologicalSpace X]
    (s : Set X) {x : X} (hx : x ∈ s)
    (p : GenLoop N s ⟨x, hx⟩) :
    GenLoop N X x := by
  refine ⟨⟨fun y => p.1 y, continuous_subtype_val.comp p.1.continuous⟩, ?_⟩
  intro y hy
  exact congrArg Subtype.val (p.2 y hy)

/- verified submission -/
theorem weakHomotopyEquivalence_of_iUnion_open_restrictions
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y))
    (U : {n : ℕ // 1 ≤ n} → Set X)
    (hU_open : ∀ n, IsOpen (U n))
    (hU_mono : Monotone U)
    (hU_cover : ⋃ n, U n = Set.univ)
    (hf : ∀ n,
      let g : C(U n, Y) :=
        ⟨fun x => f x.1, f.continuous.comp continuous_subtype_val⟩
      Function.Bijective
          (Quotient.map g (by
            intro a b h
            exact h.map (fun p => p.map g.continuous)) :
            ZerothHomotopy (U n) → ZerothHomotopy Y) ∧
        ∀ (k : ℕ) (x : U n), Function.Bijective
          (Quotient.map
            (fun p : GenLoop (Fin (k + 1)) (U n) x =>
              (⟨g.comp p.1, by
                intro y hy
                rw [ContinuousMap.comp_apply, p.2 y hy]⟩ :
                GenLoop (Fin (k + 1)) Y (g x)))
            (by
              intro p q h
              exact h.map (fun H => H.compContinuousMap g)) :
            HomotopyGroup.Pi (k + 1) (U n) x →
              HomotopyGroup.Pi (k + 1) Y (g x))) :
    Function.Bijective
        (Quotient.map f (by
          intro a b h
          exact h.map (fun p => p.map f.continuous)) :
          ZerothHomotopy X → ZerothHomotopy Y) ∧
      ∀ (k : ℕ) (x : X), Function.Bijective
        (Quotient.map
          (fun p : GenLoop (Fin (k + 1)) X x =>
            (⟨f.comp p.1, by
              intro y hy
              rw [ContinuousMap.comp_apply, p.2 y hy]⟩ :
              GenLoop (Fin (k + 1)) Y (f x)))
          (by
            intro p q h
            exact h.map (fun H => H.compContinuousMap f)) :
          HomotopyGroup.Pi (k + 1) X x → HomotopyGroup.Pi (k + 1) Y (f x)) := by
  constructor
  · constructor
    · intro a b hab
      obtain ⟨x, rfl⟩ := Quotient.exists_rep a
      obtain ⟨y, rfl⟩ := Quotient.exists_rep b
      let K : Set X := {x, y}
      have hK : IsCompact K := by
        simp [K]
      obtain ⟨n, hnK⟩ :=
        exists_cover_stage_of_isCompact hK U hU_open hU_mono hU_cover
      have hx : x ∈ U n := hnK (by simp [K])
      have hy : y ∈ U n := hnK (by simp [K])
      let x' : U n := ⟨x, hx⟩
      let y' : U n := ⟨y, hy⟩
      let g : C(U n, Y) :=
        ⟨fun z => f z.1, f.continuous.comp continuous_subtype_val⟩
      have hlocal :
          (Quotient.map g (by
            intro a b h
            exact h.map (fun p => p.map g.continuous)) :
            ZerothHomotopy (U n) → ZerothHomotopy Y) ⟦x'⟧ =
          (Quotient.map g (by
            intro a b h
            exact h.map (fun p => p.map g.continuous)) :
            ZerothHomotopy (U n) → ZerothHomotopy Y) ⟦y'⟧ := by
        exact hab
      have hxy_local := (hf n).1.1 hlocal
      have hxy : Joined x y := by
        exact (Quotient.eq.mp hxy_local).map
          (fun p => p.map continuous_subtype_val)
      exact Quotient.eq.mpr hxy
    · intro b
      obtain ⟨y, rfl⟩ := Quotient.exists_rep b
      let n : {n : ℕ // 1 ≤ n} := ⟨1, le_rfl⟩
      obtain ⟨a, ha⟩ := (hf n).1.2 (⟦y⟧ : ZerothHomotopy Y)
      obtain ⟨x, rfl⟩ := Quotient.exists_rep a
      use (⟦x.1⟧ : ZerothHomotopy X)
      exact ha
  · intro k x
    constructor
    · intro a b hab
      obtain ⟨p, rfl⟩ := Quotient.exists_rep a
      obtain ⟨q, rfl⟩ := Quotient.exists_rep b
      let K : Set X := Set.range p.1 ∪ Set.range q.1 ∪ {x}
      have hpK : IsCompact (Set.range p.1) := isCompact_range p.1.continuous
      have hqK : IsCompact (Set.range q.1) := isCompact_range q.1.continuous
      have hK : IsCompact K := by
        unfold K
        exact (hpK.union hqK).union isCompact_singleton
      obtain ⟨n, hnK⟩ :=
        exists_cover_stage_of_isCompact hK U hU_open hU_mono hU_cover
      have hx : x ∈ U n := hnK (by simp [K])
      have hp : Set.range p.1 ⊆ U n := by
        intro z hz
        exact hnK (Set.mem_union_left {x}
          (Set.mem_union_left (Set.range q.1) hz))
      have hq : Set.range q.1 ⊆ U n := by
        intro z hz
        exact hnK (Set.mem_union_left {x}
          (Set.mem_union_right (Set.range p.1) hz))
      let x' : U n := ⟨x, hx⟩
      let pU := genLoopRestrict (U n) hx p hp
      let qU := genLoopRestrict (U n) hx q hq
      let g : C(U n, Y) :=
        ⟨fun z => f z.1, f.continuous.comp continuous_subtype_val⟩
      have hlocal :
          (Quotient.map
            (fun r : GenLoop (Fin (k + 1)) (U n) x' =>
              (⟨g.comp r.1, by
                intro y hy
                rw [ContinuousMap.comp_apply, r.2 y hy]⟩ :
                GenLoop (Fin (k + 1)) Y (g x')))
            (by
              intro r s h
              exact h.map (fun H => H.compContinuousMap g)) :
            HomotopyGroup.Pi (k + 1) (U n) x' →
              HomotopyGroup.Pi (k + 1) Y (g x')) ⟦pU⟧ =
          (Quotient.map
            (fun r : GenLoop (Fin (k + 1)) (U n) x' =>
              (⟨g.comp r.1, by
                intro y hy
                rw [ContinuousMap.comp_apply, r.2 y hy]⟩ :
                GenLoop (Fin (k + 1)) Y (g x')))
            (by
              intro r s h
              exact h.map (fun H => H.compContinuousMap g)) :
            HomotopyGroup.Pi (k + 1) (U n) x' →
              HomotopyGroup.Pi (k + 1) Y (g x')) ⟦qU⟧ := by
        exact hab
      have hpq_local := ((hf n).2 k x').1 hlocal
      have hpqX : GenLoop.Homotopic p q := by
        exact (Quotient.eq.mp hpq_local).map (fun H =>
          H.compContinuousMap
            (⟨Subtype.val, continuous_subtype_val⟩ : C(U n, X)))
      exact Quotient.eq.mpr hpqX
    · intro b
      obtain ⟨q, rfl⟩ := Quotient.exists_rep b
      let K : Set X := {x}
      have hK : IsCompact K := by
        simp [K]
      obtain ⟨n, hnK⟩ :=
        exists_cover_stage_of_isCompact hK U hU_open hU_mono hU_cover
      have hx : x ∈ U n := hnK (by simp [K])
      let x' : U n := ⟨x, hx⟩
      obtain ⟨a, ha⟩ :=
        ((hf n).2 k x').2
          (⟦q⟧ : HomotopyGroup.Pi (k + 1) Y (f x))
      obtain ⟨p, rfl⟩ := Quotient.exists_rep a
      use (⟦genLoopExtend (U n) hx p⟧ :
        HomotopyGroup.Pi (k + 1) X x)
      exact ha


#check_dependency_graph "weakHomotopyEquivalence_of_iUnion_open_restrictions" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"Function.Bijective (Quotient.map ⇑f ⋯) ∧ ∀ (k : ℕ) (x : X), Function.Bijective (Quotient.map (fun p => ⟨f.comp ↑p, ⋯⟩) ⋯)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hU_open\",\"statement\":\"∀ (n : { n // 1 ≤ n }), IsOpen (U n)\"},{\"name\":\"hU_mono\",\"statement\":\"Monotone U\"},{\"name\":\"hU_cover\",\"statement\":\"⋃ n, U n = Set.univ\"},{\"name\":\"hf\",\"statement\":\"∀ (n : { n // 1 ≤ n }), let g := { toFun := fun x => f ↑x, continuous_toFun := ⋯ }; Function.Bijective (Quotient.map ⇑g ⋯) ∧ ∀ (k : ℕ) (x : ↑(U n)), Function.Bijective (Quotient.map (fun p => ⟨g.comp ↑p, ⋯⟩) ⋯)\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0367_weakhomotopyequivalence_of_iunion_open_res\",\"reconstructedProofSha256\":\"021b5d859c09bf217def9d432e626804cba028c718e90a5d7d260509c806db5b\",\"selectedEdgeCount\":1,\"theoremName\":\"weakHomotopyEquivalence_of_iUnion_open_restrictions\",\"topologySha256\":\"d8054a5027501cba618538efb0a26a4cda17a805880f39cd49477c4e14fe5b91\"}"
