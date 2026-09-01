import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p3013_finite_compatible_shrinking_lemma
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 8b9aca9fc832e636b74f6b231361ef29e13d563e12637c3874475ffa894fc31d
-- reconstructed_proof_sha256: 5f17a7ff424ed6b8ce9c9d2327c5207d3fdb5da6c55f6e40efd1305f2b5f2569
-- selected_edge_count: 1

/- accepted add_to_file helper 1 -/
lemma compatible_shrinking_closureInterOfRelClosed
    {X : Type*} [TopologicalSpace X] {O B : Set X}
    (hBsub : B ⊆ O)
    (hB : IsClosed (Subtype.val ⁻¹' B : Set O)) :
    closure B ∩ O = B := by
  apply Set.Subset.antisymm
  · intro x hx
    have h := isClosed_preimage_val.mp hB
    have hx' : x ∈ O ∩ closure (O ∩ B) := by
      refine ⟨hx.2, ?_⟩
      have hcl : closure (O ∩ B) = closure B := by
        rw [Set.inter_eq_right.mpr hBsub]
      simpa [hcl] using hx.1
    exact h hx'
  · intro x hx
    exact ⟨subset_closure hx, hBsub hx⟩

/- accepted add_to_file helper 2 -/
lemma compatible_shrinking_relClosedDiff
    {X : Type*} [TopologicalSpace X] {O Z A : Set X}
    (hZO : Z ⊆ O)
    (hZ : IsClosed (Subtype.val ⁻¹' Z : Set O))
    (hA : IsOpen (Subtype.val ⁻¹' A : Set Z)) :
    IsClosed (Subtype.val ⁻¹' (Z \ A) : Set O) := by
  let B : Set X := Z \ A
  have hBsub : B ⊆ O := fun x hx => hZO hx.1
  have hBsubZ : B ⊆ Z := fun x hx => hx.1
  rw [isClosed_preimage_val]
  intro x hx
  have hxO : x ∈ O := hx.1
  have hxclB : x ∈ closure B := by
    change x ∈ closure (Z \ A)
    have hcl : closure (O ∩ (Z \ A)) = closure (Z \ A) := by
      rw [Set.inter_eq_right.mpr (fun y hy => hZO hy.1)]
    simpa [hcl] using hx.2
  have hxZ : x ∈ Z := by
    have hZchar := isClosed_preimage_val.mp hZ
    have hx' : x ∈ O ∩ closure (O ∩ Z) := by
      refine ⟨hxO, ?_⟩
      have hclZ : closure (O ∩ Z) = closure Z := by
        rw [Set.inter_eq_right.mpr hZO]
      have hBcl : closure B ⊆ closure Z := closure_mono hBsubZ
      simpa [hclZ] using hBcl hxclB
    exact hZchar hx'
  have hxnotA : x ∉ A := by
    intro hxA
    rcases isOpen_induced_iff.mp hA with ⟨V, hVopen, hVA⟩
    have hxV : x ∈ V := by
      have hzV : (⟨x, hxZ⟩ : Z) ∈ Subtype.val ⁻¹' V := by
        rw [hVA]
        exact hxA
      exact hzV
    have hdis : V ∩ B = ∅ := by
      ext y
      constructor
      · intro hy
        have hyZ : y ∈ Z := hy.2.1
        have hyA : y ∈ A := by
          have hzV : (⟨y, hyZ⟩ : Z) ∈ Subtype.val ⁻¹' V := hy.1
          rwa [hVA] at hzV
        exact (hy.2.2 hyA).elim
      · intro hy
        cases hy
    have hmem := (mem_closure_iff.mp hxclB) V hVopen hxV
    exact hmem.ne_empty hdis
  exact ⟨hxZ, hxnotA⟩

/- accepted add_to_file helper 3 -/
noncomputable def testIf (A : Set ℕ) : ℕ := @ite ℕ A.Nonempty (Classical.dec _) 1 0

/- accepted add_to_file helper 4 -/
noncomputable def compatibleDistAux
    {X : Type*} [MetricSpace X] (A : Set X) (x : X) : ℝ :=
  @ite ℝ A.Nonempty (Classical.dec _) (min 1 (Metric.infDist x A)) 1

lemma compatibleDistAux_zero_iff
    {X : Type*} [MetricSpace X] (A : Set X) (x : X) :
    compatibleDistAux A x = 0 ↔ x ∈ closure A := by
  unfold compatibleDistAux
  by_cases hA : A.Nonempty
  · rw [if_pos hA]
    constructor
    · intro h0
      have hd0 : Metric.infDist x A = 0 := by
        by_cases hdle : Metric.infDist x A ≤ 1
        · have hmin := min_eq_right hdle
          rw [hmin] at h0
          exact h0
        · have hmin : min 1 (Metric.infDist x A) = 1 :=
            min_eq_left (le_of_lt (not_le.mp hdle))
          rw [hmin] at h0
          norm_num at h0
      exact (Metric.mem_closure_iff_infDist_zero hA).mpr hd0
    · intro hx
      rw [Metric.infDist_zero_of_mem_closure hx]
      norm_num
  · rw [if_neg hA]
    have hempty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    simp [hempty]

lemma continuous_compatibleDistAux
    {X : Type*} [MetricSpace X] (A : Set X) :
    Continuous fun x => compatibleDistAux A x := by
  unfold compatibleDistAux
  by_cases hA : A.Nonempty
  · have hfun : (fun x => @ite ℝ A.Nonempty (Classical.dec _)
        (min 1 (Metric.infDist x A)) 1) =
        fun x => min 1 (Metric.infDist x A) := by
      funext x
      exact if_pos hA
    rw [hfun]
    exact continuous_const.min (Metric.continuous_infDist_pt A)
  · have hfun : (fun x => @ite ℝ A.Nonempty (Classical.dec _)
        (min 1 (Metric.infDist x A)) 1) = fun _ => 1 := by
      funext x
      exact if_neg hA
    rw [hfun]
    exact continuous_const

/- accepted add_to_file helper 5 -/
lemma compatibleDistAux_nonneg
    {X : Type*} [MetricSpace X] (A : Set X) (x : X) :
    0 ≤ compatibleDistAux A x := by
  unfold compatibleDistAux
  by_cases hA : A.Nonempty
  · rw [if_pos hA]
    exact le_min zero_le_one Metric.infDist_nonneg
  · rw [if_neg hA]
    norm_num

/- accepted add_to_file helper 6 -/
lemma compatible_shrinking_exists_singletons
    {X : Type*} [MetricSpace X]
    {O Z : Set X} (N : ℕ)
    (Zi : Fin N → Set X) (W : Set (Fin N) → Set X)
    (hO : IsOpen O)
    (hZO : Z ⊆ O)
    (hZclosed : IsClosed (Subtype.val ⁻¹' Z : Set O))
    (hZi_subset : ∀ i, Zi i ⊆ Z)
    (hZi_open : ∀ i, IsOpen (Subtype.val ⁻¹' Zi i : Set Z))
    (hW : ∀ K : Set (Fin N), K.Nonempty →
      IsOpen (W K) ∧ W K ⊆ O ∧ W K ∩ Z = ⋂ i ∈ K, Zi i) :
    ∃ V : Fin N → Set X,
      (∀ i, IsOpen (V i) ∧ V i ∩ Z = Zi i) ∧
      ∀ K : Set (Fin N), K.Nonempty → (⋂ i ∈ K, V i) ⊆ W K := by
  classical
  let B : Fin N → Set X := fun i => Z \ Zi i
  let A : Fin N → Set X := fun i => closure (B i)
  let D : Set (Fin N) → Set X := fun K => closure (O \ W K) ∩ (W K)ᶜ
  let d : Fin N → X → ℝ := fun i x => compatibleDistAux (B i) x
  let P : Set (Fin N) → Fin N → Set X := fun K i =>
    {x | x ∈ D K ∧ ∀ j ∈ K, d i x ≤ d j x}
  let S : Fin N → Set (Set (Fin N)) := fun i => {K | K.Nonempty ∧ i ∈ K}
  let E : Fin N → Set X := fun i => A i ∪ ⋃ K ∈ S i, P K i
  have hBsub : ∀ i, B i ⊆ O := by
    intro i x hx
    exact hZO hx.1
  have hBrel : ∀ i, IsClosed (Subtype.val ⁻¹' B i : Set O) := by
    intro i
    exact compatible_shrinking_relClosedDiff hZO hZclosed (hZi_open i)
  have hAtrace : ∀ i, A i ∩ Z = B i := by
    intro i
    have h := compatible_shrinking_closureInterOfRelClosed (hBsub i) (hBrel i)
    apply Set.Subset.antisymm
    · intro x hx
      have hxO : x ∈ O := hZO hx.2
      have hx' : x ∈ A i ∩ O := ⟨hx.1, hxO⟩
      rwa [h] at hx'
    · intro x hx
      exact ⟨subset_closure hx, hx.1⟩
  have hPclosed : ∀ K : Set (Fin N), K.Nonempty → ∀ i, IsClosed (P K i) := by
    intro K hK i
    have hDclosed : IsClosed (D K) := by
      exact isClosed_closure.inter ((hW K hK).1.isClosed_compl)
    have hineq : ∀ j ∈ K, IsClosed {x : X | d i x ≤ d j x} := by
      intro j hj
      exact isClosed_le (continuous_compatibleDistAux (B i))
        (continuous_compatibleDistAux (B j))
    have hbi : IsClosed (⋂ j ∈ K, {x : X | d i x ≤ d j x}) :=
      isClosed_biInter hineq
    have hPeq : P K i = D K ∩ ⋂ j ∈ K, {x : X | d i x ≤ d j x} := by
      ext x
      simp [P]
    rw [hPeq]
    exact hDclosed.inter hbi
  have hSfinite : ∀ i, (S i).Finite := by
    intro i
    exact Set.finite_univ.subset (Set.subset_univ _)
  have hEclosed : ∀ i, IsClosed (E i) := by
    intro i
    apply isClosed_closure.union
    exact (hSfinite i).isClosed_biUnion (by
      intro K hK
      exact hPclosed K hK.1 i)
  have hPtrace : ∀ K : Set (Fin N), K.Nonempty → ∀ i, P K i ∩ Z ⊆ A i := by
    intro K hK i x hx
    have hxP : x ∈ P K i := hx.1
    have hxZ : x ∈ Z := hx.2
    have hxnotW : x ∉ W K := hxP.1.2
    have hnotinter : x ∉ ⋂ j ∈ K, Zi j := by
      intro hxinter
      have hxmem : x ∈ W K ∩ Z := by
        rw [(hW K hK).2.2]
        exact hxinter
      exact hxnotW hxmem.1
    have hnotforall : ¬ ∀ j, j ∈ K → x ∈ Zi j := by
      intro hall
      apply hnotinter
      simpa using hall
    rcases not_forall₂.mp hnotforall with ⟨j, hjK, hxnotj⟩
    have hxBj : x ∈ B j := ⟨hxZ, hxnotj⟩
    have hdj0 : d j x = 0 := by
      exact (compatibleDistAux_zero_iff (B j) x).mpr (subset_closure hxBj)
    have hle : d i x ≤ 0 := by
      simpa [hdj0] using hxP.2 j hjK
    have hdi0 : d i x = 0 := le_antisymm hle (compatibleDistAux_nonneg (B i) x)
    exact (compatibleDistAux_zero_iff (B i) x).mp hdi0
  have hEtrace : ∀ i, E i ∩ Z = B i := by
    intro i
    apply Set.Subset.antisymm
    · intro x hx
      have hxZ : x ∈ Z := hx.2
      have hxE : x ∈ E i := hx.1
      rcases hxE with hxA | hxU
      · have : x ∈ A i ∩ Z := ⟨hxA, hxZ⟩
        rwa [hAtrace i] at this
      · rcases Set.mem_iUnion.mp hxU with ⟨K, hKmem⟩
        rcases Set.mem_iUnion.mp hKmem with ⟨hKS, hxP⟩
        have : x ∈ P K i ∩ Z := ⟨hxP, hxZ⟩
        have hxA := hPtrace K hKS.1 i this
        have : x ∈ A i ∩ Z := ⟨hxA, hxZ⟩
        rwa [hAtrace i] at this
    · intro x hx
      exact ⟨Or.inl (subset_closure hx), hx.1⟩
  have hPcover : ∀ K : Set (Fin N), K.Nonempty → D K ⊆ ⋃ i ∈ K, P K i := by
    intro K hK x hxD
    let s : Finset (Fin N) := K.toFinset
    have hs : s.Nonempty := by
      simpa [s, Set.toFinset_nonempty] using hK
    rcases Finset.exists_min_image s (fun i => d i x) hs with ⟨i, his, hmin⟩
    have hiK : i ∈ K := by simpa [s] using his
    apply Set.mem_iUnion.mpr
    exists i
    apply Set.mem_iUnion.mpr
    exists hiK
    exact ⟨hxD, by
      intro j hjK
      exact hmin j (by simpa [s] using hjK)⟩
  have hEcover : ∀ K : Set (Fin N), K.Nonempty → O \ W K ⊆ ⋃ i ∈ K, E i := by
    intro K hK x hx
    have hxD : x ∈ D K := ⟨subset_closure hx, hx.2⟩
    have hxP := hPcover K hK hxD
    rcases Set.mem_iUnion.mp hxP with ⟨i, himem⟩
    rcases Set.mem_iUnion.mp himem with ⟨hiK, hxi⟩
    apply Set.mem_iUnion.mpr
    exists i
    apply Set.mem_iUnion.mpr
    exists hiK
    exact Or.inr (Set.mem_iUnion.mpr ⟨K,
      Set.mem_iUnion.mpr ⟨⟨hK, hiK⟩, hxi⟩⟩)
  let V : Fin N → Set X := fun i => O ∩ (E i)ᶜ
  refine ⟨V, ?_, ?_⟩
  · intro i
    constructor
    · exact hO.inter (hEclosed i).isOpen_compl
    · apply Set.Subset.antisymm
      · intro x hx
        have hxZ : x ∈ Z := hx.2
        have hxnotE : x ∉ E i := hx.1.2
        have hxnotB : x ∉ B i := by
          intro hxB
          apply hxnotE
          have hxEi : x ∈ E i := Or.inl (subset_closure hxB)
          exact hxEi
        by_contra hnot
        exact hxnotB ⟨hxZ, hnot⟩
      · intro x hx
        have hxZ : x ∈ Z := hZi_subset i hx
        have hxO : x ∈ O := hZO hxZ
        have hxnotE : x ∉ E i := by
          intro hxE
          have hxEZ : x ∈ E i ∩ Z := ⟨hxE, hxZ⟩
          rw [hEtrace i] at hxEZ
          exact hxEZ.2 hx
        exact ⟨⟨hxO, hxnotE⟩, hxZ⟩
  · intro K hK x hx
    rcases hK with ⟨i₀, hi₀⟩
    have hxVi₀ : x ∈ V i₀ := Set.mem_iInter₂.mp hx i₀ hi₀
    have hxO : x ∈ O := hxVi₀.1
    by_contra hxW
    have hxdiff : x ∈ O \ W K := ⟨hxO, hxW⟩
    have hxE := hEcover K ⟨i₀, hi₀⟩ hxdiff
    rcases Set.mem_iUnion.mp hxE with ⟨i, himem⟩
    rcases Set.mem_iUnion.mp himem with ⟨hiK, hxiE⟩
    have hxVi : x ∈ V i := Set.mem_iInter₂.mp hx i hiK
    exact hxVi.2 hxiE

/- verified submission -/
theorem finite_compatible_shrinking_lemma
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    {O Z : Set X} (N : ℕ) (hN : 0 < N)
    (Zi : Fin N → Set X) (W : Set (Fin N) → Set X)
    (hO : IsOpen O) (hOcompact : IsCompact (closure O))
    (hZO : Z ⊆ O)
    (hZclosed : IsClosed (Subtype.val ⁻¹' Z : Set O))
    (hZi_subset : ∀ i, Zi i ⊆ Z)
    (hZi_open : ∀ i, IsOpen (Subtype.val ⁻¹' Zi i : Set Z))
    (hW : ∀ K : Set (Fin N), K.Nonempty →
      IsOpen (W K) ∧ W K ⊆ O ∧ W K ∩ Z = ⋂ i ∈ K, Zi i) :
    ∃ U : Set (Fin N) → Set X,
      (∀ K : Set (Fin N), K.Nonempty →
        IsOpen (U K) ∧ U K ⊆ W K ∧ U K ∩ Z = ⋂ i ∈ K, Zi i) ∧
      ∀ J K : Set (Fin N), J.Nonempty → K.Nonempty →
        U J ∩ U K = U (J ∪ K) := by
  classical
  rcases compatible_shrinking_exists_singletons N Zi W hO hZO hZclosed
      hZi_subset hZi_open hW with ⟨V, hV, hVsub⟩
  let U : Set (Fin N) → Set X := fun K => ⋂ i ∈ K, V i
  refine ⟨U, ?_, ?_⟩
  · intro K hK
    refine ⟨?_, hVsub K hK, ?_⟩
    · exact K.toFinite.isOpen_biInter (fun i hi => (hV i).1)
    · calc
        U K ∩ Z = (⋂ i ∈ K, V i) ∩ Z := rfl
        _ = ⋂ i ∈ K, (V i ∩ Z) := by
          ext x
          constructor
          · intro hx
            have hmem := Set.mem_iInter₂.mp hx.1
            apply Set.mem_iInter₂.mpr
            intro i hi
            exact ⟨hmem i hi, hx.2⟩
          · intro hx
            have hall := Set.mem_iInter₂.mp hx
            rcases hK with ⟨i₀, hi₀⟩
            constructor
            · apply Set.mem_iInter₂.mpr
              intro i hi
              exact (hall i hi).1
            · exact (hall i₀ hi₀).2
        _ = ⋂ i ∈ K, Zi i := by
          simp [fun i => (hV i).2]
  · intro J K hJ hK
    ext x
    simp [U, Set.mem_union, or_imp, forall_and]


#check_dependency_graph "finite_compatible_shrinking_lemma" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∃ U, (∀ (K : Set (Fin N)), K.Nonempty → IsOpen (U K) ∧ U K ⊆ W K ∧ U K ∩ Z = ⋂ i ∈ K, Zi i) ∧ ∀ (J K : Set (Fin N)), J.Nonempty → K.Nonempty → U J ∩ U K = U (J ∪ K)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hO\",\"statement\":\"IsOpen O\"},{\"name\":\"hZO\",\"statement\":\"Z ⊆ O\"},{\"name\":\"hZclosed\",\"statement\":\"IsClosed (Subtype.val ⁻¹' Z)\"},{\"name\":\"hZi_subset\",\"statement\":\"∀ (i : Fin N), Zi i ⊆ Z\"},{\"name\":\"hZi_open\",\"statement\":\"∀ (i : Fin N), IsOpen (Subtype.val ⁻¹' Zi i)\"},{\"name\":\"hW\",\"statement\":\"∀ (K : Set (Fin N)), K.Nonempty → IsOpen (W K) ∧ W K ⊆ O ∧ W K ∩ Z = ⋂ i ∈ K, Zi i\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p3013_finite_compatible_shrinking_lemma\",\"reconstructedProofSha256\":\"5f17a7ff424ed6b8ce9c9d2327c5207d3fdb5da6c55f6e40efd1305f2b5f2569\",\"selectedEdgeCount\":1,\"theoremName\":\"finite_compatible_shrinking_lemma\",\"topologySha256\":\"8b9aca9fc832e636b74f6b231361ef29e13d563e12637c3874475ffa894fc31d\"}"
