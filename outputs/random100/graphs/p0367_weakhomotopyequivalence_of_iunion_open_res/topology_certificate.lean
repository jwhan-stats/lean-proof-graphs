import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0367_weakhomotopyequivalence_of_iunion_open_res
-- topology_sha256: d8054a5027501cba618538efb0a26a4cda17a805880f39cd49477c4e14fe5b91
namespace TopologyCertificate_p0367_weakhomotopyequivalence_of_iunion_open_res

-- N001 = hf: ∀ (n : { n // 1 ≤ n }), let g := { toFun := fun x => f ↑x, continuous_toFun := ⋯ }; Function.Bijective (Quotient.map ⇑g ⋯) ∧ ∀ (k : ℕ) (x : ↑(U n)), Function.Bijective (Quotient.map (fun p => ⟨g.comp ↑p, ⋯⟩) ⋯)
-- N002 = hU_cover: ⋃ n, U n = Set.univ
-- N003 = hU_mono: Monotone U
-- N004 = hU_open: ∀ (n : { n // 1 ≤ n }), IsOpen (U n)
-- N005 = goal: Function.Bijective (Quotient.map ⇑f ⋯) ∧ ∀ (k : ℕ) (x : X), Function.Bijective (Quotient.map (fun p => ⟨f.comp ↑p, ⋯⟩) ⋯)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N004 → N003 → N002 → N001 → N005)
    : N005 := by
  have H_N005 : N005 := E001 B004 B003 B002 B001
  exact H_N005

end TopologyCertificate_p0367_weakhomotopyequivalence_of_iunion_open_res
