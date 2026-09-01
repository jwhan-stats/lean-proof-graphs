import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2674_graded_dual_rational_map_mem_completion
-- topology_sha256: ee96ffed4839bb111b30a81d1b3d00b895a201f2c741ddc0e91de1722bd55d11
namespace TopologyCertificate_p2674_graded_dual_rational_map_mem_completion

-- N001 = hcleared: ∀ (w' : DirectSum ℂ fun a => Module.Dual ℂ (W a)), ∃ P, (∀ (α : Fin n →₀ ℕ), MvPolynomial.coeff α P = (DirectSum.toModule ℂ ℂ ℂ fun a => (Module.Dual.eval ℂ (W a)) (g α a)) w') ∧ ∀ (z : { z // Function.Injective z }), (∏ i, ∏ j ∈ Finset.Ioi i, (↑z i - ↑z j) ^ p i j) * (f z) w' = (MvPolynomial.eval ↑z) P
-- N002 = hfinite_g: ∀ (a : ℂ), {α | g α a ≠ 0}.Finite
-- N003 = hD: D ≠ 0
-- N004 = hcomponent: ∀ (a : ℂ) (l : Module.Dual ℂ (W a)), (f z) ((DirectSum.lof ℂ ℂ (fun c => Module.Dual ℂ (W c)) a) l) = l (b a)
-- N005 = goal: ∃ b, f z = DirectSum.toModule ℂ ℂ ℂ fun a => (Module.Dual.eval ℂ (W a)) (b a)

-- E001 represents h_001_hfinite_g
-- E002 represents h_002_hd
-- E003 represents h_003_hcomponent
-- E004 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    (E002 : N003)
    (E003 : N001 → N002 → N003 → N004)
    (E004 : N004 → N005)
    : N005 := by
  have H_N002 : N002 := E001 B001
  have H_N003 : N003 := E002
  have H_N004 : N004 := E003 B001 H_N002 H_N003
  have H_N005 : N005 := E004 H_N004
  exact H_N005

end TopologyCertificate_p2674_graded_dual_rational_map_mem_completion
