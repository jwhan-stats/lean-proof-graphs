import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1335_quarter_stratifiable_diagonal_isgdelta_and
-- topology_sha256: f6d5f2b5cdd3ab71e8e47d685829467cee1447f2787f921b97cf0a3b7dda70a0
namespace TopologyCertificate_p1335_quarter_stratifiable_diagonal_isgdelta_and

-- N001 = hg_converges: ∀ (x : X) (a : ℕ → X), (∀ (n : ℕ), x ∈ g n (a n)) → Filter.Tendsto a Filter.atTop (nhds x)
-- N002 = hg_cover: ∀ (n : ℕ), ⋃ a, g n a = Set.univ
-- N003 = hg_open: ∀ (n : ℕ) (a : X), IsOpen (g n a)
-- N004 = inst._@.proofs.1599378177._hygCtx._hyg.6: T2Space X
-- N005 = goal: (∃ G, (∀ (n : ℕ), IsOpen (G n)) ∧ Set.diagonal X = ⋂ n, G n) ∧ ∀ (x : X), ∃ V, (∀ (n : ℕ), IsOpen (V n) ∧ x ∈ V n) ∧ ⋂ n, V n = {x}

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

end TopologyCertificate_p1335_quarter_stratifiable_diagonal_isgdelta_and
