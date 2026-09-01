import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0019_unique_diagonal_perfect_matching_iff_no_al
-- topology_sha256: a1634d7f40419c801a109035bdeb7fe0590e91296c79e9c810f08e9363381342
namespace TopologyCertificate_p0019_unique_diagonal_perfect_matching_iff_no_al

-- N001 = hdiag: ∀ (i : Fin n), G.Adj (x i) (y i)
-- N002 = hunmixed: ∀ (C : Set V), Minimal G.IsVertexCover C → C.ncard = n
-- N003 = hxy: Function.Bijective (Sum.elim x y)
-- N004 = hY: Maximal G.IsIndepSet (Set.range y)
-- N005 = hBC: B ↔ C
-- N006 = goal: ((∃ M, M.IsPerfectMatching ∧ (∀ (u v : V), M.Adj u v ↔ ∃ i, u = x i ∧ v = y i ∨ u = y i ∧ v = x i) ∧ ∀ (M' : G.Subgraph), M'.IsPerfectMatching → M' = M) ↔ ∀ (i j : Fin n), i < j → ¬(G.Adj (x i) (y i) ∧ G.Adj (y i) (x j) ∧ G.Adj (x j) (y j) ∧ G.Adj (y j) (x i))) ∧ ((∀ (i j : Fin n), i < j → ¬(G.Adj (x i) (y i) ∧ G.Adj (y i) (x j) ∧ G.Adj (x j) (y j) ∧ G.Adj (y j) (x i))) ↔ ∀ (r : ℕ) (i : Fin (r + 2) → Fin n), Function.Injective i → ¬∀ (s : Fin (r + 2)), G.Adj (x (i s)) (y (i s)) ∧ G.Adj (y (i s)) (x (i (s + 1))))

-- E001 represents h_001_hbc
-- E002 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N003 → N004 → N001 → N002 → N005)
    (E002 : N003 → N004 → N001 → N005 → N006)
    : N006 := by
  have H_N005 : N005 := E001 B003 B004 B001 B002
  have H_N006 : N006 := E002 B003 B004 B001 H_N005
  exact H_N006

end TopologyCertificate_p0019_unique_diagonal_perfect_matching_iff_no_al
