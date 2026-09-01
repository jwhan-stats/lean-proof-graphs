import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2581_looptree_height_bound
-- topology_sha256: b7ec0112d20e1e455666de77441337e930d042a56ef4ed9c1c4be27d8ce7cc77
namespace TopologyCertificate_p2581_looptree_height_bound

-- N001 = hchildren: ∀ v ∈ τ, ∀ (m : ℕ), v ++ [m] ∈ τ ↔ 1 ≤ m ∧ m ≤ k v
-- N002 = hij: i < j
-- N003 = hlex: ∀ (a b : Fin N), a < b ↔ List.Lex (fun x y => x < y) ↑(u a) ↑(u b)
-- N004 = hpre: ↑(u i) <+: ↑(u j)
-- N005 = hprefix: ∀ ⦃v p : List ℕ⦄, v ∈ τ → p <+: v → p ∈ τ
-- N006 = hroot: [] ∈ τ
-- N007 = hWstep: ∀ (r : Fin N), W r.succ = W r.castSucc + ↑(k ↑(u r)) - 1
-- N008 = hreach: Loop.Reachable (u i) (u j)
-- N009 = hdist: ↑(Loop.dist (u i) (u j)) ≤ W j.castSucc - W i.castSucc + ↑(H j) - ↑(H i)
-- N010 = hcomm: Loop.dist (u j) (u i) = Loop.dist (u i) (u j)
-- N011 = hdist_i: Loop.dist (u i) ⟨[], hroot⟩ = Loop.dist ⟨[], hroot⟩ (u i)
-- N012 = hdist_j: Loop.dist (u j) ⟨[], hroot⟩ = Loop.dist ⟨[], hroot⟩ (u j)
-- N013 = htri_i: Loop.dist (u i) ⟨[], hroot⟩ ≤ Loop.dist (u i) (u j) + Loop.dist (u j) ⟨[], hroot⟩
-- N014 = htri_j: Loop.dist (u j) ⟨[], hroot⟩ ≤ Loop.dist (u j) (u i) + Loop.dist (u i) ⟨[], hroot⟩
-- N015 = htri_iZ: ↑(Loop.dist (u i) ⟨[], hroot⟩) ≤ ↑(Loop.dist (u i) (u j)) + ↑(Loop.dist (u j) ⟨[], hroot⟩)
-- N016 = htri_jZ: ↑(Loop.dist (u j) ⟨[], hroot⟩) ≤ ↑(Loop.dist (u i) (u j)) + ↑(Loop.dist (u i) ⟨[], hroot⟩)
-- N017 = goal: |↑(Hb i) - ↑(Hb j)| ≤ W j.castSucc - W i.castSucc + ↑(H j) - ↑(H i)

-- E001 represents h_001_hreach
-- E002 represents h_002_hdist
-- E003 represents h_005_hcomm
-- E004 represents h_008_hdist_i
-- E005 represents h_009_hdist_j
-- E006 represents h_003_htri_i
-- E007 represents h_004_htri_j
-- E008 represents h_006_htri_iz
-- E009 represents h_007_htri_jz
-- E010 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (N008 : Prop)
    (N009 : Prop)
    (N010 : Prop)
    (N011 : Prop)
    (N012 : Prop)
    (N013 : Prop)
    (N014 : Prop)
    (N015 : Prop)
    (N016 : Prop)
    (N017 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (B007 : N007)
    (E001 : N005 → N001 → N004 → N008)
    (E002 : N005 → N001 → N003 → N007 → N002 → N004 → N009)
    (E003 : N010)
    (E004 : N006 → N011)
    (E005 : N006 → N012)
    (E006 : N006 → N008 → N013)
    (E007 : N006 → N008 → N014)
    (E008 : N006 → N013 → N015)
    (E009 : N006 → N014 → N010 → N016)
    (E010 : N006 → N009 → N015 → N016 → N011 → N012 → N017)
    : N017 := by
  have H_N008 : N008 := E001 B005 B001 B004
  have H_N009 : N009 := E002 B005 B001 B003 B007 B002 B004
  have H_N010 : N010 := E003
  have H_N011 : N011 := E004 B006
  have H_N012 : N012 := E005 B006
  have H_N013 : N013 := E006 B006 H_N008
  have H_N014 : N014 := E007 B006 H_N008
  have H_N015 : N015 := E008 B006 H_N013
  have H_N016 : N016 := E009 B006 H_N014 H_N010
  have H_N017 : N017 := E010 B006 H_N009 H_N015 H_N016 H_N011 H_N012
  exact H_N017

end TopologyCertificate_p2581_looptree_height_bound
