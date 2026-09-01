import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2116_pendant_branch_laplacian_eigenvector_decay
-- topology_sha256: 6def72b531159d4e71e5ba8bebbb09ad9dc81baad6b3138a095ddbee09f704e8
namespace TopologyCertificate_p2116_pendant_branch_laplacian_eigenvector_decay

-- N001 = hbranch: ∀ (a b : Fin k), G.Adj (i a) (i b) ↔ ↑a + 1 = ↑b ∨ ↑b + 1 = ↑a
-- N002 = heigen: (SimpleGraph.lapMatrix ℝ G).mulVec φ = lam • φ
-- N003 = hexternal: ∃ x ∉ Set.range i, G.Adj (i ⟨0, hk⟩) x ∧ ∀ (a : Fin k), ∀ v ∉ Set.range i, G.Adj (i a) v → a = ⟨0, hk⟩ ∧ v = x
-- N004 = hi: Function.Injective i
-- N005 = hk: 1 ≤ k
-- N006 = hlam: 4 < lam
-- N007 = goal: let γ := 2 / (lam - 2); 0 < γ ∧ γ < 1 ∧ (∀ (j : Fin k) (hj : ↑j + 1 < k), |φ (i ⟨↑j + 1, hj⟩)| ≤ γ * |φ (i j)|) ∧ ∀ (j : Fin k), |φ (i j)| ≤ γ ^ ↑j * |φ (i ⟨0, hk⟩)|

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (E001 : N005 → N004 → N001 → N003 → N006 → N002 → N007)
    : N007 := by
  have H_N007 : N007 := E001 B005 B004 B001 B003 B006 B002
  exact H_N007

end TopologyCertificate_p2116_pendant_branch_laplacian_eigenvector_decay
