import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0489_caristi_kirk_bmetric_fixed_point
-- topology_sha256: e3c506562155440bc52f1df77609cd5aa3e4eb91c6122edfd93871c94b5cd418
namespace TopologyCertificate_p0489_caristi_kirk_bmetric_fixed_point

-- N001 = hA: 1 < A
-- N002 = hcaristi: ∀ (x : X), ↑(d (x, f x)) ≤ ↑(Φ x) - A * ↑(Φ (f x))
-- N003 = hcomplete: ∀ (x : ℕ → X), Filter.Tendsto (fun p => d (x p.1, x p.2)) (Filter.atTop ×ˢ Filter.atTop) (nhds 0) → ∃ u, Filter.Tendsto (fun n => d (x n, u)) Filter.atTop (nhds 0)
-- N004 = hd_symm: ∀ (x y : X), d (x, y) = d (y, x)
-- N005 = hd_triangle: ∀ (x y z : X), ↑(d (x, y)) ≤ s * (↑(d (x, z)) + ↑(d (z, y)))
-- N006 = hd_zero: ∀ (x y : X), d (x, y) = 0 ↔ x = y
-- N007 = hf_continuous: ∀ (x : ℕ → X) (u : X), Filter.Tendsto (fun n => d (x n, u)) Filter.atTop (nhds 0) → Filter.Tendsto (fun n => d (f (x n), f u)) Filter.atTop (nhds 0)
-- N008 = hs: 1 ≤ s
-- N009 = hcauchy: Filter.Tendsto (fun p => d (x p.1, x p.2)) (Filter.atTop ×ˢ Filter.atTop) (nhds 0)
-- N010 = goal: ∃ u, f u = u ∧ Filter.Tendsto (fun n => d (f^[n] x₀, u)) Filter.atTop (nhds 0)

-- E001 represents h_001_hcauchy
-- E002 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (B007 : N007)
    (B008 : N008)
    (E001 : N008 → N006 → N004 → N005 → N001 → N002 → N009)
    (E002 : N006 → N004 → N005 → N003 → N007 → N009 → N010)
    : N010 := by
  have H_N009 : N009 := E001 B008 B006 B004 B005 B001 B002
  have H_N010 : N010 := E002 B006 B004 B005 B003 B007 H_N009
  exact H_N010

end TopologyCertificate_p0489_caristi_kirk_bmetric_fixed_point
