import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1151_strict_convex_modular_fixed_point
-- topology_sha256: d75903c07f3cb6dafb1d31aa074ca2f36785d75d8e5ad8a06a5b6745d6002ea8
namespace TopologyCertificate_p1151_strict_convex_modular_fixed_point

-- N001 = hcomplete: ∀ (x : ℕ → { x // ∃ l, 0 < l ∧ w l x b < ⊤ }) (l : NNReal), 0 < l → Filter.Tendsto (fun p => w l ↑(x p.1) ↑(x p.2)) (Filter.atTop ×ˢ Filter.atTop) (nhds 0) → ∃ y, Filter.Tendsto (fun n => w l ↑(x n) ↑y) Filter.atTop (nhds 0)
-- N002 = hcontractive: ∃ k L, 0 < k ∧ k < 1 ∧ 0 < L ∧ ∀ (x y : { x // ∃ l, 0 < l ∧ w l x b < ⊤ }) (l : NNReal), 0 < l → l ≤ L → w (k * l) ↑(T x) ↑(T y) ≤ w l ↑x ↑y
-- N003 = hconv: ∀ (l m : NNReal), 0 < l → 0 < m → ∀ (x y z : X), w (l + m) x y ≤ ↑l / (↑l + ↑m) * w l x z + ↑m / (↑l + ↑m) * w m y z
-- N004 = hself: ∀ (l : NNReal), 0 < l → ∀ (x : X), w l x x = 0
-- N005 = hstrict: ∀ (x y : X), (∃ l, 0 < l ∧ w l x y = 0) → x = y
-- N006 = hsymm: ∀ (l : NNReal), 0 < l → ∀ (x y : X), w l x y = w l y x
-- N007 = goal: ((∀ (l : NNReal), 0 < l → ∃ x, w l ↑x ↑(T x) < ⊤) → ∃ x, T x = x) ∧ ((∀ (l : NNReal), 0 < l → ∀ (x y : { x // ∃ m, 0 < m ∧ w m x b < ⊤ }), w l ↑x ↑y < ⊤) → ∃ xstar, T xstar = xstar ∧ (∀ (y : { x // ∃ l, 0 < l ∧ w l x b < ⊤ }), T y = y → y = xstar) ∧ ∀ (x : { x // ∃ l, 0 < l ∧ w l x b < ⊤ }), ∃ l, 0 < l ∧ Filter.Tendsto (fun n => w l ↑(T^[n] x) ↑xstar) Filter.atTop (nhds 0))

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
    (E001 : N004 → N006 → N005 → N003 → N001 → N002 → N007)
    : N007 := by
  have H_N007 : N007 := E001 B004 B006 B005 B003 B001 B002
  exact H_N007

end TopologyCertificate_p1151_strict_convex_modular_fixed_point
