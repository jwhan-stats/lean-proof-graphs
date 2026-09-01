import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1362_common_coincidence_point_of_ordered_metric
-- topology_sha256: 78e4ae4bf05249dce38e5d4dbc12c701bc55911baceeacadef29b6de62e91336
namespace TopologyCertificate_p1362_common_coincidence_point_of_ordered_metric

-- N001 = hβ_lt_one: ∀ (t : NNReal), β t < 1
-- N002 = hβ_zero: ∀ (t : ℕ → NNReal), Filter.Tendsto (fun n => β (t n)) Filter.atTop (nhds 1) → Filter.Tendsto t Filter.atTop (nhds 0)
-- N003 = hcontract: ∀ (x y : X), H x ≤ H y ∨ H y ≤ H x → nndist (f x) (g y) ≤ β (nndist (H x) (H y)) * nndist (H x) (H y)
-- N004 = hf_range: Set.range f ⊆ Set.range H
-- N005 = hfg_inc: ∀ (x y : X), H y = f x → f x ≤ g y
-- N006 = hH_closed: IsClosed (Set.range H)
-- N007 = hregular: ∀ (z : ℕ → X) (a : X), Monotone z → Filter.Tendsto z Filter.atTop (nhds a) → ∀ (n : ℕ), z n ≤ a
-- N008 = inst._@.proofs.697528154._hygCtx._hyg.12: CompleteSpace X
-- N009 = inst._@.proofs.697528154._hygCtx._hyg.3: Nonempty X
-- N010 = hf_eq_g: ∀ (x : X), f x = g x
-- N011 = goal: ∃ u, f u = g u ∧ g u = H u

-- E001 represents h_001_hf_eq_g
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
    (N011 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (B007 : N007)
    (B008 : N008)
    (B009 : N009)
    (E001 : N003 → N010)
    (E002 : N009 → N008 → N007 → N004 → N006 → N005 → N001 → N002 → N003 → N010 → N011)
    : N011 := by
  have H_N010 : N010 := E001 B003
  have H_N011 : N011 := E002 B009 B008 B007 B004 B006 B005 B001 B002 B003 H_N010
  exact H_N011

end TopologyCertificate_p1362_common_coincidence_point_of_ordered_metric
