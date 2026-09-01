import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p3210_substochastic_row_update_product
-- topology_sha256: db50fe190604d05227612447bcc66f9ea76bc24aec9dacd3acf69bb671db2c27
namespace TopologyCertificate_p3210_substochastic_row_update_product

-- N001 = hC_nonneg: ∀ (i j : Fin N), 0 ≤ C i j
-- N002 = hQ: Q = (List.ofFn fun i => Matrix.updateRow 1 i (C i)).reverse.prod
-- N003 = hr: IsGreatest (Set.range fun i => ∑ j, C i j) r
-- N004 = hr_lt_one: r < 1
-- N005 = hinvariant: (∀ (x : Fin N), ∑ j, (List.map (fun a => Matrix.updateRow 1 a (C a)) idx.reverse).prod x j ≤ 1) ∧ ∀ i ∈ idx.reverse, ∑ j, (List.map (fun a => Matrix.updateRow 1 a (C a)) idx.reverse).prod i j ≤ r
-- N006 = hi_idx: i ∈ idx
-- N007 = hi: i ∈ idx.reverse
-- N008 = hbound: ∑ j, (List.map (fun a => Matrix.updateRow 1 a (C a)) idx.reverse).prod i j ≤ r
-- N009 = goal: ∑ j, Q i j ≤ r

-- E001 represents h_001_hinvariant
-- E002 represents h_002_hi_idx
-- E003 represents h_003_hi
-- E004 represents h_004_hbound
-- E005 represents h_goal

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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N001 → N003 → N004 → N005)
    (E002 : N006)
    (E003 : N006 → N007)
    (E004 : N005 → N007 → N008)
    (E005 : N002 → N008 → N009)
    : N009 := by
  have H_N005 : N005 := E001 B001 B003 B004
  have H_N006 : N006 := E002
  have H_N007 : N007 := E003 H_N006
  have H_N008 : N008 := E004 H_N005 H_N007
  have H_N009 : N009 := E005 B002 H_N008
  exact H_N009

end TopologyCertificate_p3210_substochastic_row_update_product
