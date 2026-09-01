import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1722_hirzebruch_jung_large_entries_at_most_two
-- topology_sha256: 68ed2744cdb1d7035722b828fa61040478e1c5ad3b5b31aff3bcf59ad48149a7
namespace TopologyCertificate_p1722_hirzebruch_jung_large_entries_at_most_two

-- N001 = ha: ∀ (i : Fin n), 2 ≤ a i
-- N002 = hfrac: List.foldr (fun x r => x - 1 / r) 0 (List.ofFn fun i => ↑(a i)) = ↑p / ↑q
-- N003 = hn: 1 ≤ n
-- N004 = hp: 0 < p
-- N005 = hpq: p.Coprime q
-- N006 = hq: 0 < q
-- N007 = hS: 2 * ↑p / 9 < ∑ i with 3 < a i, ↑(a i - 3)
-- N008 = goal: {i | 3 < a i}.card ≤ 2

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (N006 : Prop)
    (N007 : Prop)
    (N008 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (B007 : N007)
    (E001 : N003 → N001 → N004 → N006 → N005 → N002 → N007 → N008)
    : N008 := by
  have H_N008 : N008 := E001 B003 B001 B004 B006 B005 B002 B007
  exact H_N008

end TopologyCertificate_p1722_hirzebruch_jung_large_entries_at_most_two
