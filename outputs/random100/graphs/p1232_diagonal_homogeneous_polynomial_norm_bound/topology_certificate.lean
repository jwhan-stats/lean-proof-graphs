import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1232_diagonal_homogeneous_polynomial_norm_bound
-- topology_sha256: 910854e5c1c89e9dea383bc8c54c2f4098dc9bdd1ead6751c521e969dbe06da9
namespace TopologyCertificate_p1232_diagonal_homogeneous_polynomial_norm_bound

-- N001 = hφ: ∀ (α : Fin k → 𝕂), (A * if p = ⊤ then ‖α‖ else (∑ j, ‖α j‖.rpow p.toReal).rpow (1 / p.toReal)) ≤ ‖∑ j, α j • φ j‖ ∧ ‖∑ j, α j • φ j‖ ≤ B * if p = ⊤ then ‖α‖ else (∑ j, ‖α j‖.rpow p.toReal).rpow (1 / p.toReal)
-- N002 = hA: 0 < A
-- N003 = hB: 0 < B
-- N004 = hk: 1 ≤ k
-- N005 = hn: 1 ≤ n
-- N006 = hnq: p.conjExponent ≤ ↑n
-- N007 = hp: 1 < p
-- N008 = hpoint: ∀ y ∈ S, y ≤ B ^ n * ‖α‖
-- N009 = hnonempty: S.Nonempty
-- N010 = hBdd: BddAbove S
-- N011 = hupper: sSup S ≤ B ^ n * ‖α‖
-- N012 = goal: A ^ n * ‖α‖ ≤ sSup (Set.range fun x => ‖∑ j, α j * (φ j) ↑x ^ n‖) ∧ sSup (Set.range fun x => ‖∑ j, α j * (φ j) ↑x ^ n‖) ≤ B ^ n * ‖α‖

-- E001 represents h_001_hpoint
-- E002 represents h_003_hnonempty
-- E003 represents h_002_hbdd
-- E004 represents h_004_hupper
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
    (N010 : Prop)
    (N011 : Prop)
    (N012 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (B005 : N005)
    (B006 : N006)
    (B007 : N007)
    (E001 : N004 → N003 → N007 → N001 → N005 → N006 → N008)
    (E002 : N005 → N009)
    (E003 : N008 → N010)
    (E004 : N008 → N010 → N009 → N011)
    (E005 : N004 → N002 → N007 → N001 → N005 → N010 → N011 → N012)
    : N012 := by
  have H_N008 : N008 := E001 B004 B003 B007 B001 B005 B006
  have H_N009 : N009 := E002 B005
  have H_N010 : N010 := E003 H_N008
  have H_N011 : N011 := E004 H_N008 H_N010 H_N009
  have H_N012 : N012 := E005 B004 B002 B007 B001 B005 H_N010 H_N011
  exact H_N012

end TopologyCertificate_p1232_diagonal_homogeneous_polynomial_norm_bound
