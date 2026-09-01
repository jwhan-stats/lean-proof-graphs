import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1299_convexpolytope_trace_latticeembedding
-- topology_sha256: 05c80beeafdb73c7eb8a5d1fdb49b2806e9f9882af8cd90b50f37d0303868e47
namespace TopologyCertificate_p1299_convexpolytope_trace_latticeembedding

-- N001 = hextreme: ∀ (x : L), Set.extremePoints F (φ x) ⊆ Ω
-- N002 = hinj: Function.Injective φ
-- N003 = hjoin: ∀ (x y : L), φ (x ⊔ y) = (convexHull F) (φ x ∪ φ y)
-- N004 = hmeet: ∀ (x y : L), φ (x ⊓ y) = φ x ∩ φ y
-- N005 = hpoly: ∀ (x : L), ∃ A, A.Finite ∧ (convexHull F) A = φ x
-- N006 = inst._@.proofs.3608069470._hygCtx._hyg.11: IsStrictOrderedRing F
-- N007 = hconv: ∀ (x : L), (convexHull F) (ψ x) = φ x
-- N008 = hψinj: Function.Injective ψ
-- N009 = goal: (Function.Injective fun x => φ x ∩ Ω) ∧ (∀ (x : L), Ω ∩ (convexHull F) ((fun x => φ x ∩ Ω) x) = (fun x => φ x ∩ Ω) x) ∧ (∀ (x y : L), (fun x => φ x ∩ Ω) (x ⊓ y) = (fun x => φ x ∩ Ω) x ∩ (fun x => φ x ∩ Ω) y) ∧ (∀ (x y : L), (fun x => φ x ∩ Ω) (x ⊔ y) = Ω ∩ (convexHull F) ((fun x => φ x ∩ Ω) x ∪ (fun x => φ x ∩ Ω) y)) ∧ ∀ (x : L), (convexHull F) ((fun x => φ x ∩ Ω) x) = φ x

-- E001 represents h_001_hconv
-- E002 represents h_002_h_inj
-- E003 represents h_goal

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
    (B005 : N005)
    (B006 : N006)
    (E001 : N006 → N005 → N001 → N007)
    (E002 : N002 → N007 → N008)
    (E003 : N004 → N003 → N007 → N008 → N009)
    : N009 := by
  have H_N007 : N007 := E001 B006 B005 B001
  have H_N008 : N008 := E002 B002 H_N007
  have H_N009 : N009 := E003 B004 B003 H_N007 H_N008
  exact H_N009

end TopologyCertificate_p1299_convexpolytope_trace_latticeembedding
