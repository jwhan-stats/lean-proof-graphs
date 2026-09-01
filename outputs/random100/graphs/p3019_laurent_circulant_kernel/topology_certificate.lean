import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p3019_laurent_circulant_kernel
-- topology_sha256: 63d6015b119f90a9baba38749e4205742c89b29c8136c262b83a135dc804b604
namespace TopologyCertificate_p3019_laurent_circulant_kernel

-- N001 = ha: 0 < a
-- N002 = hab: a < b
-- N003 = hab_coprime: a.Coprime b
-- N004 = hv: B.mulVec v = 0
-- N005 = hNe: NeZero (a + b)
-- N006 = hcop: a.Coprime (a + b)
-- N007 = hv': (Rollout_p3019_laurent_circulant_kernel.laurentCirculantB a b ε).mulVec v = 0
-- N008 = ht: t ^ (a + b) ≠ (-1) ^ (a + b)
-- N009 = hrec: ∀ (r : ZMod (a + b)), x r + t * x (r + 1) = 0
-- N010 = hx: ∀ (r : ZMod (a + b)), x r = 0
-- N011 = hwinv: ∀ (r : ZMod (a + b)), w r = w (r - ↑a)
-- N012 = hweq: ∀ (i j : ZMod (a + b)), w i = w j
-- N013 = hvinv: ∀ (r : ZMod (a + b)), v r = v (r - ↑a)
-- N014 = goal: v i = v j

-- E001 represents h_001_hne
-- E002 represents h_006_hcop
-- E003 represents h_002_hv
-- E004 represents h_004_ht
-- E005 represents h_003_hrec
-- E006 represents h_005_hx
-- E007 represents h_007_hwinv
-- E008 represents h_008_hweq
-- E009 represents h_009_hvinv
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
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N001 → N005)
    (E002 : N003 → N006)
    (E003 : N005 → N004 → N007)
    (E004 : N005 → N008)
    (E005 : N001 → N002 → N005 → N007 → N009)
    (E006 : N005 → N009 → N008 → N010)
    (E007 : N010 → N011)
    (E008 : N005 → N006 → N011 → N012)
    (E009 : N001 → N005 → N012 → N013)
    (E010 : N005 → N006 → N013 → N014)
    : N014 := by
  have H_N005 : N005 := E001 B001
  have H_N006 : N006 := E002 B003
  have H_N007 : N007 := E003 H_N005 B004
  have H_N008 : N008 := E004 H_N005
  have H_N009 : N009 := E005 B001 B002 H_N005 H_N007
  have H_N010 : N010 := E006 H_N005 H_N009 H_N008
  have H_N011 : N011 := E007 H_N010
  have H_N012 : N012 := E008 H_N005 H_N006 H_N011
  have H_N013 : N013 := E009 B001 H_N005 H_N012
  have H_N014 : N014 := E010 H_N005 H_N006 H_N013
  exact H_N014

end TopologyCertificate_p3019_laurent_circulant_kernel
