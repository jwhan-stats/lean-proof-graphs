import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p0130_affinesemigroup_normal_equiv
-- topology_sha256: b6e0b51344ee410e1677d05af1a57204e4ffb055c0a46ace81c966c822d992e2
namespace TopologyCertificate_p0130_affinesemigroup_normal_equiv

-- N001 = haLI: LinearIndependent ℝ fun i j => ↑(a i j)
-- N002 = haS: ∀ (i : Fin d), a i ∈ S
-- N003 = hcone: ∀ (x : Fin d → ℝ), x ∈ ConvexCone.hull ℝ ((fun u j => ↑(u j)) '' ↑S) ↔ ∃ c, (∀ (i : Fin d), 0 ≤ c i) ∧ x = ∑ i, c i • fun j => ↑(a i j)
-- N004 = hd: 1 ≤ d
-- N005 = goal: let natToInt := fun u j => ↑(u j); let natToReal := fun u j => ↑(u j); let intToReal := fun u j => ↑(u j); let C := {x | ∃ c, (∀ (i : Fin d), 0 ≤ c i) ∧ x = ∑ i, c i • fun j => ↑(a i j)}; let relintC := {x | ∃ c, (∀ (i : Fin d), 0 < c i) ∧ x = ∑ i, c i • fun j => ↑(a i j)}; let fundamentalParallelepiped := {x | ∃ c, (∀ (i : Fin d), 0 ≤ c i ∧ c i < 1) ∧ x = ∑ i, c i • fun j => ↑(a i j)}; let apery := {w | w ∈ S ∧ ∀ (i : Fin d), ¬∃ s ∈ S, w = s + a i}; let leS := fun u v => ∃ s ∈ S, v = u + s; let maximalApery := fun m => m ∈ apery ∧ ∀ w ∈ apery, leS m w → leS w m; let QF := {f | ∃ m, maximalApery m ∧ f = natToInt m - ∑ i, natToInt (a i)}; let G := {z | ∃ u ∈ S, ∃ v ∈ S, z = natToInt u - natToInt v}; let normal := natToInt '' ↑S = G ∩ {z | intToReal z ∈ C}; let condition2 := ∀ f ∈ QF, -f ∈ natToInt '' ↑S ∧ intToReal (-f) ∈ relintC; let condition3 := ∀ f ∈ QF, intToReal (-f) ∈ relintC; let condition4 := ∀ w ∈ apery, natToReal w ∈ fundamentalParallelepiped; (normal ↔ condition2) ∧ (normal ↔ condition3) ∧ (normal ↔ condition4)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (N005 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (B004 : N004)
    (E001 : N004 → N002 → N001 → N003 → N005)
    : N005 := by
  have H_N005 : N005 := E001 B004 B002 B001 B003
  exact H_N005

end TopologyCertificate_p0130_affinesemigroup_normal_equiv
