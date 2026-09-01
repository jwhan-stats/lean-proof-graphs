import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p3184_levykhintchine_increment_bound
-- topology_sha256: 23545fecef4f1ff04645c5d928169ac23e01358909956c9b1a0cd1de6e02c090
namespace TopologyCertificate_p3184_levykhintchine_increment_bound

-- N001 = hσ2: 0 ≤ σ2
-- N002 = hΔ: 0 ≤ Δ
-- N003 = hn2: MeasureTheory.Integrable (fun x => x ^ 2 * ↑(n x)) MeasureTheory.volume
-- N004 = goal: (∀ (u : ℝ), ‖(fun u => Complex.exp (↑Δ * (Complex.I * ↑u * ↑b - ↑σ2 * ↑u ^ 2 / 2 + ∫ (x : ℝ), (Complex.exp (Complex.I * ↑u * ↑x) - 1 - Complex.I * ↑u * ↑x) * ↑↑(n x)))) u - 1‖ ≤ Δ * |u| * ((fun u => |b| + ∫ (v : ℝ) in Set.Icc (min 0 u) (max 0 u), ‖(fun v => ∫ (x : ℝ), Complex.exp (Complex.I * ↑v * ↑x) * (fun x => ↑(x ^ 2 * ↑(n x))) x) v‖) u + σ2 * |u|)) ∧ (MeasureTheory.Integrable (fun v => ∫ (x : ℝ), Complex.exp (Complex.I * ↑v * ↑x) * (fun x => ↑(x ^ 2 * ↑(n x))) x) MeasureTheory.volume → ∀ (u : ℝ), ‖(fun u => Complex.exp (↑Δ * (Complex.I * ↑u * ↑b - ↑σ2 * ↑u ^ 2 / 2 + ∫ (x : ℝ), (Complex.exp (Complex.I * ↑u * ↑x) - 1 - Complex.I * ↑u * ↑x) * ↑↑(n x)))) u - 1‖ ≤ Δ * |u| * ((|b| + ∫ (v : ℝ), ‖(fun v => ∫ (x : ℝ), Complex.exp (Complex.I * ↑v * ↑x) * (fun x => ↑(x ^ 2 * ↑(n x))) x) v‖) + σ2 * |u|))

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N001 → N002 → N003 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B001 B002 B003
  exact H_N004

end TopologyCertificate_p3184_levykhintchine_increment_bound
