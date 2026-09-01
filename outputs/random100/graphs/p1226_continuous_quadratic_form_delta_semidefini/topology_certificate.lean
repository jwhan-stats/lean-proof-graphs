import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1226_continuous_quadratic_form_delta_semidefini
-- topology_sha256: fcee227336671d974a9daef65058f17ab415ea536aaf240335313305cad50f04
namespace TopologyCertificate_p1226_continuous_quadratic_form_delta_semidefini

-- N001 = hTq: ∀ (x : X), q x = (T x) x
-- N002 = hTsymm: ∀ (x y : X), (T x) y = (T y) x
-- N003 = inst._@.proofs.3283946215._hygCtx._hyg.12: CompleteSpace X
-- N004 = goal: ((∃ q₁ q₂, (∃ b₁, ∀ (x : X), q₁ x = (b₁ x) x) ∧ (∃ b₂, ∀ (x : X), q₂ x = (b₂ x) x) ∧ (∀ (x : X), 0 ≤ q₁ x) ∧ (∀ (x : X), 0 ≤ q₂ x) ∧ ∀ (x : X), q x = q₁ x - q₂ x) ↔ ∃ p, (∃ bp, ∀ (x : X), p x = (bp x) x) ∧ ∀ (x : X), |q x| ≤ p x) ∧ ((∃ p, (∃ bp, ∀ (x : X), p x = (bp x) x) ∧ ∀ (x : X), |q x| ≤ p x) ↔ ∃ H x x_1, ∃ (_ : CompleteSpace H), ∃ A B, T = B.comp A)

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N003 → N001 → N002 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B003 B001 B002
  exact H_N004

end TopologyCertificate_p1226_continuous_quadratic_form_delta_semidefini
