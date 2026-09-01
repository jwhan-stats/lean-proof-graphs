import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1918_correspondence_of_induced_probability_assi
-- topology_sha256: 904ffa87e9965ebbd17e6fd553aa5ec27a654b9b759f39bd4bd300ddc3f04112
namespace TopologyCertificate_p1918_correspondence_of_induced_probability_assi

-- N001 = hPconj: ∀ (φ ψ : Formula), P (conj φ ψ) = P φ ∩ P ψ
-- N002 = hPneg: ∀ (φ : Formula), P (neg φ) = N φ
-- N003 = inst._@.proofs.4233523538._hygCtx._hyg.23: MeasureTheory.IsProbabilityMeasure μ
-- N004 = goal: T41 q = p ∧ T14 p = q

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (N004 : Prop)
    (B001 : N001)
    (B002 : N002)
    (B003 : N003)
    (E001 : N003 → N002 → N001 → N004)
    : N004 := by
  have H_N004 : N004 := E001 B003 B002 B001
  exact H_N004

end TopologyCertificate_p1918_correspondence_of_induced_probability_assi
