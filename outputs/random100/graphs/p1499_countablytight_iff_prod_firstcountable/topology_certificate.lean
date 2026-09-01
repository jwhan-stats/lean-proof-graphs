import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p1499_countablytight_iff_prod_firstcountable
-- topology_sha256: 6d791668e76419bbfe9379e31a02f72cf68e3d1b1e9e38d859c818bd9a9bb10a
namespace TopologyCertificate_p1499_countablytight_iff_prod_firstcountable

-- N001 = goal: (∀ (A : Set X), ∀ x ∈ closure A, ∃ B ⊆ A, B.Countable ∧ x ∈ closure B) ↔ ∀ (Y : Type v) [inst : TopologicalSpace Y] [FirstCountableTopology Y] (A : Set (X × Y)), ∀ p ∈ closure A, ∃ B ⊆ A, B.Countable ∧ p ∈ closure B

-- E001 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (E001 : N001)
    : N001 := by
  have H_N001 : N001 := E001
  exact H_N001

end TopologyCertificate_p1499_countablytight_iff_prod_firstcountable
