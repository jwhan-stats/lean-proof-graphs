import Init

/- Generated dependency-topology certificate.
Semantic edge witnesses are kernel-checked in the reconstructed proof;
this theorem independently checks composition of the selected closure. -/
-- graph_id: p2109_stable_equivalence_empty_subfield_points_i
-- topology_sha256: 83c1f3429a819d27d51092c231154faa95c7febde4ce81a49b36cda28c209492
namespace TopologyCertificate_p2109_stable_equivalence_empty_subfield_points_i

-- N001 = hstable: Relation.EqvGen (fun X Y => (∃ k d S T, X = ⟨k, S⟩ ∧ Y = ⟨k + d, T⟩ ∧ ∃ r s φ ψ, (∀ v ∈ S, ∃ v', Fin.append v v' ∈ T) ∧ ∀ (v : Fin k → ℝ) (v' : Fin d → ℝ), Fin.append v v' ∈ T ↔ v ∈ S ∧ (∀ (i : Fin r), ∑ j, MvPolynomial.eval₂ (Int.castRingHom ℝ) v (φ i j) * v' j > 0) ∧ ∀ (i : Fin s), ∑ j, MvPolynomial.eval₂ (Int.castRingHom ℝ) v (ψ i j) * v' j = 0) ∨ ∃ k l S T, X = ⟨k, S⟩ ∧ Y = ⟨l, T⟩ ∧ ∃ h, (∀ (i : Fin l), ∃ p q, ∀ (v : ↑S), MvPolynomial.eval₂ (Rat.castHom ℝ) (↑v) q ≠ 0 ∧ ↑(h v) i = MvPolynomial.eval₂ (Rat.castHom ℝ) (↑v) p / MvPolynomial.eval₂ (Rat.castHom ℝ) (↑v) q) ∧ ∀ (i : Fin k), ∃ p q, ∀ (w : ↑T), MvPolynomial.eval₂ (Rat.castHom ℝ) (↑w) q ≠ 0 ∧ ↑(h.symm w) i = MvPolynomial.eval₂ (Rat.castHom ℝ) (↑w) p / MvPolynomial.eval₂ (Rat.castHom ℝ) (↑w) q) ⟨n, V⟩ ⟨m, W⟩
-- N002 = hpoints: Rollout_p2109_stable_equivalence_empty_subfield_points_i.HasSubfieldPoint A ⟨n, V⟩ ↔ Rollout_p2109_stable_equivalence_empty_subfield_points_i.HasSubfieldPoint A ⟨m, W⟩
-- N003 = goal: (¬∃ v, (fun i => ↑(v i)) ∈ V) ↔ ¬∃ w, (fun i => ↑(w i)) ∈ W

-- E001 represents h_001_hpoints
-- E002 represents h_goal

theorem graph_derives_goal
    (N001 : Prop)
    (N002 : Prop)
    (N003 : Prop)
    (B001 : N001)
    (E001 : N001 → N002)
    (E002 : N002 → N003)
    : N003 := by
  have H_N002 : N002 := E001 B001
  have H_N003 : N003 := E002 H_N002
  exact H_N003

end TopologyCertificate_p2109_stable_equivalence_empty_subfield_points_i
