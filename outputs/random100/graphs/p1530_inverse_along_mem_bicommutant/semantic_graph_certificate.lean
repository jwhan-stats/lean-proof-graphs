import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1530_inverse_along_mem_bicommutant
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: b46fcaa3152d6c46b1095bf53141771c7e60801a5c82e999fd8954042fb790bd
-- reconstructed_proof_sha256: d0b7ac0bd21f6d7f9cc1eab953c262573b5c36f6ca7507ec968bf8b07254cd45
-- selected_edge_count: 1

/- verified submission -/
theorem inverse_along_mem_bicommutant {S : Type*} [Semigroup S] {a d b : S}
    (hbad : b * a * d = d) (hdab : d * a * b = d)
    (hbd : ∃ x y : S, b = d * x ∧ b = y * d) :
    ∀ c : S, c * a = a * c → c * d = d * c → c * b = b * c := by
  rcases hbd with ⟨x, y, hbx, hby⟩
  intro c hca hcd
  have hyad : y * d * a * d = d := by
    simpa [hby] using hbad
  have hdadx : d * a * d * x = d := by
    simpa [hbx, mul_assoc] using hdab
  calc
    c * b = d * c * x := by
      calc
        c * b = c * (d * x) := by rw [hbx]
        _ = c * d * x := by rw [mul_assoc]
        _ = d * c * x := by rw [hcd]
    _ = y * d * a * d * c * x := by
      rw [hyad]
    _ = y * d * a * c * d * x := by
      have h : y * d * a * (d * c) * x = y * d * a * (c * d) * x := by
        rw [hcd]
      simpa [mul_assoc] using h
    _ = y * d * c * a * d * x := by
      have h : y * d * (a * c) * d * x = y * d * (c * a) * d * x := by
        rw [← hca]
      simpa [mul_assoc] using h
    _ = y * c * d * a * d * x := by
      have h : y * (d * c) * a * d * x = y * (c * d) * a * d * x := by
        rw [hcd]
      simpa [mul_assoc] using h
    _ = y * c * d := by
      have h : y * c * (d * a * d * x) = y * c * d := by
        rw [hdadx]
      simpa [mul_assoc] using h
    _ = y * d * c := by
      rw [mul_assoc, hcd, ← mul_assoc]
    _ = b * c := by
      rw [← hby]


#check_dependency_graph "inverse_along_mem_bicommutant" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∀ (c : S), c * a = a * c → c * d = d * c → c * b = b * c\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hbad\",\"statement\":\"b * a * d = d\"},{\"name\":\"hdab\",\"statement\":\"d * a * b = d\"},{\"name\":\"hbd\",\"statement\":\"∃ x y, b = d * x ∧ b = y * d\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1530_inverse_along_mem_bicommutant\",\"reconstructedProofSha256\":\"d0b7ac0bd21f6d7f9cc1eab953c262573b5c36f6ca7507ec968bf8b07254cd45\",\"selectedEdgeCount\":1,\"theoremName\":\"inverse_along_mem_bicommutant\",\"topologySha256\":\"b46fcaa3152d6c46b1095bf53141771c7e60801a5c82e999fd8954042fb790bd\"}"
