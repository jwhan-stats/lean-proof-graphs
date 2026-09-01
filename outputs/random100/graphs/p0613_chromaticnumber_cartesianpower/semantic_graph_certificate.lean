import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p0613_chromaticnumber_cartesianpower
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: ae22701a4b328287dc620e363fc049b384035cf483673f85fda6131a05a68d18
-- reconstructed_proof_sha256: bcb8d2e0bdd036b6d187d8e253efa05446de627f6eee43e128b9f5d64acce725
-- selected_edge_count: 6

/- verified submission -/
lemma cartesianPower_colorable_of_coloring {n k q : ℕ}
    (G : SimpleGraph (Fin n)) (C : G.Coloring (Fin q)) (hq : q ≠ 0) :
    (SimpleGraph.fromRel (fun x y : Fin k → Fin n =>
      ∃ i : Fin k, G.Adj (x i) (y i) ∧
        ∀ j : Fin k, j ≠ i → x j = y j)).Colorable q := by
  letI : NeZero q := ⟨hq⟩
  let H : SimpleGraph (Fin k → Fin n) :=
    SimpleGraph.fromRel (fun x y : Fin k → Fin n =>
      ∃ i : Fin k, G.Adj (x i) (y i) ∧
        ∀ j : Fin k, j ≠ i → x j = y j)
  let color : H.Coloring (Fin q) :=
    { toFun := fun x => ∑ j : Fin k, C (x j)
      map_rel' := by
        intro x y hxy
        rw [SimpleGraph.fromRel_adj] at hxy
        have hrel : ∃ i : Fin k, G.Adj (x i) (y i) ∧
            ∀ j : Fin k, j ≠ i → x j = y j := by
          rcases hxy with ⟨_, hxy | hxy⟩
          · exact hxy
          · rcases hxy with ⟨i, hi, hrest⟩
            exact ⟨i, hi.symm, fun j hj => (hrest j hj).symm⟩
        rcases hrel with ⟨i, hi, hrest⟩
        show (∑ j : Fin k, C (x j)) ≠ ∑ j : Fin k, C (y j)
        intro hsum
        have htail : (∑ j ∈ (Finset.univ : Finset (Fin k)).erase i, C (x j)) =
            ∑ j ∈ (Finset.univ : Finset (Fin k)).erase i, C (y j) := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hrest j (Finset.mem_erase.mp hj).1]
        rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin k))
              (fun j => C (x j)) (Finset.mem_univ i),
            ← Finset.sum_erase_add (Finset.univ : Finset (Fin k))
              (fun j => C (y j)) (Finset.mem_univ i),
            htail] at hsum
        exact C.valid hi (add_left_cancel hsum) }
  exact ⟨color⟩

lemma cartesianPower_chromaticNumber_lower {n k : ℕ} (hn : 0 < n) (hk : 1 ≤ k)
    (G : SimpleGraph (Fin n)) :
    G.chromaticNumber ≤
      (SimpleGraph.fromRel (fun x y : Fin k → Fin n =>
        ∃ i : Fin k, G.Adj (x i) (y i) ∧
          ∀ j : Fin k, j ≠ i → x j = y j)).chromaticNumber := by
  let p : Fin k := ⟨0, hk⟩
  let a : Fin n := ⟨0, hn⟩
  let H : SimpleGraph (Fin k → Fin n) :=
    SimpleGraph.fromRel (fun x y : Fin k → Fin n =>
      ∃ i : Fin k, G.Adj (x i) (y i) ∧
        ∀ j : Fin k, j ≠ i → x j = y j)
  let emb (v : Fin n) : Fin k → Fin n := fun j => if j = p then v else a
  let embed : G →g H :=
    { toFun := emb
      map_rel' := by
        intro v w hvw
        rw [SimpleGraph.fromRel_adj]
        constructor
        · intro h
          have hp := congrFun h p
          simp [emb] at hp
          exact hvw.ne hp
        · left
          refine ⟨p, ?_, ?_⟩
          · simpa [emb] using hvw
          · intro j hj
            simp [emb, hj] }
  exact SimpleGraph.chromaticNumber_mono_of_hom embed

theorem chromaticNumber_cartesianPower {n : ℕ} (hn : 0 < n)
    (G : SimpleGraph (Fin n)) :
    ∀ k : ℕ, 1 ≤ k →
      (SimpleGraph.fromRel (fun x y : Fin k → Fin n =>
        ∃ i : Fin k, G.Adj (x i) (y i) ∧
          ∀ j : Fin k, j ≠ i → x j = y j)).chromaticNumber =
        G.chromaticNumber := by
  intro k hk
  let q : ℕ := G.chromaticNumber.toNat
  have hcG : G.Colorable q := by
    simpa [q] using SimpleGraph.colorable_chromaticNumber_of_fintype G
  have hq : q ≠ 0 := by
    intro hq
    rw [hq] at hcG
    have hempty : IsEmpty (Fin n) := SimpleGraph.isEmpty_of_colorable_zero hcG
    exact IsEmpty.elim hempty ⟨0, hn⟩
  have hcolor : (SimpleGraph.fromRel (fun x y : Fin k → Fin n =>
      ∃ i : Fin k, G.Adj (x i) (y i) ∧
        ∀ j : Fin k, j ≠ i → x j = y j)).Colorable q := by
    rcases hcG with ⟨C⟩
    exact cartesianPower_colorable_of_coloring G C hq
  have htop : G.chromaticNumber ≠ ⊤ := by
    exact SimpleGraph.chromaticNumber_ne_top_iff_exists.mpr ⟨q, hcG⟩
  have upper : (SimpleGraph.fromRel (fun x y : Fin k → Fin n =>
      ∃ i : Fin k, G.Adj (x i) (y i) ∧
        ∀ j : Fin k, j ≠ i → x j = y j)).chromaticNumber ≤ G.chromaticNumber := by
    have hle := hcolor.chromaticNumber_le
    have hqeq : (q : ℕ∞) = G.chromaticNumber := by
      dsimp [q]
      exact ENat.coe_toNat htop
    rw [hqeq] at hle
    exact hle
  exact le_antisymm upper (cartesianPower_chromaticNumber_lower hn hk G)


#check_dependency_graph "chromaticNumber_cartesianPower" against "{\"edges\":[{\"conclusion\":{\"name\":\"hcG\",\"statement\":\"G.Colorable q\"},\"graphEdgeId\":\"h_001_hcg\",\"premises\":[],\"rawEdgeId\":\"telescope_6\"},{\"conclusion\":{\"name\":\"hq\",\"statement\":\"q ≠ 0\"},\"graphEdgeId\":\"h_002_hq\",\"premises\":[{\"name\":\"hn\",\"statement\":\"0 < n\"},{\"name\":\"hcG\",\"statement\":\"G.Colorable q\"}],\"rawEdgeId\":\"telescope_7\"},{\"conclusion\":{\"name\":\"htop\",\"statement\":\"G.chromaticNumber ≠ ⊤\"},\"graphEdgeId\":\"h_004_htop\",\"premises\":[{\"name\":\"hcG\",\"statement\":\"G.Colorable q\"}],\"rawEdgeId\":\"telescope_9\"},{\"conclusion\":{\"name\":\"hcolor\",\"statement\":\"(SimpleGraph.fromRel fun x y => ∃ i, G.Adj (x i) (y i) ∧ ∀ (j : Fin k), j ≠ i → x j = y j).Colorable q\"},\"graphEdgeId\":\"h_003_hcolor\",\"premises\":[{\"name\":\"hcG\",\"statement\":\"G.Colorable q\"},{\"name\":\"hq\",\"statement\":\"q ≠ 0\"}],\"rawEdgeId\":\"telescope_8\"},{\"conclusion\":{\"name\":\"upper\",\"statement\":\"(SimpleGraph.fromRel fun x y => ∃ i, G.Adj (x i) (y i) ∧ ∀ (j : Fin k), j ≠ i → x j = y j).chromaticNumber ≤ G.chromaticNumber\"},\"graphEdgeId\":\"h_005_upper\",\"premises\":[{\"name\":\"hcolor\",\"statement\":\"(SimpleGraph.fromRel fun x y => ∃ i, G.Adj (x i) (y i) ∧ ∀ (j : Fin k), j ≠ i → x j = y j).Colorable q\"},{\"name\":\"htop\",\"statement\":\"G.chromaticNumber ≠ ⊤\"}],\"rawEdgeId\":\"telescope_10\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(SimpleGraph.fromRel fun x y => ∃ i, G.Adj (x i) (y i) ∧ ∀ (j : Fin k), j ≠ i → x j = y j).chromaticNumber = G.chromaticNumber\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hn\",\"statement\":\"0 < n\"},{\"name\":\"hk\",\"statement\":\"1 ≤ k\"},{\"name\":\"upper\",\"statement\":\"(SimpleGraph.fromRel fun x y => ∃ i, G.Adj (x i) (y i) ∧ ∀ (j : Fin k), j ≠ i → x j = y j).chromaticNumber ≤ G.chromaticNumber\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0613_chromaticnumber_cartesianpower\",\"reconstructedProofSha256\":\"bcb8d2e0bdd036b6d187d8e253efa05446de627f6eee43e128b9f5d64acce725\",\"selectedEdgeCount\":6,\"theoremName\":\"chromaticNumber_cartesianPower\",\"topologySha256\":\"ae22701a4b328287dc620e363fc049b384035cf483673f85fda6131a05a68d18\"}"
