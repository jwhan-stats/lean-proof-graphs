import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p2697_finite_field_normalized_one_cocycle_iff
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 4688cecc6caa9aaae7cb3c31292c9b97c22cc81698adb4908adfe5a123c9c151
-- reconstructed_proof_sha256: b5feb0fdc31683c5668e76b00cb56480ece0411b4737e50b6452e14f0ba7512b
-- selected_edge_count: 1

/- verified submission -/
theorem finite_field_normalized_one_cocycle_iff
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≡ 1 [MOD q])
    (ν : (ZMod p)ˣ) (hν : orderOf ν = q)
    (α : ZMod q → GaloisField p 2) (hα : α ≠ 0) :
    (α 0 = 0 ∧
      ∀ x y : ZMod q,
        α (x + y) =
          α x + (algebraMap (ZMod p) (GaloisField p 2) (ν : ZMod p)) ^ x.val * α y) ↔
      ∃ r : GaloisField p 2, r ≠ 0 ∧ α 0 = 0 ∧
        ∀ x : ZMod q, x ≠ 0 →
          α x = r * ∑ j ∈ Finset.range x.val,
            (algebraMap (ZMod p) (GaloisField p 2) (ν : ZMod p)) ^ j := by
  classical
  let t : GaloisField p 2 := algebraMap (ZMod p) (GaloisField p 2) (ν : ZMod p)
  let S : ℕ → GaloisField p 2 := fun n => ∑ j ∈ Finset.range n, t ^ j
  constructor
  · intro h
    rcases h with ⟨h0, hcoc⟩
    have hform_nat : ∀ n : ℕ, n ≤ q → α (n : ZMod q) = α 1 * S n := by
      intro n
      induction n with
      | zero =>
          intro hn
          simp [S, h0]
      | succ n ih =>
          intro hn
          have hnq : n < q := Nat.lt_of_succ_le hn
          have ih' : α (n : ZMod q) = α 1 * S n := ih (Nat.le_of_lt hnq)
          calc
            α ((n + 1 : ℕ) : ZMod q) = α ((n : ZMod q) + 1) := by
              norm_num
            _ = α (n : ZMod q) + t ^ ((n : ZMod q).val) * α 1 := hcoc (n : ZMod q) 1
            _ = α 1 * S n + t ^ n * α 1 := by
              rw [ZMod.val_cast_of_lt hnq, ih']
            _ = α 1 * S (n + 1) := by
              simp [S, Finset.sum_range_succ]
              ring
    have hform : ∀ x : ZMod q, α x = α 1 * S x.val := by
      intro x
      have hx := hform_nat x.val (Nat.le_of_lt (ZMod.val_lt x))
      rwa [ZMod.natCast_zmod_val x] at hx
    refine ⟨α 1, ?_, h0, ?_⟩
    · by_contra hr
      apply hα
      funext x
      have hx := hform x
      rw [hr] at hx
      simpa using hx
    · intro x hx
      simpa [S] using hform x
  · intro h
    rcases h with ⟨r, hr, h0, hformne⟩
    have htpow : t ^ q = 1 := by
      have hνpow : (ν : ZMod p) ^ q = 1 := by
        have hu : ν ^ q = 1 := by
          rw [← hν]
          exact pow_orderOf_eq_one ν
        exact congrArg Units.val hu
      calc
        t ^ q = algebraMap (ZMod p) (GaloisField p 2) ((ν : ZMod p) ^ q) := by
          simp [t, map_pow]
        _ = 1 := by
          rw [hνpow]
          simp
    have htne : t ≠ 1 := by
      intro ht
      have hmap : algebraMap (ZMod p) (GaloisField p 2) (ν : ZMod p) =
          algebraMap (ZMod p) (GaloisField p 2) 1 := by
        simpa [t] using ht
      have hcoerce : (ν : ZMod p) = 1 :=
        (RingHom.injective (algebraMap (ZMod p) (GaloisField p 2))) hmap
      have hunit : ν = 1 := Units.ext hcoerce
      have hqeq : q = 1 := by
        rw [← hν, hunit]
        exact orderOf_one
      exact (Fact.out : Nat.Prime q).ne_one hqeq
    have hqsum : S q = 0 := by
      have hg := geom_sum_eq (x := t) htne q
      rw [htpow] at hg
      simpa [S] using hg
    have hsplit : ∀ m n : ℕ, S (m+n) = S m + t^m * S n := by
      intro m n
      dsimp [S]
      rw [Finset.sum_range_add]
      rw [Finset.mul_sum]
      apply congrArg ((∑ j ∈ Finset.range m, t ^ j) + ·)
      apply Finset.sum_congr rfl
      intro z hz
      rw [pow_add]
    have hgeom : ∀ x y : ZMod q,
        S (x+y).val = S x.val + t ^ x.val * S y.val := by
      intro x y
      by_cases hover : q ≤ x.val + y.val
      · have hval : (x + y).val = x.val + y.val - q := ZMod.val_add_of_le hover
        have hdecomp : x.val + y.val = q + (x + y).val := by
          rw [hval]
          omega
        calc
          S (x+y).val = S (q + (x+y).val) := by
            rw [hsplit q (x+y).val, hqsum, htpow]
            simp
          _ = S (x.val + y.val) := by
            rw [← hdecomp]
          _ = S x.val + t ^ x.val * S y.val := hsplit x.val y.val
      · have hlt : x.val + y.val < q := Nat.lt_of_not_ge hover
        have hval : (x+y).val = x.val+y.val := by
          rw [ZMod.val_add, Nat.mod_eq_of_lt hlt]
        rw [hval]
        exact hsplit x.val y.val
    have hall : ∀ z : ZMod q, α z = r * S z.val := by
      intro z
      by_cases hz : z = 0
      · rw [hz, h0]
        simp [S]
      · simpa [S] using hformne z hz
    constructor
    · exact h0
    · intro x y
      calc
        α (x+y) = r * S (x+y).val := hall (x+y)
        _ = r * (S x.val + t ^ x.val * S y.val) := by
          rw [hgeom x y]
        _ = α x + t ^ x.val * α y := by
          rw [hall x, hall y]
          ring


#check_dependency_graph "finite_field_normalized_one_cocycle_iff" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(α 0 = 0 ∧ ∀ (x y : ZMod q), α (x + y) = α x + (algebraMap (ZMod p) (GaloisField p 2)) ↑ν ^ x.val * α y) ↔ ∃ r, r ≠ 0 ∧ α 0 = 0 ∧ ∀ (x : ZMod q), x ≠ 0 → α x = r * ∑ j ∈ Finset.range x.val, (algebraMap (ZMod p) (GaloisField p 2)) ↑ν ^ j\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"Fact (Nat.Prime p)\"},{\"name\":\"<generated-instance>\",\"statement\":\"Fact (Nat.Prime q)\"},{\"name\":\"hν\",\"statement\":\"orderOf ν = q\"},{\"name\":\"hα\",\"statement\":\"α ≠ 0\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2697_finite_field_normalized_one_cocycle_iff\",\"reconstructedProofSha256\":\"b5feb0fdc31683c5668e76b00cb56480ece0411b4737e50b6452e14f0ba7512b\",\"selectedEdgeCount\":1,\"theoremName\":\"finite_field_normalized_one_cocycle_iff\",\"topologySha256\":\"4688cecc6caa9aaae7cb3c31292c9b97c22cc81698adb4908adfe5a123c9c151\"}"
