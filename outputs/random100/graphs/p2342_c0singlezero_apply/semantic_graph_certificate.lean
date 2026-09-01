import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p2342_c0singlezero_apply
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 21795638089805f2200533f25659a7f89ca729fc135727d8148dab9b2ca30161
-- reconstructed_proof_sha256: 726dfca9dc47d67d031d5dd151cd70f9c0ed149aa4a716b805dca98fa931d81d
-- selected_edge_count: 1

/- verified submission -/
noncomputable def c0SingleZero {E : Type*} [TopologicalSpace E] [Zero E] (x : E) :
    ZeroAtInftyContinuousMap ℕ E where
  toFun n := if n = 0 then x else 0
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by
    apply HasCompactSupport.is_zero_at_infty
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_singleton (x := (0 : ℕ)))
    intro n hn
    by_cases h0 : n = 0
    · exact Set.mem_singleton_iff.mpr h0
    · exfalso
      exact hn (by simp [h0])

@[simp] theorem c0SingleZero_apply {E : Type*} [TopologicalSpace E] [Zero E] (x : E) (n : ℕ) :
    c0SingleZero x n = (if n = 0 then x else 0) := rfl

theorem no_implementing_star_hom
    {A : Type*} [CStarAlgebra A] [Nontrivial A]
    (α : A →⋆ₙₐ[ℂ] A)
    (hα : α 1 = 1)
    (hessential : ∀ a : A,
      (∀ x : (⊥ : NonUnitalStarSubalgebra ℂ A).comap α, a * (x : A) = 0) → a = 0) :
    let I := (⊥ : NonUnitalStarSubalgebra ℂ A).comap α
    letI : ContinuousStar I :=
      ⟨(continuous_star.comp continuous_subtype_val).subtype_mk _⟩
    let B := A × ZeroAtInftyContinuousMap ℕ I
    ¬ ∃ β : B →⋆ₙₐ[ℂ] B, ∀ b b' : B,
      (β b * b').1 = α b.1 * b'.1 ∧
      (↑((β b * b').2 0) : A) = α b.1 * ↑(b'.2 0) ∧
      ∀ n : ℕ, (↑((β b * b').2 (n + 1)) : A) =
        (↑(b.2 n) : A) * ↑(b'.2 (n + 1)) := by
  dsimp only
  intro h
  rcases h with ⟨β, hβ⟩
  letI : ContinuousStar ((⊥ : NonUnitalStarSubalgebra ℂ A).comap α) :=
    ⟨(continuous_star.comp continuous_subtype_val).subtype_mk _⟩
  let I := (⊥ : NonUnitalStarSubalgebra ℂ A).comap α
  let b0 : A × ZeroAtInftyContinuousMap ℕ I := (1, 0)
  let d : I := (β b0).2 0
  have hleft : ∀ x : I, ((d : A) * (x : A)) = (x : A) := by
    intro x
    let bx : A × ZeroAtInftyContinuousMap ℕ I := (0, c0SingleZero x)
    have hx := (hβ b0 bx).2.1
    simpa [b0, bx, d, hα] using hx
  have hd_eq : (d : A) = 1 := by
    have hzero : ∀ x : (⊥ : NonUnitalStarSubalgebra ℂ A).comap α,
        (((d : A) - 1) * (x : A)) = 0 := by
      intro x
      rw [sub_mul, one_mul, hleft x, sub_self]
    exact sub_eq_zero.mp (hessential ((d : A) - 1) hzero)
  have hdα : α (d : A) = 0 := by
    have hmem : α (d : A) ∈ (⊥ : NonUnitalStarSubalgebra ℂ A) :=
      (NonUnitalStarSubalgebra.mem_comap (⊥ : NonUnitalStarSubalgebra ℂ A) α (d : A)).mp d.property
    exact NonUnitalStarAlgebra.mem_bot.mp hmem
  have h10 : (1 : A) = 0 := by
    calc
      (1 : A) = α 1 := hα.symm
      _ = α (d : A) := by rw [hd_eq]
      _ = 0 := hdα
  exact one_ne_zero h10


#check_dependency_graph "c0SingleZero_apply" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"(Rollout_p2342_c0singlezero_apply.c0SingleZero x) n = (Rollout_p2342_c0singlezero_apply.c0SingleZero x) n\"},\"graphEdgeId\":\"h_goal\",\"premises\":[],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2342_c0singlezero_apply\",\"reconstructedProofSha256\":\"726dfca9dc47d67d031d5dd151cd70f9c0ed149aa4a716b805dca98fa931d81d\",\"selectedEdgeCount\":1,\"theoremName\":\"c0SingleZero_apply\",\"topologySha256\":\"21795638089805f2200533f25659a7f89ca729fc135727d8148dab9b2ca30161\"}"
