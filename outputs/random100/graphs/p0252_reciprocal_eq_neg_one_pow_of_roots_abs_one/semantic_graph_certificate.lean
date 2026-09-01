import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p0252_reciprocal_eq_neg_one_pow_of_roots_abs_one
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 8135949077b0fb96d1c6fae3bccdb4227c53b9d315b1129708d80ccc0e0481f7
-- reconstructed_proof_sha256: c8d0557b1bfb53b4360e1a89f409935e1a246e1f3fbfe327c0b3d3346182f3f2
-- selected_edge_count: 2

/- accepted add_to_file helper 1 -/

open Polynomial

lemma reverse_quadratic_unit (a : ℝ) :
    (X ^ 2 - C (2 * a) * X + C (1 : ℝ)).reverse =
      X ^ 2 - C (2 * a) * X + C (1 : ℝ) := by
  let q : Polynomial ℝ := X ^ 2 - C (2 * a) * X + C (1 : ℝ)
  have hdeg : q.natDegree = 2 := by
    dsimp [q]
    compute_degree!
  change q.reverse = q
  ext k
  rw [Polynomial.coeff_reverse, hdeg]
  by_cases hk : k ≤ 2
  · interval_cases k <;> simp [Polynomial.revAt_le, q, Polynomial.coeff_one]
  · have hkgt : 2 < k := Nat.lt_of_not_ge hk
    have hzero : q.coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      simpa [hdeg] using hkgt
    simp [Polynomial.revAt_eq_self_of_lt hkgt, hzero]

lemma reverse_X_sub_C_neg_one :
    (X - C (-1 : ℝ)).reverse = X - C (-1 : ℝ) := by
  let q : Polynomial ℝ := X - C (-1 : ℝ)
  have hdeg : q.natDegree = 1 := by
    dsimp [q]
    compute_degree!
  change q.reverse = q
  ext k
  rw [Polynomial.coeff_reverse, hdeg]
  by_cases hk : k ≤ 1
  · interval_cases k <;> simp [Polynomial.revAt_le, q, Polynomial.coeff_one]
  · have hkgt : 1 < k := Nat.lt_of_not_ge hk
    have hzero : q.coeff k = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      simpa [hdeg] using hkgt
    simp [Polynomial.revAt_eq_self_of_lt hkgt, hzero]

lemma reverse_X_sub_C_one_pow (n : ℕ) :
    ((X - C (1 : ℝ)) ^ n).reverse = ((-1 : ℝ) ^ n) • (X - C (1 : ℝ)) ^ n := by
  let A : Polynomial ℝ := X - C (1 : ℝ)
  have hbase : A.reverse = C (-1 : ℝ) * A := by
    have hdeg : A.natDegree = 1 := by
      dsimp [A]
      compute_degree!
    ext k
    rw [Polynomial.coeff_reverse, hdeg]
    by_cases hk : k ≤ 1
    · interval_cases k <;> simp [Polynomial.revAt_le, A, Polynomial.coeff_one]
    · have hkgt : 1 < k := Nat.lt_of_not_ge hk
      have hzero : A.coeff k = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        simpa [hdeg] using hkgt
      simp [Polynomial.revAt_eq_self_of_lt hkgt, hzero]
  have hrevpow : (A ^ n).reverse = A.reverse ^ n := by
    induction n with
    | zero =>
        change (C (1 : ℝ)).reverse = (C (1 : ℝ)) ^ 0
        rw [Polynomial.reverse_C]
        simp
    | succ n ih =>
        rw [pow_succ, Polynomial.reverse_mul_of_domain, ih, pow_succ]
  change (A ^ n).reverse = ((-1 : ℝ) ^ n) • A ^ n
  rw [hrevpow, hbase, mul_pow, ← map_pow, ← Polynomial.smul_eq_C_mul]

/- accepted add_to_file helper 2 -/
lemma isRoot_real_of_map_isRoot_of_im_eq_zero
    (f : Polynomial ℝ) {z : ℂ} (him : z.im = 0)
    (hz : (f.map (algebraMap ℝ ℂ)).IsRoot z) : f.IsRoot z.re := by
  let r := z.re
  have hzr : z = (r : ℂ) := by
    apply Complex.ext <;> simp [r, him]
  have hrootmap : (f.map (algebraMap ℝ ℂ)).IsRoot (r : ℂ) := by
    simpa [hzr] using hz
  rw [Polynomial.IsRoot.def, Polynomial.eval_map] at hrootmap
  have heval₂ := Polynomial.eval₂_at_apply (algebraMap ℝ ℂ) r (p := f)
  have hmapzero : algebraMap ℝ ℂ (f.eval r) = 0 := by
    rw [show algebraMap ℝ ℂ r = (r : ℂ) by rfl] at heval₂
    exact heval₂ ▸ hrootmap
  rw [Polynomial.IsRoot.def]
  exact (RingHom.injective (algebraMap ℝ ℂ)) hmapzero

lemma aeval_eq_zero_of_map_isRoot
    (f : Polynomial ℝ) {z : ℂ}
    (hz : (f.map (algebraMap ℝ ℂ)).IsRoot z) :
    (Polynomial.aeval z) f = 0 := by
  rw [Polynomial.IsRoot.def, Polynomial.eval_map] at hz
  rw [Polynomial.aeval_def]
  exact hz

/- accepted add_to_file helper 3 -/
lemma reverse_eq_self_of_roots_norm_one_of_not_root_one
    (f : Polynomial ℝ) (hf : f ≠ 0)
    (hroots : ∀ z : ℂ, (f.map (algebraMap ℝ ℂ)).IsRoot z → ‖z‖ = 1)
    (h1 : ¬ f.IsRoot 1) :
    f.reverse = f := by
  let P : ℕ → Prop := fun n =>
    ∀ g : Polynomial ℝ, g.natDegree = n → g ≠ 0 →
      (∀ z : ℂ, (g.map (algebraMap ℝ ℂ)).IsRoot z → ‖z‖ = 1) →
      ¬ g.IsRoot 1 → g.reverse = g
  have H : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro g hdeg hg0 hgroots hg1
        by_cases hconst : g.natDegree = 0
        · rw [Polynomial.eq_C_of_natDegree_eq_zero hconst, Polynomial.reverse_C]
        · have hFdeg : (g.map (algebraMap ℝ ℂ)).degree ≠ 0 := by
            rw [Polynomial.degree_map, Polynomial.degree_eq_natDegree hg0]
            exact_mod_cast hconst
          obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hFdeg
          have hzn : ‖z‖ = 1 := hgroots z hz
          by_cases him : z.im = 0
          · have hrroot : g.IsRoot z.re :=
              isRoot_real_of_map_isRoot_of_im_eq_zero g him hz
            have habs : |z.re| = 1 := by
              have hzr : z = (z.re : ℂ) := by
                apply Complex.ext <;> simp [him]
              rw [hzr] at hzn
              simpa using hzn
            have hrneg : z.re = -1 := by
              rcases eq_or_eq_neg_of_abs_eq habs with hr | hr
              · exfalso
                exact hg1 (by rwa [hr] at hrroot)
              · exact hr
            have hdvd : X - C (-1 : ℝ) ∣ g := by
              rw [Polynomial.dvd_iff_isRoot]
              simpa [hrneg] using hrroot
            rcases hdvd with ⟨h, gh⟩
            have hh0 : h ≠ 0 := by
              intro hh
              apply hg0
              rw [gh, hh, mul_zero]
            have hroots_h : ∀ w : ℂ, (h.map (algebraMap ℝ ℂ)).IsRoot w → ‖w‖ = 1 := by
              intro w hw
              have hgw : (g.map (algebraMap ℝ ℂ)).IsRoot w := by
                rw [gh, Polynomial.map_mul]
                exact Polynomial.root_mul.2 (Or.inr hw)
              exact hgroots w hgw
            have h1_h : ¬ h.IsRoot 1 := by
              intro hh
              have hrootg : g.IsRoot 1 := by
                rw [gh]
                exact Polynomial.root_mul.2 (Or.inr hh)
              exact hg1 hrootg
            have hq0 : X - C (-1 : ℝ) ≠ 0 := (Polynomial.monic_X_sub_C _).ne_zero
            have hdegmul : g.natDegree = (X - C (-1 : ℝ)).natDegree + h.natDegree := by
              rw [gh, Polynomial.natDegree_mul hq0 hh0]
            have hqdeg : (X - C (-1 : ℝ)).natDegree = 1 := by
              compute_degree!
            have hhlt : h.natDegree < n := by
              rw [← hdeg, hdegmul, hqdeg]
              omega
            have hhrev : h.reverse = h :=
              ih h.natDegree hhlt h rfl hh0 hroots_h h1_h
            rw [gh, Polynomial.reverse_mul_of_domain, reverse_X_sub_C_neg_one, hhrev]
          · have haeval : (Polynomial.aeval z) g = 0 :=
              aeval_eq_zero_of_map_isRoot g hz
            have hdvd : X ^ 2 - C (2 * z.re) * X + C (1 : ℝ) ∣ g := by
              have h := Polynomial.quadratic_dvd_of_aeval_eq_zero_im_ne_zero g haeval him
              have hnormsq : ‖z‖ ^ 2 = (1 : ℝ) := by
                rw [hzn]
                norm_num
              simpa [hnormsq] using h
            rcases hdvd with ⟨h, gh⟩
            have hh0 : h ≠ 0 := by
              intro hh
              apply hg0
              rw [gh, hh, mul_zero]
            have hroots_h : ∀ w : ℂ, (h.map (algebraMap ℝ ℂ)).IsRoot w → ‖w‖ = 1 := by
              intro w hw
              have hgw : (g.map (algebraMap ℝ ℂ)).IsRoot w := by
                rw [gh, Polynomial.map_mul]
                exact Polynomial.root_mul.2 (Or.inr hw)
              exact hgroots w hgw
            have h1_h : ¬ h.IsRoot 1 := by
              intro hh
              have hrootg : g.IsRoot 1 := by
                rw [gh]
                exact Polynomial.root_mul.2 (Or.inr hh)
              exact hg1 hrootg
            have hq0 : X ^ 2 - C (2 * z.re) * X + C (1 : ℝ) ≠ 0 := by
              have hdegq : (X ^ 2 - C (2 * z.re) * X + C (1 : ℝ)).natDegree = 2 := by
                compute_degree!
              intro hq
              rw [hq] at hdegq
              norm_num at hdegq
            have hdegmul : g.natDegree =
                (X ^ 2 - C (2 * z.re) * X + C (1 : ℝ)).natDegree + h.natDegree := by
              rw [gh, Polynomial.natDegree_mul hq0 hh0]
            have hqdeg : (X ^ 2 - C (2 * z.re) * X + C (1 : ℝ)).natDegree = 2 := by
              compute_degree!
            have hhlt : h.natDegree < n := by
              rw [← hdeg, hdegmul, hqdeg]
              omega
            have hhrev : h.reverse = h :=
              ih h.natDegree hhlt h rfl hh0 hroots_h h1_h
            rw [gh, Polynomial.reverse_mul_of_domain, reverse_quadratic_unit, hhrev]
  exact H f.natDegree f rfl hf hroots h1

/- verified submission -/
theorem reciprocal_eq_neg_one_pow_of_roots_abs_one
    (f : Polynomial ℝ) (n : ℕ) (hf : f ≠ 0)
    (hroots : ∀ z : ℂ, (f.map (algebraMap ℝ ℂ)).IsRoot z → ‖z‖ = 1)
    (hn : f.rootMultiplicity 1 = n) :
    f.reverse = ((-1 : ℝ) ^ n) • f := by
  let A : Polynomial ℝ := X - C (1 : ℝ)
  have hdvd : A ^ n ∣ f := by
    have h := Polynomial.pow_rootMultiplicity_dvd f (1 : ℝ)
    rwa [hn] at h
  rcases hdvd with ⟨g, hfg⟩
  have hg0 : g ≠ 0 := by
    intro hg
    apply hf
    rw [hfg, hg, mul_zero]
  have hnotg : ¬ g.IsRoot 1 := by
    intro hgroot
    have hlin : A ∣ g := by
      rw [Polynomial.dvd_iff_isRoot]
      exact hgroot
    rcases hlin with ⟨h, gh⟩
    have hbig : A ^ (n + 1) ∣ f := by
      use h
      rw [hfg, gh]
      change A ^ n * (A * h) = A ^ (n + 1) * h
      rw [pow_succ]
      ring
    have hnot := Polynomial.pow_rootMultiplicity_not_dvd hf (1 : ℝ)
    rw [hn] at hnot
    exact hnot hbig
  have hgroots : ∀ z : ℂ, (g.map (algebraMap ℝ ℂ)).IsRoot z → ‖z‖ = 1 := by
    intro z hz
    have hrootf : (f.map (algebraMap ℝ ℂ)).IsRoot z := by
      rw [hfg, Polynomial.map_mul]
      exact Polynomial.root_mul.2 (Or.inr hz)
    exact hroots z hrootf
  have hgrev : g.reverse = g :=
    reverse_eq_self_of_roots_norm_one_of_not_root_one g hg0 hgroots hnotg
  rw [hfg, Polynomial.reverse_mul_of_domain, reverse_X_sub_C_one_pow, hgrev, smul_mul_assoc]


#check_dependency_graph "reciprocal_eq_neg_one_pow_of_roots_abs_one" against "{\"edges\":[{\"conclusion\":{\"name\":\"hdvd\",\"statement\":\"A ^ n ∣ f\"},\"graphEdgeId\":\"h_001_hdvd\",\"premises\":[{\"name\":\"hn\",\"statement\":\"Polynomial.rootMultiplicity 1 f = n\"}],\"rawEdgeId\":\"telescope_6\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"f.reverse = (-1) ^ n • f\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hf\",\"statement\":\"f ≠ 0\"},{\"name\":\"hroots\",\"statement\":\"∀ (z : ℂ), (Polynomial.map (algebraMap ℝ ℂ) f).IsRoot z → ‖z‖ = 1\"},{\"name\":\"hn\",\"statement\":\"Polynomial.rootMultiplicity 1 f = n\"},{\"name\":\"hdvd\",\"statement\":\"A ^ n ∣ f\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0252_reciprocal_eq_neg_one_pow_of_roots_abs_one\",\"reconstructedProofSha256\":\"c8d0557b1bfb53b4360e1a89f409935e1a246e1f3fbfe327c0b3d3346182f3f2\",\"selectedEdgeCount\":2,\"theoremName\":\"reciprocal_eq_neg_one_pow_of_roots_abs_one\",\"topologySha256\":\"8135949077b0fb96d1c6fae3bccdb4227c53b9d315b1129708d80ccc0e0481f7\"}"
