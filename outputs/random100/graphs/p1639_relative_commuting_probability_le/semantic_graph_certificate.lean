import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1639_relative_commuting_probability_le
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 238ee4d8a7cc5f36548c7db5590c508e76736bd9d1fa902a5b8e58d80fd2b1f5
-- reconstructed_proof_sha256: cb6c150eab58d9a70eca0d44089c03967e53e1c410f9bd5faf1089f338ed94a8
-- selected_edge_count: 8

/- accepted add_to_file helper 1 -/
open scoped BigOperators

lemma natCard_commute_pairs_eq_sum {M : Type*} [Group M] [Fintype M] (L : Subgroup M) :
    Nat.card {p : L × M // Commute (p.1 : M) p.2} =
      ∑ x : M, Nat.card {l : L // Commute (l : M) x} := by
  classical
  let e : {p : L × M // Commute (p.1 : M) p.2} ≃
      (Σ x : M, {l : L // Commute (l : M) x}) :=
    { toFun := fun p => ⟨p.1.2, ⟨p.1.1, p.2⟩⟩
      invFun := fun q => ⟨⟨q.2.1, q.1⟩, q.2.2⟩
      left_inv := fun p => rfl
      right_inv := fun q => rfl }
  rw [Nat.card_eq_fintype_card, Fintype.card_congr e, Fintype.card_sigma]
  congr with x
  exact (Nat.card_eq_fintype_card (α := {l : L // Commute (l : M) x})).symm

lemma coset_centralizer_sum_le_commute_pairs
    {G : Type*} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] [Fintype N]
    (I : Subgroup N) [Fintype I] (x : G) :
    ∑ n : N, Nat.card {i : I // Commute ((i : N) : G) (x * (n : G))} ≤
      Nat.card {p : I × N // Commute (p.1 : N) p.2} := by
  classical
  let base : I → N := fun i =>
    if h : ∃ n : N, Commute ((i : N) : G) (x * (n : G)) then
      Classical.choose h
    else 1
  have hbase : ∀ (i : I) {n : N},
      Commute ((i : N) : G) (x * (n : G)) →
      Commute ((i : N) : G) (x * (base i : G)) := by
    intro i n hn
    dsimp [base]
    rw [dif_pos (show ∃ n : N, Commute ((i : N) : G) (x * (n : G)) from ⟨n, hn⟩)]
    exact Classical.choose_spec (show ∃ n : N, Commute ((i : N) : G) (x * (n : G)) from ⟨n, hn⟩)
  have conj_of_comm : ∀ (i : I) {n : N},
      Commute ((i : N) : G) (x * (n : G)) →
      (n : G) * ((i : N) : G) =
        x⁻¹ * ((i : N) : G) * x * (n : G) := by
    intro i n hn
    calc
      (n : G) * ((i : N) : G) = x⁻¹ * ((x * (n : G)) * ((i : N) : G)) := by group
      _ = x⁻¹ * (((i : N) : G) * (x * (n : G))) := by rw [hn.eq]
      _ = x⁻¹ * ((i : N) : G) * x * (n : G) := by group
  have commute_diff : ∀ (i : I) {n : N},
      Commute ((i : N) : G) (x * (n : G)) →
      Commute ((base i)⁻¹ * n : N) (i : N) := by
    intro i n hn
    have hb := hbase i hn
    have hnG := conj_of_comm i hn
    have hbG := conj_of_comm i hb
    have hbG' : (base i : G)⁻¹ * (x⁻¹ * ((i : N) : G) * x) =
        ((i : N) : G) * (base i : G)⁻¹ := by
      calc
        (base i : G)⁻¹ * (x⁻¹ * ((i : N) : G) * x)
            = (base i : G)⁻¹ *
                ((x⁻¹ * ((i : N) : G) * x) * (base i : G)) *
                (base i : G)⁻¹ := by group
        _ = (base i : G)⁻¹ * ((base i : G) * ((i : N) : G)) *
              (base i : G)⁻¹ := by rw [← hbG]
        _ = ((i : N) : G) * (base i : G)⁻¹ := by group
    have hdG : (((base i)⁻¹ * n : N) : G) * ((i : N) : G) =
        ((i : N) : G) * (((base i)⁻¹ * n : N) : G) := by
      calc
        (((base i)⁻¹ * n : N) : G) * ((i : N) : G)
            = (base i : G)⁻¹ * ((n : G) * ((i : N) : G)) := by
              simp; group
        _ = (base i : G)⁻¹ *
              (x⁻¹ * ((i : N) : G) * x * (n : G)) := by rw [hnG]
        _ = ((base i : G)⁻¹ * (x⁻¹ * ((i : N) : G) * x)) * (n : G) := by group
        _ = (((i : N) : G) * (base i : G)⁻¹) * (n : G) := by rw [hbG']
        _ = ((i : N) : G) * (((base i)⁻¹ * n : N) : G) := by
              simp; group
    show ((base i)⁻¹ * n : N) * (i : N) = (i : N) * ((base i)⁻¹ * n : N)
    exact Subtype.ext hdG
  let F : (Σ n : N, {i : I // Commute ((i : N) : G) (x * (n : G))}) →
      {p : I × N // Commute (p.1 : N) p.2} :=
    fun q => ⟨⟨q.2.1, (base q.2.1)⁻¹ * q.1⟩, (commute_diff q.2.1 q.2.2).symm⟩
  have hF : Function.Injective F := by
    intro a b hab
    rcases a with ⟨n, i, hi⟩
    rcases b with ⟨m, j, hj⟩
    have hp : ((i, (base i)⁻¹ * n) : I × N) =
        (j, (base j)⁻¹ * m) := congrArg Subtype.val hab
    have hij : i = j := congrArg Prod.fst hp
    subst j
    have hnm : n = m := mul_left_cancel (congrArg Prod.snd hp)
    subst m
    rfl
  calc
    ∑ n : N, Nat.card {i : I // Commute ((i : N) : G) (x * (n : G))}
        = Nat.card (Σ n : N, {i : I // Commute ((i : N) : G) (x * (n : G))}) := by
          rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
          congr with n
          exact Nat.card_eq_fintype_card (α := {i : I // Commute ((i : N) : G) (x * (n : G))})
    _ ≤ Nat.card {p : I × N // Commute (p.1 : N) p.2} := by
          rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
          exact Fintype.card_le_of_injective F hF

/- accepted add_to_file helper 2 -/
lemma centralizer_card_le_map_mul_comap
    {G Q : Type*} [Group G] [Group Q] [Fintype G] [Fintype Q]
    (f : G →* Q) (K : Subgroup G) [Fintype K]
    [Fintype (K.map f)] [Fintype (K.comap f.ker.subtype)] (x : G) :
    Nat.card {k : K // Commute (k : G) x} ≤
      Nat.card {u : K.map f // Commute (u : Q) (f x)} *
        Nat.card {i : K.comap f.ker.subtype // Commute ((i : f.ker) : G) x} := by
  classical
  let A := {k : K // Commute (k : G) x}
  let B := {u : K.map f // Commute (u : Q) (f x)}
  let I := {i : K.comap f.ker.subtype // Commute ((i : f.ker) : G) x}
  let im : A → B := fun a =>
    ⟨⟨f (a.1 : G), Subgroup.mem_map_of_mem f a.1.2⟩, a.2.map f⟩
  let base : B → A := fun b =>
    if h : ∃ a : A, im a = b then
      Classical.choose h
    else ⟨1, by simp⟩
  have hbase : ∀ (b : B), (∃ a : A, im a = b) →
      im (base b) = b ∧ Commute ((base b : K) : G) x := by
    intro b hb
    dsimp [base]
    rw [dif_pos hb]
    exact ⟨Classical.choose_spec hb, (Classical.choose hb).2⟩
  let dfun : A → f.ker := fun a =>
    ⟨(a.1 : G) * ((base (im a) : K) : G)⁻¹, by
      obtain ⟨him, _⟩ := hbase (im a) ⟨a, rfl⟩
      rw [MonoidHom.mem_ker]
      have himv : f ((base (im a) : K) : G) = f (a.1 : G) := by
        have := congrArg (fun z : B => (z.1 : Q)) him
        simpa [im] using this
      simp [map_mul, map_inv, himv]⟩
  let jfun : A → K.comap f.ker.subtype := fun a =>
    ⟨dfun a, by
      change ((dfun a : f.ker) : G) ∈ K
      dsimp [dfun]
      exact K.mul_mem a.1.2 (K.inv_mem (base (im a)).1.2)⟩
  let F : A → B × I := fun a =>
    ⟨im a, ⟨jfun a, by
      obtain ⟨_, hcomm⟩ := hbase (im a) ⟨a, rfl⟩
      exact a.2.mul_left ((hcomm.symm.inv_right).symm)⟩⟩
  have hF : Function.Injective F := by
    intro a b hab
    have him : im a = im b := congrArg Prod.fst hab
    have hbaseeq : base (im a) = base (im b) := congrArg base him
    have hival : jfun a = jfun b := by
      have := congrArg Subtype.val (congrArg Prod.snd hab)
      simpa [F] using this
    have hd : ((dfun a : f.ker) : G) = ((dfun b : f.ker) : G) := by
      have := congrArg (fun z : K.comap f.ker.subtype => ((z : f.ker) : G)) hival
      simpa [jfun] using this
    have hmul :
        (a.1 : G) * ((base (im a) : K) : G)⁻¹ =
          (b.1 : G) * ((base (im b) : K) : G)⁻¹ := by
      simpa [dfun] using hd
    have hG : (a.1 : G) = (b.1 : G) := by
      calc
        (a.1 : G) = ((a.1 : G) * ((base (im a) : K) : G)⁻¹) *
            ((base (im a) : K) : G) := by group
        _ = ((b.1 : G) * ((base (im b) : K) : G)⁻¹) *
              ((base (im a) : K) : G) := by rw [hmul]
        _ = ((b.1 : G) * ((base (im b) : K) : G)⁻¹) *
              ((base (im b) : K) : G) := by rw [hbaseeq]
        _ = (b.1 : G) := by group
    apply Subtype.ext
    exact Subtype.ext hG
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  calc
    Fintype.card A ≤ Fintype.card (B × I) := Fintype.card_le_of_injective F hF
    _ = Fintype.card B * Fintype.card I := Fintype.card_prod B I

/- accepted add_to_file helper 3 -/
lemma commute_pairs_card_le_quotient_mul_comap
    {G : Type*} [Group G] [Fintype G]
    (N K : Subgroup G) [N.Normal] [Fintype (G ⧸ N)] :
    let π : G →* G ⧸ N := QuotientGroup.mk' N
    let Kbar : Subgroup (G ⧸ N) := K.map π
    Nat.card {p : K × G // Commute (p.1 : G) p.2} ≤
      Nat.card {p : Kbar × (G ⧸ N) // Commute (p.1 : G ⧸ N) p.2} *
        Nat.card {p : (K.comap N.subtype) × N // Commute (p.1 : N) p.2} := by
  classical
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  let Kbar : Subgroup (G ⧸ N) := K.map π
  let I : Subgroup N := K.comap N.subtype
  let cA : G → ℕ := fun x => Nat.card {k : K // Commute (k : G) x}
  let cB : G ⧸ N → ℕ := fun q =>
    Nat.card {u : Kbar // Commute (u : G ⧸ N) q}
  let cI : G → ℕ := fun x =>
    Nat.card {i : I // Commute ((i : N) : G) x}
  have hpoint : ∀ x : G, cA x ≤ cB (π x) * cI x := by
    intro x
    have h := centralizer_card_le_map_mul_comap π K x
    rw [show π.ker = N by simp [π, QuotientGroup.ker_mk']] at h
    exact h
  let lift : G ⧸ N → G := fun q => Classical.choose (QuotientGroup.mk'_surjective N q)
  have hlift : ∀ q : G ⧸ N, π (lift q) = q :=
    fun q => Classical.choose_spec (QuotientGroup.mk'_surjective N q)
  let efib : ∀ q : G ⧸ N, {x : G // π x = q} ≃ N := fun q =>
    { toFun := fun x =>
        ⟨(lift q)⁻¹ * (x : G), by
          rw [← QuotientGroup.eq_one_iff (N := N)]
          change π ((lift q)⁻¹ * (x : G)) = 1
          simp [map_mul, map_inv, hlift q, x.property]⟩
      invFun := fun n =>
        ⟨lift q * (n : G), by
          simp [π, map_mul, hlift q]⟩
      left_inv := fun x => by
        apply Subtype.ext
        group
      right_inv := fun n => by
        apply Subtype.ext
        group }
  have hfiber_sum : ∀ q : G ⧸ N,
      (∑ z : {x : G // π x = q}, cI (z : G)) =
        ∑ n : N, cI (lift q * (n : G)) := by
    intro q
    exact (Fintype.sum_equiv (efib q).symm
      (fun n : N => cI (lift q * (n : G)))
      (fun z : {x : G // π x = q} => cI (z : G))
      (fun n => rfl)).symm
  have hcoset : ∀ q : G ⧸ N,
      (∑ z : {x : G // π x = q}, cI (z : G)) ≤
        Nat.card {p : I × N // Commute (p.1 : N) p.2} := by
    intro q
    rw [hfiber_sum q]
    exact coset_centralizer_sum_le_commute_pairs N I (lift q)
  calc
    Nat.card {p : K × G // Commute (p.1 : G) p.2}
        = ∑ x : G, cA x := natCard_commute_pairs_eq_sum K
    _ ≤ ∑ x : G, cB (π x) * cI x := by
          exact Finset.sum_le_sum (fun x _ => hpoint x)
    _ = ∑ q : G ⧸ N, ∑ z : {x : G // π x = q}, cB (π (z : G)) * cI (z : G) := by
          exact (Fintype.sum_fiberwise π (fun x : G => cB (π x) * cI x)).symm
    _ = ∑ q : G ⧸ N, ∑ z : {x : G // π x = q}, cB q * cI (z : G) := by
          congr with q
          congr with z
          rw [z.property]
    _ = ∑ q : G ⧸ N, cB q * (∑ z : {x : G // π x = q}, cI (z : G)) := by
          congr with q
          rw [Finset.mul_sum]
    _ ≤ ∑ q : G ⧸ N, cB q *
          Nat.card {p : I × N // Commute (p.1 : N) p.2} := by
          exact Finset.sum_le_sum (fun q _ => mul_le_mul_left' (hcoset q) (cB q))
    _ = (∑ q : G ⧸ N, cB q) *
          Nat.card {p : I × N // Commute (p.1 : N) p.2} := by
          rw [Finset.sum_mul]
    _ = Nat.card {p : Kbar × (G ⧸ N) // Commute (p.1 : G ⧸ N) p.2} *
          Nat.card {p : I × N // Commute (p.1 : N) p.2} := by
          rw [natCard_commute_pairs_eq_sum Kbar]

/- accepted add_to_file helper 4 -/
lemma card_comap_mul_card_map_quotient
    {G : Type*} [Group G]
    (N K : Subgroup G) [N.Normal] :
    let π : G →* G ⧸ N := QuotientGroup.mk' N
    Nat.card (K.comap N.subtype) * Nat.card (K.map π) = Nat.card K := by
  classical
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  let I : Subgroup N := K.comap N.subtype
  let J : Subgroup K := N.subgroupOf K
  have hrel : N.relIndex K = Nat.card (K.map π) := by
    have h := Subgroup.relIndex_ker K π
    rw [show π.ker = N by simp [π, QuotientGroup.ker_mk']] at h
    exact h
  have hIeq : Nat.card I = Nat.card J := by
    let e : I ≃ J :=
      { toFun := fun i => ⟨⟨(i.1 : G), i.2⟩, i.1.2⟩
        invFun := fun j => ⟨⟨(j.1 : G), j.2⟩, j.1.2⟩
        left_inv := fun i => rfl
        right_inv := fun j => rfl }
    exact Nat.card_congr e
  have hJ : Nat.card J * J.index = Nat.card K := Subgroup.card_mul_index J
  calc
    Nat.card I * Nat.card (K.map π) = Nat.card J * N.relIndex K := by
      rw [hIeq, hrel]
    _ = Nat.card J * J.index := rfl
    _ = Nat.card K := hJ

/- verified submission -/
theorem relative_commuting_probability_le
    {G : Type*} [Group G] [Finite G]
    (N K : Subgroup G) [N.Normal] :
    let π : G →* G ⧸ N := QuotientGroup.mk' N
    let Kbar : Subgroup (G ⧸ N) := K.map π
    (Nat.card {p : K × G // Commute (p.1 : G) p.2} : ℚ) /
        ((Nat.card K : ℚ) * (Nat.card G : ℚ)) ≤
      ((Nat.card {p : Kbar × (G ⧸ N) // Commute (p.1 : G ⧸ N) p.2} : ℚ) /
          ((Nat.card Kbar : ℚ) * (Nat.card (G ⧸ N) : ℚ))) *
        ((Nat.card {p : (K.comap N.subtype) × N // Commute (p.1 : N) p.2} : ℚ) /
          ((Nat.card (K.comap N.subtype) : ℚ) * (Nat.card N : ℚ))) := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype (G ⧸ N) := Fintype.ofFinite (G ⧸ N)
  let π : G →* G ⧸ N := QuotientGroup.mk' N
  let Kbar : Subgroup (G ⧸ N) := K.map π
  let I : Subgroup N := K.comap N.subtype
  let A : ℕ := Nat.card {p : K × G // Commute (p.1 : G) p.2}
  let B : ℕ := Nat.card {p : Kbar × (G ⧸ N) // Commute (p.1 : G ⧸ N) p.2}
  let C : ℕ := Nat.card {p : I × N // Commute (p.1 : N) p.2}
  have hnat : A ≤ B * C := by
    simpa [A, B, C, π, Kbar, I] using
      commute_pairs_card_le_quotient_mul_comap N K
  have hK : Nat.card I * Nat.card Kbar = Nat.card K := by
    simpa [I, Kbar, π] using card_comap_mul_card_map_quotient N K
  have hG : Nat.card (G ⧸ N) * Nat.card N = Nat.card G :=
    (Subgroup.card_eq_card_quotient_mul_card_subgroup N).symm
  have hden : (Nat.card K : ℚ) * (Nat.card G : ℚ) =
      ((Nat.card Kbar : ℚ) * (Nat.card (G ⧸ N) : ℚ)) *
        ((Nat.card I : ℚ) * (Nat.card N : ℚ)) := by
    have hdenNat : Nat.card K * Nat.card G =
        (Nat.card Kbar * Nat.card (G ⧸ N)) * (Nat.card I * Nat.card N) := by
      rw [← hK, ← hG]
      ring
    exact_mod_cast hdenNat
  have hnum : (A : ℚ) ≤ ((B * C : ℕ) : ℚ) := by
    exact_mod_cast hnat
  have hnonneg : 0 ≤ (Nat.card K : ℚ) * (Nat.card G : ℚ) := by
    positivity
  have hfactor : ((B : ℚ) /
        ((Nat.card Kbar : ℚ) * (Nat.card (G ⧸ N) : ℚ))) *
      ((C : ℚ) / ((Nat.card I : ℚ) * (Nat.card N : ℚ))) =
      ((B * C : ℕ) : ℚ) / ((Nat.card K : ℚ) * (Nat.card G : ℚ)) := by
    rw [div_mul_div_comm]
    have hnumcast : (B : ℚ) * (C : ℚ) = ((B * C : ℕ) : ℚ) := by
      norm_num
    have hdencast : ((Nat.card Kbar : ℚ) * (Nat.card (G ⧸ N) : ℚ)) *
        ((Nat.card I : ℚ) * (Nat.card N : ℚ)) =
        (Nat.card K : ℚ) * (Nat.card G : ℚ) := hden.symm
    rw [hnumcast, hdencast]
  calc
    (A : ℚ) / ((Nat.card K : ℚ) * (Nat.card G : ℚ)) ≤
        ((B * C : ℕ) : ℚ) / ((Nat.card K : ℚ) * (Nat.card G : ℚ)) :=
      div_le_div_of_nonneg_right hnum hnonneg
    _ = ((B : ℚ) /
          ((Nat.card Kbar : ℚ) * (Nat.card (G ⧸ N) : ℚ))) *
        ((C : ℚ) / ((Nat.card I : ℚ) * (Nat.card N : ℚ))) := hfactor.symm
    _ = ((Nat.card {p : Kbar × (G ⧸ N) // Commute (p.1 : G ⧸ N) p.2} : ℚ) /
          ((Nat.card Kbar : ℚ) * (Nat.card (G ⧸ N) : ℚ))) *
        ((Nat.card {p : (K.comap N.subtype) × N // Commute (p.1 : N) p.2} : ℚ) /
          ((Nat.card (K.comap N.subtype) : ℚ) * (Nat.card N : ℚ))) := rfl


#check_dependency_graph "relative_commuting_probability_le" against "{\"edges\":[{\"conclusion\":{\"name\":\"hnat\",\"statement\":\"A ≤ B * C\"},\"graphEdgeId\":\"h_001_hnat\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"Finite G\"},{\"name\":\"<generated-instance>\",\"statement\":\"N.Normal\"}],\"rawEdgeId\":\"telescope_12\"},{\"conclusion\":{\"name\":\"hK\",\"statement\":\"Nat.card ↥I * Nat.card ↥Kbar = Nat.card ↥K\"},\"graphEdgeId\":\"h_002_hk\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"Finite G\"},{\"name\":\"<generated-instance>\",\"statement\":\"N.Normal\"}],\"rawEdgeId\":\"telescope_13\"},{\"conclusion\":{\"name\":\"hG\",\"statement\":\"Nat.card (G ⧸ N) * Nat.card ↥N = Nat.card G\"},\"graphEdgeId\":\"h_003_hg\",\"premises\":[],\"rawEdgeId\":\"telescope_14\"},{\"conclusion\":{\"name\":\"hnonneg\",\"statement\":\"0 ≤ ↑(Nat.card ↥K) * ↑(Nat.card G)\"},\"graphEdgeId\":\"h_006_hnonneg\",\"premises\":[],\"rawEdgeId\":\"telescope_17\"},{\"conclusion\":{\"name\":\"hden\",\"statement\":\"↑(Nat.card ↥K) * ↑(Nat.card G) = ↑(Nat.card ↥Kbar) * ↑(Nat.card (G ⧸ N)) * (↑(Nat.card ↥I) * ↑(Nat.card ↥N))\"},\"graphEdgeId\":\"h_004_hden\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"N.Normal\"},{\"name\":\"hK\",\"statement\":\"Nat.card ↥I * Nat.card ↥Kbar = Nat.card ↥K\"},{\"name\":\"hG\",\"statement\":\"Nat.card (G ⧸ N) * Nat.card ↥N = Nat.card G\"}],\"rawEdgeId\":\"telescope_15\"},{\"conclusion\":{\"name\":\"hnum\",\"statement\":\"↑A ≤ ↑(B * C)\"},\"graphEdgeId\":\"h_005_hnum\",\"premises\":[{\"name\":\"hnat\",\"statement\":\"A ≤ B * C\"}],\"rawEdgeId\":\"telescope_16\"},{\"conclusion\":{\"name\":\"hfactor\",\"statement\":\"↑B / (↑(Nat.card ↥Kbar) * ↑(Nat.card (G ⧸ N))) * (↑C / (↑(Nat.card ↥I) * ↑(Nat.card ↥N))) = ↑(B * C) / (↑(Nat.card ↥K) * ↑(Nat.card G))\"},\"graphEdgeId\":\"h_007_hfactor\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"N.Normal\"},{\"name\":\"hden\",\"statement\":\"↑(Nat.card ↥K) * ↑(Nat.card G) = ↑(Nat.card ↥Kbar) * ↑(Nat.card (G ⧸ N)) * (↑(Nat.card ↥I) * ↑(Nat.card ↥N))\"}],\"rawEdgeId\":\"telescope_18\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"↑A / (↑(Nat.card ↥K) * ↑(Nat.card G)) ≤ ↑(Nat.card { p // Commute (↑p.1) p.2 }) / (↑(Nat.card ↥Kbar) * ↑(Nat.card (G ⧸ N))) * (↑(Nat.card { p // Commute (↑p.1) p.2 }) / (↑(Nat.card ↥(Subgroup.comap N.subtype K)) * ↑(Nat.card ↥N)))\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"N.Normal\"},{\"name\":\"hnum\",\"statement\":\"↑A ≤ ↑(B * C)\"},{\"name\":\"hnonneg\",\"statement\":\"0 ≤ ↑(Nat.card ↥K) * ↑(Nat.card G)\"},{\"name\":\"hfactor\",\"statement\":\"↑B / (↑(Nat.card ↥Kbar) * ↑(Nat.card (G ⧸ N))) * (↑C / (↑(Nat.card ↥I) * ↑(Nat.card ↥N))) = ↑(B * C) / (↑(Nat.card ↥K) * ↑(Nat.card G))\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1639_relative_commuting_probability_le\",\"reconstructedProofSha256\":\"cb6c150eab58d9a70eca0d44089c03967e53e1c410f9bd5faf1089f338ed94a8\",\"selectedEdgeCount\":8,\"theoremName\":\"relative_commuting_probability_le\",\"topologySha256\":\"238ee4d8a7cc5f36548c7db5590c508e76736bd9d1fa902a5b8e58d80fd2b1f5\"}"
