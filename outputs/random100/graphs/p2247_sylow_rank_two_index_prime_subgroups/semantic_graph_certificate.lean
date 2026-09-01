import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p2247_sylow_rank_two_index_prime_subgroups
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 1c6ca46bbda1eeac93fb6cf04404be324d1119b830fc90bfd6f96fc2ea3164f9
-- reconstructed_proof_sha256: 95be45d03e9821e2b759a62abd02ffbb2f228a34dc84b4acd36cb28361c24923
-- selected_edge_count: 2

/- accepted add_to_file helper 1 -/
lemma comm_isComplement'_of_sup_top_inf_bot {G : Type*} [CommGroup G] {H K : Subgroup G}
    (hs : H ⊔ K = ⊤) (hi : H ⊓ K = ⊥) : H.IsComplement' K := by
  unfold Subgroup.IsComplement'
  constructor
  · intro a b hab
    change ((a.1 : G) * a.2) = ((b.1 : G) * b.2) at hab
    have heq : ((a.1 : G)⁻¹ * b.1) = ((a.2 : G) * (b.2 : G)⁻¹) := by
      calc
        ((a.1 : G)⁻¹ * b.1)
            = ((a.1 : G)⁻¹ * ((b.1 : G) * b.2) * (b.2 : G)⁻¹) := by group
        _ = ((a.1 : G)⁻¹ * ((a.1 : G) * a.2) * (b.2 : G)⁻¹) := by rw [hab]
        _ = ((a.2 : G) * (b.2 : G)⁻¹) := by group
    have hmem : ((a.1 : G)⁻¹ * b.1) ∈ H ⊓ K := by
      rw [Subgroup.mem_inf]
      constructor
      · exact H.mul_mem (H.inv_mem a.1.property) b.1.property
      · rw [heq]
        exact K.mul_mem a.2.property (K.inv_mem b.2.property)
    have hone : ((a.1 : G)⁻¹ * b.1) = 1 := by
      exact (Subgroup.eq_bot_iff_forall (H ⊓ K)).mp hi _ hmem
    have h1 : (a.1 : G) = b.1 := inv_mul_eq_one.mp hone
    have h2 : (a.2 : G) = b.2 := by
      have hone2 : ((a.2 : G) * (b.2 : G)⁻¹) = 1 := by rw [← heq, hone]
      exact mul_inv_eq_one.mp hone2
    ext <;> assumption
  · intro g
    have hg : (g : G) ∈ H ⊔ K := by rw [hs]; exact Subgroup.mem_top g
    rw [Subgroup.mem_sup] at hg
    rcases hg with ⟨h, hh, k, hk, hhk⟩
    exact ⟨⟨⟨h, hh⟩, ⟨k, hk⟩⟩, by simpa using hhk⟩

/- accepted add_to_file helper 2 -/
def commSubgroupProdHom {G : Type*} [CommGroup G] (H K : Subgroup G) :
    H × K →* G where
  toFun p := (p.1 : G) * p.2
  map_one' := by simp
  map_mul' := by
    intro a b
    simp [mul_left_comm, mul_comm]

/- accepted add_to_file helper 3 -/
lemma commSubgroupProdHom_range {G : Type*} [CommGroup G] (H K : Subgroup G) :
    (commSubgroupProdHom H K).range = H ⊔ K := by
  ext z
  constructor
  · intro hz
    rcases hz with ⟨p, rfl⟩
    exact Subgroup.mul_mem_sup p.1.property p.2.property
  · intro hz
    rw [Subgroup.mem_sup] at hz
    rcases hz with ⟨h, hh, k, hk, hhk⟩
    exact ⟨⟨⟨h, hh⟩, ⟨k, hk⟩⟩, by simpa [commSubgroupProdHom] using hhk⟩

lemma commSubgroupProdHom_injective {G : Type*} [CommGroup G] {H K : Subgroup G}
    (hi : H ⊓ K = ⊥) : Function.Injective (commSubgroupProdHom H K) := by
  intro a b hab
  change ((a.1 : G) * a.2) = ((b.1 : G) * b.2) at hab
  have heq : ((a.1 : G)⁻¹ * b.1) = ((a.2 : G) * (b.2 : G)⁻¹) := by
    calc
      ((a.1 : G)⁻¹ * b.1)
          = ((a.1 : G)⁻¹ * ((b.1 : G) * b.2) * (b.2 : G)⁻¹) := by group
      _ = ((a.1 : G)⁻¹ * ((a.1 : G) * a.2) * (b.2 : G)⁻¹) := by rw [hab]
      _ = ((a.2 : G) * (b.2 : G)⁻¹) := by group
  have hmem : ((a.1 : G)⁻¹ * b.1) ∈ H ⊓ K := by
    rw [Subgroup.mem_inf]
    constructor
    · exact H.mul_mem (H.inv_mem a.1.property) b.1.property
    · rw [heq]
      exact K.mul_mem a.2.property (K.inv_mem b.2.property)
  have hone : ((a.1 : G)⁻¹ * b.1) = 1 := by
    exact (Subgroup.eq_bot_iff_forall (H ⊓ K)).mp hi _ hmem
  have h1 : (a.1 : G) = b.1 := inv_mul_eq_one.mp hone
  have h2 : (a.2 : G) = b.2 := by
    have hone2 : ((a.2 : G) * (b.2 : G)⁻¹) = 1 := by rw [← heq, hone]
    exact mul_inv_eq_one.mp hone2
  ext <;> assumption

/- accepted add_to_file helper 4 -/
lemma Nat_card_sup_of_inf_bot {G : Type*} [CommGroup G] {H K : Subgroup G}
    (hi : H ⊓ K = ⊥) : Nat.card ↥(H ⊔ K) = Nat.card ↥H * Nat.card ↥K := by
  let f := commSubgroupProdHom H K
  have hinj : Function.Injective f.rangeRestrict := by
    rw [MonoidHom.rangeRestrict_injective_iff]
    exact commSubgroupProdHom_injective hi
  have hbij : Function.Bijective f.rangeRestrict :=
    ⟨hinj, MonoidHom.rangeRestrict_surjective f⟩
  let e : (↥H × ↥K) ≃* f.range := MulEquiv.ofBijective f.rangeRestrict hbij
  calc
    Nat.card ↥(H ⊔ K) = Nat.card ↥f.range := by rw [commSubgroupProdHom_range]
    _ = Nat.card (↥H × ↥K) := (Nat.card_congr e.toEquiv).symm
    _ = Nat.card ↥H * Nat.card ↥K := Nat.card_prod ↥H ↥K

/- accepted add_to_file helper 5 -/
lemma orderOf_prime_pow_pow {G : Type*} [Group G] {p u k : ℕ}
    (hp : p.Prime) {x : G} (hx : orderOf x = p ^ u) (hku : k ≤ u) :
    orderOf (x ^ (p ^ k)) = p ^ (u - k) := by
  have hdvd : p ^ k ∣ orderOf x := by
    rw [hx]
    exact pow_dvd_pow p hku
  rw [orderOf_pow_of_dvd (pow_ne_zero k hp.ne_zero) hdvd, hx]
  exact Nat.pow_div hku hp.pos

/- accepted add_to_file helper 6 -/
lemma zpowers_pow_inf_zpowers_pow_eq_bot {G : Type*} [Group G] {x y : G}
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) (m n : ℕ) :
    Subgroup.zpowers (x ^ m) ⊓ Subgroup.zpowers (y ^ n) = ⊥ := by
  have hxm : Subgroup.zpowers (x ^ m) ≤ Subgroup.zpowers x := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.pow_mem (Subgroup.zpowers x) (Subgroup.mem_zpowers x) m
  have hyn : Subgroup.zpowers (y ^ n) ≤ Subgroup.zpowers y := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.pow_mem (Subgroup.zpowers y) (Subgroup.mem_zpowers y) n
  apply le_antisymm
  · calc
      Subgroup.zpowers (x ^ m) ⊓ Subgroup.zpowers (y ^ n)
          ≤ Subgroup.zpowers x ⊓ Subgroup.zpowers y := inf_le_inf hxm hyn
      _ = ⊥ := hind
  · exact bot_le

/- accepted add_to_file helper 7 -/
lemma product_eq_one_of_inf_bot {G : Type*} [CommGroup G] {H K : Subgroup G}
    (hi : H ⊓ K = ⊥) {a b : G} (ha : a ∈ H) (hb : b ∈ K)
    (h : a * b = 1) : a = 1 ∧ b = 1 := by
  let f := commSubgroupProdHom H K
  have hpair : (⟨⟨a, ha⟩, ⟨b, hb⟩⟩ : H × K) = 1 := by
    apply commSubgroupProdHom_injective hi
    simp [commSubgroupProdHom, h]
  constructor
  · exact congrArg (fun p : H × K => (p.1 : G)) hpair
  · exact congrArg (fun p : H × K => (p.2 : G)) hpair

/- accepted add_to_file helper 8 -/
lemma int_prime_pow_mul_dvd_mul_iff {p u : ℕ} (hp : p.Prime) (hu : 0 < u) {i : ℤ} :
    ((p ^ u : ℕ) : ℤ) ∣ i * p ↔ ((p ^ (u - 1) : ℕ) : ℤ) ∣ i := by
  have hpow : ((p ^ u : ℕ) : ℤ) = (p ^ (u - 1) : ℕ) * p := by
    calc
      ((p ^ u : ℕ) : ℤ) = ((p ^ (u - 1 + 1) : ℕ) : ℤ) := by rw [Nat.sub_add_cancel hu]
      _ = (p ^ (u - 1) : ℕ) * p := by rw [pow_succ, Nat.cast_mul]
  have hpz : ((p : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [hpow, Int.mul_dvd_mul_iff_right hpz]

/- accepted add_to_file helper 9 -/
lemma zpow_mem_zpowers_pow_of_dvd {G : Type*} [Group G] (x : G) {n : ℕ} {i : ℤ}
    (hd : (n : ℤ) ∣ i) : x ^ i ∈ Subgroup.zpowers (x ^ n) := by
  rcases hd with ⟨t, rfl⟩
  rw [zpow_mul]
  convert Subgroup.zpow_mem _ (Subgroup.mem_zpowers (x ^ n)) t using 2
  exact zpow_natCast x n

/- accepted add_to_file helper 10 -/
lemma pow_ker_eq_zpowers_sup {G : Type*} [CommGroup G]
    {p u v : ℕ} (hp : p.Prime) (hu : 0 < u) (hv : 0 < v)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p ^ v)
    (hspan : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    (powMonoidHom p : G →* G).ker =
      Subgroup.zpowers (x ^ (p ^ (u - 1))) ⊔
        Subgroup.zpowers (y ^ (p ^ (v - 1))) := by
  ext z
  constructor
  · intro hzker
    have hzpow : z ^ p = 1 := by simpa [powMonoidHom] using hzker
    have htop : z ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y := by
      rw [hspan]
      exact Subgroup.mem_top z
    rw [Subgroup.mem_sup] at htop
    rcases htop with ⟨a, ha, b, hb, hab⟩
    rw [Subgroup.mem_zpowers_iff] at ha hb
    rcases ha with ⟨i, rfl⟩
    rcases hb with ⟨j, rfl⟩
    subst z
    have hzpowprod : x ^ (i * p) * y ^ (j * p) = 1 := by
      calc
        x ^ (i * p) * y ^ (j * p) = (x ^ i * y ^ j) ^ p := by
          calc
            x ^ (i * p) * y ^ (j * p) = (x ^ i * y ^ j) ^ (p : ℤ) := by
              rw [mul_zpow, ← zpow_mul, ← zpow_mul]
            _ = (x ^ i * y ^ j) ^ p := by rw [zpow_natCast]
        _ = 1 := hzpow
    have hone := product_eq_one_of_inf_bot hind
      (Subgroup.zpow_mem (Subgroup.zpowers x) (Subgroup.mem_zpowers x) _)
      (Subgroup.zpow_mem (Subgroup.zpowers y) (Subgroup.mem_zpowers y) _) hzpowprod
    have hdix : (orderOf x : ℤ) ∣ i * p := orderOf_dvd_iff_zpow_eq_one.mpr hone.1
    have hdiy : (orderOf y : ℤ) ∣ j * p := orderOf_dvd_iff_zpow_eq_one.mpr hone.2
    rw [hx] at hdix
    rw [hy] at hdiy
    have hiq : ((p ^ (u - 1) : ℕ) : ℤ) ∣ i := (int_prime_pow_mul_dvd_mul_iff hp hu).mp hdix
    have hjq : ((p ^ (v - 1) : ℕ) : ℤ) ∣ j := (int_prime_pow_mul_dvd_mul_iff hp hv).mp hdiy
    exact Subgroup.mul_mem_sup
      (zpow_mem_zpowers_pow_of_dvd x hiq)
      (zpow_mem_zpowers_pow_of_dvd y hjq)
  · intro hz
    rw [Subgroup.mem_sup] at hz
    rcases hz with ⟨a, ha, b, hb, hab⟩
    subst z
    have hxqord : orderOf (x ^ (p ^ (u - 1))) = p := by
      rw [orderOf_prime_pow_pow hp hx (Nat.sub_le u 1)]
      rw [show u - (u - 1) = 1 by omega, pow_one]
    have hyqord : orderOf (y ^ (p ^ (v - 1))) = p := by
      rw [orderOf_prime_pow_pow hp hy (Nat.sub_le v 1)]
      rw [show v - (v - 1) = 1 by omega, pow_one]
    have hadvd : orderOf a ∣ p := by
      rw [← hxqord]
      exact orderOf_dvd_of_mem_zpowers ha
    have hbdvd : orderOf b ∣ p := by
      rw [← hyqord]
      exact orderOf_dvd_of_mem_zpowers hb
    have hap : a ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp hadvd
    have hbp : b ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp hbdvd
    change (a * b) ^ p = 1
    rw [mul_pow, hap, hbp, one_mul]

/- accepted add_to_file helper 11 -/
lemma Nat_card_pow_ker {G : Type*} [CommGroup G]
    {p u v : ℕ} (hp : p.Prime) (hu : 0 < u) (hv : 0 < v)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p ^ v)
    (hspan : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    Nat.card ↥((powMonoidHom p : G →* G).ker) = p ^ 2 := by
  rw [pow_ker_eq_zpowers_sup hp hu hv hx hy hspan hind]
  rw [Nat_card_sup_of_inf_bot (zpowers_pow_inf_zpowers_pow_eq_bot hind _ _)]
  rw [Nat.card_zpowers, Nat.card_zpowers]
  have hxqord : orderOf (x ^ (p ^ (u - 1))) = p := by
    rw [orderOf_prime_pow_pow hp hx (Nat.sub_le u 1)]
    rw [show u - (u - 1) = 1 by omega, pow_one]
  have hyqord : orderOf (y ^ (p ^ (v - 1))) = p := by
    rw [orderOf_prime_pow_pow hp hy (Nat.sub_le v 1)]
    rw [show v - (v - 1) = 1 by omega, pow_one]
  rw [hxqord, hyqord]
  exact (pow_two p).symm

/- accepted add_to_file helper 12 -/
lemma Nat_card_of_zpowers_sup_top_inf_bot {G : Type*} [CommGroup G] {x y : G}
    (hspan : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    Nat.card G = orderOf x * orderOf y := by
  have hcomp := comm_isComplement'_of_sup_top_inf_bot hspan hind
  calc
    Nat.card G = Nat.card ↥(Subgroup.zpowers x) * Nat.card ↥(Subgroup.zpowers y) :=
      hcomp.card_mul.symm
    _ = orderOf x * orderOf y := by rw [Nat.card_zpowers, Nat.card_zpowers]

/- accepted add_to_file helper 13 -/
lemma subgroup_index_prime_iff_card_prime_of_card_sq {G : Type*} [Group G]
    {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ 2) (U : Subgroup G) :
    U.index = p ↔ Nat.card U = p := by
  have h := U.card_mul_index
  rw [hG, pow_two] at h
  constructor
  · intro hindex
    rw [hindex, mul_comm] at h
    exact Nat.mul_left_cancel hp.pos h
  · intro hcard
    rw [hcard] at h
    exact Nat.mul_left_cancel hp.pos h

/- accepted add_to_file helper 14 -/
lemma pow_mem_subgroup_of_index_eq {G : Type*} [CommGroup G]
    (U : Subgroup G) {p : ℕ} (hindex : U.index = p) (g : G) :
    g ^ p ∈ U := by
  letI := Subgroup.normal_of_comm U
  let q := QuotientGroup.mk' U
  have hqpow : (q g) ^ p = 1 := by
    have h := pow_card_eq_one' (x := q g)
    rwa [← U.index_eq_card, hindex] at h
  have hker : g ^ p ∈ q.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hqpow
  rwa [QuotientGroup.ker_mk'] at hker

/- accepted add_to_file helper 15 -/
lemma subgroup_index_prime_iff_card_eq_of_card_pow_succ {G : Type*} [Group G]
    {p u : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ (u + 1)) (U : Subgroup G) :
    U.index = p ↔ Nat.card ↥U = p ^ u := by
  have h := U.card_mul_index
  rw [hG, pow_succ] at h
  have hpu : 0 < p ^ u := pow_pos hp.pos u
  constructor
  · intro hindex
    rw [hindex] at h
    exact Nat.mul_right_cancel hp.pos h
  · intro hcard
    rw [hcard] at h
    exact Nat.mul_left_cancel hpu h

/- accepted add_to_file helper 16 -/
lemma zpowers_x_pow_pred_le_zpowers_x_pow {G : Type*} [Group G]
    {p u : ℕ} (hu : 1 < u) (x : G) :
    Subgroup.zpowers (x ^ (p ^ (u - 1))) ≤ Subgroup.zpowers (x ^ p) := by
  rw [Subgroup.zpowers_le]
  rw [show u - 1 = (u - 2) + 1 by omega, pow_succ, mul_comm, pow_mul]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers (x ^ p)) _

/- accepted add_to_file helper 17 -/
lemma N_index_mem_unique_v1 {G : Type*} [CommGroup G] [Finite G]
    {p u v : ℕ} (hp : p.Prime) (hu : 0 < u) (hv : 0 < v)
    (hu1 : 1 < u) (hv1 : v = 1)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p ^ v)
    (hspan : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    let E : Subgroup G := (powMonoidHom p : G →* G).ker
    let N : Subgroup G := Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y
    N.index = p ∧ E ≤ N ∧
      (∀ U : Subgroup G, U.index = p → E ≤ U → U = N) := by
  intro E N
  have hE : E = Subgroup.zpowers (x ^ (p ^ (u - 1))) ⊔
      Subgroup.zpowers (y ^ (p ^ (v - 1))) :=
    pow_ker_eq_zpowers_sup hp hu hv hx hy hspan hind
  have hPcard : Nat.card G = p ^ (u + 1) := by
    rw [Nat_card_of_zpowers_sup_top_inf_bot hspan hind, hx, hy, hv1, pow_one, ← pow_succ]
  have hNcard : Nat.card ↥N = p ^ u := by
    dsimp [N]
    have hNinf : Subgroup.zpowers (x ^ p) ⊓ Subgroup.zpowers y = ⊥ := by
      simpa using zpowers_pow_inf_zpowers_pow_eq_bot hind p 1
    rw [Nat_card_sup_of_inf_bot hNinf]
    rw [Nat.card_zpowers, Nat.card_zpowers]
    have hordxp : orderOf (x ^ p) = p ^ (u - 1) := by
      simpa using orderOf_prime_pow_pow hp hx (k := 1) (by omega : 1 ≤ u)
    rw [hordxp, hy, hv1, pow_one]
    rw [← pow_succ]
    congr 1
    omega
  have hNindex : N.index = p :=
    (subgroup_index_prime_iff_card_eq_of_card_pow_succ hp hPcard N).mpr hNcard
  refine ⟨hNindex, ?_, ?_⟩
  · rw [hE, hv1]
    simp only [Nat.reduceSub, pow_zero, pow_one]
    apply sup_le
    · exact le_trans (zpowers_x_pow_pred_le_zpowers_x_pow hu1 x) le_sup_left
    · exact (le_sup_right : Subgroup.zpowers y ≤
        Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y)
  · intro U hUindex hEU
    have hyE : y ∈ E := by
      rw [hE, hv1]
      simp only [Nat.reduceSub, pow_zero, pow_one]
      exact (le_sup_right : Subgroup.zpowers y ≤
        Subgroup.zpowers (x ^ (p ^ (u - 1))) ⊔ Subgroup.zpowers y) (Subgroup.mem_zpowers y)
    have hyU : y ∈ U := hEU hyE
    have hxpU : x ^ p ∈ U := pow_mem_subgroup_of_index_eq U hUindex x
    have hNU : N ≤ U := by
      dsimp [N]
      apply sup_le
      · rwa [Subgroup.zpowers_le]
      · rwa [Subgroup.zpowers_le]
    have hUcard : Nat.card ↥U = p ^ u :=
      (subgroup_index_prime_iff_card_eq_of_card_pow_succ hp hPcard U).mp hUindex
    apply Eq.symm
    apply Subgroup.eq_of_le_of_card_ge hNU
    rw [hUcard, hNcard]

/- accepted add_to_file helper 18 -/
lemma orderOf_mul_zpow_right_v1 {G : Type*} [CommGroup G] [Finite G]
    {p u : ℕ} (hp : p.Prime) (hu : 0 < u)
    {x y : G} (hx : orderOf x = p ^ u) (hy : orderOf y = p)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) (k : ℤ) :
    orderOf (x * y ^ k) = p ^ u := by
  let z := x * y ^ k
  have hpow_formula : ∀ n : ℕ, z ^ n = x ^ n * y ^ (k * n) := by
    intro n
    calc
      z ^ n = (x * y ^ k) ^ (n : ℤ) := by rw [zpow_natCast]
      _ = x ^ (n : ℤ) * (y ^ k) ^ (n : ℤ) := by rw [mul_zpow]
      _ = x ^ n * y ^ (k * n) := by rw [zpow_natCast, ← zpow_mul]
  have hxupper : x ^ p ^ u = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hyupper : y ^ (k * ((p ^ u : ℕ) : ℤ)) = 1 := by
    have hfac : k * (((p ^ u : ℕ) : ℤ)) = (p : ℤ) * (k * (((p ^ (u - 1) : ℕ) : ℤ))) := by
      have hpow : (((p ^ u : ℕ) : ℤ)) = (p : ℤ) * (((p ^ (u - 1) : ℕ) : ℤ)) := by
        calc
          (((p ^ u : ℕ) : ℤ)) = (((p ^ (u - 1 + 1) : ℕ) : ℤ)) := by rw [Nat.sub_add_cancel hu]
          _ = (p : ℤ) * (((p ^ (u - 1) : ℕ) : ℤ)) := by
            rw [pow_succ, Nat.cast_mul, mul_comm]
      rw [hpow]
      ring
    rw [hfac, zpow_mul]
    have hyp : y ^ (p : ℤ) = 1 := by
      rw [zpow_natCast, ← hy]
      exact pow_orderOf_eq_one y
    rw [hyp, one_zpow]
  have hupper : z ^ p ^ u = 1 := by
    rw [hpow_formula, hxupper, hyupper, one_mul]
  have hle : orderOf z ≤ p ^ u :=
    orderOf_le_of_pow_eq_one (pow_pos hp.pos u) hupper
  have hge : p ^ u ≤ orderOf z := by
    have hzd : z ^ orderOf z = 1 := pow_orderOf_eq_one z
    rw [hpow_formula] at hzd
    have hone := product_eq_one_of_inf_bot hind
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _)
      (Subgroup.zpow_mem _ (Subgroup.mem_zpowers y) _) hzd
    have hdvd : orderOf x ∣ orderOf z := orderOf_dvd_iff_pow_eq_one.mpr hone.1
    rw [hx] at hdvd
    exact Nat.le_of_dvd (orderOf_pos z) hdvd
  exact le_antisymm hle hge

/- accepted add_to_file helper 19 -/
lemma mul_zpow_right_pow_pred_eq_left {G : Type*} [CommGroup G]
    {p u : ℕ} (hu : 1 < u) {x y : G} (hy : orderOf y = p) (k : ℤ) :
    (x * y ^ k) ^ (p ^ (u - 1)) = x ^ (p ^ (u - 1)) := by
  let z := x * y ^ k
  have hpow_formula : ∀ n : ℕ, z ^ n = x ^ n * y ^ (k * n) := by
    intro n
    calc
      z ^ n = (x * y ^ k) ^ (n : ℤ) := by rw [zpow_natCast]
      _ = x ^ (n : ℤ) * (y ^ k) ^ (n : ℤ) := by rw [mul_zpow]
      _ = x ^ n * y ^ (k * n) := by rw [zpow_natCast, ← zpow_mul]
  have hyq : y ^ (k * (((p ^ (u - 1) : ℕ) : ℤ))) = 1 := by
    have hfac : k * (((p ^ (u - 1) : ℕ) : ℤ)) =
        (p : ℤ) * (k * (((p ^ (u - 2) : ℕ) : ℤ))) := by
      have hpow : (((p ^ (u - 1) : ℕ) : ℤ)) =
          (p : ℤ) * (((p ^ (u - 2) : ℕ) : ℤ)) := by
        calc
          (((p ^ (u - 1) : ℕ) : ℤ)) = (((p ^ ((u - 2) + 1) : ℕ) : ℤ)) := by
            congr 2
            omega
          _ = (p : ℤ) * (((p ^ (u - 2) : ℕ) : ℤ)) := by
            rw [pow_succ, Nat.cast_mul, mul_comm]
      rw [hpow]
      ring
    rw [hfac, zpow_mul]
    have hyp : y ^ (p : ℤ) = 1 := by
      rw [zpow_natCast, ← hy]
      exact pow_orderOf_eq_one y
    rw [hyp, one_zpow]
  calc
    (x * y ^ k) ^ (p ^ (u - 1)) = z ^ (p ^ (u - 1)) := rfl
    _ = x ^ (p ^ (u - 1)) * y ^ (k * (((p ^ (u - 1) : ℕ) : ℤ))) := hpow_formula _
    _ = x ^ (p ^ (u - 1)) := by rw [hyq, mul_one]

/- accepted add_to_file helper 20 -/
lemma cyclic_nonN_v1 {G : Type*} [CommGroup G] [Finite G]
    {p u v : ℕ} (hp : p.Prime) (hu : 0 < u) (hv : 0 < v)
    (hu1 : 1 < u) (hv1 : v = 1)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p ^ v)
    (hspan : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥)
    {U : Subgroup G} (hU : U.index = p)
    (hUN : U ≠ Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y) :
    let E : Subgroup G := (powMonoidHom p : G →* G).ker
    IsCyclic U ∧ Nat.card ↥U = p ^ u ∧
      U ⊓ E = Subgroup.zpowers (x ^ (p ^ (u - 1))) := by
  intro E
  let N : Subgroup G := Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y
  have hN := N_index_mem_unique_v1 hp hu hv hu1 hv1 hx hy hspan hind
  change N.index = p ∧ E ≤ N ∧ (∀ V : Subgroup G, V.index = p → E ≤ V → V = N) at hN
  have hE : E = Subgroup.zpowers (x ^ (p ^ (u - 1))) ⊔
      Subgroup.zpowers (y ^ (p ^ (v - 1))) :=
    pow_ker_eq_zpowers_sup hp hu hv hx hy hspan hind
  have hPcard : Nat.card G = p ^ (u + 1) := by
    rw [Nat_card_of_zpowers_sup_top_inf_bot hspan hind, hx, hy, hv1, pow_one, ← pow_succ]
  have hUcard : Nat.card ↥U = p ^ u :=
    (subgroup_index_prime_iff_card_eq_of_card_pow_succ hp hPcard U).mp hU
  have hyU : y ∉ U := by
    intro h
    have hEU : E ≤ U := by
      rw [hE, hv1]
      simp only [Nat.reduceSub, pow_zero, pow_one]
      apply sup_le
      · have hxpU : x ^ p ∈ U := pow_mem_subgroup_of_index_eq U hU x
        exact le_trans (zpowers_x_pow_pred_le_zpowers_x_pow hu1 x)
          ((Subgroup.zpowers_le).mpr hxpU)
      · exact (Subgroup.zpowers_le).mpr h
    exact hUN (hN.2.2 U hU hEU)
  letI : Fact p.Prime := ⟨hp⟩
  letI := Subgroup.normal_of_comm U
  let q : G →* G ⧸ U := QuotientGroup.mk' U
  have hQcard : Nat.card (G ⧸ U) = p := by rw [← U.index_eq_card, hU]
  have hqy : q y ≠ 1 := by
    intro h
    have hyker : y ∈ q.ker := by rw [MonoidHom.mem_ker]; exact h
    rw [QuotientGroup.ker_mk'] at hyker
    exact hyU hyker
  have hqxmem : q x ∈ Subgroup.zpowers (q y) :=
    mem_zpowers_of_prime_card hQcard hqy
  rw [Subgroup.mem_zpowers_iff] at hqxmem
  rcases hqxmem with ⟨i, hiq⟩
  let k : ℤ := -i
  let z : G := x * y ^ k
  have hzq : q z = 1 := by
    change q (x * y ^ (-i)) = 1
    rw [map_mul, map_zpow, ← hiq]
    simp
  have hzU : z ∈ U := by
    have hzker : z ∈ q.ker := by rw [MonoidHom.mem_ker]; exact hzq
    rw [QuotientGroup.ker_mk'] at hzker
    exact hzker
  have hy' : orderOf y = p := by simpa [hv1] using hy
  have hzorder : orderOf z = p ^ u :=
    orderOf_mul_zpow_right_v1 hp hu hx hy' hind k
  have hHzU : Subgroup.zpowers z ≤ U := (Subgroup.zpowers_le).mpr hzU
  have hUeq : U = Subgroup.zpowers z := by
    apply Eq.symm
    apply Subgroup.eq_of_le_of_card_ge hHzU
    rw [hUcard, Nat.card_zpowers, hzorder]
  have hA : Subgroup.zpowers (x ^ (p ^ (u - 1))) ≤ U ⊓ E := by
    apply le_inf
    · rw [hUeq, Subgroup.zpowers_le]
      rw [← mul_zpow_right_pow_pred_eq_left hu1 hy' k]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers z) _
    · rw [hE, hv1]
      simp only [Nat.reduceSub, pow_zero, pow_one]
      exact le_sup_left
  have hinter : U ⊓ E = Subgroup.zpowers (x ^ (p ^ (u - 1))) := by
    apply le_antisymm
    · intro w hw
      have hwU : w ∈ U := hw.1
      have hwE : w ∈ E := hw.2
      rw [hUeq, Subgroup.mem_zpowers_iff] at hwU
      rcases hwU with ⟨t, hwt⟩
      have hwpow : w ^ p = 1 := by simpa [E, powMonoidHom] using hwE
      have hzpowtp : z ^ (t * p) = 1 := by
        calc
          z ^ (t * p) = (z ^ t) ^ (p : ℤ) := by rw [← zpow_mul]
          _ = (z ^ t) ^ p := by rw [zpow_natCast]
          _ = 1 := by rw [hwt]; exact hwpow
      have hdvd : (orderOf z : ℤ) ∣ t * p := orderOf_dvd_iff_zpow_eq_one.mpr hzpowtp
      rw [hzorder] at hdvd
      have hqdt : (((p ^ (u - 1) : ℕ) : ℤ)) ∣ t :=
        (int_prime_pow_mul_dvd_mul_iff hp hu).mp hdvd
      rcases hqdt with ⟨s, rfl⟩
      have hzqpow : z ^ (((p ^ (u - 1) : ℕ) : ℤ)) = x ^ (p ^ (u - 1)) := by
        rw [zpow_natCast]
        exact mul_zpow_right_pow_pred_eq_left hu1 hy' k
      have hweq : w = (x ^ (p ^ (u - 1))) ^ s := by
        calc
          w = z ^ ((((p ^ (u - 1) : ℕ) : ℤ)) * s) := hwt.symm
          _ = (z ^ (((p ^ (u - 1) : ℕ) : ℤ))) ^ s := by rw [zpow_mul]
          _ = (x ^ (p ^ (u - 1))) ^ s := by rw [hzqpow]
      rw [hweq]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers (x ^ (p ^ (u - 1)))) s
    · exact hA
  refine ⟨?_, hUcard, hinter⟩
  rw [hUeq]
  exact Subgroup.isCyclic_zpowers z

/- accepted add_to_file helper 21 -/
lemma H_fin_injective_v1 {G : Type*} [CommGroup G]
    {p u : ℕ} (hp : p.Prime) (hu : 0 < u)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    Function.Injective (fun r : Fin p =>
      Subgroup.zpowers (x * y ^ (r.val : ℕ))) := by
  intro r s hrs
  change Subgroup.zpowers (x * y ^ (r.val : ℕ)) =
    Subgroup.zpowers (x * y ^ (s.val : ℕ)) at hrs
  have hrs_mem : x * y ^ (s.val : ℕ) ∈
      Subgroup.zpowers (x * y ^ (r.val : ℕ)) := by
    rw [hrs]
    exact Subgroup.mem_zpowers _
  rw [Subgroup.mem_zpowers_iff] at hrs_mem
  rcases hrs_mem with ⟨t, ht⟩
  have hformula : ((x * y ^ (r.val : ℕ)) ^ t) =
      x ^ t * y ^ (((r.val : ℤ)) * t) := by
    calc
      ((x * y ^ (r.val : ℕ)) ^ t) = x ^ t * (y ^ (r.val : ℕ)) ^ t := by rw [mul_zpow]
      _ = x ^ t * (y ^ ((r.val : ℤ))) ^ t := by rw [zpow_natCast]
      _ = x ^ t * y ^ (((r.val : ℤ)) * t) := by rw [← zpow_mul]
  rw [hformula] at ht
  let X : Subgroup G := Subgroup.zpowers x
  let Y : Subgroup G := Subgroup.zpowers y
  have hpair :
      (⟨⟨x ^ t, Subgroup.zpow_mem X (Subgroup.mem_zpowers x) t⟩,
        ⟨y ^ (((r.val : ℤ)) * t), Subgroup.zpow_mem Y (Subgroup.mem_zpowers y) _⟩⟩ : X × Y) =
      ⟨⟨x, Subgroup.mem_zpowers x⟩,
        ⟨y ^ (s.val : ℕ), Subgroup.pow_mem Y (Subgroup.mem_zpowers y) _⟩⟩ := by
    apply commSubgroupProdHom_injective hind
    simpa [commSubgroupProdHom] using ht
  have hxt : x ^ t = x := congrArg (fun a : X × Y => (a.1 : G)) hpair
  have hyt : y ^ (((r.val : ℤ)) * t) = y ^ (s.val : ℕ) :=
    congrArg (fun a : X × Y => (a.2 : G)) hpair
  have hxone : x ^ (1 - t) = 1 := by
    calc
      x ^ (1 - t) = x * (x ^ t)⁻¹ := by group
      _ = x * x⁻¹ := by rw [hxt]
      _ = 1 := by simp
  have hyone : y ^ (((s.val : ℤ)) - ((r.val : ℤ)) * t) = 1 := by
    calc
      y ^ (((s.val : ℤ)) - ((r.val : ℤ)) * t)
          = y ^ (s.val : ℕ) * (y ^ (((r.val : ℤ)) * t))⁻¹ := by group
      _ = y ^ (s.val : ℕ) * (y ^ (s.val : ℕ))⁻¹ := by rw [hyt]
      _ = 1 := by simp
  have hdvdx : (orderOf x : ℤ) ∣ 1 - t := orderOf_dvd_iff_zpow_eq_one.mpr hxone
  have hdvdy : (orderOf y : ℤ) ∣ (((s.val : ℤ)) - ((r.val : ℤ)) * t) :=
    orderOf_dvd_iff_zpow_eq_one.mpr hyone
  rw [hx] at hdvdx
  rw [hy] at hdvdy
  have hp_dvd_orderx : (p : ℤ) ∣ ((p ^ u : ℕ) : ℤ) := by
    have hd : p ^ 1 ∣ p ^ u := pow_dvd_pow p (by omega : 1 ≤ u)
    have hdZ : (((p ^ 1 : ℕ) : ℤ)) ∣ (((p ^ u : ℕ) : ℤ)) := by exact_mod_cast hd
    simpa using hdZ
  have hpt : (p : ℤ) ∣ 1 - t := dvd_trans hp_dvd_orderx hdvdx
  rcases hpt with ⟨a, ha⟩
  rcases hdvdy with ⟨b, hb⟩
  have hpsr : (p : ℤ) ∣ (((s.val : ℤ)) - (r.val : ℤ)) := by
    refine ⟨b - (r.val : ℤ) * a, ?_⟩
    have hrewrite : (((s.val : ℤ)) - (r.val : ℤ)) =
        ((((s.val : ℤ)) - ((r.val : ℤ)) * t) - ((r.val : ℤ)) * (1 - t)) := by ring
    rw [hrewrite, hb, ha]
    ring
  have hzmod : (((s.val : ℤ) - (r.val : ℤ) : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (((s.val : ℤ) - (r.val : ℤ))) p).mpr hpsr
  have hzmods : (((s.val : ℤ)) : ZMod p) = (((r.val : ℤ)) : ZMod p) := by
    apply sub_eq_zero.mp
    simpa using hzmod
  have hzmodnat : ((s.val : ZMod p) = (r.val : ZMod p)) := by exact_mod_cast hzmods
  have hnatmod : s.val ≡ r.val [MOD p] :=
    (ZMod.natCast_eq_natCast_iff s.val r.val p).mp hzmodnat
  have hval : s.val = r.val :=
    Nat.ModEq.eq_of_lt_of_lt hnatmod s.isLt r.isLt
  exact Fin.ext hval.symm

/- accepted add_to_file helper 22 -/
lemma H_fin_ne_N_v1 {G : Type*} [CommGroup G]
    {p u : ℕ} (hp : p.Prime) (hu : 0 < u)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) (r : Fin p) :
    Subgroup.zpowers (x * y ^ (r.val : ℕ)) ≠
      Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y := by
  intro hHN
  have hyN : y ∈ Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y :=
    (le_sup_right : Subgroup.zpowers y ≤
      Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y) (Subgroup.mem_zpowers y)
  rw [← hHN] at hyN
  rw [Subgroup.mem_zpowers_iff] at hyN
  rcases hyN with ⟨t, ht⟩
  have hformula : ((x * y ^ (r.val : ℕ)) ^ t) =
      x ^ t * y ^ (((r.val : ℤ)) * t) := by
    calc
      ((x * y ^ (r.val : ℕ)) ^ t) = x ^ t * (y ^ (r.val : ℕ)) ^ t := by rw [mul_zpow]
      _ = x ^ t * (y ^ ((r.val : ℤ))) ^ t := by rw [zpow_natCast]
      _ = x ^ t * y ^ (((r.val : ℤ)) * t) := by rw [← zpow_mul]
  rw [hformula] at ht
  let X : Subgroup G := Subgroup.zpowers x
  let Y : Subgroup G := Subgroup.zpowers y
  have hpair :
      (⟨⟨x ^ t, Subgroup.zpow_mem X (Subgroup.mem_zpowers x) t⟩,
        ⟨y ^ (((r.val : ℤ)) * t), Subgroup.zpow_mem Y (Subgroup.mem_zpowers y) _⟩⟩ : X × Y) =
      ⟨⟨1, X.one_mem⟩, ⟨y, Subgroup.mem_zpowers y⟩⟩ := by
    apply commSubgroupProdHom_injective hind
    simpa [commSubgroupProdHom] using ht
  have hxt : x ^ t = 1 := congrArg (fun a : X × Y => (a.1 : G)) hpair
  have hyt : y ^ (((r.val : ℤ)) * t) = y := congrArg (fun a : X × Y => (a.2 : G)) hpair
  have hyone : y ^ (((r.val : ℤ)) * t - 1) = 1 := by
    calc
      y ^ (((r.val : ℤ)) * t - 1) = y ^ (((r.val : ℤ)) * t) * y⁻¹ := by group
      _ = y * y⁻¹ := by rw [hyt]
      _ = 1 := by simp
  have hdvdx : (orderOf x : ℤ) ∣ t := orderOf_dvd_iff_zpow_eq_one.mpr hxt
  have hdvdy : (orderOf y : ℤ) ∣ (((r.val : ℤ)) * t - 1) :=
    orderOf_dvd_iff_zpow_eq_one.mpr hyone
  rw [hx] at hdvdx
  rw [hy] at hdvdy
  have hp_dvd_orderx : (p : ℤ) ∣ ((p ^ u : ℕ) : ℤ) := by
    have hd : p ^ 1 ∣ p ^ u := pow_dvd_pow p (by omega : 1 ≤ u)
    have hdZ : (((p ^ 1 : ℕ) : ℤ)) ∣ (((p ^ u : ℕ) : ℤ)) := by exact_mod_cast hd
    simpa using hdZ
  have hpt : (p : ℤ) ∣ t := dvd_trans hp_dvd_orderx hdvdx
  have hprt : (p : ℤ) ∣ ((r.val : ℤ)) * t := dvd_mul_of_dvd_right hpt _
  rcases hprt with ⟨b, hb⟩
  rcases hdvdy with ⟨a, ha⟩
  have hdiv1 : (p : ℤ) ∣ 1 := by
    refine ⟨b - a, ?_⟩
    have hsub : (p : ℤ) * b - (p : ℤ) * a = 1 := by
      rw [← hb, ← ha]
      ring
    calc
      1 = (p : ℤ) * b - (p : ℤ) * a := hsub.symm
      _ = (p : ℤ) * (b - a) := by ring
  have hdiv1nat : p ∣ 1 := by exact_mod_cast hdiv1
  exact hp.not_dvd_one hdiv1nat

/- accepted add_to_file helper 23 -/
lemma nonN_eq_H_fin_v1 {G : Type*} [CommGroup G] [Finite G]
    {p u v : ℕ} (hp : p.Prime) (hu : 0 < u) (hv : 0 < v)
    (hu1 : 1 < u) (hv1 : v = 1)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p ^ v)
    (hspan : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥)
    {U : Subgroup G} (hU : U.index = p)
    (hUN : U ≠ Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y) :
    ∃ r : Fin p, U = Subgroup.zpowers (x * y ^ (r.val : ℕ)) := by
  let E : Subgroup G := (powMonoidHom p : G →* G).ker
  let N : Subgroup G := Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y
  have hN := N_index_mem_unique_v1 hp hu hv hu1 hv1 hx hy hspan hind
  change N.index = p ∧ E ≤ N ∧ (∀ V : Subgroup G, V.index = p → E ≤ V → V = N) at hN
  have hE : E = Subgroup.zpowers (x ^ (p ^ (u - 1))) ⊔
      Subgroup.zpowers (y ^ (p ^ (v - 1))) :=
    pow_ker_eq_zpowers_sup hp hu hv hx hy hspan hind
  have hyU : y ∉ U := by
    intro h
    have hEU : E ≤ U := by
      rw [hE, hv1]
      simp only [Nat.reduceSub, pow_zero, pow_one]
      apply sup_le
      · have hxpU : x ^ p ∈ U := pow_mem_subgroup_of_index_eq U hU x
        exact le_trans (zpowers_x_pow_pred_le_zpowers_x_pow hu1 x)
          ((Subgroup.zpowers_le).mpr hxpU)
      · exact (Subgroup.zpowers_le).mpr h
    exact hUN (hN.2.2 U hU hEU)
  letI : Fact p.Prime := ⟨hp⟩
  letI := Subgroup.normal_of_comm U
  let q : G →* G ⧸ U := QuotientGroup.mk' U
  have hQcard : Nat.card (G ⧸ U) = p := by rw [← U.index_eq_card, hU]
  have hqy : q y ≠ 1 := by
    intro h
    have hyker : y ∈ q.ker := by rw [MonoidHom.mem_ker]; exact h
    rw [QuotientGroup.ker_mk'] at hyker
    exact hyU hyker
  have hqxmem : q x ∈ Subgroup.zpowers (q y) :=
    mem_zpowers_of_prime_card hQcard hqy
  rw [Subgroup.mem_zpowers_iff] at hqxmem
  rcases hqxmem with ⟨i, hiq⟩
  let k : ℤ := -i
  let z : G := x * y ^ k
  have hzq : q z = 1 := by
    change q (x * y ^ (-i)) = 1
    rw [map_mul, map_zpow, ← hiq]
    simp
  have hzU : z ∈ U := by
    have hzker : z ∈ q.ker := by rw [MonoidHom.mem_ker]; exact hzq
    rw [QuotientGroup.ker_mk'] at hzker
    exact hzker
  have hPcard : Nat.card G = p ^ (u + 1) := by
    rw [Nat_card_of_zpowers_sup_top_inf_bot hspan hind, hx, hy, hv1, pow_one, ← pow_succ]
  have hUcard : Nat.card ↥U = p ^ u :=
    (subgroup_index_prime_iff_card_eq_of_card_pow_succ hp hPcard U).mp hU
  have hy' : orderOf y = p := by simpa [hv1] using hy
  have hzorder : orderOf z = p ^ u :=
    orderOf_mul_zpow_right_v1 hp hu hx hy' hind k
  have hHzU : Subgroup.zpowers z ≤ U := (Subgroup.zpowers_le).mpr hzU
  have hUeqz : U = Subgroup.zpowers z := by
    apply Eq.symm
    apply Subgroup.eq_of_le_of_card_ge hHzU
    rw [hUcard, Nat.card_zpowers, hzorder]
  have hknonneg : 0 ≤ k % (p : ℤ) :=
    Int.emod_nonneg k (by exact_mod_cast hp.ne_zero)
  have hklt : k % (p : ℤ) < (p : ℤ) :=
    Int.emod_lt_of_pos k (by exact_mod_cast hp.pos)
  let r : Fin p := ⟨(k % (p : ℤ)).toNat, by
    exact (Int.toNat_lt hknonneg).mpr hklt⟩
  have hmod : y ^ (k % ↑(orderOf y)) = y ^ k := zpow_mod_orderOf y k
  rw [hy'] at hmod
  have hrcast : ((r.val : ℤ)) = k % (p : ℤ) := Int.toNat_of_nonneg hknonneg
  have hykr : y ^ k = y ^ (r.val : ℕ) := by
    calc
      y ^ k = y ^ (k % (p : ℤ)) := hmod.symm
      _ = y ^ ((r.val : ℤ)) := by rw [← hrcast]
      _ = y ^ (r.val : ℕ) := by rw [zpow_natCast]
  have hzr : z = x * y ^ (r.val : ℕ) := by
    dsimp [z]
    rw [hykr]
  exact ⟨r, by rw [hUeqz, hzr]⟩

/- accepted add_to_file helper 24 -/
lemma card_nonN_index_prime_v1 {G : Type*} [CommGroup G] [Finite G]
    {p u v : ℕ} (hp : p.Prime) (hu : 0 < u) (hv : 0 < v)
    (hu1 : 1 < u) (hv1 : v = 1)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p ^ v)
    (hspan : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    Nat.card {U : Subgroup G // U.index = p ∧
      U ≠ Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y} = p := by
  let N : Subgroup G := Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y
  let H : Fin p → Subgroup G := fun r =>
    Subgroup.zpowers (x * y ^ (r.val : ℕ))
  have hPcard : Nat.card G = p ^ (u + 1) := by
    rw [Nat_card_of_zpowers_sup_top_inf_bot hspan hind, hx, hy, hv1, pow_one, ← pow_succ]
  have hy' : orderOf y = p := by simpa [hv1] using hy
  have hHindex : ∀ r : Fin p, (H r).index = p := by
    intro r
    have hzorder : orderOf (x * y ^ (r.val : ℕ)) = p ^ u := by
      simpa [zpow_natCast] using
        (orderOf_mul_zpow_right_v1 hp hu hx hy' hind (((r.val : ℤ))))
    have hHcard : Nat.card ↥(H r) = p ^ u := by
      dsimp [H]
      rw [Nat.card_zpowers, hzorder]
    exact (subgroup_index_prime_iff_card_eq_of_card_pow_succ hp hPcard (H r)).mpr hHcard
  have hHne : ∀ r : Fin p, H r ≠ N := by
    intro r
    exact H_fin_ne_N_v1 hp hu hx hy' hind r
  let S := {U : Subgroup G // U.index = p ∧ U ≠ N}
  let f : Fin p → S := fun r => ⟨H r, hHindex r, hHne r⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply H_fin_injective_v1 hp hu hx hy' hind
    exact congrArg Subtype.val hab
  have hsurj : Function.Surjective f := by
    intro UU
    rcases nonN_eq_H_fin_v1 hp hu hv hu1 hv1 hx hy hspan hind UU.2.1 UU.2.2 with ⟨r, hr⟩
    exact ⟨r, Subtype.ext hr.symm⟩
  let e : Fin p ≃ S := Equiv.ofBijective f ⟨hinj, hsurj⟩
  calc
    Nat.card S = Nat.card (Fin p) := (Nat.card_congr e).symm
    _ = p := Nat.card_fin p

/- accepted add_to_file helper 25 -/
lemma pow_pred_mem_subgroup_of_index_eq {G : Type*} [CommGroup G]
    (U : Subgroup G) {p n : ℕ} (hn : 1 < n) (hindex : U.index = p) (x : G) :
    x ^ (p ^ (n - 1)) ∈ U := by
  have h := pow_mem_subgroup_of_index_eq U hindex (x ^ (p ^ (n - 2)))
  convert h using 1
  rw [← pow_mul]
  congr 1
  rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]

/- accepted add_to_file helper 26 -/
lemma N_mulEquiv_v1 {G : Type*} [CommGroup G]
    {p u : ℕ} (hp : p.Prime) (hu : 0 < u)
    {x y : G}
    (hx : orderOf x = p ^ u) (hy : orderOf y = p)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    let N : Subgroup G := Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y
    Nonempty (N ≃* Multiplicative (ZMod (p ^ (u - 1))) × Multiplicative (ZMod p)) := by
  intro N
  let X : Subgroup G := Subgroup.zpowers (x ^ p)
  let Y : Subgroup G := Subgroup.zpowers y
  have hinf : X ⊓ Y = ⊥ := by
    dsimp [X, Y]
    simpa using zpowers_pow_inf_zpowers_pow_eq_bot hind p 1
  let f := commSubgroupProdHom X Y
  have hrange : f.range = N := by
    dsimp [f, N, X, Y]
    exact commSubgroupProdHom_range (Subgroup.zpowers (x ^ p)) (Subgroup.zpowers y)
  have hinj : Function.Injective f.rangeRestrict := by
    rw [MonoidHom.rangeRestrict_injective_iff]
    dsimp [f]
    exact commSubgroupProdHom_injective hinf
  have hbij : Function.Bijective f.rangeRestrict :=
    ⟨hinj, MonoidHom.rangeRestrict_surjective f⟩
  let eprod : (↥X × ↥Y) ≃* N := by
    let e : (↥X × ↥Y) ≃* f.range := MulEquiv.ofBijective f.rangeRestrict hbij
    rwa [hrange] at e
  have hXcard : Nat.card ↥X = p ^ (u - 1) := by
    dsimp [X]
    rw [Nat.card_zpowers]
    simpa using orderOf_prime_pow_pow hp hx (k := 1) (by omega : 1 ≤ u)
  have hYcard : Nat.card ↥Y = p := by
    dsimp [Y]
    rw [Nat.card_zpowers, hy]
  rcases IsCyclic.exists_generator (α := X) with ⟨gx, hgx⟩
  rcases IsCyclic.exists_generator (α := Y) with ⟨gy, hgy⟩
  let eX : Multiplicative (ZMod (p ^ (u - 1))) ≃* X :=
    zmodMulEquivOfGenerator hgx hXcard
  let eY : Multiplicative (ZMod p) ≃* Y := zmodMulEquivOfGenerator hgy hYcard
  exact ⟨eprod.symm.trans (MulEquiv.prodCongr eX.symm eY.symm)⟩

/- verified submission -/
theorem sylow_rank_two_index_prime_subgroups
    {A : Type*} [CommGroup A] [Finite A]
    {p u v : ℕ} (hp : p.Prime) (hu : 0 < u) (hv : 0 < v) (huv : v ≤ u)
    (P : Sylow p A) (x y : P)
    (hx : orderOf x = p ^ u) (hy : orderOf y = p ^ v)
    (hspan : Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤)
    (hind : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥) :
    let E : Subgroup P := (powMonoidHom p : P →* P).ker
    let N : Subgroup P := Subgroup.zpowers (x ^ p) ⊔ Subgroup.zpowers y
    E = Subgroup.zpowers (x ^ (p ^ (u - 1))) ⊔
          Subgroup.zpowers (y ^ (p ^ (v - 1))) ∧
    (u = 1 ∧ v = 1 →
      ∀ U : Subgroup P, U.index = p ↔ U ≤ E ∧ Nat.card U = p) ∧
    (v = 1 ∧ 1 < u →
      N.index = p ∧ E ≤ N ∧
      (∀ U : Subgroup P, U.index = p → E ≤ U → U = N) ∧
      Nonempty (N ≃* Multiplicative (ZMod (p ^ (u - 1))) × Multiplicative (ZMod p)) ∧
      Nat.card {U : Subgroup P // U.index = p ∧ U ≠ N} = p ∧
      (∀ U : Subgroup P, U.index = p → U ≠ N →
        IsCyclic U ∧ Nat.card U = p ^ u ∧
          U ⊓ E = Subgroup.zpowers (x ^ (p ^ (u - 1))))) ∧
    (1 < v → ∀ U : Subgroup P, U.index = p → E ≤ U) := by
  intro E N
  have hE : E = Subgroup.zpowers (x ^ (p ^ (u - 1))) ⊔
      Subgroup.zpowers (y ^ (p ^ (v - 1))) :=
    pow_ker_eq_zpowers_sup hp hu hv hx hy hspan hind
  refine ⟨hE, ?_, ?_, ?_⟩
  · rintro ⟨hu1, hv1⟩
    have hPcard : Nat.card P = p ^ 2 := by
      calc
        Nat.card P = orderOf x * orderOf y :=
          Nat_card_of_zpowers_sup_top_inf_bot hspan hind
        _ = p ^ 2 := by rw [hx, hy, hu1, hv1]; simpa using (pow_two p).symm
    have hEcard : Nat.card ↥E = p ^ 2 :=
      Nat_card_pow_ker hp hu hv hx hy hspan hind
    have hEtop : E = ⊤ := Subgroup.eq_top_of_card_eq E (by rw [hEcard, hPcard])
    intro U
    rw [hEtop]
    constructor
    · intro hU
      exact ⟨le_top, (subgroup_index_prime_iff_card_prime_of_card_sq hp hPcard U).mp hU⟩
    · intro hU
      exact (subgroup_index_prime_iff_card_prime_of_card_sq hp hPcard U).mpr hU.2
  · rintro ⟨hv1, hu1⟩
    have hNstruct := N_index_mem_unique_v1 hp hu hv hu1 hv1 hx hy hspan hind
    change N.index = p ∧ E ≤ N ∧
      (∀ U : Subgroup P, U.index = p → E ≤ U → U = N) at hNstruct
    have hy' : orderOf y = p := by simpa [hv1] using hy
    have hNiso : Nonempty (N ≃* Multiplicative (ZMod (p ^ (u - 1))) ×
        Multiplicative (ZMod p)) := by
      exact N_mulEquiv_v1 hp hu hx hy' hind
    have hcount : Nat.card {U : Subgroup P // U.index = p ∧ U ≠ N} = p := by
      exact card_nonN_index_prime_v1 hp hu hv hu1 hv1 hx hy hspan hind
    refine ⟨hNstruct.1, hNstruct.2.1, hNstruct.2.2, hNiso, hcount, ?_⟩
    intro U hU hUN
    exact cyclic_nonN_v1 hp hu hv hu1 hv1 hx hy hspan hind hU hUN
  · intro hv1
    intro U hU
    rw [hE]
    apply sup_le
    · rw [Subgroup.zpowers_le]
      exact pow_pred_mem_subgroup_of_index_eq U (by omega : 1 < u) hU x
    · rw [Subgroup.zpowers_le]
      exact pow_pred_mem_subgroup_of_index_eq U hv1 hU y


#check_dependency_graph "sylow_rank_two_index_prime_subgroups" against "{\"edges\":[{\"conclusion\":{\"name\":\"hE\",\"statement\":\"E = Subgroup.zpowers (x ^ p ^ (u - 1)) ⊔ Subgroup.zpowers (y ^ p ^ (v - 1))\"},\"graphEdgeId\":\"h_001_he\",\"premises\":[{\"name\":\"hp\",\"statement\":\"Nat.Prime p\"},{\"name\":\"hu\",\"statement\":\"0 < u\"},{\"name\":\"hv\",\"statement\":\"0 < v\"},{\"name\":\"hx\",\"statement\":\"orderOf x = p ^ u\"},{\"name\":\"hy\",\"statement\":\"orderOf y = p ^ v\"},{\"name\":\"hspan\",\"statement\":\"Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤\"},{\"name\":\"hind\",\"statement\":\"Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥\"}],\"rawEdgeId\":\"telescope_19\"},{\"conclusion\":{\"name\":\"goal\",\"statement\":\"E = Subgroup.zpowers (x ^ p ^ (u - 1)) ⊔ Subgroup.zpowers (y ^ p ^ (v - 1)) ∧ (u = 1 ∧ v = 1 → ∀ (U : Subgroup ↥↑P), U.index = p ↔ U ≤ E ∧ Nat.card ↥U = p) ∧ (v = 1 ∧ 1 < u → N.index = p ∧ E ≤ N ∧ (∀ (U : Subgroup ↥↑P), U.index = p → E ≤ U → U = N) ∧ Nonempty (↥N ≃* Multiplicative (ZMod (p ^ (u - 1))) × Multiplicative (ZMod p)) ∧ Nat.card { U // U.index = p ∧ U ≠ N } = p ∧ ∀ (U : Subgroup ↥↑P), U.index = p → U ≠ N → IsCyclic ↥U ∧ Nat.card ↥U = p ^ u ∧ U ⊓ E = Subgroup.zpowers (x ^ p ^ (u - 1))) ∧ (1 < v → ∀ (U : Subgroup ↥↑P), U.index = p → E ≤ U)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"<generated-instance>\",\"statement\":\"Finite A\"},{\"name\":\"hp\",\"statement\":\"Nat.Prime p\"},{\"name\":\"hu\",\"statement\":\"0 < u\"},{\"name\":\"hv\",\"statement\":\"0 < v\"},{\"name\":\"huv\",\"statement\":\"v ≤ u\"},{\"name\":\"hx\",\"statement\":\"orderOf x = p ^ u\"},{\"name\":\"hy\",\"statement\":\"orderOf y = p ^ v\"},{\"name\":\"hspan\",\"statement\":\"Subgroup.zpowers x ⊔ Subgroup.zpowers y = ⊤\"},{\"name\":\"hind\",\"statement\":\"Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥\"},{\"name\":\"hE\",\"statement\":\"E = Subgroup.zpowers (x ^ p ^ (u - 1)) ⊔ Subgroup.zpowers (y ^ p ^ (v - 1))\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p2247_sylow_rank_two_index_prime_subgroups\",\"reconstructedProofSha256\":\"95be45d03e9821e2b759a62abd02ffbb2f228a34dc84b4acd36cb28361c24923\",\"selectedEdgeCount\":2,\"theoremName\":\"sylow_rank_two_index_prime_subgroups\",\"topologySha256\":\"1c6ca46bbda1eeac93fb6cf04404be324d1119b830fc90bfd6f96fc2ea3164f9\"}"
