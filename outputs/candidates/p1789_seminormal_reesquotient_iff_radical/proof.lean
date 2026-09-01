import Mathlib

/- accepted add_to_file helper 1 -/
lemma pow_eq_zero_of_le_pow_eq_zero {M : Type*} [MonoidWithZero M] {x : M} {n k : ℕ}
    (h : n ≤ k) (hx : x ^ n = 0) : x ^ k = 0 := by
  rw [← Nat.add_sub_of_le h, pow_add, hx, zero_mul]

lemma pow_eq_zero_of_reduced {M : Type*} [CommMonoidWithZero M]
    (hred : ∀ a b : M, a ^ 2 = b ^ 2 → a ^ 3 = b ^ 3 → a = b)
    {x : M} : ∀ {n : ℕ}, 1 ≤ n → x ^ n = 0 → x = 0 := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih h1 hx
  by_cases hn : n ≤ 1
  · have hn_eq : n = 1 := by omega
    subst n
    simpa using hx
  · let m := (n + 1) / 2
    have hn2 : 2 ≤ n := by omega
    have hm1 : 1 ≤ m := by
      dsimp [m]
      omega
    have hmn : m < n := by
      dsimp [m]
      omega
    have hn2m : n ≤ 2 * m := by
      dsimp [m]
      omega
    have hn3m : n ≤ 3 * m := by
      dsimp [m]
      omega
    have hx2m : x ^ (2 * m) = 0 := pow_eq_zero_of_le_pow_eq_zero hn2m hx
    have hx3m : x ^ (3 * m) = 0 := pow_eq_zero_of_le_pow_eq_zero hn3m hx
    have hsq : (x ^ m) ^ 2 = (0 : M) ^ 2 := by
      calc
        (x ^ m) ^ 2 = x ^ (m * 2) := by rw [pow_mul]
        _ = x ^ (2 * m) := by rw [Nat.mul_comm]
        _ = 0 := hx2m
        _ = (0 : M) ^ 2 := by simp
    have hcube : (x ^ m) ^ 3 = (0 : M) ^ 3 := by
      calc
        (x ^ m) ^ 3 = x ^ (m * 3) := by rw [pow_mul]
        _ = x ^ (3 * m) := by rw [Nat.mul_comm]
        _ = 0 := hx3m
        _ = (0 : M) ^ 3 := by simp
    exact ih m hmn hm1 (hred (x ^ m) 0 hsq hcube)

/- accepted add_to_file helper 2 -/
lemma monoidWithZeroHom_eq_zero_iff_mem_of_fiber {A B : Type*}
    [CommMonoidWithZero A] [CommMonoidWithZero B]
    (q : A →*₀ B) (I : SemigroupIdeal A) (hI_zero : (0 : A) ∈ I)
    (hq_fiber : ∀ a b : A, q a = q b ↔ a = b ∨ (a ∈ I ∧ b ∈ I))
    (a : A) : q a = 0 ↔ a ∈ I := by
  constructor
  · intro ha
    have hfiber : q a = q 0 := by simpa using ha
    rcases (hq_fiber a 0).mp hfiber with rfl | hmem
    · exact hI_zero
    · exact hmem.1
  · intro ha
    have hfiber : q a = q 0 :=
      (hq_fiber a 0).mpr (Or.inr ⟨ha, hI_zero⟩)
    simpa using hfiber

/- verified submission -/
theorem seminormal_reesQuotient_iff_radical
    {A C B : Type*}
    [CommMonoidWithZero A] [CommMonoidWithZero C] [IsCancelMulZero C]
    [CommMonoidWithZero B]
    (J : SemigroupIdeal C)
    (hJ_zero : (0 : C) ∈ J)
    (p : C →*₀ A)
    (hp_surjective : Function.Surjective p)
    (hp_fiber : ∀ c d : C, p c = p d ↔ c = d ∨ (c ∈ J ∧ d ∈ J))
    (hA :
      (∀ a b : A, a ^ 2 = b ^ 2 → a ^ 3 = b ^ 3 → a = b) ∧
      (∀ x y : A, x ^ 3 = y ^ 2 → ∃ z : A, x = z ^ 2 ∧ y = z ^ 3))
    (I : SemigroupIdeal A)
    (hI_zero : (0 : A) ∈ I)
    (q : A →*₀ B)
    (hq_surjective : Function.Surjective q)
    (hq_fiber : ∀ a b : A, q a = q b ↔ a = b ∨ (a ∈ I ∧ b ∈ I)) :
    ((∀ a b : B, a ^ 2 = b ^ 2 → a ^ 3 = b ^ 3 → a = b) ∧
        (∀ x y : B, x ^ 3 = y ^ 2 → ∃ z : B, x = z ^ 2 ∧ y = z ^ 3)) ↔
      ∀ a : A, (∃ n : ℕ, 1 ≤ n ∧ a ^ n ∈ I) → a ∈ I := by
  let qzero : ∀ a : A, q a = 0 ↔ a ∈ I :=
    fun a => monoidWithZeroHom_eq_zero_iff_mem_of_fiber q I hI_zero hq_fiber a
  constructor
  · intro hB a ha
    rcases ha with ⟨n, hn, han⟩
    have hqan : q (a ^ n) = 0 := (qzero (a ^ n)).mpr han
    have hpow : (q a) ^ n = 0 := by
      calc
        (q a) ^ n = q (a ^ n) := by rw [map_pow]
        _ = 0 := hqan
    have hqa : q a = 0 := pow_eq_zero_of_reduced hB.1 hn hpow
    exact (qzero a).mp hqa
  · intro hrad
    have q_eq_of_mem : ∀ {a b : A}, a ∈ I → b ∈ I → q a = q b := by
      intro a b ha hb
      exact (hq_fiber a b).mpr (Or.inr ⟨ha, hb⟩)
    have cube_mem_of_sq_mem : ∀ {a : A}, a ^ 2 ∈ I → a ^ 3 ∈ I := by
      intro a ha
      have hmul := I.mul_mem a ha
      simpa [pow_two, pow_three] using hmul
    constructor
    · intro x y h2 h3
      obtain ⟨a, rfl⟩ := hq_surjective x
      obtain ⟨b, rfl⟩ := hq_surjective y
      have h2A : q (a ^ 2) = q (b ^ 2) := by
        simpa [map_pow] using h2
      have h3A : q (a ^ 3) = q (b ^ 3) := by
        simpa [map_pow] using h3
      rcases (hq_fiber (a ^ 2) (b ^ 2)).mp h2A with hpow2 | hpow2I
      · rcases (hq_fiber (a ^ 3) (b ^ 3)).mp h3A with hpow3 | hpow3I
        · have hab : a = b := hA.1 a b hpow2 hpow3
          simpa [hab]
        · have haI : a ∈ I := hrad a ⟨3, by norm_num, hpow3I.1⟩
          have hbI : b ∈ I := hrad b ⟨3, by norm_num, hpow3I.2⟩
          exact q_eq_of_mem haI hbI
      · have ha3I : a ^ 3 ∈ I := cube_mem_of_sq_mem hpow2I.1
        have hb3I : b ^ 3 ∈ I := cube_mem_of_sq_mem hpow2I.2
        have haI : a ∈ I := hrad a ⟨3, by norm_num, ha3I⟩
        have hbI : b ∈ I := hrad b ⟨3, by norm_num, hb3I⟩
        exact q_eq_of_mem haI hbI
    · intro x y hxy
      obtain ⟨a, rfl⟩ := hq_surjective x
      obtain ⟨b, rfl⟩ := hq_surjective y
      have hxyA : q (a ^ 3) = q (b ^ 2) := by
        simpa [map_pow] using hxy
      rcases (hq_fiber (a ^ 3) (b ^ 2)).mp hxyA with hpow | hpowI
      · obtain ⟨z, haz, hbz⟩ := hA.2 a b hpow
        refine ⟨q z, ?_, ?_⟩
        · calc
            q a = q (z ^ 2) := congrArg q haz
            _ = (q z) ^ 2 := by rw [map_pow]
        · calc
            q b = q (z ^ 3) := congrArg q hbz
            _ = (q z) ^ 3 := by rw [map_pow]
      · have haI : a ∈ I := hrad a ⟨3, by norm_num, hpowI.1⟩
        have hbI : b ∈ I := hrad b ⟨2, by norm_num, hpowI.2⟩
        have hqa : q a = 0 := (qzero a).mpr haI
        have hqb : q b = 0 := (qzero b).mpr hbI
        refine ⟨0, ?_, ?_⟩
        · simpa using hqa
        · simpa using hqb
