import Mathlib

/- accepted add_to_file helper 1 -/
lemma derivation_mono_of_finite_generation
    {W : Type*} (D : Set W → Set W)
    (hD : ∀ (S : Set W) (x : W),
      x ∈ D S ↔ ∃ F : Set W, F.Finite ∧ F ⊆ S ∧ x ∈ D F)
    {S T : Set W} (hST : S ⊆ T) : D S ⊆ D T := by
  intro x hx
  rw [hD S x] at hx
  rw [hD T x]
  rcases hx with ⟨F, hFfin, hFS, hxF⟩
  exact ⟨F, hFfin, hFS.trans hST, hxF⟩

lemma finite_support_of_derivation
    {W : Type*} (D : Set W → Set W)
    (hD : ∀ (S : Set W) (x : W),
      x ∈ D S ↔ ∃ F : Set W, F.Finite ∧ F ⊆ S ∧ x ∈ D F)
    {U B : Set W} (hB : B.Finite) (hsub : B ⊆ D U) :
    ∃ C : Set W, C.Finite ∧ C ⊆ U ∧ B ⊆ D C := by
  classical
  have hchoice : ∀ x : B, ∃ F : Set W,
      F.Finite ∧ F ⊆ U ∧ (x : W) ∈ D F := by
    intro x
    exact (hD U (x : W)).1 (hsub x.property)
  choose F hF using hchoice
  letI : Fintype B := hB.fintype
  refine ⟨⋃ x : B, F x, Set.finite_iUnion (fun x : B => (hF x).1), ?_, ?_⟩
  · intro y hy
    rw [Set.mem_iUnion] at hy
    rcases hy with ⟨x, hyx⟩
    exact (hF x).2.1 hyx
  · intro x hx
    exact derivation_mono_of_finite_generation D hD
      (Set.subset_iUnion (fun x : B => F x) ⟨x, hx⟩)
      (hF ⟨x, hx⟩).2.2

/- accepted add_to_file helper 2 -/
lemma finite_support_chain_forall
    {W : Type*} (D : Set W → Set W)
    (hD : ∀ (S : Set W) (x : W),
      x ∈ D S ↔ ∃ F : Set W, F.Finite ∧ F ⊆ S ∧ x ∈ D F)
    (A : Set W) :
    ∀ n : ℕ, 1 ≤ n → ∀ B : Set W, B.Finite → B ⊆ (D^[n]) A →
      ∃ S : ℕ → Set W,
        (∀ k < n, (S k).Finite) ∧
        (∀ k < n, S k ⊆ (D^[k]) A) ∧
        B ⊆ D (S (n - 1)) ∧
        ∀ k, k + 1 < n → S (k + 1) ⊆ D (S k) := by
  intro n
  induction n with
  | zero =>
      intro hn
      omega
  | succ m ihm =>
      intro hm B hB hsub
      have hsubD : B ⊆ D ((D^[m]) A) := by
        simpa [Function.iterate_succ_apply'] using hsub
      rcases finite_support_of_derivation D hD hB hsubD with
        ⟨C, hCfin, hCsub, hBDC⟩
      cases m with
      | zero =>
          refine ⟨fun _ => C, ?_, ?_, ?_, ?_⟩
          · intro k hk
            exact hCfin
          · intro k hk
            have hk0 : k = 0 := by omega
            subst k
            simpa using hCsub
          · simpa using hBDC
          · intro k hk
            exfalso
            omega
      | succ r =>
          rcases ihm (by omega) C hCfin hCsub with
            ⟨T, hTfin, hTsub, hCT, hTchain⟩
          let S : ℕ → Set W := fun k => if k ≤ r then T k else C
          refine ⟨S, ?_, ?_, ?_, ?_⟩
          · intro k hk
            by_cases hkr : k ≤ r
            · have hklt : k < r + 1 := Nat.lt_succ_of_le hkr
              simp [S, hkr, hTfin k hklt]
            · have hkeq : k = r + 1 := by omega
              subst k
              simp [S, hCfin]
          · intro k hk
            by_cases hkr : k ≤ r
            · have hklt : k < r + 1 := Nat.lt_succ_of_le hkr
              simp [S, hkr, hTsub k hklt]
            · have hkeq : k = r + 1 := by omega
              subst k
              simp [S]
              simpa [Function.iterate_succ_apply] using hCsub
          · simp [S, hBDC]
          · intro k hk
            by_cases hkr : k + 1 ≤ r
            · have hk1lt : k + 1 < r + 1 := Nat.lt_succ_of_le hkr
              have hklt : k ≤ r := by omega
              simpa [S, hkr, hklt] using hTchain k hk1lt
            · have hk1 : k + 1 = r + 1 := by omega
              have hkeq : k = r := by omega
              subst k
              have hrle : r ≤ r := le_rfl
              simpa [S, hrle] using hCT

/- verified submission -/
theorem finite_support_derivation
    {W : Type*} (D : Set W → Set W)
    (hD : ∀ (S : Set W) (x : W),
      x ∈ D S ↔ ∃ F : Set W, F.Finite ∧ F ⊆ S ∧ x ∈ D F)
    (A : Set W) (n : ℕ) (P : W)
    (hn : 1 ≤ n) (hP : P ∈ (D^[n]) A) :
    ∃ S : ℕ → Set W,
      (∀ k < n, (S k).Finite) ∧
      (∀ k < n, S k ⊆ (D^[k]) A) ∧
      P ∈ D (S (n - 1)) ∧
      ∀ k, k + 1 < n → S (k + 1) ⊆ D (S k) := by
  have hsub : {P} ⊆ (D^[n]) A := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact hP
  rcases finite_support_chain_forall D hD A n hn {P} (Set.finite_singleton P) hsub with
    ⟨S, hSfin, hSsub, hStop, hSchain⟩
  exact ⟨S, hSfin, hSsub, hStop rfl, hSchain⟩
