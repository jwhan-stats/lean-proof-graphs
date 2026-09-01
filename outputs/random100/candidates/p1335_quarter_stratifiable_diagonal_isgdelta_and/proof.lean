import Mathlib

/- verified submission -/
theorem quarter_stratifiable_diagonal_isGDelta_and_countable_pseudocharacter
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (g : ℕ → X → Set X)
    (hg_open : ∀ n a, IsOpen (g n a))
    (hg_cover : ∀ n, ⋃ a, g n a = Set.univ)
    (hg_converges : ∀ (x : X) (a : ℕ → X),
      (∀ n, x ∈ g n (a n)) → Filter.Tendsto a Filter.atTop (nhds x)) :
    (∃ G : ℕ → Set (X × X),
      (∀ n, IsOpen (G n)) ∧
      Set.diagonal X = ⋂ n, G n) ∧
    ∀ x : X, ∃ V : ℕ → Set X,
      (∀ n, IsOpen (V n) ∧ x ∈ V n) ∧
      ⋂ n, V n = {x} := by
  classical
  constructor
  · refine ⟨fun n => ⋃ a, (g n a) ×ˢ (g n a), ?_, ?_⟩
    · intro n
      exact isOpen_iUnion fun a => (hg_open n a).prod (hg_open n a)
    · ext p
      constructor
      · intro hp
        rw [Set.mem_diagonal_iff] at hp
        rw [Set.mem_iInter]
        intro n
        have hc : p.1 ∈ ⋃ a, g n a := by
          rw [hg_cover n]
          trivial
        rw [Set.mem_iUnion] at hc
        rcases hc with ⟨a, hpa⟩
        rw [Set.mem_iUnion]
        exact ⟨a, by
          rw [Set.mem_prod]
          exact ⟨hpa, by simpa [hp] using hpa⟩⟩
      · intro hp
        rw [Set.mem_diagonal_iff]
        have hchoice : ∀ n, ∃ a, p.1 ∈ g n a ∧ p.2 ∈ g n a := by
          intro n
          have hpn : p ∈ ⋃ a, (g n a) ×ˢ (g n a) := Set.mem_iInter.mp hp n
          rw [Set.mem_iUnion] at hpn
          rcases hpn with ⟨a, hpa⟩
          exact ⟨a, Set.mem_prod.mp hpa⟩
        choose a ha using hchoice
        have hlim₁ := hg_converges p.1 a fun n => (ha n).1
        have hlim₂ := hg_converges p.2 a fun n => (ha n).2
        exact tendsto_nhds_unique hlim₁ hlim₂
  · intro x
    have hchoice : ∀ n, ∃ a, x ∈ g n a := by
      intro n
      have hx : x ∈ ⋃ a, g n a := by
        rw [hg_cover n]
        trivial
      rw [Set.mem_iUnion] at hx
      exact hx
    choose a ha using hchoice
    refine ⟨fun n => g n (a n), ?_, ?_⟩
    · intro n
      exact ⟨hg_open n (a n), ha n⟩
    · ext y
      constructor
      · intro hy
        have hy' : ∀ n, y ∈ g n (a n) := Set.mem_iInter.mp hy
        have hlimy := hg_converges y a hy'
        have hlimx := hg_converges x a ha
        have hyx : y = x := tendsto_nhds_unique hlimy hlimx
        simpa [hyx]
      · intro hy
        have hyx : y = x := by simpa using hy
        rw [Set.mem_iInter]
        intro n
        simpa [hyx] using ha n
