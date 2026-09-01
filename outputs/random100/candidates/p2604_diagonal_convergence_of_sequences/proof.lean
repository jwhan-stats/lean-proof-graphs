import Mathlib

/- verified submission -/
import Mathlib

open Filter Topology

theorem diagonal_convergence_of_sequences
    {E : Type*} [MetricSpace E]
    (a : ℕ → ℕ → E) (aInf : ℕ → E) (aInfInf : E)
    (ha : ∀ m : ℕ, Filter.Tendsto (a m) Filter.atTop (nhds (aInf m)))
    (hInf : Filter.Tendsto aInf Filter.atTop (nhds aInfInf)) :
    ∃ b : ℕ → ℕ,
      Monotone b ∧
      Filter.Tendsto b Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun n : ℕ => a (b n) n) Filter.atTop (nhds aInfInf) := by
  choose N hN using fun (m : ℕ) (k : ℕ) =>
    Metric.tendsto_atTop.mp (ha m) (1 / ((k : ℝ) + 1))
      (one_div_pos.mpr (Nat.cast_add_one_pos k))
  let A : ℕ → ℕ := fun m =>
    max m ((Finset.range (m + 1)).sup fun k => N m k)
  let b : ℕ → ℕ := fun n => Nat.findGreatest (fun m => A m ≤ n) n
  have hbmono : Monotone b := by
    intro m n hmn
    dsimp [b]
    calc
      Nat.findGreatest (fun k => A k ≤ m) m
          ≤ Nat.findGreatest (fun k => A k ≤ m) n :=
        Nat.findGreatest_mono_right (fun k => A k ≤ m) hmn
      _ ≤ Nat.findGreatest (fun k => A k ≤ n) n :=
        Nat.findGreatest_mono_left (fun k hk => le_trans hk hmn) n
  have hbtop : Filter.Tendsto b Filter.atTop Filter.atTop := by
    rw [Filter.tendsto_atTop_atTop_iff_of_monotone hbmono]
    intro m
    refine ⟨A m, ?_⟩
    dsimp [b]
    exact Nat.le_findGreatest (P := fun k => A k ≤ A m) (le_max_left _ _) le_rfl
  refine ⟨b, hbmono, hbtop, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_one_div_lt (K := ℝ) (show 0 < ε / 2 by positivity)
  obtain ⟨L, hL⟩ := Metric.tendsto_atTop.mp hInf (ε / 2) (by positivity)
  obtain ⟨Nb, hNb⟩ := Filter.tendsto_atTop_atTop.mp hbtop (max K L)
  refine ⟨max (A 0) Nb, ?_⟩
  intro n hn
  have hA0n : A 0 ≤ n := le_trans (le_max_left _ _) hn
  have hAbn : A (b n) ≤ n := by
    dsimp [b]
    exact Nat.findGreatest_spec (P := fun m => A m ≤ n) (Nat.zero_le n) hA0n
  have hbn_ge : max K L ≤ b n := hNb n (le_trans (le_max_right _ _) hn)
  have hKb : K ≤ b n := le_trans (le_max_left _ _) hbn_ge
  have hLb : L ≤ b n := le_trans (le_max_right _ _) hbn_ge
  have hNA : N (b n) (b n) ≤ A (b n) := by
    have hmem : b n ∈ Finset.range (b n + 1) := by simp
    have hs := Finset.le_sup (s := Finset.range (b n + 1))
      (f := fun k => N (b n) k) hmem
    dsimp [A]
    exact le_trans hs (le_max_right _ _)
  have hfirst : dist (a (b n) n) (aInf (b n)) < 1 / ((b n : ℝ) + 1) :=
    hN (b n) (b n) n (le_trans hNA hAbn)
  have hcast : (K : ℝ) + 1 ≤ (b n : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ hKb
  have hrec : 1 / ((b n : ℝ) + 1) ≤ 1 / ((K : ℝ) + 1) :=
    one_div_le_one_div_of_le (Nat.cast_add_one_pos K) hcast
  have hfirst' : dist (a (b n) n) (aInf (b n)) < ε / 2 :=
    lt_trans (lt_of_lt_of_le hfirst hrec) hK
  have hsecond : dist (aInf (b n)) aInfInf < ε / 2 := hL (b n) hLb
  calc
    dist (a (b n) n) aInfInf
        ≤ dist (a (b n) n) (aInf (b n)) + dist (aInf (b n)) aInfInf :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hfirst' hsecond
    _ = ε := by ring
