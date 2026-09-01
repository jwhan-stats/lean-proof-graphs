import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1722_hirzebruch_jung_large_entries_at_most_two
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 68ed2744cdb1d7035722b828fa61040478e1c5ad3b5b31aff3bcf59ad48149a7
-- reconstructed_proof_sha256: a53b118b316b0c237f4fe8c3638b0137ad1475c8d729d90af9cb23d5b8d10a2d
-- selected_edge_count: 1

/- accepted add_to_file helper 1 -/

def hjCont : List ℤ → ℤ × ℤ
  | [] => (1, 0)
  | x :: xs =>
      let y := hjCont xs
      (x * y.1 - y.2, y.1)

lemma hjCont_bounds (xs : List ℤ) (h : ∀ x ∈ xs, 2 ≤ x) :
    0 < (hjCont xs).1 ∧
    0 ≤ (hjCont xs).2 ∧
    (hjCont xs).2 ≤ (hjCont xs).1 ∧
    (xs.map fun x => x - 1).prod ≤ (hjCont xs).1 := by
  induction xs with
  | nil => simp [hjCont]
  | cons x xs ih =>
      have hx : 2 ≤ x := h x (by simp)
      have hxs : ∀ y ∈ xs, 2 ≤ y := fun y hy => h y (by simp [hy])
      rcases ih hxs with ⟨hu_pos, hv_nonneg, hvu, hprod⟩
      set u := (hjCont xs).1
      set v := (hjCont xs).2
      have hu_nonneg : 0 ≤ u := le_of_lt hu_pos
      have hxu : 2 * u ≤ x * u := mul_le_mul_of_nonneg_right hx hu_nonneg
      have hxm1_nonneg : 0 ≤ x - 1 := by linarith
      have hmul : (x - 1) * (xs.map fun y => y - 1).prod ≤ (x - 1) * u :=
        mul_le_mul_of_nonneg_left hprod hxm1_nonneg
      have hstep : (x - 1) * u ≤ x * u - v := by nlinarith
      simp [hjCont]
      constructor
      · nlinarith
      constructor
      · exact hu_nonneg
      constructor
      · nlinarith
      · exact le_trans hmul hstep

lemma hjCont_snd_pos_of_ne_nil (xs : List ℤ) (h : ∀ x ∈ xs, 2 ≤ x) (hne : xs ≠ []) :
    0 < (hjCont xs).2 := by
  cases xs with
  | nil => contradiction
  | cons x xs =>
      simp [hjCont]
      exact (hjCont_bounds xs (fun y hy => h y (by simp [hy]))).1

lemma hjCont_gcd (xs : List ℤ) :
    (hjCont xs).1.gcd (hjCont xs).2 = 1 := by
  induction xs with
  | nil => simp [hjCont]
  | cons x xs ih =>
      simp [hjCont]
      rw [Int.gcd_comm]
      exact ih

lemma hj_fold_eq_div (xs : List ℤ) (h : ∀ x ∈ xs, 2 ≤ x) :
    (xs.map fun x : ℤ => (x : ℚ)).foldr (fun x r => x - 1 / r) 0 =
      ((hjCont xs).1 : ℚ) / ((hjCont xs).2 : ℚ) := by
  induction xs with
  | nil => simp [hjCont]
  | cons x xs ih =>
      have hxs : ∀ y ∈ xs, 2 ≤ y := fun y hy => h y (by simp [hy])
      have hb := hjCont_bounds xs hxs
      have hN : ((hjCont xs).1 : ℚ) ≠ 0 := by
        exact_mod_cast (ne_of_gt hb.1)
      rw [List.map_cons, List.foldr_cons, ih hxs]
      simp [hjCont]
      field_simp [hN]

lemma triple_tail_sum_le_prod_add_two (x y z : ℤ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (t : List ℤ) (ht : ∀ w ∈ t, 1 ≤ w) :
    5 * (x + y + z + t.sum) ≤
      (x + 2) * (y + 2) * (z + 2) * (t.map fun u => u + 2).prod := by
  induction t with
  | nil =>
      simp
      nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy),
        mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hz),
        mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr hz)]
  | cons w t ih =>
      have hw : 1 ≤ w := ht w (by simp)
      have ht' : ∀ u ∈ t, 1 ≤ u := by
        intro u hu
        exact ht u (by simp [hu])
      have hS : 3 ≤ x + y + z + t.sum := by
        have hnon : 0 ≤ t.sum := List.sum_nonneg (by
          intro u hu
          exact le_trans (by norm_num : (0:ℤ) ≤ 1) (ht' u hu))
        nlinarith
      have hP := ih ht'
      simp [List.sum_cons, List.map_cons, List.prod_cons]
      nlinarith

lemma list_sum_le_prod_add_two (xs : List ℤ)
    (hpos : ∀ x ∈ xs, 1 ≤ x) (hlen : 3 ≤ xs.length) :
    5 * xs.sum ≤ (xs.map fun x => x + 2).prod := by
  have hne : xs ≠ [] := by
    intro h
    rw [h] at hlen
    norm_num at hlen
  rcases List.exists_cons_of_ne_nil hne with ⟨x, xs₁, rfl⟩
  have hlen₁ : 2 ≤ xs₁.length := by
    simpa using hlen
  have hne₁ : xs₁ ≠ [] := by
    intro h
    rw [h] at hlen₁
    norm_num at hlen₁
  rcases List.exists_cons_of_ne_nil hne₁ with ⟨y, xs₂, rfl⟩
  have hlen₂ : 1 ≤ xs₂.length := by
    simpa using hlen₁
  have hne₂ : xs₂ ≠ [] := by
    intro h
    rw [h] at hlen₂
    norm_num at hlen₂
  rcases List.exists_cons_of_ne_nil hne₂ with ⟨z, t, rfl⟩
  have hx : 1 ≤ x := hpos x (by simp)
  have hy : 1 ≤ y := hpos y (by simp)
  have hz : 1 ≤ z := hpos z (by simp)
  have ht : ∀ w ∈ t, 1 ≤ w := by
    intro w hw
    exact hpos w (by simp [hw])
  have h := triple_tail_sum_le_prod_add_two x y z hx hy hz t ht
  simpa [List.sum_cons, List.map_cons, List.prod_cons, add_assoc, add_comm, add_left_comm,
    mul_assoc] using h

lemma finset_five_sum_excess_le_prod_sub_one {n : ℕ} (a : Fin n → ℤ)
    (ha : ∀ i, 2 ≤ a i)
    (F : Finset (Fin n)) (hF : F ⊆ Finset.univ.filter (fun i => 3 < a i))
    (hcard : 3 ≤ F.card) :
    5 * ∑ i ∈ F, (a i - 3) ≤ ∏ i ∈ Finset.univ, (a i - 1) := by
  let xs := F.toList.map (fun i => a i - 3)
  have hpos : ∀ x ∈ xs, 1 ≤ x := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
    have hiF : i ∈ F := by
      simpa using hi
    have hbig : 3 < a i := by
      have hiu : i ∈ Finset.univ.filter (fun j => 3 < a j) := hF hiF
      simpa using hiu
    linarith
  have hlen : 3 ≤ xs.length := by
    simp [xs, hcard]
  have hlist := list_sum_le_prod_add_two xs hpos hlen
  have hsum : xs.sum = ∑ i ∈ F, (a i - 3) := by
    simp [xs]
  have hprodF : (xs.map fun x => x + 2).prod = ∏ i ∈ F, (a i - 1) := by
    simp [xs]
    apply Finset.prod_congr rfl
    intro i hi
    ring
  have hFprod : 5 * ∑ i ∈ F, (a i - 3) ≤ ∏ i ∈ F, (a i - 1) := by
    simpa [hsum, hprodF] using hlist
  have hsubset : (∏ i ∈ F, (a i - 1)) ≤ ∏ i ∈ Finset.univ, (a i - 1) := by
    apply Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ F)
    · intro i hi
      have := ha i
      linarith
    · intro i hi hnot
      have := ha i
      linarith
  exact le_trans hFprod hsubset

/- verified submission -/
theorem hirzebruch_jung_large_entries_at_most_two
    (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℤ)
    (ha : ∀ i, 2 ≤ a i)
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q)
    (hfrac : (List.ofFn fun i => (a i : ℚ)).foldr
      (fun x r => x - 1 / r) 0 = (p : ℚ) / (q : ℚ))
    (hS : (2 * (p : ℚ)) / 9 <
      ∑ i ∈ Finset.univ.filter (fun i => 3 < a i), ((a i - 3 : ℤ) : ℚ)) :
    (Finset.univ.filter (fun i => 3 < a i)).card ≤ 2 := by
  by_contra hcardle
  have hcard3 : 3 ≤ (Finset.univ.filter (fun i => 3 < a i)).card := by
    omega
  let L : List ℤ := List.ofFn a
  have hL : ∀ x ∈ L, 2 ≤ x := by
    intro x hx
    rw [List.mem_ofFn] at hx
    rcases hx with ⟨i, rfl⟩
    exact ha i
  have hcomb := finset_five_sum_excess_le_prod_sub_one a ha
    (Finset.univ.filter (fun i => 3 < a i)) (fun i hi => hi) hcard3
  have hb := hjCont_bounds L hL
  have hprod_eq : (L.map fun x : ℤ => x - 1).prod = ∏ i ∈ Finset.univ, (a i - 1) := by
    simp [L, List.map_ofFn]
    rw [List.prod_ofFn]
    rfl
  have hSN : 5 * ∑ i ∈ Finset.univ.filter (fun i => 3 < a i), (a i - 3) ≤ (hjCont L).1 := by
    exact le_trans (by simpa [hprod_eq] using hcomb) hb.2.2.2
  have hcf : (List.ofFn fun i => (a i : ℚ)).foldr (fun x r => x - 1 / r) 0 =
      ((hjCont L).1 : ℚ) / ((hjCont L).2 : ℚ) := by
    simpa [L] using hj_fold_eq_div L hL
  have hLne : L ≠ [] := by
    intro hnil
    have hlen : L.length = n := by simp [L]
    have hzero : L.length = 0 := by simp [hnil]
    omega
  have hDpos : 0 < (hjCont L).2 := hjCont_snd_pos_of_ne_nil L hL hLne
  have hgcd : (hjCont L).1.gcd (hjCont L).2 = 1 := hjCont_gcd L
  have hco : (hjCont L).1.natAbs.Coprime (hjCont L).2.natAbs := by
    rw [Nat.coprime_iff_gcd_eq_one]
    simpa [Int.gcd] using hgcd
  have hNnum : (((hjCont L).1 : ℚ) / ((hjCont L).2 : ℚ)).num = (hjCont L).1 :=
    Rat.num_div_eq_of_coprime hDpos hco
  have hpqInt : ((p : ℤ).natAbs).Coprime ((q : ℤ).natAbs) := by
    simpa using hpq
  have hpnum : ((p : ℚ) / (q : ℚ)).num = (p : ℤ) := by
    have h := Rat.num_div_eq_of_coprime (show (0 : ℤ) < (q : ℤ) by exact_mod_cast hq) hpqInt
    simpa using h
  have hNp : (hjCont L).1 = (p : ℤ) := by
    calc
      (hjCont L).1 = (((hjCont L).1 : ℚ) / ((hjCont L).2 : ℚ)).num := hNnum.symm
      _ = ((p : ℚ) / (q : ℚ)).num := by
        congr 1
        exact hcf.symm.trans hfrac
      _ = (p : ℤ) := hpnum
  rw [hNp] at hSN
  let S : ℤ := ∑ i ∈ Finset.univ.filter (fun i => 3 < a i), (a i - 3)
  have hSNp : (5 : ℤ) * S ≤ (p : ℤ) := by
    simpa [S] using hSN
  have hSNq : (5 : ℚ) * (S : ℚ) ≤ (p : ℚ) := by
    exact_mod_cast hSNp
  have hsumq : (∑ i ∈ Finset.univ.filter (fun i => 3 < a i), ((a i - 3 : ℤ) : ℚ)) = (S : ℚ) := by
    simp [S]
  have hSq : (2 * (p : ℚ)) / 9 < (S : ℚ) := by
    rw [← hsumq]
    exact hS
  have hpqpos : 0 < (p : ℚ) := by
    exact_mod_cast hp
  nlinarith


#check_dependency_graph "hirzebruch_jung_large_entries_at_most_two" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"{i | 3 < a i}.card ≤ 2\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hn\",\"statement\":\"1 ≤ n\"},{\"name\":\"ha\",\"statement\":\"∀ (i : Fin n), 2 ≤ a i\"},{\"name\":\"hp\",\"statement\":\"0 < p\"},{\"name\":\"hq\",\"statement\":\"0 < q\"},{\"name\":\"hpq\",\"statement\":\"p.Coprime q\"},{\"name\":\"hfrac\",\"statement\":\"List.foldr (fun x r => x - 1 / r) 0 (List.ofFn fun i => ↑(a i)) = ↑p / ↑q\"},{\"name\":\"hS\",\"statement\":\"2 * ↑p / 9 < ∑ i with 3 < a i, ↑(a i - 3)\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1722_hirzebruch_jung_large_entries_at_most_two\",\"reconstructedProofSha256\":\"a53b118b316b0c237f4fe8c3638b0137ad1475c8d729d90af9cb23d5b8d10a2d\",\"selectedEdgeCount\":1,\"theoremName\":\"hirzebruch_jung_large_entries_at_most_two\",\"topologySha256\":\"68ed2744cdb1d7035722b828fa61040478e1c5ad3b5b31aff3bcf59ad48149a7\"}"
