import Mathlib

/- accepted add_to_file helper 1 -/
import Mathlib

noncomputable section

namespace MetricAmalgamation

variable {X : Type*} {I : Type*} [MetricSpace X]

def pieceIndex (B : I → Set X) (hB_cover : (⋃ i, B i) = Set.univ) (x : X) : I :=
  Classical.choose (by
    have hx : x ∈ (⋃ i, B i : Set X) := by
      rw [hB_cover]
      exact Set.mem_univ x
    exact Set.mem_iUnion.mp hx)

lemma mem_piece (B : I → Set X) (hB_cover : (⋃ i, B i) = Set.univ) (x : X) :
    x ∈ B (pieceIndex B hB_cover x) :=
  Classical.choose_spec (by
    have hx : x ∈ (⋃ i, B i : Set X) := by
      rw [hB_cover]
      exact Set.mem_univ x
    exact Set.mem_iUnion.mp hx)

lemma pieceIndex_eq_of_mem {B : I → Set X}
    (hB_disjoint : (Set.univ : Set I).PairwiseDisjoint B)
    (hB_cover : (⋃ i, B i) = Set.univ) {x : X} {i : I} (hx : x ∈ B i) :
    pieceIndex B hB_cover x = i := by
  classical
  by_contra hne
  have hd : Disjoint (B (pieceIndex B hB_cover x)) (B i) :=
    hB_disjoint (Set.mem_univ _) (Set.mem_univ _) hne
  exact Set.disjoint_iff_forall_ne.mp hd (mem_piece B hB_cover x) hx rfl

def piecePoint (B : I → Set X) (hB_cover : (⋃ i, B i) = Set.univ) (x : X) :
    B (pieceIndex B hB_cover x) :=
  ⟨x, mem_piece B hB_cover x⟩

def glueDist (B : I → Set X) (hB_cover : (⋃ i, B i) = Set.univ)
    (p : ∀ i, B i) (e : ∀ i, MetricSpace (B i)) (x y : X) : ℝ := by
  classical
  exact if h : pieceIndex B hB_cover x = pieceIndex B hB_cover y then
    @dist (B (pieceIndex B hB_cover x)) (e _).toPseudoMetricSpace.toDist
      (piecePoint B hB_cover x)
      ⟨y, by simpa [h] using mem_piece B hB_cover y⟩
  else
    @dist (B (pieceIndex B hB_cover x)) (e _).toPseudoMetricSpace.toDist
      (piecePoint B hB_cover x) (p _) +
    dist (p (pieceIndex B hB_cover x) : X) (p (pieceIndex B hB_cover y) : X) +
    @dist (B (pieceIndex B hB_cover y)) (e _).toPseudoMetricSpace.toDist
      (p _) (piecePoint B hB_cover y)

end MetricAmalgamation

end

/- accepted add_to_file helper 2 -/
namespace MetricAmalgamation

variable {X : Type*} {I : Type*} [MetricSpace X]
variable {B : I → Set X}
variable {p : ∀ i, B i}
variable {e : ∀ i, MetricSpace (B i)}

lemma glueDist_left_congr {a i : I} (h : a = i) {x : X} (hx : x ∈ B a) :
    @dist (B a) (e a).toPseudoMetricSpace.toDist (⟨x, hx⟩ : B a) (p a) =
      @dist (B i) (e i).toPseudoMetricSpace.toDist
        (⟨x, h ▸ hx⟩ : B i) (p i) := by
  cases h
  rfl

lemma glueDist_right_congr {b j : I} (h : b = j) {y : X} (hy : y ∈ B b) :
    @dist (B b) (e b).toPseudoMetricSpace.toDist (p b) (⟨y, hy⟩ : B b) =
      @dist (B j) (e j).toPseudoMetricSpace.toDist (p j)
        (⟨y, h ▸ hy⟩ : B j) := by
  cases h
  rfl

lemma glueDist_base_congr {a i b j : I} (ha : a = i) (hb : b = j) :
    dist (p a : X) (p b : X) = dist (p i : X) (p j : X) := by
  cases ha
  cases hb
  rfl

variable {hB_disjoint : (Set.univ : Set I).PairwiseDisjoint B}
variable {hB_cover : (⋃ i, B i) = Set.univ}

include hB_disjoint hB_cover in
lemma glueDist_subtype_same (i : I) (x y : B i) :
    glueDist B hB_cover p e (x : X) (y : X) =
      @dist (B i) (e i).toPseudoMetricSpace.toDist x y := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  have hxi := pieceIndex_eq_of_mem (B := B) hB_disjoint hB_cover hx
  have hyi := pieceIndex_eq_of_mem (B := B) hB_disjoint hB_cover hy
  have hi : i = pieceIndex B hB_cover x := hxi.symm
  subst hi
  simp [glueDist, hyi, piecePoint]

include hB_disjoint hB_cover in
lemma glueDist_subtype_ne {i j : I} (hij : i ≠ j) (x : B i) (y : B j) :
    glueDist B hB_cover p e (x : X) (y : X) =
      @dist (B i) (e i).toPseudoMetricSpace.toDist x (p i) +
        dist (p i : X) (p j : X) +
          @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) y := by
  rcases x with ⟨x, hx⟩
  rcases y with ⟨y, hy⟩
  have hxi := pieceIndex_eq_of_mem (B := B) hB_disjoint hB_cover hx
  have hyj := pieceIndex_eq_of_mem (B := B) hB_disjoint hB_cover hy
  have hidx : pieceIndex B hB_cover x ≠ pieceIndex B hB_cover y := by
    simpa [hxi, hyj] using hij
  unfold glueDist
  rw [dif_neg hidx]
  simp only [piecePoint]
  rw [glueDist_left_congr (p := p) (e := e) hxi (mem_piece B hB_cover x)]
  rw [glueDist_right_congr (p := p) (e := e) hyj (mem_piece B hB_cover y)]
  rw [glueDist_base_congr (B := B) (p := p) hxi hyj]

end MetricAmalgamation

/- accepted add_to_file helper 3 -/
namespace MetricAmalgamation

variable {X : Type*} {I : Type*} [MetricSpace X]
variable {B : I → Set X}
variable {hB_disjoint : (Set.univ : Set I).PairwiseDisjoint B}
variable {hB_cover : (⋃ i, B i) = Set.univ}
variable {p : ∀ i, B i}
variable {e : ∀ i, MetricSpace (B i)}

include hB_disjoint hB_cover in
lemma glueDist_comm (x y : X) :
    glueDist B hB_cover p e x y = glueDist B hB_cover p e y x := by
  set i := pieceIndex B hB_cover x
  set j := pieceIndex B hB_cover y
  by_cases hij : i = j
  · let xb : B i := piecePoint B hB_cover x
    let yb : B i := ⟨y, by
      have hyj := mem_piece B hB_cover y
      change y ∈ B j at hyj
      simpa [hij] using hyj⟩
    have hxy0 := glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
      (hB_cover := hB_cover) (p := p) (e := e) i xb yb
    have hyx0 := glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
      (hB_cover := hB_cover) (p := p) (e := e) i yb xb
    have hxy : glueDist B hB_cover p e x y =
        @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb := by
      simpa [xb, yb, piecePoint] using hxy0
    have hyx : glueDist B hB_cover p e y x =
        @dist (B i) (e i).toPseudoMetricSpace.toDist yb xb := by
      simpa [xb, yb, piecePoint] using hyx0
    rw [hxy, hyx]
    exact @dist_comm (B i) (e i).toPseudoMetricSpace xb yb
  · let xb : B i := piecePoint B hB_cover x
    let yb : B j := piecePoint B hB_cover y
    have hxy0 := glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
      (hB_cover := hB_cover) (p := p) (e := e) hij xb yb
    have hyx0 := glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
      (hB_cover := hB_cover) (p := p) (e := e) (Ne.symm hij) yb xb
    have hxy : glueDist B hB_cover p e x y =
        @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
          dist (p i : X) (p j : X) +
            @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
      simpa [xb, yb, piecePoint] using hxy0
    have hyx : glueDist B hB_cover p e y x =
        @dist (B j) (e j).toPseudoMetricSpace.toDist yb (p j) +
          dist (p j : X) (p i : X) +
            @dist (B i) (e i).toPseudoMetricSpace.toDist (p i) xb := by
      simpa [xb, yb, piecePoint] using hyx0
    rw [hxy, hyx]
    rw [@dist_comm (B i) (e i).toPseudoMetricSpace xb (p i)]
    rw [dist_comm (p i : X) (p j : X)]
    rw [@dist_comm (B j) (e j).toPseudoMetricSpace (p j) yb]
    ring

include hB_disjoint hB_cover in
lemma glueDist_triangle (x y z : X) :
    glueDist B hB_cover p e x z ≤
      glueDist B hB_cover p e x y + glueDist B hB_cover p e y z := by
  set i := pieceIndex B hB_cover x
  set j := pieceIndex B hB_cover y
  set k := pieceIndex B hB_cover z
  let xb : B i := piecePoint B hB_cover x
  let yb : B j := piecePoint B hB_cover y
  let zb : B k := piecePoint B hB_cover z
  by_cases hik : i = k
  · let zb_i : B i := ⟨z, by
      have hz := mem_piece B hB_cover z
      change z ∈ B k at hz
      simpa [hik] using hz⟩
    by_cases hij : i = j
    · let yb_i : B i := ⟨y, by
        have hy := mem_piece B hB_cover y
        change y ∈ B j at hy
        simpa [hij] using hy⟩
      have hxz : glueDist B hB_cover p e x z =
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb zb_i := by
        simpa [xb, zb_i, piecePoint] using
          glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) i xb zb_i
      have hxy : glueDist B hB_cover p e x y =
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb_i := by
        simpa [xb, yb_i, piecePoint] using
          glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) i xb yb_i
      have hyz : glueDist B hB_cover p e y z =
          @dist (B i) (e i).toPseudoMetricSpace.toDist yb_i zb_i := by
        simpa [yb_i, zb_i, piecePoint] using
          glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) i yb_i zb_i
      rw [hxz, hxy, hyz]
      exact @dist_triangle (B i) (e i).toPseudoMetricSpace xb yb_i zb_i
    · have hxy : glueDist B hB_cover p e x y =
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
            dist (p i : X) (p j : X) +
              @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
        simpa [xb, yb, piecePoint] using
          glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) hij xb yb
      have hyz : glueDist B hB_cover p e y z =
          @dist (B j) (e j).toPseudoMetricSpace.toDist yb (p j) +
            dist (p j : X) (p i : X) +
              @dist (B i) (e i).toPseudoMetricSpace.toDist (p i) zb_i := by
        simpa [yb, zb_i, piecePoint] using
          glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) (Ne.symm hij) yb zb_i
      have hxz : glueDist B hB_cover p e x z =
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb zb_i := by
        simpa [xb, zb_i, piecePoint] using
          glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) i xb zb_i
      rw [hxz, hxy, hyz]
      have htri : @dist (B i) (e i).toPseudoMetricSpace.toDist xb zb_i ≤
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
            @dist (B i) (e i).toPseudoMetricSpace.toDist (p i) zb_i :=
        @dist_triangle (B i) (e i).toPseudoMetricSpace xb (p i) zb_i
      have h₁ : 0 ≤ dist (p i : X) (p j : X) := dist_nonneg
      have h₂ : 0 ≤ @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb :=
        @dist_nonneg (B j) (e j).toPseudoMetricSpace (p j) yb
      have h₃ : 0 ≤ @dist (B j) (e j).toPseudoMetricSpace.toDist yb (p j) :=
        @dist_nonneg (B j) (e j).toPseudoMetricSpace yb (p j)
      have h₄ : 0 ≤ dist (p j : X) (p i : X) := dist_nonneg
      nlinarith
  · by_cases hij : i = j
    · let yb_i : B i := ⟨y, by
        have hy := mem_piece B hB_cover y
        change y ∈ B j at hy
        simpa [hij] using hy⟩
      have hxz : glueDist B hB_cover p e x z =
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
            dist (p i : X) (p k : X) +
              @dist (B k) (e k).toPseudoMetricSpace.toDist (p k) zb := by
        simpa [xb, zb, piecePoint] using
          glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) hik xb zb
      have hxy : glueDist B hB_cover p e x y =
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb_i := by
        simpa [xb, yb_i, piecePoint] using
          glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) i xb yb_i
      have hyz : glueDist B hB_cover p e y z =
          @dist (B i) (e i).toPseudoMetricSpace.toDist yb_i (p i) +
            dist (p i : X) (p k : X) +
              @dist (B k) (e k).toPseudoMetricSpace.toDist (p k) zb := by
        simpa [yb_i, zb, piecePoint] using
          glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) hik yb_i zb
      rw [hxz, hxy, hyz]
      have htri : @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) ≤
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb_i +
            @dist (B i) (e i).toPseudoMetricSpace.toDist yb_i (p i) :=
        @dist_triangle (B i) (e i).toPseudoMetricSpace xb yb_i (p i)
      nlinarith
    · by_cases hjk : j = k
      · let zb_j : B j := ⟨z, by
          have hz := mem_piece B hB_cover z
          change z ∈ B k at hz
          simpa [hjk] using hz⟩
        have hxz : glueDist B hB_cover p e x z =
            @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
              dist (p i : X) (p j : X) +
                @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) zb_j := by
          have hij' : i ≠ j := by
            intro h
            exact hik (h.trans hjk)
          simpa [xb, zb_j, piecePoint] using
            glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
              (hB_cover := hB_cover) (p := p) (e := e) hij' xb zb_j
        have hxy : glueDist B hB_cover p e x y =
            @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
              dist (p i : X) (p j : X) +
                @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
          simpa [xb, yb, piecePoint] using
            glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
              (hB_cover := hB_cover) (p := p) (e := e) hij xb yb
        have hyz : glueDist B hB_cover p e y z =
            @dist (B j) (e j).toPseudoMetricSpace.toDist yb zb_j := by
          simpa [yb, zb_j, piecePoint] using
            glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
              (hB_cover := hB_cover) (p := p) (e := e) j yb zb_j
        rw [hxz, hxy, hyz]
        have htri : @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) zb_j ≤
            @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb +
              @dist (B j) (e j).toPseudoMetricSpace.toDist yb zb_j :=
          @dist_triangle (B j) (e j).toPseudoMetricSpace (p j) yb zb_j
        nlinarith
      · have hxz : glueDist B hB_cover p e x z =
            @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
              dist (p i : X) (p k : X) +
                @dist (B k) (e k).toPseudoMetricSpace.toDist (p k) zb := by
          simpa [xb, zb, piecePoint] using
            glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
              (hB_cover := hB_cover) (p := p) (e := e) hik xb zb
        have hxy : glueDist B hB_cover p e x y =
            @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
              dist (p i : X) (p j : X) +
                @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
          simpa [xb, yb, piecePoint] using
            glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
              (hB_cover := hB_cover) (p := p) (e := e) hij xb yb
        have hyz : glueDist B hB_cover p e y z =
            @dist (B j) (e j).toPseudoMetricSpace.toDist yb (p j) +
              dist (p j : X) (p k : X) +
                @dist (B k) (e k).toPseudoMetricSpace.toDist (p k) zb := by
          simpa [yb, zb, piecePoint] using
            glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
              (hB_cover := hB_cover) (p := p) (e := e) hjk yb zb
        rw [hxz, hxy, hyz]
        have hbase : dist (p i : X) (p k : X) ≤
            dist (p i : X) (p j : X) + dist (p j : X) (p k : X) :=
          dist_triangle (p i : X) (p j : X) (p k : X)
        have h₁ : 0 ≤ @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb :=
          @dist_nonneg (B j) (e j).toPseudoMetricSpace (p j) yb
        have h₂ : 0 ≤ @dist (B j) (e j).toPseudoMetricSpace.toDist yb (p j) :=
          @dist_nonneg (B j) (e j).toPseudoMetricSpace yb (p j)
        nlinarith

end MetricAmalgamation

/- accepted add_to_file helper 4 -/
namespace MetricAmalgamation

variable {X : Type*} {I : Type*} [MetricSpace X]
variable {B : I → Set X}
variable {hB_disjoint : (Set.univ : Set I).PairwiseDisjoint B}
variable {hB_cover : (⋃ i, B i) = Set.univ}
variable {p : ∀ i, B i}
variable {e : ∀ i, MetricSpace (B i)}

lemma glueDist_self (x : X) : glueDist B hB_cover p e x x = 0 := by
  simp [glueDist, piecePoint]

include hB_disjoint hB_cover in
lemma eq_of_glueDist_eq_zero {x y : X}
    (h : glueDist B hB_cover p e x y = 0) : x = y := by
  set i := pieceIndex B hB_cover x
  set j := pieceIndex B hB_cover y
  by_cases hij : i = j
  · let xb : B i := piecePoint B hB_cover x
    let yb : B i := ⟨y, by
      have hyj := mem_piece B hB_cover y
      change y ∈ B j at hyj
      simpa [hij] using hyj⟩
    have hxy : glueDist B hB_cover p e x y =
        @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb := by
      simpa [xb, yb, piecePoint] using
        glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
          (hB_cover := hB_cover) (p := p) (e := e) i xb yb
    rw [hxy] at h
    have hsub : xb = yb := @eq_of_dist_eq_zero (B i) (e i) xb yb h
    have hval : (xb : X) = (yb : X) := congrArg Subtype.val hsub
    simpa [xb, yb, piecePoint] using hval
  · let xb : B i := piecePoint B hB_cover x
    let yb : B j := piecePoint B hB_cover y
    have hxy : glueDist B hB_cover p e x y =
        @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
          dist (p i : X) (p j : X) +
            @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
      simpa [xb, yb, piecePoint] using
        glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
          (hB_cover := hB_cover) (p := p) (e := e) hij xb yb
    rw [hxy] at h
    have ha : 0 ≤ @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) :=
      @dist_nonneg (B i) (e i).toPseudoMetricSpace xb (p i)
    have hb : 0 ≤ @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb :=
      @dist_nonneg (B j) (e j).toPseudoMetricSpace (p j) yb
    have hc0 : dist (p i : X) (p j : X) ≤ 0 := by
      have hc : dist (p i : X) (p j : X) ≤
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
            dist (p i : X) (p j : X) +
              @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
        nlinarith
      rwa [h] at hc
    have hc : dist (p i : X) (p j : X) = 0 := le_antisymm hc0 dist_nonneg
    have hp : (p i : X) = (p j : X) := eq_of_dist_eq_zero hc
    have hd : Disjoint (B i) (B j) :=
      hB_disjoint (Set.mem_univ i) (Set.mem_univ j) hij
    exact False.elim
      (Set.disjoint_iff_forall_ne.mp hd (p i).property (p j).property hp)

end MetricAmalgamation

/- accepted add_to_file helper 5 -/
namespace MetricAmalgamation

variable {X : Type*} {I : Type*} [MetricSpace X]
variable {B : I → Set X}
variable {hB_disjoint : (Set.univ : Set I).PairwiseDisjoint B}
variable {hB_clopen : ∀ i, IsClopen (B i)}
variable {hB_cover : (⋃ i, B i) = Set.univ}
variable {p : ∀ i, B i}
variable {e : ∀ i, MetricSpace (B i)}
variable {he_top : ∀ i,
  (e i).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
    (inferInstance : TopologicalSpace (B i))}

include hB_disjoint hB_clopen hB_cover he_top in
lemma glueDist_topology (s : Set X) :
    IsOpen s ↔ ∀ x ∈ s, ∃ δ > 0, ∀ y,
      glueDist B hB_cover p e x y < δ → y ∈ s := by
  constructor
  · intro hs x hxs
    set i := pieceIndex B hB_cover x
    let xb : B i := piecePoint B hB_cover x
    let t : Set (B i) := Subtype.val ⁻¹' s
    have ht_old : IsOpen t := continuous_subtype_val.isOpen_preimage s hs
    have ht_e : @IsOpen (B i)
        (e i).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace t := by
      rw [he_top i]
      exact ht_old
    have hx_t : xb ∈ t := by
      change (xb : X) ∈ s
      simpa [xb, piecePoint] using hxs
    rcases (@Metric.isOpen_iff (B i) (e i).toPseudoMetricSpace t).mp ht_e xb hx_t with
      ⟨r, hr, hball⟩
    have hBi : IsOpen (B i) := (hB_clopen i).isOpen
    rcases Metric.isOpen_iff.mp hBi (p i : X) (p i).property with ⟨η, hη, hηsub⟩
    refine ⟨min r η, lt_min hr hη, ?_⟩
    intro y hyD
    set j := pieceIndex B hB_cover y
    let yb : B j := piecePoint B hB_cover y
    by_cases hij : i = j
    · let yb_i : B i := ⟨y, by
        have hyj := mem_piece B hB_cover y
        change y ∈ B j at hyj
        simpa [hij] using hyj⟩
      have hD : glueDist B hB_cover p e x y =
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb_i := by
        simpa [xb, yb_i, piecePoint] using
          glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) i xb yb_i
      have her : @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb_i < r := by
        rw [← hD]
        exact lt_of_lt_of_le hyD (min_le_left r η)
      have her' : @dist (B i) (e i).toPseudoMetricSpace.toDist yb_i xb < r := by
        rw [@dist_comm (B i) (e i).toPseudoMetricSpace yb_i xb]
        exact her
      have hyt : yb_i ∈ t := hball
        ((@Metric.mem_ball (B i) (e i).toPseudoMetricSpace xb yb_i r).mpr her')
      change (yb_i : X) ∈ s at hyt
      simpa [yb_i] using hyt
    · have hD : glueDist B hB_cover p e x y =
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
            dist (p i : X) (p j : X) +
              @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
        simpa [xb, yb, piecePoint] using
          glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
            (hB_cover := hB_cover) (p := p) (e := e) hij xb yb
      have ha : 0 ≤ @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) :=
        @dist_nonneg (B i) (e i).toPseudoMetricSpace xb (p i)
      have hb : 0 ≤ @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb :=
        @dist_nonneg (B j) (e j).toPseudoMetricSpace (p j) yb
      have hbase : dist (p i : X) (p j : X) < η := by
        have hle : dist (p i : X) (p j : X) ≤ glueDist B hB_cover p e x y := by
          rw [hD]
          nlinarith
        exact lt_of_le_of_lt hle (lt_of_lt_of_le hyD (min_le_right r η))
      have hbase' : dist (p j : X) (p i : X) < η := by
        rw [dist_comm]
        exact hbase
      have hpji : (p j : X) ∈ B i := hηsub (Metric.mem_ball.mpr hbase')
      have hd : Disjoint (B i) (B j) :=
        hB_disjoint (Set.mem_univ i) (Set.mem_univ j) hij
      exact False.elim
        (Set.disjoint_iff_forall_ne.mp hd hpji (p j).property rfl)
  · intro h
    rw [Metric.isOpen_iff]
    intro x hxs
    rcases h x hxs with ⟨δ, hδ, hδsub⟩
    set i := pieceIndex B hB_cover x
    let xb : B i := piecePoint B hB_cover x
    let t : Set (B i) := @Metric.ball (B i) (e i).toPseudoMetricSpace xb δ
    have ht_e : @IsOpen (B i)
        (e i).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace t := by
      exact @Metric.isOpen_ball (B i) (e i).toPseudoMetricSpace xb δ
    rw [he_top i] at ht_e
    rcases isOpen_induced_iff.mp ht_e with ⟨u, hu, hu_eq⟩
    have hx_dist : @dist (B i) (e i).toPseudoMetricSpace.toDist xb xb < δ := by
      rw [@dist_self (B i) (e i).toPseudoMetricSpace xb]
      exact hδ
    have hx_t : xb ∈ t :=
      (@Metric.mem_ball (B i) (e i).toPseudoMetricSpace xb xb δ).mpr hx_dist
    have hxu : (xb : X) ∈ u := by
      have : xb ∈ Subtype.val ⁻¹' u := by
        rw [hu_eq]
        exact hx_t
      exact this
    rcases Metric.isOpen_iff.mp hu (xb : X) hxu with ⟨ru, hru, hrusub⟩
    have hBi : IsOpen (B i) := (hB_clopen i).isOpen
    have hxBi : (xb : X) ∈ B i := by
      simpa [xb, piecePoint] using mem_piece B hB_cover x
    rcases Metric.isOpen_iff.mp hBi (xb : X) hxBi with ⟨rB, hrB, hrBsub⟩
    refine ⟨min ru rB, lt_min hru hrB, ?_⟩
    intro y hy
    have hyu : y ∈ u := hrusub (Metric.mem_ball.mpr
      (lt_of_lt_of_le hy (min_le_left ru rB)))
    have hyBi : y ∈ B i := hrBsub (Metric.mem_ball.mpr
      (lt_of_lt_of_le hy (min_le_right ru rB)))
    let yb : B i := ⟨y, hyBi⟩
    have hyt : yb ∈ t := by
      have : yb ∈ Subtype.val ⁻¹' u := hyu
      rwa [hu_eq] at this
    have helt : @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb < δ := by
      have hd : @dist (B i) (e i).toPseudoMetricSpace.toDist yb xb < δ :=
        (@Metric.mem_ball (B i) (e i).toPseudoMetricSpace xb yb δ).mp hyt
      rw [@dist_comm (B i) (e i).toPseudoMetricSpace yb xb] at hd
      exact hd
    have hD : glueDist B hB_cover p e x y =
        @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb := by
      simpa [xb, yb, piecePoint] using
        glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
          (hB_cover := hB_cover) (p := p) (e := e) i xb yb
    apply hδsub y
    rw [hD]
    exact helt

end MetricAmalgamation

/- accepted add_to_file helper 6 -/
namespace MetricAmalgamation

variable {X : Type*} {I : Type*} [MetricSpace X]
variable {B : I → Set X}
variable {hB_disjoint : (Set.univ : Set I).PairwiseDisjoint B}
variable {hB_clopen : ∀ i, IsClopen (B i)}
variable {hB_cover : (⋃ i, B i) = Set.univ}
variable {p : ∀ i, B i}
variable {e : ∀ i, MetricSpace (B i)}
variable {he_top : ∀ i,
  (e i).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
    (inferInstance : TopologicalSpace (B i))}

include hB_disjoint hB_clopen hB_cover he_top in
@[implicit_reducible] noncomputable def glueMetricSpace : MetricSpace X :=
  MetricSpace.ofDistTopology (glueDist B hB_cover p e)
    (glueDist_self (B := B) (hB_cover := hB_cover) (p := p) (e := e))
    (glueDist_comm (B := B) (hB_disjoint := hB_disjoint) (hB_cover := hB_cover)
      (p := p) (e := e))
    (glueDist_triangle (B := B) (hB_disjoint := hB_disjoint) (hB_cover := hB_cover)
      (p := p) (e := e))
    (glueDist_topology (B := B) (hB_disjoint := hB_disjoint)
      (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
      (he_top := he_top))
    (fun x y h => eq_of_glueDist_eq_zero (B := B) (hB_disjoint := hB_disjoint)
      (hB_cover := hB_cover) (p := p) (e := e) h)

include hB_disjoint hB_clopen hB_cover he_top in
lemma dist_glueMetricSpace (x y : X) :
    @dist X (glueMetricSpace (B := B) (hB_disjoint := hB_disjoint)
      (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
      (he_top := he_top)).toPseudoMetricSpace.toDist x y =
      glueDist B hB_cover p e x y :=
  rfl

include hB_disjoint hB_clopen hB_cover he_top in
lemma glueMetricSpace_topology :
    (glueMetricSpace (B := B) (hB_disjoint := hB_disjoint)
      (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
      (he_top := he_top)).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace X) :=
  rfl

end MetricAmalgamation

/- accepted add_to_file helper 7 -/
namespace MetricAmalgamation

lemma dist_le_of_ediam_le_ofReal {α : Type*} [PseudoMetricSpace α]
    {s : Set α} {ε : ℝ} (hε : 0 ≤ ε)
    (hs : Metric.ediam s ≤ ENNReal.ofReal ε)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) : dist x y ≤ ε := by
  have hed : edist x y ≤ Metric.ediam s := Metric.edist_le_ediam_of_mem hx hy
  have hof : ENNReal.ofReal (dist x y) ≤ ENNReal.ofReal ε := by
    rw [← edist_dist]
    exact hed.trans hs
  exact (ENNReal.ofReal_le_ofReal_iff hε).mp hof

end MetricAmalgamation

/- accepted add_to_file helper 8 -/
namespace MetricAmalgamation

lemma dist_le_of_ediam_le_ofReal_explicit {α : Type*} (m : PseudoMetricSpace α)
    {s : Set α} {ε : ℝ} (hε : 0 ≤ ε)
    (hs : @Metric.ediam α m.toPseudoEMetricSpace s ≤ ENNReal.ofReal ε)
    {x y : α} (hx : x ∈ s) (hy : y ∈ s) :
    @dist α m.toDist x y ≤ ε := by
  have hed : @edist α m.toPseudoEMetricSpace.toEDist x y ≤
      @Metric.ediam α m.toPseudoEMetricSpace s :=
    @Metric.edist_le_ediam_of_mem α s x y m.toPseudoEMetricSpace hx hy
  have hof : ENNReal.ofReal (@dist α m.toDist x y) ≤ ENNReal.ofReal ε := by
    rw [← @edist_dist α m x y]
    exact hed.trans hs
  exact (ENNReal.ofReal_le_ofReal_iff hε).mp hof

end MetricAmalgamation

/- accepted add_to_file helper 9 -/
namespace MetricAmalgamation

variable {X : Type*} {I : Type*} [MetricSpace X]
variable {B : I → Set X}
variable {hB_disjoint : (Set.univ : Set I).PairwiseDisjoint B}
variable {hB_clopen : ∀ i, IsClopen (B i)}
variable {hB_cover : (⋃ i, B i) = Set.univ}
variable {p : ∀ i, B i}
variable {e : ∀ i, MetricSpace (B i)}
variable {he_top : ∀ i,
  (e i).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
    (inferInstance : TopologicalSpace (B i))}

include hB_disjoint hB_clopen hB_cover he_top in
lemma dist_glueMetricSpace_error_le (ε : ℝ) (hε : 0 ≤ ε)
    (hdiam : ∀ i, Metric.ediam (B i) ≤ ENNReal.ofReal ε)
    (hediam : ∀ i,
      @Metric.ediam (B i) (e i).toPseudoMetricSpace.toPseudoEMetricSpace
        Set.univ ≤ ENNReal.ofReal ε)
    (x y : X) :
    |@dist X (glueMetricSpace (B := B) (hB_disjoint := hB_disjoint)
      (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
      (he_top := he_top)).toPseudoMetricSpace.toDist x y - dist x y| ≤
        4 * ε := by
  set i := pieceIndex B hB_cover x
  set j := pieceIndex B hB_cover y
  let xb : B i := piecePoint B hB_cover x
  let yb : B j := piecePoint B hB_cover y
  have hD0 : @dist X (glueMetricSpace (B := B) (hB_disjoint := hB_disjoint)
      (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
      (he_top := he_top)).toPseudoMetricSpace.toDist x y =
      glueDist B hB_cover p e x y :=
    dist_glueMetricSpace (B := B) (hB_disjoint := hB_disjoint)
      (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
      (he_top := he_top) x y
  by_cases hij : i = j
  · let yb_i : B i := ⟨y, by
      have hyj := mem_piece B hB_cover y
      change y ∈ B j at hyj
      simpa [hij] using hyj⟩
    have hD : @dist X (glueMetricSpace (B := B) (hB_disjoint := hB_disjoint)
        (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
        (he_top := he_top)).toPseudoMetricSpace.toDist x y =
        @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb_i := by
      rw [hD0]
      simpa [xb, yb_i, piecePoint] using
        glueDist_subtype_same (B := B) (hB_disjoint := hB_disjoint)
          (hB_cover := hB_cover) (p := p) (e := e) i xb yb_i
    rw [hD]
    have hdxy : dist x y ≤ ε := by
      exact dist_le_of_ediam_le_ofReal (s := B i) hε (hdiam i)
        (by simpa [xb, piecePoint] using mem_piece B hB_cover x)
        (by simpa [yb_i] using yb_i.property)
    have hexy : @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb_i ≤ ε := by
      exact dist_le_of_ediam_le_ofReal_explicit (e i).toPseudoMetricSpace
        (s := Set.univ) hε (hediam i) (Set.mem_univ xb) (Set.mem_univ yb_i)
    have hd0 : 0 ≤ dist x y := dist_nonneg
    have he0 : 0 ≤ @dist (B i) (e i).toPseudoMetricSpace.toDist xb yb_i :=
      @dist_nonneg (B i) (e i).toPseudoMetricSpace xb yb_i
    rw [abs_sub_le_iff]
    constructor <;> nlinarith
  · have hD : @dist X (glueMetricSpace (B := B) (hB_disjoint := hB_disjoint)
        (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
        (he_top := he_top)).toPseudoMetricSpace.toDist x y =
        @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
          dist (p i : X) (p j : X) +
            @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
      rw [hD0]
      simpa [xb, yb, piecePoint] using
        glueDist_subtype_ne (B := B) (hB_disjoint := hB_disjoint)
          (hB_cover := hB_cover) (p := p) (e := e) hij xb yb
    rw [hD]
    have hd_xp : dist x (p i : X) ≤ ε :=
      dist_le_of_ediam_le_ofReal (s := B i) hε (hdiam i)
        (by simpa [xb, piecePoint] using mem_piece B hB_cover x) (p i).property
    have hd_py : dist (p j : X) y ≤ ε :=
      dist_le_of_ediam_le_ofReal (s := B j) hε (hdiam j)
        (p j).property (by simpa [yb, piecePoint] using mem_piece B hB_cover y)
    have he_xp : @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) ≤ ε :=
      dist_le_of_ediam_le_ofReal_explicit (e i).toPseudoMetricSpace
        (s := Set.univ) hε (hediam i) (Set.mem_univ xb) (Set.mem_univ (p i))
    have he_py : @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb ≤ ε :=
      dist_le_of_ediam_le_ofReal_explicit (e j).toPseudoMetricSpace
        (s := Set.univ) hε (hediam j) (Set.mem_univ (p j)) (Set.mem_univ yb)
    have hupper : @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
        dist (p i : X) (p j : X) +
          @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb -
            dist x y ≤ 4 * ε := by
      have hc : dist (p i : X) (p j : X) ≤
          dist (p i : X) x + dist x y + dist y (p j : X) := by
        calc
          dist (p i : X) (p j : X) ≤ dist (p i : X) x + dist x (p j : X) :=
            dist_triangle _ _ _
          _ ≤ (dist (p i : X) x + dist x y) + dist y (p j : X) := by
            have := dist_triangle x y (p j : X)
            nlinarith
      have hxpi : dist (p i : X) x ≤ ε := by simpa [dist_comm] using hd_xp
      have hypj : dist y (p j : X) ≤ ε := by simpa [dist_comm] using hd_py
      nlinarith
    have hlower : dist x y -
        (@dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
          dist (p i : X) (p j : X) +
            @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb) ≤
          4 * ε := by
      have hd : dist x y ≤
          dist x (p i : X) + dist (p i : X) (p j : X) + dist (p j : X) y := by
        calc
          dist x y ≤ dist x (p i : X) + dist (p i : X) y := dist_triangle _ _ _
          _ ≤ dist x (p i : X) +
              (dist (p i : X) (p j : X) + dist (p j : X) y) := by
            have := dist_triangle (p i : X) (p j : X) y
            nlinarith
          _ = dist x (p i : X) + dist (p i : X) (p j : X) +
              dist (p j : X) y := by ring
      have hc_nonneg : dist (p i : X) (p j : X) ≤
          @dist (B i) (e i).toPseudoMetricSpace.toDist xb (p i) +
            dist (p i : X) (p j : X) +
              @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) yb := by
        have h1 := @dist_nonneg (B i) (e i).toPseudoMetricSpace xb (p i)
        have h2 := @dist_nonneg (B j) (e j).toPseudoMetricSpace (p j) yb
        nlinarith
      nlinarith
    exact abs_sub_le_iff.mpr ⟨hupper, hlower⟩

end MetricAmalgamation

/- verified submission -/
theorem metric_amalgamation
    {X : Type*} {I : Type*} [MetricSpace X]
    (B : I → Set X)
    (hB_disjoint : (Set.univ : Set I).PairwiseDisjoint B)
    (hB_clopen : ∀ i, IsClopen (B i))
    (hB_cover : (⋃ i, B i) = Set.univ)
    (p : ∀ i, B i)
    (e : ∀ i, MetricSpace (B i))
    (he_top : ∀ i,
      (e i).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace (B i))) :
    ∃ mD : MetricSpace X,
      (∀ (i : I) (x y : B i),
        @dist X mD.toPseudoMetricSpace.toDist x y =
          @dist (B i) (e i).toPseudoMetricSpace.toDist x y) ∧
      (∀ (i j : I), i ≠ j → ∀ (x : B i) (y : B j),
        @dist X mD.toPseudoMetricSpace.toDist x y =
          @dist (B i) (e i).toPseudoMetricSpace.toDist x (p i) +
            dist (p i : X) (p j : X) +
              @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) y) ∧
      mD.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace X) ∧
      ∀ ε : ℝ, 0 ≤ ε →
        ((∀ i, Metric.ediam (B i) ≤ ENNReal.ofReal ε) ∧
          (∀ i, @Metric.ediam (B i)
            (e i).toPseudoMetricSpace.toPseudoEMetricSpace Set.univ ≤
              ENNReal.ofReal ε)) →
        sSup (Set.range (fun q : X × X =>
          |@dist X mD.toPseudoMetricSpace.toDist q.1 q.2 - dist q.1 q.2|)) ≤
            4 * ε := by
  classical
  refine ⟨MetricAmalgamation.glueMetricSpace (B := B) (hB_disjoint := hB_disjoint)
    (hB_clopen := hB_clopen) (hB_cover := hB_cover) (p := p) (e := e)
    (he_top := he_top), ?_, ?_, ?_, ?_⟩
  · intro i x y
    exact (MetricAmalgamation.dist_glueMetricSpace (B := B)
      (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
      (hB_cover := hB_cover) (p := p) (e := e) (he_top := he_top) x y).trans
      (MetricAmalgamation.glueDist_subtype_same (B := B)
        (hB_disjoint := hB_disjoint) (hB_cover := hB_cover) (p := p) (e := e) i x y)
  · intro i j hij x y
    have hmain := (MetricAmalgamation.dist_glueMetricSpace (B := B)
      (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
      (hB_cover := hB_cover) (p := p) (e := e) (he_top := he_top) x y).trans
      (MetricAmalgamation.glueDist_subtype_ne (B := B)
        (hB_disjoint := hB_disjoint) (hB_cover := hB_cover) (p := p) (e := e)
        hij x y)
    have hpp0 := (MetricAmalgamation.dist_glueMetricSpace (B := B)
      (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
      (hB_cover := hB_cover) (p := p) (e := e) (he_top := he_top)
      (p i) (p j)).trans
      (MetricAmalgamation.glueDist_subtype_ne (B := B)
        (hB_disjoint := hB_disjoint) (hB_cover := hB_cover) (p := p) (e := e)
        hij (p i) (p j))
    have hpp : @dist X (MetricAmalgamation.glueMetricSpace (B := B)
        (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
        (hB_cover := hB_cover) (p := p) (e := e)
        (he_top := he_top)).toPseudoMetricSpace.toDist (p i : X) (p j : X) =
        dist (p i : X) (p j : X) := by
      calc
        @dist X (MetricAmalgamation.glueMetricSpace (B := B)
          (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
          (hB_cover := hB_cover) (p := p) (e := e)
          (he_top := he_top)).toPseudoMetricSpace.toDist (p i : X) (p j : X)
            = @dist (B i) (e i).toPseudoMetricSpace.toDist (p i) (p i) +
              dist (p i : X) (p j : X) +
                @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) (p j) := hpp0
        _ = dist (p i : X) (p j : X) := by
          rw [@dist_self (B i) (e i).toPseudoMetricSpace (p i)]
          rw [@dist_self (B j) (e j).toPseudoMetricSpace (p j)]
          ring
    calc
      @dist X (MetricAmalgamation.glueMetricSpace (B := B)
        (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
        (hB_cover := hB_cover) (p := p) (e := e)
        (he_top := he_top)).toPseudoMetricSpace.toDist x y
          = @dist (B i) (e i).toPseudoMetricSpace.toDist x (p i) +
            dist (p i : X) (p j : X) +
              @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) y := hmain
      _ = @dist (B i) (e i).toPseudoMetricSpace.toDist x (p i) +
          @dist X (MetricAmalgamation.glueMetricSpace (B := B)
            (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
            (hB_cover := hB_cover) (p := p) (e := e)
            (he_top := he_top)).toPseudoMetricSpace.toDist (p i : X) (p j : X) +
          @dist (B j) (e j).toPseudoMetricSpace.toDist (p j) y := by
        rw [hpp]
  · exact MetricAmalgamation.glueMetricSpace_topology (B := B)
      (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
      (hB_cover := hB_cover) (p := p) (e := e) (he_top := he_top)
  · intro ε hε hdiam
    let mD : MetricSpace X := MetricAmalgamation.glueMetricSpace (B := B)
      (hB_disjoint := hB_disjoint) (hB_clopen := hB_clopen)
      (hB_cover := hB_cover) (p := p) (e := e) (he_top := he_top)
    change sSup (Set.range (fun q : X × X =>
      |@dist X mD.toPseudoMetricSpace.toDist q.1 q.2 -
        @dist X mD.toPseudoMetricSpace.toDist q.1 q.2|)) ≤ 4 * ε
    by_cases hX : Nonempty X
    · rcases hX with ⟨x⟩
      apply csSup_le
      · exact ⟨|@dist X mD.toPseudoMetricSpace.toDist x x -
          @dist X mD.toPseudoMetricSpace.toDist x x|, ⟨(x, x), rfl⟩⟩
      · intro b hb
        rcases hb with ⟨q, rfl⟩
        simp
        nlinarith
    · haveI : IsEmpty X := not_nonempty_iff.mp hX
      haveI : IsEmpty (X × X) := inferInstance
      rw [Set.range_eq_empty, Real.sSup_empty]
      nlinarith
