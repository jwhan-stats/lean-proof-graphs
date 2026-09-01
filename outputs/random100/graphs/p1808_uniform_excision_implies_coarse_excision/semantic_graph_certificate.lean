import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p1808_uniform_excision_implies_coarse_excision
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: 9943d8a4477aad14cf2e09eabf976b18caee95156b6751314b607bb9d2607bee
-- reconstructed_proof_sha256: d215f2341b37da00e5ff6c0cb09a9729d7bec00a177b96d336fa9f91c2d8c547
-- selected_edge_count: 1

/- accepted add_to_file helper 1 -/
def ueRelPow {X : Type*} (W : SetRel X X) : ℕ → SetRel X X
  | 0 => SetRel.id
  | n + 1 => (ueRelPow W n).comp W

lemma ueRel_comp_mono {X : Type*} {R₁ R₂ S₁ S₂ : SetRel X X}
    (hR : R₁ ⊆ R₂) (hS : S₁ ⊆ S₂) : R₁.comp S₁ ⊆ R₂.comp S₂ := by
  intro p hp
  rcases hp with ⟨x, hpR, hpS⟩
  exact ⟨x, hR hpR, hS hpS⟩

lemma ueRel_inv_subset {X : Type*} {R S : SetRel X X} (h : R ⊆ S) : R.inv ⊆ S.inv := by
  intro p hp
  exact h hp

lemma ueRel_image_subset {X : Type*} {R S : SetRel X X} (h : R ⊆ S) (A : Set X) :
    R.image A ⊆ S.image A := by
  intro x hx
  rcases hx with ⟨a, haA, hax⟩
  exact ⟨a, haA, h hax⟩

lemma ueRelPow_id_subset {X : Type*} {W : SetRel X X} (hW : SetRel.id ⊆ W) :
    ∀ n : ℕ, SetRel.id ⊆ ueRelPow W n
  | 0 => by intro p hp; exact hp
  | n + 1 => by
      intro p hp
      have hp1 : p ∈ ueRelPow W n := ueRelPow_id_subset hW n hp
      rcases p with ⟨x, y⟩
      exact ⟨y, hp1, hW (by rfl : (y, y) ∈ SetRel.id)⟩

lemma ueRelPow_subset_succ {X : Type*} {W : SetRel X X} (hW : SetRel.id ⊆ W) (n : ℕ) :
    ueRelPow W n ⊆ ueRelPow W (n + 1) := by
  intro p hp
  rcases p with ⟨x, y⟩
  exact ⟨y, hp, hW (by rfl : (y, y) ∈ SetRel.id)⟩

lemma ueRelPow_mono {X : Type*} {W : SetRel X X} (hW : SetRel.id ⊆ W) :
    ∀ {m n : ℕ}, m ≤ n → ueRelPow W m ⊆ ueRelPow W n := by
  intro m n hmn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hadd : ∀ k : ℕ, ueRelPow W m ⊆ ueRelPow W (m + k) := by
    intro k
    induction k with
    | zero => intro p hp; exact hp
    | succ k ih =>
        intro p hp
        exact ueRelPow_subset_succ hW (m + k) (ih hp)
  exact hadd k

lemma ueRelPow_comp_subset {X : Type*} (W : SetRel X X) :
    ∀ m n : ℕ, (ueRelPow W m).comp (ueRelPow W n) ⊆ ueRelPow W (m + n) := by
  intro m n
  induction n with
  | zero =>
      intro p hp
      simpa [ueRelPow] using hp
  | succ n ih =>
      intro p hp
      have hp' : p ∈ ((ueRelPow W m).comp (ueRelPow W n)).comp W := by
        simpa [ueRelPow, SetRel.comp_assoc] using hp
      rcases hp' with ⟨y, hy₁, hy₂⟩
      exact ⟨y, ih hy₁, hy₂⟩

lemma ueRelPow_left_subset {X : Type*} (W : SetRel X X) :
    ∀ n : ℕ, W.comp (ueRelPow W n) ⊆ ueRelPow W (n + 1) := by
  intro n
  induction n with
  | zero =>
      intro p hp
      rcases hp with ⟨y, hyW, hyid⟩
      rcases p with ⟨x, z⟩
      change y = z at hyid
      subst z
      exact ⟨x, by rfl, hyW⟩
  | succ n ih =>
      intro p hp
      have hp' : p ∈ (W.comp (ueRelPow W n)).comp W := by
        simpa [ueRelPow, SetRel.comp_assoc] using hp
      rcases hp' with ⟨y, hy₁, hy₂⟩
      exact ⟨y, ih hy₁, hy₂⟩

lemma ueRelPow_inv_subset {X : Type*} {W : SetRel X X} (hW : W.inv ⊆ W) :
    ∀ n : ℕ, (ueRelPow W n).inv ⊆ ueRelPow W n := by
  intro n
  induction n with
  | zero =>
      intro p hp
      rcases p with ⟨x, y⟩
      change (y, x) ∈ SetRel.id at hp
      change y = x at hp
      subst x
      exact by rfl
  | succ n ih =>
      intro p hp
      have hp' : p ∈ W.inv.comp (ueRelPow W n).inv := by
        simpa [ueRelPow, SetRel.inv_comp] using hp
      have hp'' : p ∈ W.comp (ueRelPow W n) :=
        (ueRel_comp_mono hW ih) hp'
      exact ueRelPow_left_subset W n hp''

lemma ue_boundary {X : Type*} {A B : Set X} {W K : SetRel X X}
    (hAB : A ∪ B = Set.univ) (hrefl : SetRel.id ⊆ W)
    (hex : W.image A ∩ W.image B ⊆ K.image (A ∩ B)) :
    ∀ (n : ℕ) {a b : X}, a ∈ A → b ∈ B → (a, b) ∈ ueRelPow W n →
      b ∈ (K.comp (ueRelPow W n)).image (A ∩ B) := by
  intro n
  induction n with
  | zero =>
      intro a b ha hb hab
      change a = b at hab
      subst b
      have haW : a ∈ W.image A := ⟨a, ha, hrefl (by rfl : (a, a) ∈ SetRel.id)⟩
      have hbW : a ∈ W.image B := ⟨a, hb, hrefl (by rfl : (a, a) ∈ SetRel.id)⟩
      have hK : a ∈ K.image (A ∩ B) := hex ⟨haW, hbW⟩
      simpa [ueRelPow, SetRel.comp_id] using hK
  | succ n ih =>
      intro a b ha hb hab
      rcases hab with ⟨y, hay, hyb⟩
      have hyAB : y ∈ A ∪ B := by
        have : y ∈ (Set.univ : Set X) := Set.mem_univ y
        simpa [hAB] using this
      rcases hyAB with hyA | hyB
      · have hbWA : b ∈ W.image A := ⟨y, hyA, hyb⟩
        have hbWB : b ∈ W.image B := ⟨b, hb, hrefl (by rfl : (b, b) ∈ SetRel.id)⟩
        have hbK : b ∈ K.image (A ∩ B) := hex ⟨hbWA, hbWB⟩
        rcases hbK with ⟨c, hcAB, hcb⟩
        refine ⟨c, hcAB, ?_⟩
        exact ⟨b, hcb, ueRelPow_id_subset hrefl (n + 1) (by rfl : (b, b) ∈ SetRel.id)⟩
      · have hy : y ∈ (K.comp (ueRelPow W n)).image (A ∩ B) :=
          ih ha hyB hay
        rcases hy with ⟨c, hcAB, hcy⟩
        refine ⟨c, hcAB, ?_⟩
        have hcb : (c, b) ∈ (K.comp (ueRelPow W n)).comp W := ⟨y, hcy, hyb⟩
        simpa [ueRelPow, SetRel.comp_assoc] using hcb

def coarseGenerated {X : Type*} (R : SetRel X X) : Set (SetRel X X) :=
  {E | ∀ 𝒞 : Set (SetRel X X),
    R ∈ 𝒞 →
    SetRel.id ∈ 𝒞 →
    (∀ ⦃S T : SetRel X X⦄, S ∈ 𝒞 → T ⊆ S → T ∈ 𝒞) →
    (∀ ⦃S T : SetRel X X⦄, S ∈ 𝒞 → T ∈ 𝒞 → S ∪ T ∈ 𝒞) →
    (∀ ⦃S : SetRel X X⦄, S ∈ 𝒞 → S.inv ∈ 𝒞) →
    (∀ ⦃S T : SetRel X X⦄, S ∈ 𝒞 → T ∈ 𝒞 → S.comp T ∈ 𝒞) →
    E ∈ 𝒞}

def uniformCoarse (X : Type*) [UniformSpace X] : Set (SetRel X X) :=
  {E | ∀ R ∈ uniformity X, E ∈ coarseGenerated R}

lemma uniformCoarse_id {X : Type*} [UniformSpace X] :
    SetRel.id ∈ uniformCoarse X := by
  intro R hR 𝒞 hgen hid hsub hunion hinv hcomp
  exact hid

lemma uniformCoarse_subset {X : Type*} [UniformSpace X] {S T : SetRel X X}
    (hS : S ∈ uniformCoarse X) (hTS : T ⊆ S) : T ∈ uniformCoarse X := by
  intro R hR 𝒞 hgen hid hsub hunion hinv hcomp
  exact hsub (hS R hR 𝒞 hgen hid hsub hunion hinv hcomp) hTS

lemma uniformCoarse_comp {X : Type*} [UniformSpace X] {S T : SetRel X X}
    (hS : S ∈ uniformCoarse X) (hT : T ∈ uniformCoarse X) :
    S.comp T ∈ uniformCoarse X := by
  intro R hR 𝒞 hgen hid hsub hunion hinv hcomp
  exact hcomp (hS R hR 𝒞 hgen hid hsub hunion hinv hcomp)
    (hT R hR 𝒞 hgen hid hsub hunion hinv hcomp)

lemma coarseGenerated_relPow_bound {X : Type*} {V W : SetRel X X}
    (hrefl : SetRel.id ⊆ W) (hsymm : W.inv ⊆ W)
    (hV : V ∈ coarseGenerated W) :
    ∃ n : ℕ, V ⊆ ueRelPow W n := by
  refine hV {E : SetRel X X | ∃ n : ℕ, E ⊆ ueRelPow W n} ?_ ?_ ?_ ?_ ?_ ?_
  · exact ⟨1, by simpa [ueRelPow, SetRel.id_comp]⟩
  · exact ⟨0, by intro p hp; exact hp⟩
  · intro S T hS hTS
    rcases hS with ⟨n, hSn⟩
    exact ⟨n, hTS.trans hSn⟩
  · intro S T hS hT
    rcases hS with ⟨m, hSm⟩
    rcases hT with ⟨n, hTn⟩
    refine ⟨max m n, ?_⟩
    intro p hp
    rcases hp with hp | hp
    · exact ueRelPow_mono hrefl (Nat.le_max_left m n) (hSm hp)
    · exact ueRelPow_mono hrefl (Nat.le_max_right m n) (hTn hp)
  · intro S hS
    rcases hS with ⟨n, hSn⟩
    refine ⟨n, ?_⟩
    intro p hp
    exact ueRelPow_inv_subset hsymm n (ueRel_inv_subset hSn hp)
  · intro S T hS hT
    rcases hS with ⟨m, hSm⟩
    rcases hT with ⟨n, hTn⟩
    refine ⟨m + n, ?_⟩
    exact (ueRel_comp_mono hSm hTn).trans (ueRelPow_comp_subset W m n)

lemma ueSymmetrize_inv_subset {X : Type*} (R : SetRel X X) :
    R.symmetrize.inv ⊆ R.symmetrize := by
  intro p hp
  exact ⟨hp.2, hp.1⟩

/- verified submission -/
theorem uniform_excision_implies_coarse_excision
    {X : Type*} [UniformSpace X] (A B : Set X) :
    let generated : SetRel X X → Set (SetRel X X) := fun R =>
      {E | ∀ 𝒞 : Set (SetRel X X),
        R ∈ 𝒞 →
        SetRel.id ∈ 𝒞 →
        (∀ ⦃S T : SetRel X X⦄, S ∈ 𝒞 → T ⊆ S → T ∈ 𝒞) →
        (∀ ⦃S T : SetRel X X⦄, S ∈ 𝒞 → T ∈ 𝒞 → S ∪ T ∈ 𝒞) →
        (∀ ⦃S : SetRel X X⦄, S ∈ 𝒞 → S.inv ∈ 𝒞) →
        (∀ ⦃S T : SetRel X X⦄, S ∈ 𝒞 → T ∈ 𝒞 → S.comp T ∈ 𝒞) →
        E ∈ 𝒞}
    let coarse : Set (SetRel X X) :=
      {E | ∀ R ∈ uniformity X, E ∈ generated R}
    A ∪ B = Set.univ →
    (∃ E ∈ uniformity X, E ∈ coarse) →
    (∃ U ∈ uniformity X,
      ∃ κ : OrderDual {W : SetRel X X // W ⊆ U} → OrderDual (SetRel X X),
        Monotone κ ∧
        (∀ V ∈ uniformity X,
          ∃ W : {W : SetRel X X // W ⊆ U},
            W.1 ∈ uniformity X ∧
              OrderDual.ofDual (κ (OrderDual.toDual W)) ⊆ V) ∧
        (∀ W : {W : SetRel X X // W ⊆ U},
          W.1.image A ∩ W.1.image B ⊆
            (OrderDual.ofDual (κ (OrderDual.toDual W))).image (A ∩ B))) →
    ∀ V ∈ coarse, ∃ T ∈ coarse,
      V.image A ∩ V.image B ⊆ T.image (A ∩ B) := by
  intro generated coarse hAB hcompat hex V hV
  change V ∈ uniformCoarse X at hV
  change ∃ T ∈ uniformCoarse X, V.image A ∩ V.image B ⊆ T.image (A ∩ B)
  rcases hcompat with ⟨E, hEuniform, hEcoarse⟩
  change E ∈ uniformCoarse X at hEcoarse
  rcases hex with ⟨U, hUuniform, κ, hκmono, hκapprox, hκexc⟩
  rcases hκapprox E hEuniform with ⟨WE, hWEuniform, hκWE⟩
  let D : SetRel X X := WE.1 ∩ U ∩ E
  have hDuniform : D ∈ uniformity X := by
    exact Filter.inter_mem (Filter.inter_mem hWEuniform hUuniform) hEuniform
  let W : SetRel X X := D.symmetrize
  have hWuniform : W ∈ uniformity X := by
    exact symmetrize_mem_uniformity hDuniform
  have hW_subset_U : W ⊆ U := by
    intro p hp
    exact hp.1.1.2
  have hW_subset_E : W ⊆ E := by
    intro p hp
    exact hp.1.2
  have hW_subset_WE : W ⊆ WE.1 := by
    intro p hp
    exact hp.1.1.1
  let WU : {S : SetRel X X // S ⊆ U} := ⟨W, hW_subset_U⟩
  have hWrefl : SetRel.id ⊆ W := refl_le_uniformity hWuniform
  have hWsymm : W.inv ⊆ W := by
    exact ueSymmetrize_inv_subset D
  have hWcoarse : W ∈ uniformCoarse X :=
    uniformCoarse_subset hEcoarse hW_subset_E
  let K : SetRel X X := OrderDual.ofDual (κ (OrderDual.toDual WU))
  have hK_subset_E : K ⊆ E := by
    have hle : OrderDual.toDual WE ≤ OrderDual.toDual WU := by
      exact hW_subset_WE
    have hKWE : K ⊆ OrderDual.ofDual (κ (OrderDual.toDual WE)) := by
      exact hκmono hle
    exact hKWE.trans hκWE
  have hKcoarse : K ∈ uniformCoarse X :=
    uniformCoarse_subset hEcoarse hK_subset_E
  have hWexc : W.image A ∩ W.image B ⊆ K.image (A ∩ B) := by
    exact hκexc WU
  have hV_generated_W : V ∈ coarseGenerated W := hV W hWuniform
  rcases coarseGenerated_relPow_bound hWrefl hWsymm hV_generated_W with ⟨n, hVn⟩
  have hPowCoarse : ∀ m : ℕ, ueRelPow W m ∈ uniformCoarse X := by
    intro m
    induction m with
    | zero => exact uniformCoarse_id
    | succ m ih => exact uniformCoarse_comp ih hWcoarse
  refine ⟨K.comp (ueRelPow W (n + n + n)), ?_, ?_⟩
  · exact uniformCoarse_comp hKcoarse (hPowCoarse (n + n + n))
  · intro x hx
    have hxA : x ∈ (ueRelPow W n).image A := ueRel_image_subset hVn A hx.1
    have hxB : x ∈ (ueRelPow W n).image B := ueRel_image_subset hVn B hx.2
    rcases hxA with ⟨a, haA, hax⟩
    rcases hxB with ⟨b, hbB, hbx⟩
    have hxb : (x, b) ∈ ueRelPow W n :=
      ueRelPow_inv_subset hWsymm n hbx
    have hab₂ : (a, b) ∈ (ueRelPow W n).comp (ueRelPow W n) := ⟨x, hax, hxb⟩
    have habN : (a, b) ∈ ueRelPow W (n + n) :=
      ueRelPow_comp_subset W n n hab₂
    have hb_boundary : b ∈ (K.comp (ueRelPow W (n + n))).image (A ∩ B) :=
      ue_boundary hAB hWrefl hWexc (n + n) haA hbB habN
    rcases hb_boundary with ⟨c, hcAB, hcb⟩
    refine ⟨c, hcAB, ?_⟩
    have hcx₁ : (c, x) ∈ (K.comp (ueRelPow W (n + n))).comp (ueRelPow W n) :=
      ⟨b, hcb, hbx⟩
    have hcx₂ : (c, x) ∈ K.comp ((ueRelPow W (n + n)).comp (ueRelPow W n)) := by
      simpa [SetRel.comp_assoc] using hcx₁
    have htail : (ueRelPow W (n + n)).comp (ueRelPow W n) ⊆
        ueRelPow W (n + n + n) := by
      exact ueRelPow_comp_subset W (n + n) n
    exact (ueRel_comp_mono (by intro p hp; exact hp) htail) hcx₂


#check_dependency_graph "uniform_excision_implies_coarse_excision" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"∃ T ∈ coarse, V.image A ∩ V.image B ⊆ T.image (A ∩ B)\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hAB\",\"statement\":\"A ∪ B = Set.univ\"},{\"name\":\"hcompat\",\"statement\":\"∃ E ∈ uniformity X, E ∈ coarse\"},{\"name\":\"hex\",\"statement\":\"∃ U ∈ uniformity X, ∃ κ, Monotone κ ∧ (∀ V ∈ uniformity X, ∃ W, ↑W ∈ uniformity X ∧ OrderDual.ofDual (κ (OrderDual.toDual W)) ⊆ V) ∧ ∀ (W : { W // W ⊆ U }), (↑W).image A ∩ (↑W).image B ⊆ (OrderDual.ofDual (κ (OrderDual.toDual W))).image (A ∩ B)\"},{\"name\":\"hV\",\"statement\":\"V ∈ coarse\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p1808_uniform_excision_implies_coarse_excision\",\"reconstructedProofSha256\":\"d215f2341b37da00e5ff6c0cb09a9729d7bec00a177b96d336fa9f91c2d8c547\",\"selectedEdgeCount\":1,\"theoremName\":\"uniform_excision_implies_coarse_excision\",\"topologySha256\":\"9943d8a4477aad14cf2e09eabf976b18caee95156b6751314b607bb9d2607bee\"}"
