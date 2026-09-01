import GraphCertificate
import Mathlib

/- Generated concrete semantic dependency certificate.
The reconstructed accepted proof below supplies the proof pieces;
the final command kernel-checks and compares every selected edge. -/
-- graph_id: p0644_collapse_set_partialorder_iff_ordconnected
-- certificate_kind: embedded_theorem_replay
-- topology_sha256: ffa7fbe65112bd88a8747c3d228b9e112409eaf0464d453ac16f226471a79af6
-- reconstructed_proof_sha256: 1ae4cbda6d10f64039fa677ac0ee6fdd29c359f93ee7843f458ca49eb3b79ed2
-- selected_edge_count: 1

/- verified submission -/
theorem collapse_set_partialOrder_iff_ordConnected
    {P : Type*} [PartialOrder P] (B : Set P) (hB : B.Nonempty) :
    let Q := Sum {x : P // x ∉ B} Unit
    let r : Q → Q → Prop := fun x y =>
      match x, y with
      | Sum.inr _, Sum.inr _ => True
      | Sum.inr _, Sum.inl y => ∃ b ∈ B, b ≤ y.1
      | Sum.inl x, Sum.inr _ => ∃ b ∈ B, x.1 ≤ b
      | Sum.inl x, Sum.inl y =>
          x.1 ≤ y.1 ∨ ∃ b ∈ B, ∃ b' ∈ B, x.1 ≤ b ∧ b' ≤ y.1
    IsPartialOrder Q r ↔ B.OrdConnected := by
  let Q := Sum {x : P // x ∉ B} Unit
  let r : Q → Q → Prop := fun x y =>
      match x, y with
      | Sum.inr _, Sum.inr _ => True
      | Sum.inr _, Sum.inl y => ∃ b ∈ B, b ≤ y.1
      | Sum.inl x, Sum.inr _ => ∃ b ∈ B, x.1 ≤ b
      | Sum.inl x, Sum.inl y =>
          x.1 ≤ y.1 ∨ ∃ b ∈ B, ∃ b' ∈ B, x.1 ≤ b ∧ b' ≤ y.1
  change IsPartialOrder Q r ↔ B.OrdConnected
  have _ : B.Nonempty := hB
  constructor
  · intro hpo
    refine Set.OrdConnected.mk ?_
    intro x hx y hy z hz
    rcases Set.mem_Icc.mp hz with ⟨hxz, hzy⟩
    by_contra hzB
    let zq : {x : P // x ∉ B} := ⟨z, hzB⟩
    have hstar_z : r (Sum.inr ()) (Sum.inl zq) := ⟨x, hx, hxz⟩
    have hz_star : r (Sum.inl zq) (Sum.inr ()) := ⟨y, hy, hzy⟩
    have heq := hpo.antisymm (Sum.inr ()) (Sum.inl zq) hstar_z hz_star
    cases heq
  · intro hconn
    have hconvex : ∀ {x y z : P}, x ∈ B → y ∈ B → x ≤ z → z ≤ y → z ∈ B := by
      intro x y z hx hy hxz hzy
      exact hconn.out' hx hy (Set.mem_Icc.mpr ⟨hxz, hzy⟩)
    have hrefl : ∀ q : Q, r q q := by
      intro q
      cases q with
      | inl x =>
          exact Or.inl le_rfl
      | inr u =>
          trivial
    have htrans : ∀ a b c : Q, r a b → r b c → r a c := by
      intro a b c hab hbc
      cases a with
      | inl x =>
          cases b with
          | inl y =>
              cases c with
              | inl z =>
                  rcases hab with hxy | ⟨b₁, hb₁, b₂, hb₂, hxb₁, hb₂y⟩
                  · rcases hbc with hyz | ⟨c₁, hc₁, c₂, hc₂, hyc₁, hc₂z⟩
                    · exact Or.inl (le_trans hxy hyz)
                    · exact Or.inr ⟨c₁, hc₁, c₂, hc₂, le_trans hxy hyc₁, hc₂z⟩
                  · rcases hbc with hyz | ⟨c₁, hc₁, c₂, hc₂, hyc₁, hc₂z⟩
                    · exact Or.inr ⟨b₁, hb₁, b₂, hb₂, hxb₁, le_trans hb₂y hyz⟩
                    · exact Or.inr ⟨b₁, hb₁, c₂, hc₂, hxb₁, hc₂z⟩
              | inr z =>
                  rcases hbc with ⟨c', hc', hyc'⟩
                  rcases hab with hxy | ⟨b₁, hb₁, b₂, hb₂, hxb₁, hb₂y⟩
                  · exact ⟨c', hc', le_trans hxy hyc'⟩
                  · exact ⟨b₁, hb₁, hxb₁⟩
          | inr y =>
              cases c with
              | inl z =>
                  rcases hab with ⟨b₁, hb₁, hxb₁⟩
                  rcases hbc with ⟨b₂, hb₂, hb₂z⟩
                  exact Or.inr ⟨b₁, hb₁, b₂, hb₂, hxb₁, hb₂z⟩
              | inr z =>
                  exact hab
      | inr x =>
          cases b with
          | inl y =>
              cases c with
              | inl z =>
                  rcases hbc with hyz | ⟨c₁, hc₁, c₂, hc₂, hyc₁, hc₂z⟩
                  · rcases hab with ⟨b', hb', hb'y⟩
                    exact ⟨b', hb', le_trans hb'y hyz⟩
                  · exact ⟨c₂, hc₂, hc₂z⟩
              | inr z =>
                  trivial
          | inr y =>
              exact hbc
    have hanti : ∀ a b : Q, r a b → r b a → a = b := by
      intro a b hab hba
      cases a with
      | inl x =>
          cases b with
          | inl y =>
              rcases hab with hxy | ⟨b₁, hb₁, b₂, hb₂, hxb₁, hb₂y⟩
              · rcases hba with hyx | ⟨c₁, hc₁, c₂, hc₂, hyc₁, hc₂x⟩
                · exact congrArg Sum.inl (Subtype.ext (le_antisymm hxy hyx))
                · exfalso
                  exact y.2 (hconvex hc₂ hc₁ (le_trans hc₂x hxy) hyc₁)
              · rcases hba with hyx | ⟨c₁, hc₁, c₂, hc₂, hyc₁, hc₂x⟩
                · exfalso
                  exact x.2 (hconvex hb₂ hb₁ (le_trans hb₂y hyx) hxb₁)
                · exfalso
                  exact y.2 (hconvex hb₂ hc₁ hb₂y hyc₁)
          | inr y =>
              rcases hab with ⟨b₁, hb₁, hxb₁⟩
              rcases hba with ⟨b₂, hb₂, hb₂x⟩
              exfalso
              exact x.2 (hconvex hb₂ hb₁ hb₂x hxb₁)
      | inr x =>
          cases b with
          | inl y =>
              rcases hab with ⟨b₁, hb₁, hb₁y⟩
              rcases hba with ⟨b₂, hb₂, hyb₂⟩
              exfalso
              exact y.2 (hconvex hb₁ hb₂ hb₁y hyb₂)
          | inr y =>
              rfl
    letI : Std.Refl r := ⟨hrefl⟩
    letI : IsTrans Q r := ⟨htrans⟩
    letI : IsPreorder Q r := IsPreorder.mk
    letI : Std.Antisymm r := ⟨hanti⟩
    exact IsPartialOrder.mk


#check_dependency_graph "collapse_set_partialOrder_iff_ordConnected" against "{\"edges\":[{\"conclusion\":{\"name\":\"goal\",\"statement\":\"let Q := { x // x ∉ B } ⊕ Unit; let r := fun x y => match x, y with | Sum.inr val, Sum.inr val_1 => True | Sum.inr val, Sum.inl y => ∃ b ∈ B, b ≤ ↑y | Sum.inl x, Sum.inr val => ∃ b ∈ B, ↑x ≤ b | Sum.inl x, Sum.inl y => ↑x ≤ ↑y ∨ ∃ b ∈ B, ∃ b' ∈ B, ↑x ≤ b ∧ b' ≤ ↑y; IsPartialOrder Q r ↔ B.OrdConnected\"},\"graphEdgeId\":\"h_goal\",\"premises\":[{\"name\":\"hB\",\"statement\":\"B.Nonempty\"}],\"rawEdgeId\":\"goal_edge\"}],\"graphId\":\"p0644_collapse_set_partialorder_iff_ordconnected\",\"reconstructedProofSha256\":\"1ae4cbda6d10f64039fa677ac0ee6fdd29c359f93ee7843f458ca49eb3b79ed2\",\"selectedEdgeCount\":1,\"theoremName\":\"collapse_set_partialOrder_iff_ordConnected\",\"topologySha256\":\"ffa7fbe65112bd88a8747c3d228b9e112409eaf0464d453ac16f226471a79af6\"}"
