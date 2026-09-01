theorem strict_convex_modular_fixed_point
    {X : Type*} (b : X) (w : NNReal → X → X → ENNReal)
    (hself : ∀ (l : NNReal), 0 < l → ∀ x : X, w l x x = 0)
    (hsymm : ∀ (l : NNReal), 0 < l → ∀ x y : X, w l x y = w l y x)
    (hstrict : ∀ x y : X, (∃ l : NNReal, 0 < l ∧ w l x y = 0) → x = y)
    (hconv : ∀ (l m : NNReal), 0 < l → 0 < m → ∀ x y z : X,
      w (l + m) x y ≤ ((l : ENNReal) / (l + m)) * w l x z +
        ((m : ENNReal) / (l + m)) * w m y z)
    (hcomplete : ∀ (x : ℕ → {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤})
      (l : NNReal), 0 < l →
      Filter.Tendsto (fun p : ℕ × ℕ => w l (x p.1) (x p.2))
        (Filter.atTop ×ˢ Filter.atTop) (nhds 0) →
      ∃ y : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
        Filter.Tendsto (fun n => w l (x n) y) Filter.atTop (nhds 0))
    (T : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤} →
      {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤})
    (hcontractive : ∃ k L : NNReal, 0 < k ∧ k < 1 ∧ 0 < L ∧
      ∀ x y : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
        ∀ l : NNReal, 0 < l → l ≤ L → w (k * l) (T x) (T y) ≤ w l x y) :
    ((∀ l : NNReal, 0 < l →
        ∃ x : {x : X // ∃ m : NNReal, 0 < m ∧ w m x b < ⊤},
          w l x (T x) < ⊤) →
      ∃ x : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤}, T x = x) ∧
    ((∀ l : NNReal, 0 < l →
        ∀ x y : {x : X // ∃ m : NNReal, 0 < m ∧ w m x b < ⊤}, w l x y < ⊤) →
      ∃ xstar : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
        T xstar = xstar ∧
        (∀ y : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
          T y = y → y = xstar) ∧
        ∀ x : {x : X // ∃ l : NNReal, 0 < l ∧ w l x b < ⊤},
          ∃ l : NNReal, 0 < l ∧
            Filter.Tendsto (fun n : ℕ => w l ((T^[n]) x) xstar)
              Filter.atTop (nhds 0)) := by sorry
