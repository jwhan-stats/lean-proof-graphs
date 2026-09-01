import Mathlib

theorem graph_exporter_smoke (x : ℝ) (hx : 0 < x) : 0 < 2 * x := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  exact mul_pos h2 hx
