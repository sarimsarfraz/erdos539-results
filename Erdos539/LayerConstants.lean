/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.LayerEstimates

namespace Erdos539Geometry
noncomputable section

/-- The manuscript's constant 4^(-(d-1)) for recursively ordered layer products. -/
def layerConstant (d : ℕ) : ℝ := (4 : ℝ) ^ (-((d : ℝ) - 1))

@[simp] theorem layerConstant_one : layerConstant 1 = 1 := by simp [layerConstant]

theorem layerConstant_pos (d : ℕ) : 0 < layerConstant d := Real.rpow_pos_of_pos (by norm_num) _

theorem layerConstant_le_one {d : ℕ} (hd : 0 < d) : layerConstant d ≤ 1 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)

theorem layerConstant_split (p s : ℕ) : layerConstant p * layerConstant s / 4 = layerConstant (p + s) := by
  unfold layerConstant
  rw [div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add (by norm_num : (0 : ℝ) < 4),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 4)]
  congr 1
  push_cast
  ring

end
end Erdos539Geometry
