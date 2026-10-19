/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SmallDimensionEstimates

namespace Erdos539Geometry

/-- The final two-corner theorem pays 2^(d+1) in the base-two logarithm. -/
def cornerFanLoss (d : ℕ) : ℝ := 2 ^ (d + 1)

theorem cornerFanLoss_split {p s : ℕ} (hp : 0 < p) (hs : 0 < s) :
    cornerFanLoss p + cornerFanLoss s ≤ cornerFanLoss (p + s) := by
  have hP : (2 : ℝ) ≤ 2 ^ p := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hp
  have hS : (2 : ℝ) ≤ 2 ^ s := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hs
  unfold cornerFanLoss
  rw [pow_succ, pow_succ, pow_succ, pow_add]
  nlinarith [mul_nonneg (sub_nonneg.mpr hP) (sub_nonneg.mpr hS)]

/-- The deterministic selector's loss fits the target from dimension four
onward; dimensions one through three use the stronger existing base cases. -/
theorem corner_selection_loss_budget {d : ℕ} (hd : 4 ≤ d) :
    ((3 * 2 ^ (d - 1) + 5 : ℕ) : ℝ) + 1 ≤ cornerFanLoss d := by
  have hp : (8 : ℝ) ≤ 2 ^ (d - 1) := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show 3 ≤ d - 1 by omega)
    norm_num at h
    exact h
  have hd' : d + 1 = (d - 1) + 2 := by omega
  unfold cornerFanLoss
  rw [hd', pow_add]
  push_cast
  norm_num
  linarith

theorem corner_small_loss_budget {d : ℕ} (hd0 : 0 < d) (hd3 : d ≤ 3) :
    3 * (d : ℝ) ≤ cornerFanLoss d := by
  rcases (show d = 1 ∨ d = 2 ∨ d = 3 by omega) with h | h | h <;>
    subst d <;> norm_num [cornerFanLoss]

/-- Scalar closure of two-corner selection and the common-anchor pruning step. -/
theorem corner_split_closes {a b u N E P Q M L A V Cp Cs : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hN : 0 ≤ N) (hL : 0 ≤ L)
    (hu : u ≤ (a + b) / (1 + a + b)) (hconst : Cp + Cs ≤ A) (hselect : V + 1 ≤ A)
    (hsize : N ≤ V * L + E) (hP : P ≤ M) (hQ : Q ≤ M)
    (hprune : a * (E - L - Q) + b * (E - L - P) - Cp * L - Cs * L ≤ M) :
    u * N - A * L ≤ M := by
  have hden : 0 < 1 + a + b := by linarith
  have hu' := mul_le_mul_of_nonneg_right ((le_div_iff₀ hden).mp hu) hN
  have hsize' := mul_le_mul_of_nonneg_left hsize (show 0 ≤ a + b by linarith)
  have hP' := mul_le_mul_of_nonneg_left hP hb
  have hQ' := mul_le_mul_of_nonneg_left hQ ha
  have hconst' := mul_le_mul_of_nonneg_right hconst hL
  have hselect' := mul_le_mul_of_nonneg_right hselect (mul_nonneg (show 0 ≤ a + b by linarith) hL)
  apply (mul_le_mul_iff_right₀ hden).mp
  nlinarith

end Erdos539Geometry
