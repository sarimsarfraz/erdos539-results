/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SharpExponentBounds

namespace Erdos539Geometry

theorem sharpExponent_double_of_uniform {d : ℕ} (hd : 0 < d)
    (he : (sharpExponent d : ℝ) = uniformExponent d) :
    (sharpExponent (2 * d) : ℝ) = uniformExponent (2 * d) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (0 : ℝ) < 2 * d - 1 := by linarith
  have hden' : (0 : ℝ) < 4 * d - 1 := by linarith
  have ht : (0 : ℝ) < 1 + (d : ℝ) / (2 * d - 1) + (d : ℝ) / (2 * d - 1) := by positivity
  apply le_antisymm _ (sharpExponent_ge_uniform (by omega : 0 < 2 * d))
  have h : (sharpExponent (d + d) : ℝ) ≤
      (combineExponent (sharpExponent d) (sharpExponent d) : ℝ) := by
    exact_mod_cast sharpExponent_le_split hd hd
  rw [combineExponent] at h
  push_cast at h
  rw [he] at h
  calc
    (sharpExponent (2 * d) : ℝ) ≤ (uniformExponent d + uniformExponent d) /
        (1 + uniformExponent d + uniformExponent d) := by simpa only [two_mul] using h
    _ = uniformExponent (2 * d) := by
      unfold uniformExponent
      push_cast
      rw [show (2 : ℝ) * (2 * d) - 1 = 4 * d - 1 by ring]
      apply (div_eq_div_iff ht.ne' hden'.ne').mpr
      field_simp (disch := linarith)
      ring

/-- The lower comparison exponent is attained in every power-of-two dimension. -/
theorem sharpExponent_power_two (k : ℕ) :
    (sharpExponent (2 ^ k) : ℝ) = uniformExponent (2 ^ k) := by
  induction k with
  | zero => norm_num [uniformExponent]
  | succ k ih =>
    rw [pow_succ, Nat.mul_comm]
    exact sharpExponent_double_of_uniform (pow_pos (by decide) _) ih

end Erdos539Geometry
