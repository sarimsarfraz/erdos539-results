/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace Erdos539Geometry
noncomputable section

/-- A non-optimal exponent sufficient for the unrestricted quantitative bound. -/
def uniformExponent (d : ℕ) : ℝ := (d : ℝ) / (2 * d - 1)

theorem uniformExponent_pos {d : ℕ} (hd : 0 < d) : 0 < uniformExponent d := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  exact div_pos (by positivity) (by linarith)

theorem uniformExponent_le_one {d : ℕ} (hd : 0 < d) : uniformExponent d ≤ 1 := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  apply (div_le_one (by linarith : (0 : ℝ) < 2 * d - 1)).mpr
  linarith

theorem uniformExponent_ge_half_add {d : ℕ} (hd : 0 < d) :
    1 / 2 + 1 / (4 * (d : ℝ)) ≤ uniformExponent d := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (0 : ℝ) < 2 * d - 1 := by linarith
  rw [uniformExponent, le_div_iff₀ hden]
  field_simp
  nlinarith

theorem uniformExponent_split {p s : ℕ} (hp : 0 < p) (hs : 0 < s) :
    uniformExponent (p + s) ≤
      (uniformExponent p + uniformExponent s) / (1 + uniformExponent p + uniformExponent s) := by
  have hp' : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hs' : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hpd : (0 : ℝ) < 2 * p - 1 := by linarith
  have hsd : (0 : ℝ) < 2 * s - 1 := by linarith
  have hmd : (0 : ℝ) < 2 * (p + s) - 1 := by linarith
  have ht : 0 < 1 + uniformExponent p + uniformExponent s := by
    linarith [uniformExponent_pos hp, uniformExponent_pos hs]
  change ((p + s : ℕ) : ℝ) / (2 * (p + s : ℕ) - 1) ≤ _
  push_cast
  apply (div_le_div_iff₀ hmd ht).mpr
  have ha : (uniformExponent p + uniformExponent s) *
      ((2 * (p : ℝ) - 1) * (2 * (s : ℝ) - 1)) =
      (p : ℝ) * (2 * s - 1) + s * (2 * p - 1) := by
    dsimp only [uniformExponent]
    calc
      _ = ((p : ℝ) / (2 * p - 1) * (2 * p - 1)) * (2 * s - 1) +
        ((s : ℝ) / (2 * s - 1) * (2 * s - 1)) * (2 * p - 1) := by ring
      _ = _ := by rw [div_mul_cancel₀ _ hpd.ne', div_mul_cancel₀ _ hsd.ne']
  apply (mul_le_mul_iff_of_pos_right (mul_pos hpd hsd)).mp
  calc
    _ = ((p : ℝ) + s) * ((2 * p - 1) * (2 * s - 1) +
        (uniformExponent p + uniformExponent s) * ((2 * p - 1) * (2 * s - 1))) := by ring
    _ = ((p : ℝ) + s) * ((2 * p - 1) * (2 * s - 1) +
        (p * (2 * s - 1) + s * (2 * p - 1))) := by rw [ha]
    _ ≤ ((p : ℝ) * (2 * s - 1) + s * (2 * p - 1)) * (2 * (p + s) - 1) := by
      nlinarith [sq_nonneg ((p : ℝ) - s)]
    _ = _ := by rw [← ha]; ring

/-- Logarithmic regularity cost used with the simpler uniform exponent. -/
def regularityCost (d : ℕ) : ℝ := Real.log d / Real.log 2

theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

theorem regularityCost_nonneg {d : ℕ} (hd : 0 < d) : 0 ≤ regularityCost d := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  exact div_nonneg (Real.log_nonneg hd') log_two_pos.le

theorem one_le_regularityCost {d : ℕ} (hd : 2 ≤ d) : 1 ≤ regularityCost d := by
  rw [regularityCost, le_div_iff₀ log_two_pos, one_mul]
  exact Real.log_le_log (by norm_num) (by exact_mod_cast hd)

end
end Erdos539Geometry
