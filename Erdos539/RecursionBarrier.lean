/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SharpPowerTwo

namespace Erdos539Geometry

/-- The forced balanced-split recurrence accumulates one cost per level. -/
theorem balanced_cost_weighted_lower (α : ℕ → ℝ) (hzero : 0 ≤ α 0)
    (hstep : ∀ k : ℕ,
      (2 * (2 : ℝ) ^ (k + 1) - 1) * α (k + 1) ≥
        (2 * (2 : ℝ) ^ (k + 1) - 2) * α k + (2 : ℝ) ^ (k + 1)) :
    ∀ k : ℕ, (2 : ℝ) ^ k * k ≤ (2 * (2 : ℝ) ^ k - 1) * α k := by
  intro k
  induction k with
  | zero => simpa using hzero
  | succ k ih =>
    have hs := hstep k
    rw [pow_succ] at hs ⊢
    push_cast
    nlinarith

/-- No bounded regularity cost can satisfy this recursion in every power-of-two
 dimension: the exact lower cost is d log₂(d)/(2d-1). -/
theorem balanced_cost_lower (α : ℕ → ℝ) (hzero : 0 ≤ α 0)
    (hstep : ∀ k : ℕ,
      (2 * (2 : ℝ) ^ (k + 1) - 1) * α (k + 1) ≥
        (2 * (2 : ℝ) ^ (k + 1) - 2) * α k + (2 : ℝ) ^ (k + 1)) (k : ℕ) :
    (2 : ℝ) ^ k * k / (2 * (2 : ℝ) ^ k - 1) ≤ α k := by
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  apply (div_le_iff₀ (by linarith : 0 < 2 * (2 : ℝ) ^ k - 1)).mpr
  nlinarith [balanced_cost_weighted_lower α hzero hstep k]

/-- The actual sharp-exponent recursion implies the weighted recurrence. -/
theorem regularity_recursion_power_two_lower (α : ℕ → ℝ) (hzero : 0 ≤ α 1)
    (hclose : ∀ k : ℕ,
      (2 * α (2 ^ k) + 2 * (sharpExponent (2 ^ k) : ℝ)) /
        (1 + 2 * (sharpExponent (2 ^ k) : ℝ)) ≤ α (2 ^ (k + 1))) (k : ℕ) :
    (2 : ℝ) ^ k * k / (2 * (2 : ℝ) ^ k - 1) ≤ α (2 ^ k) := by
  apply balanced_cost_lower (fun j ↦ α (2 ^ j)) (by simpa using hzero) _ k
  intro j
  have h := hclose j
  rw [sharpExponent_power_two, uniformExponent] at h
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at h
  have hd : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hden : 0 < 2 * (2 : ℝ) ^ j - 1 := by linarith
  have ht : 0 < 1 + 2 * ((2 : ℝ) ^ j / (2 * (2 : ℝ) ^ j - 1)) := by positivity
  have hh := (div_le_iff₀ ht).mp h
  have hh' := mul_le_mul_of_nonneg_right hh hden.le
  field_simp at hh'
  rw [pow_succ]
  nlinarith

/-- A cost closing every balanced split cannot be bounded independently of dimension. -/
theorem regularity_recursion_unbounded (α : ℕ → ℝ) (hzero : 0 ≤ α 1)
    (hclose : ∀ k : ℕ,
      (2 * α (2 ^ k) + 2 * (sharpExponent (2 ^ k) : ℝ)) /
        (1 + 2 * (sharpExponent (2 ^ k) : ℝ)) ≤ α (2 ^ (k + 1))) :
    ∀ C : ℝ, ∃ k : ℕ, C < α (2 ^ k) := by
  intro C
  obtain ⟨k, hk⟩ := exists_nat_gt (2 * C)
  have h := regularity_recursion_power_two_lower α hzero hclose k
  have hp : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hden : 0 < 2 * (2 : ℝ) ^ k - 1 := by linarith
  have hhalf : (k : ℝ) / 2 ≤ (2 : ℝ) ^ k * k / (2 * (2 : ℝ) ^ k - 1) := by
    apply (le_div_iff₀ hden).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) k]
  exact ⟨k, lt_of_lt_of_le (by linarith : C < (k : ℝ) / 2) (hhalf.trans h)⟩

end Erdos539Geometry
