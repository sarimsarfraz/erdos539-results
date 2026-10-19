/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.RationalSidonScalar
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators

theorem rational_sidon_half_power_sq {a : ℝ} (ha : 0 ≤ a) :
    (a ^ (13 / 10 : ℝ)) ^ 2 = a ^ (13 / 5 : ℝ) := by
  rw [← Real.rpow_mul_natCast ha]
  norm_num

/-- The companion bound needed when merging arbitrarily many labels. -/
theorem rational_sidon_add_half_power {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ (13 / 10 : ℝ) + b ^ (13 / 10 : ℝ) ≤ (a + b) ^ (13 / 10 : ℝ) := by
  have h := rational_sidon_scalar ha hb
  rw [Real.mul_rpow ha hb, ← rational_sidon_half_power_sq ha,
    ← rational_sidon_half_power_sq hb, ← rational_sidon_half_power_sq (add_nonneg ha hb)] at h
  have hab : 0 ≤ a ^ (13 / 10 : ℝ) * b ^ (13 / 10 : ℝ) := by positivity
  have hr : 0 ≤ (a + b) ^ (13 / 10 : ℝ) := by positivity
  nlinarith

/-- Finite Sidon-label inequality in transformed weights. Both bounds
are proved together, so no component or sum-power assumption is inserted. -/
theorem rational_sidon_sums {ι : Type*} (S : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) :
    (∑ i ∈ S, a i ^ (13 / 10 : ℝ)) ≤ (∑ i ∈ S, a i) ^ (13 / 10 : ℝ) ∧
    2 * (∑ i ∈ S, a i ^ (13 / 10 : ℝ)) ^ 2 -
      (∑ i ∈ S, a i ^ (13 / 5 : ℝ)) ≤ (∑ i ∈ S, a i) ^ (13 / 5 : ℝ) := by
  classical
  induction S using Finset.induction_on with
  | empty => norm_num
  | @insert i S hi ih =>
    have hai := ha i (Finset.mem_insert_self i S)
    have haS : ∀ j ∈ S, 0 ≤ a j := fun j hj ↦ ha j (Finset.mem_insert_of_mem hj)
    obtain ⟨hfirst, hsecond⟩ := ih haS
    have hsum : 0 ≤ ∑ j ∈ S, a j := Finset.sum_nonneg haS
    simp only [Finset.sum_insert hi]
    constructor
    · calc
        _ ≤ a i ^ (13 / 10 : ℝ) + (∑ j ∈ S, a j) ^ (13 / 10 : ℝ) := add_le_add le_rfl hfirst
        _ ≤ _ := rational_sidon_add_half_power hai hsum
    · have hscalar := rational_sidon_scalar hai hsum
      rw [Real.mul_rpow hai hsum] at hscalar
      have hcross := mul_le_mul_of_nonneg_left hfirst
        (Real.rpow_nonneg hai (13 / 10))
      have hsquare := rational_sidon_half_power_sq hai
      nlinarith

/-- Rational Sidon energy bound for arbitrary nonnegative label weights.
The left side equals the sum of diagonal fourth powers and four times the
sum of unordered cross products. -/
theorem rational_sidon_energy_bound {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) :
    2 * (∑ i ∈ S, w i ^ 2) ^ 2 - (∑ i ∈ S, w i ^ 4) ≤
      (∑ i ∈ S, w i ^ (20 / 13 : ℝ)) ^ (13 / 5 : ℝ) := by
  have h := (rational_sidon_sums S (fun i ↦ w i ^ (20 / 13 : ℝ))
    (fun i hi ↦ Real.rpow_nonneg (hw i hi) _)).2
  have htwo : ∀ i ∈ S, (w i ^ (20 / 13 : ℝ)) ^ (13 / 10 : ℝ) = w i ^ 2 := by
    intro i hi
    rw [← Real.rpow_mul (hw i hi)]
    norm_num
  have hfour : ∀ i ∈ S, (w i ^ (20 / 13 : ℝ)) ^ (13 / 5 : ℝ) = w i ^ 4 := by
    intro i hi
    rw [← Real.rpow_mul (hw i hi)]
    norm_num
  rwa [Finset.sum_congr rfl htwo, Finset.sum_congr rfl hfour] at h

end
end Erdos539Geometry
