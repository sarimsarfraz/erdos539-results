/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SharpSidonScalar
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators

theorem sharp_sidon_half_power_sq {a : ℝ} (ha : 0 ≤ a) :
    (a ^ (sharpSidonExponent / 2)) ^ 2 = a ^ sharpSidonExponent := by
  rw [← Real.rpow_mul_natCast ha]
  congr 1
  norm_num

theorem sharp_sidon_add_half_power {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ (sharpSidonExponent / 2) + b ^ (sharpSidonExponent / 2) ≤ (a + b) ^ (sharpSidonExponent / 2) := by
  have h := sharp_sidon_scalar ha hb
  rw [Real.mul_rpow ha hb, ← sharp_sidon_half_power_sq ha,
    ← sharp_sidon_half_power_sq hb, ← sharp_sidon_half_power_sq (add_nonneg ha hb)] at h
  have hab : 0 ≤ a ^ (sharpSidonExponent / 2) * b ^ (sharpSidonExponent / 2) := by positivity
  have hr : 0 ≤ (a + b) ^ (sharpSidonExponent / 2) := by positivity
  nlinarith

/-- Arbitrary finite Sidon-label energy, with the sharp logarithmic
exponent. The two induction invariants are proved together. -/
theorem sharp_sidon_sums {ι : Type*} (S : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) :
    (∑ i ∈ S, a i ^ (sharpSidonExponent / 2)) ≤ (∑ i ∈ S, a i) ^ (sharpSidonExponent / 2) ∧
    2 * (∑ i ∈ S, a i ^ (sharpSidonExponent / 2)) ^ 2 -
      (∑ i ∈ S, a i ^ sharpSidonExponent) ≤ (∑ i ∈ S, a i) ^ sharpSidonExponent := by
  classical
  have hp : 0 < sharpSidonExponent := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) sharpSidonExponent_bounds.1
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Real.zero_rpow hp.ne',
      Real.zero_rpow (show sharpSidonExponent / 2 ≠ 0 by positivity)]
    norm_num
  | @insert i S hi ih =>
    have hai := ha i (Finset.mem_insert_self i S)
    have haS : ∀ j ∈ S, 0 ≤ a j := fun j hj ↦ ha j (Finset.mem_insert_of_mem hj)
    obtain ⟨hfirst, hsecond⟩ := ih haS
    have hsum : 0 ≤ ∑ j ∈ S, a j := Finset.sum_nonneg haS
    simp only [Finset.sum_insert hi]
    constructor
    · calc
        _ ≤ a i ^ (sharpSidonExponent / 2) + (∑ j ∈ S, a j) ^ (sharpSidonExponent / 2) := add_le_add le_rfl hfirst
        _ ≤ _ := sharp_sidon_add_half_power hai hsum
    · have hscalar := sharp_sidon_scalar hai hsum
      rw [Real.mul_rpow hai hsum] at hscalar
      have hcross := mul_le_mul_of_nonneg_left hfirst
        (Real.rpow_nonneg hai (sharpSidonExponent / 2))
      have hsquare := sharp_sidon_half_power_sq hai
      nlinarith

theorem sharp_sidon_energy_bound {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) :
    2 * (∑ i ∈ S, w i ^ 2) ^ 2 - (∑ i ∈ S, w i ^ 4) ≤
      (∑ i ∈ S, w i ^ (4 / sharpSidonExponent)) ^ sharpSidonExponent := by
  have hp : sharpSidonExponent ≠ 0 := ne_of_gt
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) sharpSidonExponent_bounds.1)
  have h := (sharp_sidon_sums S (fun i ↦ w i ^ (4 / sharpSidonExponent))
    (fun i hi ↦ Real.rpow_nonneg (hw i hi) _)).2
  have he2 : (4 / sharpSidonExponent) * (sharpSidonExponent / 2) = 2 := by
    field_simp
    norm_num
  have he4 : (4 / sharpSidonExponent) * sharpSidonExponent = 4 := div_mul_cancel₀ _ hp
  have htwo : ∀ i ∈ S, (w i ^ (4 / sharpSidonExponent)) ^ (sharpSidonExponent / 2) = w i ^ 2 := by
    intro i hi
    rw [← Real.rpow_mul (hw i hi), he2]
    norm_num
  have hfour : ∀ i ∈ S, (w i ^ (4 / sharpSidonExponent)) ^ sharpSidonExponent = w i ^ 4 := by
    intro i hi
    rw [← Real.rpow_mul (hw i hi), he4]
    norm_num
  rwa [Finset.sum_congr rfl htwo, Finset.sum_congr rfl hfour] at h

end
end Erdos539Geometry
