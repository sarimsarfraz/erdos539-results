/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ElementaryIntegerGrowth
import Erdos539.Threshold

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical

theorem growthParameter_lower {n q : ℕ} (hn : 0 < n) (h : n ≤ q ^ 2) :
    Real.log 2 ≤ growthParameter n q := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hK : 1 ≤ (q : ℝ) ^ 2 / n := by
    apply (le_div_iff₀ hn').mpr
    simpa only [one_mul, Nat.cast_pow] using (show (n : ℝ) ≤ (q ^ 2 : ℕ) by exact_mod_cast h)
  apply Real.log_le_log (by norm_num)
  linarith

theorem positive_card_le_cofactors_sq {A : Finset ℕ} (hA : A.Nonempty)
    (hpos : ∀ a ∈ A, 0 < a) : A.card ≤ (cofactors A).card ^ 2 := by
  have hF : (integerExponentSet A).Nonempty := Finset.card_pos.mp (by
    rw [integerExponentSet_card hpos]
    exact hA.card_pos)
  simpa only [integerExponentSet_card hpos, integerPositiveDifferences_integerExponentSet_card hpos]
    using card_le_integerPositiveDifferences_sq hF

theorem positive_log_growth {A : Finset ℕ} (hA : A.Nonempty) (hpos : ∀ a ∈ A, 0 < a) :
    Real.log A.card ≤ 2000000 * (growthParameter A.card (cofactors A).card) ^ 2 *
      (1 + Real.log (growthParameter A.card (cofactors A).card + 1)) := by
  have hF : (integerExponentSet A).Nonempty := Finset.card_pos.mp (by
    rw [integerExponentSet_card hpos]
    exact hA.card_pos)
  simpa only [integerExponentSet_card hpos, integerPositiveDifferences_integerExponentSet_card hpos]
    using elementary_integer_log_growth hF

theorem growth_expression_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ 2 * (1 + Real.log (x + 1)) ≤ y ^ 2 * (1 + Real.log (y + 1)) := by
  have hlx : 0 ≤ Real.log (x + 1) := Real.log_nonneg (by linarith)
  have hlog := Real.log_le_log (show 0 < x + 1 by linarith) (show x + 1 ≤ y + 1 by linarith)
  have hsq : x ^ 2 ≤ y ^ 2 := by nlinarith
  exact mul_le_mul hsq (by linarith) (by linarith) (sq_nonneg y)

def thresholdGrowthParameter (n q : ℕ) : ℝ := Real.log (4 * ((q : ℝ) ^ 2 / n))

/-- Zero-inclusive finite-set growth, with the one-point loss fully absorbed. -/
theorem cofactor_log_growth {A : Finset ℕ} (hn : 2 ≤ A.card) :
    Real.log 2 ≤ thresholdGrowthParameter A.card (cofactors A).card ∧
    Real.log A.card ≤ 4000000 * (thresholdGrowthParameter A.card (cofactors A).card) ^ 2 *
      (1 + Real.log (thresholdGrowthParameter A.card (cofactors A).card + 1)) := by
  classical
  have hA : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨B, hBA, hBcard, hBpos⟩ := Erdos539.positive_subset_pred hA
  have hB : B.Nonempty := Finset.card_pos.mp (by omega)
  have hn' : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hb' : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hn2b : (A.card : ℝ) ≤ 2 * B.card := by exact_mod_cast (show A.card ≤ 2 * B.card by omega)
  have hQB : B.card ≤ (cofactors B).card ^ 2 := positive_card_le_cofactors_sq hB hBpos
  have hqbNat : 0 < (cofactors B).card := by have := hB.card_pos; nlinarith
  have hqb : (0 : ℝ) < (cofactors B).card := by exact_mod_cast hqbNat
  have hqmono : ((cofactors B).card : ℝ) ≤ (cofactors A).card := by
    exact_mod_cast Finset.card_le_card (Erdos539.cofactors_mono hBA)
  let x := growthParameter B.card (cofactors B).card
  let y := thresholdGrowthParameter A.card (cofactors A).card
  have hx : Real.log 2 ≤ x := growthParameter_lower hB.card_pos hQB
  have hxy : x ≤ y := by
    apply Real.log_le_log (show 0 < 2 * (((cofactors B).card : ℝ) ^ 2 / B.card) by positivity)
    rw [← mul_div_assoc, ← mul_div_assoc]
    apply (div_le_div_iff₀ hb' hn').mpr
    have hqSq : ((cofactors B).card : ℝ) ^ 2 ≤ ((cofactors A).card : ℝ) ^ 2 := by nlinarith
    have h₁ := mul_le_mul_of_nonneg_right hqSq hn'.le
    have h₂ := mul_le_mul_of_nonneg_left hn2b (sq_nonneg ((cofactors A).card : ℝ))
    nlinarith
  refine ⟨hx.trans hxy, ?_⟩
  have hx0 : 0 ≤ x := log_two_pos.le.trans hx
  have hy0 : 0 ≤ y := hx0.trans hxy
  have hBbound : Real.log B.card ≤ 2000000 * (y ^ 2 * (1 + Real.log (y + 1))) := by
    have h := positive_log_growth hB hBpos
    have hm := mul_le_mul_of_nonneg_left (growth_expression_mono hx0 hxy) (by norm_num : (0 : ℝ) ≤ 2000000)
    change Real.log B.card ≤ 2000000 * x ^ 2 * (1 + Real.log (x + 1)) at h
    nlinarith
  have hlogn := Real.log_le_log hn' hn2b
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hb'.ne'] at hlogn
  have hl2low : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hl2high : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hyhalf : 1 / 2 ≤ y := hl2low.trans (hx.trans hxy)
  have hlogy : 0 ≤ Real.log (y + 1) := Real.log_nonneg (by linarith)
  have hextra : 1 ≤ 4 * (y ^ 2 * (1 + Real.log (y + 1))) := by
    nlinarith [mul_nonneg (sq_nonneg y) hlogy]
  change Real.log A.card ≤ 4000000 * y ^ 2 * (1 + Real.log (y + 1))
  nlinarith [mul_nonneg (sq_nonneg y) (show 0 ≤ 1 + Real.log (y + 1) by linarith)]

end
end Erdos539Geometry
