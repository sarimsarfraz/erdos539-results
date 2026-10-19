/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ReferenceGibbs
import Erdos539.EnergyNormLower
import Erdos539.EnergySupport

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Counting-measure additive energy, using the same literal convolution
as the weighted norm. -/
def countingEnergy (S : Finset G) : ℝ := weightedEnergy S (fun _ ↦ 1)

theorem countingEnergy_pos {S : Finset G} (hS : S.Nonempty) : 0 < countingEnergy S := by
  have hN : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have h := weightedEnergy_ge_squareSum_sq S (fun _ ↦ 1)
  simp only [weightSquareSum, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  exact (sq_pos_of_pos hN).trans_le h

theorem weightedGibbsPartition_constant (S : Finset G) (c : ℝ) :
    weightedGibbsPartition S (fun _ ↦ c) = c ^ 4 * countingEnergy S := by
  calc
    _ = weightedEnergy S (fun _ ↦ c * 1) := by
      apply weightedEnergy_congr
      intro x hx
      simp only [extendWeight, dif_pos hx, mul_one]
    _ = _ := weightedEnergy_scale S (fun _ ↦ 1) c

def uniformReference (S : Finset G) : S → ℝ := fun _ ↦ 1 / S.card

omit [AddCommGroup G] [DecidableEq G] in
theorem uniformReference_pos {S : Finset G} (hS : S.Nonempty) (x : S) : 0 < uniformReference S x :=
  one_div_pos.mpr (by exact_mod_cast hS.card_pos)

omit [AddCommGroup G] [DecidableEq G] in
theorem uniformReference_sum {S : Finset G} (hS : S.Nonempty) : ∑ x, uniformReference S x = 1 := by
  have hN : (S.card : ℝ) ≠ 0 := (show (0 : ℝ) < S.card by exact_mod_cast hS.card_pos).ne'
  simp [uniformReference, hN]

/-- Exact uniform-root partition function. -/
theorem referencePartition_uniform {S : Finset G} (hS : S.Nonempty) :
    referencePartition S (uniformReference S) = countingEnergy S / (S.card : ℝ) ^ 3 := by
  change weightedGibbsPartition S (fun _ ↦ (1 / (S.card : ℝ)) ^ (3 / 4 : ℝ)) = _
  rw [weightedGibbsPartition_constant, ← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ 1 / S.card)]
  norm_num
  ring

/-- The initial deficit has the literal counting-energy formula. -/
theorem referenceDeficit_uniform {S : Finset G} (hS : S.Nonempty) :
    referenceDeficit S (uniformReference S) = Real.log ((S.card : ℝ) ^ 3 / countingEnergy S) := by
  have hN : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hE := countingEnergy_pos hS
  rw [referenceDeficit, referencePartition_uniform hS,
    Real.log_div hE.ne' (pow_pos hN 3).ne', Real.log_div (pow_pos hN 3).ne' hE.ne']
  ring

/-- Uniform reference starts within the ordinary difference-doubling
budget, for every nonempty support and without equal-fiber assumptions. -/
theorem referenceDeficit_uniform_le_log_doubling {S : Finset G} (hS : S.Nonempty) :
    referenceDeficit S (uniformReference S) ≤ Real.log ((S - S).card / (S.card : ℝ)) := by
  have hN : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hE := countingEnergy_pos hS
  have h := sum_weight_fourth_le_difference_energy S (fun _ ↦ 1)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have hr : (S.card : ℝ) ^ 3 / countingEnergy S ≤ (S - S).card / (S.card : ℝ) := by
    apply (div_le_div_iff₀ hE hN).mpr
    change (S.card : ℝ) ^ 3 * S.card ≤ (S - S).card * countingEnergy S
    simpa only [← pow_succ] using h
  rw [referenceDeficit_uniform hS]
  exact Real.log_le_log (div_pos (pow_pos hN 3) hE) hr

end
end Erdos539Geometry
