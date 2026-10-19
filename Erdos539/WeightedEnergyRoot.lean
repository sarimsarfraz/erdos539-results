/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.WeightedHolder
import Mathlib.Data.Real.Sqrt

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The nonnegative fourth root of additive energy. -/
def energyFourthRoot (S : Finset G) (f : G → ℝ) : ℝ :=
  Real.sqrt (Real.sqrt (weightedEnergy S f))

theorem energyFourthRoot_nonneg (S : Finset G) (f : G → ℝ) : 0 ≤ energyFourthRoot S f :=
  Real.sqrt_nonneg _

theorem energyFourthRoot_pow_four (S : Finset G) (f : G → ℝ) :
    energyFourthRoot S f ^ 4 = weightedEnergy S f := by
  unfold energyFourthRoot
  rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul,
    Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (weightedEnergy_nonneg S f)]

/-- Mixed-energy Holder with the actual nonnegative fourth roots. -/
theorem mixedWeightedEnergy_le_roots (S : Finset G) (f g h k : G → ℝ) :
    mixedWeightedEnergy S f g h k ≤
      energyFourthRoot S f * energyFourthRoot S g * energyFourthRoot S h * energyFourthRoot S k := by
  apply le_of_pow_le_pow_left₀ (by decide : (4 : ℕ) ≠ 0)
    (mul_nonneg (mul_nonneg (mul_nonneg (energyFourthRoot_nonneg S f)
      (energyFourthRoot_nonneg S g)) (energyFourthRoot_nonneg S h)) (energyFourthRoot_nonneg S k))
  simpa only [mul_pow, energyFourthRoot_pow_four] using mixedWeightedEnergy_fourth_le S f g h k

omit [DecidableEq G] in
theorem weightedConvolution_add_left (S : Finset G) (f g h : G → ℝ) (z : G) :
    weightedConvolution S (f + g) h z = weightedConvolution S f h z + weightedConvolution S g h z := by
  simp only [weightedConvolution, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem mixedWeightedEnergy_add_first (S : Finset G) (f g h k l : G → ℝ) :
    mixedWeightedEnergy S (f + g) h k l = mixedWeightedEnergy S f h k l + mixedWeightedEnergy S g h k l := by
  simp only [mixedWeightedEnergy, weightedConvolution_add_left, add_mul, Finset.sum_add_distrib]

/-- The fourth-root triangle inequality, proved from finite mixed Holder.
Weights may have either sign. -/
theorem energyFourthRoot_add_le (S : Finset G) (f g : G → ℝ) :
    energyFourthRoot S (f + g) ≤ energyFourthRoot S f + energyFourthRoot S g := by
  let R := energyFourthRoot S (f + g)
  have hR : 0 ≤ R := energyFourthRoot_nonneg S (f + g)
  have hf := mixedWeightedEnergy_le_roots S f (f + g) (f + g) (f + g)
  have hg := mixedWeightedEnergy_le_roots S g (f + g) (f + g) (f + g)
  have he : R ^ 4 = mixedWeightedEnergy S f (f + g) (f + g) (f + g) +
      mixedWeightedEnergy S g (f + g) (f + g) (f + g) := by
    rw [energyFourthRoot_pow_four, ← mixedWeightedEnergy_self, mixedWeightedEnergy_add_first]
  have hmain : R ^ 4 ≤ (energyFourthRoot S f + energyFourthRoot S g) * R ^ 3 := by
    dsimp [R] at he ⊢
    nlinarith
  by_cases hzero : R = 0
  · change R ≤ _
    rw [hzero]
    exact add_nonneg (energyFourthRoot_nonneg S f) (energyFourthRoot_nonneg S g)
  · have hp : 0 < R := lt_of_le_of_ne hR (Ne.symm hzero)
    apply (mul_le_mul_iff_right₀ (pow_pos hp 3)).mp
    change R ^ 3 * R ≤ _
    nlinarith

end
end Erdos539Geometry
