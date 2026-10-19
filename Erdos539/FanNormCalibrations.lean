/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FanNormEntropyEquivalence
import Erdos539.ScalarFanEntropyCalibration
import Erdos539.FanEntropyDefect

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
local instance scalarNormCalibrationDecidableEq : DecidableEq ℝ := Classical.decEq _

/-- Every positive scalar exponent below four has a uniform weighted
energy bound, with the explicit constant from the scalar fan theorem. -/
theorem scalar_fanNormBound {S : Finset ℝ} (hS : S.Nonempty) {p : ℝ}
    (hp : 0 < p) (hp4 : p < 4) :
    FanNormBound S (scalarPositiveDifferenceChannel S) p
      (Real.exp (4 * Real.log (4 / (4 / p - 1)) + 2 + 2 * (4 / p - 1))) := by
  apply FanEntropyBound.to_norm hS hp (Real.exp_pos _)
  intro ν hν hs
  rw [Real.log_exp]
  exact scalar_stationary_entropy_power_bound S ν hν hs hp hp4

theorem scalar_fanNormBound_twelve_fifths {S : Finset ℝ} (hS : S.Nonempty) :
    FanNormBound S (scalarPositiveDifferenceChannel S) (12 / 5)
      (Real.exp (2 * (1 + (2 / 3 : ℝ) * Real.log 24))) := by
  apply FanEntropyBound.to_norm hS (by norm_num) (Real.exp_pos _)
  intro ν hν hs
  rw [Real.log_exp]
  rw [show (4 : ℝ) / (12 / 5) = 5 / 3 by norm_num]
  exact scalar_stationary_entropy_twelve_fifths S ν hν hs

variable {ι : Type*}
local instance vectorNormCalibrationDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- The dimension-free p=2, C=1 weighted norm bound. -/
theorem vector_fanNormBound_two {S : Finset (ι → ℝ)} (hS : S.Nonempty) :
    FanNormBound S (positiveDifferenceChannel S) 2 1 := by
  apply FanEntropyBound.to_norm hS (by norm_num) (by norm_num)
  intro ν hν hs
  obtain ⟨Q, hQ⟩ := stationaryAdditiveEntropy_attained S ν hν hs
  have h := Q.entropy_le_two_fans hν hs
  rw [hQ] at h
  norm_num only [Real.log_one, add_zero, show (4 : ℝ) / 2 = 2 by norm_num]
  change stationaryAdditiveEntropy S ν ≤ 2 * stationaryFanCapacity S ν + 2 * finiteEntropy ν
  linarith

/-- The literal weighted energy baseline E(f) <= (sum f^2 Tg/g)^2. -/
theorem weightedEnergy_le_fan_ratio_square {S : Finset (ι → ℝ)} (hS : S.Nonempty)
    (f g : S → ℝ) (hf : ∀ a, 0 < f a) (hg : ∀ a, 0 < g a) :
    weightedGibbsPartition S f ≤
      (∑ a, f a ^ 2 * channelWeightRatio (positiveDifferenceChannel S) g a) ^ 2 := by
  have h := vector_fanNormBound_two hS f g hf hg
  have he : fanPowerSum (positiveDifferenceChannel S) f g 2 =
      ∑ a, f a ^ 2 * channelWeightRatio (positiveDifferenceChannel S) g a := by
    unfold fanPowerSum
    apply Finset.sum_congr rfl
    intro a _
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt (channelWeightRatio_pos _ g hg a).le]
  norm_num only [show (4 : ℝ) / 2 = 2 by norm_num, one_mul, Real.rpow_two] at h
  rw [he] at h
  exact h

end
end Erdos539Geometry
