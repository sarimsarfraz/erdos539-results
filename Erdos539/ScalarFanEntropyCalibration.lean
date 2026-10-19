/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ScalarPositiveDifferenceCapacity
import Erdos539.StationaryEntropyMaximum

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
local instance scalarFanCalibrationDecidableEq : DecidableEq ℝ := Classical.decEq _

def scalarFanEntropyDefect (S : Finset ℝ) (ν : S → ℝ) : ℝ :=
  2 * scalarStationaryFanCapacity S ν - finiteEntropy ν + stationaryEntropyDefect S ν

theorem scalarFanEntropyDefect_log_bound (S : Finset ℝ) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    finiteEntropy ν - 4 * Real.log (finiteEntropy ν + 2) - 6 ≤ scalarFanEntropyDefect S ν := by
  have h := (scalarStationaryFanCapacity_lower_bounds S ν hν hs).1
  have he := (stationaryEntropyDefect_bounds S ν hν hs).1
  unfold scalarFanEntropyDefect
  linarith

theorem scalarFanEntropyDefect_linear_bound (S : Finset ℝ) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    (1 / 3 : ℝ) * finiteEntropy ν - 2 * (1 + (2 / 3 : ℝ) * Real.log 24) ≤ scalarFanEntropyDefect S ν := by
  have h := (scalarStationaryFanCapacity_lower_bounds S ν hν hs).2
  have he := (stationaryEntropyDefect_bounds S ν hν hs).1
  unfold scalarFanEntropyDefect
  linarith

theorem four_log_shift_bound {H ε : ℝ} (hH : 0 ≤ H) (hε : 0 < ε) :
    4 * Real.log (H + 2) + 6 ≤ ε * H + (4 * Real.log (4 / ε) + 2 + 2 * ε) := by
  have ht : 0 < ε * (H + 2) / 4 := by positivity
  have h := Real.log_le_sub_one_of_pos ht
  have he : Real.log (H + 2) = Real.log (4 / ε) + Real.log (ε * (H + 2) / 4) := by
    rw [← Real.log_mul (by positivity : (4 / ε : ℝ) ≠ 0) ht.ne']
    congr 1
    field_simp
  rw [he]
  nlinarith

/-- The exact scalar entropy calibration for every positive p<4. The
translation into a weighted norm bound is handled by the separate duality chain. -/
theorem scalar_stationary_entropy_power_bound (S : Finset ℝ) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1)
    {p : ℝ} (hp : 0 < p) (hp4 : p < 4) :
    stationaryAdditiveEntropy S ν ≤ 2 * scalarStationaryFanCapacity S ν +
      (4 / p) * finiteEntropy ν + (4 * Real.log (4 / (4 / p - 1)) + 2 + 2 * (4 / p - 1)) := by
  have hε : 0 < 4 / p - 1 := by
    have h := (one_lt_div hp).mpr hp4
    linarith
  have hlog := four_log_shift_bound (finiteEntropy_nonneg ν hν hs) hε
  have hmain := scalarFanEntropyDefect_log_bound S ν hν hs
  unfold scalarFanEntropyDefect stationaryEntropyDefect at hmain
  nlinarith

theorem scalar_stationary_entropy_twelve_fifths (S : Finset ℝ) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    stationaryAdditiveEntropy S ν ≤ 2 * scalarStationaryFanCapacity S ν +
      (5 / 3 : ℝ) * finiteEntropy ν + 2 * (1 + (2 / 3 : ℝ) * Real.log 24) := by
  have h := scalarFanEntropyDefect_linear_bound S ν hν hs
  unfold scalarFanEntropyDefect stationaryEntropyDefect at h
  linarith

end
end Erdos539Geometry
