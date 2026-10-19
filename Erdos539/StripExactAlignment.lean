/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StripZeroCosts
import Erdos539.GibbsZeroAlignment

namespace Erdos539Geometry
noncomputable section
open scoped Classical Pointwise

theorem gibbsStrip_each_fiber_drift_zero {T : ℕ} (hT : 0 < T) {H : ℤ} (hH : 2 * (T : ℤ) < H)
    (y : (gibbsStrip T H).image stripProjection) :
    fiberEndpointDrift (gibbsStrip T H) stripProjection (uniformReference (gibbsStrip T H)) y = 0 :=
  fiberEndpointDrift_zero_of_mean_zero (gibbsStrip_nonempty hT H) stripProjection _
    (uniformReference_pos (gibbsStrip_nonempty hT H)) (gibbsStrip_endpoint_costs_zero hT hH).2 y

theorem gibbsStrip_each_alignment_zero {T : ℕ} (hT : 0 < T) {H : ℤ} (hH : 2 * (T : ℤ) < H)
    (a b : (gibbsStrip T H).image stripProjection) :
    autocorrelationDistanceSq (gibbsStrip T H)
      (imageAutocorrelationWeight (gibbsStrip T H) stripProjection (uniformReference (gibbsStrip T H)) a)
      (imageAutocorrelationWeight (gibbsStrip T H) stripProjection (uniformReference (gibbsStrip T H)) b) = 0 :=
  imageAutocorrelationDistance_zero_of_mean_zero (gibbsStrip_nonempty hT H) stripProjection _
    (uniformReference_pos (gibbsStrip_nonempty hT H)) (gibbsStrip_alignment_cost_zero hT hH) a b

/-- Every actual normalized fiber autocorrelation agrees on the root
signed-difference support. -/
theorem gibbsStrip_normalized_correlations_eq {T : ℕ} (hT : 0 < T) {H : ℤ} (hH : 2 * (T : ℤ) < H)
    (a b : (gibbsStrip T H).image stripProjection) {z : (Unit ⊕ Unit) → ℤ}
    (hz : z ∈ gibbsStrip T H - gibbsStrip T H) :
    normalizedAutocorrelation (gibbsStrip T H)
      (imageAutocorrelationWeight (gibbsStrip T H) stripProjection (uniformReference (gibbsStrip T H)) a) z =
    normalizedAutocorrelation (gibbsStrip T H)
      (imageAutocorrelationWeight (gibbsStrip T H) stripProjection (uniformReference (gibbsStrip T H)) b) z :=
  normalizedAutocorrelation_eq_of_distance_zero _ _ _ (gibbsStrip_each_alignment_zero hT hH a b) hz

end
end Erdos539Geometry
