/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryCoordinateEnergy
import Erdos539.CriticalCoreBounds
import Erdos539.CoordinateEnergy
import Erdos539.EnergyDecidableInvariance

namespace Erdos539Geometry
noncomputable section
open scoped Classical
variable {ι : Type*} [Fintype ι]
local instance criticalCoreMarginalEnergyDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

namespace IsProjectionCriticalCore
variable {S T : Finset (ι → ℝ)} {I J : Finset ι} {b : ℝ}

/-- Every actual square-root marginal of a unit weight on the core is
bounded by the root norm, for masks within the retained coordinates. -/
theorem actualMarginalEnergy_le_norm (h : IsProjectionCriticalCore S b I T)
    (hb : 0 < b) (f : T → ℝ) (hf : ∑ x, f x ^ 2 = 1) (hJI : J ⊆ I) :
    actualMarginalEnergy T (extendWeight T f) J ≤ energyNorm T := by
  have hn := h.projected_subset_norm_le hb h.nonempty (Finset.Subset.refl T) hJI
  rw [energyNorm_maskedProjection_eq] at hn
  have hm := (actualMarginalEnergy_unit_bounds T J f hf).2
  simp only [energyNorm_eq_classical] at hm hn ⊢
  exact hm.trans hn

/-- The individual projection-energy losses used by the parallel budget
are nonnegative on the actual selected core. -/
theorem marginal_log_loss_nonneg (h : IsProjectionCriticalCore S b I T)
    (hb : 0 < b) (f : T → ℝ) (hf : ∑ x, f x ^ 2 = 1) (hJI : J ⊆ I) :
    0 ≤ Real.log (energyNorm T) - Real.log (actualMarginalEnergy T (extendWeight T f) J) := by
  have hp := (actualMarginalEnergy_unit_bounds T J f hf).1
  exact sub_nonneg.mpr (Real.log_le_log (by linarith) (h.actualMarginalEnergy_le_norm hb f hf hJI))

end IsProjectionCriticalCore
end
end Erdos539Geometry
