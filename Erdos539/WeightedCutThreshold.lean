/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.WeightedCutCore
import Erdos539.QuadraticCoreThreshold

namespace Erdos539
open Erdos539Geometry
noncomputable section

/-- Conditional sufficient implication only: a universal balance of the
two actual marginal energies yields the stronger exact FC lower bound.
The weighted balance is an explicit unproved hypothesis. -/
theorem cofactorThreshold_strong_bound_of_weighted_cut {B : ℝ}
    (hcut : WeightedProjectionBalanceHypothesis B) (hB : 0 ≤ B) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      Real.sqrt n * Real.exp (c * Real.sqrt (Real.log n)) ≤ (cofactorThreshold n : ℝ) := by
  apply cofactorThreshold_strong_bound_of_quadratic_core (hcut.quadratic_core hB)
  exact mul_nonneg (by norm_num) (add_nonneg hB (Real.log_nonneg (by norm_num)))

end
end Erdos539
