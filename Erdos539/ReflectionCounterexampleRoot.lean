/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ReflectionCertificate24

namespace Erdos539Geometry

theorem reflectionCounterexample_energy_nat :
    integerIntervalEnergy reflectionCounterexample 387 = 83610 := by
  have he : (integerIntervalEnergy reflectionCounterexample 387 : ℝ) = 83610 := by
    unfold integerIntervalEnergy
    push_cast
    simp_rw [integerReflection_eq]
    exact reflectionCounterexample_energy_cumulative_24
  exact_mod_cast he

theorem reflectionCounterexample_energy : countingEnergy reflectionCounterexample = 83610 := by
  rw [← integerIntervalEnergy_eq_counting _ 387 reflectionCounterexample_bounds,
    reflectionCounterexample_energy_nat]
  norm_num

theorem reflectionCounterexample_root_defect_upper :
    Real.log ((reflectionCounterexample.card : ℝ) ^ 3 / countingEnergy reflectionCounterexample) ≤
      (1412 / 1000 : ℝ) := by
  have h := rational_scaled_log_upper (q := 8575 / 8361) (u := 1412 / 1000)
    (by norm_num) 2 4 (by norm_num [rationalLogSeries, Finset.sum_range_succ])
  norm_num [reflectionCounterexample_card, reflectionCounterexample_energy] at h ⊢
  exact h

end Erdos539Geometry
