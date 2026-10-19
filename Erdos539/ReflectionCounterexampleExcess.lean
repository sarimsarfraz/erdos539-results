/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ReflectionCounterexampleRoot

namespace Erdos539Geometry

theorem reflectionCounterexample_mean_counting_lower :
    (1544 / 1000 : ℝ) ≤ reflectedMeanCountingDefect reflectionCounterexample := by
  rw [reflectedMeanCountingDefect_eq_interval _ 387 reflectionCounterexample_bounds,
    reflectionCounterexample_energy]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 83610)).mpr
  have h := reflectionCounterexample_cumulative_24
  linarith

/-- The strict reflected-parent counting-defect excess is certified with
rational logarithm intervals and exact finite counts. -/
theorem reflectionCounterexample_counting_excess :
    (13 / 100 : ℝ) < reflectedMeanCountingDefect reflectionCounterexample -
      Real.log ((reflectionCounterexample.card : ℝ) ^ 3 / countingEnergy reflectionCounterexample) := by
  have hL := reflectionCounterexample_mean_counting_lower
  have hU := reflectionCounterexample_root_defect_upper
  linarith

/-- An explicit scalar obstruction to a loss-free reflected-parent budget.
The parents and their canonical common endpoint mixture are literal laws. -/
theorem reflectionCounterexample_stationary_excess :
    (13 / 100 : ℝ) < reflectedMeanStationaryDefect reflectionCounterexample -
      stationaryEntropyDefect reflectionCounterexample
        (referenceEndpoint reflectionCounterexample (uniformReference reflectionCounterexample)) := by
  apply reflected_stationary_excess_of_counting
    (show reflectionCounterexample.Nonempty from ⟨0, by decide +kernel⟩)
  exact reflectionCounterexample_counting_excess

end Erdos539Geometry
