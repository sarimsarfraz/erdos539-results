/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ScalarReflectionPowers

namespace Erdos539Geometry
noncomputable section

/-- Each positive number of base-1000 digits gives a scalar example with
stationary reflected-parent excess greater than 0.13 times that number. -/
theorem scalarReflectionPower_stationary_excess (n : ℕ) (hn : 0 < n) :
    (13 / 100 : ℝ) * n < reflectedMeanStationaryDefect (scalarReflectionPower n) -
      stationaryEntropyDefect (scalarReflectionPower n)
        (referenceEndpoint (scalarReflectionPower n) (uniformReference (scalarReflectionPower n))) := by
  apply reflected_stationary_excess_of_counting (scalarReflectionPower_nonempty n)
  change (13 / 100 : ℝ) * n < reflectedMeanCountingDefect (scalarReflectionPower n) -
    countingDefect (scalarReflectionPower n)
  rw [scalarReflectionPower_reflectedMean, scalarReflectionPower_countingDefect]
  have h := mul_lt_mul_of_pos_left reflectionCounterexample_counting_excess
    (show (0 : ℝ) < n by exact_mod_cast hn)
  change (n : ℝ) * (13 / 100) < n *
    (reflectedMeanCountingDefect reflectionCounterexample - countingDefect reflectionCounterexample) at h
  nlinarith

/-- The reflected-parent change can have unbounded cost even in one
scalar coordinate, for the explicit radix-encoded family. -/
theorem scalar_reflected_stationary_excess_unbounded (R : ℝ) :
    ∃ n : ℕ, 0 < n ∧
      R < reflectedMeanStationaryDefect (scalarReflectionPower n) -
        stationaryEntropyDefect (scalarReflectionPower n)
          (referenceEndpoint (scalarReflectionPower n) (uniformReference (scalarReflectionPower n))) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (R * 100 / 13) 0)
  have hn0 : (0 : ℝ) < n := lt_of_le_of_lt (le_max_right _ _) hn
  have hn' : 0 < n := by exact_mod_cast hn0
  have hR : R < (13 / 100 : ℝ) * n := by
    have h := lt_of_le_of_lt (le_max_left _ _) hn
    linarith
  exact ⟨n, hn', hR.trans (scalarReflectionPower_stationary_excess n hn')⟩

/-- No universal constant pays the reflected-parent change for all scalar
sets. This does not rule out choosing a suitable individual reflection. -/
theorem no_uniform_scalar_reflected_parent_budget :
    ¬ ∃ C : ℝ, ∀ S : Finset ℤ, S.Nonempty →
      reflectedMeanStationaryDefect S ≤
        stationaryEntropyDefect S (referenceEndpoint S (uniformReference S)) + C := by
  rintro ⟨C, hC⟩
  obtain ⟨n, _, hn⟩ := scalar_reflected_stationary_excess_unbounded C
  have h := hC (scalarReflectionPower n) (scalarReflectionPower_nonempty n)
  linarith

end
end Erdos539Geometry
