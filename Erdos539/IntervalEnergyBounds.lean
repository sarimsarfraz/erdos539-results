/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.IntervalCountingEnergy
import Erdos539.StationaryOptimizedProfile

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

theorem uniformEnergyWeight_scalarInterval {n : ℕ} (hn : 0 < n) :
    weightedEnergy (scalarInterval n) (extendWeight _ (uniformEnergyWeight (scalarInterval n))) =
      (2 * (n : ℝ) ^ 2 + 1) / (3 * n) := by
  rw [uniformEnergyWeight_energy, countingEnergy_scalarInterval, scalarInterval_card]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

theorem energyNorm_scalarInterval_bounds {n : ℕ} (hn : 0 < n) :
    2 * (n : ℝ) / 3 < energyNorm (scalarInterval n) ∧ energyNorm (scalarInterval n) ≤ n := by
  have hl := energyNorm_ge_admissible (uniformEnergyWeight_admissible (scalarInterval_nonempty hn))
  rw [uniformEnergyWeight_scalarInterval hn] at hl
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · apply lt_of_lt_of_le _ hl
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 3 * n)).mpr
    nlinarith
  · simpa only [scalarInterval_card] using energyNorm_le_card (scalarInterval n)

theorem optimizer_entropy_ge_log_norm {G : Type*} [AddCommGroup G] [DecidableEq G]
    {S : Finset G} (hS : S.Nonempty) {f : S → ℝ} (hf : f ∈ admissibleWeights S)
    (hE : weightedEnergy S (extendWeight S f) = energyNorm S) :
    Real.log (energyNorm S) ≤ finiteEntropy (fun x ↦ f x ^ 2) := by
  rw [← stationaryEnergyProfile_optimizer hS hf hE]
  exact (stationaryEnergyProfile_bounds (fun x ↦ sq_nonneg _) hf.2).2

end
end Erdos539Geometry
