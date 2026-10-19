/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.QuadrupleFanEncoding

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*}
local instance energyFanNormDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- The exact optimizer's norm is controlled by the stationary fan
capacity of its own squared-weight law. -/
theorem optimizer_log_norm_le_two_stationary_fans {S : Finset (ι → ℝ)}
    (hS : S.Nonempty) {f : S → ℝ} (hf : f ∈ admissibleWeights S)
    (hE : weightedEnergy S (extendWeight S f) = energyNorm S) :
    Real.log (energyNorm S) ≤ 2 * stationaryFanCapacity S (fun x ↦ f x ^ 2) := by
  let Q := optimizerStationaryAdditiveLaw hS hf hE
  have h := Q.entropy_le_two_fans (fun x ↦ sq_nonneg (f x)) hf.2
  have he := optimizerQuadrupleEntropy_eq hS hf hE
  change Q.entropy = Real.log (energyNorm S) + 2 * finiteEntropy (fun x ↦ f x ^ 2) at he
  linarith

/-- The baseline dimension-free energy--fan norm inequality, with no
projection-balance or core hypothesis. -/
theorem energyNorm_le_maxFan_sq {S : Finset (ι → ℝ)} (hS : S.Nonempty) :
    energyNorm S ≤ (maxFan S : ℝ) ^ 2 := by
  obtain ⟨f, hfn, hfs, hE⟩ := energyNorm_attained hS
  have hf : f ∈ admissibleWeights S := ⟨hfn, hfs⟩
  have h := optimizer_log_norm_le_two_stationary_fans hS hf hE
  have hc := stationaryFanCapacity_le_log_maxFan S (fun x ↦ f x ^ 2)
    (fun x ↦ sq_nonneg (f x)) hfs
  have hM : (0 : ℝ) < maxFan S := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_maxFan hS))
  apply (Real.log_le_log_iff (energyNorm_pos hS) (pow_pos hM 2)).mp
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith

end
end Erdos539Geometry
