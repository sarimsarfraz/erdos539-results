/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ActualWeightedPruning

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*}
local instance weightedPruningLogDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- Logarithmic form of actual-marginal weighted pruning for the same exact
optimizer, ready for induction over coordinate blocks. -/
theorem weighted_pruning_log {S : Finset (ι → ℝ)} (hS : S.Nonempty) {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S)
    (I J : Finset ι) (hcover : ∀ i, i ∈ I ∨ i ∈ J)
    {a b lossI lossJ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hI : ∀ F : Finset (I → ℝ), F.Nonempty → Real.exp (-lossI) * energyNorm F ^ a ≤ (maxFan F : ℝ))
    (hJ : ∀ F : Finset (J → ℝ), F.Nonempty → Real.exp (-lossJ) * energyNorm F ^ b ≤ (maxFan F : ℝ)) :
    -lossI - lossJ + a * (Real.log (energyNorm S) - Real.log 16 -
        Real.log (actualMarginalEnergy S (extendWeight S f) J)) +
      b * (Real.log (energyNorm S) - Real.log 16 -
        Real.log (actualMarginalEnergy S (extendWeight S f) I)) ≤ Real.log (maxFan S) := by
  have hw : ∀ x ∈ S, 0 ≤ extendWeight S f x := by
    intro x hx
    simpa only [extendWeight, dif_pos hx] using hf.1 ⟨x, hx⟩
  have hpos : 0 < weightedEnergy S (extendWeight S f) := hE.symm ▸ energyNorm_pos hS
  have hLI := coordinateMarginalEnergy_pos (extendWeight S f) hw hpos I J hcover
  have hLJ := coordinateMarginalEnergy_pos (extendWeight S f) hw hpos J I (fun i ↦ (hcover i).symm)
  rw [coordinateMarginalEnergy_eq_actual _ _ I J hcover] at hLI
  rw [coordinateMarginalEnergy_eq_actual _ _ J I (fun i ↦ (hcover i).symm)] at hLJ
  have hlam := energyNorm_pos hS
  have hp := weighted_pruning_exact_optimizer hS hf hE I J hcover
    (Real.exp_nonneg _) (Real.exp_nonneg _) ha hb hI hJ
  have hl := Real.log_le_log (by positivity) hp
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (Real.exp_ne_zero _) (Real.exp_ne_zero _), Real.log_exp, Real.log_exp,
    Real.log_rpow (by positivity), Real.log_rpow (by positivity),
    Real.log_div hlam.ne' (by positivity), Real.log_div hlam.ne' (by positivity),
    Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) hLJ.ne',
    Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) hLI.ne'] at hl
  linarith

end
end Erdos539Geometry
