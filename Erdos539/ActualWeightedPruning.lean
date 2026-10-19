/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.WeightedPruning
import Erdos539.CoordinateMarginal
import Erdos539.EnergyNormBasics

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*}
local instance actualWeightedPruningDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- The literal square-root marginal of the original squared weight. -/
def actualMarginalWeight (S : Finset (ι → ℝ)) (w : (ι → ℝ) → ℝ) (I : Finset ι) (v : I → ℝ) : ℝ :=
  Real.sqrt (weightSquareSum (fiber S (project I) v) w)

def actualMarginalEnergy (S : Finset (ι → ℝ)) (w : (ι → ℝ) → ℝ) (I : Finset ι) : ℝ :=
  weightedEnergy (projection S I) (actualMarginalWeight S w I)

theorem coordinateMarginalEnergy_eq_actual (S : Finset (ι → ℝ)) (w : (ι → ℝ) → ℝ)
    (I J : Finset ι) (hcover : ∀ i, i ∈ I ∨ i ∈ J) :
    coordinateMarginalEnergy S w I J = actualMarginalEnergy S w I := by
  unfold coordinateMarginalEnergy actualMarginalEnergy
  congr 1
  funext v
  exact coordinateMarginalWeight_eq_sqrt_fiber S w I J hcover v

/-- The manuscript's weighted pruning bound, with literal original-fiber
marginals on both sides. It holds for every positive-energy nonnegative
weight, so in particular for normalized weights and exact optimizers. -/
theorem weighted_pruning_actual_marginals {S : Finset (ι → ℝ)} (w : (ι → ℝ) → ℝ)
    (hw : ∀ x ∈ S, 0 ≤ w x) (hE : 0 < weightedEnergy S w)
    (I J : Finset ι) (hcover : ∀ i, i ∈ I ∨ i ∈ J)
    {cI cJ a b : ℝ} (hcI : 0 ≤ cI) (hcJ : 0 ≤ cJ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hI : ∀ F : Finset (I → ℝ), F.Nonempty → cI * energyNorm F ^ a ≤ (maxFan F : ℝ))
    (hJ : ∀ F : Finset (J → ℝ), F.Nonempty → cJ * energyNorm F ^ b ≤ (maxFan F : ℝ)) :
    cI * cJ * (weightedEnergy S w / (16 * actualMarginalEnergy S w J)) ^ a *
      (weightedEnergy S w / (16 * actualMarginalEnergy S w I)) ^ b ≤ (maxFan S : ℝ) := by
  have h := weighted_pruning w hw hE I J hcover hcI hcJ ha hb hI hJ
  rwa [coordinateMarginalEnergy_eq_actual S w I J hcover,
    coordinateMarginalEnergy_eq_actual S w J I (fun i ↦ (hcover i).symm)] at h

/-- The same statement for an exact maximizing weight; all marginal
energies still use this one weight. -/
theorem weighted_pruning_exact_optimizer {S : Finset (ι → ℝ)} (hS : S.Nonempty) {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S)
    (I J : Finset ι) (hcover : ∀ i, i ∈ I ∨ i ∈ J)
    {cI cJ a b : ℝ} (hcI : 0 ≤ cI) (hcJ : 0 ≤ cJ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hI : ∀ F : Finset (I → ℝ), F.Nonempty → cI * energyNorm F ^ a ≤ (maxFan F : ℝ))
    (hJ : ∀ F : Finset (J → ℝ), F.Nonempty → cJ * energyNorm F ^ b ≤ (maxFan F : ℝ)) :
    cI * cJ * (energyNorm S / (16 * actualMarginalEnergy S (extendWeight S f) J)) ^ a *
      (energyNorm S / (16 * actualMarginalEnergy S (extendWeight S f) I)) ^ b ≤ (maxFan S : ℝ) := by
  have hw : ∀ x ∈ S, 0 ≤ extendWeight S f x := by
    intro x hx
    simpa only [extendWeight, dif_pos hx] using hf.1 ⟨x, hx⟩
  have hpos : 0 < weightedEnergy S (extendWeight S f) := hE.symm ▸ energyNorm_pos hS
  have h := weighted_pruning_actual_marginals (extendWeight S f) hw hpos I J hcover hcI hcJ ha hb hI hJ
  rwa [hE] at h

end
end Erdos539Geometry
