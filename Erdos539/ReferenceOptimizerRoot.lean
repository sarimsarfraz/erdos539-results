/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ReferenceWeightRoot
import Erdos539.WeightedGibbsScale

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The carried reference derived from a positive weight has exactly its
original normalized additive-quadruple mass. -/
theorem referenceGibbsMass_powerReference {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : ∀ x, 0 < f x) (a b c d : S) :
    (referenceGibbsLaw S (powerReference f) (powerReference_pos hS hf)).mass a b c d =
      weightedGibbsMass S f a b c d := by
  change weightedGibbsMass S (referencePowerWeight (powerReference f)) a b c d = _
  rw [referencePowerWeight_powerReference hS hf]
  exact weightedGibbsMass_scale S f (one_div_ne_zero
    (Real.rpow_pos_of_pos (powerReferenceMass_pos hS hf) _).ne') a b c d

/-- A positive exact optimizer yields precisely the original canonical
optimizer law, not just an entropy bound with the same cardinality. -/
theorem referenceGibbsMass_optimizer {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : ∀ x, 0 < f x) (hE : weightedEnergy S (extendWeight S f) = energyNorm S)
    (a b c d : S) :
    (referenceGibbsLaw S (powerReference f) (powerReference_pos hS hf)).mass a b c d =
      optimizerQuadrupleLaw S f a b c d := by
  rw [referenceGibbsMass_powerReference hS hf, weightedGibbsMass, weightedGibbsPartition, hE]
  rfl

theorem referenceEndpoint_optimizer {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : ∀ x, 0 < f x) (hunit : ∑ x, f x ^ 2 = 1)
    (hE : weightedEnergy S (extendWeight S f) = energyNorm S) :
    referenceEndpoint S (powerReference f) = fun x ↦ f x ^ 2 := by
  funext a
  have hfirst := (referenceGibbsLaw S (powerReference f) (powerReference_pos hS hf)).first a
  simp_rw [referenceGibbsMass_optimizer hS hf hE] at hfirst
  rw [optimizerQuadrupleLaw_first_marginal hS ⟨fun x ↦ (hf x).le, hunit⟩ hE] at hfirst
  exact hfirst.symm

/-- Initial reference cost for a full-support exact optimizer. Zero
weights require restriction to the positive support before applying this theorem. -/
theorem referenceDeficit_optimizer_le {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : ∀ x, 0 < f x) (hunit : ∑ x, f x ^ 2 = 1)
    (hE : weightedEnergy S (extendWeight S f) = energyNorm S) :
    referenceDeficit S (powerReference f) ≤ Real.log ((S.card : ℝ) / energyNorm S) := by
  have h := referenceDeficit_powerReference_le_log hS hf hunit
  simpa only [weightedGibbsPartition, hE] using h

end
end Erdos539Geometry
