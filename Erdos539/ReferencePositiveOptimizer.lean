/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ReferenceOptimizerRoot
import Erdos539.PositiveOptimizerSupport

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def positiveOptimizerWeight (S : Finset G) (f : S → ℝ) : positiveWeightSupport S f → ℝ :=
  restrictSupportWeight (positiveWeightSupport_subset S f) f

def positiveOptimizerReference (S : Finset G) (f : S → ℝ) : positiveWeightSupport S f → ℝ :=
  powerReference (positiveOptimizerWeight S f)

omit [AddCommGroup G] in
theorem positiveOptimizerReference_pos {S : Finset G} {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (x : positiveWeightSupport S f) :
    0 < positiveOptimizerReference S f x :=
  powerReference_pos (positiveWeightSupport_nonempty hf) (positiveWeightSupport_restriction_pos S f) x

omit [AddCommGroup G] in
theorem positiveOptimizerReference_sum {S : Finset G} {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) : ∑ x, positiveOptimizerReference S f x = 1 :=
  powerReference_sum (positiveWeightSupport_nonempty hf) (positiveWeightSupport_restriction_pos S f)

/-- Restricting a possibly vanishing optimizer to its literal positive
support gives the stated support-cardinality reference budget. -/
theorem referenceDeficit_positive_optimizer_le_support {S : Finset G} {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S) :
    referenceDeficit (positiveWeightSupport S f) (positiveOptimizerReference S f) ≤
      Real.log ((positiveWeightSupport S f).card / energyNorm S) := by
  have h := referenceDeficit_powerReference_le_log (positiveWeightSupport_nonempty hf)
    (positiveWeightSupport_restriction_pos S f) (positiveWeightSupport_unit hf)
  simpa only [weightedGibbsPartition, positiveWeightSupport_energy hf.1, hE] using h

/-- The original N/Lambda root budget includes all zero-weight points,
without assuming full support of the original optimizer. -/
theorem referenceDeficit_positive_optimizer_le {S : Finset G} (hS : S.Nonempty) {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S) :
    referenceDeficit (positiveWeightSupport S f) (positiveOptimizerReference S f) ≤
      Real.log ((S.card : ℝ) / energyNorm S) := by
  have hA := positiveWeightSupport_nonempty hf
  have hN : (0 : ℝ) < (positiveWeightSupport S f).card := by exact_mod_cast hA.card_pos
  have hcard : ((positiveWeightSupport S f).card : ℝ) ≤ S.card := by
    exact_mod_cast Finset.card_le_card (positiveWeightSupport_subset S f)
  exact (referenceDeficit_positive_optimizer_le_support hf hE).trans
    (Real.log_le_log (div_pos hN (energyNorm_pos hS))
      (div_le_div_of_nonneg_right hcard (energyNorm_nonneg S)))

/-- On every actual quadruple of positive-support points, the new
reference law is exactly the original optimizer's canonical law. -/
theorem referenceGibbsMass_positive_optimizer {S : Finset G} {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (hE : weightedEnergy S (extendWeight S f) = energyNorm S)
    (a b c d : positiveWeightSupport S f) :
    (referenceGibbsLaw (positiveWeightSupport S f) (positiveOptimizerReference S f)
      (positiveOptimizerReference_pos hf)).mass a b c d = optimizerQuadrupleLaw S f
        ⟨a, positiveWeightSupport_subset S f a.property⟩
        ⟨b, positiveWeightSupport_subset S f b.property⟩
        ⟨c, positiveWeightSupport_subset S f c.property⟩
        ⟨d, positiveWeightSupport_subset S f d.property⟩ := by
  change (referenceGibbsLaw (positiveWeightSupport S f) (powerReference (positiveOptimizerWeight S f))
    (powerReference_pos (positiveWeightSupport_nonempty hf) (positiveWeightSupport_restriction_pos S f))).mass a b c d = _
  unfold positiveOptimizerWeight
  rw [referenceGibbsMass_powerReference (positiveWeightSupport_nonempty hf)
    (positiveWeightSupport_restriction_pos S f)]
  unfold weightedGibbsMass weightedGibbsPartition
  rw [positiveWeightSupport_energy hf.1, hE]
  rfl

/-- Every original quadruple outside that support has zero mass. Together
with the preceding pointwise identity this describes the entire law. -/
theorem optimizerQuadrupleLaw_zero_outside_positive_support {S : Finset G} {f : S → ℝ}
    (hf : f ∈ admissibleWeights S) (a b c d : S)
    (hnot : a.val ∉ positiveWeightSupport S f ∨ b.val ∉ positiveWeightSupport S f ∨
      c.val ∉ positiveWeightSupport S f ∨ d.val ∉ positiveWeightSupport S f) :
    optimizerQuadrupleLaw S f a b c d = 0 := by
  have hz (x : S) (hx : x.val ∉ positiveWeightSupport S f) : f x = 0 := by
    simpa only [extendWeight_mem] using positiveWeightSupport_zero hf.1 x.property hx
  rcases hnot with ha | hb | hc | hd
  · simp [optimizerQuadrupleLaw, additiveQuadrupleWeight, hz a ha]
  · simp [optimizerQuadrupleLaw, additiveQuadrupleWeight, hz b hb]
  · simp [optimizerQuadrupleLaw, additiveQuadrupleWeight, hz c hc]
  · simp [optimizerQuadrupleLaw, additiveQuadrupleWeight, hz d hd]

end
end Erdos539Geometry
