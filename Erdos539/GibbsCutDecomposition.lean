/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsLogProducts

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]
local instance gibbsCutImageDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

def meanImageLogPartition (S : Finset G) (φ : G →+ H) (u : S → ℝ) (hu : ∀ x, 0 < u x) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ d, (projectedReferenceLaw S φ u hu).mass a b c d *
    Real.log (imageMixedPartition S φ u a b c d)

def meanFiberReferenceDeficit (S : Finset G) (φ : G →+ H) (u : S → ℝ) : ℝ :=
  ∑ y, finitePush (referenceEndpoint S u) (imageEndpoint S φ) y *
    referenceDeficit (fiber S φ y.val) (imageFiberReference S φ u y)

/-- The parent projection compared to the Gibbs law recomputed from the
actual projected reference. -/
def projectionReferenceDrift (S : Finset G) (φ : G →+ H) (u : S → ℝ) (hu : ∀ x, 0 < u x) : ℝ :=
  finiteRelEntropy (projectedReferenceLaw S φ u hu).flat
    (referenceGibbsLaw (S.image φ) (finitePush u (imageEndpoint S φ))
      (finitePush_imageEndpoint_pos S φ u hu)).flat

theorem projected_reference_entropy {S : Finset G} (hS : S.Nonempty) (φ : G →+ H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) :
    (projectedReferenceLaw S φ u hu).entropy = Real.log (referencePartition S u) -
      3 * (∑ y, finitePush (referenceEndpoint S u) (imageEndpoint S φ) y *
        Real.log (finitePush u (imageEndpoint S φ) y)) - meanImageLogPartition S φ u hu := by
  have hpoint (a b c d : S.image φ) :
      Real.negMulLog ((projectedReferenceLaw S φ u hu).mass a b c d) =
        -((projectedReferenceLaw S φ u hu).mass a b c d * Real.log (imageReferenceProduct S φ u a b c d)) -
          (projectedReferenceLaw S φ u hu).mass a b c d * Real.log (imageMixedPartition S φ u a b c d) +
          (projectedReferenceLaw S φ u hu).mass a b c d * Real.log (referencePartition S u) := by
    by_cases hp : (projectedReferenceLaw S φ u hu).mass a b c d = 0
    · simp [hp]
    have hB := imageReferenceProduct_pos S φ u hu a b c d
    have hK := imageMixedPartition_pos_of_projected_mass hS φ u hu hp
    have hZ := referencePartition_pos hS hu
    have hlog : Real.log ((projectedReferenceLaw S φ u hu).mass a b c d) =
        Real.log (imageReferenceProduct S φ u a b c d) + Real.log (imageMixedPartition S φ u a b c d) -
          Real.log (referencePartition S u) := by
      rw [projectedReferenceLaw_mass_density, Real.log_div (mul_pos hB hK).ne' hZ.ne',
        Real.log_mul hB.ne' hK.ne']
    rw [Real.negMulLog, hlog]
    ring
  unfold StationaryAdditiveLaw.entropy
  simp_rw [hpoint]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul]
  rw [projected_log_reference_average, (projectedReferenceLaw S φ u hu).total_mass
    (projectedReferenceLaw_endpoint_sum hS φ u hu), one_mul]
  unfold meanImageLogPartition
  ring

theorem projectionReferenceDrift_nonneg {S : Finset G} (hS : S.Nonempty) (φ : G →+ H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) : 0 ≤ projectionReferenceDrift S φ u hu :=
  (projectedReferenceLaw S φ u hu).relativeEntropy_weightedGibbs_nonneg
    (projectedReferenceLaw_endpoint_sum hS φ u hu)
    (referencePowerWeight_pos (finitePush_imageEndpoint_pos S φ u hu))
    (referencePartition_pos (hS.image φ) (finitePush_imageEndpoint_pos S φ u hu))

/-- Exact projection KL cost in terms of the actual lift partition. -/
theorem projectionReferenceDrift_eq {S : Finset G} (hS : S.Nonempty) (φ : G →+ H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) :
    projectionReferenceDrift S φ u hu = meanImageLogPartition S φ u hu +
      Real.log (referencePartition (S.image φ) (finitePush u (imageEndpoint S φ))) -
        Real.log (referencePartition S u) := by
  have h := (projectedReferenceLaw S φ u hu).referenceGibbs_variational_identity
    (projectedReferenceLaw_endpoint_sum hS φ u hu) (hS.image φ)
    (finitePush_imageEndpoint_pos S φ u hu)
  change projectionReferenceDrift S φ u hu = _ at h
  rw [finiteRelEntropy_eq_entropy_cross (finitePush (referenceEndpoint S u) (imageEndpoint S φ))
    (finitePush u (imageEndpoint S φ))] at h
  unfold StationaryAdditiveLaw.correlation referenceDeficit at h
  rw [projected_reference_entropy hS φ u hu] at h
  linarith

theorem meanImageLiftSlack_eq {S : Finset G} (hS : S.Nonempty) (φ : G →+ H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) :
    meanImageLiftSlack S φ u hu = -meanFiberReferenceDeficit S φ u - meanImageLogPartition S φ u hu := by
  unfold meanImageLiftSlack
  simp_rw [weighted_imageLiftSlack_log hS φ u hu]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [projected_log_geometric_average]
  simp only [meanFiberReferenceDeficit, referenceDeficit, mul_neg, Finset.sum_neg_distrib, neg_neg]
  rfl

/-- Exact decomposition at every additive image/fiber cut, with both
children recomputed from their actual references and actual parent weights.
Coordinate projections are special cases of the additive map. -/
theorem referenceDeficit_cut_decomposition {S : Finset G} (hS : S.Nonempty) (φ : G →+ H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) :
    referenceDeficit S u = referenceDeficit (S.image φ) (finitePush u (imageEndpoint S φ)) +
      meanFiberReferenceDeficit S φ u + projectionReferenceDrift S φ u hu + meanImageLiftSlack S φ u hu := by
  rw [projectionReferenceDrift_eq hS φ u hu, meanImageLiftSlack_eq hS φ u hu]
  unfold referenceDeficit
  ring

theorem meanFiberReferenceDeficit_nonneg {S : Finset G} (hS : S.Nonempty) (φ : G →+ H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) : 0 ≤ meanFiberReferenceDeficit S φ u := by
  apply Finset.sum_nonneg
  intro y _
  exact mul_nonneg (finitePush_nonneg (referenceEndpoint S u) (imageEndpoint S φ)
    (fun x ↦ (referenceEndpoint_pos hS hu x).le) y) (imageFiberReference_deficit_nonneg S φ u hu y)

/-- Both child deficits are paid from the one original reference deficit. -/
theorem referenceDeficit_children_le {S : Finset G} (hS : S.Nonempty) (φ : G →+ H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) :
    referenceDeficit (S.image φ) (finitePush u (imageEndpoint S φ)) + meanFiberReferenceDeficit S φ u ≤
      referenceDeficit S u := by
  rw [referenceDeficit_cut_decomposition hS φ u hu]
  linarith [projectionReferenceDrift_nonneg hS φ u hu, meanImageLiftSlack_nonneg hS φ u hu]

end
end Erdos539Geometry
