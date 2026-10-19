/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsFiberTilt
import Erdos539.StationaryEntropyFibringBound

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]
local instance fiberDriftImageDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

omit [AddCommGroup H] [DecidableEq H] in
theorem referenceGibbs_entropy {S : Finset G} (hS : S.Nonempty)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) :
    (referenceGibbsLaw S u hu).entropy = Real.log (referencePartition S u) -
      3 * ∑ x, referenceEndpoint S u x * Real.log (u x) := by
  have h := weightedGibbs_entropy (referencePowerWeight_pos hu) (referencePartition_pos hS hu)
  have hs : (∑ x, referenceEndpoint S u x * Real.log (referencePowerWeight u x)) =
      (3 / 4 : ℝ) * ∑ x, referenceEndpoint S u x * Real.log (u x) := by
    simp only [referencePowerWeight, Real.log_rpow (hu _), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  change (referenceGibbsLaw S u hu).entropy = Real.log (referencePartition S u) -
    4 * ∑ x, referenceEndpoint S u x * Real.log (referencePowerWeight u x) at h
  rw [hs] at h
  linarith

theorem fiberEndpointDrift_nonneg {S : Finset G} (hS : S.Nonempty) (φ : G →+ H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) (y : S.image φ) : 0 ≤ fiberEndpointDrift S φ u y := by
  have hη := imageFiberReference_pos S φ (referenceEndpoint S u) (referenceEndpoint_pos hS hu) y
  have hv := referenceEndpoint_pos (imageFiber_nonempty S φ y) (imageFiberReference_pos S φ u hu y)
  exact finiteRelEntropy_nonneg _ _ (fun x ↦ (hη x).le) (fun x ↦ (hv x).le)
    (imageFiberReference_sum S φ (referenceEndpoint S u) (referenceEndpoint_pos hS hu) y)
    (referenceEndpoint_sum (imageFiber_nonempty S φ y) (imageFiberReference_pos S φ u hu y)) (fun x _ ↦ hv x)

theorem meanFiberEndpointDrift_nonneg {S : Finset G} (hS : S.Nonempty) (φ : G →+ H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) : 0 ≤ meanFiberEndpointDrift S φ u := by
  apply Finset.sum_nonneg
  intro y _
  exact mul_nonneg (finitePush_nonneg _ _ (fun x ↦ (referenceEndpoint_pos hS hu x).le) y)
    (fiberEndpointDrift_nonneg hS φ u hu y)

/-- The actual conditional endpoint drift is paid solely by the mean
mixed-energy Holder slack. A fourth-root tilt gives a direct proof;
no arbitrary-endpoint entropy maximizer is assumed. -/
theorem meanFiberEndpointDrift_le {S : Finset G} (hS : S.Nonempty) (φ : G →+ H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) :
    meanFiberEndpointDrift S φ u ≤ meanImageLiftSlack S φ u hu := by
  have h := (referenceGibbsLaw S u hu).entropy_image_fiber_bound (referenceEndpoint_sum hS hu) φ
    (imageAssembleWeight S φ (imageFiberEndpointTilt S φ u))
    (imageAssembleWeight_pos S φ _ (imageFiberEndpointTilt_pos hS φ u hu))
    (fun y ↦ referencePartition (fiber S φ y.val) (imageFiberReference S φ u y))
    (fun y ↦ referencePartition_pos (imageFiber_nonempty S φ y) (imageFiberReference_pos S φ u hu y))
    (by
      intro y
      rw [imageFiberWeight_assemble]
      exact imageFiberEndpointTilt_partition_le hS φ u hu y)
  have hs : (∑ y, finitePush (referenceEndpoint S u) (imageEndpoint S φ) y *
      Real.log (referencePartition (fiber S φ y.val) (imageFiberReference S φ u y))) =
        -meanFiberReferenceDeficit S φ u := by
    simp only [meanFiberReferenceDeficit, referenceDeficit, mul_neg, Finset.sum_neg_distrib, neg_neg]
  change (referenceGibbsLaw S u hu).entropy ≤ (projectedReferenceLaw S φ u hu).entropy + _ - _ at h
  rw [hs, imageFiberEndpointTilt_log_expectation hS φ u hu,
    referenceGibbs_entropy hS u hu, projected_reference_entropy hS φ u hu,
    meanFiberReferenceLog_eq hS φ u hu] at h
  rw [meanImageLiftSlack_eq hS φ u hu]
  linarith

/-- Both directions of endpoint recomputation use the same original cut
budget, with the carried parent law in the first KL argument. -/
theorem endpointDrifts_le_cut_charge {S : Finset G} (hS : S.Nonempty) (φ : G →+ H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) :
    projectionEndpointDrift S φ u + meanFiberEndpointDrift S φ u ≤
      projectionReferenceDrift S φ u hu + meanImageLiftSlack S φ u hu :=
  add_le_add (projectionEndpointDrift_le hS φ u hu) (meanFiberEndpointDrift_le hS φ u hu)

theorem referenceDeficit_children_endpointDrifts_le {S : Finset G} (hS : S.Nonempty) (φ : G →+ H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) :
    referenceDeficit (S.image φ) (finitePush u (imageEndpoint S φ)) +
      meanFiberReferenceDeficit S φ u + projectionEndpointDrift S φ u +
        meanFiberEndpointDrift S φ u ≤ referenceDeficit S u := by
  rw [referenceDeficit_cut_decomposition hS φ u hu]
  linarith [endpointDrifts_le_cut_charge hS φ u hu]

end
end Erdos539Geometry
