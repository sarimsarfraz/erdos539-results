/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsFiberDrift
import Erdos539.StationaryEntropyImageBound
import Erdos539.SeparatedLabelEntropy
import Erdos539.SharpSeparatedExponents

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [DecidableEq H]
local instance partitionBudgetImageDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

def labelReferenceCrossEntropy (S : Finset G) (φ : G → H) (u : S → ℝ) : ℝ :=
  -(∑ y, finitePush (referenceEndpoint S u) (imageEndpoint S φ) y * Real.log (finitePush u (imageEndpoint S φ) y))

def labelReferenceDivergence (S : Finset G) (φ : G → H) (u : S → ℝ) : ℝ :=
  finiteRelEntropy (finitePush (referenceEndpoint S u) (imageEndpoint S φ)) (finitePush u (imageEndpoint S φ))

def labelMeanFiberDeficit (S : Finset G) (φ : G → H) (u : S → ℝ) : ℝ :=
  ∑ y, finitePush (referenceEndpoint S u) (imageEndpoint S φ) y *
    referenceDeficit (fiber S φ y.val) (imageFiberReference S φ u y)

/-- Arbitrary actual partitions satisfy this entropy/conditional-drift
bound. The label term is left explicit and is not assumed nonnegative. -/
theorem referenceDeficit_partition_budget {S : Finset G} (hS : S.Nonempty) (φ : G → H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) :
    labelMeanFiberDeficit S φ u + 3 * labelReferenceCrossEntropy S φ u -
      finiteEntropy ((referenceGibbsLaw S u hu).imageFlat φ) + meanFiberEndpointDrift S φ u ≤ referenceDeficit S u := by
  have h := (referenceGibbsLaw S u hu).entropy_image_partition_bound (referenceEndpoint_sum hS hu) φ
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
        -labelMeanFiberDeficit S φ u := by
    simp only [labelMeanFiberDeficit, referenceDeficit, mul_neg, Finset.sum_neg_distrib, neg_neg]
  rw [hs, imageFiberEndpointTilt_log_expectation hS φ u hu, referenceGibbs_entropy hS u hu,
    meanFiberReferenceLog_eq hS φ u hu] at h
  unfold labelReferenceCrossEntropy referenceDeficit
  linarith

theorem labelReferenceDivergence_eq (S : Finset G) (φ : G → H) (u : S → ℝ) :
    labelReferenceDivergence S φ u = labelReferenceCrossEntropy S φ u -
      finiteEntropy (finitePush (referenceEndpoint S u) (imageEndpoint S φ)) := by
  rw [labelReferenceDivergence, finiteRelEntropy_eq_entropy_cross]
  unfold labelReferenceCrossEntropy
  ring

/-- The sharp component-selection budget: child deficits, reference
surprisal, label relative entropy, and actual conditional endpoint drift
are paid together. Separation is required and remains explicit. -/
theorem referenceDeficit_separated_budget {S : Finset G} (hS : S.Nonempty) (φ : G → H)
    (hsep : SeparatedSumLabels S φ) (u : S → ℝ) (hu : ∀ x, 0 < u x) :
    labelMeanFiberDeficit S φ u + (3 - sharpSidonExponent) * labelReferenceCrossEntropy S φ u +
      sharpSidonExponent * labelReferenceDivergence S φ u + meanFiberEndpointDrift S φ u ≤ referenceDeficit S u := by
  have h := referenceDeficit_partition_budget hS φ u hu
  have he := (referenceGibbsLaw S u hu).separated_image_entropy_le (referenceEndpoint_pos hS hu)
    (referenceEndpoint_sum hS hu) φ hsep
  rw [labelReferenceDivergence_eq]
  linarith

theorem labelReferenceDivergence_nonneg {S : Finset G} (hS : S.Nonempty) (φ : G → H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) (hus : ∑ x, u x = 1) : 0 ≤ labelReferenceDivergence S φ u := by
  exact finiteRelEntropy_nonneg _ _
    (finitePush_nonneg _ _ (fun x ↦ (referenceEndpoint_pos hS hu x).le))
    (finitePush_nonneg _ _ (fun x ↦ (hu x).le))
    (by rw [finitePush_sum, referenceEndpoint_sum hS hu])
    (by rw [finitePush_sum, hus]) (fun y _ ↦ finitePush_imageEndpoint_pos S φ u hu y)

theorem labelReferenceCrossEntropy_nonneg {S : Finset G} (hS : S.Nonempty) (φ : G → H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) (hus : ∑ x, u x = 1) : 0 ≤ labelReferenceCrossEntropy S φ u := by
  have h := labelReferenceDivergence_nonneg hS φ u hu hus
  rw [labelReferenceDivergence_eq] at h
  have he := finiteEntropy_nonneg (finitePush (referenceEndpoint S u) (imageEndpoint S φ))
    (finitePush_nonneg _ _ (fun x ↦ (referenceEndpoint_pos hS hu x).le))
    (by rw [finitePush_sum, referenceEndpoint_sum hS hu])
  linarith

end
end Erdos539Geometry
