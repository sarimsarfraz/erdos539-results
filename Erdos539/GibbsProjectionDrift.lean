/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsCutDecomposition

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]
local instance gibbsDriftImageDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

/-- The direction is the actual parent marginal relative to the endpoint
law recomputed from the projected reference. -/
def projectionEndpointDrift (S : Finset G) (φ : G →+ H) (u : S → ℝ) : ℝ :=
  finiteRelEntropy (finitePush (referenceEndpoint S u) (imageEndpoint S φ))
    (referenceEndpoint (S.image φ) (finitePush u (imageEndpoint S φ)))

theorem projectionEndpointDrift_nonneg {S : Finset G} (hS : S.Nonempty) (φ : G →+ H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) : 0 ≤ projectionEndpointDrift S φ u := by
  apply finiteRelEntropy_nonneg
  · exact finitePush_nonneg _ _ (fun x ↦ (referenceEndpoint_pos hS hu x).le)
  · exact fun x ↦ (referenceEndpoint_pos (hS.image φ) (finitePush_imageEndpoint_pos S φ u hu) x).le
  · rw [finitePush_sum, referenceEndpoint_sum hS hu]
  · exact referenceEndpoint_sum (hS.image φ) (finitePush_imageEndpoint_pos S φ u hu)
  · exact fun x _ ↦ referenceEndpoint_pos (hS.image φ) (finitePush_imageEndpoint_pos S φ u hu) x

theorem projectionEndpointDrift_le {S : Finset G} (hS : S.Nonempty) (φ : G →+ H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) :
    projectionEndpointDrift S φ u ≤ projectionReferenceDrift S φ u hu := by
  let Q := projectedReferenceLaw S φ u hu
  let R := referenceGibbsLaw (S.image φ) (finitePush u (imageEndpoint S φ))
    (finitePush_imageEndpoint_pos S φ u hu)
  have h := finiteRelEntropy_push_le Q.flat R.flat (fun z ↦ z.1.1)
    (fun z ↦ Q.nonneg _ _ _ _) (fun z ↦ R.nonneg _ _ _ _)
    (fun z hz ↦ Q.weightedGibbsMass_pos_of_support
      (referencePowerWeight_pos (finitePush_imageEndpoint_pos S φ u hu))
      (referencePartition_pos (hS.image φ) (finitePush_imageEndpoint_pos S φ u hu)) hz)
  rw [Q.flat_first, R.flat_first] at h
  exact h

/-- The two literal children and the projection's endpoint drift share
the original reference budget. The additional fiber drift is treated
separately and is not assumed here. -/
theorem referenceDeficit_children_projectionDrift_le {S : Finset G} (hS : S.Nonempty)
    (φ : G →+ H) (u : S → ℝ) (hu : ∀ x, 0 < u x) :
    referenceDeficit (S.image φ) (finitePush u (imageEndpoint S φ)) +
      meanFiberReferenceDeficit S φ u + projectionEndpointDrift S φ u +
        meanImageLiftSlack S φ u hu ≤ referenceDeficit S u := by
  rw [referenceDeficit_cut_decomposition hS φ u hu]
  linarith [projectionEndpointDrift_le hS φ u hu]

end
end Erdos539Geometry
