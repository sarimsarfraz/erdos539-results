/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsFiberDrift

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A literal nonempty support and a carried positive probability law. -/
structure GibbsReference (G : Type*) where
  support : Finset G
  nonempty : support.Nonempty
  weight : support → ℝ
  positive : ∀ x, 0 < weight x
  normalized : ∑ x, weight x = 1

namespace GibbsReference
local instance referenceImageDecidableEq (s : GibbsReference G) (φ : G →+ G) :
    DecidableEq (s.support.image φ) := Classical.decEq _

def deficit (s : GibbsReference G) : ℝ := referenceDeficit s.support s.weight

theorem deficit_nonneg (s : GibbsReference G) : 0 ≤ s.deficit :=
  referenceDeficit_nonneg s.nonempty s.positive s.normalized

/-- Both children carry literal restrictions of the reference, and their
Gibbs laws are recomputed whenever a new cut is made. -/
def image (s : GibbsReference G) (φ : G →+ G) : GibbsReference G where
  support := s.support.image φ
  nonempty := s.nonempty.image φ
  weight := finitePush s.weight (imageEndpoint s.support φ)
  positive := finitePush_imageEndpoint_pos s.support φ s.weight s.positive
  normalized := by rw [finitePush_sum, s.normalized]

def fiber (s : GibbsReference G) (φ : G →+ G) (y : s.support.image φ) : GibbsReference G where
  support := Erdos539Geometry.fiber s.support φ y.val
  nonempty := imageFiber_nonempty s.support φ y
  weight := imageFiberReference s.support φ s.weight y
  positive := imageFiberReference_pos s.support φ s.weight s.positive y
  normalized := imageFiberReference_sum s.support φ s.weight s.positive y

/-- The sampling law is the current recomputed Gibbs endpoint marginal,
which need not equal the pushed reference law. -/
def sample (s : GibbsReference G) (φ : G →+ G) (y : s.support.image φ) : ℝ :=
  finitePush (referenceEndpoint s.support s.weight) (imageEndpoint s.support φ) y

theorem sample_pos (s : GibbsReference G) (φ : G →+ G) (y : s.support.image φ) : 0 < s.sample φ y :=
  finitePush_imageEndpoint_pos s.support φ _ (referenceEndpoint_pos s.nonempty s.positive) y

theorem sample_sum (s : GibbsReference G) (φ : G →+ G) : ∑ y, s.sample φ y = 1 := by
  unfold sample
  rw [finitePush_sum, referenceEndpoint_sum s.nonempty s.positive]

def cutCharge (s : GibbsReference G) (φ : G →+ G) : ℝ :=
  projectionReferenceDrift s.support φ s.weight s.positive + meanImageLiftSlack s.support φ s.weight s.positive

def endpointCharge (s : GibbsReference G) (φ : G →+ G) (y : s.support.image φ) : ℝ :=
  projectionEndpointDrift s.support φ s.weight + fiberEndpointDrift s.support φ s.weight y

theorem cutCharge_nonneg (s : GibbsReference G) (φ : G →+ G) : 0 ≤ s.cutCharge φ :=
  add_nonneg (projectionReferenceDrift_nonneg s.nonempty φ s.weight s.positive)
    (meanImageLiftSlack_nonneg s.nonempty φ s.weight s.positive)

theorem endpointCharge_nonneg (s : GibbsReference G) (φ : G →+ G) (y : s.support.image φ) :
    0 ≤ s.endpointCharge φ y :=
  add_nonneg (projectionEndpointDrift_nonneg s.nonempty φ s.weight s.positive)
    (fiberEndpointDrift_nonneg s.nonempty φ s.weight s.positive y)

theorem deficit_cut (s : GibbsReference G) (φ : G →+ G) :
    s.deficit = (s.image φ).deficit +
      ∑ y, s.sample φ y * (s.cutCharge φ + (s.fiber φ y).deficit) := by
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sample_sum, one_mul]
  have h := referenceDeficit_cut_decomposition s.nonempty φ s.weight s.positive
  change s.deficit = (s.image φ).deficit + (∑ y, s.sample φ y * (s.fiber φ y).deficit) +
    projectionReferenceDrift s.support φ s.weight s.positive + meanImageLiftSlack s.support φ s.weight s.positive at h
  unfold cutCharge
  linarith

theorem endpointCharge_children_le (s : GibbsReference G) (φ : G →+ G) :
    (s.image φ).deficit + ∑ y, s.sample φ y * (s.endpointCharge φ y + (s.fiber φ y).deficit) ≤ s.deficit := by
  have h := referenceDeficit_children_endpointDrifts_le s.nonempty φ s.weight s.positive
  simp only [endpointCharge, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sample_sum, one_mul]
  change (s.image φ).deficit +
    (projectionEndpointDrift s.support φ s.weight + meanFiberEndpointDrift s.support φ s.weight +
      meanFiberReferenceDeficit s.support φ s.weight) ≤ s.deficit
  change (s.image φ).deficit + meanFiberReferenceDeficit s.support φ s.weight +
    projectionEndpointDrift s.support φ s.weight + meanFiberEndpointDrift s.support φ s.weight ≤ s.deficit at h
  linarith

end GibbsReference
end
end Erdos539Geometry
