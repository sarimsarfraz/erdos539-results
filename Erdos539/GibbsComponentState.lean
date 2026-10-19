/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsReferenceState
import Erdos539.GibbsPartitionBudget

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [DecidableEq H]
local instance componentStateImageDecidableEq (s : GibbsReference G) (label : G → H) :
    DecidableEq (s.support.image label) := Classical.decEq _

namespace GibbsReference

/-- Actual component restriction, with no embedding of labels as physical
coordinates. The component Gibbs law is recomputed from this reference. -/
def component (s : GibbsReference G) (label : G → H) (i : s.support.image label) : GibbsReference G where
  support := Erdos539Geometry.fiber s.support label i.val
  nonempty := imageFiber_nonempty s.support label i
  weight := imageFiberReference s.support label s.weight i
  positive := imageFiberReference_pos s.support label s.weight s.positive i
  normalized := imageFiberReference_sum s.support label s.weight s.positive i

def componentSample (s : GibbsReference G) (label : G → H) (i : s.support.image label) : ℝ :=
  finitePush (referenceEndpoint s.support s.weight) (imageEndpoint s.support label) i

theorem componentSample_pos (s : GibbsReference G) (label : G → H) (i : s.support.image label) :
    0 < s.componentSample label i :=
  finitePush_imageEndpoint_pos s.support label _ (referenceEndpoint_pos s.nonempty s.positive) i

theorem componentSample_sum (s : GibbsReference G) (label : G → H) : ∑ i, s.componentSample label i = 1 := by
  unfold componentSample
  rw [finitePush_sum, referenceEndpoint_sum s.nonempty s.positive]

def componentCharge (s : GibbsReference G) (label : G → H) (i : s.support.image label) : ℝ :=
  (3 - sharpSidonExponent) * (-Real.log (finitePush s.weight (imageEndpoint s.support label) i)) +
    sharpSidonExponent * labelReferenceDivergence s.support label s.weight +
    fiberEndpointDrift s.support label s.weight i

theorem componentCharge_nonneg (s : GibbsReference G) (label : G → H) (i : s.support.image label) :
    0 ≤ s.componentCharge label i := by
  have hv := finitePush_imageEndpoint_pos s.support label s.weight s.positive
  have hvs : (∑ j, finitePush s.weight (imageEndpoint s.support label) j) = 1 := by
    rw [finitePush_sum, s.normalized]
  have hvi : finitePush s.weight (imageEndpoint s.support label) i ≤ 1 := by
    rw [← hvs]
    exact Finset.single_le_sum (fun j _ ↦ (hv j).le) (Finset.mem_univ i)
  have hlog := neg_nonneg.mpr (Real.log_nonpos (hv i).le hvi)
  have hγ : 0 ≤ sharpSidonExponent := le_trans (by norm_num) sharpSidonExponent_bounds.1
  have hc : 0 ≤ 3 - sharpSidonExponent := sub_nonneg.mpr sharpSidonExponent_bounds.2
  have hη := imageFiberReference_pos s.support label (referenceEndpoint s.support s.weight)
    (referenceEndpoint_pos s.nonempty s.positive) i
  have hν := referenceEndpoint_pos (imageFiber_nonempty s.support label i)
    (imageFiberReference_pos s.support label s.weight s.positive i)
  have hd : 0 ≤ fiberEndpointDrift s.support label s.weight i :=
    finiteRelEntropy_nonneg _ _ (fun x ↦ (hη x).le) (fun x ↦ (hν x).le)
      (imageFiberReference_sum s.support label (referenceEndpoint s.support s.weight)
        (referenceEndpoint_pos s.nonempty s.positive) i)
      (referenceEndpoint_sum (imageFiber_nonempty s.support label i)
        (imageFiberReference_pos s.support label s.weight s.positive i)) (fun x _ ↦ hν x)
  exact add_nonneg (add_nonneg (mul_nonneg hc hlog)
    (mul_nonneg hγ (labelReferenceDivergence_nonneg s.nonempty label s.weight s.positive s.normalized))) hd

theorem mean_componentCharge (s : GibbsReference G) (label : G → H) :
    (∑ i, s.componentSample label i * s.componentCharge label i) =
      (3 - sharpSidonExponent) * labelReferenceCrossEntropy s.support label s.weight +
      sharpSidonExponent * labelReferenceDivergence s.support label s.weight +
      meanFiberEndpointDrift s.support label s.weight := by
  have hsum : (∑ i, s.componentSample label i * s.componentCharge label i) =
      (3 - sharpSidonExponent) * labelReferenceCrossEntropy s.support label s.weight +
      (∑ i, s.componentSample label i) *
        (sharpSidonExponent * labelReferenceDivergence s.support label s.weight) +
      meanFiberEndpointDrift s.support label s.weight := by
    simp only [componentCharge, labelReferenceCrossEntropy, meanFiberEndpointDrift,
      componentSample, mul_neg, Finset.mul_sum, Finset.sum_mul]
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [componentSample_sum, one_mul] at hsum
  exact hsum

/-- The actual one-child component-selection step satisfies the same
reference potential inequality as coordinate recomputation. -/
theorem component_local_budget (s : GibbsReference G) (label : G → H)
    (hsep : SeparatedSumLabels s.support label) :
    (∑ i, s.componentSample label i * (s.componentCharge label i + (s.component label i).deficit)) ≤ s.deficit := by
  simp only [mul_add, Finset.sum_add_distrib]
  rw [mean_componentCharge]
  have h := referenceDeficit_separated_budget s.nonempty label hsep s.weight s.positive
  change (3 - sharpSidonExponent) * labelReferenceCrossEntropy s.support label s.weight +
    sharpSidonExponent * labelReferenceDivergence s.support label s.weight +
    meanFiberEndpointDrift s.support label s.weight + labelMeanFiberDeficit s.support label s.weight ≤ s.deficit
  change _ ≤ s.deficit at h
  linarith

end GibbsReference
end
end Erdos539Geometry
