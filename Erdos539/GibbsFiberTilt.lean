/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.WeightedGibbsTilt
import Erdos539.ImageFiberAssembly
import Erdos539.GibbsProjectionDrift

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [DecidableEq H]
local instance fiberTiltImageDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

def fiberEndpointDrift (S : Finset G) (φ : G → H) (u : S → ℝ) (y : S.image φ) : ℝ :=
  finiteRelEntropy (imageFiberReference S φ (referenceEndpoint S u) y)
    (referenceEndpoint (fiber S φ y.val) (imageFiberReference S φ u y))

def meanFiberEndpointDrift (S : Finset G) (φ : G → H) (u : S → ℝ) : ℝ :=
  ∑ y, finitePush (referenceEndpoint S u) (imageEndpoint S φ) y * fiberEndpointDrift S φ u y

def meanFiberReferenceLog (S : Finset G) (φ : G → H) (u : S → ℝ) : ℝ :=
  ∑ y, finitePush (referenceEndpoint S u) (imageEndpoint S φ) y *
    ∑ x, imageFiberReference S φ (referenceEndpoint S u) y x * Real.log (imageFiberReference S φ u y x)

def imageFiberEndpointTilt (S : Finset G) (φ : G → H) (u : S → ℝ) (y : S.image φ) :
    fiber S φ y.val → ℝ :=
  weightedGibbsEndpointTilt (fiber S φ y.val) (referencePowerWeight (imageFiberReference S φ u y))
    (imageFiberReference S φ (referenceEndpoint S u) y)

theorem imageFiberEndpointTilt_pos {S : Finset G} (hS : S.Nonempty) (φ : G → H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) (y : S.image φ) (x : fiber S φ y.val) :
    0 < imageFiberEndpointTilt S φ u y x :=
  weightedGibbsEndpointTilt_pos (imageFiber_nonempty S φ y)
    (referencePowerWeight_pos (imageFiberReference_pos S φ u hu y))
    (imageFiberReference_pos S φ (referenceEndpoint S u) (referenceEndpoint_pos hS hu) y) x

theorem imageFiberEndpointTilt_partition_le {S : Finset G} (hS : S.Nonempty) (φ : G → H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) (y : S.image φ) :
    weightedGibbsPartition (fiber S φ y.val) (imageFiberEndpointTilt S φ u y) ≤
      referencePartition (fiber S φ y.val) (imageFiberReference S φ u y) :=
  weightedGibbsEndpointTilt_partition_le (imageFiber_nonempty S φ y)
    (referencePowerWeight_pos (imageFiberReference_pos S φ u hu y))
    (imageFiberReference_pos S φ (referenceEndpoint S u) (referenceEndpoint_pos hS hu) y)
    (imageFiberReference_sum S φ (referenceEndpoint S u) (referenceEndpoint_pos hS hu) y)

theorem imageFiberEndpointTilt_log {S : Finset G} (hS : S.Nonempty) (φ : G → H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) (y : S.image φ) (x : fiber S φ y.val) :
    Real.log (imageFiberEndpointTilt S φ u y x) =
      (3 / 4 : ℝ) * Real.log (imageFiberReference S φ u y x) +
      (1 / 4 : ℝ) * (Real.log (imageFiberReference S φ (referenceEndpoint S u) y x) -
        Real.log (referenceEndpoint (fiber S φ y.val) (imageFiberReference S φ u y) x)) := by
  rw [imageFiberEndpointTilt, weightedGibbsEndpointTilt_log (imageFiber_nonempty S φ y)
    (referencePowerWeight_pos (imageFiberReference_pos S φ u hu y))
    (imageFiberReference_pos S φ (referenceEndpoint S u) (referenceEndpoint_pos hS hu) y)]
  rw [referencePowerWeight, Real.log_rpow (imageFiberReference_pos S φ u hu y x)]
  rfl

theorem meanFiberReferenceLog_eq {S : Finset G} (hS : S.Nonempty) (φ : G → H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) :
    (∑ x, referenceEndpoint S u x * Real.log (u x)) =
      (∑ y, finitePush (referenceEndpoint S u) (imageEndpoint S φ) y *
        Real.log (finitePush u (imageEndpoint S φ) y)) + meanFiberReferenceLog S φ u := by
  have hlog (y : S.image φ) (x : fiber S φ y.val) : Real.log (u (imageFiberEndpoint S φ y x)) =
      Real.log (finitePush u (imageEndpoint S φ) y) + Real.log (imageFiberReference S φ u y x) := by
    rw [← imageFiberReference_reconstruct S φ u hu y x,
      Real.log_mul (finitePush_imageEndpoint_pos S φ u hu y).ne'
        (imageFiberReference_pos S φ u hu y x).ne']
  rw [imageFiber_expectation S φ (referenceEndpoint S u) (referenceEndpoint_pos hS hu)]
  simp_rw [hlog]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
    imageFiberReference_sum S φ (referenceEndpoint S u) (referenceEndpoint_pos hS hu), one_mul]
  rfl

/-- The actual conditional relative entropy is exactly the logarithmic
gain of the assembled fourth-root tilt. -/
theorem imageFiberEndpointTilt_log_expectation {S : Finset G} (hS : S.Nonempty) (φ : G → H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) :
    (∑ x, referenceEndpoint S u x * Real.log (imageAssembleWeight S φ (imageFiberEndpointTilt S φ u) x)) =
      (3 / 4 : ℝ) * meanFiberReferenceLog S φ u + (1 / 4 : ℝ) * meanFiberEndpointDrift S φ u := by
  rw [imageFiber_expectation S φ (referenceEndpoint S u) (referenceEndpoint_pos hS hu)]
  simp_rw [imageAssembleWeight_onFiber, imageFiberEndpointTilt_log hS φ u hu]
  simp only [meanFiberReferenceLog, meanFiberEndpointDrift, fiberEndpointDrift, finiteRelEntropy,
    Finset.mul_sum, mul_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

end
end Erdos539Geometry
