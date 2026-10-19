/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ImageFiberAssembly
import Erdos539.FiniteRelativeEntropyChain

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {G H : Type*} [DecidableEq H]
local instance conditionalEntropyImageDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

theorem imageFiberReference_nonneg (S : Finset G) (φ : G → H) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (y : S.image φ) (x : fiber S φ y.val) :
    0 ≤ imageFiberReference S φ ν y x :=
  div_nonneg (hν _) (finitePush_nonneg ν (imageEndpoint S φ) hν y)

theorem imageFiberReference_sum_of_mass_ne_zero (S : Finset G) (φ : G → H) (ν : S → ℝ)
    (y : S.image φ) (hy : finitePush ν (imageEndpoint S φ) y ≠ 0) :
    ∑ x, imageFiberReference S φ ν y x = 1 := by
  simp only [imageFiberReference, div_eq_mul_inv, ← Finset.sum_mul]
  rw [← finitePush_imageEndpoint_eq_fiber, mul_inv_cancel₀ hy]

theorem imageFiberReference_reconstruct_of_nonneg (S : Finset G) (φ : G → H) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (y : S.image φ) (x : fiber S φ y.val) :
    finitePush ν (imageEndpoint S φ) y * imageFiberReference S φ ν y x = ν (imageFiberEndpoint S φ y x) :=
  conditionalWeight_mul_mass ν hν (imageEndpoint S φ) y ((imageFiberEquiv S φ y).symm x)

theorem imageFiber_expectation_of_nonneg (S : Finset G) (φ : G → H) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (g : S → ℝ) :
    (∑ x, ν x * g x) = ∑ y, finitePush ν (imageEndpoint S φ) y *
      ∑ x, imageFiberReference S φ ν y x * g (imageFiberEndpoint S φ y x) := by
  rw [imageFiber_sum S φ (fun x ↦ ν x * g x)]
  simp only [Finset.mul_sum, ← mul_assoc, imageFiberReference_reconstruct_of_nonneg S φ ν hν]

/-- Entropy disintegration on literal support fibers, retaining zero-mass
fibers with zero contribution. -/
theorem imageFiber_entropy_chain (S : Finset G) (φ : G → H) (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) :
    finiteEntropy ν = finiteEntropy (finitePush ν (imageEndpoint S φ)) +
      ∑ y, finitePush ν (imageEndpoint S φ) y * finiteEntropy (imageFiberReference S φ ν y) := by
  rw [finiteEntropy_fiber_chain ν hν (imageEndpoint S φ)]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  unfold finiteEntropy
  apply Fintype.sum_equiv (imageFiberEquiv S φ y)
  intro x
  rfl

theorem imageFiber_relativeEntropy_chain (S : Finset G) (φ : G → H) (ν u : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hu : ∀ x, 0 < u x) :
    finiteRelEntropy ν u = finiteRelEntropy (finitePush ν (imageEndpoint S φ)) (finitePush u (imageEndpoint S φ)) +
      ∑ y, finitePush ν (imageEndpoint S φ) y *
        finiteRelEntropy (imageFiberReference S φ ν y) (imageFiberReference S φ u y) := by
  rw [finiteRelEntropy_fiber_chain ν u hν hu (imageEndpoint S φ)]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  unfold finiteRelEntropy
  apply Fintype.sum_equiv (imageFiberEquiv S φ y)
  intro x
  rfl

end
end Erdos539Geometry
