/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ImageFiberConditionalEntropy

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {G H : Type*} [DecidableEq H]
local instance imageEntropyBoundIndexDecidableEq (S : Finset G) (φ : G → H) : DecidableEq (S.image φ) := Classical.decEq _

/-- Conditional entropy is at most the logarithm of the largest actual
fiber, including when some endpoint masses vanish. -/
theorem finiteEntropy_le_image_add_log_maxFiber (S : Finset G)
    (φ : G → H) (ν : S → ℝ) (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    finiteEntropy ν ≤ finiteEntropy (finitePush ν (imageEndpoint S φ)) + Real.log (maxFiber S φ) := by
  have hpoint : ∀ y : S.image φ,
      finitePush ν (imageEndpoint S φ) y * finiteEntropy (imageFiberReference S φ ν y) ≤
        finitePush ν (imageEndpoint S φ) y * Real.log (maxFiber S φ) := by
    intro y
    by_cases hy : finitePush ν (imageEndpoint S φ) y = 0
    · simp [hy]
    have hne := imageFiber_nonempty S φ y
    letI : Nonempty (fiber S φ y.val) := hne.coe_sort
    have hh := finiteEntropy_le_log_card (imageFiberReference S φ ν y)
      (imageFiberReference_nonneg S φ ν hν y) (imageFiberReference_sum_of_mass_ne_zero S φ ν y hy)
    simp only [Fintype.card_coe] at hh
    have hc : ((fiber S φ y.val).card : ℝ) ≤ maxFiber S φ := by
      exact_mod_cast card_fiber_le_maxFiber S φ y.val
    have hl := Real.log_le_log (by exact_mod_cast hne.card_pos : (0 : ℝ) < (fiber S φ y.val).card) hc
    exact mul_le_mul_of_nonneg_left (hh.trans hl) (finitePush_nonneg ν _ hν y)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun y _ ↦ hpoint y)
  rw [← Finset.sum_mul, finitePush_sum, hs, one_mul] at hsum
  rw [imageFiber_entropy_chain S φ ν hν]
  linarith

end
end Erdos539Geometry
