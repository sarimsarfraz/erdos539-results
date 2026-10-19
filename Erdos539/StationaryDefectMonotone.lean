/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryEntropyFibring

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]
local instance defectMonotoneImageDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

/-- An additive projection cannot increase stationary defect. Zero-mass
fibers contribute zero, so no positivity of every endpoint is required. -/
theorem stationaryEntropyDefect_image_le {S : Finset G} {ν : S → ℝ}
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) (φ : G →+ H) :
    stationaryEntropyDefect (S.image φ) (finitePush ν (imageEndpoint S φ)) ≤
      stationaryEntropyDefect S ν := by
  have h := stationaryEntropyDefect_superadditive hν hs φ
  have hc : 0 ≤ ∑ y, finitePush ν (imageEndpoint S φ) y *
      stationaryEntropyDefect (fiber S φ y.val) (imageFiberReference S φ ν y) := by
    apply Finset.sum_nonneg
    intro y _
    by_cases hy : finitePush ν (imageEndpoint S φ) y = 0
    · simp only [hy, zero_mul, le_refl]
    · exact mul_nonneg (finitePush_nonneg ν _ hν y)
        (stationaryEntropyDefect_bounds _ _ (imageFiberReference_nonneg S φ ν hν y)
          (imageFiberReference_sum_of_mass_ne_zero S φ ν y hy)).1
  exact (le_add_of_nonneg_right hc).trans h

end
end Erdos539Geometry
