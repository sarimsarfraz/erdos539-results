/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsImageFibers
import Erdos539.GibbsLogProducts

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq H]
local instance imageQuadrupleDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

namespace StationaryAdditiveLaw
variable {S : Finset G} {ν : S → ℝ}

/-- Actual image of all four endpoints under an arbitrary label map.
It is not declared an additive law unless the labels preserve relations. -/
def imageFlat (Q : StationaryAdditiveLaw S ν) (φ : G → H) :
    ((S.image φ) × (S.image φ)) × ((S.image φ) × (S.image φ)) → ℝ :=
  finitePush Q.flat (mapFour (imageEndpoint S φ))

theorem imageFlat_nonneg (Q : StationaryAdditiveLaw S ν) (φ : G → H) : ∀ z, 0 ≤ Q.imageFlat φ z :=
  finitePush_nonneg Q.flat _ (fun _ ↦ Q.nonneg _ _ _ _)

theorem imageFlat_sum (Q : StationaryAdditiveLaw S ν) (φ : G → H) (hν : ∑ x, ν x = 1) :
    ∑ z, Q.imageFlat φ z = 1 := by
  rw [imageFlat, finitePush_sum]
  simpa only [flat, Fintype.sum_prod_type] using Q.total_mass hν

theorem imageFlat_endpoint_expectation (Q : StationaryAdditiveLaw S ν) (φ : G → H) (g : S.image φ → ℝ) :
    (∑ z, Q.imageFlat φ z * (g z.1.1 + g z.1.2 + g z.2.1 + g z.2.2)) =
      4 * ∑ y, finitePush ν (imageEndpoint S φ) y * g y := by
  rw [imageFlat, finitePush_expectation, finitePush_expectation]
  simpa only [mapFour, flat, Fintype.sum_prod_type] using Q.endpoint_expectation (fun x ↦ g (imageEndpoint S φ x))

theorem imageFlat_endpoint_expectation_factor (Q : StationaryAdditiveLaw S ν) (φ : G → H)
    (t : ℝ) (g : S.image φ → ℝ) :
    (∑ z, Q.imageFlat φ z * (t * (g z.1.1 + g z.1.2 + g z.2.1 + g z.2.2))) =
      (4 * t) * ∑ y, finitePush ν (imageEndpoint S φ) y * g y := by
  simp_rw [mul_left_comm _ t]
  rw [← Finset.mul_sum, imageFlat_endpoint_expectation]
  ring

end StationaryAdditiveLaw
end
end Erdos539Geometry
