/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.EnergyTransport
import Erdos539.MaskedProjection

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*}
local instance maskedEnergyDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

def maskCoordinatesHom (I : Finset ι) : (ι → ℝ) →+ (ι → ℝ) where
  toFun := maskCoordinates I
  map_zero' := by ext i; simp [maskCoordinates]
  map_add' := maskCoordinates_add I

theorem energyNorm_le_maskedProjection {S : Finset (ι → ℝ)} (I : Finset ι)
    (hinj : Set.InjOn (maskCoordinates I) S) :
    energyNorm S ≤ energyNorm (maskedProjection S I) := by
  exact energyNorm_le_injective_image (maskCoordinatesHom I) hinj

end
end Erdos539Geometry
