/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ImageFiberEntropyBound
import Erdos539.CoordinateEntropySubmodular

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*}
local instance projectionSupportBoundRealDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _
local instance projectionSupportBoundIndexDecidableEq (S : Finset (ι → ℝ)) (I : Finset ι) :
    DecidableEq (projection S I) := Classical.decEq _

/-- Every literal coordinate projection obeys the entropy-to-support bound
with eta=log|S-S|-H, for the same original law and with no reoptimization. -/
theorem projection_log_card_le_entropy_deficit {S : Finset (ι → ℝ)} (hS : S.Nonempty)
    (ν : S → ℝ) (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) (I : Finset ι) :
    Real.log (projection S I).card ≤ coordinateProjectionEntropy S ν I +
      Real.log (differences S).card - finiteEntropy ν := by
  letI : DecidableEq (I → ℝ) := fun a b ↦ @Fintype.decidablePiFintype I (fun _ ↦ ℝ)
    (fun _ ↦ Classical.decEq ℝ) inferInstance a b
  have hcond := finiteEntropy_le_image_add_log_maxFiber S (project I) ν hν hs
  change finiteEntropy ν ≤ coordinateProjectionEntropy S ν I + Real.log (maxFiber S (project I)) at hcond
  have hP : (0 : ℝ) < (projection S I).card := by exact_mod_cast (hS.image (project I)).card_pos
  have hprod := projection_mul_maxFiber_le_differences S I
  have hcard := card_le_image_mul_maxFiber S (project I)
  have hM : 0 < maxFiber S (project I) := by
    by_contra hh
    have he : maxFiber S (project I) = 0 := by omega
    rw [he, mul_zero] at hcard
    have hp := hS.card_pos
    omega
  have hMreal : (0 : ℝ) < maxFiber S (project I) := by exact_mod_cast hM
  have hh := Real.log_le_log (mul_pos hP hMreal) (by exact_mod_cast hprod :
    (projection S I).card * (maxFiber S (project I) : ℝ) ≤ (differences S).card)
  rw [Real.log_mul hP.ne' hMreal.ne'] at hh
  linarith

theorem actualMarginal_log_le_projection_card {S : Finset (ι → ℝ)} (I : Finset ι)
    (f : S → ℝ) (hf : ∑ x, f x ^ 2 = 1) :
    Real.log (actualMarginalEnergy S (extendWeight S f) I) ≤ Real.log (projection S I).card := by
  have hm := actualMarginalEnergy_unit_bounds S I f hf
  exact Real.log_le_log (lt_of_lt_of_le zero_lt_one hm.1) (hm.2.trans (energyNorm_le_card _))

end
end Erdos539Geometry
