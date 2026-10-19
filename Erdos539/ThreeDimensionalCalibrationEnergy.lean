/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ThreeDimensionalCalibrationFans

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
local instance calibrationThreeEnergyIntegerDecidableEq : DecidableEq (CalibrationThreeCoordinates → ℤ) := Classical.decEq _

/-- Additive real realization of the integral geometry. -/
def integerRealAddHom {ι : Type} : (ι → ℤ) →+ (ι → ℝ) where
  toFun := integerToReal
  map_zero' := by funext i; simp [integerToReal]
  map_add' a b := by funext i; simp [integerToReal]

local instance integerRealEnergyDecidableEq {ι : Type} : DecidableEq (ι → ℝ) := Classical.decEq _

theorem countingEnergy_integerRealSet {ι : Type} (F : Finset (ι → ℤ)) :
    countingEnergy (integerRealSet F) = countingEnergy F := by
  change countingEnergy (F.image (integerRealAddHom : (ι → ℤ) →+ (ι → ℝ))) = _
  exact countingEnergy_image_of_sum_injective F integerRealAddHom integerToReal_injective.injOn integerToReal_injective.injOn

def calibrationThreeReal (T : ℕ) : Finset (CalibrationThreeCoordinates → ℝ) :=
  integerRealSet (calibrationThree T)

theorem calibrationThreeReal_card {T : ℕ} (hT : 0 < T) : (calibrationThreeReal T).card = T ^ 8 := by
  rw [calibrationThreeReal, integerRealSet_card, calibrationThree_card hT]

theorem calibrationThreeReal_nonempty {T : ℕ} (hT : 0 < T) : (calibrationThreeReal T).Nonempty := by
  apply Finset.card_pos.mp
  rw [calibrationThreeReal_card hT]
  positivity

theorem calibrationThreeReal_maxFan {T : ℕ} (hT : 0 < T) :
    maxFan (calibrationThreeReal T) ≤ 4 * T ^ 5 := calibrationThree_maxFan hT

theorem countingEnergy_interval_cubic (N : ℕ) :
    (2 / 3 : ℝ) * (N : ℝ) ^ 3 ≤ countingEnergy (scalarInterval N) := by
  rw [countingEnergy_scalarInterval]
  nlinarith [Nat.cast_nonneg (α := ℝ) N]

/-- The real three-dimensional support has energy at least (2/3)^5 T^24. -/
theorem calibrationThreeReal_energy_lower {T : ℕ} (hT : 0 < T) :
    (2 / 3 : ℝ) ^ 5 * (T : ℝ) ^ 24 ≤ countingEnergy (calibrationThreeReal T) := by
  rw [calibrationThreeReal, countingEnergy_integerRealSet, calibrationThree_countingEnergy hT]
  have h2 := countingEnergy_interval_cubic (T ^ 2)
  have h1 := countingEnergy_interval_cubic T
  have h3 := countingEnergy_interval_cubic (T ^ 3)
  simp only [Nat.cast_pow] at h2 h3
  have he1 : 0 ≤ countingEnergy (scalarInterval T) := (by positivity : (0 : ℝ) ≤ (2 / 3) * (T : ℝ) ^ 3).trans h1
  have he2 : 0 ≤ countingEnergy (scalarInterval (T ^ 2)) := (by positivity : (0 : ℝ) ≤ (2 / 3) * ((T : ℝ) ^ 2) ^ 3).trans h2
  calc
    _ = ((2 / 3 : ℝ) * ((T : ℝ) ^ 2) ^ 3) * (((2 / 3 : ℝ) * (T : ℝ) ^ 3) ^ 3) *
      ((2 / 3 : ℝ) * ((T : ℝ) ^ 3) ^ 3) := by ring
    _ ≤ _ := by gcongr

end
end Erdos539Geometry
