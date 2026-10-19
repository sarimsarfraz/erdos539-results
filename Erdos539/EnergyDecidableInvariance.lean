/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.EnergyMaximizer

namespace Erdos539Geometry
noncomputable section
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Equality-testing implementation choices do not change the finite norm.
This makes coordinate-reindexing proofs independent of Pi instance choices. -/
theorem energyNorm_eq_classical (S : Finset G) :
    energyNorm S = @energyNorm G _ (Classical.decEq G) S := by
  have he : (inferInstance : DecidableEq G) = Classical.decEq G := Subsingleton.elim _ _
  cases he
  rfl

theorem weightedEnergy_eq_classical (S : Finset G) (f : G → ℝ) :
    weightedEnergy S f = @weightedEnergy G _ (Classical.decEq G) S f := by
  have he : (inferInstance : DecidableEq G) = Classical.decEq G := Subsingleton.elim _ _
  cases he
  rfl

end
end Erdos539Geometry
