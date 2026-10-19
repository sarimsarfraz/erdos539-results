/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CountingMixedDifferences
import Erdos539.FiberDifferencePacking

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]

/-- Collective counting-energy control for all actual fibers of an
additive map. Each denominator is that fiber's own ordinary energy. -/
theorem collective_counting_energy {S : Finset G} (hS : S.Nonempty) (φ : G →+ H) :
    (∑ y : S.image φ, ((fiber S φ y.val).card : ℝ) ^ 4 / countingEnergy (fiber S φ y.val)) ≤ (S - S).card := by
  obtain ⟨a, ha⟩ := hS
  letI : Nonempty (S.image φ) := ⟨⟨φ a, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩⟩
  obtain ⟨z, _, hmax⟩ := Finset.univ.exists_max_image
    (fun y : S.image φ ↦ countingEnergyScale (fiber S φ y.val)) Finset.univ_nonempty
  have hpoint (y : S.image φ) : ((fiber S φ y.val).card : ℝ) ^ 4 / countingEnergy (fiber S φ y.val) ≤
      (fiber S φ y.val - fiber S φ z.val).card := by
    rw [← countingEnergyScale_sq]
    calc
      _ ≤ countingEnergyScale (fiber S φ y.val) * countingEnergyScale (fiber S φ z.val) := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left (hmax y (Finset.mem_univ y)) (countingEnergyScale_nonneg _)
      _ ≤ _ := countingEnergyScale_mul_le_sub (imageFiber_nonempty S φ y) (imageFiber_nonempty S φ z)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun y _ ↦ hpoint y)
  have hpack : (∑ y : S.image φ, ((fiber S φ y.val - fiber S φ z.val).card : ℝ)) ≤ (S - S).card := by
    exact_mod_cast sum_card_fiber_sub_le S φ z.val
  exact hsum.trans hpack

end
end Erdos539Geometry
