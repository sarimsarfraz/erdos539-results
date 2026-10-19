/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CollectiveCountingEnergy
import Erdos539.FiniteCollectiveEnergyBudgets
import Erdos539.ImageFiberAssembly

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]
local instance collectiveBudgetImageDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

omit [DecidableEq G] in
theorem sum_actual_fiber_card (S : Finset G) (φ : G →+ H) :
    (∑ y : S.image φ, ((fiber S φ y.val).card : ℝ)) = S.card := by
  have h := imageFiber_sum S φ (fun _ ↦ (1 : ℝ))
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, mul_one] using h.symm

/-- The mean ordinary counting-energy defect of actual fibers is paid
by the root's ordinary difference doubling. -/
theorem collective_fiber_log_defect {S : Finset G} (hS : S.Nonempty) (φ : G →+ H) :
    (∑ y : S.image φ, ((fiber S φ y.val).card : ℝ) / S.card *
      Real.log (((fiber S φ y.val).card : ℝ) ^ 3 / countingEnergy (fiber S φ y.val))) ≤
        Real.log ((S - S).card / (S.card : ℝ)) := by
  obtain ⟨a, ha⟩ := hS
  letI : Nonempty (S.image φ) := ⟨⟨φ a, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩⟩
  apply finite_collective_log_budget
    (fun y : S.image φ ↦ ((fiber S φ y.val).card : ℝ)) (fun y ↦ countingEnergy (fiber S φ y.val))
  · intro y
    exact_mod_cast (imageFiber_nonempty S φ y).card_pos
  · intro y
    exact countingEnergy_pos (imageFiber_nonempty S φ y)
  · exact_mod_cast (show S.Nonempty from ⟨a, ha⟩).card_pos
  · exact sum_actual_fiber_card S φ
  · exact collective_counting_energy ⟨a, ha⟩ φ

/-- Actual fiber energies supply total reflected-support size at least
N^2/|S-S| = N/K, before selecting a common coordinate sign cell. -/
theorem collective_fiber_inverse_energy {S : Finset G} (hS : S.Nonempty) (φ : G →+ H) :
    (S.card : ℝ) ^ 2 / (S - S).card ≤
      ∑ y : S.image φ, countingEnergy (fiber S φ y.val) / ((fiber S φ y.val).card : ℝ) ^ 2 := by
  obtain ⟨a, ha⟩ := hS
  letI : Nonempty (S.image φ) := ⟨⟨φ a, Finset.mem_image.mpr ⟨a, ha, rfl⟩⟩⟩
  apply finite_collective_inverse_budget
    (fun y : S.image φ ↦ ((fiber S φ y.val).card : ℝ)) (fun y ↦ countingEnergy (fiber S φ y.val))
  · intro y
    exact_mod_cast (imageFiber_nonempty S φ y).card_pos
  · intro y
    exact countingEnergy_pos (imageFiber_nonempty S φ y)
  · exact sum_actual_fiber_card S φ
  · exact collective_counting_energy ⟨a, ha⟩ φ

end
end Erdos539Geometry
