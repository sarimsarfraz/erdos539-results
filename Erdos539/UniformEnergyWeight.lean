/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ReferenceUniformRoot

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def uniformEnergyWeight (S : Finset G) : S → ℝ := fun _ ↦ 1 / Real.sqrt (S.card : ℝ)

omit [AddCommGroup G] [DecidableEq G] in
theorem uniformEnergyWeight_sq (S : Finset G) (x : S) :
    uniformEnergyWeight S x ^ 2 = uniformReference S x := by
  simp only [uniformEnergyWeight, uniformReference, div_pow, one_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)]

omit [AddCommGroup G] [DecidableEq G] in
theorem uniformEnergyWeight_admissible {S : Finset G} (hS : S.Nonempty) :
    uniformEnergyWeight S ∈ admissibleWeights S := by
  refine ⟨fun _ ↦ by unfold uniformEnergyWeight; positivity, ?_⟩
  simp_rw [uniformEnergyWeight_sq]
  exact uniformReference_sum hS

theorem uniformEnergyWeight_energy (S : Finset G) :
    weightedEnergy S (extendWeight S (uniformEnergyWeight S)) =
      countingEnergy S / (S.card : ℝ) ^ 2 := by
  change weightedGibbsPartition S (fun _ ↦ 1 / Real.sqrt (S.card : ℝ)) = _
  rw [weightedGibbsPartition_constant]
  have he : (1 / Real.sqrt (S.card : ℝ)) ^ 4 = 1 / (S.card : ℝ) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, div_pow, one_pow,
      Real.sq_sqrt (Nat.cast_nonneg _), div_pow, one_pow]
  rw [he]
  ring

end
end Erdos539Geometry
