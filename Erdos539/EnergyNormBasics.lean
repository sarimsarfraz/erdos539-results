/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.EnergyMaximizer

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
theorem weightedCorrelation_zero (S : Finset G) (f : G → ℝ) :
    weightedCorrelation S f f 0 = weightSquareSum S f := by
  have he : fiber (S ×ˢ S) (fun p ↦ p.1 - p.2) 0 = S.diag := by
    ext p
    simp only [mem_fiber, Finset.mem_product, sub_eq_zero, Finset.mem_diag]
    aesop
  rw [weightedCorrelation, he, Finset.sum_diag]
  simp only [weightSquareSum, pow_two]

theorem weightedEnergy_ge_squareSum_sq (S : Finset G) (f : G → ℝ) :
    weightSquareSum S f ^ 2 ≤ weightedEnergy S f := by
  by_cases hS : S.Nonempty
  · obtain ⟨a, ha⟩ := hS
    have hz : (0 : G) ∈ S - S := Finset.mem_sub.mpr ⟨a, ha, a, ha, sub_self a⟩
    rw [← differenceMixedEnergy_self, differenceMixedEnergy]
    have h := Finset.single_le_sum
      (fun z _ ↦ mul_self_nonneg (weightedCorrelation S f f z)) hz
    simpa only [weightedCorrelation_zero, pow_two] using h
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    simp [weightSquareSum, weightedEnergy]

theorem one_le_energyNorm {S : Finset G} (hS : S.Nonempty) : 1 ≤ energyNorm S := by
  rw [energyNorm, dif_pos hS]
  have h := weightedEnergy_ge_squareSum_sq S (extendWeight S (energyMaximizer S hS))
  rw [weightSquareSum_extend, (energyMaximizer_spec S hS).1.2] at h
  simpa using h

theorem energyNorm_pos {S : Finset G} (hS : S.Nonempty) : 0 < energyNorm S :=
  lt_of_lt_of_le (by norm_num) (one_le_energyNorm hS)

@[simp] theorem energyNorm_empty : energyNorm (∅ : Finset G) = 0 := by simp [energyNorm]

@[simp] theorem energyNorm_singleton (a : G) : energyNorm ({a} : Finset G) = 1 := by
  apply le_antisymm
  · simpa using energyNorm_le_card ({a} : Finset G)
  · exact one_le_energyNorm (Finset.singleton_nonempty a)

/-- A normalized nonnegative optimizer exists for the literal finite norm. -/
theorem energyNorm_attained {S : Finset G} (hS : S.Nonempty) :
    ∃ f : S → ℝ, (∀ x, 0 ≤ f x) ∧ (∑ x, f x ^ 2 = 1) ∧
      weightedEnergy S (extendWeight S f) = energyNorm S := by
  exact ⟨energyMaximizer S hS, (energyMaximizer_spec S hS).1.1,
    (energyMaximizer_spec S hS).1.2, by simp [energyNorm, hS]⟩

end
end Erdos539Geometry
