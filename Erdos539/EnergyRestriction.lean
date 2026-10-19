/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.EnergySupport

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def restrictSupportWeight {A S : Finset G} (hAS : A ⊆ S) (f : S → ℝ) : A → ℝ :=
  fun x ↦ f ⟨x, hAS x.property⟩

omit [AddCommGroup G] in
theorem extend_restrict_mem {A S : Finset G} (hAS : A ⊆ S) (f : S → ℝ) {x : G} (hx : x ∈ A) :
    extendWeight A (restrictSupportWeight hAS f) x = extendWeight S f x := by
  simp only [extendWeight, dif_pos hx, dif_pos (hAS hx), restrictSupportWeight]

omit [AddCommGroup G] in
theorem restrictSupportWeight_squareSum {A S : Finset G} (hAS : A ⊆ S) (f : S → ℝ) :
    (∑ x, restrictSupportWeight hAS f x ^ 2) = weightSquareSum A (extendWeight S f) := by
  rw [← weightSquareSum_extend]
  apply Finset.sum_congr rfl
  intro x hx
  rw [extend_restrict_mem hAS f hx]

omit [AddCommGroup G] in
theorem restrictSupportWeight_inner {A S : Finset G} (hAS : A ⊆ S) (f : S → ℝ) :
    (∑ x : S, f x * extendWeight A (restrictSupportWeight hAS f) x) =
      weightSquareSum A (extendWeight S f) := by
  let h := restrictSupportWeight hAS f
  calc
    _ = ∑ x ∈ S, extendWeight S f x * extendWeight A h x := by
      rw [← Finset.sum_attach S]
      simp [h]
    _ = ∑ x ∈ A, extendWeight S f x * extendWeight A h x := by
      symm
      apply Finset.sum_subset hAS
      intro x _ hxa
      rw [extendWeight_zero_of_not_mem A h hxa, mul_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      dsimp [h]
      rw [extend_restrict_mem hAS f hx, pow_two]

theorem restrictSupportWeight_energy {A S : Finset G} (hAS : A ⊆ S) (f : S → ℝ) :
    weightedEnergy S (extendWeight A (restrictSupportWeight hAS f)) =
      weightedEnergy A (extendWeight A (restrictSupportWeight hAS f)) := by
  symm
  exact weightedEnergy_support hAS _ (fun _ _ hx ↦ extendWeight_zero_of_not_mem _ _ hx)

end
end Erdos539Geometry
