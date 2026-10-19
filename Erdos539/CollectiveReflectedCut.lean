/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CollectiveReflectedSignCell

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι H : Type*} [AddCommGroup H] [DecidableEq H]
local instance collectiveCutVectorDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _
local instance collectiveCutImageDecidableEq (S : Finset (ι → ℝ)) (φ : (ι → ℝ) → H) :
    DecidableEq (S.image φ) := Classical.decEq _

/-- The improved simultaneous reflected cut, with retention 2^(-b)N/K
and both actual forward-fan witnesses in each retained original fiber. -/
theorem exists_collective_reflected_cut {S : Finset (ι → ℝ)} (hS : S.Nonempty)
    (φ : (ι → ℝ) →+ H) (B : Finset ι) :
    ∃ (P : Finset ι) (A : Finset (ι → ℝ)), P ⊆ B ∧ A ⊆ S ∧ A.Nonempty ∧
      (S.card : ℝ) ^ 2 / ((2 : ℝ) ^ B.card * (S - S).card) ≤ A.card ∧
      ∀ y : S.image φ, (fiber A φ y.val).Nonempty →
        ∃ a ∈ fiber A φ y.val, collectiveReflectedCenter S φ y - a ∈ fiber S φ y.val ∧
          (projection (fiber A φ y.val) P).card ≤
            (fan (fiber S φ y.val) (collectiveReflectedCenter S φ y - a)).card ∧
          (projection (fiber A φ y.val) (B \ P)).card ≤ (fan (fiber S φ y.val) a).card := by
  obtain ⟨P, A, hP, hAR, hA, hsize, hmask⟩ := exists_common_reflected_sign_cell hS φ B
  have hAS := hAR.trans (collectiveReflectedSubset_subset S φ)
  refine ⟨P, A, hP, hAS, hA, hsize, ?_⟩
  intro y hy
  have hf : fiber A φ y.val ⊆ collectiveReflectedFiber S φ y := by
    intro x hx
    rw [← collectiveReflectedSubset_fiber]
    exact mem_fiber.mpr ⟨hAR (mem_fiber.mp hx).1, (mem_fiber.mp hx).2⟩
  apply reflected_sign_projection_fans hy hf B P
  intro x hx
  have hx' := mem_fiber.mp hx
  have hm := hmask x hx'.1
  change reflectionSignMask B (originalFiberReflectionCenter S φ x) x = P at hm
  rwa [originalFiberReflectionCenter_eq S φ y (mem_fiber.mpr ⟨hAS hx'.1, hx'.2⟩)] at hm

/-- Both complementary projection sizes are bounded by the same
original fiber's largest forward fan. Empty retained fibers are included. -/
theorem exists_collective_reflected_cut_maxFan {S : Finset (ι → ℝ)} (hS : S.Nonempty)
    (φ : (ι → ℝ) →+ H) (B : Finset ι) :
    ∃ (P : Finset ι) (A : Finset (ι → ℝ)), P ⊆ B ∧ A ⊆ S ∧ A.Nonempty ∧
      (S.card : ℝ) ^ 2 / ((2 : ℝ) ^ B.card * (S - S).card) ≤ A.card ∧
      ∀ y : S.image φ, (projection (fiber A φ y.val) P).card ≤ maxFan (fiber S φ y.val) ∧
        (projection (fiber A φ y.val) (B \ P)).card ≤ maxFan (fiber S φ y.val) := by
  obtain ⟨P, A, hP, hAS, hA, hsize, hw⟩ := exists_collective_reflected_cut hS φ B
  refine ⟨P, A, hP, hAS, hA, hsize, ?_⟩
  intro y
  by_cases hy : (fiber A φ y.val).Nonempty
  · obtain ⟨a, ha, hb, hleft, hright⟩ := hw y hy
    have haS : a ∈ fiber S φ y.val := mem_fiber.mpr ⟨hAS (mem_fiber.mp ha).1, (mem_fiber.mp ha).2⟩
    exact ⟨hleft.trans (card_fan_le_maxFan hb), hright.trans (card_fan_le_maxFan haS)⟩
  · have he := Finset.not_nonempty_iff_eq_empty.mp hy
    simp only [he, projection, Finset.image_empty, Finset.card_empty, Nat.zero_le, and_self]

end
end Erdos539Geometry
