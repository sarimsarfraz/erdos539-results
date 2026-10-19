/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.MixedEnergyStability

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [AddCommGroup H] [DecidableEq H]
local instance autocorrelationImageDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

omit [DecidableEq G] [AddCommGroup H] [DecidableEq H] in
theorem weightedCorrelation_support {A S : Finset G} (hAS : A ⊆ S) (f : G → ℝ)
    (hzero : ∀ x ∈ S, x ∉ A → f x = 0) (z : G) :
    weightedCorrelation A f f z = weightedCorrelation S f f z := by
  apply Finset.sum_subset
  · intro p hp
    obtain ⟨hp, he⟩ := mem_fiber.mp hp
    exact mem_fiber.mpr ⟨Finset.product_subset_product hAS hAS hp, he⟩
  · intro p hp hpa
    have hs := mem_fiber.mp hp
    have hn : p ∉ A ×ˢ A := fun h ↦ hpa (mem_fiber.mpr ⟨h, hs.2⟩)
    exact pair_weight_zero_of_not_mem f hzero hs.1 hn

def imageAutocorrelationWeight (S : Finset G) (φ : G → H) (u : S → ℝ) (y : S.image φ) : G → ℝ :=
  extendWeight S (imageConditionalWeight S φ u y)

omit [AddCommGroup H] in
theorem imageAutocorrelationWeight_energy (S : Finset G) (φ : G → H) (u : S → ℝ) (y : S.image φ) :
    weightedEnergy S (imageAutocorrelationWeight S φ u y) =
      referencePartition (fiber S φ y.val) (imageFiberReference S φ u y) :=
  imageConditionalWeight_partition S φ u y

omit [AddCommGroup H] in
/-- The root-ambient expression is exactly the normalized autocorrelation
of the literal actual fiber; zero extension does not change any value. -/
theorem image_normalizedAutocorrelation_eq (S : Finset G) (φ : G → H) (u : S → ℝ)
    (y : S.image φ) (z : G) :
    normalizedAutocorrelation S (imageAutocorrelationWeight S φ u y) z =
      weightedCorrelation (fiber S φ y.val)
        (extendWeight (fiber S φ y.val) (referencePowerWeight (imageFiberReference S φ u y)))
        (extendWeight (fiber S φ y.val) (referencePowerWeight (imageFiberReference S φ u y))) z /
          Real.sqrt (referencePartition (fiber S φ y.val) (imageFiberReference S φ u y)) := by
  rw [normalizedAutocorrelation, imageAutocorrelationWeight_energy]
  unfold imageAutocorrelationWeight
  rw [extend_imageConditionalWeight, ← weightedCorrelation_support (fun _ hx ↦ (mem_fiber.mp hx).1) _
    (fun _ _ hn ↦ extendWeight_zero_of_not_mem _ _ hn)]

def imageSixAutocorrelationDistances (S : Finset G) (φ : G → H) (u : S → ℝ)
    (a b c d : S.image φ) : ℝ :=
  autocorrelationDistanceSq S (imageAutocorrelationWeight S φ u a) (imageAutocorrelationWeight S φ u b) +
  autocorrelationDistanceSq S (imageAutocorrelationWeight S φ u a) (imageAutocorrelationWeight S φ u c) +
  autocorrelationDistanceSq S (imageAutocorrelationWeight S φ u a) (imageAutocorrelationWeight S φ u d) +
  autocorrelationDistanceSq S (imageAutocorrelationWeight S φ u b) (imageAutocorrelationWeight S φ u c) +
  autocorrelationDistanceSq S (imageAutocorrelationWeight S φ u b) (imageAutocorrelationWeight S φ u d) +
  autocorrelationDistanceSq S (imageAutocorrelationWeight S φ u c) (imageAutocorrelationWeight S φ u d)

omit [AddCommGroup H] in
theorem imageSixAutocorrelationDistances_nonneg (S : Finset G) (φ : G → H) (u : S → ℝ)
    (a b c d : S.image φ) : 0 ≤ imageSixAutocorrelationDistances S φ u a b c d := by
  unfold imageSixAutocorrelationDistances
  repeat' apply add_nonneg
  all_goals exact autocorrelationDistanceSq_nonneg S _ _

theorem imageSixAutocorrelationDistances_le {S : Finset G} (hS : S.Nonempty) (φ : G →+ H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) {a b c d : S.image φ}
    (hm : (projectedReferenceLaw S φ u hu).mass a b c d ≠ 0) :
    imageSixAutocorrelationDistances S φ u a b c d ≤ 12 * imageLiftSlack S φ u a b c d := by
  have hpos (y : S.image φ) : 0 < weightedEnergy S (imageAutocorrelationWeight S φ u y) := by
    rw [imageAutocorrelationWeight_energy]
    exact referencePartition_pos (imageFiber_nonempty S φ y) (imageFiberReference_pos S φ u hu y)
  have hK := imageMixedPartition_pos_of_projected_mass hS φ u hu hm
  have hh := six_autocorrelation_distances_le S
    (imageAutocorrelationWeight S φ u a) (imageAutocorrelationWeight S φ u b)
    (imageAutocorrelationWeight S φ u c) (imageAutocorrelationWeight S φ u d)
    (hpos a) (hpos b) (hpos c) (hpos d) hK
  have he : mixedEnergyGeometricMean S
      (imageAutocorrelationWeight S φ u a) (imageAutocorrelationWeight S φ u b)
      (imageAutocorrelationWeight S φ u c) (imageAutocorrelationWeight S φ u d) =
        imageGeometricPartition S φ u a b c d := by
    simp only [mixedEnergyGeometricMean, imageAutocorrelationWeight_energy, imageGeometricPartition]
  rw [he] at hh
  exact hh

def meanImageAutocorrelationDistance (S : Finset G) (φ : G →+ H) (u : S → ℝ) (hu : ∀ x, 0 < u x) : ℝ :=
  ∑ a, ∑ b, ∑ c, ∑ d, (projectedReferenceLaw S φ u hu).mass a b c d *
    imageSixAutocorrelationDistances S φ u a b c d

theorem meanImageAutocorrelationDistance_nonneg (S : Finset G) (φ : G →+ H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) : 0 ≤ meanImageAutocorrelationDistance S φ u hu := by
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  apply Finset.sum_nonneg
  intro c _
  apply Finset.sum_nonneg
  intro d _
  exact mul_nonneg ((projectedReferenceLaw S φ u hu).nonneg a b c d)
    (imageSixAutocorrelationDistances_nonneg S φ u a b c d)

/-- The twelve-fold stability charge is averaged over actual interacting
quadruples. Missing lifts have zero mass, and no all-pairs claim is made. -/
theorem meanImageAutocorrelationDistance_le {S : Finset G} (hS : S.Nonempty) (φ : G →+ H)
    (u : S → ℝ) (hu : ∀ x, 0 < u x) :
    meanImageAutocorrelationDistance S φ u hu ≤ 12 * meanImageLiftSlack S φ u hu := by
  simp only [meanImageAutocorrelationDistance, meanImageLiftSlack, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  apply Finset.sum_le_sum
  intro b _
  apply Finset.sum_le_sum
  intro c _
  apply Finset.sum_le_sum
  intro d _
  by_cases hm : (projectedReferenceLaw S φ u hu).mass a b c d = 0
  · simp [hm]
  have hh := mul_le_mul_of_nonneg_left (imageSixAutocorrelationDistances_le hS φ u hu hm)
    ((projectedReferenceLaw S φ u hu).nonneg a b c d)
  nlinarith only [hh]

end
end Erdos539Geometry
