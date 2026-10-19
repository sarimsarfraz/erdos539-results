/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsConditionalWeights
import Erdos539.EnergyMonotonicity

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [DecidableEq H]
local instance gibbsMixedImageDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

/-- Literal mixed sum over additive lifts in four specified fibers. -/
def imageMixedPartition (S : Finset G) (φ : G → H) (u : S → ℝ) (a b c d : S.image φ) : ℝ :=
  mixedWeightedEnergy S (extendWeight S (imageConditionalWeight S φ u a))
    (extendWeight S (imageConditionalWeight S φ u b))
    (extendWeight S (imageConditionalWeight S φ u c))
    (extendWeight S (imageConditionalWeight S φ u d))

/-- Product of the four actual conditional partition functions' fourth roots. -/
def imageGeometricPartition (S : Finset G) (φ : G → H) (u : S → ℝ) (a b c d : S.image φ) : ℝ :=
  referencePartition (fiber S φ a.val) (imageFiberReference S φ u a) ^ (1 / 4 : ℝ) *
    referencePartition (fiber S φ b.val) (imageFiberReference S φ u b) ^ (1 / 4 : ℝ) *
    referencePartition (fiber S φ c.val) (imageFiberReference S φ u c) ^ (1 / 4 : ℝ) *
    referencePartition (fiber S φ d.val) (imageFiberReference S φ u d) ^ (1 / 4 : ℝ)

theorem imageMixedPartition_nonneg (S : Finset G) (φ : G → H) (u : S → ℝ)
    (hu : ∀ x, 0 < u x) (i j k l : S.image φ) : 0 ≤ imageMixedPartition S φ u i j k l := by
  rw [imageMixedPartition, mixedWeightedEnergy_subtype]
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  apply Finset.sum_nonneg
  intro c _
  apply Finset.sum_nonneg
  intro d _
  split_ifs
  · exact mul_nonneg (mul_nonneg (imageConditionalWeight_nonneg S φ u hu i a)
      (imageConditionalWeight_nonneg S φ u hu j b))
      (mul_nonneg (imageConditionalWeight_nonneg S φ u hu k c)
        (imageConditionalWeight_nonneg S φ u hu l d))
  · rfl

theorem imageGeometricPartition_pos (S : Finset G) (φ : G → H) (u : S → ℝ)
    (hu : ∀ x, 0 < u x) (a b c d : S.image φ) : 0 < imageGeometricPartition S φ u a b c d := by
  have hpos (y : S.image φ) :
      0 < referencePartition (fiber S φ y.val) (imageFiberReference S φ u y) ^ (1 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (referencePartition_pos (imageFiber_nonempty S φ y) (imageFiberReference_pos S φ u hu y)) _
  exact mul_pos (mul_pos (mul_pos (hpos a) (hpos b)) (hpos c)) (hpos d)

/-- Mixed Holder bounds the literal lift partition by the actual child
partition functions, without substituting child energy optimizers. -/
theorem imageMixedPartition_le_geometric (S : Finset G) (φ : G → H) (u : S → ℝ)
    (hu : ∀ x, 0 < u x) (a b c d : S.image φ) :
    imageMixedPartition S φ u a b c d ≤ imageGeometricPartition S φ u a b c d := by
  let Z := fun y : S.image φ ↦ referencePartition (fiber S φ y.val) (imageFiberReference S φ u y)
  have hpos (y : S.image φ) : 0 < Z y :=
    referencePartition_pos (imageFiber_nonempty S φ y) (imageFiberReference_pos S φ u hu y)
  have hroot (y : S.image φ) : 0 ≤ Z y ^ (1 / 4 : ℝ) := Real.rpow_nonneg (hpos y).le _
  have hrow (y : S.image φ) : weightedEnergy S (extendWeight S (imageConditionalWeight S φ u y)) ≤
      1 * (Z y ^ (1 / 4 : ℝ)) ^ 4 := by
    change weightedGibbsPartition S (imageConditionalWeight S φ u y) ≤ _
    rw [imageConditionalWeight_partition, one_mul, ← Real.rpow_mul_natCast (hpos y).le]
    norm_num
    exact le_rfl
  have h := mixedWeightedEnergy_le_common_bound S
    (extendWeight S (imageConditionalWeight S φ u a))
    (extendWeight S (imageConditionalWeight S φ u b))
    (extendWeight S (imageConditionalWeight S φ u c))
    (extendWeight S (imageConditionalWeight S φ u d))
    (by norm_num : (0 : ℝ) ≤ 1) (hroot a) (hroot b) (hroot c) (hroot d)
    (hrow a) (hrow b) (hrow c) (hrow d)
  simpa only [one_mul] using h

end
end Erdos539Geometry
