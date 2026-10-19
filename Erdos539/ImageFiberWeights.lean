/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsMixedPartition

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {G H : Type*} [DecidableEq G] [DecidableEq H]
local instance imageWeightDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

def imageRestrictedWeight (S : Finset G) (φ : G → H) (f : S → ℝ)
    (y : S.image φ) (x : S) : ℝ := if φ x.val = y.val then f x else 0

def imageFiberWeight (S : Finset G) (φ : G → H) (f : S → ℝ)
    (y : S.image φ) (x : fiber S φ y.val) : ℝ := f (imageFiberEndpoint S φ y x)

theorem extend_imageRestrictedWeight (S : Finset G) (φ : G → H) (f : S → ℝ) (y : S.image φ) :
    extendWeight S (imageRestrictedWeight S φ f y) =
      extendWeight (fiber S φ y.val) (imageFiberWeight S φ f y) := by
  funext x
  by_cases hx : x ∈ S
  · by_cases hy : φ x = y.val
    · have hxy := mem_fiber.mpr ⟨hx, hy⟩
      simp only [extendWeight, dif_pos hx, dif_pos hxy, imageRestrictedWeight, if_pos hy,
        imageFiberWeight, imageFiberEndpoint]
    · have hxy : x ∉ fiber S φ y.val := fun h ↦ hy (mem_fiber.mp h).2
      simp only [extendWeight, dif_pos hx, dif_neg hxy, imageRestrictedWeight, if_neg hy]
  · have hxy : x ∉ fiber S φ y.val := fun h ↦ hx (mem_fiber.mp h).1
    simp only [extendWeight, dif_neg hx, dif_neg hxy]

variable [AddCommGroup G]

theorem imageRestrictedWeight_partition (S : Finset G) (φ : G → H) (f : S → ℝ) (y : S.image φ) :
    weightedGibbsPartition S (imageRestrictedWeight S φ f y) =
      weightedGibbsPartition (fiber S φ y.val) (imageFiberWeight S φ f y) := by
  rw [weightedGibbsPartition, extend_imageRestrictedWeight]
  symm
  exact weightedEnergy_support (fun _ hx ↦ (mem_fiber.mp hx).1) _
    (fun _ _ hn ↦ extendWeight_zero_of_not_mem _ _ hn)

theorem additiveWeight_image_push (S : Finset G) (φ : G → H) (f : S → ℝ) (i j k l : S.image φ) :
    finitePush (fun z : (S × S) × (S × S) ↦ additiveQuadrupleWeight S f z.1.1 z.1.2 z.2.1 z.2.2)
      (StationaryAdditiveLaw.mapFour (imageEndpoint S φ)) ((i, j), (k, l)) =
        mixedWeightedEnergy S (extendWeight S (imageRestrictedWeight S φ f i))
          (extendWeight S (imageRestrictedWeight S φ f j))
          (extendWeight S (imageRestrictedWeight S φ f k))
          (extendWeight S (imageRestrictedWeight S φ f l)) := by
  rw [finitePush, mixedWeightedEnergy_subtype]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  simp only [StationaryAdditiveLaw.mapFour, Prod.mk.injEq, Subtype.ext_iff,
    imageEndpoint, and_assoc, imageRestrictedWeight, additiveQuadrupleWeight]
  by_cases he : a.val + b.val = c.val + d.val <;>
    by_cases ha : φ a.val = i.val <;> by_cases hb : φ b.val = j.val <;>
    by_cases hc : φ c.val = k.val <;> by_cases hd : φ d.val = l.val <;> simp [he, ha, hb, hc, hd]

/-- Actual image partitions inherit any positive bounds for the literal
fiber energies. No stationarity or optimality of the weights is required. -/
theorem additiveWeight_image_push_le (S : Finset G) (φ : G → H) (f : S → ℝ)
    (B : S.image φ → ℝ) (hB : ∀ y, 0 < B y)
    (hpart : ∀ y, weightedGibbsPartition (fiber S φ y.val) (imageFiberWeight S φ f y) ≤ B y)
    (i j k l : S.image φ) :
    finitePush (fun z : (S × S) × (S × S) ↦ additiveQuadrupleWeight S f z.1.1 z.1.2 z.2.1 z.2.2)
      (StationaryAdditiveLaw.mapFour (imageEndpoint S φ)) ((i, j), (k, l)) ≤
        B i ^ (1 / 4 : ℝ) * B j ^ (1 / 4 : ℝ) * B k ^ (1 / 4 : ℝ) * B l ^ (1 / 4 : ℝ) := by
  rw [additiveWeight_image_push]
  have hrow (y : S.image φ) : weightedEnergy S (extendWeight S (imageRestrictedWeight S φ f y)) ≤
      1 * (B y ^ (1 / 4 : ℝ)) ^ 4 := by
    change weightedGibbsPartition S _ ≤ _
    rw [imageRestrictedWeight_partition, one_mul, ← Real.rpow_mul_natCast (hB y).le]
    norm_num
    exact hpart y
  have h := mixedWeightedEnergy_le_common_bound S
    (extendWeight S (imageRestrictedWeight S φ f i))
    (extendWeight S (imageRestrictedWeight S φ f j))
    (extendWeight S (imageRestrictedWeight S φ f k))
    (extendWeight S (imageRestrictedWeight S φ f l))
    (by norm_num : (0 : ℝ) ≤ 1)
    (Real.rpow_nonneg (hB i).le _) (Real.rpow_nonneg (hB j).le _)
    (Real.rpow_nonneg (hB k).le _) (Real.rpow_nonneg (hB l).le _)
    (hrow i) (hrow j) (hrow k) (hrow l)
  simpa only [one_mul] using h

end
end Erdos539Geometry
