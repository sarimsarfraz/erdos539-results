/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GibbsMixedPartition

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical

theorem finitePush_div {α β : Type*} [Fintype α] (p : α → ℝ) (f : α → β) (t : ℝ) (b : β) :
    finitePush (fun x ↦ p x / t) f b = finitePush p f b / t := by
  simp only [finitePush, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> simp

variable {G H : Type*} [AddCommGroup G] [DecidableEq G] [DecidableEq H]
local instance gibbsProjectedImageDecidableEq (S : Finset G) (φ : G → H) :
    DecidableEq (S.image φ) := Classical.decEq _

def imageReferenceProduct (S : Finset G) (φ : G → H) (u : S → ℝ) (a b c d : S.image φ) : ℝ :=
  finitePush u (imageEndpoint S φ) a ^ (3 / 4 : ℝ) * finitePush u (imageEndpoint S φ) b ^ (3 / 4 : ℝ) *
    finitePush u (imageEndpoint S φ) c ^ (3 / 4 : ℝ) * finitePush u (imageEndpoint S φ) d ^ (3 / 4 : ℝ)

omit [AddCommGroup G] [DecidableEq G] in
theorem imageReferenceProduct_pos (S : Finset G) (φ : G → H) (u : S → ℝ)
    (hu : ∀ x, 0 < u x) (a b c d : S.image φ) : 0 < imageReferenceProduct S φ u a b c d := by
  have h (y : S.image φ) : 0 < finitePush u (imageEndpoint S φ) y ^ (3 / 4 : ℝ) :=
    Real.rpow_pos_of_pos (finitePush_imageEndpoint_pos S φ u hu y) _
  exact mul_pos (mul_pos (mul_pos (h a) (h b)) (h c)) (h d)

omit [AddCommGroup G] [DecidableEq G] in
theorem imageConditional_four_product (S : Finset G) (φ : G → H) (u : S → ℝ)
    (hu : ∀ x, 0 < u x) (i j k l : S.image φ) (a b c d : S) :
    imageReferenceProduct S φ u i j k l *
      ((imageConditionalWeight S φ u i a * imageConditionalWeight S φ u j b) *
        (imageConditionalWeight S φ u k c * imageConditionalWeight S φ u l d)) =
      if φ a.val = i.val ∧ φ b.val = j.val ∧ φ c.val = k.val ∧ φ d.val = l.val then
        (referencePowerWeight u a * referencePowerWeight u b) *
          (referencePowerWeight u c * referencePowerWeight u d) else 0 := by
  calc
    _ = ((finitePush u (imageEndpoint S φ) i ^ (3 / 4 : ℝ) * imageConditionalWeight S φ u i a) *
        (finitePush u (imageEndpoint S φ) j ^ (3 / 4 : ℝ) * imageConditionalWeight S φ u j b)) *
        ((finitePush u (imageEndpoint S φ) k ^ (3 / 4 : ℝ) * imageConditionalWeight S φ u k c) *
        (finitePush u (imageEndpoint S φ) l ^ (3 / 4 : ℝ) * imageConditionalWeight S φ u l d)) := by
      unfold imageReferenceProduct
      ring
    _ = _ := by
      rw [imageConditionalWeight_reconstruct S φ u hu, imageConditionalWeight_reconstruct S φ u hu,
        imageConditionalWeight_reconstruct S φ u hu, imageConditionalWeight_reconstruct S φ u hu]
      by_cases ha : φ a.val = i.val <;> by_cases hb : φ b.val = j.val <;>
        by_cases hc : φ c.val = k.val <;> by_cases hd : φ d.val = l.val <;> simp [ha, hb, hc, hd]

/-- The exact sum over additive lifts factors into the projected reference
weight times the mixed conditional partition. -/
theorem imageAdditiveWeight_push (S : Finset G) (φ : G → H) (u : S → ℝ)
    (hu : ∀ x, 0 < u x) (i j k l : S.image φ) :
    finitePush (fun z : (S × S) × (S × S) ↦
      additiveQuadrupleWeight S (referencePowerWeight u) z.1.1 z.1.2 z.2.1 z.2.2)
      (StationaryAdditiveLaw.mapFour (imageEndpoint S φ)) ((i, j), (k, l)) =
        imageReferenceProduct S φ u i j k l * imageMixedPartition S φ u i j k l := by
  rw [finitePush, imageMixedPartition, mixedWeightedEnergy_subtype]
  simp only [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  simp only [StationaryAdditiveLaw.mapFour, Prod.mk.injEq, Subtype.ext_iff,
    imageEndpoint, and_assoc]
  by_cases he : a.val + b.val = c.val + d.val
  · simp only [additiveQuadrupleWeight, if_pos he]
    exact (imageConditional_four_product S φ u hu i j k l a b c d).symm
  · simp [additiveQuadrupleWeight, he]

/-- Literal projected density of the parent reference Gibbs law. A
projected quadruple with no additive lift has zero mixed partition. -/
theorem referenceGibbs_projected_density (S : Finset G) (φ : G → H) (u : S → ℝ)
    (hu : ∀ x, 0 < u x) (i j k l : S.image φ) :
    finitePush (referenceGibbsLaw S u hu).flat
      (StationaryAdditiveLaw.mapFour (imageEndpoint S φ)) ((i, j), (k, l)) =
      imageReferenceProduct S φ u i j k l * imageMixedPartition S φ u i j k l / referencePartition S u := by
  change finitePush (fun z : (S × S) × (S × S) ↦
    additiveQuadrupleWeight S (referencePowerWeight u) z.1.1 z.1.2 z.2.1 z.2.2 / referencePartition S u)
    (StationaryAdditiveLaw.mapFour (imageEndpoint S φ)) ((i, j), (k, l)) = _
  rw [finitePush_div, imageAdditiveWeight_push S φ u hu]

end
end Erdos539Geometry
