/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.Fans
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {α β ι : Type*}

def fiber (F : Finset α) (f : α → β) (b : β) : Finset α :=
  F.filter (fun x ↦ f x = b)

def maxFiber (F : Finset α) (f : α → β) : ℕ :=
  (F.image f).sup (fun b ↦ (fiber F f b).card)

@[simp] theorem mem_fiber {F : Finset α} {f : α → β} {b : β} {x : α} :
    x ∈ fiber F f b ↔ x ∈ F ∧ f x = b := Finset.mem_filter

theorem card_fiber_le_maxFiber (F : Finset α) (f : α → β) (b : β) :
    (fiber F f b).card ≤ maxFiber F f := by
  by_cases hb : b ∈ F.image f
  · exact Finset.le_sup (f := fun b ↦ (fiber F f b).card) hb
  · have he : fiber F f b = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hb (Finset.mem_image.mpr ⟨x, (mem_fiber.mp hx).1, (mem_fiber.mp hx).2⟩)
    simp [he]

theorem card_le_image_mul_maxFiber (F : Finset α) (f : α → β) :
    F.card ≤ (F.image f).card * maxFiber F f := by
  calc
    F.card = ∑ b ∈ F.image f, (fiber F f b).card := Finset.card_eq_sum_card_image f F
    _ ≤ ∑ _b ∈ F.image f, maxFiber F f :=
      Finset.sum_le_sum (fun b _ ↦ card_fiber_le_maxFiber F f b)
    _ = _ := by simp

def project (I : Finset ι) (x : ι → ℝ) : I → ℝ := fun i ↦ x i

def projection (F : Finset (ι → ℝ)) (I : Finset ι) : Finset (I → ℝ) :=
  F.image (project I)

def differences (F : Finset (ι → ℝ)) : Finset (ι → ℝ) :=
  (F ×ˢ F).image (fun p ↦ p.1 - p.2)

@[simp] theorem mem_differences {F : Finset (ι → ℝ)} {z : ι → ℝ} :
    z ∈ differences F ↔ ∃ x ∈ F, ∃ y ∈ F, x - y = z := by
  simp only [differences, Finset.mem_image, Prod.exists, Finset.mem_product]
  aesop

/-- Translates of a single coordinate fiber give disjoint ordinary differences. -/
theorem projection_mul_card_fiber_le_differences
    (F : Finset (ι → ℝ)) (I : Finset ι) (b : I → ℝ) :
    (projection F I).card * (fiber F (project I) b).card ≤ (differences F).card := by
  classical
  let r : {y // y ∈ projection F I} → (ι → ℝ) :=
    fun y ↦ Classical.choose (Finset.mem_image.mp y.property)
  have hr (y : {y // y ∈ projection F I}) :
      r y ∈ F ∧ project I (r y) = y.val :=
    Classical.choose_spec (Finset.mem_image.mp y.property)
  let D := (projection F I).attach ×ˢ fiber F (project I) b
  let g : {y // y ∈ projection F I} × (ι → ℝ) → (ι → ℝ) :=
    fun z ↦ r z.1 - z.2
  have hcard : D.card ≤ (differences F).card := by
    apply Finset.card_le_card_of_injOn g
    · intro z hz
      have hx := mem_fiber.mp (Finset.mem_product.mp hz).2
      exact mem_differences.mpr ⟨r z.1, (hr z.1).1, z.2, hx.1, rfl⟩
    · intro z hz w hw h
      have hx := mem_fiber.mp (Finset.mem_product.mp hz).2
      have hy := mem_fiber.mp (Finset.mem_product.mp hw).2
      have hfirst : z.1 = w.1 := by
        apply Subtype.ext
        funext i
        have he := congrFun h i
        change r z.1 i - z.2 i = r w.1 i - w.2 i at he
        have hf := congrFun (hx.2.trans hy.2.symm) i
        change z.2 i = w.2 i at hf
        have hzv := congrFun (hr z.1).2 i
        have hwv := congrFun (hr w.1).2 i
        change r z.1 i = z.1.val i at hzv
        change r w.1 i = w.1.val i at hwv
        linarith
      apply Prod.ext hfirst
      funext i
      have he := congrFun h i
      change r z.1 i - z.2 i = r w.1 i - w.2 i at he
      rw [hfirst] at he
      linarith
  simpa only [D, Finset.card_product, Finset.card_attach] using hcard

/-- The manuscript's projection-size times largest-fiber bound. -/
theorem projection_mul_maxFiber_le_differences
    (F : Finset (ι → ℝ)) (I : Finset ι) :
    (projection F I).card * maxFiber F (project I) ≤ (differences F).card := by
  by_cases hF : F.Nonempty
  · have hp : 0 < (projection F I).card := Finset.card_pos.mpr (hF.image _)
    have hmax : maxFiber F (project I) ≤ (differences F).card / (projection F I).card := by
      apply Finset.sup_le
      intro b _hb
      apply (Nat.le_div_iff_mul_le hp).mpr
      simpa only [Nat.mul_comm] using projection_mul_card_fiber_le_differences F I b
    simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp).mp hmax
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simp [he, projection]

/-- An ordinary difference is determined by its positive and negative parts. -/
theorem differences_card_le_posDiff_sq (F : Finset (ι → ℝ)) :
    (differences F).card ≤ (posDiff F).card ^ 2 := by
  have h : (differences F).card ≤ (posDiff F ×ˢ posDiff F).card := by
    apply Finset.card_le_card_of_injOn (fun z ↦ (pdiff z 0, pdiff 0 z))
    · intro z hz
      obtain ⟨x, hx, y, hy, rfl⟩ := mem_differences.mp hz
      apply Finset.mem_product.mpr
      constructor
      · apply mem_posDiff.mpr
        refine ⟨x, hx, y, hy, ?_⟩
        ext i
        simp [pdiff]
      · apply mem_posDiff.mpr
        refine ⟨y, hy, x, hx, ?_⟩
        ext i
        simp [pdiff, neg_sub]
    · exact (anchored_split_injective 0).injOn
  simpa only [Finset.card_product, pow_two] using h

theorem projection_mul_maxFiber_le_posDiff_sq
    (F : Finset (ι → ℝ)) (I : Finset ι) :
    (projection F I).card * maxFiber F (project I) ≤ (posDiff F).card ^ 2 :=
  (projection_mul_maxFiber_le_differences F I).trans (differences_card_le_posDiff_sq F)

end
end Erdos539Geometry
