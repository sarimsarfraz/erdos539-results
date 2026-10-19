/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.Restricted
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {α β : Type*}

theorem card_eq_sum_card_parent [DecidableEq β] (F : Finset α) (f : α → β)
    (T : Finset β) (h : (F : Set α).MapsTo f T) :
    F.card = ∑ b ∈ T, (fiber F f b).card := by
  calc
    _ = ∑ b ∈ T, (F.filter (fun a ↦ f a = b)).card := Finset.card_eq_sum_card_fiberwise h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      congr 1
      ext a
      simp only [Finset.mem_filter, mem_fiber]

theorem card_eq_sum_card_fiber [DecidableEq β] (F : Finset α) (f : α → β) :
    F.card = ∑ b ∈ F.image f, (fiber F f b).card := by
  calc
    _ = ∑ b ∈ F.image f, (F.filter (fun a ↦ f a = b)).card := Finset.card_eq_sum_card_image f F
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      congr 1
      ext a
      simp only [Finset.mem_filter, mem_fiber]

/-- Ordered pairs in one fiber, including diagonal pairs. -/
def samePairs (F : Finset α) (f : α → β) : Finset (α × α) :=
  (F ×ˢ F).filter (fun p ↦ f p.1 = f p.2)

@[simp] theorem mem_samePairs {F : Finset α} {f : α → β} {p : α × α} :
    p ∈ samePairs F f ↔ p.1 ∈ F ∧ p.2 ∈ F ∧ f p.1 = f p.2 := by
  simp only [samePairs, Finset.mem_filter, Finset.mem_product, and_assoc]

theorem card_samePairs [DecidableEq β] (F : Finset α) (f : α → β) :
    (samePairs F f).card = ∑ b ∈ F.image f, (fiber F f b).card ^ 2 := by
  have hmaps : (samePairs F f : Set (α × α)).MapsTo (fun p ↦ f p.1) (F.image f) := by
    intro p hp
    exact Finset.mem_image_of_mem f (mem_samePairs.mp hp).1
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro b _
  have he : {p ∈ samePairs F f | f p.1 = b} = fiber F f b ×ˢ fiber F f b := by
    ext p
    simp only [Finset.mem_filter, mem_samePairs, Finset.mem_product, mem_fiber]
    aesop
  rw [he, Finset.card_product, pow_two]

/-- Cauchy--Schwarz counting, with no division or nonemptiness assumptions. -/
theorem card_sq_le_image_mul_samePairs [DecidableEq β] (F : Finset α) (f : α → β) :
    F.card ^ 2 ≤ (F.image f).card * (samePairs F f).card := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (F.image f)
    (fun _ ↦ (1 : ℕ)) (fun b ↦ (fiber F f b).card)
  simp only [one_mul, one_pow, Finset.sum_const, smul_eq_mul, mul_one] at h
  rw [← card_samePairs F f] at h
  have he : ∑ b ∈ F.image f, (fiber F f b).card = F.card :=
    (card_eq_sum_card_fiber F f).symm
  rwa [he] at h

theorem card_sq_le_parent_image_mul_samePairs [DecidableEq β] {A S : Finset α} (hAS : A ⊆ S)
    (f : α → β) :
    A.card ^ 2 ≤ (S.image f).card * (samePairs A f).card :=
  (card_sq_le_image_mul_samePairs A f).trans
    (Nat.mul_le_mul_right _ (Finset.card_le_card (Finset.image_subset_image hAS)))

/-- A map with bounded fibers gives the standard product cardinality bound. -/
theorem card_le_image_mul_of_fiber_le [DecidableEq β] (F : Finset α) (f : α → β) (D : ℕ)
    (h : ∀ b ∈ F.image f, (fiber F f b).card ≤ D) :
    F.card ≤ (F.image f).card * D := by
  calc
    F.card = ∑ b ∈ F.image f, (fiber F f b).card := card_eq_sum_card_fiber F f
    _ ≤ ∑ _b ∈ F.image f, D := Finset.sum_le_sum h
    _ = _ := by simp

/-- Weighted fiber counting avoids division and remains valid for empty sets. -/
theorem card_mul_le_image_mul [DecidableEq β] (F : Finset α) (f : α → β) (L D : ℕ)
    (h : ∀ b ∈ F.image f, (fiber F f b).card * L ≤ D) :
    F.card * L ≤ (F.image f).card * D := by
  calc
    F.card * L = (∑ b ∈ F.image f, (fiber F f b).card) * L :=
      congrArg (fun k ↦ k * L) (card_eq_sum_card_fiber F f)
    _ = ∑ b ∈ F.image f, (fiber F f b).card * L := Finset.sum_mul _ _ _
    _ ≤ ∑ _b ∈ F.image f, D := Finset.sum_le_sum h
    _ = _ := by simp

end
end Erdos539Geometry
