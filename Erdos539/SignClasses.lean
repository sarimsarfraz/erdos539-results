/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SliceBounds
import Erdos539.SignMasks

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι : Type*} [Fintype ι]

/-- In dimension three, at least one orientation of each pair has two
nonnegative coordinates. Equal coordinates are retained in both masks. -/
theorem two_le_mask_or_reverse (hd : Fintype.card ι = 3) (x y : ι → ℝ) :
    2 ≤ (freeMask ∅ x y).card ∨ 2 ≤ (freeMask ∅ y x).card := by
  classical
  have hc := Finset.card_le_card (complement_freeMask_subset_reverse ∅ x y)
  have hs := Finset.card_sdiff_of_subset (freeMask_subset ∅ x y)
  simp only [Finset.sdiff_empty, Finset.card_univ, hd] at hc hs
  omega

/-- Finite averaging with a representative in the maximizing fiber. -/
theorem exists_large_fiber {α β : Type*} [DecidableEq β]
    (F : Finset α) (hF : F.Nonempty) (f : α → β) :
    ∃ x ∈ F, F.card ≤ (F.image f).card * (fiber F f (f x)).card := by
  classical
  obtain ⟨x, hx, hmax⟩ := F.exists_max_image (fun x ↦ (fiber F f (f x)).card) hF
  refine ⟨x, hx, card_le_image_mul_of_fiber_le F f _ ?_⟩
  intro b hb
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
  exact hmax y hy

/-- A three-dimensional set has a large sign class at an anchor in the set.
The slightly loose factor sixteen keeps all eight masks in the counting. -/
theorem exists_large_three_dimensional_sign_class (hd : Fintype.card ι = 3)
    {F : Finset (ι → ℝ)} (hF : F.Nonempty) :
    ∃ a ∈ F, ∃ P : Finset ι, ∃ E : Finset (ι → ℝ),
      E ⊆ F ∧ E.Nonempty ∧ F.card ≤ 16 * E.card ∧ 2 ≤ P.card ∧
      (∀ x ∈ E, freeMask ∅ x a = P) := by
  classical
  let G := (F ×ˢ F).filter (fun p ↦ 2 ≤ (freeMask ∅ p.1 p.2).card)
  have hG (p : (ι → ℝ) × (ι → ℝ)) :
      p ∈ G ↔ p.1 ∈ F ∧ p.2 ∈ F ∧ 2 ≤ (freeMask ∅ p.1 p.2).card := by
    simp only [G, Finset.mem_filter, Finset.mem_product, and_assoc]
  have hcover : F ×ˢ F ⊆ G ∪ G.image Prod.swap := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    rcases two_le_mask_or_reverse hd p.1 p.2 with h | h
    · exact Finset.mem_union_left _ ((hG p).mpr ⟨hp1, hp2, h⟩)
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨p.swap, (hG p.swap).mpr ⟨hp2, hp1, h⟩, Prod.swap_swap p⟩
  have hcount : F.card * F.card ≤ 2 * G.card := by
    have hc := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
    have hi : (G.image Prod.swap).card ≤ G.card := Finset.card_image_le
    rw [Finset.card_product] at hc
    omega
  let R := fun a : ι → ℝ ↦ F.filter (fun x ↦ 2 ≤ (freeMask ∅ x a).card)
  obtain ⟨a, ha, hmax⟩ := F.exists_max_image (fun a ↦ (R a).card) hF
  have hfiber (b : ι → ℝ) : (fiber G Prod.snd b).card ≤ (R b).card := by
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro p hp
      obtain ⟨hg, he⟩ := mem_fiber.mp hp
      have hd := (hG p).mp hg
      exact Finset.mem_filter.mpr ⟨hd.1, he ▸ hd.2.2⟩
    · intro p hp q hq he
      exact Prod.ext he ((mem_fiber.mp hp).2.trans (mem_fiber.mp hq).2.symm)
  have hmaps : (G : Set ((ι → ℝ) × (ι → ℝ))).MapsTo Prod.snd F :=
    fun p hp ↦ ((hG p).mp hp).2.1
  have hcount' : G.card ≤ F.card * (R a).card := by
    calc
      G.card = ∑ b ∈ F, (fiber G Prod.snd b).card := card_eq_sum_card_parent G Prod.snd F hmaps
      _ ≤ ∑ _b ∈ F, (R a).card := Finset.sum_le_sum (fun b hb ↦ (hfiber b).trans (hmax b hb))
      _ = _ := by simp
  have hrow : F.card ≤ 2 * (R a).card := by
    have := hF.card_pos
    nlinarith
  have hR : (R a).Nonempty := Finset.card_pos.mp (by have := hF.card_pos; omega)
  obtain ⟨x, hx, hclass⟩ := exists_large_fiber (R a) hR (fun x ↦ freeMask ∅ x a)
  let P := freeMask ∅ x a
  let E := fiber (R a) (fun x ↦ freeMask ∅ x a) P
  have hmaskcount : ((R a).image (fun x ↦ freeMask ∅ x a)).card ≤ 8 := by
    have hc := Finset.card_le_univ ((R a).image (fun x ↦ freeMask ∅ x a))
    simpa only [Fintype.card_finset, hd] using hc
  have hclass' : (R a).card ≤ 8 * E.card :=
    hclass.trans (Nat.mul_le_mul_right _ hmaskcount)
  refine ⟨a, ha, P, E, ?_, ?_, by omega, (Finset.mem_filter.mp hx).2, ?_⟩
  · intro y hy
    exact (Finset.mem_filter.mp (mem_fiber.mp hy).1).1
  · exact ⟨x, mem_fiber.mpr ⟨hx, rfl⟩⟩
  · intro y hy
    exact (mem_fiber.mp hy).2

/-- On a fixed nonnegative sign block, the anchor's positive differences
recover every projected coordinate value. -/
theorem projection_sign_class_le_maxFan {E F : Finset (ι → ℝ)} (hEF : E ⊆ F)
    {a : ι → ℝ} (ha : a ∈ F) (P : Finset ι)
    (hmask : ∀ x ∈ E, freeMask ∅ x a = P) :
    (projection E P).card ≤ maxFan F := by
  classical
  let recover : (ι → ℝ) → (P → ℝ) := fun z i ↦ z i + a i
  have hsub : projection E P ⊆ (fan F a).image recover := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    apply Finset.mem_image.mpr
    refine ⟨pdiff x a, mem_fan.mpr ⟨x, hEF hx, rfl⟩, ?_⟩
    funext i
    have hm : i.val ∈ freeMask ∅ x a := by rw [hmask x hx]; exact i.property
    have hp := (mem_freeMask.mp hm).2
    change max (x i.val - a i.val) 0 + a i.val = x i.val
    rw [max_eq_left (sub_nonneg.mpr hp)]
    ring
  exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (card_fan_le_maxFan ha))

end
end Erdos539Geometry
