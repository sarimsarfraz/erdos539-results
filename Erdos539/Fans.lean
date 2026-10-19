/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PositiveDiff
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Tactic.Linarith

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι κ : Type*}

/-- Positive differences with one fixed anchor. -/
def fan (F : Finset (ι → ℝ)) (a : ι → ℝ) : Finset (ι → ℝ) :=
  F.image (fun x ↦ pdiff x a)

/-- Maximum forward fan over anchors in the set; zero for the empty set. -/
def maxFan (F : Finset (ι → ℝ)) : ℕ := F.sup (fun a ↦ (fan F a).card)

@[simp] theorem mem_fan {F : Finset (ι → ℝ)} {a u : ι → ℝ} :
    u ∈ fan F a ↔ ∃ x ∈ F, pdiff x a = u := Finset.mem_image

theorem fan_mono {F G : Finset (ι → ℝ)} (h : F ⊆ G) (a : ι → ℝ) :
    fan F a ⊆ fan G a := Finset.image_subset_image h

theorem fan_subset_posDiff {F : Finset (ι → ℝ)} {a : ι → ℝ} (ha : a ∈ F) :
    fan F a ⊆ posDiff F := by
  intro u hu
  obtain ⟨x, hx, rfl⟩ := mem_fan.mp hu
  exact mem_posDiff.mpr ⟨x, hx, a, ha, rfl⟩

theorem card_fan_le_maxFan {F : Finset (ι → ℝ)} {a : ι → ℝ} (ha : a ∈ F) :
    (fan F a).card ≤ maxFan F := by
  exact Finset.le_sup (f := fun x ↦ (fan F x).card) ha

theorem maxFan_le_card_posDiff (F : Finset (ι → ℝ)) :
    maxFan F ≤ (posDiff F).card := by
  apply Finset.sup_le
  intro a ha
  exact Finset.card_le_card (fan_subset_posDiff ha)

theorem maxFan_mono {F G : Finset (ι → ℝ)} (h : F ⊆ G) :
    maxFan F ≤ maxFan G := by
  apply Finset.sup_le
  intro a ha
  exact (Finset.card_le_card (fan_mono h a)).trans (card_fan_le_maxFan (h ha))

theorem maxFan_le_card (F : Finset (ι → ℝ)) : maxFan F ≤ F.card := by
  apply Finset.sup_le
  intro a _
  exact Finset.card_image_le

@[simp] theorem pdiff_self (x : ι → ℝ) : pdiff x x = 0 := by
  ext i
  simp [pdiff]

theorem one_le_maxFan {F : Finset (ι → ℝ)} (hF : F.Nonempty) : 1 ≤ maxFan F := by
  obtain ⟨a, ha⟩ := hF
  have hzero : (0 : ι → ℝ) ∈ fan F a := mem_fan.mpr ⟨a, ha, pdiff_self a⟩
  exact (Finset.card_pos.mpr ⟨0, hzero⟩).trans_le (card_fan_le_maxFan ha)

/-- A difference is recovered from its two positive parts. -/
theorem pdiff_sub_reverse (x y : ι → ℝ) : pdiff x y - pdiff y x = x - y := by
  ext i
  change max (x i - y i) 0 - max (y i - x i) 0 = x i - y i
  simpa only [neg_sub] using max_zero_sub_max_neg_zero_eq_self (x i - y i)

theorem anchored_split_injective (a : ι → ℝ) :
    Function.Injective (fun x : ι → ℝ ↦ (pdiff x a, pdiff a x)) := by
  intro x y h
  have hp : pdiff x a = pdiff y a := congrArg Prod.fst h
  have hn : pdiff a x = pdiff a y := congrArg Prod.snd h
  have hs : x - a = y - a := by rw [← pdiff_sub_reverse x a, hp, hn, pdiff_sub_reverse]
  funext i
  have hi := congrFun hs i
  change x i - a i = y i - a i at hi
  linarith

/-- Every point is encoded by its forward and reverse outputs at any fixed anchor. -/
theorem card_le_forward_mul_reverse (F : Finset (ι → ℝ)) (a : ι → ℝ) :
    F.card ≤ (fan F a).card * (F.image (fun x ↦ pdiff a x)).card := by
  rw [← Finset.card_product]
  apply Finset.card_le_card_of_injOn (fun x ↦ (pdiff x a, pdiff a x))
  · intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx, Finset.mem_image_of_mem _ hx⟩
  · exact (anchored_split_injective a).injOn

theorem fan_image_comp (F : Finset (ι → ℝ)) (a : ι → ℝ) (f : κ → ι) :
    fan (F.image (fun x ↦ x ∘ f)) (a ∘ f) = (fan F a).image (fun x ↦ x ∘ f) := by
  simp only [fan, Finset.image_image]
  rfl

theorem maxFan_image_comp_le (F : Finset (ι → ℝ)) (f : κ → ι) :
    maxFan (F.image (fun x ↦ x ∘ f)) ≤ maxFan F := by
  apply Finset.sup_le
  intro a ha
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
  rw [fan_image_comp]
  exact Finset.card_image_le.trans (card_fan_le_maxFan hx)

/-- An anchor minimizing one coordinate sees every value of that coordinate. -/
theorem coordinate_card_le_maxFan (F : Finset (ι → ℝ)) (i : ι) :
    (F.image (fun x ↦ x i)).card ≤ maxFan F := by
  by_cases hF : F.Nonempty
  · obtain ⟨a, ha, hmin⟩ := F.exists_min_image (fun x ↦ x i) hF
    have himage : (fan F a).image (fun z ↦ z i + a i) = F.image (fun x ↦ x i) := by
      ext t
      constructor
      · intro ht
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ht
        obtain ⟨x, hx, rfl⟩ := mem_fan.mp hz
        apply Finset.mem_image.mpr
        refine ⟨x, hx, ?_⟩
        dsimp [pdiff]
        rw [max_eq_left (sub_nonneg.mpr (hmin x hx))]
        linarith
      · intro ht
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
        apply Finset.mem_image.mpr
        refine ⟨pdiff x a, mem_fan.mpr ⟨x, hx, rfl⟩, ?_⟩
        dsimp [pdiff]
        rw [max_eq_left (sub_nonneg.mpr (hmin x hx))]
        linarith
    calc
      (F.image (fun x ↦ x i)).card = ((fan F a).image (fun z ↦ z i + a i)).card :=
        congrArg Finset.card himage.symm
      _ ≤ (fan F a).card := Finset.card_image_le
      _ ≤ maxFan F := card_fan_le_maxFan ha
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    simp [he, maxFan]

theorem maxFan_eq_card_one_dimensional [Subsingleton ι] (i : ι)
    (F : Finset (ι → ℝ)) : maxFan F = F.card := by
  apply le_antisymm (maxFan_le_card F)
  have hinj : Function.Injective (fun x : ι → ℝ ↦ x i) := by
    intro x y h
    funext j
    simpa only [Subsingleton.elim j i] using h
  have hcard := Finset.card_image_of_injective F hinj
  exact hcard ▸ coordinate_card_le_maxFan F i

end
end Erdos539Geometry
