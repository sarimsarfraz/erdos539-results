/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.Fans

namespace Erdos539Geometry
noncomputable section
open scoped Classical
variable {ι : Type*} {α β : ι → Type*}
variable [∀ i, LinearOrder (α i)] [∀ i, LinearOrder (β i)]

def anchoredJoin (x a : ∀ i, α i) : ∀ i, α i := fun i ↦ max (x i) (a i)

def joinFan (S : Finset (∀ i, α i)) (a : ∀ i, α i) : Finset (∀ i, α i) :=
  S.image (fun x ↦ anchoredJoin x a)

def maxJoinFan (S : Finset (∀ i, α i)) : ℕ := S.sup (fun a ↦ (joinFan S a).card)

def coordinateMap (f : ∀ i, α i → β i) (x : ∀ i, α i) : ∀ i, β i := fun i ↦ f i (x i)

omit [∀ i, LinearOrder (α i)] [∀ i, LinearOrder (β i)] in
theorem coordinateMap_injective (f : ∀ i, α i → β i) (hf : ∀ i, Function.Injective (f i)) :
    Function.Injective (coordinateMap f) := by
  intro x y h
  funext i
  exact hf i (congrFun h i)

theorem coordinateMap_anchoredJoin (f : ∀ i, α i → β i) (hf : ∀ i, Monotone (f i))
    (x a : ∀ i, α i) :
    coordinateMap f (anchoredJoin x a) = anchoredJoin (coordinateMap f x) (coordinateMap f a) := by
  funext i
  exact (hf i).map_max

theorem joinFan_coordinateMap (f : ∀ i, α i → β i) (hf : ∀ i, Monotone (f i))
    (S : Finset (∀ i, α i)) (a : ∀ i, α i) :
    joinFan (S.image (coordinateMap f)) (coordinateMap f a) = (joinFan S a).image (coordinateMap f) := by
  simp only [joinFan, Finset.image_image]
  congr 1
  funext x
  exact (coordinateMap_anchoredJoin f hf x a).symm

/-- Strictly increasing coordinate relabellings preserve each anchored
join count; they need not preserve the full positive-difference palette. -/
theorem joinFan_card_strictMono (f : ∀ i, α i → β i) (hf : ∀ i, StrictMono (f i))
    (S : Finset (∀ i, α i)) (a : ∀ i, α i) :
    (joinFan (S.image (coordinateMap f)) (coordinateMap f a)).card = (joinFan S a).card := by
  rw [joinFan_coordinateMap f (fun i ↦ (hf i).monotone)]
  exact Finset.card_image_of_injective _ (coordinateMap_injective f (fun i ↦ (hf i).injective))

theorem maxJoinFan_strictMono (f : ∀ i, α i → β i) (hf : ∀ i, StrictMono (f i))
    (S : Finset (∀ i, α i)) : maxJoinFan (S.image (coordinateMap f)) = maxJoinFan S := by
  unfold maxJoinFan
  rw [Finset.sup_image]
  apply Finset.sup_congr rfl
  intro a _
  exact joinFan_card_strictMono f hf S a

theorem anchoredJoin_real (x a : ι → ℝ) : anchoredJoin x a = a + pdiff x a := by
  funext i
  simp only [anchoredJoin, Pi.add_apply, pdiff]
  rcases le_total (x i) (a i) with h | h
  · rw [max_eq_right h, max_eq_right (sub_nonpos.mpr h), add_zero]
  · rw [max_eq_left h, max_eq_left (sub_nonneg.mpr h)]
    linarith

theorem joinFan_real (S : Finset (ι → ℝ)) (a : ι → ℝ) :
    joinFan S a = (fan S a).image (fun v ↦ a + v) := by
  simp only [joinFan, fan, Finset.image_image]
  congr 1
  funext x
  exact anchoredJoin_real x a

theorem joinFan_real_card (S : Finset (ι → ℝ)) (a : ι → ℝ) :
    (joinFan S a).card = (fan S a).card := by
  rw [joinFan_real]
  exact Finset.card_image_of_injective _ (fun _ _ h ↦ add_left_cancel h)

theorem maxJoinFan_real (S : Finset (ι → ℝ)) : maxJoinFan S = maxFan S := by
  unfold maxJoinFan maxFan
  apply Finset.sup_congr rfl
  intro a _
  exact joinFan_real_card S a

end
end Erdos539Geometry
