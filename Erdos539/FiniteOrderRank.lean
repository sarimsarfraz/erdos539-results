/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.AnchoredJoin

namespace Erdos539Geometry
noncomputable section
open scoped Classical

/-- Real-valued rank in the finite set of values that actually occur. -/
def finiteOrderRank {α : Type*} [LinearOrder α] (A : Finset α) (x : α) : ℝ :=
  ((A.filter (fun y ↦ y < x)).card : ℝ)

theorem finiteOrderRank_monotone {α : Type*} [LinearOrder α] (A : Finset α) :
    Monotone (finiteOrderRank A) := by
  intro x y hxy
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro z hz
  obtain ⟨hzA, hzx⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨hzA, hzx.trans_le hxy⟩

theorem finiteOrderRank_strictMonoOn {α : Type*} [LinearOrder α] (A : Finset α) :
    StrictMonoOn (finiteOrderRank A) A := by
  intro x hx y _hy hxy
  apply Nat.cast_lt.mpr
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨hzA, hzx⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hzA, hzx.trans hxy⟩
  · intro he
    have hx' : x ∈ A.filter (fun z ↦ z < y) := Finset.mem_filter.mpr ⟨hx, hxy⟩
    rw [← he] at hx'
    exact (lt_irrefl x) (Finset.mem_filter.mp hx').2

variable {ι : Type*} {α : ι → Type*} [∀ i, LinearOrder (α i)]

def coordinateValues (S : Finset (∀ i, α i)) (i : ι) : Finset (α i) := S.image (fun x ↦ x i)

def coordinateRanks (S : Finset (∀ i, α i)) : (∀ i, α i) → (ι → ℝ) :=
  coordinateMap (fun i ↦ finiteOrderRank (coordinateValues S i))

theorem coordinateRanks_injOn_values (S : Finset (∀ i, α i)) :
    Set.InjOn (coordinateRanks S) {x | ∀ i, x i ∈ coordinateValues S i} := by
  intro x hx y hy h
  funext i
  exact (finiteOrderRank_strictMonoOn (coordinateValues S i)).injOn
    (hx i) (hy i) (congrFun h i)

theorem coordinateRanks_injOn (S : Finset (∀ i, α i)) : Set.InjOn (coordinateRanks S) S := by
  intro x hx y hy h
  exact coordinateRanks_injOn_values S (fun i ↦ Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    (fun i ↦ Finset.mem_image.mpr ⟨y, hy, rfl⟩) h

theorem coordinateRanks_card (S : Finset (∀ i, α i)) : (S.image (coordinateRanks S)).card = S.card :=
  Finset.card_image_iff.mpr (coordinateRanks_injOn S)

theorem joinFan_values {S : Finset (∀ i, α i)} {a x : ∀ i, α i} (ha : a ∈ S)
    (hx : x ∈ joinFan S a) (i : ι) : x i ∈ coordinateValues S i := by
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  rcases le_total (y i) (a i) with h | h
  · change max (y i) (a i) ∈ coordinateValues S i
    rw [max_eq_right h]
    exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  · change max (y i) (a i) ∈ coordinateValues S i
    rw [max_eq_left h]
    exact Finset.mem_image.mpr ⟨y, hy, rfl⟩

/-- Finite coordinate ranks preserve each actual anchored join count. -/
theorem joinFan_coordinateRanks_card {S : Finset (∀ i, α i)} {a : ∀ i, α i} (ha : a ∈ S) :
    (joinFan (S.image (coordinateRanks S)) (coordinateRanks S a)).card = (joinFan S a).card := by
  rw [coordinateRanks, joinFan_coordinateMap _ (fun i ↦ finiteOrderRank_monotone (coordinateValues S i))]
  apply Finset.card_image_iff.mpr
  intro x hx y hy h
  exact coordinateRanks_injOn_values S (joinFan_values ha hx) (joinFan_values ha hy) h

theorem maxJoinFan_coordinateRanks (S : Finset (∀ i, α i)) :
    maxJoinFan (S.image (coordinateRanks S)) = maxJoinFan S := by
  unfold maxJoinFan
  rw [Finset.sup_image]
  apply Finset.sup_congr rfl
  intro a ha
  exact joinFan_coordinateRanks_card ha

end
end Erdos539Geometry
