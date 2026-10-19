/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.WeightedFanColorBound
import Erdos539.ReferenceUniformRoot

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

theorem channelWeightRatio_one {α β : Type*} [Fintype α] [Fintype β]
    (channel : α → α → β) (a : α) :
    channelWeightRatio channel (fun _ ↦ 1) a = (channelOutputs channel a).card := by
  simp [channelWeightRatio, channelWeightSum, channelMaxWeight, channelReference]

variable {ι : Type*}
local instance countingFanBoundDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

theorem channelOutputs_positiveDifference (S : Finset (ι → ℝ)) (a : S) :
    channelOutputs (positiveDifferenceChannel S) a = fanOutputs S a := by
  ext z
  simp only [channelOutputs, fanOutputs, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩
    exact mem_fan.mpr ⟨x.val, x.property, rfl⟩
  · intro hz
    obtain ⟨x, hx, h⟩ := mem_fan.mp hz
    exact ⟨⟨x, hx⟩, Subtype.ext h⟩

theorem weightedGibbsPartition_one (S : Finset (ι → ℝ)) :
    weightedGibbsPartition S (fun _ ↦ 1) = countingEnergy S := by
  unfold weightedGibbsPartition countingEnergy
  apply weightedEnergy_congr
  intro x hx
  simp [extendWeight, hx]

/-- The sharper counting baseline uses the sum of actual fan sizes. -/
theorem countingEnergy_le_fan_sum_square {S : Finset (ι → ℝ)} (hS : S.Nonempty) :
    countingEnergy S ≤ (∑ c : S, ((fan S c.val).card : ℝ)) ^ 2 := by
  have h := weighted_fan_color_chain hS (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ by norm_num)
  have hh := h.1.trans (h.2.1.trans h.2.2)
  simpa only [weightedGibbsPartition_one, one_pow, one_mul, channelWeightRatio_one,
    channelOutputs_positiveDifference, fanOutputs_card] using hh

theorem countingEnergy_le_card_sq_mul_maxFan_sq {S : Finset (ι → ℝ)} (hS : S.Nonempty) :
    countingEnergy S ≤ (S.card : ℝ) ^ 2 * (maxFan S : ℝ) ^ 2 := by
  have h := countingEnergy_le_fan_sum_square hS
  have hs : (∑ c : S, ((fan S c.val).card : ℝ)) ≤ (S.card : ℝ) * maxFan S := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset S)) (fun c _ ↦
      (show ((fan S c.val).card : ℝ) ≤ maxFan S by exact_mod_cast card_fan_le_maxFan c.property))
    simpa using hh
  have hn : 0 ≤ ∑ c : S, ((fan S c.val).card : ℝ) := Finset.sum_nonneg (fun _ _ ↦ Nat.cast_nonneg _)
  nlinarith

end
end Erdos539Geometry
