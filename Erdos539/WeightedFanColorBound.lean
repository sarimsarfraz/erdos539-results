/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FanColorWeights

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {ι : Type*}
local instance weightedFanColorDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

theorem transferAmplitude_le_encoded {S : Finset (ι → ℝ)} (f g : S → ℝ)
    (hg : ∀ a, 0 < g a) (t : (S × S) × (S × S))
    (ht : t.1.1.val + t.1.2.val = t.2.1.val + t.2.2.val) :
    transferAmplitude S f g t ^ 2 ≤ encodedFanWeight S f g (quadrupleFanEncoding S t) := by
  rw [transferAmplitude_square S f g hg, if_pos ht, encodedFanWeight,
    if_pos (quadrupleFanEncoding_disjoint t ht)]
  let z := positiveDifferenceChannel S t.2.1 t.1.1
  let w := positiveDifferenceChannel S t.2.2 t.1.2
  have ha := (channelMaxWeight_spec (positiveDifferenceChannel S) g hg t.2.1
    (mem_channelOutputs (positiveDifferenceChannel S) t.2.1 t.1.1)).2 t.1.1 rfl
  have hb := (channelMaxWeight_spec (positiveDifferenceChannel S) g hg t.2.2
    (mem_channelOutputs (positiveDifferenceChannel S) t.2.2 t.1.2)).2 t.1.2 rfl
  have hmax : g t.1.1 * g t.1.2 ≤
      channelMaxWeight (positiveDifferenceChannel S) g t.2.1 z *
        channelMaxWeight (positiveDifferenceChannel S) g t.2.2 w :=
    mul_le_mul ha hb (hg t.1.2).le ((hg t.1.1).le.trans ha)
  have hc : 0 ≤ (f t.2.1 ^ 2 / g t.2.1) * (f t.2.2 ^ 2 / g t.2.2) :=
    mul_nonneg (div_nonneg (sq_nonneg _) (hg _).le) (div_nonneg (sq_nonneg _) (hg _).le)
  have hh := mul_le_mul_of_nonneg_left hmax hc
  change _ ≤ ((f t.2.1 ^ 2 / g t.2.1) * channelMaxWeight (positiveDifferenceChannel S) g t.2.1 z) *
    ((f t.2.2 ^ 2 / g t.2.2) * channelMaxWeight (positiveDifferenceChannel S) g t.2.2 w)
  convert hh using 1 <;> ring

/-- The actual additive encoding proves the intermediate disjoint-color
bound in the source, with no assumption on the sign of f. -/
theorem weightedTransferSum_le_disjointFanColorSum {S : Finset (ι → ℝ)} (hS : S.Nonempty)
    (f g : S → ℝ) (hg : ∀ a, 0 < g a) :
    weightedTransferSum S f g ≤ disjointFanColorSum S f g := by
  let T : Finset ((S × S) × (S × S)) := Finset.univ.filter
    (fun t ↦ t.1.1.val + t.1.2.val = t.2.1.val + t.2.2.val)
  have he : weightedTransferSum S f g = ∑ t : (S × S) × (S × S), transferAmplitude S f g t ^ 2 := by
    simp only [transferAmplitude_square S f g hg, Fintype.sum_prod_type, weightedTransferSum]
  have heT : (∑ t ∈ T, transferAmplitude S f g t ^ 2) = ∑ t, transferAmplitude S f g t ^ 2 := by
    apply Finset.sum_subset (Finset.subset_univ T)
    intro t _ ht
    have hrel : t.1.1.val + t.1.2.val ≠ t.2.1.val + t.2.2.val := by
      simpa only [T, Finset.mem_filter, Finset.mem_univ, true_and] using ht
    simp [transferAmplitude, hrel]
  rw [he, ← heT, ← encodedFanWeight_sum S f g]
  calc
    _ ≤ ∑ t ∈ T, encodedFanWeight S f g (quadrupleFanEncoding S t) := by
      apply Finset.sum_le_sum
      intro t ht
      exact transferAmplitude_le_encoded f g hg t (Finset.mem_filter.mp ht).2
    _ = ∑ y ∈ T.image (quadrupleFanEncoding S), encodedFanWeight S f g y := by
      rw [Finset.sum_image]
      intro u hu v hv heq
      exact quadrupleFanEncoding_injective_additive hS u v
        (Finset.mem_filter.mp hu).2 (Finset.mem_filter.mp hv).2 heq
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun y _ _ ↦ encodedFanWeight_nonneg S f g hg y)

theorem disjointFanColorSum_le_square (S : Finset (ι → ℝ)) (f g : S → ℝ)
    (hg : ∀ a, 0 < g a) :
    disjointFanColorSum S f g ≤ (∑ z, fanColorWeight S f g z) ^ 2 := by
  rw [pow_two, Finset.sum_mul]
  simp only [Finset.mul_sum]
  unfold disjointFanColorSum
  apply Finset.sum_le_sum
  intro z _
  apply Finset.sum_le_sum
  intro w _
  split_ifs
  · rfl
  · exact mul_nonneg (fanColorWeight_nonneg S f g hg z) (fanColorWeight_nonneg S f g hg w)

/-- The complete E <= S1 <= disjoint-color sum <= Q^2 chain. -/
theorem weighted_fan_color_chain {S : Finset (ι → ℝ)} (hS : S.Nonempty)
    (f g : S → ℝ) (hg : ∀ a, 0 < g a) :
    weightedGibbsPartition S f ≤ weightedTransferSum S f g ∧
    weightedTransferSum S f g ≤ disjointFanColorSum S f g ∧
    disjointFanColorSum S f g ≤
      (∑ c, f c ^ 2 * channelWeightRatio (positiveDifferenceChannel S) g c) ^ 2 := by
  refine ⟨weightedEnergy_le_transfer S f g hg, weightedTransferSum_le_disjointFanColorSum hS f g hg, ?_⟩
  rw [← fanColorWeight_sum S f g]
  exact disjointFanColorSum_le_square S f g hg

end
end Erdos539Geometry
