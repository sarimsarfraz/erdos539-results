/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FanTranslations
import Erdos539.GluingLayers
import Erdos539.LayerSharpness

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

/-- The two outside-level contributions together count every level except the anchor's. -/
theorem range_outside_sum {K i : ℕ} (hi : i < K) (N : ℕ) :
    (∑ _j ∈ (Finset.range K).filter (fun j ↦ i < j), N) +
      (∑ _j ∈ (Finset.range K).filter (fun j ↦ j < i), N) = (K - 1) * N := by
  have hd : Disjoint ((Finset.range K).filter (fun j ↦ i < j))
      ((Finset.range K).filter (fun j ↦ j < i)) := by
    apply Finset.disjoint_left.mpr
    intro j hj hk
    have := (Finset.mem_filter.mp hj).2
    have := (Finset.mem_filter.mp hk).2
    omega
  have he : (Finset.range K).filter (fun j ↦ i < j) ∪
      (Finset.range K).filter (fun j ↦ j < i) = (Finset.range K).erase i := by
    ext j
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_erase]
    omega
  rw [← Finset.sum_union hd, he]
  simp [Finset.card_erase_of_mem (Finset.mem_range.mpr hi)]

/-- Exact maximum fan of a symmetric separated gluing. -/
theorem maxFan_symmetric_gluing {ι : Type} {F : Finset (ι → ℤ)}
    (hF : F.Nonempty) {K : ℕ} (hK : 0 < K) {M : ℤ} (hM : 0 < M)
    (hgap : HasCoordinateGap F M) (i : ι) :
    maxFan (integerRealSet (gluing F F K M)) =
      maxFan (integerRealSet F) ^ 2 + (K - 1) * F.card := by
  have hord := gluing_isOrderedLayers K hM hgap hgap
  have hA (j : ℕ) (_ : j ∈ Finset.range K) : (glueLeftLayer F M j).Nonempty :=
    translateRealSet_nonempty (integerRealSet_nonempty hF) _
  have hB (j : ℕ) (_ : j ∈ Finset.range K) : (glueRightLayer F M j).Nonempty :=
    translateRealSet_nonempty (integerRealSet_nonempty hF) _
  have hsum (j : ℕ) (hj : j ∈ Finset.range K) :
      (∑ k ∈ (Finset.range K).filter (fun k ↦ j < k), (glueLeftLayer F M k).card) +
      (∑ k ∈ (Finset.range K).filter (fun k ↦ k < j), (glueRightLayer F M k).card) =
        (K - 1) * F.card := by
    simpa only [glueLeftLayer, glueRightLayer, translateRealSet_card, integerRealSet_card]
      using range_outside_sum (Finset.mem_range.mp hj) F.card
  rw [gluing_real_eq_layers]
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro a ha
    obtain ⟨j, hj, ha⟩ := mem_orderedLayerProduct.mp ha
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_coordinateProduct.mp ha
    rw [ordered_layer_fan_card hord i i hA hB hj hx hy, add_assoc, hsum j hj]
    apply Nat.add_le_add_right
    have hx' := card_fan_le_maxFan hx
    have hy' := card_fan_le_maxFan hy
    simp only [glueLeftLayer, glueRightLayer, maxFan_translateRealSet] at hx' hy'
    simpa only [pow_two] using Nat.mul_le_mul hx' hy'
  · have hl := maxFan_orderedLayerProduct_ge hord i i hA hB (Finset.mem_range.mpr hK)
    rw [add_assoc, hsum 0 (Finset.mem_range.mpr hK)] at hl
    simpa only [glueLeftLayer, glueRightLayer, maxFan_translateRealSet, pow_two] using hl

end
end Erdos539Geometry
