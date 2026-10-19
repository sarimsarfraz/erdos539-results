/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GluingMaxFan

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

/-- Equal layer sizes suffice for the outside-anchor contribution;
the two layer shapes need not coincide. -/
theorem maxFan_gluing_equal_card {ι κ : Type} {F : Finset (ι → ℤ)} {G : Finset (κ → ℤ)}
    (hF : F.Nonempty) (hG : G.Nonempty) (hcard : F.card = G.card)
    (K : ℕ) {M : ℤ} (hM : 0 < M) (hgapF : HasCoordinateGap F M) (hgapG : HasCoordinateGap G M)
    (i : ι) (j : κ) :
    maxFan (integerRealSet (gluing F G K M)) ≤
      maxFan (integerRealSet F) * maxFan (integerRealSet G) + (K - 1) * F.card := by
  have hord := gluing_isOrderedLayers K hM hgapF hgapG
  have hA (k : ℕ) (_ : k ∈ Finset.range K) : (glueLeftLayer F M k).Nonempty :=
    translateRealSet_nonempty (integerRealSet_nonempty hF) _
  have hB (k : ℕ) (_ : k ∈ Finset.range K) : (glueRightLayer G M k).Nonempty :=
    translateRealSet_nonempty (integerRealSet_nonempty hG) _
  have hsum (k : ℕ) (hk : k ∈ Finset.range K) :
      (∑ l ∈ (Finset.range K).filter (fun l ↦ k < l), (glueLeftLayer F M l).card) +
      (∑ l ∈ (Finset.range K).filter (fun l ↦ l < k), (glueRightLayer G M l).card) =
        (K - 1) * F.card := by
    simpa only [glueLeftLayer, glueRightLayer, translateRealSet_card, integerRealSet_card, ← hcard]
      using range_outside_sum (Finset.mem_range.mp hk) F.card
  rw [gluing_real_eq_layers]
  apply Finset.sup_le
  intro a ha
  obtain ⟨k, hk, ha⟩ := mem_orderedLayerProduct.mp ha
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_coordinateProduct.mp ha
  rw [ordered_layer_fan_card hord i j hA hB hk hx hy, add_assoc, hsum k hk]
  apply Nat.add_le_add_right
  have hx' := card_fan_le_maxFan hx
  have hy' := card_fan_le_maxFan hy
  simp only [glueLeftLayer, glueRightLayer, maxFan_translateRealSet] at hx' hy'
  exact Nat.mul_le_mul hx' hy'

end
end Erdos539Geometry
