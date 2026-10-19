/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.LayerCounting

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical

/-- Quantitative closure under an ordered layer product. The bound is
independent of the number of layers and of their individual sizes. -/
theorem ordered_layer_bound {ι κ τ : Type*} [LinearOrder τ]
    {L : Finset τ} (hL : L.Nonempty) {A : τ → Finset (ι → ℝ)} {B : τ → Finset (κ → ℝ)}
    (hord : IsOrderedLayers L A B) (t : ι) (v : κ)
    (hA : ∀ i ∈ L, (A i).Nonempty) (hB : ∀ i ∈ L, (B i).Nonempty)
    {a b u cA cB : ℝ} (ha : 0 < a) (hb : 0 < b) (ha1 : a ≤ 1)
    (hcA : 0 < cA) (hcB : 0 < cB) (hcA1 : cA ≤ 1) (hcB1 : cB ≤ 1)
    (hua : u ≤ a) (hub : u ≤ b) (hu : u ≤ (a + b) / (1 + a + b))
    (hAbound : ∀ i ∈ L, cA * ((A i).card : ℝ) ^ a ≤ maxFan (A i))
    (hBbound : ∀ i ∈ L, cB * ((B i).card : ℝ) ^ b ≤ maxFan (B i)) :
    (cA * cB / 4) * ((orderedLayerProduct L A B).card : ℝ) ^ u ≤
      maxFan (orderedLayerProduct L A B) := by
  classical
  let S := orderedLayerProduct L A B
  let q : ℝ := maxFan S
  let c := cA * cB
  have hc : 0 < c := mul_pos hcA hcB
  have hc1 : c ≤ 1 := by
    dsimp only [c]
    nlinarith [mul_nonneg hcA.le (sub_nonneg.mpr hcB1)]
  have hL' := hL
  obtain ⟨i, hi⟩ := hL
  obtain ⟨x, hx⟩ := hA i hi
  obtain ⟨y, hy⟩ := hB i hi
  have hS : S.Nonempty := ⟨Sum.elim x y,
    mem_orderedLayerProduct.mpr ⟨i, hi, mem_coordinateProduct.mpr ⟨x, hx, y, hy, rfl⟩⟩⟩
  have hq : 0 < q := by
    dsimp only [q]
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxFan hS))
  have hQ : 0 ≤ q / c := (div_pos hq hc).le
  have hconstraint (j : τ) (hj : j ∈ L) :
      ((A j).card : ℝ) ^ a * ((B j).card : ℝ) ^ b ≤ q / c := by
    have hf := maxFan_orderedLayerProduct_ge hord t v hA hB hj
    have hf' : (maxFan (A j) : ℝ) * maxFan (B j) ≤ q := by
      dsimp only [q]
      exact_mod_cast (show maxFan (A j) * maxFan (B j) ≤ maxFan S by dsimp only [S]; omega)
    apply (le_div_iff₀ hc).mpr
    calc
      _ = (cA * ((A j).card : ℝ) ^ a) * (cB * ((B j).card : ℝ) ^ b) := by dsimp only [c]; ring
      _ ≤ (maxFan (A j) : ℝ) * maxFan (B j) :=
        mul_le_mul (hAbound j hj) (hBbound j hj)
          (mul_nonneg hcB.le (Real.rpow_nonneg (Nat.cast_nonneg _) b)) (Nat.cast_nonneg _)
      _ ≤ q := hf'
  let lo := L.min' hL'
  let hi' := L.max' hL'
  have hlo : lo ∈ L := Finset.min'_mem L hL'
  have hhi : hi' ∈ L := Finset.max'_mem L hL'
  have hleft : ∑ j ∈ L.filter (fun j ↦ lo < j), ((A j).card : ℝ) ≤ q := by
    dsimp only [q]
    have h := maxFan_orderedLayerProduct_ge hord t v hA hB hlo
    exact_mod_cast (show ∑ j ∈ L.filter (fun j ↦ lo < j), (A j).card ≤ maxFan S by dsimp only [S]; omega)
  have hright : ∑ j ∈ L.filter (fun j ↦ j < hi'), ((B j).card : ℝ) ≤ q := by
    dsimp only [q]
    have h := maxFan_orderedLayerProduct_ge hord t v hA hB hhi
    exact_mod_cast (show ∑ j ∈ L.filter (fun j ↦ j < hi'), (B j).card ≤ maxFan S by dsimp only [S]; omega)
  have hcount := layer_sum_bound L (fun j ↦ ((A j).card : ℝ)) (fun j ↦ ((B j).card : ℝ)) hlo hhi
    (fun j hj ↦ Finset.min'_le L j hj) (fun j hj ↦ Finset.le_max' L j hj)
    (Real.rpow_nonneg hQ (1 / (a + b))) (Real.rpow_nonneg hQ (1 / min a b))
    (fun _ _ ↦ Nat.cast_nonneg _) (fun _ _ ↦ Nat.cast_nonneg _)
    (fun j hj ↦ layer_endpoint_bound
      (show (1 : ℝ) ≤ (A j).card by exact_mod_cast (show 1 ≤ (A j).card from (hA j hj).card_pos))
      (show (1 : ℝ) ≤ (B j).card by exact_mod_cast (show 1 ≤ (B j).card from (hB j hj).card_pos)) ha hb hQ (hconstraint j hj))
    (fun j hj ↦ layer_interior_bound (Nat.cast_nonneg _) (Nat.cast_nonneg _) ha hb hQ (hconstraint j hj))
    hleft hright
  have hcard : (S.card : ℝ) = ∑ j ∈ L, ((A j).card : ℝ) * (B j).card := by
    exact_mod_cast orderedLayerProduct_card hord t
  rw [← hcard] at hcount
  exact ordered_layer_scalar_bound (by exact_mod_cast hS.card_pos) hq hc hc1 ha hb ha1 hua hub hu hcount

end
end Erdos539Geometry
