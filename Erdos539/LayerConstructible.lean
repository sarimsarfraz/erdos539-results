/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.OrderedLayerBound
import Erdos539.LayerConstants
import Erdos539.SharpExponentMonotonicity
import Erdos539.RealReindex
import Erdos539.SliceBounds

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
universe u

/-- Finite sets generated from one-dimensional sets by ordered layer products
and coordinate relabeling. Factors in a layer can have different construction histories. -/
inductive LayerConstructible : (ι : Type u) → [Fintype ι] → Finset (ι → ℝ) → Prop where
  | line {ι : Type u} [Fintype ι] (F : Finset (ι → ℝ)) (hd : Fintype.card ι = 1) :
      LayerConstructible ι F
  | layers {ι κ τ : Type u} [Fintype ι] [Fintype κ] [LinearOrder τ]
      (L : Finset τ) (hL : L.Nonempty) (A : τ → Finset (ι → ℝ)) (B : τ → Finset (κ → ℝ))
      (hord : IsOrderedLayers L A B)
      (hA : ∀ i ∈ L, (A i).Nonempty) (hB : ∀ i ∈ L, (B i).Nonempty)
      (hCA : ∀ i ∈ L, LayerConstructible ι (A i)) (hCB : ∀ i ∈ L, LayerConstructible κ (B i)) :
      LayerConstructible (ι ⊕ κ) (orderedLayerProduct L A B)
  | reindex {ι κ : Type u} [Fintype ι] [Fintype κ] (e : ι ≃ κ) {F : Finset (ι → ℝ)}
      (h : LayerConstructible ι F) : LayerConstructible κ (reindexRealSet e F)

/-- The complete recursive ordered-layer theorem, including its uniform constant. -/
theorem LayerConstructible.bound {ι : Type u} [Fintype ι] {F : Finset (ι → ℝ)}
    (h : LayerConstructible ι F) :
    0 < Fintype.card ι ∧ layerConstant (Fintype.card ι) *
      (F.card : ℝ) ^ (sharpExponent (Fintype.card ι) : ℝ) ≤ maxFan F := by
  induction h with
  | line F hd =>
    constructor
    · omega
    · rw [hd, layerConstant_one, sharpExponent_one, Rat.cast_one, Real.rpow_one, one_mul,
        one_dimensional_maxFan_eq_card hd]
  | @layers ι κ τ instι instκ instτ L hL A B hord hA hB hCA hCB ihA ihB =>
    obtain ⟨i, hi⟩ := hL
    have hp : 0 < Fintype.card ι := (ihA i hi).1
    have hs : 0 < Fintype.card κ := (ihB i hi).1
    let t : ι := Classical.choice (Fintype.card_pos_iff.mp hp)
    let v : κ := Classical.choice (Fintype.card_pos_iff.mp hs)
    rw [Fintype.card_sum]
    refine ⟨by omega, ?_⟩
    rw [← layerConstant_split]
    have hsplit : (sharpExponent (Fintype.card ι + Fintype.card κ) : ℝ) ≤
        ((sharpExponent (Fintype.card ι) : ℝ) + sharpExponent (Fintype.card κ)) /
          (1 + (sharpExponent (Fintype.card ι) : ℝ) + sharpExponent (Fintype.card κ)) := by
      have h : (sharpExponent (Fintype.card ι + Fintype.card κ) : ℝ) ≤
          (combineExponent (sharpExponent (Fintype.card ι)) (sharpExponent (Fintype.card κ)) : ℝ) := by
        exact_mod_cast sharpExponent_le_split hp hs
      rw [combineExponent] at h
      push_cast at h
      exact h
    exact ordered_layer_bound ⟨i, hi⟩ hord t v hA hB
      (by exact_mod_cast sharpExponent_pos (Fintype.card ι))
      (by exact_mod_cast sharpExponent_pos (Fintype.card κ))
      (by exact_mod_cast (sharpExponent_bounds (Fintype.card ι)).2)
      (layerConstant_pos _) (layerConstant_pos _) (layerConstant_le_one hp) (layerConstant_le_one hs)
      (by exact_mod_cast (sharpExponent_le_parts (p := Fintype.card ι) (s := Fintype.card κ)).1)
      (by exact_mod_cast (sharpExponent_le_parts (p := Fintype.card ι) (s := Fintype.card κ)).2)
      hsplit (fun j hj ↦ (ihA j hj).2) (fun j hj ↦ (ihB j hj).2)
  | reindex e h ih =>
    rw [← Fintype.card_congr e, reindexRealSet_card, maxFan_reindexRealSet]
    exact ih

theorem layerConstant_eq_inv_pow {d : ℕ} (hd : 0 < d) :
    layerConstant d = ((4 : ℝ) ^ (d - 1))⁻¹ := by
  have he : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub hd]
    norm_num
  rw [layerConstant, ← he, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4), Real.rpow_natCast]

/-- The manuscript's stated 4^(-(d-1)) lower bound for every recursively
constructed ordered-layer set, in ordinary power notation. -/
theorem LayerConstructible.fan_lower_bound {ι : Type u} [Fintype ι] {F : Finset (ι → ℝ)}
    (h : LayerConstructible ι F) :
    (F.card : ℝ) ^ (sharpExponent (Fintype.card ι) : ℝ) / (4 : ℝ) ^ (Fintype.card ι - 1) ≤ maxFan F := by
  have hh := h.bound
  rw [layerConstant_eq_inv_pow hh.1] at hh
  simpa only [div_eq_mul_inv, mul_comm] using hh.2

end
end Erdos539Geometry
