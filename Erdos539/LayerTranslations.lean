/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.LayerConstructible

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
universe u
variable {ι κ τ : Type*}

def translateRealSet (F : Finset (ι → ℝ)) (v : ι → ℝ) : Finset (ι → ℝ) :=
  F.image (fun x ↦ x + v)

@[simp] theorem mem_translateRealSet {F : Finset (ι → ℝ)} {v z : ι → ℝ} :
    z ∈ translateRealSet F v ↔ ∃ x ∈ F, x + v = z := Finset.mem_image

theorem translateRealSet_nonempty {F : Finset (ι → ℝ)} (hF : F.Nonempty) (v : ι → ℝ) :
    (translateRealSet F v).Nonempty := hF.image _

theorem translate_orderedLayerProduct (L : Finset τ) (A : τ → Finset (ι → ℝ))
    (B : τ → Finset (κ → ℝ)) (v : ι ⊕ κ → ℝ) :
    translateRealSet (orderedLayerProduct L A B) v =
      orderedLayerProduct L (fun t ↦ translateRealSet (A t) (fun i ↦ v (Sum.inl i)))
        (fun t ↦ translateRealSet (B t) (fun j ↦ v (Sum.inr j))) := by
  ext z
  constructor
  · intro hz
    obtain ⟨w, hw, rfl⟩ := mem_translateRealSet.mp hz
    obtain ⟨t, ht, hw⟩ := mem_orderedLayerProduct.mp hw
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_coordinateProduct.mp hw
    apply mem_orderedLayerProduct.mpr
    refine ⟨t, ht, mem_coordinateProduct.mpr ⟨x + (fun i ↦ v (Sum.inl i)),
      mem_translateRealSet.mpr ⟨x, hx, rfl⟩, y + (fun j ↦ v (Sum.inr j)),
      mem_translateRealSet.mpr ⟨y, hy, rfl⟩, ?_⟩⟩
    funext i
    cases i <;> rfl
  · intro hz
    obtain ⟨t, ht, hz⟩ := mem_orderedLayerProduct.mp hz
    obtain ⟨x', hx', y', hy', rfl⟩ := mem_coordinateProduct.mp hz
    obtain ⟨x, hx, rfl⟩ := mem_translateRealSet.mp hx'
    obtain ⟨y, hy, rfl⟩ := mem_translateRealSet.mp hy'
    apply mem_translateRealSet.mpr
    refine ⟨Sum.elim x y, mem_orderedLayerProduct.mpr
      ⟨t, ht, mem_coordinateProduct.mpr ⟨x, hx, y, hy, rfl⟩⟩, ?_⟩
    funext i
    cases i <;> rfl

theorem IsOrderedLayers.translate [LinearOrder τ] {L : Finset τ}
    {A : τ → Finset (ι → ℝ)} {B : τ → Finset (κ → ℝ)} (h : IsOrderedLayers L A B)
    (v : ι → ℝ) (w : κ → ℝ) :
    IsOrderedLayers L (fun t ↦ translateRealSet (A t) v) (fun t ↦ translateRealSet (B t) w) := by
  constructor
  · intro i hi j hj hij x hx y hy t
    obtain ⟨x', hx', rfl⟩ := mem_translateRealSet.mp hx
    obtain ⟨y', hy', rfl⟩ := mem_translateRealSet.mp hy
    change x' t + v t < y' t + v t
    linarith [h.left i hi j hj hij x' hx' y' hy' t]
  · intro i hi j hj hij x hx y hy t
    obtain ⟨x', hx', rfl⟩ := mem_translateRealSet.mp hx
    obtain ⟨y', hy', rfl⟩ := mem_translateRealSet.mp hy
    change y' t + w t < x' t + w t
    linarith [h.right i hi j hj hij x' hx' y' hy' t]

theorem translate_reindexRealSet (e : ι ≃ κ) (F : Finset (ι → ℝ)) (v : κ → ℝ) :
    translateRealSet (reindexRealSet e F) v =
      reindexRealSet e (translateRealSet F (fun i ↦ v (e i))) := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := mem_translateRealSet.mp hz
    obtain ⟨x, hx, rfl⟩ := mem_reindexRealSet.mp hy
    refine mem_reindexRealSet.mpr ⟨x + (fun i ↦ v (e i)), mem_translateRealSet.mpr ⟨x, hx, rfl⟩, ?_⟩
    funext i
    simp only [reindexRealVector, Pi.add_apply, e.apply_symm_apply]
  · intro hz
    obtain ⟨y, hy, rfl⟩ := mem_reindexRealSet.mp hz
    obtain ⟨x, hx, rfl⟩ := mem_translateRealSet.mp hy
    refine mem_translateRealSet.mpr ⟨reindexRealVector e x, mem_reindexRealSet.mpr ⟨x, hx, rfl⟩, ?_⟩
    funext i
    simp only [reindexRealVector, Pi.add_apply, e.apply_symm_apply]

/-- Translation closure follows from the recursive definition; no additional
constructor or structural hypothesis is needed. -/
theorem LayerConstructible.translate {ι : Type u} [Fintype ι] {F : Finset (ι → ℝ)}
    (h : LayerConstructible ι F) (v : ι → ℝ) : LayerConstructible ι (translateRealSet F v) := by
  induction h with
  | line F hd => exact .line _ hd
  | layers L hL A B hord hA hB hCA hCB ihA ihB =>
    rw [translate_orderedLayerProduct]
    exact .layers L hL _ _ (hord.translate _ _) (fun t ht ↦ translateRealSet_nonempty (hA t ht) _)
      (fun t ht ↦ translateRealSet_nonempty (hB t ht) _) (fun t ht ↦ ihA t ht _) (fun t ht ↦ ihB t ht _)
  | reindex e h ih =>
    rw [translate_reindexRealSet]
    exact .reindex e (ih _)

end
end Erdos539Geometry
