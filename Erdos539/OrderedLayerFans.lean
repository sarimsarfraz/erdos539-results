/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.OrderedLayers
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι κ τ : Type*} [LinearOrder τ]

omit [LinearOrder τ] in
theorem fan_orderedLayerProduct (L : Finset τ) (A : τ → Finset (ι → ℝ))
    (B : τ → Finset (κ → ℝ)) (a : ι ⊕ κ → ℝ) :
    fan (orderedLayerProduct L A B) a = L.biUnion (fun i ↦ fan (coordinateProduct (A i) (B i)) a) := by
  ext z
  simp only [mem_fan, mem_orderedLayerProduct, Finset.mem_biUnion]
  aesop

/-- Exact fan count at any anchor in a layer. Nonempty coordinate blocks
separate the outputs from different layers. -/
theorem ordered_layer_fan_card {L : Finset τ} {A : τ → Finset (ι → ℝ)}
    {B : τ → Finset (κ → ℝ)} (hord : IsOrderedLayers L A B) (t : ι) (v : κ)
    (hA : ∀ i ∈ L, (A i).Nonempty) (hB : ∀ i ∈ L, (B i).Nonempty)
    {i : τ} (hi : i ∈ L) {x : ι → ℝ} {y : κ → ℝ} (hx : x ∈ A i) (hy : y ∈ B i) :
    (fan (orderedLayerProduct L A B) (Sum.elim x y)).card =
      (fan (A i) x).card * (fan (B i) y).card +
        ∑ j ∈ L.filter (fun j ↦ i < j), (A j).card +
        ∑ j ∈ L.filter (fun j ↦ j < i), (B j).card := by
  classical
  have hdisj : (L : Set τ).PairwiseDisjoint
      (fun j ↦ fan (coordinateProduct (A j) (B j)) (Sum.elim x y)) := by
    intro j hj k hk hne
    rcases lt_or_gt_of_ne hne with hjk | hkj
    · exact ordered_layer_fans_disjoint hord t v hi hj hk hjk hx hy
    · exact (ordered_layer_fans_disjoint hord t v hi hk hj hkj hx hy).symm
  rw [fan_orderedLayerProduct, Finset.card_biUnion hdisj]
  have hterm (j : τ) (hj : j ∈ L) :
      (fan (coordinateProduct (A j) (B j)) (Sum.elim x y)).card =
        (if j = i then (fan (A i) x).card * (fan (B i) y).card else 0) +
        (if i < j then (A j).card else 0) + (if j < i then (B j).card else 0) := by
    rcases lt_trichotomy j i with hji | hji | hij
    · rw [ordered_layer_fan_card_below hord hi hj hji hx hy (hA j hj)]
      simp only [ne_of_lt hji, if_false, not_lt_of_ge hji.le, if_pos hji, zero_add]
    · subst j
      rw [fan_coordinateProduct, coordinateProduct_card]
      simp
    · rw [ordered_layer_fan_card_above hord hi hj hij hx hy (hB j hj)]
      simp only [ne_of_gt hij, if_false, if_pos hij, not_lt_of_ge hij.le, zero_add, add_zero]
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', hi, if_true, Finset.sum_filter]

/-- The manuscript's ordered-layer fan bound, with all outside-layer contributions. -/
theorem maxFan_orderedLayerProduct_ge {L : Finset τ} {A : τ → Finset (ι → ℝ)}
    {B : τ → Finset (κ → ℝ)} (hord : IsOrderedLayers L A B) (t : ι) (v : κ)
    (hA : ∀ i ∈ L, (A i).Nonempty) (hB : ∀ i ∈ L, (B i).Nonempty)
    {i : τ} (hi : i ∈ L) :
    maxFan (A i) * maxFan (B i) +
        ∑ j ∈ L.filter (fun j ↦ i < j), (A j).card +
        ∑ j ∈ L.filter (fun j ↦ j < i), (B j).card ≤ maxFan (orderedLayerProduct L A B) := by
  obtain ⟨x, hx, hxmax⟩ := exists_fan_eq_max (hA i hi)
  obtain ⟨y, hy, hymax⟩ := exists_fan_eq_max (hB i hi)
  have hxy : Sum.elim x y ∈ orderedLayerProduct L A B :=
    mem_orderedLayerProduct.mpr ⟨i, hi, mem_coordinateProduct.mpr ⟨x, hx, y, hy, rfl⟩⟩
  have h := card_fan_le_maxFan hxy
  rwa [ordered_layer_fan_card hord t v hA hB hi hx hy, hxmax, hymax] at h

/-- The layers are disjoint, so their sizes add exactly. -/
theorem orderedLayerProduct_card {L : Finset τ} {A : τ → Finset (ι → ℝ)}
    {B : τ → Finset (κ → ℝ)} (hord : IsOrderedLayers L A B) (t : ι) :
    (orderedLayerProduct L A B).card = ∑ i ∈ L, (A i).card * (B i).card := by
  classical
  have hdisj : (L : Set τ).PairwiseDisjoint (fun i ↦ coordinateProduct (A i) (B i)) := by
    intro i hi j hj hne
    apply Finset.disjoint_left.mpr
    intro z hzi hzj
    obtain ⟨x, hx, y, _hy, he⟩ := mem_coordinateProduct.mp hzi
    obtain ⟨x', hx', y', _hy', he'⟩ := mem_coordinateProduct.mp hzj
    have hh : x t = x' t := congrFun (he.trans he'.symm) (Sum.inl t)
    rcases lt_or_gt_of_ne hne with hij | hji
    · exact (ne_of_lt (hord.left i hi j hj hij x hx x' hx' t)) hh
    · exact (ne_of_gt (hord.left j hj i hi hji x' hx' x hx t)) hh
  rw [orderedLayerProduct, Finset.card_biUnion hdisj]
  exact Finset.sum_congr rfl (fun i _ ↦ coordinateProduct_card (A i) (B i))

end
end Erdos539Geometry
