/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ProductFans

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι κ τ : Type*} [LinearOrder τ]

/-- The two coordinate blocks move in opposite strict orders between layers. -/
structure IsOrderedLayers (L : Finset τ) (A : τ → Finset (ι → ℝ)) (B : τ → Finset (κ → ℝ)) : Prop where
  left : ∀ i ∈ L, ∀ j ∈ L, i < j → ∀ x ∈ A i, ∀ x' ∈ A j, ∀ t, x t < x' t
  right : ∀ i ∈ L, ∀ j ∈ L, i < j → ∀ y ∈ B i, ∀ y' ∈ B j, ∀ t, y' t < y t

def orderedLayerProduct (L : Finset τ) (A : τ → Finset (ι → ℝ)) (B : τ → Finset (κ → ℝ)) :
    Finset (ι ⊕ κ → ℝ) := L.biUnion (fun i ↦ coordinateProduct (A i) (B i))

omit [LinearOrder τ] in
@[simp] theorem mem_orderedLayerProduct {L : Finset τ} {A : τ → Finset (ι → ℝ)}
    {B : τ → Finset (κ → ℝ)} {z : ι ⊕ κ → ℝ} :
    z ∈ orderedLayerProduct L A B ↔ ∃ i ∈ L, z ∈ coordinateProduct (A i) (B i) := by
  simp only [orderedLayerProduct, Finset.mem_biUnion]

omit [LinearOrder τ] in
theorem pdiff_sum_of_above {a x : ι → ℝ} {b y : κ → ℝ}
    (ha : ∀ i, x i ≤ a i) (hb : ∀ i, b i ≤ y i) :
    pdiff (Sum.elim a b) (Sum.elim x y) = Sum.elim (fun i ↦ a i - x i) (fun _ ↦ 0) := by
  funext i
  cases i with
  | inl i => exact max_eq_left (sub_nonneg.mpr (ha i))
  | inr i => exact max_eq_right (sub_nonpos.mpr (hb i))

omit [LinearOrder τ] in
theorem pdiff_sum_of_below {a x : ι → ℝ} {b y : κ → ℝ}
    (ha : ∀ i, a i ≤ x i) (hb : ∀ i, y i ≤ b i) :
    pdiff (Sum.elim a b) (Sum.elim x y) = Sum.elim (fun _ ↦ 0) (fun i ↦ b i - y i) := by
  funext i
  cases i with
  | inl i => exact max_eq_right (sub_nonpos.mpr (ha i))
  | inr i => exact max_eq_left (sub_nonneg.mpr (hb i))

theorem ordered_layer_fan_card_above {L : Finset τ} {A : τ → Finset (ι → ℝ)}
    {B : τ → Finset (κ → ℝ)} (hord : IsOrderedLayers L A B)
    {i j : τ} (hi : i ∈ L) (hj : j ∈ L) (hij : i < j)
    {x : ι → ℝ} {y : κ → ℝ} (hx : x ∈ A i) (hy : y ∈ B i) (hBj : (B j).Nonempty) :
    (fan (coordinateProduct (A j) (B j)) (Sum.elim x y)).card = (A j).card := by
  classical
  let f : (ι → ℝ) → (ι ⊕ κ → ℝ) := fun a ↦ Sum.elim (fun t ↦ a t - x t) (fun _ ↦ 0)
  have he : fan (coordinateProduct (A j) (B j)) (Sum.elim x y) = (A j).image f := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw, rfl⟩ := mem_fan.mp hz
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_coordinateProduct.mp hw
      exact Finset.mem_image.mpr ⟨a, ha, (pdiff_sum_of_above
        (fun t ↦ (hord.left i hi j hj hij x hx a ha t).le)
        (fun t ↦ (hord.right i hi j hj hij y hy b hb t).le)).symm⟩
    · intro hz
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨b, hb⟩ := hBj
      exact mem_fan.mpr ⟨Sum.elim a b, mem_coordinateProduct.mpr ⟨a, ha, b, hb, rfl⟩,
        pdiff_sum_of_above (fun t ↦ (hord.left i hi j hj hij x hx a ha t).le)
          (fun t ↦ (hord.right i hi j hj hij y hy b hb t).le)⟩
  rw [he]
  apply Finset.card_image_of_injOn
  intro a _ b _ hab
  funext t
  have h := congrFun hab (Sum.inl t)
  change a t - x t = b t - x t at h
  linarith

theorem ordered_layer_fan_card_below {L : Finset τ} {A : τ → Finset (ι → ℝ)}
    {B : τ → Finset (κ → ℝ)} (hord : IsOrderedLayers L A B)
    {i j : τ} (hi : i ∈ L) (hj : j ∈ L) (hji : j < i)
    {x : ι → ℝ} {y : κ → ℝ} (hx : x ∈ A i) (hy : y ∈ B i) (hAj : (A j).Nonempty) :
    (fan (coordinateProduct (A j) (B j)) (Sum.elim x y)).card = (B j).card := by
  classical
  let f : (κ → ℝ) → (ι ⊕ κ → ℝ) := fun b ↦ Sum.elim (fun _ ↦ 0) (fun t ↦ b t - y t)
  have he : fan (coordinateProduct (A j) (B j)) (Sum.elim x y) = (B j).image f := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, hw, rfl⟩ := mem_fan.mp hz
      obtain ⟨a, ha, b, hb, rfl⟩ := mem_coordinateProduct.mp hw
      exact Finset.mem_image.mpr ⟨b, hb, (pdiff_sum_of_below
        (fun t ↦ (hord.left j hj i hi hji a ha x hx t).le)
        (fun t ↦ (hord.right j hj i hi hji b hb y hy t).le)).symm⟩
    · intro hz
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨a, ha⟩ := hAj
      exact mem_fan.mpr ⟨Sum.elim a b, mem_coordinateProduct.mpr ⟨a, ha, b, hb, rfl⟩,
        pdiff_sum_of_below (fun t ↦ (hord.left j hj i hi hji a ha x hx t).le)
          (fun t ↦ (hord.right j hj i hi hji b hb y hy t).le)⟩
  rw [he]
  apply Finset.card_image_of_injOn
  intro a _ b _ hab
  funext t
  have h := congrFun hab (Sum.inr t)
  change a t - y t = b t - y t at h
  linarith

/-- Every other layer contributes outputs distinct from those of each earlier layer. -/
theorem ordered_layer_fans_disjoint {L : Finset τ} {A : τ → Finset (ι → ℝ)}
    {B : τ → Finset (κ → ℝ)} (hord : IsOrderedLayers L A B) (t : ι) (v : κ)
    {i j k : τ} (hi : i ∈ L) (hj : j ∈ L) (hk : k ∈ L) (hjk : j < k)
    {x : ι → ℝ} {y : κ → ℝ} (hx : x ∈ A i) (hy : y ∈ B i) :
    Disjoint (fan (coordinateProduct (A j) (B j)) (Sum.elim x y))
      (fan (coordinateProduct (A k) (B k)) (Sum.elim x y)) := by
  apply Finset.disjoint_left.mpr
  intro z hzj hzk
  obtain ⟨w, hw, hew⟩ := mem_fan.mp hzj
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_coordinateProduct.mp hw
  obtain ⟨w', hw', hew'⟩ := mem_fan.mp hzk
  obtain ⟨a', ha', b', hb', rfl⟩ := mem_coordinateProduct.mp hw'
  have he := hew.trans hew'.symm
  by_cases hik : i < k
  · have hpos : 0 < a' t - x t := sub_pos.mpr (hord.left i hi k hk hik x hx a' ha' t)
    have hlt : max (a t - x t) 0 < a' t - x t :=
      max_lt (sub_lt_sub_right (hord.left j hj k hk hjk a ha a' ha' t) _) hpos
    have hh := congrFun he (Sum.inl t)
    change max (a t - x t) 0 = max (a' t - x t) 0 at hh
    rw [max_eq_left hpos.le] at hh
    linarith
  · have hji : j < i := hjk.trans_le (le_of_not_gt hik)
    have hpos : 0 < b v - y v := sub_pos.mpr (hord.right j hj i hi hji b hb y hy v)
    have hlt : max (b' v - y v) 0 < b v - y v :=
      max_lt (sub_lt_sub_right (hord.right j hj k hk hjk b hb b' hb' v) _) hpos
    have hh := congrFun he (Sum.inr v)
    change max (b v - y v) 0 = max (b' v - y v) 0 at hh
    rw [max_eq_left hpos.le] at hh
    linarith

end
end Erdos539Geometry
