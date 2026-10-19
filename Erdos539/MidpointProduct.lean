/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.MidpointCoset

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι M : Type*} [AddCommGroup M]

theorem max_double_div_two (x : ℝ) : max (x + x) 0 / 2 = max x 0 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, max_eq_left (by linarith : 0 ≤ x + x)]
    ring
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hx', max_eq_right (by linarith : x + x ≤ 0), zero_div]

/-- The positive parts of the two actual descendants inject, after halving,
into the parent's positive parts. No union of unrelated anchors is used. -/
theorem midpointDescendant_positive_product_le {F : Finset M} (hF : GroupMidpointClosed F)
    (e : M →ₗ[ℤ] (ι → ℝ)) (he : Function.Injective e) (I J : Finset ι)
    (hIJ : Disjoint I J) (hcover : ∀ i, i ∈ I ∨ i ∈ J) :
    (fan ((midpointDescendant F e he I).image (supportedChildEmbedding e I)) 0).card *
      (fan ((midpointDescendant F e he J).image (supportedChildEmbedding e J)) 0).card ≤
        (fan (F.image e) 0).card := by
  classical
  let A := (midpointDescendant F e he I).image (supportedChildEmbedding e I)
  let B := (midpointDescendant F e he J).image (supportedChildEmbedding e J)
  let f : (I → ℝ) × (J → ℝ) → (ι → ℝ) := fun z i ↦
    if hi : i ∈ I then z.1 ⟨i, hi⟩ / 2 else z.2 ⟨i, (hcover i).resolve_left hi⟩ / 2
  have hcard : (fan A 0 ×ˢ fan B 0).card ≤ (fan (F.image e) 0).card := by
    apply Finset.card_le_card_of_injOn f
    · intro z hz
      obtain ⟨hzA, hzB⟩ := Finset.mem_product.mp hz
      obtain ⟨a, ha, hpa⟩ := mem_fan.mp hzA
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨b, hb, hpb⟩ := mem_fan.mp hzB
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
      have hz' : z = (pdiff (supportedChildEmbedding e I x) 0, pdiff (supportedChildEmbedding e J y) 0) :=
        Prod.ext hpa.symm hpb.symm
      rw [hz']
      apply mem_fan.mpr
      refine ⟨e (x.val + y.val), Finset.mem_image_of_mem e (midpointDescendant_add_mem hF hx hy), ?_⟩
      funext i
      dsimp only [f]
      by_cases hi : i ∈ I
      · rw [dif_pos hi]
        have hj : i ∉ J := fun hj ↦ Finset.disjoint_left.mp hIJ hi hj
        have hy0 : e y.val i = 0 := y.property i hj
        change max (e (x.val + y.val) i - 0) 0 = max (e ((2 : ℤ) • x.val) i - 0) 0 / 2
        simp only [two_zsmul, map_add, Pi.add_apply, hy0, add_zero, sub_zero]
        exact (max_double_div_two (e x.val i)).symm
      · rw [dif_neg hi]
        have hx0 : e x.val i = 0 := x.property i hi
        change max (e (x.val + y.val) i - 0) 0 = max (e ((2 : ℤ) • y.val) i - 0) 0 / 2
        simp only [two_zsmul, map_add, Pi.add_apply, hx0, zero_add, sub_zero]
        exact (max_double_div_two (e y.val i)).symm
    · intro z _ w _ hzw
      apply Prod.ext
      · funext i
        have hh := congrFun hzw i.val
        dsimp only [f] at hh
        rw [dif_pos i.property, dif_pos i.property] at hh
        linarith
      · funext i
        have hi : i.val ∉ I := fun hi ↦ Finset.disjoint_left.mp hIJ hi i.property
        have hh := congrFun hzw i.val
        dsimp only [f] at hh
        rw [dif_neg hi, dif_neg hi] at hh
        linarith
  simpa only [Finset.card_product] using hcard

end
end Erdos539Geometry
