/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StripProjection
import Erdos539.FourLeafFans

namespace Erdos539Geometry
noncomputable section
open scoped Classical

theorem gibbsStrip_eq_gluing (T : ℕ) (H : ℤ) :
    gibbsStrip T H = gluing (intervalVectors T) (intervalVectors T) T H := by
  ext z
  constructor
  · intro hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    simp only [stripDigits, Finset.mem_product, scalarInterval, Finset.mem_Ico] at ha
    apply mem_gluing.mpr
    refine ⟨a.1.1.toNat, by omega, (fun _ : Unit ↦ a.1.2), ?_,
      (fun _ : Unit ↦ a.2), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨a.1.2.toNat, Finset.mem_range.mpr (by omega),
        by funext i; exact Int.toNat_of_nonneg ha.1.2.1⟩
    · exact Finset.mem_image.mpr ⟨a.2.toNat, Finset.mem_range.mpr (by omega),
        by funext i; exact Int.toNat_of_nonneg ha.2.1⟩
    · funext i
      cases i <;> simp only [glueVector, stripEncode, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        Sum.elim_inl, Sum.elim_inr, Int.toNat_of_nonneg ha.1.1.1] <;> ring
  · intro hz
    obtain ⟨t, ht, x, hx, y, hy, rfl⟩ := mem_gluing.mp hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    have hu' := Finset.mem_range.mp hu
    have hv' := Finset.mem_range.mp hv
    apply Finset.mem_image.mpr
    refine ⟨(((t : ℤ), (u : ℤ)), (v : ℤ)), ?_, ?_⟩
    · simp only [stripDigits, Finset.mem_product, scalarInterval, Finset.mem_Ico]
      omega
    · funext i
      cases i <;> simp only [glueVector, stripEncode, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        Sum.elim_inl, Sum.elim_inr] <;> ring

theorem gibbsStrip_maxFan {T : ℕ} (hT : 0 < T) {H : ℤ} (hH : 2 * (T : ℤ) < H) :
    maxFan (integerRealSet (gibbsStrip T H)) = T ^ 2 + (T - 1) * T := by
  rw [gibbsStrip_eq_gluing, maxFan_symmetric_gluing (intervalVectors_nonempty hT) hT
    (by omega) (coordinateGap_of_diameter (Int.natCast_nonneg T) hH (intervalVectors_diameter T)) (),
    maxFan_eq_card_one_dimensional (), integerRealSet_card, intervalVectors_card]

theorem gibbsStrip_maxFan_real {T : ℕ} (hT : 0 < T) {H : ℤ} (hH : 2 * (T : ℤ) < H) :
    (maxFan (integerRealSet (gibbsStrip T H)) : ℝ) = 2 * (T : ℝ) ^ 2 - T := by
  rw [gibbsStrip_maxFan hT hH]
  push_cast [Nat.cast_sub hT]
  ring

theorem gibbsStrip_projected_maxFan {T : ℕ} (hT : 0 < T) {H : ℤ} (hH : (T : ℤ) < H) :
    maxFan (((gibbsStrip T H).image stripProjection).image (fun z : ℤ ↦ fun _ : Unit ↦ (z : ℝ))) = T ^ 2 := by
  rw [maxFan_eq_card_one_dimensional (), Finset.card_image_of_injective _ (by
    intro x y he
    have hh : (x : ℝ) = (y : ℝ) := congrFun he ()
    exact_mod_cast hh), gibbsStrip_projection hT H, stripProjected_card hH]

theorem gibbsStrip_fiber_maxFan {T : ℕ} (hT : 0 < T) {H : ℤ} (hH : (T : ℤ) < H)
    (y : (gibbsStrip T H).image stripProjection) :
    maxFan (integerRealSet (fiber (gibbsStrip T H) stripProjection y.val)) = T := by
  let F := integerRealSet (fiber (gibbsStrip T H) stripProjection y.val)
  have hi : Set.InjOn (fun x : (Unit ⊕ Unit) → ℝ ↦ x (Sum.inr ())) F := by
    intro x hx z hz he
    obtain ⟨a, ha, rfl⟩ := mem_integerRealSet.mp hx
    obtain ⟨b, hb, rfl⟩ := mem_integerRealSet.mp hz
    have hap := (mem_fiber.mp ha).2
    have hbp := (mem_fiber.mp hb).2
    funext i
    cases i with
    | inl u => cases u; exact congrArg (fun k : ℤ ↦ (k : ℝ)) (hap.trans hbp.symm)
    | inr u => cases u; exact he
  have hc : F.card = T := by
    dsimp only [F]
    rw [integerRealSet_card, gibbsStrip_fiber_card hT hH]
  have hlo := coordinate_card_le_maxFan F (Sum.inr ())
  rw [Finset.card_image_of_injOn hi, hc] at hlo
  exact le_antisymm ((maxFan_le_card F).trans_eq hc) hlo

/-- The product of the actual projected and fiber fan sizes is T^3. -/
theorem gibbsStrip_fan_product {T : ℕ} (hT : 0 < T) {H : ℤ} (hH : (T : ℤ) < H)
    (y : (gibbsStrip T H).image stripProjection) :
    maxFan (((gibbsStrip T H).image stripProjection).image (fun z : ℤ ↦ fun _ : Unit ↦ (z : ℝ))) *
      maxFan (integerRealSet (fiber (gibbsStrip T H) stripProjection y.val)) = T ^ 3 := by
  rw [gibbsStrip_projected_maxFan hT hH, gibbsStrip_fiber_maxFan hT hH]
  ring

end
end Erdos539Geometry
