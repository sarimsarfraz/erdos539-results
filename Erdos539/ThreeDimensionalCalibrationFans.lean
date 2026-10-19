/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ThreeDimensionalCalibrationGeometry
import Erdos539.GluingEqualCardFan
import Erdos539.StripFans
import Erdos539.GluingDiameter

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
local instance calibrationThreeFansIntegerDecidableEq : DecidableEq (CalibrationThreeCoordinates → ℤ) := Classical.decEq _

/-- The explicit five-parameter family is exactly this separated gluing. -/
theorem calibrationThree_eq_gluing (T : ℕ) :
    calibrationThree T = gluing (gibbsStrip T (4 * T)) (intervalVectors (T ^ 3))
      (T ^ 2) (10 * (T : ℤ) ^ 3) := by
  ext z
  constructor
  · intro hz
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨⟨hat, has⟩, hac⟩ := Finset.mem_product.mp ha |>.imp_left Finset.mem_product.mp
    have ht := Finset.mem_Ico.mp hat
    have hc := Finset.mem_Ico.mp hac
    apply mem_gluing.mpr
    refine ⟨a.1.1.toNat, by omega, stripEncode (4 * T) a.1.2, Finset.mem_image.mpr ⟨a.1.2, has, rfl⟩,
      (fun _ : Unit ↦ a.2), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨a.2.toNat, Finset.mem_range.mpr (by omega),
        by funext i; exact Int.toNat_of_nonneg hc.1⟩
    · funext i
      cases i <;> simp only [calibrationThreeEncode, glueVector, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        Sum.elim_inl, Sum.elim_inr, Int.toNat_of_nonneg ht.1] <;> ring
  · intro hz
    obtain ⟨t, ht, x, hx, y, hy, rfl⟩ := mem_gluing.mp hz
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hy
    apply Finset.mem_image.mpr
    refine ⟨(((t : ℤ), r), (c : ℤ)), ?_, ?_⟩
    · refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨?_, hr⟩, ?_⟩
      · apply Finset.mem_Ico.mpr
        constructor
        · exact Int.natCast_nonneg _
        · change (t : ℤ) < (T ^ 2 : ℕ)
          exact_mod_cast ht
      · apply Finset.mem_Ico.mpr
        constructor
        · exact Int.natCast_nonneg _
        · change (c : ℤ) < (T ^ 3 : ℕ)
          exact_mod_cast Finset.mem_range.mp hc
    · funext i
      cases i <;> simp only [calibrationThreeEncode, glueVector, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
        Sum.elim_inl, Sum.elim_inr] <;> ring

theorem calibrationThree_strip_gap {T : ℕ} (hT : 0 < T) :
    HasCoordinateGap (gibbsStrip T (4 * T)) (10 * (T : ℤ) ^ 3) := by
  rw [gibbsStrip_eq_gluing]
  have ht : (1 : ℤ) ≤ T := by exact_mod_cast hT
  have h12 : (T : ℤ) ≤ (T : ℤ) ^ 2 := by nlinarith
  have h23 : (T : ℤ) ^ 2 ≤ (T : ℤ) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (T : ℤ)) (show 0 ≤ (T : ℤ) - 1 by omega)]
  have hsmall : (T : ℤ) + (T : ℤ) * (4 * T) < 10 * (T : ℤ) ^ 3 := by nlinarith
  intro x hx y hy i
  exact (gluing_diameter (by positivity : (0 : ℤ) ≤ 4 * T) T
    (intervalVectors_diameter T) (intervalVectors_diameter T) x hx y hy i).trans_lt hsmall

theorem calibrationThree_interval_gap {T : ℕ} (hT : 0 < T) :
    HasCoordinateGap (intervalVectors (T ^ 3)) (10 * (T : ℤ) ^ 3) := by
  have ht : (0 : ℤ) < T := by exact_mod_cast hT
  intro x hx y hy i
  have h := intervalVectors_diameter (T ^ 3) x hx y hy i
  push_cast at h
  exact h.trans_lt (by nlinarith [pow_pos ht 3])

/-- The literal family has maximum fan at most 4 T^5, as in the source. -/
theorem calibrationThree_maxFan {T : ℕ} (hT : 0 < T) :
    maxFan (integerRealSet (calibrationThree T)) ≤ 4 * T ^ 5 := by
  have ht : (0 : ℤ) < T := by exact_mod_cast hT
  have hgap := calibrationThree_strip_gap hT
  have hcard : (gibbsStrip T (4 * T)).card = (intervalVectors (T ^ 3)).card := by
    rw [gibbsStrip_card (by omega), intervalVectors_card]
  have h := maxFan_gluing_equal_card (gibbsStrip_nonempty hT _) (intervalVectors_nonempty (by positivity))
    hcard (T ^ 2) (by positivity : (0 : ℤ) < 10 * (T : ℤ) ^ 3) hgap (calibrationThree_interval_gap hT)
    (Sum.inl ()) ()
  rw [← calibrationThree_eq_gluing, gibbsStrip_maxFan hT (by omega),
    maxFan_eq_card_one_dimensional (), integerRealSet_card, intervalVectors_card,
    gibbsStrip_card (by omega)] at h
  have hm : T - 1 ≤ T := Nat.sub_le _ _
  have hk : T ^ 2 - 1 ≤ T ^ 2 := Nat.sub_le _ _
  have hm' := Nat.mul_le_mul_right (T * T ^ 3) hm
  have hk' := Nat.mul_le_mul_right (T ^ 3) hk
  nlinarith

end
end Erdos539Geometry
