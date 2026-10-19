/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CenteredMidpoint
import Erdos539.MidpointSymmetrization

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι M : Type*} [AddCommGroup M]

/-- The centered core's positive parts are all in the original fan at its center. -/
theorem centered_core_positive_subset (e : M →ₗ[ℤ] (ι → ℝ)) (F : Finset M) (a : M) :
    embeddedPositiveParts e (groupTranslate (symmetricCore F a) a) ⊆ fan (F.image e) (e a) := by
  intro z hz
  obtain ⟨v, hv, hvz⟩ := mem_fan.mp hz
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨x, hx, rfl⟩ := mem_groupTranslate.mp hw
  apply mem_fan.mpr
  refine ⟨e x, Finset.mem_image_of_mem e (mem_symmetricCore.mp hx).1, ?_⟩
  have heq : pdiff (e x) (e a) = pdiff (e (x - a)) 0 := by
    funext i
    simp only [pdiff, map_sub, Pi.sub_apply, Pi.zero_apply, sub_zero]
  exact heq.trans hvz

/-- The sharp midpoint theorem with the complete rank loss, in logarithmic form. -/
theorem midpoint_log_fan_bound [Fintype ι] [Module.Free ℤ M] [Module.Finite ℤ M]
    (e : M →ₗ[ℤ] (ι → ℝ)) (he : Function.Injective e) {F : Finset M}
    (hFn : F.Nonempty) (hF : GroupMidpointClosed F) (hd : 0 < Fintype.card ι) :
    (sharpExponent (Fintype.card ι) : ℝ) * Real.log F.card -
      ((Fintype.card ι : ℝ) + 3 * Module.finrank ℤ M) * Real.log 2 ≤
        Real.log (maxFan (F.image e)) := by
  classical
  obtain ⟨a, ha, hlarge⟩ := exists_large_symmetricCore hFn hF
  let C := groupTranslate (symmetricCore F a) a
  have hzero : 0 ∈ C := zero_mem_centered_symmetricCore ha
  have hCn : C.Nonempty := ⟨0, hzero⟩
  have hc : (0 : ℝ) < C.card := by exact_mod_cast hCn.card_pos
  have hn : (0 : ℝ) < F.card := by exact_mod_cast hFn.card_pos
  have hq : (0 : ℝ) < (embeddedPositiveParts e C).card := by
    exact_mod_cast (embeddedPositiveParts_nonempty e hCn).card_pos
  have hbound := centered_midpoint_log_bound (Fintype.card ι) ι rfl hd M e he C hzero
    (centered_symmetricCore_symmetric F a) ((hF.symmetricCore a).translate a)
  have hCcard : C.card = (symmetricCore F a).card := groupTranslate_card _ _
  rw [← hCcard] at hlarge
  have hsize := Real.log_le_log hn (show (F.card : ℝ) ≤
    (2 : ℝ) ^ Module.finrank ℤ M * C.card by exact_mod_cast hlarge)
  rw [Real.log_mul (by positivity) hc.ne', Real.log_pow] at hsize
  have hsub : embeddedPositiveParts e C ⊆ fan (F.image e) (e a) := by
    have hi : @Finset.image M (ι → ℝ) (Classical.decEq _) e F = F.image e := by
      ext x
      simp only [Finset.mem_image]
    have hh := centered_core_positive_subset e F a
    rw [hi] at hh
    exact hh
  have hfan : (embeddedPositiveParts e C).card ≤ maxFan (F.image e) :=
    (Finset.card_le_card hsub).trans
      (card_fan_le_maxFan (Finset.mem_image_of_mem e ha))
  have hmono := Real.log_le_log hq (show ((embeddedPositiveParts e C).card : ℝ) ≤
    maxFan (F.image e) by exact_mod_cast hfan)
  have hu : (0 : ℝ) ≤ sharpExponent (Fintype.card ι) := by
    exact_mod_cast (sharpExponent_pos (Fintype.card ι)).le
  have hu1 : (sharpExponent (Fintype.card ι) : ℝ) ≤ 1 := by
    exact_mod_cast (sharpExponent_bounds (Fintype.card ι)).2
  have hL : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsizeu := mul_le_mul_of_nonneg_left hsize hu
  have hloss := mul_le_mul_of_nonneg_right hu1
    (mul_nonneg (Nat.cast_nonneg (Module.finrank ℤ M)) hL)
  nlinarith

/-- The centered theorem in the exact power form of the manuscript. -/
theorem centered_midpoint_fan_bound [Fintype ι] [Module.Free ℤ M] [Module.Finite ℤ M]
    (e : M →ₗ[ℤ] (ι → ℝ)) (he : Function.Injective e) {F : Finset M}
    (hzero : 0 ∈ F) (hsym : GroupSymmetric F) (hF : GroupMidpointClosed F)
    (hd : 0 < Fintype.card ι) :
    (F.card : ℝ) ^ (sharpExponent (Fintype.card ι) : ℝ) /
      (2 : ℝ) ^ (Fintype.card ι + 2 * Module.finrank ℤ M) ≤ (embeddedPositiveParts e F).card := by
  have hFn : F.Nonempty := ⟨0, hzero⟩
  have hn : (0 : ℝ) < F.card := by exact_mod_cast hFn.card_pos
  have hq : (0 : ℝ) < (embeddedPositiveParts e F).card := by
    exact_mod_cast (embeddedPositiveParts_nonempty e hFn).card_pos
  have h := centered_midpoint_log_bound (Fintype.card ι) ι rfl hd M e he F hzero hsym hF
  have hnp := Real.rpow_pos_of_pos hn (sharpExponent (Fintype.card ι) : ℝ)
  have hp : (0 : ℝ) < (2 : ℝ) ^ (Fintype.card ι + 2 * Module.finrank ℤ M) := by positivity
  apply (Real.log_le_log_iff (div_pos hnp hp) hq).mp
  rw [Real.log_div hnp.ne' hp.ne', Real.log_rpow hn, Real.log_pow]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  exact h

/-- Every midpoint-closed finite subset of a rank-r free group in R^d has
an anchored fan at least 2^(-d-3r) times its size to the sharp exponent. -/
theorem midpoint_fan_bound [Fintype ι] [Module.Free ℤ M] [Module.Finite ℤ M]
    (e : M →ₗ[ℤ] (ι → ℝ)) (he : Function.Injective e) {F : Finset M}
    (hFn : F.Nonempty) (hF : GroupMidpointClosed F) (hd : 0 < Fintype.card ι) :
    (F.card : ℝ) ^ (sharpExponent (Fintype.card ι) : ℝ) /
      (2 : ℝ) ^ (Fintype.card ι + 3 * Module.finrank ℤ M) ≤ maxFan (F.image e) := by
  have hn : (0 : ℝ) < F.card := by exact_mod_cast hFn.card_pos
  have hq : (0 : ℝ) < maxFan (F.image e) := by
    exact_mod_cast (one_le_maxFan (hFn.image e))
  have h := midpoint_log_fan_bound e he hFn hF hd
  have hnp := Real.rpow_pos_of_pos hn (sharpExponent (Fintype.card ι) : ℝ)
  have hp : (0 : ℝ) < (2 : ℝ) ^ (Fintype.card ι + 3 * Module.finrank ℤ M) := by positivity
  apply (Real.log_le_log_iff (div_pos hnp hp) hq).mp
  rw [Real.log_div hnp.ne' hp.ne', Real.log_rpow hn, Real.log_pow]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  exact h

end
end Erdos539Geometry
