/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CoordinateProductEnergyPalette
import Erdos539.CriticalCoreSelection

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι κ : Type} [Fintype ι] [Fintype κ]
local instance productCriticalRealDecidableEq {α : Type} : DecidableEq (α → ℝ) := Classical.decEq _

/-- Removing a factor with 1 < Lambda <= q strictly improves the actual
critical selection score for b>1. Thus such a product cannot be a selected
critical core, regardless of its possible original parent or mask. -/
theorem product_not_projectionCriticalCore {A : Finset (ι → ℝ)} {B : Finset (κ → ℝ)}
    (hA : A.Nonempty) (hB : B.Nonempty) (hlarge : 1 < energyNorm A)
    (hq : energyNorm A ≤ (posDiff A).card) {b : ℝ} (hb : 1 < b)
    (parent : Finset (ι ⊕ κ → ℝ)) (I : Finset (ι ⊕ κ)) :
    ¬ IsProjectionCriticalCore parent b I (coordinateProduct A B) := by
  intro hcrit
  obtain ⟨a, ha⟩ := hA
  have hU := coordinateProduct_nonempty (Finset.singleton_nonempty a) hB
  have hsub := coordinateProduct_mono_left (Finset.singleton_subset_iff.mpr ha) B
  have h := hcrit.compare_subset hU hsub
  rw [posDiff_coordinateProduct, coordinateProduct_card, posDiff_coordinateProduct,
    coordinateProduct_card, posDiff_singleton, Finset.card_singleton, one_mul,
    energyNorm_coordinateProduct, energyNorm_coordinateProduct, energyNorm_singleton, one_mul,
    Nat.cast_mul] at h
  have hqA : (0 : ℝ) < (posDiff A).card := lt_of_lt_of_le (by linarith) hq
  have hqB : (0 : ℝ) < (posDiff B).card := by exact_mod_cast posDiff_card_pos hB
  have hlA : 0 < Real.log (energyNorm A) := Real.log_pos hlarge
  have hlq := Real.log_le_log (by linarith : 0 < energyNorm A) hq
  unfold criticalLogScore at h
  rw [Real.log_mul hqA.ne' hqB.ne', Real.log_mul (by linarith : energyNorm A ≠ 0) (energyNorm_pos hB).ne'] at h
  nlinarith [mul_nonneg (by linarith : 0 ≤ b) (sub_nonneg.mpr hlq)]

/-- The palette/norm ratio test fails for every exponent below one. -/
theorem reciprocal_palette_lt_norm_rpow {q lam θ : ℝ} (hlam : 1 < lam) (hq : lam ≤ q) (hθ : θ < 1) :
    1 / q < (1 / lam) ^ θ := by
  have hlamp : 0 < lam := by linarith
  have hqp : 0 < q := hlamp.trans_le hq
  apply (Real.log_lt_log_iff (div_pos zero_lt_one hqp)
    (Real.rpow_pos_of_pos (div_pos zero_lt_one hlamp) θ)).mp
  rw [Real.log_rpow (div_pos zero_lt_one hlamp), Real.log_div one_ne_zero hqp.ne',
    Real.log_div one_ne_zero hlamp.ne', Real.log_one]
  have hl := Real.log_le_log hlamp hq
  have hp := Real.log_pos hlam
  nlinarith

end
end Erdos539Geometry
