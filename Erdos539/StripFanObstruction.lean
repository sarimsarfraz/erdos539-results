/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StripExactAlignment
import Erdos539.StripFans

namespace Erdos539Geometry
noncomputable section
open scoped Classical

/-- The literal strip makes the product of child fan sizes arbitrarily
larger than the parent fan, while all the reference-Gibbs costs are zero. -/
theorem gibbsStrip_zero_cost_fan_obstruction {R : ℝ} (hR : 0 ≤ R) :
    ∃ T : ℕ, ∃ hT : 2 ≤ T,
      projectionReferenceDrift (gibbsStrip T (3 * T)) stripProjection
        (uniformReference (gibbsStrip T (3 * T))) (uniformReference_pos (gibbsStrip_nonempty (by omega) _)) = 0 ∧
      meanImageLiftSlack (gibbsStrip T (3 * T)) stripProjection
        (uniformReference (gibbsStrip T (3 * T))) (uniformReference_pos (gibbsStrip_nonempty (by omega) _)) = 0 ∧
      projectionEndpointDrift (gibbsStrip T (3 * T)) stripProjection
        (uniformReference (gibbsStrip T (3 * T))) = 0 ∧
      meanFiberEndpointDrift (gibbsStrip T (3 * T)) stripProjection
        (uniformReference (gibbsStrip T (3 * T))) = 0 ∧
      meanImageAutocorrelationDistance (gibbsStrip T (3 * T)) stripProjection
        (uniformReference (gibbsStrip T (3 * T))) (uniformReference_pos (gibbsStrip_nonempty (by omega) _)) = 0 ∧
      ∀ y : (gibbsStrip T (3 * T)).image stripProjection,
        R * (maxFan (integerRealSet (gibbsStrip T (3 * T))) : ℝ) <
          (maxFan (((gibbsStrip T (3 * T)).image stripProjection).image
            (fun z : ℤ ↦ fun _ : Unit ↦ (z : ℝ))) : ℝ) *
          maxFan (integerRealSet (fiber (gibbsStrip T (3 * T)) stripProjection y.val)) := by
  obtain ⟨T, hT⟩ := exists_nat_gt (max 2 (2 * R))
  have ht2 : (2 : ℝ) < T := (le_max_left _ _).trans_lt hT
  have ht : 0 < T := by exact_mod_cast (lt_trans (by norm_num : (0 : ℝ) < 2) ht2)
  have hH : 2 * (T : ℤ) < 3 * T := by omega
  have hr : 2 * R < (T : ℝ) := (le_max_right _ _).trans_lt hT
  refine ⟨T, by exact_mod_cast ht2.le, (gibbsStrip_cut_costs_zero ht hH).1,
    (gibbsStrip_cut_costs_zero ht hH).2, (gibbsStrip_endpoint_costs_zero ht hH).1,
    (gibbsStrip_endpoint_costs_zero ht hH).2, gibbsStrip_alignment_cost_zero ht hH, ?_⟩
  intro y
  rw [← Nat.cast_mul, gibbsStrip_fan_product ht (by omega), Nat.cast_pow, gibbsStrip_maxFan_real ht hH]
  have htp : (0 : ℝ) < T := by exact_mod_cast ht
  have hmul := mul_pos (sub_pos.mpr hr) (sq_pos_of_pos htp)
  have hRT := mul_nonneg hR htp.le
  nlinarith

end
end Erdos539Geometry
