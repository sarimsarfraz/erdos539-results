/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CriticalPaletteInversion

namespace Erdos539Geometry
noncomputable section

/-- The exact mass threshold encoded by inherited root criticality.
The potential identity is explicit, and all zero/one mass cases are covered. -/
theorem inherited_deletion_mass_lower {α q lam qB lamB r μ δ : ℝ}
    (hα : 0 < α) (hq : 0 < q) (hlam : 0 < lam) (hqB : 0 < qB) (hlamB : 0 < lamB)
    (hr : r < qB) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hδ : δ = Real.log qB - α * Real.log lamB - (Real.log q - α * Real.log lam))
    (hret : lamB * (1 - μ) ^ 2 ≤ lam * ((qB - r) / q) ^ (1 / α)) :
    max 0 (1 - (Real.exp δ * (1 - r / qB)) ^ (1 / (2 * α))) ≤ μ := by
  have ht : 0 < 1 - r / qB := sub_pos.mpr ((div_lt_one hqB).mpr hr)
  have hz : 0 < Real.exp δ * (1 - r / qB) := mul_pos (Real.exp_pos _) ht
  have hp : 0 < (Real.exp δ * (1 - r / qB)) ^ (1 / (2 * α)) := Real.rpow_pos_of_pos hz _
  apply max_le hμ
  by_cases hμeq : μ = 1
  · rw [hμeq]
    linarith
  · have hrem : 0 < 1 - μ := sub_pos.mpr (lt_of_le_of_ne hμ1 hμeq)
    have hqr : 0 < qB - r := sub_pos.mpr hr
    have hl := Real.log_le_log (mul_pos hlamB (sq_pos_of_pos hrem)) hret
    rw [Real.log_mul hlamB.ne' (sq_pos_of_pos hrem).ne', Real.log_pow,
      Real.log_mul hlam.ne' (Real.rpow_pos_of_pos (div_pos hqr hq) _).ne',
      Real.log_rpow (div_pos hqr hq), Real.log_div hqr.ne' hq.ne'] at hl
    norm_num only [Nat.cast_ofNat] at hl
    have hm := mul_le_mul_of_nonneg_left hl hα.le
    have hinv : α * (1 / α) = 1 := by field_simp
    rw [mul_add, mul_add, ← mul_assoc α (1 / α), hinv, one_mul] at hm
    have hratio : 1 - r / qB = (qB - r) / qB := by field_simp
    have hbound : 1 - μ ≤ (Real.exp δ * (1 - r / qB)) ^ (1 / (2 * α)) := by
      apply (Real.log_le_log_iff hrem hp).mp
      rw [Real.log_rpow hz]
      have hcancel : (2 * α) * (1 / (2 * α)) = 1 := by field_simp
      have hscaled : (2 * α) * Real.log (1 - μ) ≤
          (2 * α) * ((1 / (2 * α)) * Real.log (Real.exp δ * (1 - r / qB))) := by
        rw [← mul_assoc, hcancel, one_mul, Real.log_mul (Real.exp_pos _).ne' ht.ne',
          Real.log_exp, hratio, Real.log_div hqr.ne' hqB.ne']
        nlinarith only [hm, hδ]
      have hcoef : 0 < 2 * α := by positivity
      nlinarith only [hscaled, hcoef]
    linarith

/-- The mass lower bound is positive exactly below the single- or
multi-color inheritance threshold. This is a limitation of this bound,
not a counterexample to any stronger geometric statement. -/
theorem inherited_deletion_bound_positive_iff {α qB r δ : ℝ}
    (hα : 0 < α) (hqB : 0 < qB) (hr : r < qB) :
    0 < max 0 (1 - (Real.exp δ * (1 - r / qB)) ^ (1 / (2 * α))) ↔
      δ < Real.log (qB / (qB - r)) := by
  have ht : 0 < 1 - r / qB := sub_pos.mpr ((div_lt_one hqB).mpr hr)
  have hz : 0 < Real.exp δ * (1 - r / qB) := mul_pos (Real.exp_pos _) ht
  have hp : 0 < (Real.exp δ * (1 - r / qB)) ^ (1 / (2 * α)) := Real.rpow_pos_of_pos hz _
  have hqr : 0 < qB - r := sub_pos.mpr hr
  have hratio : 1 - r / qB = (qB - r) / qB := by field_simp
  rw [lt_max_iff]
  simp only [lt_self_iff_false, false_or, sub_pos]
  rw [← Real.log_lt_log_iff hp (by norm_num : (0 : ℝ) < 1), Real.log_one,
    Real.log_rpow hz, Real.log_mul (Real.exp_pos _).ne' ht.ne', Real.log_exp,
    hratio, Real.log_div hqr.ne' hqB.ne', Real.log_div hqB.ne' hqr.ne']
  have hpos : 0 < 1 / (2 * α) := by positivity
  constructor
  · intro h
    nlinarith only [h, hpos]
  · intro h
    exact mul_neg_of_pos_of_neg hpos (by linarith)

end
end Erdos539Geometry
