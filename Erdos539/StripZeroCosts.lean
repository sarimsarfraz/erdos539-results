/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StripPartitions
import Erdos539.GibbsFiberDrift
import Erdos539.GibbsAutocorrelationStability

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

theorem gibbsStrip_referenceDeficit {T : ℕ} (hT : 0 < T) {H : ℤ} (hH : 2 * (T : ℤ) < H) :
    referenceDeficit (gibbsStrip T H) (uniformReference (gibbsStrip T H)) =
      -3 * Real.log (stripIntervalPartition T) := by
  rw [referenceDeficit, gibbsStrip_referencePartition hT hH, Real.log_pow]
  norm_num

theorem gibbsStrip_projectedDeficit {T : ℕ} (hT : 0 < T) {H : ℤ} (hH : 2 * (T : ℤ) < H) :
    referenceDeficit ((gibbsStrip T H).image stripProjection)
      (finitePush (uniformReference (gibbsStrip T H)) (imageEndpoint (gibbsStrip T H) stripProjection)) =
        -2 * Real.log (stripIntervalPartition T) := by
  rw [referenceDeficit, gibbsStrip_projectedPartition hT hH, Real.log_pow]
  norm_num

theorem gibbsStrip_meanFiberDeficit {T : ℕ} (hT : 0 < T) {H : ℤ} (hH : 2 * (T : ℤ) < H) :
    meanFiberReferenceDeficit (gibbsStrip T H) stripProjection (uniformReference (gibbsStrip T H)) =
      -Real.log (stripIntervalPartition T) := by
  simp only [meanFiberReferenceDeficit, referenceDeficit]
  simp_rw [gibbsStrip_fiberPartition hT hH]
  rw [← Finset.sum_mul, finitePush_sum,
    referenceEndpoint_sum (gibbsStrip_nonempty hT H) (uniformReference_pos (gibbsStrip_nonempty hT H)), one_mul]

/-- Both nonnegative costs at the actual first-coordinate cut vanish. -/
theorem gibbsStrip_cut_costs_zero {T : ℕ} (hT : 0 < T) {H : ℤ} (hH : 2 * (T : ℤ) < H) :
    projectionReferenceDrift (gibbsStrip T H) stripProjection (uniformReference (gibbsStrip T H))
      (uniformReference_pos (gibbsStrip_nonempty hT H)) = 0 ∧
    meanImageLiftSlack (gibbsStrip T H) stripProjection (uniformReference (gibbsStrip T H))
      (uniformReference_pos (gibbsStrip_nonempty hT H)) = 0 := by
  have hS := gibbsStrip_nonempty hT H
  have hu := uniformReference_pos hS
  have he := referenceDeficit_cut_decomposition hS stripProjection (uniformReference _) hu
  rw [gibbsStrip_referenceDeficit hT hH, gibbsStrip_projectedDeficit hT hH,
    gibbsStrip_meanFiberDeficit hT hH] at he
  have hD := projectionReferenceDrift_nonneg hS stripProjection (uniformReference _) hu
  have hK := meanImageLiftSlack_nonneg hS stripProjection (uniformReference _) hu
  constructor <;> linarith

/-- The actual projected endpoint drift and mean actual fiber drift vanish. -/
theorem gibbsStrip_endpoint_costs_zero {T : ℕ} (hT : 0 < T) {H : ℤ} (hH : 2 * (T : ℤ) < H) :
    projectionEndpointDrift (gibbsStrip T H) stripProjection (uniformReference (gibbsStrip T H)) = 0 ∧
    meanFiberEndpointDrift (gibbsStrip T H) stripProjection (uniformReference (gibbsStrip T H)) = 0 := by
  have hS := gibbsStrip_nonempty hT H
  have hu := uniformReference_pos hS
  have h := endpointDrifts_le_cut_charge hS stripProjection (uniformReference _) hu
  rw [(gibbsStrip_cut_costs_zero hT hH).1, (gibbsStrip_cut_costs_zero hT hH).2] at h
  have hP := projectionEndpointDrift_nonneg hS stripProjection (uniformReference _) hu
  have hF := meanFiberEndpointDrift_nonneg hS stripProjection (uniformReference _) hu
  constructor <;> linarith

theorem gibbsStrip_alignment_cost_zero {T : ℕ} (hT : 0 < T) {H : ℤ} (hH : 2 * (T : ℤ) < H) :
    meanImageAutocorrelationDistance (gibbsStrip T H) stripProjection (uniformReference (gibbsStrip T H))
      (uniformReference_pos (gibbsStrip_nonempty hT H)) = 0 := by
  have hS := gibbsStrip_nonempty hT H
  have hu := uniformReference_pos hS
  have h := meanImageAutocorrelationDistance_le hS stripProjection (uniformReference _) hu
  rw [(gibbsStrip_cut_costs_zero hT hH).2, mul_zero] at h
  exact le_antisymm h (meanImageAutocorrelationDistance_nonneg _ _ _ _)

theorem gibbsStrip_deficit_lt {T : ℕ} (hT : 0 < T) {H : ℤ} (hH : 2 * (T : ℤ) < H) :
    referenceDeficit (gibbsStrip T H) (uniformReference (gibbsStrip T H)) < 3 * Real.log (3 / 2 : ℝ) := by
  rw [gibbsStrip_referenceDeficit hT hH]
  have hl := Real.log_lt_log (by norm_num : (0 : ℝ) < 2 / 3) (stripIntervalPartition_gt_two_thirds hT)
  have hi : Real.log (3 / 2 : ℝ) = -Real.log (2 / 3 : ℝ) := by
    rw [show (3 / 2 : ℝ) = (2 / 3 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [hi]
  linarith

end
end Erdos539Geometry
