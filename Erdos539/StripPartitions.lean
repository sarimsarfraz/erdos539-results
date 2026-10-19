/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StripProjection
import Erdos539.UniformImageFibers

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

def stripIntervalPartition (T : ℕ) : ℝ := (2 * (T : ℝ) ^ 2 + 1) / (3 * (T : ℝ) ^ 2)

theorem stripIntervalPartition_pos {T : ℕ} (hT : 0 < T) : 0 < stripIntervalPartition T := by
  unfold stripIntervalPartition
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  positivity

theorem stripIntervalPartition_gt_two_thirds {T : ℕ} (hT : 0 < T) :
    (2 / 3 : ℝ) < stripIntervalPartition T := by
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 3 * (T : ℝ) ^ 2)).mpr
  nlinarith

theorem interval_referencePartition {T : ℕ} (hT : 0 < T) :
    referencePartition (scalarInterval T) (uniformReference (scalarInterval T)) = stripIntervalPartition T := by
  rw [referencePartition_uniform (scalarInterval_nonempty hT), countingEnergy_scalarInterval,
    scalarInterval_card]
  have ht : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  unfold stripIntervalPartition
  field_simp

theorem gibbsStrip_referencePartition {T : ℕ} (hT : 0 < T) {H : ℤ} (hH : 2 * (T : ℤ) < H) :
    referencePartition (gibbsStrip T H) (uniformReference (gibbsStrip T H)) = stripIntervalPartition T ^ 3 := by
  rw [referencePartition_uniform (gibbsStrip_nonempty hT H), gibbsStrip_countingEnergy hH,
    gibbsStrip_card (by omega), countingEnergy_scalarInterval]
  push_cast
  have ht : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  unfold stripIntervalPartition
  field_simp

theorem gibbsStrip_uniform_marginal {T : ℕ} (hT : 0 < T) {H : ℤ} (hH : (T : ℤ) < H) :
    finitePush (uniformReference (gibbsStrip T H)) (imageEndpoint (gibbsStrip T H) stripProjection) =
      uniformReference ((gibbsStrip T H).image stripProjection) := by
  apply uniformReference_image_of_constant_fibers (gibbsStrip_nonempty hT H) stripProjection
    (gibbsStrip_fiber_card hT hH)
  rw [gibbsStrip_card hH, gibbsStrip_projection hT H, stripProjected_card hH]
  ring

theorem gibbsStrip_projectedPartition {T : ℕ} (hT : 0 < T) {H : ℤ} (hH : 2 * (T : ℤ) < H) :
    referencePartition ((gibbsStrip T H).image stripProjection)
      (finitePush (uniformReference (gibbsStrip T H)) (imageEndpoint (gibbsStrip T H) stripProjection)) =
        stripIntervalPartition T ^ 2 := by
  rw [gibbsStrip_uniform_marginal hT (by omega),
    referencePartition_uniform ((gibbsStrip_nonempty hT H).image _),
    gibbsStrip_projection hT H, stripProjected_countingEnergy hH,
    stripProjected_card (by omega), countingEnergy_scalarInterval]
  push_cast
  have ht : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  unfold stripIntervalPartition
  field_simp

theorem gibbsStrip_fiberPartition {T : ℕ} (hT : 0 < T) {H : ℤ} (hH : 2 * (T : ℤ) < H)
    (y : (gibbsStrip T H).image stripProjection) :
    referencePartition (fiber (gibbsStrip T H) stripProjection y.val)
      (imageFiberReference (gibbsStrip T H) stripProjection (uniformReference (gibbsStrip T H)) y) =
        stripIntervalPartition T := by
  rw [uniformReference_imageFiber (gibbsStrip_nonempty hT H),
    referencePartition_uniform (imageFiber_nonempty _ _ y), gibbsStrip_fiber_countingEnergy hT hH,
    gibbsStrip_fiber_card hT (by omega), countingEnergy_scalarInterval]
  have ht : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  unfold stripIntervalPartition
  field_simp

end
end Erdos539Geometry
