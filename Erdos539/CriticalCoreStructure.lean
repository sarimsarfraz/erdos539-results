/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CriticalCoreBounds
import Erdos539.EnergyPositiveSupport
import Erdos539.MaskedEnergy
import Erdos539.QuadrupleEntropy

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*} [Fintype ι]
local instance criticalCoreStructureDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

namespace IsProjectionCriticalCore
variable {S T : Finset (ι → ℝ)} {I : Finset ι} {b : ℝ}

/-- The first tie rule forces every exact maximizer of the actual core to
have full support. This conclusion is not part of the optimizer definition. -/
theorem optimizer_full_support (h : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    {f : T → ℝ} (hf : f ∈ admissibleWeights T)
    (hE : weightedEnergy T (extendWeight T f) = energyNorm T) : ∀ x, 0 < f x := by
  let A := positiveWeightSupport T f
  have hAT : A ⊆ T := positiveWeightSupport_subset T f
  have hA : A.Nonempty := positiveWeightSupport_nonempty hf
  have hnorm : energyNorm A = energyNorm T := energyNorm_positiveWeightSupport h.nonempty hf hE
  have hqA : (0 : ℝ) < (posDiff A).card := by exact_mod_cast posDiff_card_pos hA
  have hqle : ((posDiff A).card : ℝ) ≤ (posDiff T).card := by
    exact_mod_cast Finset.card_le_card (posDiff_mono hAT)
  have hscore : projectionCandidateScore b (I, A) = projectionCandidateScore b (I, T) := by
    apply le_antisymm
    · unfold projectionCandidateScore criticalLogScore
      rw [hnorm]
      exact sub_le_sub_right (mul_le_mul_of_nonneg_left (Real.log_le_log hqA hqle)
        (by positivity : 0 ≤ 2 * b)) _
    · exact h.compare_subset hA hAT
  have hcard := h.2.2.1 (I, A) (projectionCandidates_subset h.1 hA hAT) hscore
  have heq : A = T := Finset.eq_of_subset_of_card_le hAT hcard
  intro x
  have hx : x.val ∈ A := by rw [heq]; exact x.property
  have hp := (Finset.mem_filter.mp hx).2
  simpa only [extendWeight_mem] using hp

/-- The coordinate tie rule rules out every proper injective coordinate
projection. The energy comparison retains the actual old quadruples. -/
theorem no_injective_proper_projection (h : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    {J : Finset ι} (hJI : J ⊂ I) : ¬ Set.InjOn (maskCoordinates J) T := by
  intro hinj
  let A := maskedProjection T J
  have hA : A.Nonempty := maskedProjection_nonempty.mpr h.nonempty
  have hnorm : energyNorm A = energyNorm T := le_antisymm
    (h.projected_subset_norm_le hb h.nonempty (Finset.Subset.refl T) hJI.subset)
    (energyNorm_le_maskedProjection J hinj)
  have hqA : (0 : ℝ) < (posDiff A).card := by exact_mod_cast posDiff_card_pos hA
  have hqle : ((posDiff A).card : ℝ) ≤ (posDiff T).card := by
    exact_mod_cast posDiff_maskedProjection_card_le T J
  have hscore : projectionCandidateScore b (J, A) = projectionCandidateScore b (I, T) := by
    apply le_antisymm
    · unfold projectionCandidateScore criticalLogScore
      rw [hnorm]
      exact sub_le_sub_right (mul_le_mul_of_nonneg_left (Real.log_le_log hqA hqle)
        (by positivity : 0 ≤ 2 * b)) _
    · exact h.compare_projected_subset h.nonempty (Finset.Subset.refl T) hJI.subset
  have hcard : A.card = T.card := Finset.card_image_of_injOn hinj
  have hdim := h.2.2.2 (J, A)
    (projectionCandidates_project_subset h.1 h.nonempty (Finset.Subset.refl T) hJI.subset) hscore hcard
  exact (not_le_of_gt (Finset.card_lt_card hJI)) hdim

/-- Every retained coordinate has an actual axis-parallel pair in the core. -/
theorem axis_pair (h : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    {i : ι} (hi : i ∈ I) :
    ∃ x ∈ T, ∃ y ∈ T, x i ≠ y i ∧ ∀ j, j ≠ i → x j = y j := by
  have hn := h.no_injective_proper_projection hb (Finset.erase_ssubset hi)
  simp only [Set.InjOn] at hn
  push_neg at hn
  obtain ⟨x, hx, y, hy, heq, hxy⟩ := hn
  have hout : ∀ j, j ∉ I → x j = y j := by
    intro j hj
    rw [maskedProjection_zero_outside ((mem_projectionCandidates.mp h.1).2 hx) hj,
      maskedProjection_zero_outside ((mem_projectionCandidates.mp h.1).2 hy) hj]
  have he : ∀ j, j ≠ i → x j = y j := by
    intro j hji
    by_cases hj : j ∈ I
    · have herase : j ∈ I.erase i := Finset.mem_erase.mpr ⟨hji, hj⟩
      simpa only [maskCoordinates, if_pos herase] using congrFun heq j
    · exact hout j hj
  refine ⟨x, hx, y, hy, ?_, he⟩
  intro hiEq
  apply hxy
  funext j
  by_cases hji : j = i
  · simpa only [hji] using hiEq
  · exact he j hji

/-- The entropy-defect bounds now refer to an actual selected core and an
actual maximizing law, using the checked atom and palette estimates. -/
theorem entropy_defect_bounds (h : IsProjectionCriticalCore S b I T)
    (hS : S.Nonempty) (hb : 0 < b) {f : T → ℝ} (hf : f ∈ admissibleWeights T)
    (hE : weightedEnergy T (extendWeight T f) = energyNorm T) :
    0 ≤ finiteEntropy (fun x : T ↦ f x ^ 2) - Real.log (energyNorm T) ∧
      finiteEntropy (fun x : T ↦ f x ^ 2) - Real.log (energyNorm T) ≤
        (2 + 1 / b) * Real.log (paletteSurplus S) := by
  have hent := energyMaximizer_entropy_bounds h.nonempty hf hE
  refine ⟨sub_nonneg.mpr hent.1, ?_⟩
  have hN : (0 : ℝ) < T.card := by exact_mod_cast h.nonempty.card_pos
  have hsize := Real.log_le_log hN (by exact_mod_cast card_le_real_posDiff_sq h.nonempty :
    (T.card : ℝ) ≤ ((posDiff T).card : ℝ) ^ 2)
  rw [Real.log_pow] at hsize
  norm_num only [Nat.cast_ofNat] at hsize
  linarith [h.log_surplus hS hb]

end IsProjectionCriticalCore
end
end Erdos539Geometry
