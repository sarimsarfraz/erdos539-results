/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FourMaskTrimming
import Erdos539.ProjectionEntropySupportBound
import Erdos539.ExposedProjectionBounds
import Erdos539.SignMasks

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι]
local instance fourMaskCutRealDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _
local instance fourMaskCutIndexDecidableEq (S : Finset (ι → ℝ)) (I : Finset ι) :
    DecidableEq (projection S I) := Classical.decEq _

/-- The six actual blocks give four physical cuts of the same law. Both
projection cardinalities are controlled, with the entropy deficit retained. -/
theorem four_mask_entropy_support_cuts {S : Finset (ι → ℝ)} (hS : S.Nonempty)
    (ν : S → ℝ) (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1)
    (A : Fin 4 → Finset ι) (c : Fin 4 → ℝ) (hc : ∀ k, 0 ≤ c k)
    (hcover : ∀ x, 1 ≤ ∑ k, if x ∈ A k then c k else 0)
    (hr : ∑ k, c k ≤ 2) (hmiss : ∀ i j, i ≠ j → ∃ x, x ∉ A i ∧ x ∉ A j)
    {h : ℝ} (hcard : ∀ v, Real.log (projection S (A v)).card ≤ h) :
    finiteEntropy ν ≤ 2 * h ∧ ∃ J : Fin 4 → Finset ι, ∀ v,
      J v ⊆ A v ∧ (J v).Nonempty ∧ (Finset.univ \ J v).Nonempty ∧
      Real.log (projection S (J v)).card ≤ h ∧
      Real.log (projection S (Finset.univ \ J v)).card ≤
        3 * h + Real.log (differences S).card - 2 * finiteEntropy ν := by
  have hw := (four_mask_cover_weights A c hc hcover hr hmiss).1
  have hH := coordinate_fractional_entropy_cover S ν hν hs A c hc hcover
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun v _ ↦
    mul_le_mul_of_nonneg_left ((coordinateProjectionEntropy_le_log_card hS ν hν hs (A v)).trans (hcard v)) (hc v))
  rw [← Finset.sum_mul, hw] at hsum
  obtain ⟨_, B, hB, _, hfull, htrim⟩ := four_mask_trim_to_k4 A c hc hcover hr hmiss
  let J := k4Star (B 0) (B 1) (B 2) (B 3) (B 4) (B 5)
  have hlogstar : ∀ v, Real.log (projection S (J v)).card ≤ h := by
    intro v
    have hmono : ((projection S (J v)).card : ℝ) ≤ (projection S (A v)).card := by
      exact_mod_cast projection_card_mono S (htrim v).1
    have hpos : (0 : ℝ) < (projection S (J v)).card := by
      obtain ⟨x, hx⟩ := hS
      have hp : (projection S (J v)).Nonempty := ⟨(projectEndpoint S (J v) ⟨x, hx⟩).val,
        (projectEndpoint S (J v) ⟨x, hx⟩).property⟩
      exact_mod_cast hp.card_pos
    exact (Real.log_le_log hpos hmono).trans (hcard v)
  have hstar : ∀ v, coordinateProjectionEntropy S ν (J v) ≤ h := fun v ↦
    (coordinateProjectionEntropy_le_log_card hS ν hν hs (J v)).trans (hlogstar v)
  refine ⟨hH.trans hsum, J, ?_⟩
  intro v
  have hJne : (J v).Nonempty := by
    fin_cases v <;> dsimp [J, k4Star]
    all_goals exact ((hB _).inl).inl
  have hCne : (Finset.univ \ J v).Nonempty := by
    rw [(htrim v).2]
    fin_cases v <;> dsimp [k4Triangle]
    all_goals exact ((hB _).inl).inl
  refine ⟨(htrim v).1, hJne, hCne, hlogstar v, ?_⟩
  have htri := k4_triangle_of_star_bounds (coordinateProjectionEntropy S ν)
    (coordinateProjectionEntropy_empty S ν hν hs) (coordinate_maskCMI_nonneg S ν hν)
    (B 0) (B 1) (B 2) (B 3) (B 4) (B 5) h hstar v
  rw [hfull, coordinateProjectionEntropy_univ] at htri
  have hcEnt := projection_log_card_le_entropy_deficit hS ν hν hs (Finset.univ \ J v)
  rw [(htrim v).2] at hcEnt
  rw [(htrim v).2]
  linarith

end
end Erdos539Geometry
