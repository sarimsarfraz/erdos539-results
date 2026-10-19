/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CriticalColorDeletion
import Erdos539.InheritedDeletionMass

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*} [Fintype ι]
local instance criticalColorMassDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

omit [Fintype ι] in
theorem KillsColors.card_lt_palette_of_nonzero {B V R : Finset (ι → ℝ)}
    (h : KillsColors B V R) (hB : B.Nonempty) (hR : 0 ∉ R) :
    (R.card : ℝ) < (posDiff B).card := by
  obtain ⟨a, ha⟩ := hB
  have hzero : (0 : ι → ℝ) ∈ posDiff B := mem_posDiff.mpr ⟨a, ha, a, ha, pdiff_self a⟩
  have hsub : insert 0 R ⊆ posDiff B := Finset.insert_subset_iff.mpr ⟨hzero, h.1⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hR] at hc
  exact_mod_cast (show R.card < (posDiff B).card by omega)

namespace IsProjectionCriticalCore
variable {S T B V R : Finset (ι → ℝ)} {I J : Finset ι} {b : ℝ}

/-- The exact logarithmic inherited mass threshold for deletion of actual
nonzero colors from an actual projected descendant, including an empty
remaining support. -/
theorem color_deletion_mass_lower (h : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    (hB : (J, B) ∈ projectionCandidates S) (hVB : V ⊆ B)
    (hkill : KillsColors B V R) (hR : 0 ∉ R)
    {f : B → ℝ} (hf : f ∈ admissibleWeights B)
    (hE : weightedEnergy B (extendWeight B f) = energyNorm B) :
    max 0 (1 - (Real.exp (rootPotential b (posDiff T).card (energyNorm T)
        (posDiff B).card (energyNorm B)) * (1 - (R.card : ℝ) / (posDiff B).card)) ^
          (1 / (2 * criticalAlpha b))) ≤ weightSquareSum V (extendWeight B f) := by
  have hBne := (mem_projectionCandidates.mp hB).1
  have hα : 0 < criticalAlpha b := by unfold criticalAlpha; positivity
  have hq : (0 : ℝ) < (posDiff T).card := by exact_mod_cast posDiff_card_pos h.nonempty
  have hqB : (0 : ℝ) < (posDiff B).card := by exact_mod_cast posDiff_card_pos hBne
  have hμ : 0 ≤ weightSquareSum V (extendWeight B f) := weightSquareSum_nonneg _ _
  have hμ1 : weightSquareSum V (extendWeight B f) ≤ 1 := by
    have hl := Finset.sum_le_sum_of_subset_of_nonneg (f := fun x ↦ extendWeight B f x ^ 2)
      hVB (fun x _ _ ↦ sq_nonneg (extendWeight B f x))
    change weightSquareSum V (extendWeight B f) ≤ weightSquareSum B (extendWeight B f) at hl
    rwa [weightSquareSum_extend, hf.2] at hl
  exact inherited_deletion_mass_lower hα hq (energyNorm_pos h.nonempty) hqB
    (energyNorm_pos hBne) (hkill.card_lt_palette_of_nonzero hBne hR) hμ hμ1 rfl
    (h.color_deletion_retention hb hB hVB hkill hf hE)

end IsProjectionCriticalCore
end
end Erdos539Geometry
