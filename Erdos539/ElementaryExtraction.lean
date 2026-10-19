/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.DownsetExtraction
import Erdos539.PrefixUniform

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical

/-- Polynomial-cost extraction of an actual uniform original-coordinate tree.
The compressed downset is used only for counting feasible branching profiles. -/
theorem exists_prefixUniform_extraction {d : ℕ} {S : Finset (Fin d → ℝ)}
    (hS : S.Nonempty) {K : ℝ} (hK : 1 ≤ K)
    (hDiff : ((S - S).card : ℝ) ≤ K * S.card) :
    ∃ (T : Finset (Fin d → ℝ)) (a : Fin d → ℕ), T ⊆ S ∧ PrefixUniform d T a ∧
      (S.card : ℝ) / (1024 * K ^ 10) ≤ T.card ∧
      (activeCoordinates a).card ≤ extractionSupport (K ^ 2) ∧
      (T : Set (Fin d → ℝ)).InjOn (project (activeCoordinates a)) := by
  have hsum := sumset_card_le_of_difference_doubling hS hDiff
  have hdown : NatDownset (feasibleProfiles d S) := fun _ _ hb hab ↦
    feasibleProfiles_downward d S hb hab
  have hprof : (feasibleProfiles d S).Nonempty := feasibleProfiles_nonempty_iff.mpr hS
  have hσ : (1 : ℝ) ≤ K ^ 2 := by nlinarith
  have hcompress : ((feasibleProfiles d S + feasibleProfiles d S).card : ℝ) ≤
      K ^ 2 * (feasibleProfiles d S).card := by
    rw [feasibleProfiles_card]
    have hc : ((feasibleProfiles d S + feasibleProfiles d S).card : ℝ) ≤ (S + S).card := by
      exact_mod_cast feasibleProfiles_sum_card_le d S
    exact hc.trans hsum
  obtain ⟨a, ha, har, hvol⟩ := exists_large_downset_box hdown hprof hσ hcompress
  obtain ⟨T, hTS, hTa⟩ := exists_prefixUniform_subset d S ha
  refine ⟨T, a, hTS, hTa, ?_, har, hTa.project_injOn⟩
  rw [feasibleProfiles_card] at hvol
  simpa only [hTa.card, boxVolume, ← pow_mul, show 2 * 5 = 10 from rfl] using hvol

end
end Erdos539Geometry
