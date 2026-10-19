/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ProjectionCandidates
import Erdos539.TripleMinimum
import Erdos539.EnergyNormLower
import Erdos539.CriticalCoreEstimates

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*} [Fintype ι]
local instance criticalCoreSelectionDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- The paper's score on a literal projected-subset candidate. -/
def projectionCandidateScore (b : ℝ) (c : Finset ι × Finset (ι → ℝ)) : ℝ :=
  criticalLogScore b (posDiff c.2).card (energyNorm c.2)

/-- Actual projection criticality, including both tie rules. The finite
candidate family, and not a supplied abstract optimization premise, is fixed
by the original parent S. -/
def IsProjectionCriticalCore (S : Finset (ι → ℝ)) (b : ℝ)
    (I : Finset ι) (T : Finset (ι → ℝ)) : Prop :=
  (I, T) ∈ projectionCandidates S ∧
    (∀ c ∈ projectionCandidates S, projectionCandidateScore b (I, T) ≤ projectionCandidateScore b c) ∧
    (∀ c ∈ projectionCandidates S, projectionCandidateScore b c = projectionCandidateScore b (I, T) →
      T.card ≤ c.2.card) ∧
    (∀ c ∈ projectionCandidates S, projectionCandidateScore b c = projectionCandidateScore b (I, T) →
      c.2.card = T.card → I.card ≤ c.1.card)

theorem exists_projectionCriticalCore {S : Finset (ι → ℝ)} (hS : S.Nonempty) (b : ℝ) :
    ∃ I T, IsProjectionCriticalCore S b I T := by
  obtain ⟨c, hc, hmin, hsize, hdim⟩ := exists_three_stage_minimum
    (projectionCandidates S) (projectionCandidates_nonempty hS) (projectionCandidateScore b)
    (fun c ↦ c.2.card) (fun c ↦ c.1.card)
  exact ⟨c.1, c.2, hc, hmin, hsize, hdim⟩

namespace IsProjectionCriticalCore

variable {S T : Finset (ι → ℝ)} {I : Finset ι} {b : ℝ}

theorem nonempty (h : IsProjectionCriticalCore S b I T) : T.Nonempty :=
  (mem_projectionCandidates.mp h.1).1

theorem card_le (h : IsProjectionCriticalCore S b I T) : T.card ≤ S.card :=
  projectionCandidates_card_le h.1

theorem palette_le (h : IsProjectionCriticalCore S b I T) :
    (posDiff T).card ≤ (posDiff S).card := projectionCandidates_palette_le h.1

theorem compare_parent (h : IsProjectionCriticalCore S b I T) (hS : S.Nonempty) :
    criticalLogScore b (posDiff T).card (energyNorm T) ≤
      criticalLogScore b (posDiff S).card (energyNorm S) :=
  h.2.1 (Finset.univ, S) (parent_mem_projectionCandidates hS)

theorem compare_projected_subset (h : IsProjectionCriticalCore S b I T)
    {A : Finset (ι → ℝ)} (hA : A.Nonempty) (hAT : A ⊆ T) {J : Finset ι} (hJI : J ⊆ I) :
    criticalLogScore b (posDiff T).card (energyNorm T) ≤
      criticalLogScore b (posDiff (maskedProjection A J)).card (energyNorm (maskedProjection A J)) :=
  h.2.1 (J, maskedProjection A J) (projectionCandidates_project_subset h.1 hA hAT hJI)

theorem compare_subset (h : IsProjectionCriticalCore S b I T)
    {A : Finset (ι → ℝ)} (hA : A.Nonempty) (hAT : A ⊆ T) :
    criticalLogScore b (posDiff T).card (energyNorm T) ≤
      criticalLogScore b (posDiff A).card (energyNorm A) :=
  h.2.1 (I, A) (projectionCandidates_subset h.1 hA hAT)

end IsProjectionCriticalCore
end
end Erdos539Geometry
