/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CriticalCoreTheorem

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*} [Fintype ι]
local instance criticalCorePotentialDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

namespace IsProjectionCriticalCore
variable {S T : Finset (ι → ℝ)} {I : Finset ι} {b : ℝ}

/-- Root potential is nonnegative on the actual finite candidate family. -/
theorem candidate_potential_nonneg (h : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    {J : Finset ι} {A : Finset (ι → ℝ)} (hA : (J, A) ∈ projectionCandidates S) :
    0 ≤ rootPotential b (posDiff T).card (energyNorm T) (posDiff A).card (energyNorm A) :=
  rootPotential_nonneg_of_minimal hb (h.2.1 (J, A) hA)

/-- The inherited comparison keeps the exact root-referenced potential
cost of the intermediate candidate. No new optimizer is substituted. -/
theorem inherited_palette_bound (h : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    {JA JB : Finset ι} {A B : Finset (ι → ℝ)}
    (hA : (JA, A) ∈ projectionCandidates S) (hB : (JB, B) ∈ projectionCandidates S) :
    Real.exp (-rootPotential b (posDiff T).card (energyNorm T) (posDiff B).card (energyNorm B)) *
        (posDiff B).card * (energyNorm A / energyNorm B) ^ criticalAlpha b ≤ (posDiff A).card := by
  have hneA := (mem_projectionCandidates.mp hA).1
  have hneB := (mem_projectionCandidates.mp hB).1
  have hqA : (0 : ℝ) < (posDiff A).card := by exact_mod_cast posDiff_card_pos hneA
  have hqB : (0 : ℝ) < (posDiff B).card := by exact_mod_cast posDiff_card_pos hneB
  exact rootPotential_inherited hqB (energyNorm_pos hneB) hqA (energyNorm_pos hneA)
    (h.candidate_potential_nonneg hb hA)

theorem singleton_potential_bounds (h : IsProjectionCriticalCore S b I T)
    (hS : S.Nonempty) (hb : 0 < b) :
    0 ≤ rootPotential b (posDiff T).card (energyNorm T) 1 1 ∧
      rootPotential b (posDiff T).card (energyNorm T) 1 1 ≤ Real.log (energyNorm T) / (2 * b) := by
  have hq : (0 : ℝ) < (posDiff T).card := by exact_mod_cast posDiff_card_pos h.nonempty
  have hm := h.2.1 (∅, {0}) (singleton_mem_projectionCandidates hS)
  simp only [projectionCandidateScore, posDiff_singleton, Finset.card_singleton,
    Nat.cast_one, energyNorm_singleton] at hm
  exact rootPotential_singleton_bounds hb hq (energyNorm_pos h.nonempty)
    (energyNorm_le_palette_sq h.nonempty) hm

end IsProjectionCriticalCore
end
end Erdos539Geometry
