/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.MaskedProjection
import Mathlib.Data.Fintype.Powerset

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι : Type*} [Fintype ι]
local instance projectionCandidatesDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- All nonempty subsets of all coordinate projections of the parent,
with projected points zero-filled in the parent ambient space. -/
def projectionCandidates (S : Finset (ι → ℝ)) :
    Finset (Finset ι × Finset (ι → ℝ)) :=
  Finset.univ.biUnion fun I : Finset ι ↦
    ((maskedProjection S I).powerset.filter Finset.Nonempty).image (fun T ↦ (I, T))

@[simp] theorem mem_projectionCandidates {S T : Finset (ι → ℝ)} {I : Finset ι} :
    (I, T) ∈ projectionCandidates S ↔ T.Nonempty ∧ T ⊆ maskedProjection S I := by
  simp only [projectionCandidates, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_image, Finset.mem_filter, Finset.mem_powerset, Prod.mk.injEq]
  constructor
  · rintro ⟨J, A, ⟨hA, hne⟩, hJI, hAT⟩
    subst J
    subst A
    exact ⟨hne, hA⟩
  · rintro ⟨hne, hT⟩
    exact ⟨I, T, ⟨hT, hne⟩, rfl, rfl⟩

theorem parent_mem_projectionCandidates {S : Finset (ι → ℝ)} (hS : S.Nonempty) :
    (Finset.univ, S) ∈ projectionCandidates S := by
  rw [mem_projectionCandidates, maskedProjection_univ]
  exact ⟨hS, Finset.Subset.refl S⟩

theorem singleton_mem_projectionCandidates {S : Finset (ι → ℝ)} (hS : S.Nonempty) :
    (∅, {0}) ∈ projectionCandidates S := by
  rw [mem_projectionCandidates, maskedProjection_empty_coordinates hS]
  exact ⟨Finset.singleton_nonempty _, Finset.Subset.refl _⟩

theorem projectionCandidates_nonempty {S : Finset (ι → ℝ)} (hS : S.Nonempty) :
    (projectionCandidates S).Nonempty := ⟨_, parent_mem_projectionCandidates hS⟩

/-- Closure under actual subsets, without changing the coordinate mask. -/
theorem projectionCandidates_subset {S T A : Finset (ι → ℝ)} {I : Finset ι}
    (hT : (I, T) ∈ projectionCandidates S) (hA : A.Nonempty) (hAT : A ⊆ T) :
    (I, A) ∈ projectionCandidates S := by
  exact mem_projectionCandidates.mpr ⟨hA, hAT.trans (mem_projectionCandidates.mp hT).2⟩

/-- Closure under further coordinate projections. Masks retain the original
coordinate labels; no new ambient copy or rank model is introduced. -/
theorem projectionCandidates_project_subset {S T A : Finset (ι → ℝ)} {I J : Finset ι}
    (hT : (I, T) ∈ projectionCandidates S) (hA : A.Nonempty) (hAT : A ⊆ T) (hJI : J ⊆ I) :
    (J, maskedProjection A J) ∈ projectionCandidates S := by
  apply mem_projectionCandidates.mpr
  exact ⟨maskedProjection_nonempty.mpr hA,
    maskedProjection_subset_parent (hAT.trans (mem_projectionCandidates.mp hT).2) hJI⟩

theorem projectionCandidates_card_le {S T : Finset (ι → ℝ)} {I : Finset ι}
    (hT : (I, T) ∈ projectionCandidates S) : T.card ≤ S.card :=
  (Finset.card_le_card (mem_projectionCandidates.mp hT).2).trans (maskedProjection_card_le S I)

theorem projectionCandidates_palette_le {S T : Finset (ι → ℝ)} {I : Finset ι}
    (hT : (I, T) ∈ projectionCandidates S) : (posDiff T).card ≤ (posDiff S).card :=
  (Finset.card_le_card (posDiff_mono (mem_projectionCandidates.mp hT).2)).trans
    (posDiff_maskedProjection_card_le S I)

end
end Erdos539Geometry
