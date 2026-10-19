/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ProjectionCandidates

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι : Type*} [Fintype ι]
local instance projectionCandidateLiftDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

/-- Every finite candidate really is the projection of a nonempty subset
of the original parent. This identifies the finite implementation with the
paper's projected-subset family. -/
theorem projectionCandidate_lifts {S T : Finset (ι → ℝ)} {I : Finset ι}
    (hT : (I, T) ∈ projectionCandidates S) :
    ∃ A ⊆ S, A.Nonempty ∧ maskedProjection A I = T := by
  let A := S.filter (fun x ↦ maskCoordinates I x ∈ T)
  have hAS : A ⊆ S := Finset.filter_subset _ _
  have heq : maskedProjection A I = T := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hx, rfl⟩ := mem_maskedProjection.mp hy
      exact (Finset.mem_filter.mp hx).2
    · intro hy
      obtain ⟨x, hx, hxy⟩ := mem_maskedProjection.mp ((mem_projectionCandidates.mp hT).2 hy)
      exact mem_maskedProjection.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hxy ▸ hy⟩, hxy⟩
  refine ⟨A, hAS, ?_, heq⟩
  apply (maskedProjection_nonempty (I := I)).mp
  rw [heq]
  exact (mem_projectionCandidates.mp hT).1

end
end Erdos539Geometry
