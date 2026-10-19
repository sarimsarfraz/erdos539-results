/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CoordinateHan
import Erdos539.FiniteEntropyFactors

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*}
local instance nestedProjectionEntropyIndexDecidableEq {κ : Type*} (J : Finset κ) :
    DecidableEq J := Classical.decEq _
local instance nestedProjectionEntropyDecidableEq {κ : Type*} : DecidableEq (κ → ℝ) := Classical.decEq _
local instance nestedProjectionEntropyProjectionDecidableEq {κ : Type*}
    (S : Finset (κ → ℝ)) (I : Finset κ) : DecidableEq (projection S I) := Classical.decEq _

/-- Deleting one coordinate after a projection has exactly the same
entropy as deleting that original coordinate from the root mask. -/
theorem nested_outside_entropy (S : Finset (ι → ℝ)) (ν : S → ℝ)
    (hν : ∀ a, 0 ≤ ν a) (J : Finset ι) (i : J) :
    finiteEntropy (finitePush (finitePush ν (projectEndpoint S J))
      (outsideEndpoint (projection S J) i)) =
      coordinateProjectionEntropy S ν (J.erase i.val) := by
  rw [finitePush_comp]
  apply finiteEntropy_push_eq_of_fibers ν hν
  intro a b
  constructor
  · intro he
    apply Subtype.ext
    funext j
    have hj := Finset.mem_erase.mp j.property
    let t : J := ⟨j.val, hj.2⟩
    have ht : t ≠ i := fun h ↦ hj.1 (congrArg Subtype.val h)
    exact congrFun (congrArg Subtype.val he) ⟨t, Finset.mem_erase.mpr ⟨ht, Finset.mem_univ t⟩⟩
  · intro he
    apply Subtype.ext
    funext j
    have hj := Finset.mem_erase.mp j.property
    have hne : j.val.val ≠ i.val := fun h ↦ hj.1 (Subtype.ext h)
    exact congrFun (congrArg Subtype.val he) ⟨j.val.val, Finset.mem_erase.mpr ⟨hne, j.val.property⟩⟩

theorem projected_coordinateConditionalEntropy (S : Finset (ι → ℝ)) (ν : S → ℝ)
    (hν : ∀ a, 0 ≤ ν a) (J : Finset ι) (i : J) :
    coordinateConditionalEntropy (projection S J) (finitePush ν (projectEndpoint S J)) i =
      coordinateProjectionEntropy S ν J - coordinateProjectionEntropy S ν (J.erase i.val) := by
  unfold coordinateConditionalEntropy
  rw [nested_outside_entropy S ν hν J i]
  rfl

end
end Erdos539Geometry
