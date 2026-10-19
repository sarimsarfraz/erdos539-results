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
local instance coordinateEntropySubmodularDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _
local instance coordinateEntropySubmodularProjectionDecidableEq
    (S : Finset (ι → ℝ)) (I : Finset ι) : DecidableEq (projection S I) := Classical.decEq _

theorem coordinateProjectionEntropy_mono (S : Finset (ι → ℝ)) (ν : S → ℝ)
    (hν : ∀ a, 0 ≤ ν a) {I J : Finset ι} (hIJ : I ⊆ J) :
    coordinateProjectionEntropy S ν I ≤ coordinateProjectionEntropy S ν J := by
  have h := finiteEntropy_push_le (finitePush ν (projectEndpoint S J))
    (restrictProjectedEndpoint S hIJ) (finitePush_nonneg ν _ hν)
  rw [finitePush_comp, restrictProjectedEndpoint_comp] at h
  exact h

theorem coordinateProjectionEntropy_empty (S : Finset (ι → ℝ)) (ν : S → ℝ)
    (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1) :
    coordinateProjectionEntropy S ν ∅ = 0 := by
  have he := finiteEntropy_push_eq_of_fibers ν hν (projectEndpoint S ∅)
    (fun _ : S ↦ Unit.unit) (fun a b ↦ by
      constructor
      · intro _; rfl
      · intro _; apply Subtype.ext; funext j; exact (Finset.notMem_empty _ j.property).elim)
  change finiteEntropy (finitePush ν (projectEndpoint S ∅)) = 0
  rw [he]
  have hp : finitePush ν (fun _ : S ↦ Unit.unit) = fun _ : Unit ↦ (1 : ℝ) := by
    funext u
    cases u
    simp only [finitePush, ite_true]
    exact hs
  rw [hp]
  simp [finiteEntropy]

/-- The pair of a coordinate and a mask is exactly their union as an
observation of the original law, including overlapping masks. -/
theorem coordinate_pair_entropy (S : Finset (ι → ℝ)) (ν : S → ℝ)
    (hν : ∀ a, 0 ≤ ν a) (i : ι) (J : Finset ι) :
    finiteEntropy (finitePush ν (fun a ↦ (projectEndpoint S {i} a, projectEndpoint S J a))) =
      coordinateProjectionEntropy S ν (insert i J) := by
  apply finiteEntropy_push_eq_of_fibers ν hν
  intro a b
  constructor
  · intro he
    apply Subtype.ext
    funext j
    rcases Finset.mem_insert.mp j.property with hj | hj
    · change a.val j.val = b.val j.val
      rw [hj]
      exact congrFun (congrArg Subtype.val (congrArg Prod.fst he)) ⟨i, Finset.mem_singleton_self i⟩
    · exact congrFun (congrArg Subtype.val (congrArg Prod.snd he)) ⟨j.val, hj⟩
  · intro he
    apply Prod.ext
    · apply Subtype.ext
      funext j
      exact congrFun (congrArg Subtype.val he) ⟨j.val, Finset.mem_insert.mpr
        (Or.inl (Finset.mem_singleton.mp j.property))⟩
    · apply Subtype.ext
      funext j
      exact congrFun (congrArg Subtype.val he) ⟨j.val, Finset.mem_insert.mpr (Or.inr j.property)⟩

/-- Diminishing entropy increments for literal coordinate observations
of one fixed finite nonnegative law. -/
theorem coordinateProjectionEntropy_increment_antitone (S : Finset (ι → ℝ))
    (ν : S → ℝ) (hν : ∀ a, 0 ≤ ν a) {I J : Finset ι} (hIJ : I ⊆ J) (i : ι) :
    coordinateProjectionEntropy S ν (insert i J) - coordinateProjectionEntropy S ν J ≤
      coordinateProjectionEntropy S ν (insert i I) - coordinateProjectionEntropy S ν I := by
  let X := projectEndpoint S {i}
  let F := projectEndpoint S J
  let G := projectEndpoint S I
  let p := finitePush ν (fun a ↦ (X a, F a))
  let h := restrictProjectedEndpoint S hIJ
  have hF : finitePush p Prod.snd = finitePush ν F := by rw [finitePush_comp]; rfl
  have hG : finitePush (finitePush ν F) h = finitePush ν G := by rw [finitePush_comp]; rfl
  have hpair : finitePush p (mapSecond h) = finitePush ν (fun a ↦ (X a, G a)) := by
    rw [finitePush_comp]; rfl
  have hc := finite_conditionalEntropy_map_condition p (finitePush_nonneg ν _ hν) h
  rw [hF, hG, hpair] at hc
  have hJ := coordinate_pair_entropy S ν hν i J
  have hI := coordinate_pair_entropy S ν hν i I
  change finiteEntropy p = _ at hJ
  change finiteEntropy (finitePush ν (fun a ↦ (X a, G a))) = _ at hI
  rw [hJ, hI] at hc
  exact hc

end
end Erdos539Geometry
