/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationarySweepLinear
import Erdos539.FiniteConditionalComparison
import Erdos539.CoordinateProfileMonotonicity

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι]
local instance coordinateHanDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _
local instance coordinateHanProjectionDecidableEq (S : Finset (ι → ℝ)) (I : Finset ι) :
    DecidableEq (projection S I) := Classical.decEq _

/-- Entropy of the literal coordinate projection of the original law. -/
def coordinateProjectionEntropy (S : Finset (ι → ℝ)) (ν : S → ℝ) (I : Finset ι) : ℝ :=
  finiteEntropy (finitePush ν (projectEndpoint S I))

theorem coordinateConditionalEntropy_le_increment (S : Finset (ι → ℝ)) (ν : S → ℝ)
    (hν : ∀ a, 0 ≤ ν a) {I : Finset ι} {i : ι} (hi : i ∉ I) :
    coordinateConditionalEntropy S ν i ≤
      coordinateProjectionEntropy S ν (insert i I) - coordinateProjectionEntropy S ν I := by
  have hI : I ⊆ Finset.univ.erase i := by
    intro j hj
    exact Finset.mem_erase.mpr ⟨by intro he; exact hi (he ▸ hj), Finset.mem_univ j⟩
  have hsingle : ({i} : Finset ι) ⊆ insert i I := by simp
  have hsub : I ⊆ insert i I := Finset.subset_insert i I
  let X := projectEndpoint S {i}
  let F := outsideEndpoint S i
  let G := projectEndpoint S I
  let L := projectEndpoint S (insert i I)
  let h := restrictProjectedEndpoint S hI
  let g := fun v : projection S (insert i I) ↦
    (restrictProjectedEndpoint S hsingle v, restrictProjectedEndpoint S hsub v)
  have hinj : Function.Injective (fun a ↦ (X a, F a)) := by
    intro a b he
    apply Subtype.ext
    funext j
    by_cases hj : j = i
    · subst j
      have hv := congrArg Prod.fst he
      exact congrFun (congrArg Subtype.val hv) ⟨i, Finset.mem_singleton_self i⟩
    · have hv := congrArg Prod.snd he
      exact congrFun (congrArg Subtype.val hv) ⟨j, Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩⟩
  exact finite_conditional_entropy_comparison ν hν X F G L h g rfl rfl hinj

theorem coordinateProjectionEntropy_univ (S : Finset (ι → ℝ)) (ν : S → ℝ) :
    coordinateProjectionEntropy S ν Finset.univ = finiteEntropy ν := by
  apply finiteEntropy_push_eq_of_support_injective
  intro a b _ _ he
  apply Subtype.ext
  funext i
  exact congrFun (congrArg Subtype.val he) ⟨i, Finset.mem_univ i⟩

/-- Conditional Han inequality on the actual coordinate labels. -/
theorem coordinate_han (S : Finset (ι → ℝ)) (ν : S → ℝ)
    (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1) :
    (∑ i, coordinateConditionalEntropy S ν i) ≤ finiteEntropy ν := by
  have hmask (I : Finset ι) :
      (∑ i ∈ I, coordinateConditionalEntropy S ν i) ≤ coordinateProjectionEntropy S ν I := by
    induction I using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact finiteEntropy_nonneg _ (finitePush_nonneg ν _ hν) (by rw [finitePush_sum, hs])
    | @insert i I hi ih =>
      rw [Finset.sum_insert hi]
      have h := coordinateConditionalEntropy_le_increment S ν hν hi
      linarith
  simpa only [coordinateProjectionEntropy_univ] using hmask Finset.univ

end
end Erdos539Geometry
