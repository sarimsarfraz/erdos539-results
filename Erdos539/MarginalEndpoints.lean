/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ActualWeightedPruning
import Erdos539.CoordinateEnergy

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*}
local instance marginalEndpointsDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

theorem actualMarginalWeight_at_injective_project {S : Finset (ι → ℝ)}
    (w : (ι → ℝ) → ℝ) (hw : ∀ x ∈ S, 0 ≤ w x) (I : Finset ι)
    (hinj : Function.Injective (project I)) {x : ι → ℝ} (hx : x ∈ S) :
    actualMarginalWeight S w I (project I x) = w x := by
  have he : fiber S (project I) (project I x) = {x} := by
    ext y
    simp only [mem_fiber, Finset.mem_singleton]
    constructor
    · intro hy
      exact hinj hy.2
    · intro hy
      subst y
      exact ⟨hx, rfl⟩
  rw [actualMarginalWeight, he]
  simp only [weightSquareSum, Finset.sum_singleton, Real.sqrt_sq_eq_abs, abs_of_nonneg (hw x hx)]

/-- An injective coordinate projection retains exactly the original
weighted energy in its actual square-root marginal. -/
theorem actualMarginalEnergy_eq_of_injective_project {S : Finset (ι → ℝ)}
    (w : (ι → ℝ) → ℝ) (hw : ∀ x ∈ S, 0 ≤ w x) (I : Finset ι)
    (hinj : Function.Injective (project I)) : actualMarginalEnergy S w I = weightedEnergy S w := by
  let φ := projectCoordinatesHom I
  have himage : S.image φ = projection S I := by
    ext v
    simp only [Finset.mem_image, projection]
    rfl
  have he := weightedEnergy_pushWeight S φ hinj w
  rw [himage] at he
  rw [← he]
  apply weightedEnergy_congr
  intro v hv
  have hv' : ∃ x ∈ S, project I x = v := by simpa only [projection, Finset.mem_image] using hv
  obtain ⟨x, hx, rfl⟩ := hv'
  rw [actualMarginalWeight_at_injective_project w hw I hinj hx]
  exact (pushWeight_at_image hinj.injOn w hx).symm

theorem actualMarginalEnergy_univ [Fintype ι] {S : Finset (ι → ℝ)}
    (w : (ι → ℝ) → ℝ) (hw : ∀ x ∈ S, 0 ≤ w x) :
    actualMarginalEnergy S w Finset.univ = weightedEnergy S w := by
  apply actualMarginalEnergy_eq_of_injective_project w hw
  intro x y hxy
  funext i
  exact congrFun hxy ⟨i, Finset.mem_univ i⟩

end
end Erdos539Geometry
