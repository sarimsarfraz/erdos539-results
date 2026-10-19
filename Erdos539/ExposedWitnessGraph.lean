/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ExposedOutput

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι]
local instance exposedWitnessGraphDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

namespace PositiveExposure
variable {T : Finset (ι → ℝ)} {I : Finset ι} {w z : ι → ℝ}

theorem witness_second_projection (h : PositiveExposure T I w z)
    {x y a c : ι → ℝ} (hx : x ∈ T) (hy : y ∈ T) (ha : a ∈ T) (hc : c ∈ T)
    (hxy : pdiff x y = z) (hac : pdiff a c = z) : project I c = project I y := by
  have he := h.witness_score hxy
  have he' := h.witness_score hac
  have h1 := h.partial_difference_le ha hy
  have h2 := h.partial_difference_le hx hc
  rw [coordinateScore_sub] at he he' h1 h2
  exact h.generic c hc y hy (by linarith)

/-- Every cross pair between the two extremal actual coordinate fibers
represents the same exposed output; extra positive coordinates would
strictly increase its positive exposing score. -/
theorem witness_of_projection_pair (h : PositiveExposure T I w z)
    {x y a c : ι → ℝ} (ha : a ∈ T) (hc : c ∈ T) (hxy : pdiff x y = z)
    (haI : project I a = project I x) (hcI : project I c = project I y) : pdiff a c = z := by
  have hinside (j : ι) (hj : j ∈ I) : pdiff a c j = z j := by
    have he := congrFun hxy j
    change max (a j - c j) 0 = z j
    rw [show a j = x j from congrFun haI ⟨j, hj⟩,
      show c j = y j from congrFun hcI ⟨j, hj⟩]
    exact he
  have hpartial : (∑ j ∈ I, w j * pdiff a c j) = coordinateScore w Finset.univ z := by
    calc
      _ = ∑ j ∈ I, w j * z j := Finset.sum_congr rfl (fun j hj ↦ by rw [hinside j hj])
      _ = _ := Finset.sum_subset (Finset.subset_univ I) (by
        intro j _ hj
        have hz : z j = 0 := le_antisymm (le_of_not_gt (fun hp ↦ hj ((h.active j).mpr hp))) (h.color_nonneg j)
        rw [hz, mul_zero])
  funext j
  by_cases hj : j ∈ I
  · exact hinside j hj
  · have hz : z j = 0 := le_antisymm (le_of_not_gt (fun hp ↦ hj ((h.active j).mpr hp))) (h.color_nonneg j)
    have hs := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k ↦ w k * pdiff a c k)
      (Finset.subset_univ (insert j I))
      (fun k _ _ ↦ mul_nonneg (h.weight_pos k).le (le_max_right _ _))
    rw [Finset.sum_insert hj, hpartial] at hs
    have hm := h.maximal _ (mem_posDiff.mpr ⟨a, ha, c, hc, rfl⟩)
    change (∑ k, w k * pdiff a c k) ≤ coordinateScore w Finset.univ z at hm
    have hp := h.weight_pos j
    have hn : 0 ≤ pdiff a c j := le_max_right _ _
    rw [hz]
    nlinarith

/-- The full literal representation graph is a complete bipartite graph
between the two actual projected fibers, with no missing cross edges. -/
theorem witness_iff_projection_pair (h : PositiveExposure T I w z)
    {x y a c : ι → ℝ} (hx : x ∈ T) (hy : y ∈ T) (ha : a ∈ T) (hc : c ∈ T)
    (hxy : pdiff x y = z) :
    pdiff a c = z ↔ project I a = project I x ∧ project I c = project I y := by
  constructor
  · intro hac
    exact ⟨h.witness_first_projection hx hy ha hc hxy hac,
      h.witness_second_projection hx hy ha hc hxy hac⟩
  · rintro ⟨haI, hcI⟩
    exact h.witness_of_projection_pair ha hc hxy haI hcI

/-- The two actual fibers are ordered in every complementary coordinate. -/
theorem witness_fibers_ordered (h : PositiveExposure T I w z)
    {x y a c : ι → ℝ} (ha : a ∈ T) (hc : c ∈ T) (hxy : pdiff x y = z)
    (haI : project I a = project I x) (hcI : project I c = project I y)
    {j : ι} (hj : j ∉ I) : a j ≤ c j := by
  have he := congrFun (h.witness_of_projection_pair ha hc hxy haI hcI) j
  have hz : z j = 0 := le_antisymm (le_of_not_gt (fun hp ↦ hj ((h.active j).mpr hp))) (h.color_nonneg j)
  change max (a j - c j) 0 = z j at he
  have hh := le_max_left (a j - c j) 0
  rw [he, hz] at hh
  linarith

end PositiveExposure
end
end Erdos539Geometry
