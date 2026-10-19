/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CriticalColorDeletion

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι]
local instance exposedOutputDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

def coordinateScore (w : ι → ℝ) (I : Finset ι) (x : ι → ℝ) : ℝ := ∑ i ∈ I, w i * x i

omit [Fintype ι] in
theorem coordinateScore_sub (w x y : ι → ℝ) (I : Finset ι) :
    coordinateScore w I (x - y) = coordinateScore w I x - coordinateScore w I y := by
  simp only [coordinateScore, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- A literal positive exposed palette output. Genericity is required
only on its active projection and means injectivity of its linear score. -/
structure PositiveExposure (T : Finset (ι → ℝ)) (I : Finset ι) (w z : ι → ℝ) : Prop where
  weight_pos : ∀ i, 0 < w i
  color : z ∈ posDiff T
  active : ∀ i, i ∈ I ↔ 0 < z i
  maximal : ∀ v ∈ posDiff T, coordinateScore w Finset.univ v ≤ coordinateScore w Finset.univ z
  generic : ∀ a ∈ T, ∀ b ∈ T, coordinateScore w I a = coordinateScore w I b → project I a = project I b

namespace PositiveExposure
variable {T : Finset (ι → ℝ)} {I : Finset ι} {w z : ι → ℝ}

theorem color_nonneg (h : PositiveExposure T I w z) (i : ι) : 0 ≤ z i := by
  obtain ⟨x, _, y, _, rfl⟩ := mem_posDiff.mp h.color
  exact le_max_right _ _

theorem partial_difference_le (h : PositiveExposure T I w z)
    {a c : ι → ℝ} (ha : a ∈ T) (hc : c ∈ T) :
    coordinateScore w I (a - c) ≤ coordinateScore w Finset.univ z := by
  calc
    _ ≤ ∑ i ∈ I, w i * pdiff a c i := Finset.sum_le_sum
      (fun i _ ↦ mul_le_mul_of_nonneg_left (le_max_left _ _) (h.weight_pos i).le)
    _ ≤ coordinateScore w Finset.univ (pdiff a c) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
        (fun i _ _ ↦ mul_nonneg (h.weight_pos i).le (le_max_right _ _))
    _ ≤ _ := h.maximal _ (mem_posDiff.mpr ⟨a, ha, c, hc, rfl⟩)

theorem witness_score (h : PositiveExposure T I w z) {x y : ι → ℝ}
    (hxy : pdiff x y = z) :
    coordinateScore w I (x - y) = coordinateScore w Finset.univ z := by
  calc
    _ = ∑ i ∈ I, w i * z i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hz := (h.active i).mp hi
      have he := congrFun hxy i
      change max (x i - y i) 0 = z i at he
      have hp : 0 < x i - y i := (lt_max_iff.mp (he.symm ▸ hz)).resolve_right (lt_irrefl 0)
      rw [max_eq_left hp.le] at he
      change w i * (x i - y i) = w i * z i
      rw [he]
    _ = _ := Finset.sum_subset (Finset.subset_univ I) (by
      intro i _ hi
      have hz : z i = 0 := le_antisymm (le_of_not_gt (fun hp ↦ hi ((h.active i).mpr hp))) (h.color_nonneg i)
      rw [hz, mul_zero])

/-- The first endpoint of any witness lies in the same actual active-
coordinate fiber. This is proved from maximality and genericity. -/
theorem witness_first_projection (h : PositiveExposure T I w z)
    {x y a c : ι → ℝ} (hx : x ∈ T) (hy : y ∈ T) (ha : a ∈ T) (hc : c ∈ T)
    (hxy : pdiff x y = z) (hac : pdiff a c = z) : project I a = project I x := by
  have he := h.witness_score hxy
  have he' := h.witness_score hac
  have h1 := h.partial_difference_le ha hy
  have h2 := h.partial_difference_le hx hc
  rw [coordinateScore_sub] at he he' h1 h2
  exact h.generic a ha x hx (by linarith)

/-- An exposed output has a color-killing actual coordinate fiber. -/
theorem exists_color_killing_fiber (h : PositiveExposure T I w z) :
    ∃ v : I → ℝ, KillsColors T (fiber T (project I) v) {z} := by
  obtain ⟨x, hx, y, hy, hxy⟩ := mem_posDiff.mp h.color
  refine ⟨project I x, Finset.singleton_subset_iff.mpr h.color, ?_⟩
  apply Finset.disjoint_left.mpr
  intro u hu hsurvive
  have hu' : u = z := Finset.mem_singleton.mp hu
  subst u
  obtain ⟨a, ha, c, hc, hac⟩ := mem_posDiff.mp hsurvive
  have ha' := Finset.mem_sdiff.mp ha
  have hc' := Finset.mem_sdiff.mp hc
  exact ha'.2 (mem_fiber.mpr ⟨ha'.1, h.witness_first_projection hx hy ha'.1 hc'.1 hxy hac⟩)

end PositiveExposure

/-- Membership in the family of generic positive exposed active masks.
This definition asserts an actual exposing vector and palette output. -/
def IsExposedActiveMask (T : Finset (ι → ℝ)) (I : Finset ι) : Prop :=
  ∃ w z, PositiveExposure T I w z

end
end Erdos539Geometry
