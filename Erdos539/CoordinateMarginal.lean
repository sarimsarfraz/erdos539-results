/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CoordinateFiberEnergy

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*}
local instance coordinateMarginalDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

theorem project_injOn_fiber (S : Finset (ι → ℝ)) (I J : Finset ι)
    (hcover : ∀ i, i ∈ I ∨ i ∈ J) (v : I → ℝ) :
    Set.InjOn (project J) (fiber S (project I) v) := by
  intro x hx y hy hxy
  ext i
  rcases hcover i with hi | hj
  · exact congrFun ((mem_fiber.mp hx).2.trans (mem_fiber.mp hy).2.symm) ⟨i, hi⟩
  · exact congrFun hxy ⟨i, hj⟩

/-- The marginal used in weighted pruning is exactly sqrt(sum f^2) over
the original coordinate fiber. It is independent of the chosen covering
complement, and is not the weight of a new optimizer. -/
theorem coordinateMarginalWeight_eq_sqrt_fiber (S : Finset (ι → ℝ)) (w : (ι → ℝ) → ℝ)
    (I J : Finset ι) (hcover : ∀ i, i ∈ I ∨ i ∈ J) (v : I → ℝ) :
    coordinateMarginalWeight S w I J v =
      Real.sqrt (weightSquareSum (fiber S (project I) v) w) := by
  unfold coordinateMarginalWeight rowNormWeight
  congr 1
  let F := fiber S (project I) v
  have hFS : F ⊆ S := fun _ hx ↦ (mem_fiber.mp hx).1
  have hproj : projection F J ⊆ projection S J := by
    intro u hu
    simp only [projection, Finset.mem_image] at hu ⊢
    obtain ⟨x, hx, rfl⟩ := hu
    exact ⟨x, hFS hx, rfl⟩
  calc
    weightSquareSum (projection S J) (fun u ↦ pushWeight S (coordinateSplit I J) w (u,v)) =
        ∑ u ∈ projection F J, pushWeight S (coordinateSplit I J) w (u,v) ^ 2 := by
      symm
      apply Finset.sum_subset hproj
      intro u _ hun
      have hn : (u,v) ∉ S.image (coordinateSplit I J) := by
        intro hu
        have hr := mem_rowSupport.mpr hu
        rw [rowSupport_coordinateSplit] at hr
        exact hun hr
      rw [pushWeight_zero w hn, zero_pow (by decide : 2 ≠ 0)]
    _ = ∑ x ∈ F, pushWeight S (coordinateSplit I J) w (project J x,v) ^ 2 := by
      symm
      apply Finset.sum_bij (fun x _ ↦ project J x)
      · intro x hx
        simp only [projection, Finset.mem_image]
        exact ⟨x, hx, rfl⟩
      · intro x hx y hy hxy
        exact project_injOn_fiber S I J hcover v hx hy hxy
      · intro u hu
        have hu' : ∃ x ∈ F, project J x = u := by
          simpa only [projection, Finset.mem_image] using hu
        obtain ⟨x, hx, hxu⟩ := hu'
        exact ⟨x, hx, hxu⟩
      · intro x _
        rfl
    _ = weightSquareSum (fiber S (project I) v) w := by
      apply Finset.sum_congr rfl
      intro x hx
      have hxv := (mem_fiber.mp hx).2
      have he : (project J x, v) = coordinateSplit I J x := by
        change (project J x, v) = (project J x, project I x)
        rw [hxv]
      rw [he, pushWeight_at_image (coordinateSplit_injective I J hcover).injOn w (hFS hx)]

/-- Any two covering complements give the same actual marginal energy. -/
theorem coordinateMarginalEnergy_independent_complement (S : Finset (ι → ℝ))
    (w : (ι → ℝ) → ℝ) (I J K : Finset ι)
    (hJ : ∀ i, i ∈ I ∨ i ∈ J) (hK : ∀ i, i ∈ I ∨ i ∈ K) :
    coordinateMarginalEnergy S w I J = coordinateMarginalEnergy S w I K := by
  unfold coordinateMarginalEnergy
  congr 1
  funext v
  rw [coordinateMarginalWeight_eq_sqrt_fiber S w I J hJ,
    coordinateMarginalWeight_eq_sqrt_fiber S w I K hK]

end
end Erdos539Geometry
