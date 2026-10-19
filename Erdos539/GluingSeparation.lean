/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.GluingExactDifferences
import Mathlib.Data.Finset.Sum

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι : Type*}

def glueShift (M g : ℤ) (u : ι → ℤ) : ι → ℤ := fun i ↦ u i + g * M

theorem glueShift_injective_of_gap {D : Finset (ι → ℤ)} {M : ℤ}
    (hM : 0 < M) (hgap : HasCoordinateGap D M) (i : ι)
    {g h : ℤ} {u v : ι → ℤ} (hu : u ∈ D) (hv : v ∈ D)
    (he : glueShift M g u = glueShift M h v) : g = h ∧ u = v := by
  have hh := congrFun he i
  change u i + g * M = v i + h * M at hh
  have hd := abs_lt.mp (hgap u hu v hv i)
  have hgh : g = h := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlt | hlt
    · have : g + 1 ≤ h := by omega
      nlinarith
    · have : h + 1 ≤ g := by omega
      nlinarith
  refine ⟨hgh, ?_⟩
  funext j
  have hj := congrFun he j
  change u j + g * M = v j + h * M at hj
  rw [hgh] at hj
  exact add_right_cancel hj

theorem integerDifference_coordinate_bound {F : Finset (ι → ℤ)} {L : ℤ}
    (hdiam : ∀ x ∈ F, ∀ y ∈ F, ∀ i, |x i - y i| ≤ L)
    {u : ι → ℤ} (hu : u ∈ integerDifferences F) (i : ι) : -L ≤ u i ∧ u i ≤ L := by
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_integerDifferences.mp hu
  exact abs_le.mp (hdiam x hx y hy i)

theorem integerPositiveDifference_coordinate_bound {F : Finset (ι → ℤ)} {L : ℤ}
    (hL : 0 ≤ L) (hdiam : ∀ x ∈ F, ∀ y ∈ F, ∀ i, |x i - y i| ≤ L)
    {u : ι → ℤ} (hu : u ∈ integerPositiveDifferences F) (i : ι) : 0 ≤ u i ∧ u i ≤ L := by
  obtain ⟨x, hx, y, hy, rfl⟩ := mem_integerPositiveDifferences.mp hu
  have hh := abs_le.mp (hdiam x hx y hy i)
  exact ⟨le_max_right _ _, max_le hh.2 hL⟩

theorem glueShift_coordinate_gt {F : Finset (ι → ℤ)} {L M g : ℤ}
    (hL : 0 ≤ L) (hM : 2 * L < M) (hg : 1 ≤ g)
    (hdiam : ∀ x ∈ F, ∀ y ∈ F, ∀ i, |x i - y i| ≤ L)
    {u : ι → ℤ} (hu : u ∈ integerDifferences F) (i : ι) : L < glueShift M g u i := by
  have hh := integerDifference_coordinate_bound hdiam hu i
  have hMp : 0 < M := by omega
  dsimp only [glueShift]
  nlinarith

end
end Erdos539Geometry
