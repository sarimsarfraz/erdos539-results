/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PairCounting

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι : Type*} [Fintype ι]

/-- Equality belongs to both directional masks; the complement still lies in
the reverse mask. This convention deliberately retains coordinate ties. -/
def freeMask (I : Finset ι) (x y : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i ↦ i ∉ I ∧ y i ≤ x i)

@[simp] theorem mem_freeMask {I : Finset ι} {x y : ι → ℝ} {i : ι} :
    i ∈ freeMask I x y ↔ i ∉ I ∧ y i ≤ x i := by simp [freeMask]

theorem freeMask_subset (I : Finset ι) (x y : ι → ℝ) :
    freeMask I x y ⊆ Finset.univ \ I := by
  classical
  intro i hi
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, (mem_freeMask.mp hi).1⟩

theorem complement_freeMask_subset_reverse (I : Finset ι) (x y : ι → ℝ) :
    (Finset.univ \ I) \ freeMask I x y ⊆ freeMask I y x := by
  classical
  intro i hi
  obtain ⟨hfree, hnot⟩ := Finset.mem_sdiff.mp hi
  have hI := (Finset.mem_sdiff.mp hfree).2
  apply mem_freeMask.mpr
  refine ⟨hI, ?_⟩
  have hn : ¬ y i ≤ x i := fun h ↦ hnot (mem_freeMask.mpr ⟨hI, h⟩)
  exact (lt_of_not_ge hn).le

def maskCell (A : Finset (ι → ℝ)) (I J : Finset ι) (y : ι → ℝ) : Finset (ι → ℝ) :=
  (slice A I y).filter (fun x ↦ freeMask I x y = J)

@[simp] theorem mem_maskCell {A : Finset (ι → ℝ)} {I J : Finset ι} {x y : ι → ℝ} :
    x ∈ maskCell A I J y ↔ x ∈ A ∧ project I x = project I y ∧ freeMask I x y = J := by
  classical
  simp only [maskCell, Finset.mem_filter, mem_slice, and_assoc]

theorem project_eq_of_mask_and_pdiff_eq {I J : Finset ι} {x x' y : ι → ℝ}
    (hx : project I x = project I y) (hx' : project I x' = project I y)
    (hm : freeMask I x y = J) (hm' : freeMask I x' y = J)
    (h : pdiff x y = pdiff x' y) : project (I ∪ J) x = project (I ∪ J) x' := by
  classical
  funext i
  rcases Finset.mem_union.mp i.property with hi | hj
  · exact (congrFun hx ⟨i.val, hi⟩).trans (congrFun hx' ⟨i.val, hi⟩).symm
  · have hxmem : i.val ∈ freeMask I x y := by rwa [hm]
    have hpos := (mem_freeMask.mp hxmem).2
    have hxmem' : i.val ∈ freeMask I x' y := by rwa [hm']
    have hpos' := (mem_freeMask.mp hxmem').2
    have he := congrFun h i.val
    change max (x i.val - y i.val) 0 = max (x' i.val - y i.val) 0 at he
    rw [max_eq_left (sub_nonneg.mpr hpos), max_eq_left (sub_nonneg.mpr hpos')] at he
    change x i.val = x' i.val
    linarith

/-- A sign cell has at most one parent coordinate fiber per positive output. -/
theorem card_maskCell_le {A S : Finset (ι → ℝ)} (hAS : A ⊆ S)
    (I J : Finset ι) {y : ι → ℝ} (hy : y ∈ A) :
    (maskCell A I J y).card ≤
      maxRestrictedFan A I * maxFiber S (project (I ∪ J)) := by
  classical
  let C := maskCell A I J y
  let f := fun x ↦ pdiff x y
  have hf : ∀ z ∈ C.image f, (fiber C f z).card ≤ maxFiber S (project (I ∪ J)) := by
    intro z hz
    obtain ⟨x, hx, hfx⟩ := Finset.mem_image.mp hz
    have hxdata := mem_maskCell.mp hx
    have hsub : fiber C f z ⊆ fiber S (project (I ∪ J)) (project (I ∪ J) x) := by
      intro x' hx'
      obtain ⟨hc, he⟩ := mem_fiber.mp hx'
      have hd := mem_maskCell.mp hc
      apply mem_fiber.mpr
      refine ⟨hAS hd.1, ?_⟩
      exact project_eq_of_mask_and_pdiff_eq hd.2.1 hxdata.2.1 hd.2.2 hxdata.2.2
        (he.trans hfx.symm)
    exact (Finset.card_le_card hsub).trans (card_fiber_le_maxFiber S _ _)
  have hi : C.image f ⊆ restrictedFan A I y := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    exact mem_fan.mpr ⟨x, mem_slice.mpr ⟨(mem_maskCell.mp hx).1, (mem_maskCell.mp hx).2.1⟩, rfl⟩
  exact (card_le_image_mul_of_fiber_le C f _ hf).trans
    (Nat.mul_le_mul_right _ ((Finset.card_le_card hi).trans (card_restrictedFan_le_max I hy)))

omit [Fintype ι] in
/-- More coordinates cannot decrease the number of distinct projections. -/
theorem projection_card_mono (S : Finset (ι → ℝ)) {I J : Finset ι} (hIJ : I ⊆ J) :
    (projection S I).card ≤ (projection S J).card := by
  classical
  let r : (J → ℝ) → (I → ℝ) := fun x i ↦ x ⟨i.val, hIJ i.property⟩
  have he : (projection S J).image r = projection S I := by
    simp only [projection, Finset.image_image]
    rfl
  rw [← he]
  exact Finset.card_image_le

end
end Erdos539Geometry
