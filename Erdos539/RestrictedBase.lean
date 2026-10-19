/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.Restricted
import Erdos539.PairCounting

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι : Type*}

theorem slice_eq_of_project_eq (F : Finset (ι → ℝ)) (I : Finset ι)
    {a b : ι → ℝ} (h : project I a = project I b) : slice F I a = slice F I b := by
  ext x
  simp only [mem_slice, h]

theorem maxFan_slice_le_maxRestrictedFan (F : Finset (ι → ℝ)) (I : Finset ι) (a : ι → ℝ) :
    maxFan (slice F I a) ≤ maxRestrictedFan F I := by
  apply Finset.sup_le
  intro b hb
  have he := slice_eq_of_project_eq F I (mem_slice.mp hb).2
  rw [← he]
  exact card_restrictedFan_le_max I (mem_slice.mp hb).1

/-- With one free coordinate, a minimum anchor in the fiber sees every point. -/
theorem card_slice_le_maxRestrictedFan_one_free
    (F : Finset (ι → ℝ)) (I : Finset ι) (i : ι)
    (hcover : ∀ j, j ∈ I ∨ j = i) (a : ι → ℝ) :
    (slice F I a).card ≤ maxRestrictedFan F I := by
  have hinj : (slice F I a : Set (ι → ℝ)).InjOn (fun x ↦ x i) := by
    intro x hx y hy he
    funext j
    rcases hcover j with hj | hj
    · exact (congrFun (mem_slice.mp hx).2 ⟨j, hj⟩).trans
        (congrFun (mem_slice.mp hy).2 ⟨j, hj⟩).symm
    · simpa only [hj] using he
  have hcard := Finset.card_image_of_injOn hinj
  calc
    (slice F I a).card = ((slice F I a).image (fun x ↦ x i)).card := hcard.symm
    _ ≤ maxFan (slice F I a) := coordinate_card_le_maxFan _ i
    _ ≤ maxRestrictedFan F I := maxFan_slice_le_maxRestrictedFan F I a

/-- The base case uses projection counts of the original parent, even when
the subset occupies only some of its fibers. -/
theorem card_le_projection_mul_restrictedFan_one_free
    {A S : Finset (ι → ℝ)} (hAS : A ⊆ S) (I : Finset ι) (i : ι)
    (hcover : ∀ j, j ∈ I ∨ j = i) :
    A.card ≤ (projection S I).card * maxRestrictedFan A I := by
  have hmaps : (A : Set (ι → ℝ)).MapsTo (project I) (projection S I) := by
    intro a ha
    exact Finset.mem_image_of_mem _ (hAS ha)
  have hf (b : I → ℝ) : (fiber A (project I) b).card ≤ maxRestrictedFan A I := by
    by_cases hb : (fiber A (project I) b).Nonempty
    · obtain ⟨a, ha⟩ := hb
      have he : fiber A (project I) b = slice A I a := by
        dsimp [slice]
        rw [(mem_fiber.mp ha).2]
      rw [he]
      exact card_slice_le_maxRestrictedFan_one_free A I i hcover a
    · rw [Finset.not_nonempty_iff_eq_empty.mp hb]
      exact Nat.zero_le _
  calc
    A.card = ∑ b ∈ projection S I, (fiber A (project I) b).card :=
      card_eq_sum_card_parent A (project I) (projection S I) hmaps
    _ ≤ ∑ _b ∈ projection S I, maxRestrictedFan A I := Finset.sum_le_sum (fun b _ ↦ hf b)
    _ = _ := by simp

theorem projection_card_eq_card_of_covers (S : Finset (ι → ℝ))
    (I : Finset ι) (hI : ∀ i, i ∈ I) : (projection S I).card = S.card := by
  apply Finset.card_image_of_injective
  intro x y h
  funext i
  exact congrFun h ⟨i, hI i⟩

end
end Erdos539Geometry
