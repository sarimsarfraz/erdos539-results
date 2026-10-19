/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.MidpointClosure

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι M : Type*} [AddCommGroup M]

/-- Positive parts of the actual embedded group points, centered at zero. -/
def embeddedPositiveParts (e : M →ₗ[ℤ] (ι → ℝ)) (F : Finset M) : Finset (ι → ℝ) :=
  fan (F.image e) 0

/-- A large zero-centered sign class has two complementary projections
controlled by the same positive-part set of a symmetric parent. -/
theorem exists_centered_sign_partition [Fintype ι] {F : Finset M} (hF : F.Nonempty)
    (hsym : GroupSymmetric F) (e : M →ₗ[ℤ] (ι → ℝ)) :
    ∃ I J : Finset ι, Disjoint I J ∧ (∀ i, i ∈ I ∨ i ∈ J) ∧
      I.card + J.card = Fintype.card ι ∧
      ∃ E ⊆ F, E.Nonempty ∧ F.card ≤ 2 ^ Fintype.card ι * E.card ∧
        (E.image (fun x ↦ project I (e x))).card ≤ (embeddedPositiveParts e F).card ∧
        (E.image (fun x ↦ project J (e x))).card ≤ (embeddedPositiveParts e F).card := by
  classical
  letI : DecidableEq (ι → ℝ) := Classical.decEq _
  let mask := fun x : M ↦ freeMask ∅ (e x) 0
  obtain ⟨a, ha, hlarge⟩ := exists_large_fiber F hF mask
  let I := mask a
  let J := Finset.univ \ I
  let E := fiber F mask I
  have hEF : E ⊆ F := fun _ hx ↦ (mem_fiber.mp hx).1
  have hE : E.Nonempty := ⟨a, mem_fiber.mpr ⟨ha, rfl⟩⟩
  have hmask (x : M) (hx : x ∈ E) : freeMask ∅ (e x) 0 = I := (mem_fiber.mp hx).2
  have hcard : (F.image mask).card ≤ 2 ^ Fintype.card ι := by
    have h := Finset.card_le_univ (F.image mask)
    simpa only [Fintype.card_finset] using h
  have hP : (E.image (fun x ↦ project I (e x))).card ≤ (embeddedPositiveParts e F).card := by
    have hsub : E.image (fun x ↦ project I (e x)) ⊆ (embeddedPositiveParts e F).image (project I) := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      apply Finset.mem_image.mpr
      refine ⟨pdiff (e x) 0, mem_fan.mpr ⟨e x, Finset.mem_image_of_mem e (hEF hx), rfl⟩, ?_⟩
      funext i
      have hi : i.val ∈ freeMask ∅ (e x) 0 := by rw [hmask x hx]; exact i.property
      have hnonneg := (mem_freeMask.mp hi).2
      change 0 ≤ e x i.val at hnonneg
      change max (e x i.val - 0) 0 = e x i.val
      rw [sub_zero, max_eq_left hnonneg]
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  have hQ : (E.image (fun x ↦ project J (e x))).card ≤ (embeddedPositiveParts e F).card := by
    let recover : (ι → ℝ) → (J → ℝ) := fun z j ↦ -(z j)
    have hsub : E.image (fun x ↦ project J (e x)) ⊆ (embeddedPositiveParts e F).image recover := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      apply Finset.mem_image.mpr
      refine ⟨pdiff (e (-x)) 0, mem_fan.mpr ⟨e (-x), Finset.mem_image_of_mem e (hsym x (hEF hx)), rfl⟩, ?_⟩
      funext j
      have hj : j.val ∉ I := (Finset.mem_sdiff.mp j.property).2
      have hn : ¬ 0 ≤ e x j.val := by
        intro hn
        have hm : j.val ∈ freeMask ∅ (e x) 0 := mem_freeMask.mpr ⟨by simp, hn⟩
        rw [hmask x hx] at hm
        exact hj hm
      have hnonpos : e x j.val ≤ 0 := le_of_not_ge hn
      change -(max (e (-x) j.val - 0) 0) = e x j.val
      simp only [map_neg, Pi.neg_apply, sub_zero]
      rw [max_eq_left (neg_nonneg.mpr hnonpos), neg_neg]
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  refine ⟨I, J, ?_, ?_, ?_, E, hEF, hE,
    hlarge.trans (Nat.mul_le_mul_right _ hcard), hP, hQ⟩
  · exact Finset.disjoint_left.mpr (fun _ hi hj ↦ (Finset.mem_sdiff.mp hj).2 hi)
  · intro i
    by_cases hi : i ∈ I
    · exact Or.inl hi
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩)
  · have h := Finset.card_sdiff_of_subset (Finset.subset_univ I)
    have hi := Finset.card_le_univ I
    simp only [Finset.card_univ] at h
    dsimp only [J]
    omega

end
end Erdos539Geometry
