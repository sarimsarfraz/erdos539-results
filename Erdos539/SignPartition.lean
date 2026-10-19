/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SignClasses
import Erdos539.SignedMonotonicity

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι : Type*} [Fintype ι]

/-- The negative block is recovered from the reverse fan at the same anchor. -/
theorem projection_negative_sign_class_le_two {E F : Finset (ι → ℝ)} (hEF : E ⊆ F)
    {a : ι → ℝ} (ha : a ∈ F) (P : Finset ι)
    (hmask : ∀ x ∈ E, freeMask ∅ x a = P) :
    (projection E (Finset.univ \ P)).card ≤ maxTwoFan F := by
  classical
  let Q := Finset.univ \ P
  let recover : (ι → ℝ) → (Q → ℝ) := fun z i ↦ a i - z i
  have hsub : projection E Q ⊆ (signedFan false F a).image recover := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hv
    apply Finset.mem_image.mpr
    refine ⟨pdiff a x, mem_signedFan.mpr ⟨x, hEF hx, rfl⟩, ?_⟩
    funext i
    have hnot : i.val ∉ freeMask ∅ x a := by
      rw [hmask x hx]
      exact (Finset.mem_sdiff.mp i.property).2
    have hlt : x i.val < a i.val := by
      by_contra h
      exact hnot (mem_freeMask.mpr ⟨Finset.notMem_empty _, le_of_not_gt h⟩)
    change a i.val - max (a i.val - x i.val) 0 = x i.val
    rw [max_eq_left (by linarith : 0 ≤ a i.val - x i.val)]
    ring
  exact (Finset.card_le_card hsub).trans
    (Finset.card_image_le.trans (card_signedFan_le_maxTwoFan false ha))

/-- A large sign class has both coordinate-block projections bounded by
one two-sided fan maximum of the original parent. -/
theorem exists_large_sign_partition {F : Finset (ι → ℝ)} (hF : F.Nonempty) :
    ∃ P : Finset ι, ∃ E : Finset (ι → ℝ), E ⊆ F ∧ E.Nonempty ∧
      F.card ≤ 2 ^ Fintype.card ι * E.card ∧
      (projection E P).card ≤ maxTwoFan F ∧
      (projection E (Finset.univ \ P)).card ≤ maxTwoFan F := by
  classical
  obtain ⟨a, ha⟩ := hF
  obtain ⟨x, hx, hlarge⟩ := exists_large_fiber F ⟨a, ha⟩ (fun x ↦ freeMask ∅ x a)
  let P := freeMask ∅ x a
  let E := fiber F (fun x ↦ freeMask ∅ x a) P
  have hEF : E ⊆ F := fun y hy ↦ (mem_fiber.mp hy).1
  have hE : E.Nonempty := ⟨x, mem_fiber.mpr ⟨hx, rfl⟩⟩
  have hmask : ∀ y ∈ E, freeMask ∅ y a = P := fun y hy ↦ (mem_fiber.mp hy).2
  have hcount : (F.image (fun x ↦ freeMask ∅ x a)).card ≤ 2 ^ Fintype.card ι := by
    simpa only [Fintype.card_finset] using Finset.card_le_univ (F.image (fun x ↦ freeMask ∅ x a))
  exact ⟨P, E, hEF, hE, hlarge.trans (Nat.mul_le_mul_right _ hcount),
    (projection_sign_class_le_maxFan hEF ha P hmask).trans (maxFan_le_maxTwoFan F),
    projection_negative_sign_class_le_two hEF ha P hmask⟩

end
end Erdos539Geometry
