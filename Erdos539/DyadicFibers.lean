/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SignClasses
import Mathlib.Data.Nat.Log

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {α β : Type*}

/-- A subfamily occupying one dyadic bucket of the original fibers has
projection size times largest fiber at most twice the original cardinality. -/
theorem dyadic_fiber_product_le [DecidableEq β] {S F : Finset α} (hSF : S ⊆ F)
    (f : α → β) (b : ℕ)
    (hbucket : ∀ x ∈ S, Nat.log 2 (fiber F f (f x)).card = b) :
    (S.image f).card * maxFiber S f ≤ 2 * F.card := by
  classical
  have hlower : (S.image f).card * 2 ^ b ≤ F.card := by
    calc
      _ = ∑ _y ∈ S.image f, 2 ^ b := by simp
      _ ≤ ∑ y ∈ S.image f, (fiber F f y).card := by
        apply Finset.sum_le_sum
        intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
        have hxF : x ∈ fiber F f (f x) := mem_fiber.mpr ⟨hSF hx, rfl⟩
        have h := Nat.pow_log_le_self 2 (Finset.card_ne_zero.mpr ⟨x, hxF⟩)
        rwa [hbucket x hx] at h
      _ ≤ ∑ y ∈ F.image f, (fiber F f y).card :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.image_subset_image hSF)
          (fun _ _ _ ↦ Nat.zero_le _)
      _ = F.card := (card_eq_sum_card_fiber F f).symm
  have hupper : maxFiber S f ≤ 2 ^ (b + 1) := by
    letI : DecidableEq β := Classical.decEq β
    apply Finset.sup_le
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hsub : fiber S f (f x) ⊆ fiber F f (f x) := by
      intro z hz
      exact mem_fiber.mpr ⟨hSF (mem_fiber.mp hz).1, (mem_fiber.mp hz).2⟩
    have h := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (fiber F f (f x)).card
    rw [hbucket x hx] at h
    exact (Finset.card_le_card hsub).trans h.le
  calc
    _ ≤ (S.image f).card * 2 ^ (b + 1) := Nat.mul_le_mul_left _ hupper
    _ = 2 * ((S.image f).card * 2 ^ b) := by rw [pow_succ]; ring
    _ ≤ 2 * F.card := Nat.mul_le_mul_left 2 hlower

end
end Erdos539Geometry
