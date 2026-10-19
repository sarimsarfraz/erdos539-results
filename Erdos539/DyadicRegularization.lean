/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.DyadicFibers
import Erdos539.UniformRegularity

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Classical
variable {ι : Type*} [Fintype ι]

/-- Number of occupied dyadic scales available below the size bound `N`. -/
def dyadicLevels (N : ℕ) : ℕ := Nat.log 2 N + 1

/-- Only nonempty proper coordinate subsets require regularization. -/
def properCoordinates : Finset (Finset ι) :=
  (Finset.univ.erase ∅).erase Finset.univ

@[simp] theorem mem_properCoordinates (I : Finset ι) :
    I ∈ properCoordinates ↔ I ≠ ∅ ∧ I ≠ Finset.univ := by
  simp only [properCoordinates, Finset.mem_erase, Finset.mem_univ, and_true]
  exact and_comm

theorem card_properCoordinates (hd : 0 < Fintype.card ι) :
    (properCoordinates : Finset (Finset ι)).card = 2 ^ Fintype.card ι - 2 := by
  classical
  have hne : (Finset.univ : Finset ι) ≠ ∅ := by
    intro he
    have h := congrArg Finset.card he
    simp only [Finset.card_univ, Finset.card_empty] at h
    omega
  rw [properCoordinates, Finset.card_erase_of_mem (by simp [hne]),
    Finset.card_erase_of_mem (Finset.mem_univ ∅)]
  simp only [Finset.card_univ, Fintype.card_finset]
  omega

omit [Fintype ι] in
theorem projection_mul_maxFiber_empty {S : Finset (ι → ℝ)} (hS : S.Nonempty) :
    (projection S ∅).card * maxFiber S (project ∅) ≤ S.card := by
  rw [projection_empty_card hS, one_mul]
  apply Finset.sup_le
  intro y _
  exact Finset.card_le_card (fun _ hx ↦ (mem_fiber.mp hx).1)

theorem projection_mul_maxFiber_univ (S : Finset (ι → ℝ)) :
    (projection S Finset.univ).card * maxFiber S (project Finset.univ) ≤ S.card := by
  classical
  have hmax : maxFiber S (project Finset.univ) ≤ 1 := by
    apply Finset.sup_le
    intro y _
    apply Finset.card_le_one.mpr
    intro x hx z hz
    funext i
    exact congrFun ((mem_fiber.mp hx).2.trans (mem_fiber.mp hz).2.symm)
      ⟨i, Finset.mem_univ i⟩
  calc
    _ ≤ (projection S Finset.univ).card * 1 := Nat.mul_le_mul_left _ hmax
    _ ≤ S.card := by simpa only [mul_one] using (Finset.card_image_le (s := S) (f := project Finset.univ))

/-- Simultaneous dyadic regularization, uniformly at any ambient size bound.
Every coordinate projection obeys the same product estimate. -/
theorem exists_dyadic_regularization {F : Finset (ι → ℝ)} (hF : F.Nonempty)
    (hd : 0 < Fintype.card ι) {N : ℕ} (hFN : F.card ≤ N) :
    ∃ S ⊆ F, S.Nonempty ∧
      F.card ≤ dyadicLevels N ^ (2 ^ Fintype.card ι - 2) * S.card ∧
      ∀ I, (projection S I).card * maxFiber S (project I) ≤
        2 * dyadicLevels N ^ (2 ^ Fintype.card ι - 2) * S.card := by
  classical
  let P : Finset (Finset ι) := properCoordinates
  let profile : (ι → ℝ) → (P → Fin (dyadicLevels N)) := fun x I ↦
    ⟨Nat.log 2 (slice F I.val x).card,
      Nat.lt_succ_of_le (Nat.log_mono_right ((Finset.card_le_card (slice_subset F I.val x)).trans hFN))⟩
  obtain ⟨a, ha, hlarge⟩ := exists_large_fiber F hF profile
  let S := fiber F profile (profile a)
  have hSF : S ⊆ F := fun _ hx ↦ (mem_fiber.mp hx).1
  have hS : S.Nonempty := ⟨a, mem_fiber.mpr ⟨ha, rfl⟩⟩
  have hprofiles : (F.image profile).card ≤ dyadicLevels N ^ (2 ^ Fintype.card ι - 2) := by
    have h := Finset.card_le_univ (F.image profile)
    simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, P,
      card_properCoordinates hd] using h
  have hsize : F.card ≤ dyadicLevels N ^ (2 ^ Fintype.card ι - 2) * S.card :=
    hlarge.trans (Nat.mul_le_mul_right _ hprofiles)
  refine ⟨S, hSF, hS, hsize, ?_⟩
  intro I
  have htwice : 2 * F.card ≤ 2 * dyadicLevels N ^ (2 ^ Fintype.card ι - 2) * S.card := by
    simpa only [mul_assoc] using Nat.mul_le_mul_left 2 hsize
  by_cases hIempty : I = ∅
  · rw [hIempty]
    exact (projection_mul_maxFiber_empty hS).trans ((Finset.card_le_card hSF).trans (by omega))
  by_cases hIfull : I = Finset.univ
  · rw [hIfull]
    exact (projection_mul_maxFiber_univ S).trans ((Finset.card_le_card hSF).trans (by omega))
  have hIP : I ∈ P := mem_properCoordinates I |>.mpr ⟨hIempty, hIfull⟩
  apply (dyadic_fiber_product_le hSF (project I) (Nat.log 2 (slice F I a).card) ?_).trans htwice
  intro x hx
  have he := congrArg (fun t : P → Fin (dyadicLevels N) ↦ (t ⟨I, hIP⟩).val) (mem_fiber.mp hx).2
  exact he

end
end Erdos539Geometry
