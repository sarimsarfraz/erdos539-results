/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.RestrictedBase

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι : Type*} [Fintype ι]

theorem remaining_union (I U : Finset ι) :
    Finset.univ \ (I ∪ U) = (Finset.univ \ I) \ U := by
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_univ, true_and]
  tauto

theorem remaining_union_complement (I : Finset ι) {U : Finset ι}
    (hU : U ⊆ Finset.univ \ I) :
    Finset.univ \ (I ∪ ((Finset.univ \ I) \ U)) = U := by
  ext i
  have hUi : i ∈ U → i ∉ I := fun hi ↦ (Finset.mem_sdiff.mp (hU hi)).2
  simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_univ, true_and]
  tauto

theorem partition_cover (I U : Finset ι) :
    ∀ i, i ∈ I ∪ U ∨ i ∈ I ∪ ((Finset.univ \ I) \ U) := by
  intro i
  simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and]
  tauto

theorem partition_card (I : Finset ι) {U : Finset ι} (hU : U ⊆ Finset.univ \ I) :
    U.card + ((Finset.univ \ I) \ U).card = (Finset.univ \ I).card := by
  simpa only [Nat.add_comm] using Finset.card_sdiff_add_card_eq_card hU

theorem covers_of_remaining_empty {I : Finset ι} (hI : Finset.univ \ I = ∅) :
    ∀ i, i ∈ I := by
  intro i
  by_contra hi
  have h : i ∈ Finset.univ \ I := Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩
  rw [hI] at h
  exact Finset.notMem_empty _ h

theorem exists_one_free_coordinate {I : Finset ι} (hI : (Finset.univ \ I).card = 1) :
    ∃ i : ι, ∀ j, j ∈ I ∨ j = i := by
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hI
  refine ⟨i, fun j ↦ ?_⟩
  by_cases hj : j ∈ I
  · exact Or.inl hj
  · right
    have hmem : j ∈ Finset.univ \ I := Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩
    rw [hi] at hmem
    exact Finset.mem_singleton.mp hmem

theorem parent_card_le_of_fiber_bound {S : Finset (ι → ℝ)} (hS : S.Nonempty)
    {H : ℕ} (hH : ∀ J, (projection S J).card * maxFiber S (project J) ≤ H) : S.card ≤ H := by
  obtain ⟨a, ha⟩ := hS
  have hf : 1 ≤ maxFiber S (project Finset.univ) := by
    apply (Finset.card_pos.mpr (show (fiber S (project Finset.univ) (project Finset.univ a)).Nonempty
      from ⟨a, mem_fiber.mpr ⟨ha, rfl⟩⟩)).trans_le
    exact card_fiber_le_maxFiber S _ _
  calc
    S.card = (projection S Finset.univ).card * 1 := by
      rw [projection_card_eq_card_of_covers S Finset.univ Finset.mem_univ, Nat.mul_one]
    _ ≤ (projection S Finset.univ).card * maxFiber S (project Finset.univ) :=
      Nat.mul_le_mul_left _ hf
    _ ≤ H := hH _

end
end Erdos539Geometry
