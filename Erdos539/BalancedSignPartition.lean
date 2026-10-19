/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SignPartition

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι : Type*} [Fintype ι]

/-- Order the two sign blocks by dimension, retaining the same large class
and the projection bounds from the original parent. Empty blocks are allowed. -/
theorem exists_ordered_sign_partition {F : Finset (ι → ℝ)} (hF : F.Nonempty) :
    ∃ I J : Finset ι, ∃ E : Finset (ι → ℝ), E ⊆ F ∧ E.Nonempty ∧
      F.card ≤ 2 ^ Fintype.card ι * E.card ∧
      (∀ i, i ∈ I ∨ i ∈ J) ∧ I.card + J.card = Fintype.card ι ∧ I.card ≤ J.card ∧
      (projection E I).card ≤ maxTwoFan F ∧ (projection E J).card ≤ maxTwoFan F := by
  classical
  obtain ⟨P, E, hEF, hE, hsize, hP, hQ⟩ := exists_large_sign_partition hF
  let Q := Finset.univ \ P
  have hcover : ∀ i, i ∈ P ∨ i ∈ Q := by
    intro i
    by_cases hi : i ∈ P
    · exact Or.inl hi
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩)
  have hcard : P.card + Q.card = Fintype.card ι := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ P)
    simpa only [Finset.card_univ, Nat.add_comm] using h
  by_cases hPQ : P.card ≤ Q.card
  · exact ⟨P, Q, E, hEF, hE, hsize, hcover, hcard, hPQ, hP, hQ⟩
  · exact ⟨Q, P, E, hEF, hE, hsize, fun i ↦ (hcover i).symm, by omega,
      le_of_not_ge hPQ, hQ, hP⟩

end
end Erdos539Geometry
