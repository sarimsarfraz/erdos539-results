/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FourMaskMembership
import Erdos539.K4BlockEntropy

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι]

def k4AssignedBlock (F : ι → Fin 6) (k : Fin 6) : Finset ι := Finset.univ.filter (fun x ↦ F x = k)

theorem k4AssignedBlock_disjoint (F : ι → Fin 6) :
    Pairwise (fun k l ↦ Disjoint (k4AssignedBlock F k) (k4AssignedBlock F l)) := by
  intro k l hkl
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact hkl ((Finset.mem_filter.mp hx).2.symm.trans (Finset.mem_filter.mp hy).2)

theorem k4AssignedBlock_nonempty (F : ι → Fin 6) (hF : Function.Surjective F) (k : Fin 6) :
    (k4AssignedBlock F k).Nonempty := by
  obtain ⟨x, hx⟩ := hF k
  exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩

theorem k4AssignedBlock_union (F : ι → Fin 6) :
    k4AssignedBlock F 0 ∪ k4AssignedBlock F 1 ∪ k4AssignedBlock F 2 ∪
      k4AssignedBlock F 3 ∪ k4AssignedBlock F 4 ∪ k4AssignedBlock F 5 = Finset.univ := by
  ext x
  generalize hx : F x = k
  fin_cases k <;> simp [k4AssignedBlock, hx]

theorem k4AssignedBlock_star_mem (F : ι → Fin 6) (x : ι) (v : Fin 4) :
    x ∈ k4Star (k4AssignedBlock F 0) (k4AssignedBlock F 1) (k4AssignedBlock F 2)
      (k4AssignedBlock F 3) (k4AssignedBlock F 4) (k4AssignedBlock F 5) v ↔ v ∈ k4CoverEdge (F x) := by
  generalize hx : F x = k
  fin_cases v <;> fin_cases k <;>
    simp [k4Star, k4AssignedBlock, hx, k4CoverEdge, k4EdgeFirst, k4EdgeSecond]

theorem k4AssignedBlock_complement (F : ι → Fin 6) (v : Fin 4) :
    Finset.univ \ k4Star (k4AssignedBlock F 0) (k4AssignedBlock F 1) (k4AssignedBlock F 2)
      (k4AssignedBlock F 3) (k4AssignedBlock F 4) (k4AssignedBlock F 5) v =
      k4Triangle (k4AssignedBlock F 0) (k4AssignedBlock F 1) (k4AssignedBlock F 2)
      (k4AssignedBlock F 3) (k4AssignedBlock F 4) (k4AssignedBlock F 5) v := by
  ext x
  generalize hx : F x = k
  fin_cases v <;> fin_cases k <;> simp [k4Star, k4Triangle, k4AssignedBlock, hx]

/-- The fractional four-mask case yields six actual nonempty disjoint
coordinate blocks. Their stars shrink the original masks, and triangles
are their literal physical complements. No exposedness of the trimmed
masks is asserted. -/
theorem four_mask_trim_to_k4 (A : Fin 4 → Finset ι) (c : Fin 4 → ℝ)
    (hc : ∀ k, 0 ≤ c k) (hcover : ∀ x, 1 ≤ ∑ k, if x ∈ A k then c k else 0)
    (hr : ∑ k, c k ≤ 2) (hmiss : ∀ i j, i ≠ j → ∃ x, x ∉ A i ∧ x ∉ A j) :
    6 ≤ Fintype.card ι ∧ ∃ B : Fin 6 → Finset ι,
      (∀ k, (B k).Nonempty) ∧ Pairwise (fun k l ↦ Disjoint (B k) (B l)) ∧
      B 0 ∪ B 1 ∪ B 2 ∪ B 3 ∪ B 4 ∪ B 5 = Finset.univ ∧
      ∀ v, k4Star (B 0) (B 1) (B 2) (B 3) (B 4) (B 5) v ⊆ A v ∧
        Finset.univ \ k4Star (B 0) (B 1) (B 2) (B 3) (B 4) (B 5) v =
          k4Triangle (B 0) (B 1) (B 2) (B 3) (B 4) (B 5) v := by
  have hw := (four_mask_cover_weights A c hc hcover hr hmiss).2
  have hhalf : ∀ x, 1 ≤ ∑ k, if x ∈ A k then (1 / 2 : ℝ) else 0 := by simpa only [hw] using hcover
  obtain ⟨F, hF⟩ := exists_four_mask_edge_assignment A hhalf
  have hsurj := four_mask_assignment_surjective A F hF hmiss
  have hdim := Fintype.card_le_of_surjective F hsurj
  refine ⟨by simpa using hdim, k4AssignedBlock F, k4AssignedBlock_nonempty F hsurj,
    k4AssignedBlock_disjoint F, k4AssignedBlock_union F, ?_⟩
  intro v
  refine ⟨?_, k4AssignedBlock_complement F v⟩
  intro x hx
  exact hF x v ((k4AssignedBlock_star_mem F x v).mp hx)

end
end Erdos539Geometry
