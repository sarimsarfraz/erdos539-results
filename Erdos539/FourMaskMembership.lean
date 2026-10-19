/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FractionalCoverPairBounds

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*}

def fourMaskMembership (A : Fin 4 → Finset ι) (x : ι) : Finset (Fin 4) :=
  Finset.univ.filter (fun k ↦ x ∈ A k)

theorem four_mask_membership_card (A : Fin 4 → Finset ι)
    (hcover : ∀ x, 1 ≤ ∑ k, if x ∈ A k then (1 / 2 : ℝ) else 0) (x : ι) :
    2 ≤ (fourMaskMembership A x).card := by
  have hh := hcover x
  have he : (∑ k, if x ∈ A k then (1 / 2 : ℝ) else 0) =
      ((fourMaskMembership A x).card : ℝ) / 2 := by
    rw [fourMaskMembership, ← Finset.sum_filter]
    simp [div_eq_mul_inv]
  rw [he] at hh
  have hn : (2 : ℝ) ≤ (fourMaskMembership A x).card := by linarith
  exact_mod_cast hn

def k4EdgeFirst : Fin 6 → Fin 4
  | 0 => 0 | 1 => 0 | 2 => 0 | 3 => 1 | 4 => 1 | 5 => 2

def k4EdgeSecond : Fin 6 → Fin 4
  | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 2 | 4 => 3 | 5 => 3

def k4CoverEdge (k : Fin 6) : Finset (Fin 4) := {k4EdgeFirst k, k4EdgeSecond k}

theorem k4Edge_endpoints_ne (k : Fin 6) : k4EdgeFirst k ≠ k4EdgeSecond k := by
  fin_cases k <;> decide

theorem k4CoverEdge_card (k : Fin 6) : (k4CoverEdge k).card = 2 := by
  simp [k4CoverEdge, k4Edge_endpoints_ne]

theorem k4CoverEdge_exhaustive (i j : Fin 4) (hij : i ≠ j) :
    ∃ k : Fin 6, k4CoverEdge k = {i, j} := by
  have h : ∀ i j : Fin 4, i ≠ j → ∃ k : Fin 6, k4CoverEdge k = {i, j} := by decide
  exact h i j hij

def k4EdgeComplement : Fin 6 → Fin 6
  | 0 => 5 | 1 => 4 | 2 => 3 | 3 => 2 | 4 => 1 | 5 => 0

theorem k4EdgeComplement_involutive (k : Fin 6) : k4EdgeComplement (k4EdgeComplement k) = k := by
  fin_cases k <;> rfl

theorem k4CoverEdge_disjoint_forces (k l : Fin 6)
    (h : Disjoint (k4CoverEdge k) (k4CoverEdge l)) : l = k4EdgeComplement k := by
  have hh : ∀ k l : Fin 6, Disjoint (k4CoverEdge k) (k4CoverEdge l) → l = k4EdgeComplement k := by decide
  exact hh k l h

/-- Every covered coordinate can be assigned to exactly two of its original
masks. This is an actual assignment, not an assumed incidence profile. -/
theorem exists_four_mask_edge_assignment (A : Fin 4 → Finset ι)
    (hcover : ∀ x, 1 ≤ ∑ k, if x ∈ A k then (1 / 2 : ℝ) else 0) :
    ∃ F : ι → Fin 6, ∀ x i, i ∈ k4CoverEdge (F x) → x ∈ A i := by
  have hex : ∀ x, ∃ k : Fin 6, ∀ i ∈ k4CoverEdge k, x ∈ A i := by
    intro x
    obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp
      (show 1 < (fourMaskMembership A x).card by have h := four_mask_membership_card A hcover x; omega)
    obtain ⟨k, hk⟩ := k4CoverEdge_exhaustive i j hij
    refine ⟨k, ?_⟩
    intro v hv
    rw [hk] at hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact (Finset.mem_filter.mp hi).2
    · exact (Finset.mem_filter.mp hj).2
  choose F hF using hex
  exact ⟨F, hF⟩

/-- The absence of a covering pair forces every one of the six assigned
edge blocks to occur, regardless of the choice of assignment. -/
theorem four_mask_assignment_surjective (A : Fin 4 → Finset ι)
    (F : ι → Fin 6) (hF : ∀ x i, i ∈ k4CoverEdge (F x) → x ∈ A i)
    (hmiss : ∀ i j, i ≠ j → ∃ x, x ∉ A i ∧ x ∉ A j) : Function.Surjective F := by
  intro k
  obtain ⟨x, hx, hy⟩ := hmiss (k4EdgeFirst (k4EdgeComplement k))
    (k4EdgeSecond (k4EdgeComplement k)) (k4Edge_endpoints_ne _)
  have hd : Disjoint (k4CoverEdge (k4EdgeComplement k)) (k4CoverEdge (F x)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hix
    have ha := hF x i hix
    simp only [k4CoverEdge, Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hx ha
    · exact hy ha
  exact ⟨x, (k4CoverEdge_disjoint_forces _ _ hd).trans (k4EdgeComplement_involutive k)⟩

end
end Erdos539Geometry
