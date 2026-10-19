/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteEntropy
import Mathlib.Data.Finset.Lattice.Basic

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- Fractional covering for a normalized monotone set function with
diminishing increments. The finite family may have repeated masks and
zero weights, and the cover condition is needed only on the target mask. -/
theorem finite_fractional_cover {ι κ : Type*} [Fintype κ]
    (f : Finset ι → ℝ) (hf0 : f ∅ = 0)
    (hmono : Monotone f)
    (hinc : ∀ {I J : Finset ι}, I ⊆ J → ∀ i, i ∉ J →
      f (insert i J) - f J ≤ f (insert i I) - f I)
    (A : κ → Finset ι) (c : κ → ℝ) (hc : ∀ k, 0 ≤ c k)
    (U : Finset ι) (hcover : ∀ i ∈ U, 1 ≤ ∑ k, if i ∈ A k then c k else 0) :
    f U ≤ ∑ k, c k * f (A k ∩ U) := by
  induction U using Finset.induction_on with
  | empty => simp [hf0]
  | @insert i J hi ih =>
    have hJ : ∀ j ∈ J, 1 ≤ ∑ k, if j ∈ A k then c k else 0 :=
      fun j hj ↦ hcover j (Finset.mem_insert_of_mem hj)
    have hind := ih hJ
    let delta := f (insert i J) - f J
    have hd : 0 ≤ delta := sub_nonneg.mpr (hmono (Finset.subset_insert i J))
    have hs := mul_le_mul_of_nonneg_right (hcover i (Finset.mem_insert_self i J)) hd
    simp only [one_mul, Finset.sum_mul, ite_mul, zero_mul] at hs
    have hpoint (k : κ) : (if i ∈ A k then c k * delta else 0) ≤
        c k * (f (A k ∩ insert i J) - f (A k ∩ J)) := by
      by_cases hk : i ∈ A k
      · have he : A k ∩ insert i J = insert i (A k ∩ J) := by
          ext x; simp only [Finset.mem_inter, Finset.mem_insert]; aesop
        rw [if_pos hk, he]
        exact mul_le_mul_of_nonneg_left (hinc Finset.inter_subset_right i hi) (hc k)
      · have he : A k ∩ insert i J = A k ∩ J := by
          ext x; simp only [Finset.mem_inter, Finset.mem_insert]; aesop
        simp only [if_neg hk, he, sub_self, mul_zero, le_refl]
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun k _ ↦ hpoint k)
    simp only [mul_sub, Finset.sum_sub_distrib] at hsum
    dsimp [delta] at hs
    linarith

end
end Erdos539Geometry
