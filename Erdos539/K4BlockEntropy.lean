/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ThreeBlockEntropy

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {ι : Type*}

/-- The six blocks correspond, in order, to edges 12,13,14,23,24,34. -/
def k4Star (a b c d e f : Finset ι) : Fin 4 → Finset ι
  | 0 => a ∪ b ∪ c
  | 1 => a ∪ d ∪ e
  | 2 => b ∪ d ∪ f
  | 3 => c ∪ e ∪ f

def k4Triangle (a b c d e f : Finset ι) : Fin 4 → Finset ι
  | 0 => d ∪ e ∪ f
  | 1 => b ∪ c ∪ f
  | 2 => a ∪ c ∪ e
  | 3 => a ∪ b ∪ d

/-- Each complementary triangle is controlled by the other three stars. -/
theorem k4_triangle_entropy_bound (H : Finset ι → ℝ) (h0 : H ∅ = 0)
    (hCMI : ∀ A B C, 0 ≤ maskCMI H A B C) (a b c d e f : Finset ι) (v : Fin 4) :
    H (k4Triangle a b c d e f v) + H (a ∪ b ∪ c ∪ d ∪ e ∪ f) ≤
      (∑ w, H (k4Star a b c d e f w)) - H (k4Star a b c d e f v) := by
  have h₀ := three_block_entropy_inequality H h0 hCMI a b c f e d
  have h₁ := three_block_entropy_inequality H h0 hCMI a d e f c b
  have h₂ := three_block_entropy_inequality H h0 hCMI b d f e c a
  have h₃ := three_block_entropy_inequality H h0 hCMI c e f d b a
  have hsum : (∑ w, H (k4Star a b c d e f w)) =
      H (a ∪ b ∪ c) + H (a ∪ d ∪ e) + H (b ∪ d ∪ f) + H (c ∪ e ∪ f) := by
    rw [show (Finset.univ : Finset (Fin 4)) = {0, 1, 2, 3} by decide]
    simp [k4Star, add_assoc]
  rw [hsum]
  fin_cases v <;> simp only [k4Star, k4Triangle] <;>
    simp only [Finset.union_left_comm, Finset.union_comm] at * <;> linarith

theorem k4_entropy_gap_inequality (H : Finset ι → ℝ) (h0 : H ∅ = 0)
    (hCMI : ∀ A B C, 0 ≤ maskCMI H A B C) (a b c d e f : Finset ι) :
    (∑ v, H (k4Triangle a b c d e f v)) ≤
      3 * (∑ v, H (k4Star a b c d e f v)) - 4 * H (a ∪ b ∪ c ∪ d ∪ e ∪ f) := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun v _ ↦ k4_triangle_entropy_bound H h0 hCMI a b c d e f v)
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith

theorem k4_fractional_gap_inequality (H : Finset ι → ℝ) (h0 : H ∅ = 0)
    (hCMI : ∀ A B C, 0 ≤ maskCMI H A B C) (a b c d e f : Finset ι) :
    (1 / 2 : ℝ) * (∑ v, H (k4Triangle a b c d e f v)) - H (a ∪ b ∪ c ∪ d ∪ e ∪ f) ≤
      3 * ((1 / 2 : ℝ) * (∑ v, H (k4Star a b c d e f v)) - H (a ∪ b ∪ c ∪ d ∪ e ∪ f)) := by
  linarith [k4_entropy_gap_inequality H h0 hCMI a b c d e f]

theorem k4_triangle_of_star_bounds (H : Finset ι → ℝ) (h0 : H ∅ = 0)
    (hCMI : ∀ A B C, 0 ≤ maskCMI H A B C) (a b c d e f : Finset ι)
    (h : ℝ) (hstar : ∀ v, H (k4Star a b c d e f v) ≤ h) (v : Fin 4) :
    H (k4Triangle a b c d e f v) ≤ 3 * h - H (a ∪ b ∪ c ∪ d ∪ e ∪ f) := by
  have hb := k4_triangle_entropy_bound H h0 hCMI a b c d e f v
  have hsum := Finset.sum_le_sum (s := Finset.univ.erase v) (fun w _ ↦ hstar w)
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ v)] at hsum
  simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ v),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  norm_num only at hsum
  linarith

/-- The inequality applies to the literal marginals of a single finite law,
including zero atoms and constant blocks. -/
theorem coordinate_k4_entropy_gap {S : Finset (ι → ℝ)} (ν : S → ℝ)
    (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) (a b c d e f : Finset ι) :
    (∑ v, coordinateProjectionEntropy S ν (k4Triangle a b c d e f v)) ≤
      3 * (∑ v, coordinateProjectionEntropy S ν (k4Star a b c d e f v)) -
        4 * coordinateProjectionEntropy S ν (a ∪ b ∪ c ∪ d ∪ e ∪ f) :=
  k4_entropy_gap_inequality _ (coordinateProjectionEntropy_empty S ν hν hs)
    (coordinate_maskCMI_nonneg S ν hν) a b c d e f

end
end Erdos539Geometry
