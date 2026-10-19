/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FourLeafBranch

namespace Erdos539Geometry
noncomputable section
open scoped Classical

def fourLeafShift (T : ℕ) : ℤ := 2 * (10 * (T : ℤ)) ^ 2 * T
def fourLeafCeiling (T : ℕ) : ℤ := 5 * (10 * (T : ℤ)) ^ 2 * T

theorem fourLeafEncode_abs_lt {T : ℕ} (hT : 0 < T) (a : Fin 7 → Fin T) (i : Fin 4) :
    |fourLeafEncode T a i| < fourLeafShift T := by
  have ht : (1 : ℤ) ≤ T := by exact_mod_cast hT
  have hb : (0 : ℤ) ≤ 10 * T := by positivity
  have ha (j : Fin 7) : |(a j : ℤ)| ≤ (T : ℤ) := by
    rw [abs_of_nonneg (Int.natCast_nonneg _)]
    have := (a j).isLt
    omega
  have he : |fourLeafRootSign i| = 1 := by
    unfold fourLeafRootSign
    split_ifs <;> norm_num
  have hd : |fourLeafSiblingSign i| = 1 := by
    unfold fourLeafSiblingSign
    split_ifs <;> norm_num
  have hr : |fourLeafRootSign i * (10 * (T : ℤ)) ^ 2 * (a 0 : ℤ)| ≤
      (10 * (T : ℤ)) ^ 2 * T := by
    rw [abs_mul, abs_mul, he, one_mul, abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul_of_nonneg_left (ha 0) (sq_nonneg _)
  have hs : |fourLeafSiblingSign i * (10 * (T : ℤ)) * (a (fourLeafSibling i) : ℤ)| ≤
      (10 * (T : ℤ)) * T := by
    rw [abs_mul, abs_mul, hd, one_mul, abs_of_nonneg hb]
    exact mul_le_mul_of_nonneg_left (ha _) hb
  have hbound : |fourLeafEncode T a i| ≤
      (10 * (T : ℤ)) ^ 2 * T + (10 * (T : ℤ)) * T + T := by
    change |fourLeafRootSign i * (10 * (T : ℤ)) ^ 2 * (a 0 : ℤ) +
      fourLeafSiblingSign i * (10 * (T : ℤ)) * (a (fourLeafSibling i) : ℤ) +
        (a (fourLeafLeaf i) : ℤ)| ≤ _
    exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add hr hs)) (ha _))
  have hb2 : 0 < (10 * (T : ℤ)) ^ 2 - 10 * T - 1 := by nlinarith
  have hh := mul_pos hb2 (show (0 : ℤ) < T by omega)
  unfold fourLeafShift
  nlinarith

theorem fourLeafBranch_shift_bounds {T : ℕ} (hT : 0 < T)
    {x : Fin 4 → ℤ} (hx : x ∈ fourLeafBranch T) (i : Fin 4) :
    0 < x i + fourLeafShift T ∧ x i + fourLeafShift T < fourLeafCeiling T := by
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
  have h := abs_lt.mp (fourLeafEncode_abs_lt hT a i)
  have ht : (0 : ℤ) < T := by exact_mod_cast hT
  have hc : 2 * fourLeafShift T < fourLeafCeiling T := by
    unfold fourLeafShift fourLeafCeiling
    nlinarith [mul_pos (sq_pos_of_pos (show (0 : ℤ) < 10 * T by positivity)) ht]
  constructor <;> omega

end
end Erdos539Geometry
