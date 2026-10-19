/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SharpExponentBounds
import Mathlib.Tactic.FinCases

namespace Erdos539Geometry

/-- Exact kernel-checked value at dimension 2. -/
theorem sharpExponent_2 : sharpExponent 2 = (2 / 3 : ℚ) := by
  rw [show 2 = 0 + 2 by rfl, sharpExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 1 ↦ combineExponent (sharpExponent (i.val + 1)) (sharpExponent (1 - i.val)))
      (Finset.mem_univ (⟨0, by decide⟩ : Fin 1))
    apply le_trans h
    norm_num [combineExponent, sharpExponent_one]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i; norm_num [combineExponent, sharpExponent_one]

/-- Exact kernel-checked value at dimension 3. -/
theorem sharpExponent_3 : sharpExponent 3 = (5 / 8 : ℚ) := by
  rw [show 3 = 1 + 2 by rfl, sharpExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 2 ↦ combineExponent (sharpExponent (i.val + 1)) (sharpExponent (2 - i.val)))
      (Finset.mem_univ (⟨0, by decide⟩ : Fin 2))
    apply le_trans h
    norm_num [combineExponent, sharpExponent_one, sharpExponent_2]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, sharpExponent_one, sharpExponent_2]

/-- Exact kernel-checked value at dimension 4. -/
theorem sharpExponent_4 : sharpExponent 4 = (4 / 7 : ℚ) := by
  rw [show 4 = 2 + 2 by rfl, sharpExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 3 ↦ combineExponent (sharpExponent (i.val + 1)) (sharpExponent (3 - i.val)))
      (Finset.mem_univ (⟨1, by decide⟩ : Fin 3))
    apply le_trans h
    norm_num [combineExponent, sharpExponent_one, sharpExponent_2, sharpExponent_3]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, sharpExponent_one, sharpExponent_2, sharpExponent_3]

/-- Exact kernel-checked value at dimension 5. -/
theorem sharpExponent_5 : sharpExponent 5 = (31 / 55 : ℚ) := by
  rw [show 5 = 3 + 2 by rfl, sharpExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 4 ↦ combineExponent (sharpExponent (i.val + 1)) (sharpExponent (4 - i.val)))
      (Finset.mem_univ (⟨1, by decide⟩ : Fin 4))
    apply le_trans h
    norm_num [combineExponent, sharpExponent_one, sharpExponent_2, sharpExponent_3, sharpExponent_4]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, sharpExponent_one, sharpExponent_2, sharpExponent_3, sharpExponent_4]

/-- Exact kernel-checked value at dimension 6. -/
theorem sharpExponent_6 : sharpExponent 6 = (26 / 47 : ℚ) := by
  rw [show 6 = 4 + 2 by rfl, sharpExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 5 ↦ combineExponent (sharpExponent (i.val + 1)) (sharpExponent (5 - i.val)))
      (Finset.mem_univ (⟨1, by decide⟩ : Fin 5))
    apply le_trans h
    norm_num [combineExponent, sharpExponent_one, sharpExponent_2, sharpExponent_3, sharpExponent_4, sharpExponent_5]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, sharpExponent_one, sharpExponent_2, sharpExponent_3, sharpExponent_4, sharpExponent_5]

/-- Exact kernel-checked value at dimension 7. -/
theorem sharpExponent_7 : sharpExponent 7 = (67 / 123 : ℚ) := by
  rw [show 7 = 5 + 2 by rfl, sharpExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 6 ↦ combineExponent (sharpExponent (i.val + 1)) (sharpExponent (6 - i.val)))
      (Finset.mem_univ (⟨2, by decide⟩ : Fin 6))
    apply le_trans h
    norm_num [combineExponent, sharpExponent_one, sharpExponent_2, sharpExponent_3, sharpExponent_4, sharpExponent_5, sharpExponent_6]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, sharpExponent_one, sharpExponent_2, sharpExponent_3, sharpExponent_4, sharpExponent_5, sharpExponent_6]

/-- Exact kernel-checked value at dimension 8. -/
theorem sharpExponent_8 : sharpExponent 8 = (8 / 15 : ℚ) := by
  rw [show 8 = 6 + 2 by rfl, sharpExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 7 ↦ combineExponent (sharpExponent (i.val + 1)) (sharpExponent (7 - i.val)))
      (Finset.mem_univ (⟨3, by decide⟩ : Fin 7))
    apply le_trans h
    norm_num [combineExponent, sharpExponent_one, sharpExponent_2, sharpExponent_3, sharpExponent_4, sharpExponent_5, sharpExponent_6, sharpExponent_7]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, sharpExponent_one, sharpExponent_2, sharpExponent_3, sharpExponent_4, sharpExponent_5, sharpExponent_6, sharpExponent_7]

/-- Exact kernel-checked value at dimension 9. -/
theorem sharpExponent_9 : sharpExponent 9 = (437 / 822 : ℚ) := by
  rw [show 9 = 7 + 2 by rfl, sharpExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 8 ↦ combineExponent (sharpExponent (i.val + 1)) (sharpExponent (8 - i.val)))
      (Finset.mem_univ (⟨3, by decide⟩ : Fin 8))
    apply le_trans h
    norm_num [combineExponent, sharpExponent_one, sharpExponent_2, sharpExponent_3, sharpExponent_4, sharpExponent_5, sharpExponent_6, sharpExponent_7, sharpExponent_8]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, sharpExponent_one, sharpExponent_2, sharpExponent_3, sharpExponent_4, sharpExponent_5, sharpExponent_6, sharpExponent_7, sharpExponent_8]

/-- Exact kernel-checked value at dimension 10. -/
theorem sharpExponent_10 : sharpExponent 10 = (370 / 699 : ℚ) := by
  rw [show 10 = 8 + 2 by rfl, sharpExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 9 ↦ combineExponent (sharpExponent (i.val + 1)) (sharpExponent (9 - i.val)))
      (Finset.mem_univ (⟨3, by decide⟩ : Fin 9))
    apply le_trans h
    norm_num [combineExponent, sharpExponent_one, sharpExponent_2, sharpExponent_3, sharpExponent_4, sharpExponent_5, sharpExponent_6, sharpExponent_7, sharpExponent_8, sharpExponent_9]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, sharpExponent_one, sharpExponent_2, sharpExponent_3, sharpExponent_4, sharpExponent_5, sharpExponent_6, sharpExponent_7, sharpExponent_8, sharpExponent_9]

/-- Exact kernel-checked value at dimension 11. -/
theorem sharpExponent_11 : sharpExponent 11 = (961 / 1822 : ℚ) := by
  rw [show 11 = 9 + 2 by rfl, sharpExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 10 ↦ combineExponent (sharpExponent (i.val + 1)) (sharpExponent (10 - i.val)))
      (Finset.mem_univ (⟨3, by decide⟩ : Fin 10))
    apply le_trans h
    norm_num [combineExponent, sharpExponent_one, sharpExponent_2, sharpExponent_3, sharpExponent_4, sharpExponent_5, sharpExponent_6, sharpExponent_7, sharpExponent_8, sharpExponent_9, sharpExponent_10]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, sharpExponent_one, sharpExponent_2, sharpExponent_3, sharpExponent_4, sharpExponent_5, sharpExponent_6, sharpExponent_7, sharpExponent_8, sharpExponent_9, sharpExponent_10]

/-- Exact kernel-checked value at dimension 12. -/
theorem sharpExponent_12 : sharpExponent 12 = (116 / 221 : ℚ) := by
  rw [show 12 = 10 + 2 by rfl, sharpExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 11 ↦ combineExponent (sharpExponent (i.val + 1)) (sharpExponent (11 - i.val)))
      (Finset.mem_univ (⟨3, by decide⟩ : Fin 11))
    apply le_trans h
    norm_num [combineExponent, sharpExponent_one, sharpExponent_2, sharpExponent_3, sharpExponent_4, sharpExponent_5, sharpExponent_6, sharpExponent_7, sharpExponent_8, sharpExponent_9, sharpExponent_10, sharpExponent_11]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, sharpExponent_one, sharpExponent_2, sharpExponent_3, sharpExponent_4, sharpExponent_5, sharpExponent_6, sharpExponent_7, sharpExponent_8, sharpExponent_9, sharpExponent_10, sharpExponent_11]

/-- Exact kernel-checked value at dimension 13. -/
theorem sharpExponent_13 : sharpExponent 13 = (181 / 346 : ℚ) := by
  rw [show 13 = 11 + 2 by rfl, sharpExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 12 ↦ combineExponent (sharpExponent (i.val + 1)) (sharpExponent (12 - i.val)))
      (Finset.mem_univ (⟨4, by decide⟩ : Fin 12))
    apply le_trans h
    norm_num [combineExponent, sharpExponent_one, sharpExponent_2, sharpExponent_3, sharpExponent_4, sharpExponent_5, sharpExponent_6, sharpExponent_7, sharpExponent_8, sharpExponent_9, sharpExponent_10, sharpExponent_11, sharpExponent_12]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, sharpExponent_one, sharpExponent_2, sharpExponent_3, sharpExponent_4, sharpExponent_5, sharpExponent_6, sharpExponent_7, sharpExponent_8, sharpExponent_9, sharpExponent_10, sharpExponent_11, sharpExponent_12]

/-- Exact kernel-checked value at dimension 14. -/
theorem sharpExponent_14 : sharpExponent 14 = (766 / 1471 : ℚ) := by
  rw [show 14 = 12 + 2 by rfl, sharpExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 13 ↦ combineExponent (sharpExponent (i.val + 1)) (sharpExponent (13 - i.val)))
      (Finset.mem_univ (⟨5, by decide⟩ : Fin 13))
    apply le_trans h
    norm_num [combineExponent, sharpExponent_one, sharpExponent_2, sharpExponent_3, sharpExponent_4, sharpExponent_5, sharpExponent_6, sharpExponent_7, sharpExponent_8, sharpExponent_9, sharpExponent_10, sharpExponent_11, sharpExponent_12, sharpExponent_13]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, sharpExponent_one, sharpExponent_2, sharpExponent_3, sharpExponent_4, sharpExponent_5, sharpExponent_6, sharpExponent_7, sharpExponent_8, sharpExponent_9, sharpExponent_10, sharpExponent_11, sharpExponent_12, sharpExponent_13]

/-- Exact kernel-checked value at dimension 15. -/
theorem sharpExponent_15 : sharpExponent 15 = (221 / 426 : ℚ) := by
  rw [show 15 = 13 + 2 by rfl, sharpExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 14 ↦ combineExponent (sharpExponent (i.val + 1)) (sharpExponent (14 - i.val)))
      (Finset.mem_univ (⟨6, by decide⟩ : Fin 14))
    apply le_trans h
    norm_num [combineExponent, sharpExponent_one, sharpExponent_2, sharpExponent_3, sharpExponent_4, sharpExponent_5, sharpExponent_6, sharpExponent_7, sharpExponent_8, sharpExponent_9, sharpExponent_10, sharpExponent_11, sharpExponent_12, sharpExponent_13, sharpExponent_14]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, sharpExponent_one, sharpExponent_2, sharpExponent_3, sharpExponent_4, sharpExponent_5, sharpExponent_6, sharpExponent_7, sharpExponent_8, sharpExponent_9, sharpExponent_10, sharpExponent_11, sharpExponent_12, sharpExponent_13, sharpExponent_14]

/-- Exact kernel-checked value at dimension 16. -/
theorem sharpExponent_16 : sharpExponent 16 = (16 / 31 : ℚ) := by
  rw [show 16 = 14 + 2 by rfl, sharpExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 15 ↦ combineExponent (sharpExponent (i.val + 1)) (sharpExponent (15 - i.val)))
      (Finset.mem_univ (⟨7, by decide⟩ : Fin 15))
    apply le_trans h
    norm_num [combineExponent, sharpExponent_one, sharpExponent_2, sharpExponent_3, sharpExponent_4, sharpExponent_5, sharpExponent_6, sharpExponent_7, sharpExponent_8, sharpExponent_9, sharpExponent_10, sharpExponent_11, sharpExponent_12, sharpExponent_13, sharpExponent_14, sharpExponent_15]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, sharpExponent_one, sharpExponent_2, sharpExponent_3, sharpExponent_4, sharpExponent_5, sharpExponent_6, sharpExponent_7, sharpExponent_8, sharpExponent_9, sharpExponent_10, sharpExponent_11, sharpExponent_12, sharpExponent_13, sharpExponent_14, sharpExponent_15]

end Erdos539Geometry
