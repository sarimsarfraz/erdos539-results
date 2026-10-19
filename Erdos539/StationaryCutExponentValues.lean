/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationaryCutExponents
import Mathlib.Tactic.FinCases

namespace Erdos539Geometry

theorem stationaryCutExponent_2 : stationaryCutExponent 2 = (4 / 7 : ℚ) := by
  rw [show 2 = 0 + 2 by rfl, stationaryCutExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 1 ↦ combineExponent (stationaryCutExponent (i.val + 1))
        (stationaryCutExponent (1 - i.val)))
      (Finset.mem_univ (⟨0, by decide⟩ : Fin 1))
    apply le_trans h
    norm_num [combineExponent, stationaryCutExponent_one]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i ; norm_num [combineExponent, stationaryCutExponent_one]

theorem stationaryCutExponent_3 : stationaryCutExponent 3 = (26 / 47 : ℚ) := by
  rw [show 3 = 1 + 2 by rfl, stationaryCutExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 2 ↦ combineExponent (stationaryCutExponent (i.val + 1))
        (stationaryCutExponent (2 - i.val)))
      (Finset.mem_univ (⟨0, by decide⟩ : Fin 2))
    apply le_trans h
    norm_num [combineExponent, stationaryCutExponent_one, stationaryCutExponent_2]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, stationaryCutExponent_one, stationaryCutExponent_2]

theorem stationaryCutExponent_4 : stationaryCutExponent 4 = (8 / 15 : ℚ) := by
  rw [show 4 = 2 + 2 by rfl, stationaryCutExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 3 ↦ combineExponent (stationaryCutExponent (i.val + 1))
        (stationaryCutExponent (3 - i.val)))
      (Finset.mem_univ (⟨1, by decide⟩ : Fin 3))
    apply le_trans h
    norm_num [combineExponent, stationaryCutExponent_one, stationaryCutExponent_2, stationaryCutExponent_3]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, stationaryCutExponent_one, stationaryCutExponent_2, stationaryCutExponent_3]

theorem stationaryCutExponent_5 : stationaryCutExponent 5 = (370 / 699 : ℚ) := by
  rw [show 5 = 3 + 2 by rfl, stationaryCutExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 4 ↦ combineExponent (stationaryCutExponent (i.val + 1))
        (stationaryCutExponent (4 - i.val)))
      (Finset.mem_univ (⟨1, by decide⟩ : Fin 4))
    apply le_trans h
    norm_num [combineExponent, stationaryCutExponent_one, stationaryCutExponent_2, stationaryCutExponent_3, stationaryCutExponent_4]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, stationaryCutExponent_one, stationaryCutExponent_2, stationaryCutExponent_3, stationaryCutExponent_4]

theorem stationaryCutExponent_6 : stationaryCutExponent 6 = (116 / 221 : ℚ) := by
  rw [show 6 = 4 + 2 by rfl, stationaryCutExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 5 ↦ combineExponent (stationaryCutExponent (i.val + 1))
        (stationaryCutExponent (5 - i.val)))
      (Finset.mem_univ (⟨1, by decide⟩ : Fin 5))
    apply le_trans h
    norm_num [combineExponent, stationaryCutExponent_one, stationaryCutExponent_2, stationaryCutExponent_3, stationaryCutExponent_4, stationaryCutExponent_5]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, stationaryCutExponent_one, stationaryCutExponent_2, stationaryCutExponent_3, stationaryCutExponent_4, stationaryCutExponent_5]

theorem stationaryCutExponent_7 : stationaryCutExponent 7 = (766 / 1471 : ℚ) := by
  rw [show 7 = 5 + 2 by rfl, stationaryCutExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 6 ↦ combineExponent (stationaryCutExponent (i.val + 1))
        (stationaryCutExponent (6 - i.val)))
      (Finset.mem_univ (⟨2, by decide⟩ : Fin 6))
    apply le_trans h
    norm_num [combineExponent, stationaryCutExponent_one, stationaryCutExponent_2, stationaryCutExponent_3, stationaryCutExponent_4, stationaryCutExponent_5, stationaryCutExponent_6]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, stationaryCutExponent_one, stationaryCutExponent_2, stationaryCutExponent_3, stationaryCutExponent_4, stationaryCutExponent_5, stationaryCutExponent_6]

theorem stationaryCutExponent_8 : stationaryCutExponent 8 = (16 / 31 : ℚ) := by
  rw [show 8 = 6 + 2 by rfl, stationaryCutExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 7 ↦ combineExponent (stationaryCutExponent (i.val + 1))
        (stationaryCutExponent (7 - i.val)))
      (Finset.mem_univ (⟨3, by decide⟩ : Fin 7))
    apply le_trans h
    norm_num [combineExponent, stationaryCutExponent_one, stationaryCutExponent_2, stationaryCutExponent_3, stationaryCutExponent_4, stationaryCutExponent_5, stationaryCutExponent_6, stationaryCutExponent_7]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, stationaryCutExponent_one, stationaryCutExponent_2, stationaryCutExponent_3, stationaryCutExponent_4, stationaryCutExponent_5, stationaryCutExponent_6, stationaryCutExponent_7]

theorem stationaryCutExponent_9 : stationaryCutExponent 9 = (1238 / 2403 : ℚ) := by
  rw [show 9 = 7 + 2 by rfl, stationaryCutExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 8 ↦ combineExponent (stationaryCutExponent (i.val + 1))
        (stationaryCutExponent (8 - i.val)))
      (Finset.mem_univ (⟨3, by decide⟩ : Fin 8))
    apply le_trans h
    norm_num [combineExponent, stationaryCutExponent_one, stationaryCutExponent_2, stationaryCutExponent_3, stationaryCutExponent_4, stationaryCutExponent_5, stationaryCutExponent_6, stationaryCutExponent_7, stationaryCutExponent_8]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, stationaryCutExponent_one, stationaryCutExponent_2, stationaryCutExponent_3, stationaryCutExponent_4, stationaryCutExponent_5, stationaryCutExponent_6, stationaryCutExponent_7, stationaryCutExponent_8]

theorem stationaryCutExponent_10 : stationaryCutExponent 10 = (3508 / 6823 : ℚ) := by
  rw [show 10 = 8 + 2 by rfl, stationaryCutExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 9 ↦ combineExponent (stationaryCutExponent (i.val + 1))
        (stationaryCutExponent (9 - i.val)))
      (Finset.mem_univ (⟨3, by decide⟩ : Fin 9))
    apply le_trans h
    norm_num [combineExponent, stationaryCutExponent_one, stationaryCutExponent_2, stationaryCutExponent_3, stationaryCutExponent_4, stationaryCutExponent_5, stationaryCutExponent_6, stationaryCutExponent_7, stationaryCutExponent_8, stationaryCutExponent_9]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, stationaryCutExponent_one, stationaryCutExponent_2, stationaryCutExponent_3, stationaryCutExponent_4, stationaryCutExponent_5, stationaryCutExponent_6, stationaryCutExponent_7, stationaryCutExponent_8, stationaryCutExponent_9]

theorem stationaryCutExponent_11 : stationaryCutExponent 11 = (23258 / 45323 : ℚ) := by
  rw [show 11 = 9 + 2 by rfl, stationaryCutExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 10 ↦ combineExponent (stationaryCutExponent (i.val + 1))
        (stationaryCutExponent (10 - i.val)))
      (Finset.mem_univ (⟨3, by decide⟩ : Fin 10))
    apply le_trans h
    norm_num [combineExponent, stationaryCutExponent_one, stationaryCutExponent_2, stationaryCutExponent_3, stationaryCutExponent_4, stationaryCutExponent_5, stationaryCutExponent_6, stationaryCutExponent_7, stationaryCutExponent_8, stationaryCutExponent_9, stationaryCutExponent_10]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, stationaryCutExponent_one, stationaryCutExponent_2, stationaryCutExponent_3, stationaryCutExponent_4, stationaryCutExponent_5, stationaryCutExponent_6, stationaryCutExponent_7, stationaryCutExponent_8, stationaryCutExponent_9, stationaryCutExponent_10]

theorem stationaryCutExponent_12 : stationaryCutExponent 12 = (488 / 953 : ℚ) := by
  rw [show 12 = 10 + 2 by rfl, stationaryCutExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 11 ↦ combineExponent (stationaryCutExponent (i.val + 1))
        (stationaryCutExponent (11 - i.val)))
      (Finset.mem_univ (⟨3, by decide⟩ : Fin 11))
    apply le_trans h
    norm_num [combineExponent, stationaryCutExponent_one, stationaryCutExponent_2, stationaryCutExponent_3, stationaryCutExponent_4, stationaryCutExponent_5, stationaryCutExponent_6, stationaryCutExponent_7, stationaryCutExponent_8, stationaryCutExponent_9, stationaryCutExponent_10, stationaryCutExponent_11]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, stationaryCutExponent_one, stationaryCutExponent_2, stationaryCutExponent_3, stationaryCutExponent_4, stationaryCutExponent_5, stationaryCutExponent_6, stationaryCutExponent_7, stationaryCutExponent_8, stationaryCutExponent_9, stationaryCutExponent_10, stationaryCutExponent_11]

theorem stationaryCutExponent_13 : stationaryCutExponent 13 = (22654 / 44323 : ℚ) := by
  rw [show 13 = 11 + 2 by rfl, stationaryCutExponent_rec]
  apply le_antisymm
  · have h := Finset.inf'_le
      (fun i : Fin 12 ↦ combineExponent (stationaryCutExponent (i.val + 1))
        (stationaryCutExponent (12 - i.val)))
      (Finset.mem_univ (⟨4, by decide⟩ : Fin 12))
    apply le_trans h
    norm_num [combineExponent, stationaryCutExponent_one, stationaryCutExponent_2, stationaryCutExponent_3, stationaryCutExponent_4, stationaryCutExponent_5, stationaryCutExponent_6, stationaryCutExponent_7, stationaryCutExponent_8, stationaryCutExponent_9, stationaryCutExponent_10, stationaryCutExponent_11, stationaryCutExponent_12]
  · apply Finset.le_inf'
    intro i _hi
    fin_cases i <;> norm_num [combineExponent, stationaryCutExponent_one, stationaryCutExponent_2, stationaryCutExponent_3, stationaryCutExponent_4, stationaryCutExponent_5, stationaryCutExponent_6, stationaryCutExponent_7, stationaryCutExponent_8, stationaryCutExponent_9, stationaryCutExponent_10, stationaryCutExponent_11, stationaryCutExponent_12]

end Erdos539Geometry
