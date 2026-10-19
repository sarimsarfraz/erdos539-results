/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SignClasses
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
variable {ι : Type*} [Fintype ι]

/-- The sharp three-dimensional fan exponent, with an explicit absolute loss.
This is a geometric lower bound, independent of any arithmetic encoding. -/
theorem three_dimensional_log_fan_bound (hd : Fintype.card ι = 3)
    {F : Finset (ι → ℝ)} (hF : F.Nonempty) :
    (5 / 8 : ℝ) * Real.log F.card - 4 * Real.log 2 ≤ Real.log (maxFan F) := by
  classical
  obtain ⟨a, ha, P, E, hEF, hE, hsize, hPlo, hmask⟩ :=
    exists_large_three_dimensional_sign_class hd hF
  have hn : (0 : ℝ) < F.card := by exact_mod_cast hF.card_pos
  have hm : (0 : ℝ) < E.card := by exact_mod_cast hE.card_pos
  have hM : (0 : ℝ) < maxFan F := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxFan hF))
  have hnlog : 0 ≤ Real.log F.card := Real.log_nonneg (by exact_mod_cast hF.card_pos)
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 4
    norm_num at h
    exact h
  have hsize' := Real.log_le_log hn (show (F.card : ℝ) ≤ 16 * E.card by exact_mod_cast hsize)
  rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) hm.ne', h16] at hsize'
  have hP : (projection E P).card ≤ maxFan F := projection_sign_class_le_maxFan hEF ha P hmask
  have hPhi : P.card ≤ 3 := by simpa only [hd] using Finset.card_le_univ P
  by_cases hPfull : P.card = 3
  · have hPeq : P = Finset.univ := Finset.eq_univ_of_card P (by simpa only [hd] using hPfull)
    have he : (projection E P).card = E.card := projection_card_eq_card_of_covers E P (by intro i; rw [hPeq]; exact Finset.mem_univ i)
    rw [he] at hP
    have hl := Real.log_le_log hm (show (E.card : ℝ) ≤ maxFan F by exact_mod_cast hP)
    linarith
  · have hPtwo : P.card = 2 := by omega
    let Q := Finset.univ \ P
    have hQone : Q.card = 1 := by
      dsimp only [Q]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ P), Finset.card_univ, hd, hPtwo]
    have hcover : ∀ i, i ∈ P ∨ i ∈ Q := by
      intro i
      by_cases hi : i ∈ P
      · exact Or.inl hi
      · exact Or.inr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩)
    have hQ : (projection E Q).card ≤ maxFan F := by
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hQone
      rw [hj]
      exact (projection_singleton_card_le_maxFan E j).trans (maxFan_mono hEF)
    have hprune := one_sided_log_pruning hE P Q hcover
      (2 / 3) 1 ((2 / 3) * Real.log 2) 0 (by norm_num) (by norm_num)
      (fun G hG ↦ planar_log_fan_bound (by simpa only [Fintype.card_coe] using hPtwo) hG)
      (fun G _ ↦ by rw [one_dimensional_maxFan_eq_card (by simpa only [Fintype.card_coe] using hQone)]; simp)
    have hPE : (0 : ℝ) < (projection E P).card := by exact_mod_cast (hE.image (project P)).card_pos
    have hQE : (0 : ℝ) < (projection E Q).card := by exact_mod_cast (hE.image (project Q)).card_pos
    have hME : (0 : ℝ) < maxFan E := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxFan hE))
    have hpLog := Real.log_le_log hPE (show ((projection E P).card : ℝ) ≤ maxFan F by exact_mod_cast hP)
    have hqLog := Real.log_le_log hQE (show ((projection E Q).card : ℝ) ≤ maxFan F by exact_mod_cast hQ)
    have hfanLog := Real.log_le_log hME (show (maxFan E : ℝ) ≤ maxFan F by exact_mod_cast maxFan_mono hEF)
    linarith

/-- Explicit power form of the three-dimensional lower bound. -/
theorem three_dimensional_fan_lower_bound (hd : Fintype.card ι = 3)
    {F : Finset (ι → ℝ)} (hF : F.Nonempty) :
    (F.card : ℝ) ^ (5 / 8 : ℝ) / 16 ≤ maxFan F := by
  have hn : (0 : ℝ) < F.card := by exact_mod_cast hF.card_pos
  have hM : (0 : ℝ) < maxFan F := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxFan hF))
  have hpow : 0 < (F.card : ℝ) ^ (5 / 8 : ℝ) := Real.rpow_pos_of_pos hn _
  apply (Real.log_le_log_iff (div_pos hpow (by norm_num)) hM).mp
  rw [Real.log_div hpow.ne' (by norm_num : (16 : ℝ) ≠ 0), Real.log_rpow hn]
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 4
    norm_num at h
    exact h
  rw [h16]
  exact three_dimensional_log_fan_bound hd hF

theorem three_dimensional_posDiff_lower_bound (hd : Fintype.card ι = 3)
    {F : Finset (ι → ℝ)} (hF : F.Nonempty) :
    (F.card : ℝ) ^ (5 / 8 : ℝ) / 16 ≤ (posDiff F).card :=
  (three_dimensional_fan_lower_bound hd hF).trans (by exact_mod_cast maxFan_le_card_posDiff F)

end
end Erdos539Geometry
