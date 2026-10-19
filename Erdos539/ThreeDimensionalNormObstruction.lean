/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ThreeDimensionalCalibrationEnergy
import Erdos539.CountingFanPower
import Erdos539.FanNormEntropyEquivalence

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
local instance threeDimensionalNormDecidableEq : DecidableEq (CalibrationThreeCoordinates → ℝ) := Classical.decEq _

theorem calibrationThree_coordinate_count : Fintype.card CalibrationThreeCoordinates = 3 := by decide

theorem calibrationThree_counting_power_bound {T : ℕ} (hT : 0 < T) {p : ℝ} (hp : 0 < p) :
    (fanPowerSum (positiveDifferenceChannel (calibrationThreeReal T)) (fun _ ↦ 1) (fun _ ↦ 1) p) ^ (4 / p) ≤
      16 * (T : ℝ) ^ (32 / p + 10) := by
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hM : ∀ a : calibrationThreeReal T, ((fan (calibrationThreeReal T) a.val).card : ℝ) ≤ 4 * (T : ℝ) ^ 5 := by
    intro a
    exact_mod_cast (card_fan_le_maxFan a.property).trans (calibrationThreeReal_maxFan hT)
  have h := counting_fanPowerNorm_le (calibrationThreeReal_nonempty hT) hp (by positivity) hM
  rw [calibrationThreeReal_card hT, Nat.cast_pow] at h
  have he : (((T : ℝ) ^ 8) ^ (4 / p)) * (4 * (T : ℝ) ^ 5) ^ 2 =
      16 * (T : ℝ) ^ (32 / p + 10) := by
    calc
      _ = 16 * ((T : ℝ) ^ ((8 : ℝ) * (4 / p)) * (T : ℝ) ^ 10) := by
        rw [Real.rpow_mul ht.le]
        norm_num only [Real.rpow_ofNat]
        ring
      _ = _ := by
        rw [← Real.rpow_natCast (T : ℝ) 10, ← Real.rpow_add ht]
        congr 2
        push_cast
        ring
  rwa [he] at h

/-- An explicit Archimedean power comparison; no numerical cutoff is assumed. -/
theorem exists_natural_power_gap {a b k C : ℝ} (hab : b < a) (hk : 0 < k) (hC : 0 < C) :
    ∃ T : ℕ, 2 ≤ T ∧ C * (T : ℝ) ^ b < k * (T : ℝ) ^ a := by
  obtain ⟨T, hT⟩ := exists_nat_gt (max 2 (Real.exp ((Real.log (C / k) + 1) / (a - b))))
  have hT2 : (2 : ℝ) < T := (le_max_left _ _).trans_lt hT
  have hTp : (0 : ℝ) < T := by linarith
  have hexp := (le_max_right _ _).trans_lt hT
  have hlog := Real.log_lt_log (Real.exp_pos _) hexp
  rw [Real.log_exp] at hlog
  have hgap := (div_lt_iff₀ (sub_pos.mpr hab)).mp hlog
  rw [Real.log_div hC.ne' hk.ne'] at hgap
  refine ⟨T, by exact_mod_cast (show (2 : ℝ) ≤ T from hT2.le), ?_⟩
  apply (Real.log_lt_log_iff (mul_pos hC (Real.rpow_pos_of_pos hTp _))
    (mul_pos hk (Real.rpow_pos_of_pos hTp _))).mp
  rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hTp _).ne',
    Real.log_mul hk.ne' (Real.rpow_pos_of_pos hTp _).ne', Real.log_rpow hTp, Real.log_rpow hTp]
  nlinarith

/-- The literal three-dimensional family excludes every p>16/7, including
12/5, for every fixed positive constant in the weighted norm inequality. -/
theorem no_uniform_three_dimensional_fanNormBound {p C : ℝ} (hp : 16 / 7 < p) (hC : 0 < C) :
    ∃ T : ℕ, 2 ≤ T ∧ ¬FanNormBound (calibrationThreeReal T)
      (positiveDifferenceChannel (calibrationThreeReal T)) p C := by
  have hp0 : 0 < p := by linarith
  have hexp : 32 / p + 10 < 24 := by
    have h : 32 / p < 14 := (div_lt_iff₀ hp0).mpr (by linarith)
    linarith
  obtain ⟨T, hT, hgap⟩ := exists_natural_power_gap hexp
    (by norm_num : (0 : ℝ) < (2 / 3 : ℝ) ^ 5) (show 0 < 16 * C by positivity)
  have ht : 0 < T := by omega
  have hE := calibrationThreeReal_energy_lower ht
  have hP := calibrationThree_counting_power_bound ht hp0
  refine ⟨T, hT, ?_⟩
  intro h
  have hN := h (fun _ ↦ 1) (fun _ ↦ 1) (fun _ ↦ by norm_num) (fun _ ↦ by norm_num)
  rw [weightedGibbsPartition_one] at hN
  have hm := mul_le_mul_of_nonneg_left hP hC.le
  norm_num only [Real.rpow_ofNat] at hgap
  nlinarith

theorem no_uniform_three_dimensional_twelve_fifths (C : ℝ) (hC : 0 < C) :
    ∃ T : ℕ, 2 ≤ T ∧ ¬FanNormBound (calibrationThreeReal T)
      (positiveDifferenceChannel (calibrationThreeReal T)) (12 / 5) C :=
  no_uniform_three_dimensional_fanNormBound (by norm_num) hC

end
end Erdos539Geometry
