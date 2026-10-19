/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13WeightedObstruction

namespace Erdos539Geometry
noncomputable section
open scoped Classical

/-- An explicit scaled-log estimate handles the exact size 13T^7. -/
theorem pg13_exists_loglog_gap {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C) (R D : ℝ) :
    ∃ T : ℕ, 2 ≤ T ∧ R + C * (13 + Real.log (1 + Real.log ((pg13Union T).card : ℝ))) <
      ε * Real.log (T : ℝ) - D := by
  let η : ℝ := ε / (28 * (C + 1))
  let K : ℝ := C * (η * (1 + Real.log 13) - 1 - Real.log η)
  have hη : 0 < η := div_pos hε (by positivity)
  have hηid : η * (28 * (C + 1)) = ε := by
    exact div_mul_cancel₀ ε (by positivity)
  have hcoef : 7 * C * η ≤ ε / 4 := by nlinarith
  obtain ⟨T, hT⟩ := exists_nat_gt (max 2 (Real.exp (2 * (R + D + 13 * C + K) / ε)))
  have ht2 : (2 : ℝ) < T := (le_max_left _ _).trans_lt hT
  have ht : 2 ≤ T := by exact_mod_cast ht2.le
  have hp : 0 < T := by omega
  have htp : (0 : ℝ) < T := by exact_mod_cast hp
  have hx : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg (by linarith)
  have h13 : 0 ≤ Real.log (13 : ℝ) := Real.log_nonneg (by norm_num)
  have hu : 0 < 1 + Real.log 13 + 7 * Real.log (T : ℝ) := by linarith
  have hscaled := Real.log_le_sub_one_of_pos (mul_pos hη hu)
  rw [Real.log_mul hη.ne' hu.ne'] at hscaled
  have hlogbound : C * Real.log (1 + Real.log 13 + 7 * Real.log (T : ℝ)) ≤
      (ε / 4) * Real.log (T : ℝ) + K := by
    calc
      _ ≤ C * (η * (1 + Real.log 13 + 7 * Real.log (T : ℝ)) - 1 - Real.log η) :=
        mul_le_mul_of_nonneg_left (by linarith) hC
      _ = (7 * C * η) * Real.log (T : ℝ) + K := by dsimp only [K]; ring
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right hcoef hx) le_rfl
  have hlog := Real.log_lt_log (Real.exp_pos _) ((le_max_right _ _).trans_lt hT)
  rw [Real.log_exp] at hlog
  have hh := (div_lt_iff₀ hε).mp hlog
  have hsize : Real.log ((pg13Union T).card : ℝ) = Real.log 13 + 7 * Real.log (T : ℝ) := by
    rw [pg13Union_card hp]
    push_cast
    rw [Real.log_mul (by norm_num) (pow_pos htp 7).ne', Real.log_pow]
    norm_num
  refine ⟨T, ht, ?_⟩
  rw [hsize]
  have he : 1 + (Real.log 13 + 7 * Real.log (T : ℝ)) = 1 + Real.log 13 + 7 * Real.log (T : ℝ) := by ring
  rw [he]
  nlinarith [mul_nonneg hε.le hx]

/-- Even a fixed log-log size allowance cannot repair the unretained
maximum-projection-entropy bound in thirteen coordinates. -/
theorem pg13_unretained_loglog_failure {C : ℝ} (hC : 0 ≤ C) (R : ℝ) :
    ∃ T : ℕ, 2 ≤ T ∧ ∀ I : Finset (Fin 13),
      R + C * (13 + Real.log (1 + Real.log ((pg13Union T).card : ℝ))) <
        max (pg13ProjectionEntropy T I) (pg13ProjectionEntropy T Iᶜ) -
          Real.log (maxFan (integerRealSet (pg13Union T)) : ℝ) := by
  obtain ⟨T, hT, hg⟩ := pg13_exists_loglog_gap (by norm_num : (0 : ℝ) < 4 / 13) hC R (Real.log 11)
  exact ⟨T, hT, fun I ↦ hg.trans_le (pg13_unretained_entropy_gap hT I)⟩

/-- The energy-adjusted, dimension-weighted obstruction also survives
any fixed log-log size allowance. -/
theorem pg13_weighted_profile_loglog_failure {C : ℝ} (hC : 0 ≤ C) (R : ℝ) :
    ∃ T : ℕ, 2 ≤ T ∧ ∀ I : Finset (Fin 13), I.Nonempty → Iᶜ.Nonempty →
      let a : ℝ := stationaryCutExponent I.card
      let b : ℝ := stationaryCutExponent Iᶜ.card
      R + C * (13 + Real.log (1 + Real.log ((pg13Union T).card : ℝ))) <
        a * pg13ProjectionProfile T Iᶜ + b * pg13ProjectionProfile T I -
          (a + b) * pg13FanCapacity T := by
  obtain ⟨T, hT, hg⟩ := pg13_exists_loglog_gap
    (by norm_num [pg13GapCoefficient] : 0 < pg13GapCoefficient) hC R
    ((4 / 3 : ℝ) * (pg13DefectConstant + Real.log 11))
  refine ⟨T, hT, ?_⟩
  intro I hI hJ
  dsimp only
  have hsum : (stationaryCutExponent I.card : ℝ) + (stationaryCutExponent Iᶜ.card : ℝ) ≤ 4 / 3 := by
    have ha := (pg13_coefficient_bounds I).2
    have hb := (pg13_coefficient_bounds Iᶜ).2
    linarith
  have hc := mul_le_mul_of_nonneg_right hsum
    (add_nonneg pg13DefectConstant_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 11)))
  exact hg.trans_le ((sub_le_sub_left hc _).trans (pg13_weighted_profile_gap hT I hI hJ))

/-- Arbitrary fixed defect penalties and logarithmic dimension/size
allowances fail simultaneously on the same actual integer family. -/
theorem pg13_weighted_penalty_loglog_failure {A C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (R : ℝ) :
    ∃ T : ℕ, 2 ≤ T ∧ ∀ I : Finset (Fin 13), I.Nonempty → Iᶜ.Nonempty →
      let a : ℝ := stationaryCutExponent I.card
      let b : ℝ := stationaryCutExponent Iᶜ.card
      R + C * (13 + Real.log (1 + Real.log ((pg13Union T).card : ℝ))) <
        a * pg13ProjectionEntropy T Iᶜ + b * pg13ProjectionEntropy T I -
          (a + b) * pg13FanCapacity T - A * (pg13ProjectionDefect T I + pg13ProjectionDefect T Iᶜ) := by
  obtain ⟨T, hT, hg⟩ := pg13_exists_loglog_gap
    (by norm_num [pg13GapCoefficient] : 0 < pg13GapCoefficient) hC R
    ((4 / 3 : ℝ) * Real.log 11 + 2 * A * pg13DefectConstant)
  refine ⟨T, hT, ?_⟩
  intro I hI hJ
  dsimp only
  have hsum : (stationaryCutExponent I.card : ℝ) + (stationaryCutExponent Iᶜ.card : ℝ) ≤ 4 / 3 := by
    have ha := (pg13_coefficient_bounds I).2
    have hb := (pg13_coefficient_bounds Iᶜ).2
    linarith
  have hc := mul_le_mul_of_nonneg_right hsum (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 11))
  have h := pg13_weighted_entropy_penalty hT I hI hJ hA
  dsimp only at h
  have hh : pg13GapCoefficient * Real.log (T : ℝ) -
      ((4 / 3 : ℝ) * Real.log 11 + 2 * A * pg13DefectConstant) ≤
      pg13GapCoefficient * Real.log (T : ℝ) -
        ((stationaryCutExponent I.card : ℝ) + (stationaryCutExponent Iᶜ.card : ℝ)) * Real.log 11 -
          2 * A * pg13DefectConstant := by linarith
  exact hg.trans_le (hh.trans h)

end
end Erdos539Geometry
