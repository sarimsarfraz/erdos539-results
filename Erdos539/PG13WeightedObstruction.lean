/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13WeightedGap

namespace Erdos539Geometry
noncomputable section
open scoped Classical

theorem pg13_exists_log_gap (R C : ℝ) :
    ∃ T : ℕ, 2 ≤ T ∧ R < pg13GapCoefficient * Real.log (T : ℝ) - C := by
  have hε : 0 < pg13GapCoefficient := by norm_num [pg13GapCoefficient]
  obtain ⟨T, hT⟩ := exists_nat_gt (max 2 (Real.exp ((R + C) / pg13GapCoefficient)))
  have ht : (2 : ℝ) < T := (le_max_left _ _).trans_lt hT
  have hlog := Real.log_lt_log (Real.exp_pos _) ((le_max_right _ _).trans_lt hT)
  rw [Real.log_exp] at hlog
  have hh := (div_lt_iff₀ hε).mp hlog
  exact ⟨T, by exact_mod_cast ht.le, by nlinarith⟩

/-- Every nonempty proper cut fails by an arbitrarily large amount on
one common member of the explicit integer family, despite bounded defects. -/
theorem pg13_weighted_profile_unbounded (R : ℝ) :
    ∃ T : ℕ, 2 ≤ T ∧ ∀ I : Finset (Fin 13), I.Nonempty → Iᶜ.Nonempty →
      let a : ℝ := stationaryCutExponent I.card
      let b : ℝ := stationaryCutExponent Iᶜ.card
      R < a * pg13ProjectionProfile T Iᶜ + b * pg13ProjectionProfile T I -
        (a + b) * pg13FanCapacity T := by
  obtain ⟨T, hT, hg⟩ := pg13_exists_log_gap R ((4 / 3 : ℝ) * (pg13DefectConstant + Real.log 11))
  refine ⟨T, hT, ?_⟩
  intro I hI hJ
  dsimp only
  have hsum : (stationaryCutExponent I.card : ℝ) + (stationaryCutExponent Iᶜ.card : ℝ) ≤ 4 / 3 := by
    have ha := (pg13_coefficient_bounds I).2
    have hb := (pg13_coefficient_bounds Iᶜ).2
    linarith
  have hc := mul_le_mul_of_nonneg_right hsum
    (add_nonneg pg13DefectConstant_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 11)))
  have h := pg13_weighted_profile_gap hT I hI hJ
  dsimp only at h
  exact hg.trans_le ((sub_le_sub_left hc _).trans h)

/-- The same family defeats every fixed coefficient on the sum of the
projected stationary defects, as well as every fixed additive allowance. -/
theorem pg13_weighted_penalty_unbounded {A : ℝ} (hA : 0 ≤ A) (R : ℝ) :
    ∃ T : ℕ, 2 ≤ T ∧ ∀ I : Finset (Fin 13), I.Nonempty → Iᶜ.Nonempty →
      let a : ℝ := stationaryCutExponent I.card
      let b : ℝ := stationaryCutExponent Iᶜ.card
      R < a * pg13ProjectionEntropy T Iᶜ + b * pg13ProjectionEntropy T I -
        (a + b) * pg13FanCapacity T - A * (pg13ProjectionDefect T I + pg13ProjectionDefect T Iᶜ) := by
  obtain ⟨T, hT, hg⟩ := pg13_exists_log_gap R ((4 / 3 : ℝ) * Real.log 11 + 2 * A * pg13DefectConstant)
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
