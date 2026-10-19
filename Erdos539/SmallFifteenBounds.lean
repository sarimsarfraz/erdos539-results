/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SmallSevenBounds
import Erdos539.SmallFifteen

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical

theorem small_fifteen_posDiff_lower_bound {ι : Type*} [Fintype ι]
    (hd0 : 0 < Fintype.card ι) (hd15 : Fintype.card ι ≤ 15)
    {F : Finset (ι → ℝ)} (hF : F.Nonempty) :
    (F.card : ℝ) ^ (sharpExponent (Fintype.card ι) : ℝ) / (8 : ℝ) ^ Fintype.card ι ≤ (posDiff F).card := by
  have hlog := small_fifteen_log_bound (Fintype.card ι) ι rfl hd0 hd15 F hF
  have hpos : 0 < (posDiff F).card :=
    lt_of_lt_of_le (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxFan hF)) (maxFan_le_card_posDiff F)
  exact power_bound_of_small_log_bound hF.card_pos hpos _ hlog

theorem integer_small_fifteen_lower_bound {d : ℕ} (hd0 : 0 < d) (hd15 : d ≤ 15)
    {F : Finset (Fin d → ℤ)} (hF : F.Nonempty) :
    (F.card : ℝ) ^ (sharpExponent d : ℝ) / (8 : ℝ) ^ d ≤ (integerPositiveDifferences F).card := by
  letI : DecidableEq (Fin d → ℝ) := Classical.decEq _
  have h := small_fifteen_posDiff_lower_bound (by simpa using hd0) (by simpa using hd15)
    (hF.image integerToReal)
  rw [integerToReal_image_card, posDiff_integerToReal_card] at h
  simpa only [Fintype.card_fin] using h

/-- Matching sharp bounds for every dimension from one through fifteen. -/
theorem fixedDimensionalMinimum_small_fifteen_bounds {d : ℕ} (hd0 : 0 < d) (hd15 : d ≤ 15) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (n : ℝ) ^ (sharpExponent d : ℝ) / (8 : ℝ) ^ d ≤ fixedDimensionalMinimum d n ∧
      (fixedDimensionalMinimum d n : ℝ) ≤ C * (n : ℝ) ^ (sharpExponent d : ℝ) := by
  obtain ⟨C, hC, hfamily⟩ := exists_sharp_upper_construction hd0
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨A, hA, hD⟩ := hfamily n hn
  constructor
  · obtain ⟨F, hF, hq⟩ := fixedDimensionalMinimum_attained ⟨A, hA⟩
    have hFn : F.Nonempty := Finset.card_pos.mp (by omega)
    have h := integer_small_fifteen_lower_bound hd0 hd15 hFn
    rwa [hF, hq] at h
  · have hm : (fixedDimensionalMinimum d n : ℝ) ≤ (integerPositiveDifferences A).card := by
      exact_mod_cast fixedDimensionalMinimum_le A hA
    exact hm.trans hD

theorem fixedDimensionalMinimum_small_fifteen_isTheta {d : ℕ} (hd0 : 0 < d) (hd15 : d ≤ 15) :
    Asymptotics.IsTheta Filter.atTop
      (fun n : ℕ ↦ (fixedDimensionalMinimum d n : ℝ))
      (fun n : ℕ ↦ (n : ℝ) ^ (sharpExponent d : ℝ)) := by
  obtain ⟨C, _hC, hbounds⟩ := fixedDimensionalMinimum_small_fifteen_bounds hd0 hd15
  have he : ∀ᶠ n : ℕ in Filter.atTop, 0 < n := Filter.eventually_gt_atTop 0
  constructor
  · apply Asymptotics.IsBigO.of_bound C
    filter_upwards [he] with n hn
    have hp : 0 ≤ (n : ℝ) ^ (sharpExponent d : ℝ) := Real.rpow_nonneg (by positivity) _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hp, Nat.abs_cast] using (hbounds n hn).2
  · apply Asymptotics.IsBigO.of_bound ((8 : ℝ) ^ d)
    filter_upwards [he] with n hn
    have hp : 0 ≤ (n : ℝ) ^ (sharpExponent d : ℝ) := Real.rpow_nonneg (by positivity) _
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < (8 : ℝ) ^ d)).mp (hbounds n hn).1
    simpa only [Real.norm_eq_abs, abs_of_nonneg hp, Nat.abs_cast, mul_comm] using h

theorem primeSupportedMinimum_small_fifteen_isTheta {d : ℕ} (hd0 : 0 < d) (hd15 : d ≤ 15)
    (p : Fin d ↪ ℕ) (hp : ∀ i, (p i).Prime) :
    Asymptotics.IsTheta Filter.atTop
      (fun n : ℕ ↦ (primeSupportedMinimum p n : ℝ))
      (fun n : ℕ ↦ (n : ℝ) ^ (sharpExponent d : ℝ)) := by
  simpa only [primeSupportedMinimum_eq_fixedDimensionalMinimum p hp] using
    fixedDimensionalMinimum_small_fifteen_isTheta hd0 hd15

end
end Erdos539Geometry
