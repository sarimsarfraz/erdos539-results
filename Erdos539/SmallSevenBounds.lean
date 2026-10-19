/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SmallTwoSided
import Erdos539.SharpUpper

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical

/-- Power form of the uniform logarithmic loss used in the small-dimensional induction. -/
theorem power_bound_of_small_log_bound {n q d : ℕ} (hn : 0 < n) (hq : 0 < q) (e : ℝ)
    (h : e * Real.log n - 3 * (d : ℝ) * Real.log 2 ≤ Real.log q) :
    (n : ℝ) ^ e / (8 : ℝ) ^ d ≤ q := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hpow : 0 < (n : ℝ) ^ e := Real.rpow_pos_of_pos hn' e
  have hden : (0 : ℝ) < (8 : ℝ) ^ d := by positivity
  apply (Real.log_le_log_iff (div_pos hpow hden) hq').mp
  rw [Real.log_div hpow.ne' hden.ne', Real.log_rpow hn', Real.log_pow]
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    have hh := Real.log_pow (2 : ℝ) 3
    norm_num at hh
    exact hh
  rw [h8]
  nlinarith

theorem small_seven_posDiff_lower_bound {ι : Type*} [Fintype ι]
    (hd0 : 0 < Fintype.card ι) (hd7 : Fintype.card ι ≤ 7)
    {F : Finset (ι → ℝ)} (hF : F.Nonempty) :
    (F.card : ℝ) ^ (sharpExponent (Fintype.card ι) : ℝ) / (8 : ℝ) ^ Fintype.card ι ≤ (posDiff F).card := by
  have hlog := small_two_sided_log_bound (Fintype.card ι) ι rfl hd0 hd7 F hF
  have hpos : 0 < maxTwoFan F :=
    lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxTwoRestrictedFan hF ∅)
  exact (power_bound_of_small_log_bound hF.card_pos hpos _ hlog).trans
    (by exact_mod_cast maxTwoFan_le_card_posDiff F)

theorem integer_small_seven_lower_bound {d : ℕ} (hd0 : 0 < d) (hd7 : d ≤ 7)
    {F : Finset (Fin d → ℤ)} (hF : F.Nonempty) :
    (F.card : ℝ) ^ (sharpExponent d : ℝ) / (8 : ℝ) ^ d ≤ (integerPositiveDifferences F).card := by
  letI : DecidableEq (Fin d → ℝ) := Classical.decEq _
  have h := small_seven_posDiff_lower_bound (by simpa using hd0) (by simpa using hd7)
    (hF.image integerToReal)
  rw [integerToReal_image_card, posDiff_integerToReal_card] at h
  simpa only [Fintype.card_fin] using h

/-- Matching sharp bounds for every dimension from one through seven. -/
theorem fixedDimensionalMinimum_small_seven_bounds {d : ℕ} (hd0 : 0 < d) (hd7 : d ≤ 7) :
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
    have h := integer_small_seven_lower_bound hd0 hd7 hFn
    rwa [hF, hq] at h
  · have hm : (fixedDimensionalMinimum d n : ℝ) ≤ (integerPositiveDifferences A).card := by
      exact_mod_cast fixedDimensionalMinimum_le A hA
    exact hm.trans hD

theorem fixedDimensionalMinimum_small_seven_isTheta {d : ℕ} (hd0 : 0 < d) (hd7 : d ≤ 7) :
    Asymptotics.IsTheta Filter.atTop
      (fun n : ℕ ↦ (fixedDimensionalMinimum d n : ℝ))
      (fun n : ℕ ↦ (n : ℝ) ^ (sharpExponent d : ℝ)) := by
  obtain ⟨C, _hC, hbounds⟩ := fixedDimensionalMinimum_small_seven_bounds hd0 hd7
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

theorem primeSupportedMinimum_small_seven_isTheta {d : ℕ} (hd0 : 0 < d) (hd7 : d ≤ 7)
    (p : Fin d ↪ ℕ) (hp : ∀ i, (p i).Prime) :
    Asymptotics.IsTheta Filter.atTop
      (fun n : ℕ ↦ (primeSupportedMinimum p n : ℝ))
      (fun n : ℕ ↦ (n : ℝ) ^ (sharpExponent d : ℝ)) := by
  simpa only [primeSupportedMinimum_eq_fixedDimensionalMinimum p hp] using
    fixedDimensionalMinimum_small_seven_isTheta hd0 hd7

end
end Erdos539Geometry
