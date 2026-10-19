/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CornerFanBound
import Erdos539.SharpUpper

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical

theorem integer_all_dimension_lower_bound {d : ℕ} (hd0 : 0 < d)
    {F : Finset (Fin d → ℤ)} (hF : F.Nonempty) :
    (F.card : ℝ) ^ (sharpExponent d : ℝ) / (2 : ℝ) ^ (2 ^ (d + 1) : ℕ) ≤ (integerPositiveDifferences F).card := by
  letI : DecidableEq (Fin d → ℝ) := Classical.decEq _
  have h := all_dimension_posDiff_lower_bound (by simpa using hd0)
    (hF.image integerToReal)
  rw [integerToReal_image_card, posDiff_integerToReal_card] at h
  simpa only [Fintype.card_fin] using h

/-- Matching sharp bounds for every fixed positive dimension. -/
theorem fixedDimensionalMinimum_all_dimension_bounds {d : ℕ} (hd0 : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n →
      (n : ℝ) ^ (sharpExponent d : ℝ) / (2 : ℝ) ^ (2 ^ (d + 1) : ℕ) ≤ fixedDimensionalMinimum d n ∧
      (fixedDimensionalMinimum d n : ℝ) ≤ C * (n : ℝ) ^ (sharpExponent d : ℝ) := by
  obtain ⟨C, hC, hfamily⟩ := exists_sharp_upper_construction hd0
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨A, hA, hD⟩ := hfamily n hn
  constructor
  · obtain ⟨F, hF, hq⟩ := fixedDimensionalMinimum_attained ⟨A, hA⟩
    have hFn : F.Nonempty := Finset.card_pos.mp (by omega)
    have h := integer_all_dimension_lower_bound hd0 hFn
    rwa [hF, hq] at h
  · have hm : (fixedDimensionalMinimum d n : ℝ) ≤ (integerPositiveDifferences A).card := by
      exact_mod_cast fixedDimensionalMinimum_le A hA
    exact hm.trans hD

theorem fixedDimensionalMinimum_all_dimension_isTheta {d : ℕ} (hd0 : 0 < d) :
    Asymptotics.IsTheta Filter.atTop
      (fun n : ℕ ↦ (fixedDimensionalMinimum d n : ℝ))
      (fun n : ℕ ↦ (n : ℝ) ^ (sharpExponent d : ℝ)) := by
  obtain ⟨C, _hC, hbounds⟩ := fixedDimensionalMinimum_all_dimension_bounds hd0
  have he : ∀ᶠ n : ℕ in Filter.atTop, 0 < n := Filter.eventually_gt_atTop 0
  constructor
  · apply Asymptotics.IsBigO.of_bound C
    filter_upwards [he] with n hn
    have hp : 0 ≤ (n : ℝ) ^ (sharpExponent d : ℝ) := Real.rpow_nonneg (by positivity) _
    simpa only [Real.norm_eq_abs, abs_of_nonneg hp, Nat.abs_cast] using (hbounds n hn).2
  · apply Asymptotics.IsBigO.of_bound ((2 : ℝ) ^ (2 ^ (d + 1) : ℕ))
    filter_upwards [he] with n hn
    have hp : 0 ≤ (n : ℝ) ^ (sharpExponent d : ℝ) := Real.rpow_nonneg (by positivity) _
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ (2 ^ (d + 1) : ℕ))).mp (hbounds n hn).1
    simpa only [Real.norm_eq_abs, abs_of_nonneg hp, Nat.abs_cast, mul_comm] using h

theorem primeSupportedMinimum_all_dimension_isTheta {d : ℕ} (hd0 : 0 < d)
    (p : Fin d ↪ ℕ) (hp : ∀ i, (p i).Prime) :
    Asymptotics.IsTheta Filter.atTop
      (fun n : ℕ ↦ (primeSupportedMinimum p n : ℝ))
      (fun n : ℕ ↦ (n : ℝ) ^ (sharpExponent d : ℝ)) := by
  simpa only [primeSupportedMinimum_eq_fixedDimensionalMinimum p hp] using
    fixedDimensionalMinimum_all_dimension_isTheta hd0

end
end Erdos539Geometry
