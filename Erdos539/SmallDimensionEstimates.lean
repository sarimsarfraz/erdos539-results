/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SharpExponentValues
import Erdos539.ThreeDimensionalFans

namespace Erdos539Geometry

/-- The scalar induction step for constant-factor small-dimensional bounds. -/
theorem small_dimension_split_closes {d a b u N E P Q M L : ℝ}
    (hd : 1 ≤ d) (ha : 0 ≤ a) (hb : 0 ≤ b) (hN : 0 ≤ N) (hL : 0 ≤ L)
    (hu : u ≤ (a + b) / (1 + a + b))
    (hsize : N ≤ d * L + E) (hP : P ≤ M) (hQ : Q ≤ M)
    (hprune : a * (E - 2 * L - Q) + b * (E - L - P) - 3 * d * L ≤ M) :
    u * N - 3 * d * L ≤ M := by
  have hden : 0 < 1 + a + b := by linarith
  have hu' := (le_div_iff₀ hden).mp hu
  have hNu := mul_le_mul_of_nonneg_right hu' hN
  have hPa := mul_le_mul_of_nonneg_left hQ ha
  have hPb := mul_le_mul_of_nonneg_left hP hb
  have hsize' := mul_le_mul_of_nonneg_left hsize (show 0 ≤ a + b by linarith)
  have hconstant : d * (a + b) + 2 * a + b + 3 * d ≤ 3 * d * (1 + a + b) := by
    have hda := mul_nonneg (show 0 ≤ d - 1 by linarith) ha
    have hdb := mul_nonneg (show 0 ≤ d - 1 by linarith) hb
    nlinarith
  have hconstant' := mul_le_mul_of_nonneg_right hconstant hL
  apply (mul_le_mul_iff_right₀ hden).mp
  nlinarith

/-- The three one-sided base dimensions, expressed with a common 8^(-d) loss. -/
theorem one_sided_small_log_bound {ι : Type*} [Fintype ι]
    (hd0 : 0 < Fintype.card ι) (hd3 : Fintype.card ι ≤ 3)
    {F : Finset (ι → ℝ)} (hF : F.Nonempty) :
    (sharpExponent (Fintype.card ι) : ℝ) * Real.log F.card -
      3 * (Fintype.card ι : ℝ) * Real.log 2 ≤ Real.log (maxFan F) := by
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rcases (show Fintype.card ι = 1 ∨ Fintype.card ι = 2 ∨ Fintype.card ι = 3 by omega) with hd | hd | hd
  · rw [hd, sharpExponent_one, one_dimensional_maxFan_eq_card hd]
    norm_num
    positivity
  · have h := planar_log_fan_bound hd hF
    rw [hd, sharpExponent_2]
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat]
    linarith
  · have h := three_dimensional_log_fan_bound hd hF
    rw [hd, sharpExponent_3]
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat]
    linarith

end Erdos539Geometry
