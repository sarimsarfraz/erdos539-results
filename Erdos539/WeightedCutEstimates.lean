/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.RootPotential

namespace Erdos539Geometry
noncomputable section

/-- The scalar induction step for the sufficient weighted-cut hypothesis.
L and M are logarithmic norm and maximum fan, while LI and LJ are the
actual marginal logarithmic energies of the same maximizing weight. -/
theorem weighted_cut_induction_scalar {B A d p s u a b L M LI LJ : ℝ}
    (hA : A = B + Real.log 16) (hd : 1 ≤ d) (hps : p + s = d)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hL : 0 ≤ L)
    (hrec : u ≤ (a + b) / (1 + a + b))
    (hI : LI ≤ B * d + M) (hJ : LJ ≤ B * d + M)
    (hprune : -A * p - A * s + a * (L - Real.log 16 - LJ) +
      b * (L - Real.log 16 - LI) ≤ M) :
    u * L - A * d ≤ M := by
  have hlog : 0 ≤ Real.log (16 : ℝ) := Real.log_nonneg (by norm_num)
  have hcost : B * d + Real.log 16 ≤ A * d := by
    rw [hA]
    nlinarith
  have hmulI := mul_le_mul_of_nonneg_left hI hb
  have hmulJ := mul_le_mul_of_nonneg_left hJ ha
  have hcostmul := mul_le_mul_of_nonneg_left hcost (add_nonneg ha hb)
  have hden : 0 < 1 + a + b := by linarith
  have hrec' := (le_div_iff₀ hden).mp hrec
  have hrecL := mul_le_mul_of_nonneg_right hrec' hL
  have hAp : A * p + A * s = A * d := by rw [← mul_add, hps]
  have hmain : (1 + a + b) * (u * L - A * d) ≤ (1 + a + b) * M := by
    nlinarith
  exact (mul_le_mul_iff_right₀ hden).mp hmain

/-- The empty-block alternative is stronger than the desired exponent
bound, provided that the exponent is at most one. -/
theorem weighted_cut_terminal_scalar {B A d u L M : ℝ}
    (hAB : B ≤ A) (hd : 0 ≤ d) (hu : u ≤ 1) (hL : 0 ≤ L)
    (hterminal : L ≤ B * d + M) : u * L - A * d ≤ M := by
  have hmul := mul_le_mul_of_nonneg_right hAB hd
  have huL := mul_le_mul_of_nonneg_right hu hL
  nlinarith

end
end Erdos539Geometry
