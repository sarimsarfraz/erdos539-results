/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.RationalSidonCertificate

namespace Erdos539Geometry
noncomputable section

/-- Real-power form of the integer-certified two-variable inequality.
This is the rational exponent 13/5, not the sharper logarithmic exponent. -/
theorem rational_sidon_scalar {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ (13 / 5 : ℝ) + 4 * (a * b) ^ (13 / 10 : ℝ) + b ^ (13 / 5 : ℝ) ≤
      (a + b) ^ (13 / 5 : ℝ) := by
  have h := rational_sidon_polynomial (Real.rpow_nonneg ha (1 / 10)) (Real.rpow_nonneg hb (1 / 10))
  simp only [← Real.rpow_mul_natCast ha, ← Real.rpow_mul_natCast hb] at h
  norm_num at h
  rw [Real.mul_rpow ha hb]
  have he : ((a + b) ^ (13 / 5 : ℝ)) ^ 5 = (a + b) ^ 13 := by
    rw [← Real.rpow_mul_natCast (add_nonneg ha hb)]
    norm_num
  rw [← he] at h
  apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num : (5 : ℕ) ≠ 0)).mp
  simpa only [mul_assoc] using h

end
end Erdos539Geometry
