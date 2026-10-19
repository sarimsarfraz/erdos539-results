/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.RootPotential

namespace Erdos539Geometry
noncomputable section

/-- Invert an actual critical palette comparison, with every positivity
hypothesis explicit. -/
theorem critical_norm_upper_of_palette {α q lam qA lamA t : ℝ}
    (hα : 0 < α) (hq : 0 < q) (hlam : 0 < lam) (hqA : 0 < qA) (hlamA : 0 < lamA)
    (ht : 0 < t) (hpalette : qA ≤ t)
    (hcritical : Real.log q - α * Real.log lam ≤ Real.log qA - α * Real.log lamA) :
    lamA ≤ lam * (t / q) ^ (1 / α) := by
  have hlog := Real.log_le_log hqA hpalette
  apply (Real.log_le_log_iff hlamA (mul_pos hlam (Real.rpow_pos_of_pos (div_pos ht hq) _))).mp
  rw [Real.log_mul hlam.ne' (Real.rpow_pos_of_pos (div_pos ht hq) _).ne',
    Real.log_rpow (div_pos ht hq)]
  have hinv : α * (1 / α) = 1 := by field_simp
  have hm : α * Real.log lamA ≤ α * (Real.log lam + (1 / α) * Real.log (t / q)) := by
    rw [mul_add, ← mul_assoc, hinv, one_mul, Real.log_div ht.ne' hq.ne']
    linarith
  nlinarith only [hm, hα]

end
end Erdos539Geometry
