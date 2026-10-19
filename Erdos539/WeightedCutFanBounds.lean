/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.WeightedCutInduction

namespace Erdos539Geometry
noncomputable section
open scoped Classical

/-- Exact power form of the conditional sharp weighted fan bound. -/
theorem WeightedProjectionBalanceHypothesis.fan_bound {B : ℝ}
    (hcut : WeightedProjectionBalanceHypothesis B) (hB : 0 ≤ B)
    {ι : Type} [Fintype ι] (hd : 0 < Fintype.card ι)
    {S : Finset (ι → ℝ)} (hS : S.Nonempty) :
    Real.exp (-(B + Real.log 16) * Fintype.card ι) *
      energyNorm S ^ (sharpExponent (Fintype.card ι) : ℝ) ≤ (maxFan S : ℝ) := by
  have hn := energyNorm_pos hS
  have hm : (0 : ℝ) < maxFan S := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_maxFan hS))
  apply (Real.log_le_log_iff (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hn _)) hm).mp
  rw [Real.log_mul (Real.exp_ne_zero _) (Real.rpow_pos_of_pos hn _).ne',
    Real.log_exp, Real.log_rpow hn]
  have h := hcut.log_fan_bound hB (Fintype.card ι) hd ι rfl S hS
  simp only [energyNorm_eq_classical] at h ⊢
  linarith

end
end Erdos539Geometry
