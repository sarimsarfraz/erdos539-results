/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteGibbs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- The integral-test step, proved with log x <= x-1 and exp x >= 1+x,
so the finite rank estimate does not depend on a zeta-function library. -/
theorem rank_reference_step {s x : ℝ} (hs : 1 < s) (hx : 1 < x) :
    (s - 1) * x ^ (-s) ≤ (x - 1) ^ (1 - s) - x ^ (1 - s) := by
  have hx0 : 0 < x := by linarith
  have hxm : 0 < x - 1 := by linarith
  have hl := Real.log_le_sub_one_of_pos (div_pos hxm hx0)
  rw [Real.log_div hxm.ne' hx0.ne'] at hl
  have heq : (x - 1) / x - 1 = -(1 / x) := by field_simp; ring
  rw [heq] at hl
  have hm := mul_le_mul_of_nonpos_left hl (show 1 - s ≤ 0 by linarith)
  have he := Real.add_one_le_exp ((1 - s) * (Real.log (x - 1) - Real.log x))
  have hbound : 1 + (s - 1) / x ≤ Real.exp ((1 - s) * (Real.log (x - 1) - Real.log x)) := by
    simp only [div_eq_mul_inv] at hm ⊢
    nlinarith only [hm, he]
  have hp := mul_le_mul_of_nonneg_left hbound (Real.rpow_pos_of_pos hx0 (1 - s)).le
  have hid : x ^ (1 - s) * Real.exp ((1 - s) * (Real.log (x - 1) - Real.log x)) =
      (x - 1) ^ (1 - s) := by
    rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hxm, ← Real.exp_add]
    congr 1
    ring
  rw [hid] at hp
  have hr : x ^ (-s) = x ^ (1 - s) / x := by
    convert Real.rpow_sub_one hx0.ne' (1 - s) using 1
    congr 1
    ring
  rw [hr]
  simp only [div_eq_mul_inv] at hp ⊢
  nlinarith only [hp]

/-- Uniform finite p-series bound over positive ranks. -/
theorem finite_rank_reference_sum_le (N : ℕ) {s : ℝ} (hs : 1 < s) :
    (∑ k ∈ Finset.range N, ((k : ℝ) + 1) ^ (-s)) ≤ 1 + 1 / (s - 1) := by
  have hs0 : 0 < s - 1 := by linarith
  have htel : ∀ N : ℕ, 1 ≤ N →
      (s - 1) * (∑ k ∈ Finset.range N, ((k : ℝ) + 1) ^ (-s)) ≤
        s - (N : ℝ) ^ (1 - s) := by
    intro N
    induction N with
    | zero => omega
    | succ N ih =>
      intro hN
      by_cases hzero : N = 0
      · subst N
        simp
      · have hNpos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hzero
        have hb := ih hNpos
        have hx : 1 < (N : ℝ) + 1 := by exact_mod_cast (Nat.succ_lt_succ (Nat.pos_of_ne_zero hzero))
        have hstep := rank_reference_step hs hx
        simp only [add_sub_cancel_right] at hstep
        rw [Finset.sum_range_succ, Nat.cast_succ]
        nlinarith
  by_cases hN : N = 0
  · subst N
    simp only [Finset.range_zero, Finset.sum_empty]
    positivity
  · have ht := htel N (Nat.one_le_iff_ne_zero.mpr hN)
    have hpow := Real.rpow_nonneg (Nat.cast_nonneg N) (1 - s)
    have hid : (s - 1) * (1 + 1 / (s - 1)) = s := by field_simp; ring
    apply (mul_le_mul_iff_right₀ hs0).mp
    nlinarith

end
end Erdos539Geometry
