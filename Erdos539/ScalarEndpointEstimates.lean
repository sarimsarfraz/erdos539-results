/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FanPowerSum
import Erdos539.FiniteGeometricEntropy

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

/-- A finite positive geometric tail is bounded independently of its length. -/
theorem positive_geometric_sum_le {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    (∑ k ∈ Finset.range n, r ^ (k + 1)) ≤ r / (1 - r) := by
  have he := geom_sum_mul_neg r n
  have hn := pow_nonneg hr n
  have hs : (∑ k ∈ Finset.range n, r ^ (k + 1)) = r * ∑ k ∈ Finset.range n, r ^ k := by
    simp only [pow_succ, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hs]
  apply (le_div_iff₀ (by linarith : 0 < 1 - r)).mpr
  nlinarith

/-- The useful elementary global logarithm estimate. -/
theorem endpoint_log_le_sqrt {x : ℝ} (hx : 1 ≤ x) : Real.log x ≤ Real.sqrt x := by
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hlog := Real.log_nonneg hx
  have he := Real.add_one_le_exp (Real.log x / 4)
  have hexp : Real.exp (Real.log x / 4) ^ 2 = Real.exp (Real.log x / 2) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hroot : Real.exp (Real.log x / 2) = Real.sqrt x := by
    have hs : Real.exp (Real.log x / 2) ^ 2 = x := by
      rw [pow_two, ← Real.exp_add, show Real.log x / 2 + Real.log x / 2 = Real.log x by ring,
        Real.exp_log hxpos]
    have hsq := Real.sq_sqrt hxpos.le
    have hp := Real.exp_pos (Real.log x / 2)
    have hsr := Real.sqrt_nonneg x
    nlinarith
  have hlow : Real.log x ≤ Real.exp (Real.log x / 4) ^ 2 := by
    have hp := Real.exp_pos (Real.log x / 4)
    nlinarith [sq_nonneg (Real.log x - 4)]
  rwa [hexp, hroot] at hlow

/-- The scalar endpoint example's uniform ratio bound on its first half. -/
theorem endpoint_prefix_ratio_bound {N i : ℝ} (hN : 1 < N) (hi : i ≤ N / 2) :
    Real.exp (Real.log N * i / N) + 1 / (Real.exp (Real.log N / N) - 1) ≤
      2 * N / Real.log N := by
  have hNp : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos hN
  have ht : 0 < Real.log N / N := div_pos hL hNp
  have hE : Real.log N / N ≤ Real.exp (Real.log N / N) - 1 := by
    have h := Real.add_one_le_exp (Real.log N / N)
    linarith
  have hEp : 0 < Real.exp (Real.log N / N) - 1 := ht.trans_le hE
  have hrec : 1 / (Real.exp (Real.log N / N) - 1) ≤ N / Real.log N := by
    have h := one_div_le_one_div_of_le ht hE
    simpa only [one_div_div, one_mul] using h
  have hiexp : Real.exp (Real.log N * i / N) ≤ Real.sqrt N := by
    have harg : Real.log N * i / N ≤ Real.log N / 2 := by
      apply (div_le_iff₀ hNp).mpr
      nlinarith
    have h := Real.exp_le_exp.mpr harg
    have he : Real.exp (Real.log N / 2) = Real.sqrt N := by
      have hs : Real.exp (Real.log N / 2) ^ 2 = N := by
        rw [pow_two, ← Real.exp_add, show Real.log N / 2 + Real.log N / 2 = Real.log N by ring,
          Real.exp_log hNp]
      have hp := Real.exp_pos (Real.log N / 2)
      have hsr := Real.sqrt_nonneg N
      have hsq := Real.sq_sqrt hNp.le
      nlinarith
    rwa [he] at h
  have hsqrt : Real.sqrt N ≤ N / Real.log N := by
    apply (le_div_iff₀ hL).mpr
    have h := endpoint_log_le_sqrt hN.le
    have hs := Real.sq_sqrt hNp.le
    have hn := Real.sqrt_nonneg N
    nlinarith
  calc
    _ ≤ N / Real.log N + N / Real.log N := add_le_add (hiexp.trans hsqrt) hrec
    _ = _ := by ring

end
end Erdos539Geometry
