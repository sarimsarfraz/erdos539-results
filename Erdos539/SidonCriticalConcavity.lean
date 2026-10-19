/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ConcaveDerivativeEndpoint
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Ring

namespace Erdos539Geometry
noncomputable section

/-- Critical-point function for the two-weight Sidon ratio. -/
def sidonCritical (p x : ℝ) : ℝ := x ^ (p - 1) + 2 * x ^ ((p - 2) / 2) - 2 * x ^ (p / 2)

def sidonCriticalDeriv (p x : ℝ) : ℝ :=
  (p - 1) * x ^ (p - 2) + (p - 2) * x ^ ((p - 4) / 2) - p * x ^ ((p - 2) / 2)

def sidonCriticalDeriv2 (p x : ℝ) : ℝ :=
  ((p - 2) / 2) * x ^ ((p - 6) / 2) * ((2 * p - 2) * x ^ (p / 2) + p - 4 - p * x)

theorem hasDerivAt_sidonCritical (p : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (sidonCritical p) (sidonCriticalDeriv p x) x := by
  have h1 := Real.hasDerivAt_rpow_const (p := p - 1) (Or.inl hx.ne')
  have h2 := (Real.hasDerivAt_rpow_const (p := (p - 2) / 2) (Or.inl hx.ne')).const_mul 2
  have h3 := (Real.hasDerivAt_rpow_const (p := p / 2) (Or.inl hx.ne')).const_mul 2
  convert (h1.add h2).sub h3 using 1
  dsimp [sidonCritical, sidonCriticalDeriv]
  congr 1 <;> ring_nf

theorem hasDerivAt_sidonCriticalDeriv (p : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (sidonCriticalDeriv p) (sidonCriticalDeriv2 p x) x := by
  have h1 := (Real.hasDerivAt_rpow_const (p := p - 2) (Or.inl hx.ne')).const_mul (p - 1)
  have h2 := (Real.hasDerivAt_rpow_const (p := (p - 4) / 2) (Or.inl hx.ne')).const_mul (p - 2)
  have h3 := (Real.hasDerivAt_rpow_const (p := (p - 2) / 2) (Or.inl hx.ne')).const_mul p
  convert (h1.add h2).sub h3 using 1
  have he1 : x ^ (p - 2 - 1) = x ^ ((p - 6) / 2) * x ^ (p / 2) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have he2 : x ^ ((p - 2) / 2 - 1) = x ^ ((p - 6) / 2) * x := by
    conv_rhs => arg 2; rw [← Real.rpow_one x]
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have he3 : (p - 4) / 2 - 1 = (p - 6) / 2 := by ring
  rw [he1, he2, he3]
  unfold sidonCriticalDeriv2
  ring

/-- Concavity is proved uniformly for 2 <= p <= 3. The estimate uses
x^(p/2) <= x and the remaining bound 2p-6 <= 0. -/
theorem sidonCritical_concave {p : ℝ} (hp2 : 2 ≤ p) (hp3 : p ≤ 3) :
    ConcaveOn ℝ (Set.Icc 0 1) (sidonCritical p) := by
  apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1)
    (f' := sidonCriticalDeriv p) (f'' := sidonCriticalDeriv2 p)
  · exact (((Real.continuous_rpow_const (by linarith : 0 ≤ p - 1)).add
      ((Real.continuous_rpow_const (by linarith : 0 ≤ (p - 2) / 2)).const_mul 2)).sub
        ((Real.continuous_rpow_const (by linarith : 0 ≤ p / 2)).const_mul 2)).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_sidonCritical p hx.1).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_sidonCriticalDeriv p hx.1).hasDerivWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    have hpow := Real.rpow_le_self_of_le_one hx.1.le hx.2.le (show 1 ≤ p / 2 by linarith)
    have hm := mul_le_mul_of_nonneg_left hpow (show 0 ≤ 2 * p - 2 by linarith)
    have hb := mul_le_mul_of_nonneg_left hx.2.le (show 0 ≤ p - 2 by linarith)
    have hi : (2 * p - 2) * x ^ (p / 2) + p - 4 - p * x ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith)
      (Real.rpow_nonneg hx.1.le _)) hi

end
end Erdos539Geometry
