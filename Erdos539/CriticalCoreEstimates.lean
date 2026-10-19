/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.RootPotential

namespace Erdos539Geometry
noncomputable section

/-- Algebra after comparing a critical core with its parent. The variables
are logarithms: X=log N, T=log K0, L0=log Lambda(parent), Q0=log q0,
L=log Lambda(core), Q=log q(core). Norm facts and actual selection are
explicit premises, not new axioms. -/
theorem critical_core_log_retention {b X T L0 Q0 L Q : ℝ} (hb : 0 < b)
    (hparent : 2 * Q0 = X + T) (hnorm : X - T ≤ L0) (hsize : L ≤ 2 * Q)
    (hmin : 2 * b * Q - (b + 1) * L ≤ 2 * b * Q0 - (b + 1) * L0) :
    X - (2 * b + 1) * T ≤ L := by
  have hm := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ b + 1 by linarith)
  have hs := mul_le_mul_of_nonneg_left hsize hb.le
  nlinarith

theorem critical_core_log_surplus {b X T L0 Q0 L Q : ℝ} (hb : 0 < b)
    (hparent : 2 * Q0 = X + T) (hnorm : X - T ≤ L0) (hcard : L ≤ X)
    (hmin : 2 * b * Q - (b + 1) * L ≤ 2 * b * Q0 - (b + 1) * L0) :
    2 * Q - L ≤ (2 + 1 / b) * T := by
  have hm := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ b + 1 by linarith)
  have hmain : b * (2 * Q - L) ≤ (2 * b + 1) * T := by nlinarith
  have he : (2 + 1 / b) * T = ((2 * b + 1) * T) / b := by field_simp
  rw [he]
  exact (le_div_iff₀ hb).mpr (by nlinarith)

/-- Comparing with a singleton bounds the root's palette surplus. -/
theorem critical_core_singleton_log_bound {b L Q : ℝ} (hb : 0 < b)
    (hmin : 2 * b * Q - (b + 1) * L ≤ 0) :
    2 * Q ≤ (1 + 1 / b) * L := by
  have he : (1 + 1 / b) * L = ((b + 1) * L) / b := by field_simp
  rw [he]
  exact (le_div_iff₀ hb).mpr (by nlinarith)

/-- Projection criticality prohibits norm inflation when the projected
palette does not increase. -/
theorem critical_core_no_log_norm_inflation {b L Q LA QA : ℝ} (hb : 0 < b)
    (hpalette : QA ≤ Q)
    (hmin : 2 * b * Q - (b + 1) * L ≤ 2 * b * QA - (b + 1) * LA) :
    LA ≤ L := by
  have h := mul_le_mul_of_nonneg_left hpalette (show 0 ≤ 2 * b by positivity)
  nlinarith

/-- The sufficient quadratic estimate after elementary extraction. This is
only the scalar implication; an actual critical-core norm bound remains a
hypothesis to be connected through the weighted-energy formalization. -/
theorem quadratic_core_scalar_growth {X T B L C : ℝ} {D : ℕ}
    (hT : 1 / 2 ≤ T) (hC : 0 ≤ C) (hD : (D : ℝ) ≤ 100 * T)
    (hB : X - 17 * T ≤ B)
    (hretain : B - (8 * (D : ℝ) + 1) * (18 * T) ≤ L)
    (hcore : L ≤ C * (D : ℝ) ^ 2) :
    X ≤ (10000 * C + 14470) * T ^ 2 := by
  have hT0 : 0 ≤ T := by linarith
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hDsq : (D : ℝ) ^ 2 ≤ 10000 * T ^ 2 := by nlinarith
  have hCbound := mul_le_mul_of_nonneg_left hDsq hC
  have hlinear : 35 * T ≤ 70 * T ^ 2 := by nlinarith
  have hcross := mul_le_mul_of_nonneg_right hD hT0
  nlinarith

end
end Erdos539Geometry
