/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ScalarStationaryTradeoff

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- Explicit constant in the linear scalar stationary estimate. -/
def scalarStationaryConstant : ℝ := 1 + (2 / 3 : ℝ) * Real.log 24

theorem scalar_stationary_log_bound {α β : Type*}
    [Fintype α] [LinearOrder α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1)
    (channel : α → α → β) (hinj : UpperConeInjective channel) :
    finiteEntropy ν - 2 * Real.log (finiteEntropy ν + 2) - 3 ≤ stationaryCapacity ν channel := by
  let H := finiteEntropy ν
  let F := stationaryCapacity ν channel
  have hH : 0 ≤ H := finiteEntropy_nonneg ν hν hs
  obtain ⟨hF, hFH⟩ := stationaryCapacity_bounds ν hν hs channel
  change 0 ≤ F at hF
  change F ≤ H at hFH
  have hH1 : 0 < H + 1 := by linarith
  let s := 1 + 1 / (H + 1)
  have hs1 : 1 < s := by dsimp [s]; have := one_div_pos.mpr hH1; linarith
  have ht := scalar_stationary_entropy_tradeoff ν hν hs channel hinj hs1
  change H ≤ Real.log (F + 1) + 1 + s * (F + 1) + Real.log (1 + 1 / (s - 1)) at ht
  have hC : 1 + 1 / (s - 1) = H + 2 := by dsimp [s]; field_simp; ring
  rw [hC] at ht
  have hl : Real.log (F + 1) ≤ Real.log (H + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have hratio : (F + 1) / (H + 1) ≤ 1 := (div_le_one hH1).mpr (by linarith)
  have hmul : s * (F + 1) ≤ F + 2 := by
    dsimp [s]
    simp only [div_eq_mul_inv] at hratio ⊢
    nlinarith only [hratio]
  change H - 2 * Real.log (H + 2) - 3 ≤ F
  linarith

theorem scalar_stationary_linear_bound {α β : Type*}
    [Fintype α] [LinearOrder α] [Fintype β]
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1)
    (channel : α → α → β) (hinj : UpperConeInjective channel) :
    (2 / 3 : ℝ) * finiteEntropy ν - scalarStationaryConstant ≤ stationaryCapacity ν channel := by
  let H := finiteEntropy ν
  let F := stationaryCapacity ν channel
  have hF : 0 ≤ F := (stationaryCapacity_bounds ν hν hs channel).1
  have ht := scalar_stationary_entropy_tradeoff ν hν hs channel hinj (s := 4 / 3) (by norm_num)
  norm_num only at ht
  change H ≤ Real.log (F + 1) + 1 + (4 / 3 : ℝ) * (F + 1) + Real.log 4 at ht
  have hlog : Real.log (F + 1) ≤ F / 6 + Real.log 6 - 5 / 6 := by
    have hp : 0 < F + 1 := by linarith
    have h := Real.log_le_sub_one_of_pos (div_pos hp (by norm_num : (0 : ℝ) < 6))
    rw [Real.log_div hp.ne' (by norm_num : (6 : ℝ) ≠ 0)] at h
    linarith
  have hlog24 : Real.log 24 = Real.log 4 + Real.log 6 := by
    rw [show (24 : ℝ) = 4 * 6 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  change (2 / 3 : ℝ) * H - (1 + (2 / 3 : ℝ) * Real.log 24) ≤ F
  rw [hlog24]
  linarith

end
end Erdos539Geometry
