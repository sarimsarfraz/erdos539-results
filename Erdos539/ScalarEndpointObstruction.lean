/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ScalarEndpointWeights
import Erdos539.FanNormEntropyEquivalence

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
local instance scalarEndpointObstructionDecidableEq : DecidableEq ℝ := Classical.decEq _

/-- The same literal weights have norm at most one at every exponent p>=4. -/
theorem scalarEndpointWeight_large_powerSum {N : ℕ} (hN : 0 < N) {p : ℝ} (hp : 4 ≤ p) :
    (fanPowerSum (scalarPositiveDifferenceChannel (scalarRealInterval N))
      (scalarEndpointWeight N) (scalarEndpointReference N) p) ^ (4 / p) ≤ 1 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hw : 0 < (1 / (N : ℝ)) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hw1 : (1 / (N : ℝ)) ^ (1 / 4 : ℝ) ≤ 1 :=
    Real.rpow_le_one (by positivity) (by simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hN1)) (by norm_num)
  have he (a : scalarRealInterval N) : scalarEndpointWeight N a *
      Real.sqrt (channelWeightRatio (scalarPositiveDifferenceChannel (scalarRealInterval N)) (scalarEndpointReference N) a) =
        (1 / (N : ℝ)) ^ (1 / 4 : ℝ) := by
    unfold scalarEndpointWeight
    exact div_mul_cancel₀ _ (Real.sqrt_pos.2 (channelWeightRatio_pos _ _ (scalarEndpointReference_pos N) a)).ne'
  have hsum : fanPowerSum (scalarPositiveDifferenceChannel (scalarRealInterval N))
      (scalarEndpointWeight N) (scalarEndpointReference N) p ≤
        fanPowerSum (scalarPositiveDifferenceChannel (scalarRealInterval N))
          (scalarEndpointWeight N) (scalarEndpointReference N) 4 := by
    unfold fanPowerSum
    apply Finset.sum_le_sum
    intro a _
    rw [he a]
    exact Real.rpow_le_rpow_of_exponent_ge hw hw1 hp
  rw [scalarEndpointWeight_powerSum hN] at hsum
  apply Real.rpow_le_one _ hsum (by positivity)
  unfold fanPowerSum
  apply Finset.sum_nonneg
  intro a _
  rw [he a]
  exact (Real.rpow_pos_of_pos hw _).le

/-- The exact lower energy grows past any prescribed constant on even
integer lengths, not merely on finitely tested examples. -/
theorem scalarEndpointWeight_energy_unbounded (C : ℝ) (hC : 0 < C) :
    ∃ L : ℕ, 0 < L ∧ C <
      weightedGibbsPartition (scalarRealInterval (2 * L)) (scalarEndpointWeight (2 * L)) := by
  obtain ⟨L, hL⟩ := exists_nat_gt (max 1 (Real.exp (Real.sqrt (48 * C) + 1)))
  have hL1 : (1 : ℝ) < L := (le_max_left _ _).trans_lt hL
  have hLp : 0 < L := by exact_mod_cast (show (0 : ℝ) < L by linarith)
  have he : Real.exp (Real.sqrt (48 * C) + 1) < (2 * L : ℕ) := by
    have h := (le_max_right _ _).trans_lt hL
    push_cast
    linarith
  have hlog := Real.log_lt_log (Real.exp_pos _) he
  rw [Real.log_exp] at hlog
  have hs := Real.sq_sqrt (show 0 ≤ 48 * C by positivity)
  have hn := Real.sqrt_nonneg (48 * C)
  have hgap : C < Real.log (2 * L : ℕ) ^ 2 / 48 := by nlinarith
  exact ⟨L, hLp, hgap.trans_le (scalarEndpointWeight_energy_lower hLp)⟩

/-- No uniform positive constant works for the scalar weighted norm
inequality at p=4 or any larger exponent. -/
theorem no_uniform_scalar_fanNormBound_ge_four {p C : ℝ} (hp : 4 ≤ p) (hC : 0 < C) :
    ∃ L : ℕ, 0 < L ∧
      ¬FanNormBound (scalarRealInterval (2 * L))
        (scalarPositiveDifferenceChannel (scalarRealInterval (2 * L))) p C := by
  obtain ⟨L, hL, hE⟩ := scalarEndpointWeight_energy_unbounded C hC
  refine ⟨L, hL, ?_⟩
  intro h
  have hbound := h (scalarEndpointWeight (2 * L)) (scalarEndpointReference (2 * L))
    (scalarEndpointWeight_pos (by omega)) (scalarEndpointReference_pos _)
  have hnorm := scalarEndpointWeight_large_powerSum (show 0 < 2 * L by omega) hp
  have hm := mul_le_mul_of_nonneg_left hnorm hC.le
  linarith

end
end Erdos539Geometry
