/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ScalarEndpointRatio
import Erdos539.WeightedEnergyPrefix

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
local instance scalarEndpointWeightsDecidableEq : DecidableEq ℝ := Classical.decEq _

/-- The literal scalar endpoint counterexample weight from the source. -/
def scalarEndpointWeight (N : ℕ) (a : scalarRealInterval N) : ℝ :=
  (1 / (N : ℝ)) ^ (1 / 4 : ℝ) /
    Real.sqrt (channelWeightRatio (scalarPositiveDifferenceChannel (scalarRealInterval N)) (scalarEndpointReference N) a)

theorem scalarEndpointWeight_pos {N : ℕ} (hN : 0 < N) (a : scalarRealInterval N) :
    0 < scalarEndpointWeight N a := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  exact div_pos (Real.rpow_pos_of_pos (by positivity) _)
    (Real.sqrt_pos.2 (channelWeightRatio_pos _ _ (scalarEndpointReference_pos N) a))

/-- Exactly unit fourth-power norm, on every positive interval length. -/
theorem scalarEndpointWeight_powerSum {N : ℕ} (hN : 0 < N) :
    fanPowerSum (scalarPositiveDifferenceChannel (scalarRealInterval N))
      (scalarEndpointWeight N) (scalarEndpointReference N) 4 = 1 := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have h := (fanPowerSum_test (scalarPositiveDifferenceChannel (scalarRealInterval N))
    (scalarEndpointReference N) (fun _ ↦ 1 / (N : ℝ)) (scalarEndpointReference_pos N)
    (fun _ ↦ by positivity) (by norm_num : (0 : ℝ) < 4)).2.1
  change fanPowerSum _ (scalarEndpointWeight N) _ 4 = _ at h
  rw [h]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_coe, scalarRealInterval_card, nsmul_eq_mul]
  field_simp

/-- A single explicit constant lower bound for every weight in the first half. -/
theorem scalarEndpointWeight_prefix_lower {N : ℕ} (hN : 2 ≤ N) (a : scalarRealInterval N)
    (ha : a.val ≤ (N : ℝ) / 2) :
    (1 / (N : ℝ)) ^ (1 / 4 : ℝ) / Real.sqrt (2 * (N : ℝ) / Real.log N) ≤ scalarEndpointWeight N a := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hR := channelWeightRatio_pos (scalarPositiveDifferenceChannel (scalarRealInterval N))
    (scalarEndpointReference N) (scalarEndpointReference_pos N) a
  have h := Real.sqrt_le_sqrt (scalarEndpointRatio_prefix hN a ha)
  exact div_le_div_of_nonneg_left (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < 1 / (N : ℝ)) _).le
    (Real.sqrt_pos.2 hR) h

theorem scalarEndpointWeight_prefix_constant_fourth {N : ℕ} (hN : 2 ≤ N) :
    ((1 / (N : ℝ)) ^ (1 / 4 : ℝ) / Real.sqrt (2 * (N : ℝ) / Real.log N)) ^ 4 =
      (Real.log N) ^ 2 / (4 * (N : ℝ) ^ 3) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hL : 0 < Real.log N := Real.log_pos hNr
  have hp : ((1 / (N : ℝ)) ^ (1 / 4 : ℝ)) ^ 4 = 1 / (N : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))]
    norm_num
  have hs : Real.sqrt (2 * (N : ℝ) / Real.log N) ^ 4 = (2 * (N : ℝ) / Real.log N) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, Real.sq_sqrt (by positivity)]
  rw [div_pow, hp, hs]
  field_simp
  ring

/-- The lower energy bound holds for every even length 2L, L>=1. -/
theorem scalarEndpointWeight_energy_lower {L : ℕ} (hL : 0 < L) :
    (Real.log (2 * L : ℕ)) ^ 2 / 48 ≤
      weightedGibbsPartition (scalarRealInterval (2 * L)) (scalarEndpointWeight (2 * L)) := by
  have hN : 2 ≤ 2 * L := by omega
  let q : ℝ := (1 / (2 * L : ℕ)) ^ (1 / 4 : ℝ) / Real.sqrt (2 * (2 * L : ℕ) / Real.log (2 * L : ℕ))
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have h := weightedEnergy_ge_subset_constant
    (scalarRealInterval_mono (show L ≤ 2 * L by omega))
    (scalarEndpointWeight (2 * L)) (fun a ↦ (scalarEndpointWeight_pos (by omega) a).le) hq (by
      intro a ha
      apply scalarEndpointWeight_prefix_lower hN a
      have hh := scalarRealInterval_lt (⟨a.val, ha⟩ : scalarRealInterval L)
      norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hh ⊢
      linarith)
  have he : q ^ 4 = Real.log (2 * L : ℕ) ^ 2 / (4 * ((2 * L : ℕ) : ℝ) ^ 3) :=
    scalarEndpointWeight_prefix_constant_fourth hN
  rw [he, countingEnergy_scalarRealInterval] at h
  apply le_trans _ h
  have hLp : (0 : ℝ) < L := by exact_mod_cast hL
  have hlogs := sq_nonneg (Real.log (2 * L : ℕ))
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  field_simp
  nlinarith

end
end Erdos539Geometry
