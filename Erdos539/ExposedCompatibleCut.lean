/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ExposedProjectionBounds
import Erdos539.EnergyFanNorm
import Erdos539.SignMasks

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι]
local instance exposedCompatibleCutDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _
local instance exposedCompatibleCutProjectionDecidableEq
    (S : Finset (ι → ℝ)) (I : Finset ι) : DecidableEq (projection S I) := Classical.decEq _

namespace IsProjectionCriticalCore
variable {S T : Finset (ι → ℝ)} {I : Finset ι} {b : ℝ}

/-- Two actual exposed masks covering the coordinates provide one
complementary cut with both actual marginal energies controlled. The
weight is any normalized weight; no child optimizer is substituted. -/
theorem exposed_cover_marginal_bounds (h : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    {J K : Finset ι} (hJ : IsExposedActiveMask T J) (hK : IsExposedActiveMask T K)
    (hcover : J ∪ K = Finset.univ) (f : T → ℝ) (hf : ∑ x, f x ^ 2 = 1) :
    let R := (1 + 1 / b) * (posDiff T).card * (differences T).card / energyNorm T
    actualMarginalEnergy T (extendWeight T f) J ≤ R ∧
      actualMarginalEnergy T (extendWeight T f) (Finset.univ \ J) ≤ R := by
  have hsub : Finset.univ \ J ⊆ K := by
    intro i hi
    have hn := (Finset.mem_sdiff.mp hi).2
    have hu : i ∈ J ∪ K := hcover ▸ Finset.mem_univ i
    exact (Finset.mem_union.mp hu).resolve_left hn
  have hcard : ((projection T (Finset.univ \ J)).card : ℝ) ≤ (projection T K).card := by
    exact_mod_cast projection_card_mono T hsub
  exact ⟨((actualMarginalEnergy_unit_bounds T J f hf).2.trans (energyNorm_le_card _)).trans
      (h.exposed_projection_bound hb hJ),
    (((actualMarginalEnergy_unit_bounds T (Finset.univ \ J) f hf).2.trans (energyNorm_le_card _)).trans hcard).trans
      (h.exposed_projection_bound hb hK)⟩

/-- The exact surplus-dependent weighted-product certificate for a
single compatible cut, uniform over actual normalized root weights. -/
theorem exposed_cover_weighted_product (h : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    {J K : Finset ι} (hJ : IsExposedActiveMask T J) (hK : IsExposedActiveMask T K)
    (hcover : J ∪ K = Finset.univ) (f : T → ℝ) (hf : ∑ x, f x ^ 2 = 1)
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    let A := Real.log (differences T).card - Real.log (energyNorm T) +
      (2 * Real.log (posDiff T).card - Real.log (energyNorm T)) / 2 + Real.log (1 + 1 / b)
    actualMarginalEnergy T (extendWeight T f) (Finset.univ \ J) ^ a *
      actualMarginalEnergy T (extendWeight T f) J ^ c ≤
        Real.exp ((a + c) * A) * (maxFan T : ℝ) ^ (a + c) := by
  let A := Real.log (differences T).card - Real.log (energyNorm T) +
    (2 * Real.log (posDiff T).card - Real.log (energyNorm T)) / 2 + Real.log (1 + 1 / b)
  let R := (1 + 1 / b) * (posDiff T).card * (differences T).card / energyNorm T
  let LJ := actualMarginalEnergy T (extendWeight T f) J
  let LC := actualMarginalEnergy T (extendWeight T f) (Finset.univ \ J)
  have hbounds := h.exposed_cover_marginal_bounds hb hJ hK hcover f hf
  have hLJ : 0 < LJ := lt_of_lt_of_le zero_lt_one (actualMarginalEnergy_unit_bounds T J f hf).1
  have hLC : 0 < LC := lt_of_lt_of_le zero_lt_one (actualMarginalEnergy_unit_bounds T (Finset.univ \ J) f hf).1
  have hs : 0 < 1 + 1 / b := by positivity
  have hq : (0 : ℝ) < (posDiff T).card := by exact_mod_cast posDiff_card_pos h.nonempty
  have hW : (0 : ℝ) < (differences T).card := by
    exact_mod_cast (h.nonempty.card_pos.trans_le (card_le_real_differences h.nonempty))
  have hM : (0 : ℝ) < maxFan T := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (one_le_maxFan h.nonempty))
  have hn := energyNorm_pos h.nonempty
  have hnorm := Real.log_le_log hn (energyNorm_le_maxFan_sq h.nonempty)
  rw [Real.log_pow] at hnorm
  norm_num only [Nat.cast_ofNat] at hnorm
  have hlogR : Real.log R ≤ A + Real.log (maxFan T) := by
    dsimp [R, A]
    rw [Real.log_div (mul_pos (mul_pos hs hq) hW).ne' hn.ne',
      Real.log_mul (mul_pos hs hq).ne' hW.ne', Real.log_mul hs.ne' hq.ne']
    linarith
  have hj := (Real.log_le_log hLJ hbounds.1).trans hlogR
  have hk := (Real.log_le_log hLC hbounds.2).trans hlogR
  have hm1 := mul_le_mul_of_nonneg_left hk ha
  have hm2 := mul_le_mul_of_nonneg_left hj hc
  change LC ^ a * LJ ^ c ≤ Real.exp ((a + c) * A) * (maxFan T : ℝ) ^ (a + c)
  apply (Real.log_le_log_iff (mul_pos (Real.rpow_pos_of_pos hLC _) (Real.rpow_pos_of_pos hLJ _))
    (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hM _))).mp
  rw [Real.log_mul (Real.rpow_pos_of_pos hLC _).ne' (Real.rpow_pos_of_pos hLJ _).ne',
    Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos hM _).ne',
    Real.log_rpow hLC, Real.log_rpow hLJ, Real.log_rpow hM, Real.log_exp]
  nlinarith

end IsProjectionCriticalCore
end
end Erdos539Geometry
