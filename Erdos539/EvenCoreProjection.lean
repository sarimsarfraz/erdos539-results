/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SameLawProjectionChain
import Erdos539.CriticalCoreProfileCover

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι]
local instance evenCoreProjectionDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

namespace IsProjectionCriticalCore
variable {S T : Finset (ι → ℝ)} {I : Finset ι} {b : ℝ}

/-- Half-dimensional projection on an even-dimensional critical core,
retaining the original canonical law. This holds for every b > 0,
hence in particular for the manuscript's b = 4 D. -/
theorem even_core_projection (h : IsProjectionCriticalCore S b I T)
    (hS : S.Nonempty) (hb : 0 < b) (hd : 2 ≤ Fintype.card ι)
    (heven : Even (Fintype.card ι))
    {f : T → ℝ} (hf : f ∈ admissibleWeights T)
    (hE : weightedEnergy T (extendWeight T f) = energyNorm T) :
    let Q := optimizerStationaryAdditiveLaw h.nonempty hf hE
    ∃ J : Finset ι, J.card = Fintype.card ι / 2 ∧
      (1 - criticalAlpha b * Real.log 2) * Real.log (energyNorm T) -
        (Fintype.card ι : ℝ) * Real.log (2 * finiteEntropy (fun x ↦ f x ^ 2) / Fintype.card ι + 2) -
        (3 / 2 : ℝ) * Fintype.card ι ≤ (Q.projectLaw J).energyProfile ∧
      (Q.projectLaw J).energyProfile ≤ Real.log (actualMarginalEnergy T (extendWeight T f) J) := by
  obtain ⟨m, hm⟩ := heven
  have hcard : Fintype.card ι = 2 * m := by omega
  have hmpos : 0 < m := by omega
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hdreal : (Fintype.card ι : ℝ) = 2 * (m : ℝ) := by exact_mod_cast hcard
  let Q := optimizerStationaryAdditiveLaw h.nonempty hf hE
  obtain ⟨J, hJ, hret, henergy⟩ := optimizer_same_law_projection_chain h.nonempty hf hE
    (k := m) (by omega) (by omega)
  refine ⟨J, by omega, ?_, henergy⟩
  have hratio : (Fintype.card ι : ℝ) / m = 2 := by rw [hdreal]; field_simp
  rw [hratio] at hret
  have hH : 0 ≤ finiteEntropy (fun x ↦ f x ^ 2) := finiteEntropy_nonneg _ (fun x ↦ sq_nonneg (f x)) hf.2
  have hlogarg : finiteEntropy (fun x ↦ f x ^ 2) / (m + 1 : ℕ) + 2 ≤
      2 * finiteEntropy (fun x ↦ f x ^ 2) / Fintype.card ι + 2 := by
    have hdiv := div_le_div_of_nonneg_left hH hmreal
      (show (m : ℝ) ≤ (m + 1 : ℕ) by push_cast; linarith)
    have he : 2 * finiteEntropy (fun x ↦ f x ^ 2) / (Fintype.card ι : ℝ) =
        finiteEntropy (fun x ↦ f x ^ 2) / m := by rw [hdreal]; field_simp
    rw [he]
    linarith
  have hlog := Real.log_le_log (show 0 < finiteEntropy (fun x ↦ f x ^ 2) / (m + 1 : ℕ) + 2 by positivity) hlogarg
  have herr := mul_le_mul_of_nonneg_left hlog hmreal.le
  have hfan := h.log_maxFan_le_criticalAlpha hS hb
  have hfanmul := mul_le_mul_of_nonneg_right hfan (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  change (1 - criticalAlpha b * Real.log 2) * Real.log (energyNorm T) -
    (Fintype.card ι : ℝ) * Real.log (2 * finiteEntropy (fun x ↦ f x ^ 2) / Fintype.card ι + 2) -
    (3 / 2 : ℝ) * Fintype.card ι ≤ (Q.projectLaw J).energyProfile
  rw [hdreal] at hret herr ⊢
  nlinarith

end IsProjectionCriticalCore
end
end Erdos539Geometry
