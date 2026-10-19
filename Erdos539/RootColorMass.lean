/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CriticalColorMass
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι : Type*} [Fintype ι]
local instance rootColorMassDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

namespace IsProjectionCriticalCore
variable {S T V R : Finset (ι → ℝ)} {I : Finset ι} {b : ℝ}

/-- The root-level multi-color bound from the actual optimizer law.
It also covers deleting the whole support. -/
theorem root_color_mass_linear (h : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    (hVT : V ⊆ T) (hkill : KillsColors T V R)
    {f : T → ℝ} (hf : f ∈ admissibleWeights T)
    (hE : weightedEnergy T (extendWeight T f) = energyNorm T) :
    (R.card : ℝ) ≤ (1 + 1 / b) * (posDiff T).card * weightSquareSum V (extendWeight T f) := by
  let mu := weightSquareSum V (extendWeight T f)
  have hmass : weightSquareSum (T \ V) (extendWeight T f) = 1 - mu := by
    have hs := Finset.sum_sdiff (f := fun x ↦ extendWeight T f x ^ 2) hVT
    change weightSquareSum (T \ V) (extendWeight T f) + mu = weightSquareSum T (extendWeight T f) at hs
    rw [weightSquareSum_extend, hf.2] at hs
    linarith
  have hmu : mu ≤ 1 := by
    have hn := weightSquareSum_nonneg (T \ V) (extendWeight T f)
    rw [hmass] at hn
    linarith
  have hpow : (posDiff T).card * (1 - mu) ^ (1 + 1 / b) ≤
      ((posDiff T).card : ℝ) - R.card := by
    have hl : ((posDiff T).card : ℝ) *
        (weightSquareSum (T \ V) (extendWeight T f)) ^ (1 + 1 / b) ≤ (posDiff (T \ V)).card := by
      by_cases hn : (T \ V).Nonempty
      · exact h.subset_mass_bound hb hf hE hn Finset.sdiff_subset
      · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
        rw [weightSquareSum, Finset.sum_empty, Real.zero_rpow (show 1 + 1 / b ≠ 0 by positivity), mul_zero]
        exact Nat.cast_nonneg _
    rw [hmass] at hl
    exact hl.trans hkill.palette_bound
  have hs : (1 : ℝ) ≤ 1 + 1 / b := by
    have hp : 0 < 1 / b := by positivity
    linarith
  have hbern := one_add_mul_self_le_rpow_one_add (s := -mu) (by linarith) hs
  have hm := mul_le_mul_of_nonneg_left hbern (Nat.cast_nonneg (posDiff T).card : (0 : ℝ) ≤ _)
  simp only [← sub_eq_add_neg] at hm
  dsimp [mu] at *
  nlinarith

end IsProjectionCriticalCore

omit [Fintype ι] in
/-- The atom bound summed over an actual subset of the optimizer support. -/
theorem energyMaximizer_mass_mul_norm_le_card {T A : Finset (ι → ℝ)}
    (hT : T.Nonempty) (hAT : A ⊆ T) {f : T → ℝ} (hf : f ∈ admissibleWeights T)
    (hE : weightedEnergy T (extendWeight T f) = energyNorm T) :
    weightSquareSum A (extendWeight T f) * energyNorm T ≤ A.card := by
  have hn := energyNorm_pos hT
  have hpoint (x : ι → ℝ) (hx : x ∈ A) : extendWeight T f x ^ 2 * energyNorm T ≤ 1 := by
    have h := (le_div_iff₀ hn).mp (energyMaximizer_atom_bound hT hf hE ⟨x, hAT hx⟩)
    simpa only [extendWeight, dif_pos (hAT hx)] using h
  have hs := Finset.sum_le_sum (fun x hx ↦ hpoint x hx)
  simpa only [← Finset.sum_mul, weightSquareSum, Finset.sum_const, nsmul_eq_mul, mul_one] using hs

namespace IsProjectionCriticalCore
variable {S T : Finset (ι → ℝ)} {I : Finset ι} {b : ℝ}

/-- A coordinate fiber killing one actual color bounds the size of its
projection. No exposed-mask or genericity assumption is hidden here. -/
theorem color_killing_fiber_projection_bound (h : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    (J : Finset ι) (v : J → ℝ) (z : ι → ℝ)
    (hkill : KillsColors T (fiber T (project J) v) {z}) :
    ((projection T J).card : ℝ) ≤
      (1 + 1 / b) * (posDiff T).card * (differences T).card / energyNorm T := by
  obtain ⟨f, hfn, hfs, hE⟩ := energyNorm_attained h.nonempty
  have hf : f ∈ admissibleWeights T := ⟨hfn, hfs⟩
  let A := fiber T (project J) v
  have hAT : A ⊆ T := fun _ hx ↦ (mem_fiber.mp hx).1
  have hl := h.root_color_mass_linear hb hAT hkill hf hE
  simp only [Finset.card_singleton, Nat.cast_one] at hl
  have hn := energyNorm_pos h.nonempty
  have hcard := energyMaximizer_mass_mul_norm_le_card h.nonempty hAT hf hE
  have hs : 0 ≤ (1 + 1 / b) * (posDiff T).card := by positivity
  have hm := mul_le_mul_of_nonneg_right hl hn.le
  have hc := mul_le_mul_of_nonneg_left hcard hs
  have hA : energyNorm T ≤ (1 + 1 / b) * (posDiff T).card * A.card := by nlinarith
  have hp := mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg (projection T J).card : (0 : ℝ) ≤ _)
  have hw : ((projection T J).card : ℝ) * A.card ≤ (differences T).card := by
    exact_mod_cast projection_mul_card_fiber_le_differences T J v
  have hh := mul_le_mul_of_nonneg_left hw hs
  apply (le_div_iff₀ hn).mpr
  nlinarith

end IsProjectionCriticalCore
end
end Erdos539Geometry
