/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.OptimizerProjectedEntropy
import Erdos539.CriticalCorePotential

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
variable {ι H : Type*} [Fintype ι] [AddCommGroup H] [DecidableEq H]
local instance criticalFiberAmbientDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _
local instance criticalFiberImageDecidableEq (S : Finset (ι → ℝ)) (φ : (ι → ℝ) → H) :
    DecidableEq (S.image φ) := Classical.decEq _

/-- The original critical core's potential on each literal affine fiber. -/
def fiberPalettePotential (T : Finset (ι → ℝ)) (φ : (ι → ℝ) →+ H) (b : ℝ) (y : T.image φ) : ℝ :=
  rootPotential b (posDiff T).card (energyNorm T) (posDiff (fiber T φ y.val)).card (energyNorm (fiber T φ y.val))

def meanFiberPalettePotential (T : Finset (ι → ℝ)) (φ : (ι → ℝ) →+ H) (ν : T → ℝ) (b : ℝ) : ℝ :=
  ∑ y, finitePush ν (imageEndpoint T φ) y * fiberPalettePotential T φ b y

namespace IsProjectionCriticalCore
variable {S T : Finset (ι → ℝ)} {I : Finset ι} {b : ℝ}

theorem fiberPalettePotential_nonneg (h : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    (φ : (ι → ℝ) →+ H) (y : T.image φ) : 0 ≤ fiberPalettePotential T φ b y :=
  rootPotential_nonneg_of_minimal hb (h.compare_subset (imageFiber_nonempty T φ y)
    (fun _ hx ↦ (mem_fiber.mp hx).1))

theorem meanFiberPalettePotential_nonneg (h : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    (φ : (ι → ℝ) →+ H) (ν : T → ℝ) (hν : ∀ x, 0 ≤ ν x) : 0 ≤ meanFiberPalettePotential T φ ν b :=
  Finset.sum_nonneg (fun y _ ↦ mul_nonneg (finitePush_nonneg ν (imageEndpoint T φ) hν y)
    (h.fiberPalettePotential_nonneg hb φ y))

/-- Mean potential cost of actual coordinate fibers, with coefficient
one of the optimized projection profile. The original optimizer is fixed. -/
theorem meanFiberPalettePotential_le (h : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    {f : T → ℝ} (hf : f ∈ admissibleWeights T)
    (hE : weightedEnergy T (extendWeight T f) = energyNorm T) (φ : (ι → ℝ) →+ H) :
    meanFiberPalettePotential T φ (fun x ↦ f x ^ 2) b ≤
      (∑ y, finitePush (fun x ↦ f x ^ 2) (imageEndpoint T φ) y * Real.log ((posDiff (fiber T φ y.val)).card : ℝ)) -
      Real.log ((posDiff T).card : ℝ) + criticalAlpha b *
        stationaryEnergyProfile (T.image φ) (finitePush (fun x ↦ f x ^ 2) (imageEndpoint T φ)) := by
  let p := finitePush (fun x ↦ f x ^ 2) (imageEndpoint T φ)
  have hs : ∑ y, p y = 1 := by rw [finitePush_sum, hf.2]
  have hretain := (optimizer_meanFiberLogEnergy_lower_optimized h.nonempty hf hE φ).trans
    (meanFiberLogEnergy_le_logNorm φ (fun x ↦ f x ^ 2) (fun x ↦ sq_nonneg (f x)))
  have ha : 0 ≤ criticalAlpha b := by unfold criticalAlpha; positivity
  have hm := mul_le_mul_of_nonneg_left hretain ha
  have hid : meanFiberPalettePotential T φ (fun x ↦ f x ^ 2) b =
      (∑ y, p y * Real.log ((posDiff (fiber T φ y.val)).card : ℝ)) -
      Real.log ((posDiff T).card : ℝ) - criticalAlpha b *
        ((∑ y, p y * Real.log (energyNorm (fiber T φ y.val))) - Real.log (energyNorm T)) := by
    have hpoint (y : T.image φ) : p y * fiberPalettePotential T φ b y =
        p y * Real.log ((posDiff (fiber T φ y.val)).card : ℝ) -
          criticalAlpha b * (p y * Real.log (energyNorm (fiber T φ y.val))) -
          p y * (Real.log ((posDiff T).card : ℝ) - criticalAlpha b * Real.log (energyNorm T)) := by
      unfold fiberPalettePotential rootPotential
      ring
    change (∑ y, p y * fiberPalettePotential T φ b y) = _
    simp_rw [hpoint]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hs, one_mul]
    ring
  rw [hid]
  change criticalAlpha b * (Real.log (energyNorm T) - stationaryEnergyProfile (T.image φ) p) ≤
    criticalAlpha b * (∑ y, p y * Real.log (energyNorm (fiber T φ y.val))) at hm
  change _ ≤ (∑ y, p y * Real.log ((posDiff (fiber T φ y.val)).card : ℝ)) -
    Real.log ((posDiff T).card : ℝ) + criticalAlpha b * stationaryEnergyProfile (T.image φ) p
  nlinarith

theorem meanFiberPalettePotential_le_profile (h : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    {f : T → ℝ} (hf : f ∈ admissibleWeights T)
    (hE : weightedEnergy T (extendWeight T f) = energyNorm T) (φ : (ι → ℝ) →+ H) :
    meanFiberPalettePotential T φ (fun x ↦ f x ^ 2) b ≤ criticalAlpha b *
      stationaryEnergyProfile (T.image φ) (finitePush (fun x ↦ f x ^ 2) (imageEndpoint T φ)) := by
  have h := h.meanFiberPalettePotential_le hb hf hE φ
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun y _ ↦
    mul_le_mul_of_nonneg_left
      (Real.log_le_log (show (0 : ℝ) < (posDiff (fiber T φ y.val)).card by
          exact_mod_cast posDiff_card_pos (imageFiber_nonempty T φ y))
        (show ((posDiff (fiber T φ y.val)).card : ℝ) ≤ (posDiff T).card by
          exact_mod_cast Finset.card_le_card (posDiff_mono (fun _ hx ↦ (mem_fiber.mp hx).1))))
      (finitePush_nonneg (fun x ↦ f x ^ 2) (imageEndpoint T φ) (fun x ↦ sq_nonneg (f x)) y))
  rw [← Finset.sum_mul, finitePush_sum, hf.2, one_mul] at hsum
  linarith

/-- Mean logarithmic palette retention on the actual fibers of a selected
critical core. It supplies no disjoint-palette or common-anchor claim. -/
theorem meanFiberLogPalette_lower (h : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    {f : T → ℝ} (hf : f ∈ admissibleWeights T)
    (hE : weightedEnergy T (extendWeight T f) = energyNorm T) (φ : (ι → ℝ) →+ H) :
    Real.log ((posDiff T).card : ℝ) - criticalAlpha b *
      stationaryEnergyProfile (T.image φ) (finitePush (fun x ↦ f x ^ 2) (imageEndpoint T φ)) ≤
        ∑ y, finitePush (fun x ↦ f x ^ 2) (imageEndpoint T φ) y * Real.log ((posDiff (fiber T φ y.val)).card : ℝ) := by
  have hn := h.meanFiberPalettePotential_nonneg hb φ (fun x ↦ f x ^ 2) (fun x ↦ sq_nonneg (f x))
  have hu := h.meanFiberPalettePotential_le hb hf hE φ
  linarith

end IsProjectionCriticalCore
end
end Erdos539Geometry
