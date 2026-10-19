/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ExposedProjectionBounds
import Erdos539.AxisPalette

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {ι : Type*} [Fintype ι]
local instance fullExposedMaskDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

namespace IsProjectionCriticalCore
variable {S T : Finset (ι → ℝ)} {I : Finset ι} {b : ℝ}

theorem color_killing_set_norm_bound (h : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    {A : Finset (ι → ℝ)} (hAT : A ⊆ T) {z : ι → ℝ} (hkill : KillsColors T A {z}) :
    energyNorm T ≤ (1 + 1 / b) * (posDiff T).card * A.card := by
  obtain ⟨f, hfn, hfs, hE⟩ := energyNorm_attained h.nonempty
  have hf : f ∈ admissibleWeights T := ⟨hfn, hfs⟩
  have hl := h.root_color_mass_linear hb hAT hkill hf hE
  simp only [Finset.card_singleton, Nat.cast_one] at hl
  have hn := energyNorm_pos h.nonempty
  have hcard := energyMaximizer_mass_mul_norm_le_card h.nonempty hAT hf hE
  have hs : 0 ≤ (1 + 1 / b) * (posDiff T).card := by positivity
  have hm := mul_le_mul_of_nonneg_right hl hn.le
  have hc := mul_le_mul_of_nonneg_left hcard hs
  nlinarith

/-- A full exposed output has a singleton endpoint fiber and supplies
the stronger terminal norm bound. -/
theorem full_exposed_norm_bound (h : IsProjectionCriticalCore S b I T) (hb : 0 < b)
    (hexposed : IsExposedActiveMask T Finset.univ) :
    energyNorm T ≤ (1 + 1 / b) * (posDiff T).card := by
  obtain ⟨w, z, hex⟩ := hexposed
  obtain ⟨v, hv⟩ := hex.exists_color_killing_fiber
  have hAT : fiber T (project Finset.univ) v ⊆ T := fun _ hx ↦ (mem_fiber.mp hx).1
  have hcard : (fiber T (project Finset.univ) v).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have he := (mem_fiber.mp hx).2.trans (mem_fiber.mp hy).2.symm
    funext i
    exact congrFun he ⟨i, Finset.mem_univ i⟩
  have hr := h.color_killing_set_norm_bound hb hAT hv
  have hm := mul_le_mul_of_nonneg_left (show ((fiber T (project Finset.univ) v).card : ℝ) ≤ 1 by
    exact_mod_cast hcard) (show 0 ≤ (1 + 1 / b) * (posDiff T).card by positivity)
  simpa only [mul_one] using hr.trans hm

end IsProjectionCriticalCore

theorem full_exposed_scalar_impossible {b L q : ℝ} (hb : 4 ≤ b) (hq : 2 ≤ q)
    (hc : 2 * Real.log q ≤ (1 + 1 / b) * L)
    (he : L ≤ Real.log (1 + 1 / b) + Real.log q) : False := by
  have hbpos : 0 < b := by linarith
  have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) hb
  have hs0 : (0 : ℝ) ≤ 1 + 1 / b := by positivity
  have hs1 : (1 : ℝ) ≤ 1 + 1 / b := by
    have hp : 0 < 1 / b := by positivity
    linarith
  have hs5 : 1 + 1 / b ≤ (5 / 4 : ℝ) := by linarith
  have hlog0 := Real.log_nonneg hs1
  have hlog5 := Real.log_le_log (by positivity : (0 : ℝ) < 1 + 1 / b) hs5
  have hlogq := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hq
  have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hmul := mul_le_mul_of_nonneg_left he hs0
  have hupper := mul_le_mul hs5 hlog5 hlog0 (by norm_num : (0 : ℝ) ≤ 5 / 4)
  have hlower := mul_le_mul_of_nonneg_right (show (3 / 4 : ℝ) ≤ 2 - (1 + 1 / b) by linarith)
    (show 0 ≤ Real.log q by linarith)
  have hn := Real.log_lt_log (by norm_num : (0 : ℝ) < (5 / 4 : ℝ) ^ (5 : ℕ))
    (by norm_num : (5 / 4 : ℝ) ^ (5 : ℕ) < (2 : ℝ) ^ (3 : ℕ))
  rw [Real.log_pow, Real.log_pow] at hn
  norm_num only [Nat.cast_ofNat] at hn
  nlinarith

namespace IsProjectionCriticalCore
variable {S T : Finset (ι → ℝ)} {b : ℝ}

/-- No nontrivial full critical core exposes all physical coordinates
when b>=4. The numerical comparison is proved with exact rational powers. -/
theorem not_full_exposed [Nonempty ι] (h : IsProjectionCriticalCore S b Finset.univ T)
    (hS : S.Nonempty) (hb : 4 ≤ b) : ¬ IsExposedActiveMask T Finset.univ := by
  intro hexposed
  have hbpos : 0 < b := by linarith
  have hq : (2 : ℝ) ≤ (posDiff T).card := by
    have hd := Fintype.card_pos (α := ι)
    have hp := h.mask_card_add_one_le_palette hbpos
    simp only [Finset.card_univ] at hp
    exact_mod_cast (show 2 ≤ (posDiff T).card by omega)
  have hlog := Real.log_le_log (energyNorm_pos h.nonempty) (h.full_exposed_norm_bound hbpos hexposed)
  rw [Real.log_mul (by positivity : 1 + 1 / b ≠ 0)
    (by linarith : ((posDiff T).card : ℝ) ≠ 0)] at hlog
  exact full_exposed_scalar_impossible hb hq (h.singleton_log_bound hS hbpos) hlog

end IsProjectionCriticalCore
end
end Erdos539Geometry
