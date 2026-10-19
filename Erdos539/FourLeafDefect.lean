/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FourLeafProjectionEntropy

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical

theorem fourLeafBranch_nonempty {T : ℕ} (hT : 0 < T) : (fourLeafBranch T).Nonempty := by
  rw [← Finset.card_pos, fourLeafBranch_card]
  exact pow_pos hT _

/-- Every branch difference is the linear image of seven signed digits,
each in an interval of length 2T. -/
theorem fourLeafBranch_difference_card (T : ℕ) :
    (fourLeafBranch T - fourLeafBranch T).card ≤ (2 * T) ^ 7 := by
  let e : (Fin 7 → Fin (2 * T)) → (Fin 4 → ℤ) :=
    fun c ↦ fourLeafLinear (10 * T) (fun j ↦ (c j : ℤ) - T)
  have hsub : fourLeafBranch T - fourLeafBranch T ⊆ Finset.univ.image e := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_sub.mp hz
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hy
    let c : Fin 7 → Fin (2 * T) := fun j ↦
      ⟨(a j).val + T - (b j).val, by have := (a j).isLt; have := (b j).isLt; omega⟩
    have hc : (fun j ↦ (c j : ℤ) - T) = (fun j ↦ (a j : ℤ)) - (fun j ↦ (b j : ℤ)) := by
      funext j
      have := (a j).isLt
      have := (b j).isLt
      dsimp [c]
      omega
    refine Finset.mem_image.mpr ⟨c, Finset.mem_univ _, ?_⟩
    change fourLeafLinear (10 * T) (fun j ↦ (c j : ℤ) - T) = _
    rw [hc, map_sub]
    rfl
  have h := (Finset.card_le_card hsub).trans (Finset.card_image_le (s := Finset.univ) (f := e))
  simpa using h

/-- A uniform branch has dimension-independent-in-T stationary defect
at most seven log 2, by its actual signed difference support. -/
theorem fourLeafBranch_defect {T : ℕ} (hT : 0 < T) :
    stationaryEntropyDefect (fourLeafBranch T) (uniformReference (fourLeafBranch T)) ≤ 7 * Real.log 2 := by
  have hS := fourLeafBranch_nonempty hT
  have h := stationaryEntropyDefect_uniform_upper hS
  have hN : (0 : ℝ) < (fourLeafBranch T).card := by exact_mod_cast hS.card_pos
  have hr : (0 : ℝ) < (fourLeafBranch T - fourLeafBranch T).card := by
    obtain ⟨x, hx⟩ := hS
    exact_mod_cast (Finset.card_pos.mpr ⟨0, Finset.mem_sub.mpr ⟨x, hx, x, hx, sub_self x⟩⟩)
  have hb : ((fourLeafBranch T - fourLeafBranch T).card : ℝ) / (fourLeafBranch T).card ≤ (2 : ℝ) ^ 7 := by
    apply (div_le_iff₀ hN).mpr
    have hc : ((fourLeafBranch T - fourLeafBranch T).card : ℝ) ≤ (2 * (T : ℝ)) ^ 7 := by
      exact_mod_cast fourLeafBranch_difference_card T
    rw [fourLeafBranch_card]
    simpa only [Nat.cast_pow, mul_pow] using hc
  have hl := Real.log_le_log (div_pos hr hN) hb
  rw [Real.log_pow] at hl
  exact h.trans hl

end
end Erdos539Geometry
