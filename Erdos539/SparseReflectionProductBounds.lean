/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SparseReflectionProductGeometry
import Erdos539.SparseReflectionNorms
import Erdos539.ReflectionRatioDefect

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
local instance productBoundsRealDecidableEq {ι : Type} : DecidableEq (ι → ℝ) := Classical.decEq _
local instance fixedStripBoundsIntegerDecidableEq : DecidableEq ((Unit ⊕ Unit) → ℤ) := inferInstance
local instance sparseProductBoundsIntegerDecidableEq : DecidableEq ℤ := Classical.decEq _

theorem sparse_reflection_card_le_four {m : ℕ} (hm : 0 < m) {S : Finset ℤ} (hS : S.Nonempty)
    (hI : S ⊆ Finset.Ico 0 ((m ^ 12 : ℕ) : ℤ))
    (hlo : (m : ℝ) ^ 11 / 2 ≤ (S.card : ℝ)) :
    (S.card : ℝ) ≤ 4 * (m : ℝ) * energyNorm S := by
  have hE := interval_card_sq_le_energyNorm hS hI
  rw [Nat.cast_pow] at hE
  have hh := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg (α := ℝ) S.card)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  apply (mul_le_mul_iff_right₀ (pow_pos hmR 11)).mp
  nlinarith only [hE, hh]

theorem sparseReflectionProduct_fan_ratio {S : Finset ℤ} (hS : S.Nonempty)
    {m : ℝ} (hm : 0 < m) (hN : (S.card : ℝ) ≤ 4 * m * energyNorm S)
    {T : ℕ} (hT : 0 < T) :
    (T : ℝ) / (27 * m) ≤ energyNorm (sparseReflectionProduct S T) / maxFan (sparseReflectionProduct S T) := by
  have hp := sparseReflectionProduct_nonempty hS hT
  have hfan : (0 : ℝ) < maxFan (sparseReflectionProduct S T) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxFan hp))
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hb := gibbsStrip_energyNorm_lower hT
  have hn := mul_le_mul_of_nonneg_left hb (energyNorm_nonneg S)
  rw [← sparseReflectionProduct_norm] at hn
  have hfanupper : (maxFan (sparseReflectionProduct S T) : ℝ) ≤ 2 * (S.card : ℝ) * (T : ℝ) ^ 2 := by
    rw [sparseReflectionProduct_fan hS hT]
    nlinarith [Nat.cast_nonneg (α := ℝ) S.card]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 27 * m) hfan).mpr
  have h1 := mul_le_mul_of_nonneg_left hfanupper ht.le
  have h2 := mul_le_mul_of_nonneg_right hN (by positivity : (0 : ℝ) ≤ 2 * (T : ℝ) ^ 3)
  have h3 := mul_le_mul_of_nonneg_left hn (by positivity : (0 : ℝ) ≤ 27 * m)
  nlinarith only [h1, h2, h3]

theorem sparseReflectionProduct_card_norm {S : Finset ℤ} {m : ℝ} (hm : 0 < m)
    (hN : (S.card : ℝ) ≤ 16 * m * energyNorm S) {T : ℕ} (hT : 0 < T) :
    ((sparseReflectionProduct S T).card : ℝ) ≤ 54 * m * energyNorm (sparseReflectionProduct S T) := by
  rw [sparseReflectionProduct_card S hT, Nat.cast_mul, Nat.cast_pow, sparseReflectionProduct_norm]
  have h1 := mul_le_mul_of_nonneg_right hN (by positivity : (0 : ℝ) ≤ (T : ℝ) ^ 3)
  have h2 := mul_le_mul_of_nonneg_left (gibbsStrip_energyNorm_lower hT)
    (mul_nonneg (by positivity : (0 : ℝ) ≤ 54 * m) (energyNorm_nonneg S))
  nlinarith only [h1, h2]

theorem sparseReflectionProduct_reflected_bound {S : Finset ℤ} {m : ℝ} (hm : 0 < m)
    (hR : ∀ w : ℤ, energyNorm (reflectedSupport S w) / energyNorm S ≤ 24 / m ^ 2)
    (hS : S.Nonempty) (T : ℕ) (w : ReflectionProductCoordinates → ℝ) :
    energyNorm (reflectedSupport (sparseReflectionProduct S T) w) ≤
      energyNorm (sparseReflectionProduct S T) * (24 / m ^ 2) := by
  exact reflected_norm_bound_image reflectionProductEmbedding reflectionProductEmbedding_injective
    (by positivity) (reflected_norm_bound_product (by positivity) (fun z ↦ by
      have h := (div_le_iff₀ (energyNorm_pos hS)).mp (hR z)
      simpa only [mul_comm] using h)) w

end
end Erdos539Geometry
