/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SparseReflectionNorms
import Erdos539.FiniteEntropy

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
local instance sparseReflectionEntropyIntegerDecidableEq : DecidableEq ℤ := Classical.decEq _
local instance sparseReflectionEntropyIndexDecidableEq (S : Finset ℤ) : DecidableEq S := Classical.decEq _

theorem finiteEntropy_sub_log_norm_le {S : Finset ℤ} (hS : S.Nonempty) {m : ℝ} (hm : 0 < m)
    (hN : (S.card : ℝ) ≤ 16 * m * energyNorm S)
    (ν : S → ℝ) (hν : ∀ x, 0 ≤ ν x) (hs : ∑ x, ν x = 1) :
    finiteEntropy ν - Real.log (energyNorm S) ≤ Real.log m + Real.log 16 := by
  letI : Nonempty S := hS.coe_sort
  have hH := finiteEntropy_le_log_card ν hν hs
  simp only [Fintype.card_coe] at hH
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hlog := Real.log_le_log hcard hN
  rw [Real.log_mul (mul_pos (by norm_num) hm).ne' (energyNorm_pos hS).ne',
    Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) hm.ne'] at hlog
  linarith

theorem reflected_log_norm_loss_of_ratio {S : Finset ℤ} (hS : S.Nonempty) {m : ℝ} (hm : 0 < m)
    (w : ℤ) (hw : (reflectedSupport S w).Nonempty)
    (hr : energyNorm (reflectedSupport S w) / energyNorm S ≤ 24 / m ^ 2) :
    2 * Real.log m - Real.log 24 ≤ Real.log (energyNorm S / energyNorm (reflectedSupport S w)) := by
  have hlog := Real.log_le_log (div_pos (energyNorm_pos hw) (energyNorm_pos hS)) hr
  rw [Real.log_div (energyNorm_pos hw).ne' (energyNorm_pos hS).ne',
    Real.log_div (by norm_num : (24 : ℝ) ≠ 0) (pow_pos hm 2).ne', Real.log_pow] at hlog
  rw [Real.log_div (energyNorm_pos hS).ne' (energyNorm_pos hw).ne']
  norm_num at hlog
  linarith

/-- The coefficient-two lower loss holds simultaneously for every normalized
law, hence for the squared weights of every exact optimizer, on one support. -/
theorem exists_sparse_reflection_entropy_loss (m : ℕ) (hm : 10 ≤ m) :
    ∃ S : Finset ℤ, S.Nonempty ∧ S ⊆ Finset.Ico 0 ((m ^ 12 : ℕ) : ℤ) ∧
      (∀ w : ℤ, energyNorm (reflectedSupport S w) / energyNorm S ≤ 24 / (m : ℝ) ^ 2) ∧
      ∀ ν : S → ℝ, (∀ x, 0 ≤ ν x) → (∑ x, ν x = 1) →
        finiteEntropy ν - Real.log (energyNorm S) ≤ Real.log (m : ℝ) + Real.log 16 ∧
        ∀ w : ℤ, (reflectedSupport S w).Nonempty →
          2 * (finiteEntropy ν - Real.log (energyNorm S)) - Real.log 6144 ≤
            Real.log (energyNorm S / energyNorm (reflectedSupport S w)) := by
  obtain ⟨S, hI, hlo, hhi, hnorm, href⟩ := exists_sparse_reflection_norms m hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hNpos : (0 : ℝ) < S.card := lt_of_lt_of_le (by positivity) hlo
  have hS : S.Nonempty := Finset.card_pos.mp (by exact_mod_cast hNpos)
  have hN : (S.card : ℝ) ≤ 16 * (m : ℝ) * energyNorm S := by
    have h := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 16 * (m : ℝ) by positivity)
    nlinarith only [hhi, h]
  refine ⟨S, hS, hI, fun w ↦ (href w).2, ?_⟩
  intro ν hν hs
  have he := finiteEntropy_sub_log_norm_le hS hmR hN ν hν hs
  refine ⟨he, ?_⟩
  intro w hw
  have hl := reflected_log_norm_loss_of_ratio hS hmR w hw (href w).2
  have hc : Real.log 6144 = Real.log 24 + 2 * Real.log 16 := by
    rw [show (6144 : ℝ) = 24 * 16 ^ 2 by norm_num,
      Real.log_mul (by norm_num : (24 : ℝ) ≠ 0) (by norm_num : (16 : ℝ) ^ 2 ≠ 0), Real.log_pow]
    norm_num
  rw [hc]
  linarith

end
end Erdos539Geometry
