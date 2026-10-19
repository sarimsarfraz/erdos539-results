/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SparseReflectionProductBounds

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical
local instance productExistenceRealDecidableEq {ι : Type} : DecidableEq (ι → ℝ) := Classical.decEq _
local instance fixedStripExistenceIntegerDecidableEq : DecidableEq ((Unit ⊕ Unit) → ℤ) := inferInstance
local instance sparseProductExistenceIntegerDecidableEq : DecidableEq ℤ := Classical.decEq _

theorem reflectionProductCoordinates_card : Fintype.card ReflectionProductCoordinates = 3 := by decide

/-- A single sparse scalar support supplies all strip parameters. The
literal product is in three physical real coordinates. -/
theorem exists_sparse_reflection_products (m : ℕ) (hm : 10 ≤ m) :
    ∃ S : Finset ℤ, S.Nonempty ∧ S ⊆ Finset.Ico 0 ((m ^ 12 : ℕ) : ℤ) ∧
      1 < energyNorm S ∧ ∀ T : ℕ, 0 < T →
      (sparseReflectionProduct S T).Nonempty ∧
      (T : ℝ) / (27 * (m : ℝ)) ≤ energyNorm (sparseReflectionProduct S T) / maxFan (sparseReflectionProduct S T) ∧
      ((sparseReflectionProduct S T).card : ℝ) ≤ 54 * (m : ℝ) * energyNorm (sparseReflectionProduct S T) ∧
      ∀ w, energyNorm (reflectedSupport (sparseReflectionProduct S T) w) ≤
        energyNorm (sparseReflectionProduct S T) * (24 / (m : ℝ) ^ 2) := by
  obtain ⟨S, hI, hlo, _, hnorm, hR⟩ := exists_sparse_reflection_norms m hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hNpos : (0 : ℝ) < S.card := lt_of_lt_of_le (by positivity) hlo
  have hS : S.Nonempty := Finset.card_pos.mp (by exact_mod_cast hNpos)
  have h4 := sparse_reflection_card_le_four (by omega : 0 < m) hS hI hlo
  have h16 : (S.card : ℝ) ≤ 16 * (m : ℝ) * energyNorm S := by
    nlinarith [mul_nonneg hmR.le (energyNorm_nonneg S)]
  have hlarge : 1 < energyNorm S := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 10)
      (by exact_mod_cast hm : (10 : ℝ) ≤ m) 10
    nlinarith only [hpow, hnorm]
  exact ⟨S, hS, hI, hlarge, fun T hT ↦ ⟨sparseReflectionProduct_nonempty hS hT,
    sparseReflectionProduct_fan_ratio hS hmR h4 hT,
    sparseReflectionProduct_card_norm hmR h16 hT,
    sparseReflectionProduct_reflected_bound hmR (fun w ↦ (hR w).2) hS T⟩⟩

/-- Both optimizer-defect bounds and the coefficient-two loss follow for
any support with the product construction's two numerical bounds. -/
theorem reflection_product_optimizer_bounds {P : Finset (ReflectionProductCoordinates → ℝ)}
    (hP : P.Nonempty) {m : ℝ} (hm : 0 < m)
    (hN : (P.card : ℝ) ≤ 54 * m * energyNorm P)
    (hR : ∀ w, energyNorm (reflectedSupport P w) ≤ energyNorm P * (24 / m ^ 2))
    {f : P → ℝ} (hf : f ∈ admissibleWeights P)
    (hE : weightedEnergy P (extendWeight P f) = energyNorm P) :
    (Real.log m - Real.log 24 / 2 ≤ finiteEntropy (fun x ↦ f x ^ 2) - Real.log (energyNorm P)) ∧
    (finiteEntropy (fun x ↦ f x ^ 2) - Real.log (energyNorm P) ≤ Real.log m + Real.log 54) ∧
    ∀ w, (reflectedSupport P w).Nonempty →
      2 * (finiteEntropy (fun x ↦ f x ^ 2) - Real.log (energyNorm P)) - Real.log (24 * 54 ^ 2) ≤
        Real.log (energyNorm P / energyNorm (reflectedSupport P w)) := by
  have he := endpoint_defect_le_of_card_norm hP (by positivity : (0 : ℝ) < 54 * m) hN
    (fun x ↦ f x ^ 2) (fun x ↦ sq_nonneg (f x)) hf.2
  rw [Real.log_mul (by norm_num : (54 : ℝ) ≠ 0) hm.ne'] at he
  refine ⟨reflection_ratio_defect_lower hP hm hR hf hE, by linarith, ?_⟩
  intro w hw
  have hl := reflection_loss_of_norm_bound hP hm w hw (hR w)
  rw [Real.log_mul (by norm_num : (24 : ℝ) ≠ 0) (by norm_num : (54 : ℝ) ^ 2 ≠ 0), Real.log_pow]
  norm_num
  linarith

/-- With the same scalar support, any prescribed norm/fan ratio is
attainable while every reflected support retains at most 24/m^2. -/
theorem exists_large_fan_ratio_reflection_obstruction (m : ℕ) (hm : 10 ≤ m) (R : ℝ) :
    ∃ S : Finset ℤ, ∃ T : ℕ, 0 < T ∧ (sparseReflectionProduct S T).Nonempty ∧
      R ≤ energyNorm (sparseReflectionProduct S T) / maxFan (sparseReflectionProduct S T) ∧
      ((sparseReflectionProduct S T).card : ℝ) ≤ 54 * (m : ℝ) * energyNorm (sparseReflectionProduct S T) ∧
      ∀ w, energyNorm (reflectedSupport (sparseReflectionProduct S T) w) ≤
        energyNorm (sparseReflectionProduct S T) * (24 / (m : ℝ) ^ 2) := by
  obtain ⟨S, _, _, _, hprod⟩ := exists_sparse_reflection_products m hm
  obtain ⟨T, hT⟩ := exists_nat_gt (max 0 (27 * (m : ℝ) * R))
  have hTpos : 0 < T := by exact_mod_cast ((le_max_left _ _).trans_lt hT : (0 : ℝ) < T)
  obtain ⟨hP, hfan, hcard, href⟩ := hprod T hTpos
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  refine ⟨S, T, hTpos, hP, le_trans ?_ hfan, hcard, href⟩
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith only [(le_max_right _ _).trans_lt hT]

end
end Erdos539Geometry
