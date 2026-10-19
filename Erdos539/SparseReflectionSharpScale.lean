/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SparseReflectionEntropyLoss
import Erdos539.ReflectedNormRetention

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators Pointwise
local instance sparseReflectionSharpIntegerDecidableEq : DecidableEq ℤ := Classical.decEq _
local instance sparseReflectionSharpIndexDecidableEq (S : Finset ℤ) : DecidableEq S := Classical.decEq _

theorem sparse_reflection_defect_lower {S : Finset ℤ} (hS : S.Nonempty) {m : ℝ} (hm : 0 < m)
    (hR : ∀ w : ℤ, energyNorm (reflectedSupport S w) / energyNorm S ≤ 24 / m ^ 2)
    {f : S → ℝ} (hf : f ∈ admissibleWeights S)
    (hE : weightedEnergy S (extendWeight S f) = energyNorm S) :
    Real.log m - Real.log 24 / 2 ≤ finiteEntropy (fun x ↦ f x ^ 2) - Real.log (energyNorm S) := by
  let r := Real.sqrt 24 / m
  have hr : 0 ≤ r := div_nonneg (Real.sqrt_nonneg _) hm.le
  have hsq : r ^ 2 = 24 / m ^ 2 := by rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 24)]
  have hc := energyMaximizer_reflected_norm_cost hS hf hE hr (by
    intro w
    rw [hsq, mul_comm]
    exact (div_le_iff₀ (energyNorm_pos hS)).mp (hR w))
  have hlog : Real.log r = Real.log 24 / 2 - Real.log m := by
    rw [Real.log_div (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 24)).ne' hm.ne',
      Real.log_sqrt (by norm_num : (0 : ℝ) ≤ 24)]
  rw [hlog] at hc
  linarith

theorem sparse_reflection_matching_lower {S : Finset ℤ} (hS : S.Nonempty) {m : ℝ} (hm : 0 < m)
    (hN : (S.card : ℝ) ≤ 16 * m * energyNorm S) (hnorm : m ^ 10 / 8 ≤ energyNorm S)
    {f : S → ℝ} (hf : f ∈ admissibleWeights S)
    (hE : weightedEnergy S (extendWeight S f) = energyNorm S) :
    ∃ w ∈ S + S, m ^ 8 / 2048 ≤ energyNorm (reflectedSupport S w) := by
  obtain ⟨w, hw, hret⟩ := exists_reflected_energyNorm_retention hS hf hE
  have he := finiteEntropy_sub_log_norm_le hS hm hN (fun x ↦ f x ^ 2) (fun x ↦ sq_nonneg (f x)) hf.2
  have hlog : Real.log (256 * m ^ 2) = 2 * (Real.log m + Real.log 16) := by
    rw [Real.log_mul (by norm_num : (256 : ℝ) ≠ 0) (pow_pos hm 2).ne', Real.log_pow,
      show (256 : ℝ) = 16 ^ 2 by norm_num, Real.log_pow]
    norm_num
    ring
  have hexp : Real.exp (-2 * (Real.log m + Real.log 16)) = 1 / (256 * m ^ 2) := by
    rw [show -2 * (Real.log m + Real.log 16) = -(2 * (Real.log m + Real.log 16)) by ring,
      ← hlog, Real.exp_neg, Real.exp_log (by positivity), one_div]
  have hpow := Real.exp_le_exp.mpr (show -2 * (Real.log m + Real.log 16) ≤
      -2 * (finiteEntropy (fun x ↦ f x ^ 2) - Real.log (energyNorm S)) by linarith)
  have hprod := mul_le_mul hnorm hpow (Real.exp_pos _).le (energyNorm_nonneg S)
  rw [hexp] at hprod
  have hcoef : (m ^ 10 / 8) * (1 / (256 * m ^ 2)) = m ^ 8 / 2048 := by field_simp; norm_num
  rw [hcoef] at hprod
  exact ⟨w, hw, hprod.trans hret⟩

/-- The complete two-sided defect window and matching reflected norm scale
for every exact optimizer on each constructed sparse support. -/
theorem exists_sparse_reflection_sharp_scale (m : ℕ) (hm : 10 ≤ m) :
    ∃ S : Finset ℤ, S.Nonempty ∧ S ⊆ Finset.Ico 0 ((m ^ 12 : ℕ) : ℤ) ∧
      (∀ w : ℤ, energyNorm (reflectedSupport S w) ≤ 3 * (m : ℝ) ^ 8) ∧
      ∀ f : S → ℝ, f ∈ admissibleWeights S → weightedEnergy S (extendWeight S f) = energyNorm S →
        (Real.log (m : ℝ) - Real.log 24 / 2 ≤ finiteEntropy (fun x ↦ f x ^ 2) - Real.log (energyNorm S)) ∧
        (finiteEntropy (fun x ↦ f x ^ 2) - Real.log (energyNorm S) ≤ Real.log (m : ℝ) + Real.log 16) ∧
        ∃ w ∈ S + S, (m : ℝ) ^ 8 / 2048 ≤ energyNorm (reflectedSupport S w) := by
  obtain ⟨S, hI, hlo, hhi, hnorm, hR⟩ := exists_sparse_reflection_norms m hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hNpos : (0 : ℝ) < S.card := lt_of_lt_of_le (by positivity) hlo
  have hS : S.Nonempty := Finset.card_pos.mp (by exact_mod_cast hNpos)
  have hN : (S.card : ℝ) ≤ 16 * (m : ℝ) * energyNorm S := by
    have h := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 16 * (m : ℝ) by positivity)
    nlinarith only [hhi, h]
  refine ⟨S, hS, hI, fun w ↦ (hR w).1, ?_⟩
  intro f hf hE
  exact ⟨sparse_reflection_defect_lower hS hmR (fun w ↦ (hR w).2) hf hE,
    finiteEntropy_sub_log_norm_le hS hmR hN _ (fun x ↦ sq_nonneg (f x)) hf.2,
    sparse_reflection_matching_lower hS hmR hN hnorm hf hE⟩

end
end Erdos539Geometry
