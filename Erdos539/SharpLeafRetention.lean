/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SharpSeparatedHierarchy
import Erdos539.EnergyNormLower

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

namespace SeparatedHierarchy
variable {S : Finset G} {L : Finset (Finset G)}

/-- Sharp norm retention, paid once from the original root deficiency. -/
theorem exists_leaf_sharp_norm_retention (h : SeparatedHierarchy S L) :
    ∃ T ∈ L, energyNorm S * Real.exp (-sharpRetentionBeta * Real.log ((S.card : ℝ) / energyNorm S)) ≤
      energyNorm T := by
  obtain ⟨T, hT, hlog⟩ := h.exists_leaf_sharp_log_retention
  have hS := h.root_nonempty
  have hTne := (h.leaf_nonempty_subset T hT).1
  have hN : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hR := energyNorm_pos hS
  have hRT := energyNorm_pos hTne
  have hdef := Real.log_le_log hRT (energyNorm_le_card T)
  have hm := mul_le_mul_of_nonneg_left hdef sharpRetentionBeta_pos.le
  refine ⟨T, hT, ?_⟩
  apply (Real.log_le_log_iff (mul_pos hR (Real.exp_pos _)) hRT).mp
  rw [Real.log_mul hR.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_div hN.ne' hR.ne']
  nlinarith

/-- The exact sharp doubling-retention exponent log(2)/log(4/3), for a
literal nonempty leaf of any finite separated hierarchy. -/
theorem exists_leaf_sharp_norm_of_difference_doubling (h : SeparatedHierarchy S L)
    {K : ℝ} (hK : 0 < K) (hD : ((S - S).card : ℝ) ≤ K * S.card) :
    ∃ T ∈ L, T.Nonempty ∧ T ⊆ S ∧
      (S.card : ℝ) / K ^ (Real.log 2 / Real.log (4 / 3 : ℝ)) ≤ energyNorm T := by
  obtain ⟨T, hT, hlog⟩ := h.exists_leaf_sharp_log_retention
  have hS := h.root_nonempty
  obtain ⟨hTne, hTS⟩ := h.leaf_nonempty_subset T hT
  have hN : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hR := energyNorm_pos hS
  have hRT := energyNorm_pos hTne
  have hdef := Real.log_le_log hRT (energyNorm_le_card T)
  have hm := mul_le_mul_of_nonneg_left hdef sharpRetentionBeta_pos.le
  have hroot := Real.log_le_log (div_pos hN hK) (energyNorm_ge_of_difference_doubling hS hK hD)
  rw [Real.log_div hN.ne' hK.ne'] at hroot
  have hmroot := mul_le_mul_of_nonneg_left hroot (show 0 ≤ sharpRetentionBeta + 1 by linarith [sharpRetentionBeta_pos])
  refine ⟨T, hT, hTne, hTS, ?_⟩
  apply (Real.log_le_log_iff (div_pos hN (Real.rpow_pos_of_pos hK _)) hRT).mp
  rw [Real.log_div hN.ne' (Real.rpow_pos_of_pos hK _).ne', Real.log_rpow hK,
    ← sharpRetentionTau_eq_log_ratio, sharpRetentionTau_eq_beta_add_one]
  nlinarith

end SeparatedHierarchy
end
end Erdos539Geometry
