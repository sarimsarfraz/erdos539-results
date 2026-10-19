/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SeparatedHierarchy
import Erdos539.EnergyNormLower

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

namespace SeparatedHierarchy
variable {S : Finset G} {L : Finset (Finset G)}

/-- A leaf retains the exact rational power density relative to its size. -/
theorem exists_leaf_power_density (h : SeparatedHierarchy S L) :
    ∃ T ∈ L, energyNorm S ^ (5 / 3 : ℝ) * T.card ≤
      (S.card : ℝ) * energyNorm T ^ (5 / 3 : ℝ) := by
  have hcard : ∑ T ∈ L, (T.card : ℝ) = S.card := by exact_mod_cast h.sum_leaf_card
  have hm := mul_le_mul_of_nonneg_left h.norm_power_le_sum_leaves (Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)
  have hsum : (∑ T ∈ L, energyNorm S ^ (5 / 3 : ℝ) * T.card) ≤
      ∑ T ∈ L, (S.card : ℝ) * energyNorm T ^ (5 / 3 : ℝ) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum, hcard]
    nlinarith only [hm]
  exact Finset.exists_le_of_sum_le h.leaves_nonempty hsum

/-- The entire hierarchy pays once from the drop in size/norm deficiency,
with the exact rational coefficient beta = 3/2. -/
theorem exists_leaf_log_retention (h : SeparatedHierarchy S L) :
    ∃ T ∈ L, Real.log (energyNorm S) - Real.log (energyNorm T) ≤
      (3 / 2 : ℝ) * ((Real.log S.card - Real.log (energyNorm S)) -
        (Real.log T.card - Real.log (energyNorm T))) := by
  obtain ⟨T, hT, hdensity⟩ := h.exists_leaf_power_density
  have hSne := h.root_nonempty
  have hTne := (h.leaf_nonempty_subset T hT).1
  have hN : (0 : ℝ) < S.card := by exact_mod_cast hSne.card_pos
  have hNT : (0 : ℝ) < T.card := by exact_mod_cast hTne.card_pos
  have hR := energyNorm_pos hSne
  have hRT := energyNorm_pos hTne
  have hl := Real.log_le_log (mul_pos (Real.rpow_pos_of_pos hR _) hNT) hdensity
  rw [Real.log_mul (Real.rpow_pos_of_pos hR _).ne' hNT.ne', Real.log_rpow hR,
    Real.log_mul hN.ne' (Real.rpow_pos_of_pos hRT _).ne', Real.log_rpow hRT] at hl
  refine ⟨T, hT, ?_⟩
  linarith

/-- Actual norm retention, independent of the depth and branching pattern. -/
theorem exists_leaf_norm_retention (h : SeparatedHierarchy S L) :
    ∃ T ∈ L, energyNorm S * Real.exp (-(3 / 2 : ℝ) * Real.log ((S.card : ℝ) / energyNorm S)) ≤
      energyNorm T := by
  obtain ⟨T, hT, hlog⟩ := h.exists_leaf_log_retention
  have hS := h.root_nonempty
  have hTne := (h.leaf_nonempty_subset T hT).1
  have hN : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hR := energyNorm_pos hS
  have hRT := energyNorm_pos hTne
  have hdef := Real.log_le_log hRT (energyNorm_le_card T)
  refine ⟨T, hT, ?_⟩
  apply (Real.log_le_log_iff (mul_pos hR (Real.exp_pos _)) hRT).mp
  rw [Real.log_mul hR.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_div hN.ne' hR.ne']
  linarith

/-- The rational leaf-retention theorem N/K^(5/2), for any finite
separated hierarchy and the original root's ordinary difference doubling. -/
theorem exists_leaf_norm_of_difference_doubling (h : SeparatedHierarchy S L)
    {K : ℝ} (hK : 0 < K) (hD : ((S - S).card : ℝ) ≤ K * S.card) :
    ∃ T ∈ L, T.Nonempty ∧ T ⊆ S ∧
      (S.card : ℝ) / K ^ (5 / 2 : ℝ) ≤ energyNorm T := by
  obtain ⟨T, hT, hlog⟩ := h.exists_leaf_log_retention
  have hS := h.root_nonempty
  obtain ⟨hTne, hTS⟩ := h.leaf_nonempty_subset T hT
  have hN : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hR := energyNorm_pos hS
  have hRT := energyNorm_pos hTne
  have hdef := Real.log_le_log hRT (energyNorm_le_card T)
  have hroot := Real.log_le_log (div_pos hN hK) (energyNorm_ge_of_difference_doubling hS hK hD)
  rw [Real.log_div hN.ne' hK.ne'] at hroot
  refine ⟨T, hT, hTne, hTS, ?_⟩
  apply (Real.log_le_log_iff (div_pos hN (Real.rpow_pos_of_pos hK _)) hRT).mp
  rw [Real.log_div hN.ne' (Real.rpow_pos_of_pos hK _).ne', Real.log_rpow hK]
  linarith

end SeparatedHierarchy
end
end Erdos539Geometry
