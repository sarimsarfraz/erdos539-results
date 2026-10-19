/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SharpSeparatedNorm
import Erdos539.SeparatedHierarchy

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]
local instance sharpSeparatedHierarchyFinDecidableEq (n : ℕ) : DecidableEq (Fin n) := Classical.decEq _

namespace SeparatedHierarchy
variable {S : Finset G} {L : Finset (Finset G)}

/-- The sharp norm power aggregates through the entire actual hierarchy,
without dependence on depth, branch count, or equality of leaf sizes. -/
theorem sharp_norm_power_le_sum_leaves (h : SeparatedHierarchy S L) :
    energyNorm S ^ sharpSeparatedExponent ≤ ∑ T ∈ L, energyNorm T ^ sharpSeparatedExponent := by
  induction h with
  | leaf S _ => simp
  | split S _ n label L hsep children ih =>
    rw [Finset.sum_biUnion (component_leaves_disjoint S label L children)]
    exact (energyNorm_separated_sharp hsep).trans (Finset.sum_le_sum (fun i _ ↦ ih i))

theorem exists_leaf_sharp_power_density (h : SeparatedHierarchy S L) :
    ∃ T ∈ L, energyNorm S ^ sharpSeparatedExponent * T.card ≤
      (S.card : ℝ) * energyNorm T ^ sharpSeparatedExponent := by
  have hcard : ∑ T ∈ L, (T.card : ℝ) = S.card := by exact_mod_cast h.sum_leaf_card
  have hm := mul_le_mul_of_nonneg_left h.sharp_norm_power_le_sum_leaves
    (Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)
  have hsum : (∑ T ∈ L, energyNorm S ^ sharpSeparatedExponent * T.card) ≤
      ∑ T ∈ L, (S.card : ℝ) * energyNorm T ^ sharpSeparatedExponent := by
    rw [← Finset.mul_sum, ← Finset.mul_sum, hcard]
    nlinarith only [hm]
  exact Finset.exists_le_of_sum_le h.leaves_nonempty hsum

/-- Exact sharp deficiency-drop retention on an actual leaf. -/
theorem exists_leaf_sharp_log_retention (h : SeparatedHierarchy S L) :
    ∃ T ∈ L, Real.log (energyNorm S) - Real.log (energyNorm T) ≤
      sharpRetentionBeta * ((Real.log S.card - Real.log (energyNorm S)) -
        (Real.log T.card - Real.log (energyNorm T))) := by
  obtain ⟨T, hT, hdensity⟩ := h.exists_leaf_sharp_power_density
  have hSne := h.root_nonempty
  have hTne := (h.leaf_nonempty_subset T hT).1
  have hN : (0 : ℝ) < S.card := by exact_mod_cast hSne.card_pos
  have hNT : (0 : ℝ) < T.card := by exact_mod_cast hTne.card_pos
  have hR := energyNorm_pos hSne
  have hRT := energyNorm_pos hTne
  have hl := Real.log_le_log (mul_pos (Real.rpow_pos_of_pos hR _) hNT) hdensity
  rw [Real.log_mul (Real.rpow_pos_of_pos hR _).ne' hNT.ne', Real.log_rpow hR,
    Real.log_mul hN.ne' (Real.rpow_pos_of_pos hRT _).ne', Real.log_rpow hRT] at hl
  have hm := mul_le_mul_of_nonneg_left hl sharpRetentionBeta_pos.le
  have he : sharpRetentionBeta * sharpSeparatedExponent = sharpRetentionBeta + 1 := by
    nlinarith [sharpRetentionBeta_mul_exponent_sub_one]
  have heS := congrArg (fun x : ℝ ↦ x * Real.log (energyNorm S)) he
  have heT := congrArg (fun x : ℝ ↦ x * Real.log (energyNorm T)) he
  refine ⟨T, hT, ?_⟩
  nlinarith

end SeparatedHierarchy
end
end Erdos539Geometry
