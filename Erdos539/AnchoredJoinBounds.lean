/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteOrderRank
import Erdos539.AllDimensionBounds
import Erdos539.GluingLayers

namespace Erdos539Geometry
noncomputable section
open scoped Classical

/-- The sharp exponent holds for arbitrary finite subsets of products of
linearly ordered sets, without any closure under joins. -/
theorem all_dimension_anchoredJoin_lower_bound {ι : Type*} [Fintype ι]
    {α : ι → Type*} [∀ i, LinearOrder (α i)] (hd : 0 < Fintype.card ι)
    {S : Finset (∀ i, α i)} (hS : S.Nonempty) :
    (S.card : ℝ) ^ (sharpExponent (Fintype.card ι) : ℝ) /
      (2 : ℝ) ^ (2 ^ (Fintype.card ι + 1) : ℕ) ≤ maxJoinFan S := by
  letI : DecidableEq (ι → ℝ) := Classical.decEq _
  have h := all_dimension_fan_lower_bound hd (hS.image (coordinateRanks S))
  rw [coordinateRanks_card, ← maxJoinFan_real, maxJoinFan_coordinateRanks] at h
  exact h

/-- Matching upper examples exist at every positive cardinality. Thus the
order-only lower bound has the same sharp exponent u_d. -/
theorem exists_anchoredJoin_upper_construction {d : ℕ} (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∃ S : Finset (Fin d → ℝ),
      S.card = n ∧ (maxJoinFan S : ℝ) ≤ C * (n : ℝ) ^ (sharpExponent d : ℝ) := by
  obtain ⟨C, hC, hf⟩ := exists_sharp_upper_construction hd
  refine ⟨C, hC, ?_⟩
  intro n hn
  obtain ⟨A, hA, hbound⟩ := hf n hn
  refine ⟨integerRealSet A, ?_, ?_⟩
  · simpa only [integerRealSet, integerToReal_image_card] using hA
  · rw [maxJoinFan_real]
    have hm : (maxFan (integerRealSet A) : ℝ) ≤ (integerPositiveDifferences A).card := by
      exact_mod_cast (maxFan_le_card_posDiff (integerRealSet A)).trans_eq (posDiff_integerToReal_card A)
    exact hm.trans hbound

end
end Erdos539Geometry
