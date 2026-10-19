/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.StationarySumDifference
import Erdos539.StationaryEntropyReference
import Erdos539.ReferenceUniformRoot

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [AddCommGroup G] [DecidableEq G] in
theorem uniformReference_entropy {S : Finset G} (hS : S.Nonempty) :
    finiteEntropy (uniformReference S) = Real.log (S.card : ℝ) := by
  have h := finiteEntropy_normalize (fun _ : S ↦ (1 : ℝ))
    (show 0 < ∑ _ : S, (1 : ℝ) by simpa using hS)
  change finiteEntropy (fun _ : S ↦ 1 / (S.card : ℝ)) = _
  simpa using h

theorem stationaryEntropyDefect_uniform_lower {S : Finset G} (hS : S.Nonempty) :
    Real.log ((S.card : ℝ) ^ 3 / countingEnergy S) ≤ stationaryEntropyDefect S (uniformReference S) := by
  have h := referenceDeficit_le_stationaryEntropyDefect hS
    (fun x ↦ (uniformReference_pos hS x).le) (uniformReference_sum hS) (uniformReference_pos hS)
  rw [referenceDeficit_uniform hS] at h
  simpa only [finiteRelEntropy, sub_self, mul_zero, Finset.sum_const_zero, add_zero] using h

theorem stationaryEntropyDefect_uniform_upper {S : Finset G} (hS : S.Nonempty) :
    stationaryEntropyDefect S (uniformReference S) ≤ Real.log ((S - S).card / (S.card : ℝ)) := by
  obtain ⟨x, hx⟩ := hS
  have hS' : S.Nonempty := ⟨x, hx⟩
  letI : Nonempty (S - S) := ⟨⟨0, Finset.mem_sub.mpr ⟨x, hx, x, hx, sub_self x⟩⟩⟩
  have hν := fun y ↦ (uniformReference_pos hS' y).le
  have hs := uniformReference_sum hS'
  have hp : ∀ z, 0 ≤ independentPairWeight (uniformReference S) z := fun z ↦ mul_nonneg (hν z.1) (hν z.2)
  have hps : ∑ z, independentPairWeight (uniformReference S) z = 1 := by
    simp only [independentPairWeight, Fintype.sum_prod_type, ← Finset.mul_sum, hs, mul_one]
  have hbound := finiteEntropy_le_log_card
    (finitePush (independentPairWeight (uniformReference S)) (independentDifferenceLabel S))
    (finitePush_nonneg _ _ hp) (by rw [finitePush_sum, hps])
  have h := stationaryEntropyDefect_le_difference_growth S (uniformReference S) hν hs
  rw [uniformReference_entropy hS'] at h
  have hN : (0 : ℝ) < S.card := by exact_mod_cast hS'.card_pos
  have hr : (0 : ℝ) < (S - S).card := by
    exact_mod_cast (show (S - S).Nonempty from ⟨0, Finset.mem_sub.mpr ⟨x, hx, x, hx, sub_self x⟩⟩).card_pos
  rw [Real.log_div hr.ne' hN.ne']
  simpa only [Fintype.card_coe] using h.trans (sub_le_sub_right hbound (Real.log (S.card : ℝ)))

/-- The uniform stationary defect lies between ordinary counting-energy
defect and the logarithm of ordinary difference doubling. -/
theorem stationaryEntropyDefect_uniform_sandwich {S : Finset G} (hS : S.Nonempty) :
    Real.log ((S.card : ℝ) ^ 3 / countingEnergy S) ≤ stationaryEntropyDefect S (uniformReference S) ∧
      stationaryEntropyDefect S (uniformReference S) ≤ Real.log ((S - S).card / (S.card : ℝ)) :=
  ⟨stationaryEntropyDefect_uniform_lower hS, stationaryEntropyDefect_uniform_upper hS⟩

end
end Erdos539Geometry
