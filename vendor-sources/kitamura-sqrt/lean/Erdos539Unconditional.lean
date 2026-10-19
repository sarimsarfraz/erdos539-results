/-
Copyright 2026 Kenta Kitamura
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539FixedDimension
import Erdos539Dimension
import Erdos539Asymptotic

/-! Unconditional assembly of the negative square-root answers for Erdős 539. -/

namespace Erdos539Unconditional

noncomputable section
open Filter
open scoped Asymptotics Topology
open Erdos539Geometry Erdos539Dimension Erdos539Asymptotic

/-- A positive integer set has bounded size if its squared cofactor count is
bounded by a fixed multiple of its size. There are no unproved inputs. -/
theorem positive_bounded_doubling : PositiveBoundedDoubling := by
  intro K hK
  let D : ℕ := ⌈(40 / Real.log 2) * Real.log K⌉₊
  obtain ⟨c,a,hc,ha,ha1,hgrowth⟩ := exists_growth D
  have hη : 0 < K ^ (-17 : ℝ) := Real.rpow_pos_of_pos hK _
  obtain ⟨N,hN⟩ := exists_cardinal_bound_of_growth hc hη hK ha
  refine ⟨N,?_⟩
  intro A hA hdoubling
  by_cases hAne : A.Nonempty
  · let F := integerExponentSet A
    have hFcard : F.card = A.card := integerExponentSet_card hA
    have hF : F.Nonempty := Finset.card_pos.mp (by rw [hFcard]; exact hAne.card_pos)
    have hDiff : ((integerDifferences F).card : ℝ) ≤ K * F.card := by
      have h := integerDifferences_integerExponentSet_card_le hA
      have h' : ((integerDifferences F).card : ℝ) ≤ ((cofactors A).card : ℝ) ^ 2 := by
        exact_mod_cast h
      simpa only [hFcard] using h'.trans hdoubling
    obtain ⟨m,hm,B,hB,hBcard,hBdiff⟩ := exists_small_dimension_subset F hF K hDiff
    have hBL : K ^ (-17 : ℝ) * A.card ≤ B.card := by
      simpa only [hFcard] using hBcard
    have hBG : c * (B.card : ℝ) ^ a ≤ (posDiff B).card :=
      hgrowth (Fin m) (by simpa only [Fintype.card_fin] using hm) B hB
    have hBQ : ((posDiff B).card : ℝ) ≤ (cofactors A).card := by
      have h := integerPositiveDifferences_integerExponentSet_card hA
      exact_mod_cast (h ▸ hBdiff)
    have hpower : (K ^ (-17 : ℝ) * A.card) ^ a ≤ (B.card : ℝ) ^ a :=
      Real.rpow_le_rpow (by positivity) hBL (by linarith)
    have hfinal : c * (K ^ (-17 : ℝ) * A.card) ^ a ≤ (cofactors A).card :=
      (mul_le_mul_of_nonneg_left hpower hc.le).trans (hBG.trans hBQ)
    exact hN A.card (cofactors A).card (by positivity) hfinal hdoubling
  · have hzero : A.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hAne)
    omega

/-- The cofactor threshold grows faster than every fixed multiple of `sqrt n`. -/
theorem threshold_div_sqrt_tendsto :
    Tendsto (fun n : ℕ ↦ (threshold n : ℝ) / Real.sqrt (n : ℝ)) atTop atTop :=
  Erdos539Asymptotic.threshold_div_sqrt_tendsto positive_bounded_doubling

/-- The Big-O square-root question has a negative answer, without assumptions. -/
theorem not_isBigO_sqrt :
    ¬ ((fun n : ℕ ↦ (threshold n : ℝ)) =O[atTop] fun n ↦ Real.sqrt (n : ℝ)) :=
  not_isBigO_of_positive_bounded positive_bounded_doubling

/-- The Theta square-root question has a negative answer, without assumptions. -/
theorem not_isTheta_sqrt :
    ¬ ((fun n : ℕ ↦ (threshold n : ℝ)) =Θ[atTop] fun n ↦ Real.sqrt (n : ℝ)) :=
  not_isTheta_of_positive_bounded positive_bounded_doubling

end
end Erdos539Unconditional

#print axioms Erdos539Unconditional.positive_bounded_doubling
#print axioms Erdos539Unconditional.threshold_div_sqrt_tendsto
#print axioms Erdos539Unconditional.not_isBigO_sqrt
#print axioms Erdos539Unconditional.not_isTheta_sqrt
