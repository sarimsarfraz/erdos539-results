/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.BalancedSignPartition
import Erdos539.SmallDimensionEstimates
import Erdos539.FullDifferenceLogPruning
import Erdos539.SmallTwoSided

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
universe u

/-- The sharp full positive-difference bound through dimension fifteen, with the
manuscript's uniform constant 8^(-d), stated logarithmically. -/
theorem small_fifteen_log_bound (d : ℕ) :
    ∀ (ι : Type u) [Fintype ι], Fintype.card ι = d → 0 < d → d ≤ 15 →
      ∀ (F : Finset (ι → ℝ)), F.Nonempty →
        (sharpExponent d : ℝ) * Real.log F.card - 3 * (d : ℝ) * Real.log 2 ≤ Real.log (posDiff F).card := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro ι inst hdim hd0 hd15 F hF
    have hn : (0 : ℝ) < F.card := by exact_mod_cast hF.card_pos
    have hnlog : 0 ≤ Real.log F.card := Real.log_nonneg (by exact_mod_cast hF.card_pos)
    have hL : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    by_cases hd7 : d ≤ 7
    · have hbase := small_two_sided_log_bound d ι hdim hd0 hd7 F hF
      have hM : (0 : ℝ) < maxTwoFan F := by
        exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxTwoRestrictedFan hF ∅))
      have hmono := Real.log_le_log hM (show (maxTwoFan F : ℝ) ≤ (posDiff F).card by exact_mod_cast maxTwoFan_le_card_posDiff F)
      exact hbase.trans hmono
    · obtain ⟨I, J, E, hEF, hE, hsize, hcover, hcard, horder, hP, hQ⟩ := exists_ordered_sign_partition hF
      rw [hdim] at hsize hcard
      have hP' := hP.trans (maxTwoFan_le_card_posDiff F)
      have hQ' := hQ.trans (maxTwoFan_le_card_posDiff F)
      have hm : (0 : ℝ) < E.card := by exact_mod_cast hE.card_pos
      have hsize' := Real.log_le_log hn (show (F.card : ℝ) ≤ (2 : ℝ) ^ d * E.card by exact_mod_cast hsize)
      rw [Real.log_mul (pow_pos (by norm_num : (0 : ℝ) < 2) d).ne' hm.ne', Real.log_pow] at hsize'
      have hPi : (0 : ℝ) < (projection E I).card := by exact_mod_cast (hE.image (project I)).card_pos
      have hPj : (0 : ℝ) < (projection E J).card := by exact_mod_cast (hE.image (project J)).card_pos
      have hPl := Real.log_le_log hPi (show ((projection E I).card : ℝ) ≤ (posDiff F).card by exact_mod_cast hP')
      have hQl := Real.log_le_log hPj (show ((projection E J).card : ℝ) ≤ (posDiff F).card by exact_mod_cast hQ')
      by_cases hI0 : I.card = 0
      · have hIempty : I = ∅ := Finset.card_eq_zero.mp hI0
        have hJfull : ∀ i, i ∈ J := by
          intro i
          rcases hcover i with hi | hi
          · rw [hIempty] at hi
            exact False.elim (Finset.notMem_empty i hi)
          · exact hi
        rw [projection_card_eq_card_of_covers E J hJfull] at hQl
        have hu : (sharpExponent d : ℝ) ≤ 1 := by exact_mod_cast (sharpExponent_bounds d).2
        have huN := mul_le_mul_of_nonneg_right hu hnlog
        have hdL : 0 ≤ (d : ℝ) * Real.log 2 := by positivity
        linarith
      · have hp : 0 < I.card := by omega
        have hq : 0 < J.card := by omega
        have hp7 : I.card ≤ 7 := by omega
        have hJlt : J.card < d := by omega
        have hIBound (G : Finset (I → ℝ)) (hG : G.Nonempty) :
            (sharpExponent I.card : ℝ) * Real.log G.card - 3 * (I.card : ℝ) * Real.log 2 ≤ Real.log (maxTwoFan G) :=
          small_two_sided_log_bound I.card I (by simp only [Fintype.card_coe]) hp hp7 G hG
        have hJBound (G : Finset (J → ℝ)) (hG : G.Nonempty) :
            (sharpExponent J.card : ℝ) * Real.log G.card - 3 * (J.card : ℝ) * Real.log 2 ≤ Real.log (posDiff G).card :=
          ih J.card hJlt J (by simp only [Fintype.card_coe]) hq (by omega) G hG
        have ha : (0 : ℝ) ≤ sharpExponent I.card := by exact_mod_cast (sharpExponent_pos I.card).le
        have hb : (0 : ℝ) ≤ sharpExponent J.card := by exact_mod_cast (sharpExponent_pos J.card).le
        have hprune := full_difference_log_pruning hE I J hcover
          (sharpExponent I.card : ℝ) (sharpExponent J.card : ℝ)
          (3 * (I.card : ℝ) * Real.log 2) (3 * (J.card : ℝ) * Real.log 2) ha hb hIBound hJBound
        have hME : (0 : ℝ) < (posDiff E).card := by
          exact_mod_cast (lt_of_lt_of_le (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxFan hE)) (maxFan_le_card_posDiff E))
        have hmono := Real.log_le_log hME (show ((posDiff E).card : ℝ) ≤ (posDiff F).card by
          exact_mod_cast Finset.card_le_card (posDiff_mono hEF))
        have h4 : Real.log 4 = 2 * Real.log 2 := by
          have h := Real.log_pow (2 : ℝ) 2
          norm_num at h
          exact h
        rw [h4] at hprune
        have hcard' : (I.card : ℝ) + J.card = d := by exact_mod_cast hcard
        have hloss : 3 * (I.card : ℝ) * Real.log 2 + 3 * (J.card : ℝ) * Real.log 2 = 3 * (d : ℝ) * Real.log 2 := by
          calc
            _ = 3 * ((I.card : ℝ) + J.card) * Real.log 2 := by ring
            _ = _ := by rw [hcard']
        have hsplit : (sharpExponent d : ℝ) ≤
            ((sharpExponent I.card : ℝ) + sharpExponent J.card) /
              (1 + (sharpExponent I.card : ℝ) + sharpExponent J.card) := by
          have h : (sharpExponent (I.card + J.card) : ℝ) ≤
              (combineExponent (sharpExponent I.card) (sharpExponent J.card) : ℝ) := by
            exact_mod_cast sharpExponent_le_split hp hq
          rw [hcard, combineExponent] at h
          push_cast at h
          exact h
        have hsplit' : (sharpExponent d : ℝ) ≤
            ((sharpExponent J.card : ℝ) + sharpExponent I.card) /
              (1 + (sharpExponent J.card : ℝ) + sharpExponent I.card) := by
          simpa only [add_comm, add_left_comm, add_assoc] using hsplit
        apply small_dimension_split_closes (by exact_mod_cast hd0) hb ha hnlog hL hsplit' hsize' hQl hPl
        linarith

end
end Erdos539Geometry
