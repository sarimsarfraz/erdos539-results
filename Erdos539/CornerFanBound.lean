/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CornerProjections
import Erdos539.CornerEstimates

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
universe u

/-- Sharp constant-factor forward-fan bound in every positive dimension.
The large two-corner slice removes the cardinality-dependent logarithmic loss. -/
theorem corner_log_fan_bound (d : ℕ) :
    ∀ (ι : Type u) [Fintype ι], Fintype.card ι = d → 0 < d →
      ∀ (F : Finset (ι → ℝ)), F.Nonempty →
        (sharpExponent d : ℝ) * Real.log F.card - cornerFanLoss d * Real.log 2 ≤
          Real.log (maxFan F) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro ι inst hdim hd F hF
    have hn : (0 : ℝ) < F.card := by exact_mod_cast hF.card_pos
    have hnlog : 0 ≤ Real.log F.card := Real.log_nonneg (by exact_mod_cast hF.card_pos)
    have hL : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    by_cases hd3 : d ≤ 3
    · have hbase := one_sided_small_log_bound (by omega : 0 < Fintype.card ι)
        (by omega : Fintype.card ι ≤ 3) hF
      rw [hdim] at hbase
      have hcost := mul_le_mul_of_nonneg_right (corner_small_loss_budget hd hd3) hL
      linarith
    have hbudget := corner_selection_loss_budget (by omega : 4 ≤ d)
    obtain ⟨E, hEF, hE, hsize, I, J, hcover, hcard, hP, hQ⟩ := exists_corner_partition hF (hdim ▸ hd)
    rw [hdim] at hsize hcard
    have hm : (0 : ℝ) < E.card := by exact_mod_cast hE.card_pos
    have hM : (0 : ℝ) < maxFan F := by exact_mod_cast
      (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxFan hF))
    have hsize' := Real.log_le_log hn
      (show (F.card : ℝ) ≤ (2 : ℝ) ^ (3 * 2 ^ (d - 1) + 5) * E.card by exact_mod_cast hsize)
    rw [Real.log_mul (pow_pos (by norm_num : (0 : ℝ) < 2) _).ne' hm.ne', Real.log_pow] at hsize'
    have hPl := Real.log_le_log (show (0 : ℝ) < (projection E I).card by exact_mod_cast (hE.image (project I)).card_pos)
      (show ((projection E I).card : ℝ) ≤ maxFan F by exact_mod_cast hP)
    have hQl := Real.log_le_log (show (0 : ℝ) < (projection E J).card by exact_mod_cast (hE.image (project J)).card_pos)
      (show ((projection E J).card : ℝ) ≤ maxFan F by exact_mod_cast hQ)
    have hempty (T : Finset ι) (hfull : ∀ i, i ∈ T)
        (hproj : Real.log (projection E T).card ≤ Real.log (maxFan F)) :
        (sharpExponent d : ℝ) * Real.log F.card - cornerFanLoss d * Real.log 2 ≤ Real.log (maxFan F) := by
      rw [projection_card_eq_card_of_covers E T hfull] at hproj
      have hu : (sharpExponent d : ℝ) ≤ 1 := by exact_mod_cast (sharpExponent_bounds d).2
      have hu' := mul_le_mul_of_nonneg_right hu hnlog
      have hcost := mul_le_mul_of_nonneg_right (show ((3 * 2 ^ (d - 1) + 5 : ℕ) : ℝ) ≤ cornerFanLoss d by linarith) hL
      linarith
    by_cases hpzero : I.card = 0
    · apply hempty J _ hQl
      intro i
      rcases hcover i with hi | hi
      · rw [Finset.card_eq_zero.mp hpzero] at hi
        exact False.elim (Finset.notMem_empty i hi)
      · exact hi
    by_cases hszero : J.card = 0
    · apply hempty I _ hPl
      intro i
      rcases hcover i with hi | hi
      · exact hi
      · rw [Finset.card_eq_zero.mp hszero] at hi
        exact False.elim (Finset.notMem_empty i hi)
    have hp : 0 < I.card := Nat.pos_of_ne_zero hpzero
    have hs : 0 < J.card := Nat.pos_of_ne_zero hszero
    have hIBound (G : Finset (I → ℝ)) (hG : G.Nonempty) :
        (sharpExponent I.card : ℝ) * Real.log G.card - cornerFanLoss I.card * Real.log 2 ≤ Real.log (maxFan G) :=
      ih I.card (by omega) I (by simp only [Fintype.card_coe]) hp G hG
    have hJBound (G : Finset (J → ℝ)) (hG : G.Nonempty) :
        (sharpExponent J.card : ℝ) * Real.log G.card - cornerFanLoss J.card * Real.log 2 ≤ Real.log (maxFan G) :=
      ih J.card (by omega) J (by simp only [Fintype.card_coe]) hs G hG
    have ha : (0 : ℝ) ≤ sharpExponent I.card := by exact_mod_cast (sharpExponent_pos I.card).le
    have hb : (0 : ℝ) ≤ sharpExponent J.card := by exact_mod_cast (sharpExponent_pos J.card).le
    have hprune := one_sided_log_pruning hE I J hcover (sharpExponent I.card : ℝ) (sharpExponent J.card : ℝ)
      (cornerFanLoss I.card * Real.log 2) (cornerFanLoss J.card * Real.log 2) ha hb hIBound hJBound
    have hMS : (0 : ℝ) < maxFan E := by exact_mod_cast
      (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxFan hE))
    have hmono := Real.log_le_log hMS (show (maxFan E : ℝ) ≤ maxFan F by exact_mod_cast maxFan_mono hEF)
    have hsplit : (sharpExponent d : ℝ) ≤
        ((sharpExponent I.card : ℝ) + sharpExponent J.card) / (1 + (sharpExponent I.card : ℝ) + sharpExponent J.card) := by
      have h : (sharpExponent (I.card + J.card) : ℝ) ≤
          (combineExponent (sharpExponent I.card) (sharpExponent J.card) : ℝ) := by exact_mod_cast sharpExponent_le_split hp hs
      rw [hcard, combineExponent] at h
      push_cast at h
      exact h
    have hcost : cornerFanLoss I.card + cornerFanLoss J.card ≤ cornerFanLoss d := by
      simpa only [hcard] using cornerFanLoss_split hp hs
    exact corner_split_closes ha hb hnlog hL hsplit hcost hbudget hsize' hPl hQl (hprune.trans hmono)

/-- The exact requested fan constant 2^(-2^(d+1)), with no logarithmic loss. -/
theorem all_dimension_fan_lower_bound {ι : Type*} [Fintype ι] (hd : 0 < Fintype.card ι)
    {F : Finset (ι → ℝ)} (hF : F.Nonempty) :
    (F.card : ℝ) ^ (sharpExponent (Fintype.card ι) : ℝ) /
      (2 : ℝ) ^ (2 ^ (Fintype.card ι + 1) : ℕ) ≤ maxFan F := by
  have hn : (0 : ℝ) < F.card := by exact_mod_cast hF.card_pos
  have hM : (0 : ℝ) < maxFan F := by exact_mod_cast
    (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxFan hF))
  have hpow : 0 < (F.card : ℝ) ^ (sharpExponent (Fintype.card ι) : ℝ) := Real.rpow_pos_of_pos hn _
  have hden : (0 : ℝ) < (2 : ℝ) ^ (2 ^ (Fintype.card ι + 1) : ℕ) := by positivity
  apply (Real.log_le_log_iff (div_pos hpow hden) hM).mp
  rw [Real.log_div hpow.ne' hden.ne', Real.log_rpow hn, Real.log_pow]
  simpa only [cornerFanLoss, Nat.cast_pow, Nat.cast_ofNat] using
    corner_log_fan_bound (Fintype.card ι) ι rfl hd F hF

theorem all_dimension_posDiff_lower_bound {ι : Type*} [Fintype ι] (hd : 0 < Fintype.card ι)
    {F : Finset (ι → ℝ)} (hF : F.Nonempty) :
    (F.card : ℝ) ^ (sharpExponent (Fintype.card ι) : ℝ) /
      (2 : ℝ) ^ (2 ^ (Fintype.card ι + 1) : ℕ) ≤ (posDiff F).card :=
  (all_dimension_fan_lower_bound hd hF).trans (by exact_mod_cast maxFan_le_card_posDiff F)

end
end Erdos539Geometry
