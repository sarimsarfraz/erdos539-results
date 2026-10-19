/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.RegularizedPartition
import Erdos539.BoundedSliceBounds
import Erdos539.SharpLowerEstimates

namespace Erdos539Geometry
noncomputable section
open scoped Finset Classical
universe u

/-- The sharp anchored-fan lower bound in every positive dimension. The
uniform cardinality cap preserves the logarithmic loss through every slice. -/
theorem sharp_log_fan_lower_bound (d : ℕ) :
    ∀ (ι : Type u) [Fintype ι], Fintype.card ι = d → 0 < d →
      ∀ (N : ℕ) (F : Finset (ι → ℝ)), F.Nonempty → F.card ≤ N →
        (sharpExponent d : ℝ) * Real.log F.card - 8 * (d : ℝ) * Real.log 2 -
          sharpLogLoss d * Real.log (dyadicLevels N) ≤ Real.log (maxFan F) := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro ι inst hdim hd N F hF hFN
    have hn : (0 : ℝ) < F.card := by exact_mod_cast hF.card_pos
    have hnlog : 0 ≤ Real.log F.card := Real.log_nonneg (by exact_mod_cast hF.card_pos)
    have hL : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hlevels : (1 : ℝ) ≤ dyadicLevels N := by
      exact_mod_cast (show 1 ≤ dyadicLevels N by unfold dyadicLevels; omega)
    have hlevelspos : (0 : ℝ) < dyadicLevels N := by linarith
    have hK : 0 ≤ Real.log (dyadicLevels N) := Real.log_nonneg hlevels
    by_cases hd1 : d = 1
    · rw [hd1, sharpExponent_one, one_dimensional_maxFan_eq_card (hdim.trans hd1)]
      norm_num [sharpLogLoss]
      positivity
    have htwo : 2 ≤ 2 ^ d := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) hd
    have hr : ((2 ^ d - 2 : ℕ) : ℝ) = (2 : ℝ) ^ d - 2 := by
      rw [Nat.cast_sub htwo]
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    obtain ⟨S, hSF, hS, hsize, I, J, hcover, hcard, hP, hQ⟩ :=
      exists_regularized_partition hF (hdim ▸ hd) hFN
    rw [hdim] at hsize hcard hP hQ
    have hm : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    have hM : (0 : ℝ) < maxFan F := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxFan hF))
    have hsize' := Real.log_le_log hn
      (show (F.card : ℝ) ≤ (dyadicLevels N : ℝ) ^ (2 ^ d - 2) * S.card by exact_mod_cast hsize)
    rw [Real.log_mul (pow_pos hlevelspos _).ne' hm.ne', Real.log_pow, hr] at hsize'
    have hproj (T : Finset ι)
        (hT : (projection S T).card ≤ 2 ^ (d + 3) * dyadicLevels N ^ (2 ^ d - 2) * maxFan F) :
        Real.log (projection S T).card ≤ ((d : ℝ) + 3) * Real.log 2 +
          ((2 : ℝ) ^ d - 2) * Real.log (dyadicLevels N) + Real.log (maxFan F) := by
      have ht : (0 : ℝ) < (projection S T).card := by exact_mod_cast (hS.image (project T)).card_pos
      have h := Real.log_le_log ht (show ((projection S T).card : ℝ) ≤
          (2 : ℝ) ^ (d + 3) * (dyadicLevels N : ℝ) ^ (2 ^ d - 2) * maxFan F by exact_mod_cast hT)
      rw [Real.log_mul (mul_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _) (pow_pos hlevelspos _)).ne' hM.ne',
        Real.log_mul (pow_pos (by norm_num : (0 : ℝ) < 2) _).ne' (pow_pos hlevelspos _).ne',
        Real.log_pow, Real.log_pow, hr] at h
      norm_num only [Nat.cast_add, Nat.cast_ofNat] at h
      exact h
    have hPl := hproj I hP
    have hQl := hproj J hQ
    have hempty (T : Finset ι) (hfull : ∀ i, i ∈ T)
        (hT : Real.log (projection S T).card ≤ ((d : ℝ) + 3) * Real.log 2 +
          ((2 : ℝ) ^ d - 2) * Real.log (dyadicLevels N) + Real.log (maxFan F)) :
        (sharpExponent d : ℝ) * Real.log F.card - 8 * (d : ℝ) * Real.log 2 -
          sharpLogLoss d * Real.log (dyadicLevels N) ≤ Real.log (maxFan F) := by
      rw [projection_card_eq_card_of_covers S T hfull] at hT
      exact sharp_lower_empty_closes (by exact_mod_cast hd)
        (by exact_mod_cast (sharpExponent_bounds d).2) hnlog hL hsize' hT
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
    have hpLt : I.card < d := by omega
    have hsLt : J.card < d := by omega
    have hIBound (G : Finset (I → ℝ)) (hG : G.Nonempty) (hGN : G.card ≤ N) :
        (sharpExponent I.card : ℝ) * Real.log G.card -
          (8 * (I.card : ℝ) * Real.log 2 + sharpLogLoss I.card * Real.log (dyadicLevels N)) ≤ Real.log (maxFan G) := by
      have h := ih I.card hpLt I (by simp only [Fintype.card_coe]) hp N G hG hGN
      linarith
    have hJBound (G : Finset (J → ℝ)) (hG : G.Nonempty) (hGN : G.card ≤ N) :
        (sharpExponent J.card : ℝ) * Real.log G.card -
          (8 * (J.card : ℝ) * Real.log 2 + sharpLogLoss J.card * Real.log (dyadicLevels N)) ≤ Real.log (maxFan G) := by
      have h := ih J.card hsLt J (by simp only [Fintype.card_coe]) hs N G hG hGN
      linarith
    have ha : (0 : ℝ) ≤ sharpExponent I.card := by exact_mod_cast (sharpExponent_pos I.card).le
    have hb : (0 : ℝ) ≤ sharpExponent J.card := by exact_mod_cast (sharpExponent_pos J.card).le
    have hprune := bounded_one_sided_log_pruning hS ((Finset.card_le_card hSF).trans hFN)
      I J hcover (sharpExponent I.card : ℝ) (sharpExponent J.card : ℝ)
      (8 * (I.card : ℝ) * Real.log 2 + sharpLogLoss I.card * Real.log (dyadicLevels N))
      (8 * (J.card : ℝ) * Real.log 2 + sharpLogLoss J.card * Real.log (dyadicLevels N))
      ha hb hIBound hJBound
    have hMS : (0 : ℝ) < maxFan S := by
      exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 1) (one_le_maxFan hS))
    have hmono := Real.log_le_log hMS (show (maxFan S : ℝ) ≤ maxFan F by exact_mod_cast maxFan_mono hSF)
    have hcard' : (I.card : ℝ) + J.card = d := by exact_mod_cast hcard
    have hsplit : (sharpExponent d : ℝ) ≤
        ((sharpExponent I.card : ℝ) + sharpExponent J.card) /
          (1 + (sharpExponent I.card : ℝ) + sharpExponent J.card) := by
      have h : (sharpExponent (I.card + J.card) : ℝ) ≤
          (combineExponent (sharpExponent I.card) (sharpExponent J.card) : ℝ) := by
        exact_mod_cast sharpExponent_le_split hp hs
      rw [hcard, combineExponent] at h
      push_cast at h
      exact h
    have hloss : sharpLogLoss I.card + sharpLogLoss J.card ≤ 2 * ((2 : ℝ) ^ d - 2) := by
      have h := sharpLogLoss_split hp hs
      rwa [hcard] at h
    apply sharp_lower_split_closes (by exact_mod_cast hd) ha hb hnlog hL hK hloss hsplit hsize' hPl hQl
    have hloss_eq : 8 * (I.card : ℝ) * Real.log 2 + 8 * (J.card : ℝ) * Real.log 2 = 8 * (d : ℝ) * Real.log 2 := by
      calc
        _ = 8 * ((I.card : ℝ) + J.card) * Real.log 2 := by ring
        _ = _ := by rw [hcard']
    linarith

end
end Erdos539Geometry
