/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CornerSelectorFamily

namespace Erdos539Geometry
noncomputable section
open scoped Classical
local instance densityRealDecidableEq (d : ℕ) : DecidableEq (Option (Fin d) → ℝ) := Classical.decEq _

theorem two_pow_ge_square {d : ℕ} (hd : 4 ≤ d) : d ^ 2 ≤ 2 ^ d := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ d hd ih =>
    rw [pow_succ (2 : ℕ) d]
    nlinarith

theorem selector_fraction_lt_exponential {C : ℝ} (hC : 0 ≤ C) :
    ∃ d : ℕ, 4 ≤ d ∧ (2 : ℝ) / 2 ^ (2 ^ d) < Real.exp (-C * (d + 1)) := by
  have hL : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  obtain ⟨d, hd⟩ := exists_nat_gt (max 4 (4 * C / Real.log 2))
  have hd4 : (4 : ℝ) < d := (le_max_left _ _).trans_lt hd
  have hdN : 4 ≤ d := by exact_mod_cast hd4.le
  have hdp : (0 : ℝ) < d := by linarith
  have hs : 4 * C < (d : ℝ) * Real.log 2 :=
    (div_lt_iff₀ hL).mp ((le_max_right _ _).trans_lt hd)
  have hm := mul_lt_mul_of_pos_right hs hdp
  have hc := mul_nonneg hC (show (0 : ℝ) ≤ d - 1 by linarith)
  have hp : (d : ℝ) ^ 2 ≤ (2 : ℝ) ^ d := by exact_mod_cast two_pow_ge_square hdN
  have hpL := mul_le_mul_of_nonneg_right hp hL.le
  have hq := mul_nonneg (show (0 : ℝ) ≤ (d : ℝ) ^ 2 - 2 by nlinarith) hL.le
  have hlog : Real.log 2 - (2 : ℝ) ^ d * Real.log 2 < -C * (d + 1) := by nlinarith
  refine ⟨d, hdN, ?_⟩
  apply (Real.log_lt_log_iff (by positivity : (0 : ℝ) < 2 / 2 ^ (2 ^ d)) (Real.exp_pos _)).mp
  rw [Real.log_div (by norm_num) (by positivity), Real.log_pow, Real.log_exp]
  norm_num only [Nat.cast_pow, Nat.cast_ofNat]
  exact hlog

/-- No dimension-only exp(-C d) density can be guaranteed by selecting a
box whose two corners belong to the parent. The example still has M=N. -/
theorem no_exponential_corner_selector {C : ℝ} (hC : 0 ≤ C) :
    ∃ d : ℕ, 4 ≤ d ∧
      maxFan (integerRealSet (cornerSelectorFamily d)) = (integerRealSet (cornerSelectorFamily d)).card ∧
      ∀ a ∈ integerRealSet (cornerSelectorFamily d), ∀ b ∈ integerRealSet (cornerSelectorFamily d),
        ((cornerSlice (integerRealSet (cornerSelectorFamily d)) a b).card : ℝ) <
          Real.exp (-C * (d + 1)) * (integerRealSet (cornerSelectorFamily d)).card := by
  obtain ⟨d, hd, hfrac⟩ := selector_fraction_lt_exponential hC
  refine ⟨d, hd, ?_, ?_⟩
  · rw [cornerSelectorFamily_maxFan, cornerSelectorFamily_real_card]
  · intro a ha b hb
    have hcard : (cornerSlice (integerRealSet (cornerSelectorFamily d)) a b).card ≤ 2 := by
      rw [cornerSelectorFamily_boxes d ha hb]
      by_cases he : a = b
      · simp [he]
      · rw [Finset.card_pair he]
    have hc : ((cornerSlice (integerRealSet (cornerSelectorFamily d)) a b).card : ℝ) ≤ 2 := by exact_mod_cast hcard
    have hh := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ (2 ^ d))).mp hfrac
    rw [cornerSelectorFamily_real_card]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    exact hc.trans_lt hh

end
end Erdos539Geometry
