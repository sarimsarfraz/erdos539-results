/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SharpRegularityCost
import Erdos539.LogPruning

namespace Erdos539Geometry
noncomputable section

/-- Logarithm of the aggregate lower bound. `H` bounds the parent's
projection-size times maximum-fiber-size, without normalization. -/
def sharpFanLogBound (m : ℕ) (n H P : ℝ) : ℝ :=
  -8 * m * Real.log 2 + sharpRegularityCost m * (Real.log n - Real.log H) +
    sharpExponentReal m * (Real.log n - Real.log P)

theorem sharpFanLogBound_mono {m : ℕ} (hm : 0 < m) {n n' H P : ℝ}
    (hn : 0 < n) (hle : n ≤ n') : sharpFanLogBound m n H P ≤ sharpFanLogBound m n' H P := by
  have hl := Real.log_le_log hn hle
  have ha := mul_le_mul_of_nonneg_left hl (sharpRegularityCost_nonneg hm)
  have hu := mul_le_mul_of_nonneg_left hl (sharpExponentReal_pos hm).le
  dsimp only [sharpFanLogBound]
  linarith

theorem sharpFanLogBound_le_of_small_fiber {m : ℕ} (hm : 0 < m) {n H M P : ℝ}
    (hn : 0 < n) (hnH : n ≤ H) (hnP : n ≤ P) (hM : 1 ≤ M) :
    sharpFanLogBound m n H P ≤ Real.log M := by
  have hL := Real.log_le_log hn hnH
  have hZ := Real.log_le_log hn hnP
  have hcost : 0 ≤ 8 * (m : ℝ) * Real.log 2 := by positivity
  have hreg := mul_nonpos_of_nonneg_of_nonpos (sharpRegularityCost_nonneg hm) (sub_nonpos.mpr hL)
  have hexp := mul_nonpos_of_nonneg_of_nonpos (sharpExponentReal_pos hm).le (sub_nonpos.mpr hZ)
  have hlog := Real.log_nonneg hM
  dsimp only [sharpFanLogBound]
  linarith

theorem sharpFanLogBound_one {n H M P : ℝ}
    (hn : 0 < n) (hP : 0 < P) (hM : 0 < M) (h : n ≤ P * M) :
    sharpFanLogBound 1 n H P ≤ Real.log M := by
  have hl := Real.log_le_log hn h
  rw [Real.log_mul hP.ne' hM.ne'] at hl
  simp only [sharpFanLogBound, Nat.cast_one, sharpRegularityCost_one, zero_mul, sharpExponentReal_one, one_mul]
  linarith [log_two_pos]

theorem sharpFanLogBound_le_of_empty_split {m : ℕ} (hm : 2 ≤ m) {n H M P : ℝ}
    (hn : 0 < n) (hnH : n ≤ H) (hM : 0 < M) (hP : 0 < P) (hPn : P ≤ n)
    (hbal : n * n ≤ ((4 * 2 ^ m : ℕ) : ℝ) * H * M * P) :
    sharpFanLogBound m n H P ≤ Real.log M := by
  have hl := relative_balance_log hn (hn.trans_le hnH) hM hP hn hbal
  have hL : Real.log n - Real.log H ≤ 0 := sub_nonpos.mpr (Real.log_le_log hn hnH)
  have hZ : 0 ≤ Real.log n - Real.log P := sub_nonneg.mpr (Real.log_le_log hP hPn)
  have ha := mul_le_mul_of_nonpos_right (one_le_sharpRegularityCost hm) hL
  have hv := mul_le_mul_of_nonneg_right (sharpExponentReal_le_one (by omega : 0 < m)) hZ
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hc : ((m : ℝ) + 2) * Real.log 2 ≤ 8 * m * Real.log 2 := by
    nlinarith [log_two_pos, mul_nonneg (show (0 : ℝ) ≤ m - 2 by linarith) log_two_pos.le]
  dsimp only [sharpFanLogBound]
  linarith

/-- Quantitative closure of a nonempty split after aggregate pruning. -/
theorem sharpFanLogBound_split {p s : ℕ} (hp : 0 < p) (hs : 0 < s)
    {n H M P P₁ P₂ : ℝ}
    (hn : 0 < n) (hnH : n ≤ H) (hM : 0 < M) (hP : 0 < P) (hPn : P ≤ n)
    (hP₁ : 0 < P₁) (hP₂ : 0 < P₂)
    (hb₁ : n * P₁ ≤ ((4 * 2 ^ (p + s) : ℕ) : ℝ) * H * M * P)
    (hb₂ : n * P₂ ≤ ((4 * 2 ^ (p + s) : ℕ) : ℝ) * H * M * P)
    (hprune : Real.exp (sharpFanLogBound p (n / 2) H P₂) *
      Real.exp (sharpFanLogBound s (n / 2) H P₁) ≤ M) :
    sharpFanLogBound (p + s) n H P ≤ Real.log M := by
  have hH := hn.trans_le hnH
  have hL : Real.log n - Real.log H ≤ 0 := sub_nonpos.mpr (Real.log_le_log hn hnH)
  have hZ : 0 ≤ Real.log n - Real.log P := sub_nonneg.mpr (Real.log_le_log hP hPn)
  let t := sharpExponentReal p + sharpExponentReal s
  have ht : 1 ≤ t := one_le_sharpExponentReal_sum hp hs
  have ht0 : 0 < 1 + t := by linarith
  have hsum : sharpFanLogBound p (n / 2) H P₂ + sharpFanLogBound s (n / 2) H P₁ ≤ Real.log M := by
    apply (Real.le_log_iff_exp_le hM).mpr
    rwa [Real.exp_add]
  have hb₁' := relative_balance_log hn hH hM hP hP₁ hb₁
  have hb₂' := relative_balance_log hn hH hM hP hP₂ hb₂
  have hbp := mul_le_mul_of_nonneg_left hb₂' (sharpExponentReal_pos hp).le
  have hbs := mul_le_mul_of_nonneg_left hb₁' (sharpExponentReal_pos hs).le
  rw [sharpFanLogBound, sharpFanLogBound, Real.log_div hn.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hsum
  have hraw :
      -(8 * ((p + s : ℕ) : ℝ) + sharpRegularityCost p + sharpRegularityCost s +
          (((p + s : ℕ) : ℝ) + 3) * t) * Real.log 2 +
        (sharpRegularityCost p + sharpRegularityCost s + t) * (Real.log n - Real.log H) +
        t * (Real.log n - Real.log P) ≤ (1 + t) * Real.log M := by
    dsimp only [t]
    push_cast at *
    nlinarith
  have hcost := sharp_induction_constant_budget hp hs ht
  have hcost' := mul_le_mul_of_nonneg_right hcost log_two_pos.le
  have hreg : sharpRegularityCost p + sharpRegularityCost s + t ≤ sharpRegularityCost (p + s) * (1 + t) :=
    (div_le_iff₀ ht0).mp (sharpRegularityCost_split hp hs ht)
  have hreg' := mul_le_mul_of_nonpos_right hreg hL
  have hexp : sharpExponentReal (p + s) * (1 + t) ≤ t := by
    apply (le_div_iff₀ ht0).mp
    simpa only [t, add_assoc] using sharpExponentReal_split hp hs
  have hexp' := mul_le_mul_of_nonneg_right hexp hZ
  have hclosed : (1 + t) * sharpFanLogBound (p + s) n H P ≤ (1 + t) * Real.log M := by
    dsimp only [sharpFanLogBound]
    nlinarith
  exact (mul_le_mul_iff_of_pos_left ht0).mp hclosed

end
end Erdos539Geometry
