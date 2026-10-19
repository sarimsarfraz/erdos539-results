/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.InductionEstimates

namespace Erdos539Geometry
noncomputable section

/-- Logarithm of the aggregate lower bound. `H` bounds the parent's
projection-size times maximum-fiber-size, without normalization. -/
def fanLogBound (m : ℕ) (n H P : ℝ) : ℝ :=
  -8 * m * Real.log 2 + regularityCost m * (Real.log n - Real.log H) +
    uniformExponent m * (Real.log n - Real.log P)

theorem fanLogBound_mono {m : ℕ} (hm : 0 < m) {n n' H P : ℝ}
    (hn : 0 < n) (hle : n ≤ n') : fanLogBound m n H P ≤ fanLogBound m n' H P := by
  have hl := Real.log_le_log hn hle
  have ha := mul_le_mul_of_nonneg_left hl (regularityCost_nonneg hm)
  have hu := mul_le_mul_of_nonneg_left hl (uniformExponent_pos hm).le
  dsimp only [fanLogBound]
  linarith

theorem log_balance_constant (m : ℕ) :
    Real.log ((4 * 2 ^ m : ℕ) : ℝ) = ((m : ℝ) + 2) * Real.log 2 := by
  push_cast
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (by positivity : (2 : ℝ) ^ m ≠ 0),
    Real.log_pow]
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  rw [h4]
  ring

theorem relative_balance_log {m : ℕ} {n H M P Q : ℝ}
    (hn : 0 < n) (hH : 0 < H) (hM : 0 < M) (hP : 0 < P) (hQ : 0 < Q)
    (hbal : n * Q ≤ ((4 * 2 ^ m : ℕ) : ℝ) * H * M * P) :
    (Real.log n - Real.log P) + (Real.log n - Real.log H) - Real.log M -
      ((m : ℝ) + 2) * Real.log 2 ≤ Real.log n - Real.log Q := by
  have hc : (0 : ℝ) < (4 * 2 ^ m : ℕ) := by positivity
  have h := Real.log_le_log (mul_pos hn hQ) hbal
  rw [Real.log_mul hn.ne' hQ.ne',
    Real.log_mul (mul_pos (mul_pos hc hH) hM).ne' hP.ne',
    Real.log_mul (mul_pos hc hH).ne' hM.ne', Real.log_mul hc.ne' hH.ne',
    log_balance_constant] at h
  linarith

theorem fanLogBound_le_of_small_fiber {m : ℕ} (hm : 0 < m) {n H M P : ℝ}
    (hn : 0 < n) (hnH : n ≤ H) (hnP : n ≤ P) (hM : 1 ≤ M) :
    fanLogBound m n H P ≤ Real.log M := by
  have hL := Real.log_le_log hn hnH
  have hZ := Real.log_le_log hn hnP
  have hcost : 0 ≤ 8 * (m : ℝ) * Real.log 2 := by positivity
  have hreg := mul_nonpos_of_nonneg_of_nonpos (regularityCost_nonneg hm) (sub_nonpos.mpr hL)
  have hexp := mul_nonpos_of_nonneg_of_nonpos (uniformExponent_pos hm).le (sub_nonpos.mpr hZ)
  have hlog := Real.log_nonneg hM
  dsimp only [fanLogBound]
  linarith

theorem fanLogBound_one {n H M P : ℝ}
    (hn : 0 < n) (hP : 0 < P) (hM : 0 < M) (h : n ≤ P * M) :
    fanLogBound 1 n H P ≤ Real.log M := by
  have hl := Real.log_le_log hn h
  rw [Real.log_mul hP.ne' hM.ne'] at hl
  simp only [fanLogBound, Nat.cast_one, regularityCost_one, zero_mul, uniformExponent_one, one_mul]
  linarith [log_two_pos]

theorem fanLogBound_le_of_empty_split {m : ℕ} (hm : 2 ≤ m) {n H M P : ℝ}
    (hn : 0 < n) (hnH : n ≤ H) (hM : 0 < M) (hP : 0 < P) (hPn : P ≤ n)
    (hbal : n * n ≤ ((4 * 2 ^ m : ℕ) : ℝ) * H * M * P) :
    fanLogBound m n H P ≤ Real.log M := by
  have hl := relative_balance_log hn (hn.trans_le hnH) hM hP hn hbal
  have hL : Real.log n - Real.log H ≤ 0 := sub_nonpos.mpr (Real.log_le_log hn hnH)
  have hZ : 0 ≤ Real.log n - Real.log P := sub_nonneg.mpr (Real.log_le_log hP hPn)
  have ha := mul_le_mul_of_nonpos_right (one_le_regularityCost hm) hL
  have hv := mul_le_mul_of_nonneg_right (uniformExponent_le_one (by omega : 0 < m)) hZ
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hc : ((m : ℝ) + 2) * Real.log 2 ≤ 8 * m * Real.log 2 := by
    nlinarith [log_two_pos, mul_nonneg (show (0 : ℝ) ≤ m - 2 by linarith) log_two_pos.le]
  dsimp only [fanLogBound]
  linarith

/-- Quantitative closure of a nonempty split after aggregate pruning. -/
theorem fanLogBound_split {p s : ℕ} (hp : 0 < p) (hs : 0 < s)
    {n H M P P₁ P₂ : ℝ}
    (hn : 0 < n) (hnH : n ≤ H) (hM : 0 < M) (hP : 0 < P) (hPn : P ≤ n)
    (hP₁ : 0 < P₁) (hP₂ : 0 < P₂)
    (hb₁ : n * P₁ ≤ ((4 * 2 ^ (p + s) : ℕ) : ℝ) * H * M * P)
    (hb₂ : n * P₂ ≤ ((4 * 2 ^ (p + s) : ℕ) : ℝ) * H * M * P)
    (hprune : Real.exp (fanLogBound p (n / 2) H P₂) *
      Real.exp (fanLogBound s (n / 2) H P₁) ≤ M) :
    fanLogBound (p + s) n H P ≤ Real.log M := by
  have hH := hn.trans_le hnH
  have hL : Real.log n - Real.log H ≤ 0 := sub_nonpos.mpr (Real.log_le_log hn hnH)
  have hZ : 0 ≤ Real.log n - Real.log P := sub_nonneg.mpr (Real.log_le_log hP hPn)
  let t := uniformExponent p + uniformExponent s
  have ht : 1 ≤ t := one_le_uniformExponent_sum hp hs
  have ht0 : 0 < 1 + t := by linarith
  have hsum : fanLogBound p (n / 2) H P₂ + fanLogBound s (n / 2) H P₁ ≤ Real.log M := by
    apply (Real.le_log_iff_exp_le hM).mpr
    rwa [Real.exp_add]
  have hb₁' := relative_balance_log hn hH hM hP hP₁ hb₁
  have hb₂' := relative_balance_log hn hH hM hP hP₂ hb₂
  have hbp := mul_le_mul_of_nonneg_left hb₂' (uniformExponent_pos hp).le
  have hbs := mul_le_mul_of_nonneg_left hb₁' (uniformExponent_pos hs).le
  rw [fanLogBound, fanLogBound, Real.log_div hn.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hsum
  have hraw :
      -(8 * ((p + s : ℕ) : ℝ) + regularityCost p + regularityCost s +
          (((p + s : ℕ) : ℝ) + 3) * t) * Real.log 2 +
        (regularityCost p + regularityCost s + t) * (Real.log n - Real.log H) +
        t * (Real.log n - Real.log P) ≤ (1 + t) * Real.log M := by
    dsimp only [t]
    push_cast at *
    nlinarith
  have hcost := induction_constant_budget hp hs ht
  have hcost' := mul_le_mul_of_nonneg_right hcost log_two_pos.le
  have hreg : regularityCost p + regularityCost s + t ≤ regularityCost (p + s) * (1 + t) :=
    (div_le_iff₀ ht0).mp (regularityCost_split hp hs ht)
  have hreg' := mul_le_mul_of_nonpos_right hreg hL
  have hexp : uniformExponent (p + s) * (1 + t) ≤ t := by
    apply (le_div_iff₀ ht0).mp
    simpa only [t, add_assoc] using uniformExponent_split hp hs
  have hexp' := mul_le_mul_of_nonneg_right hexp hZ
  have hclosed : (1 + t) * fanLogBound (p + s) n H P ≤ (1 + t) * Real.log M := by
    dsimp only [fanLogBound]
    nlinarith
  exact (mul_le_mul_iff_of_pos_left ht0).mp hclosed

end
end Erdos539Geometry
