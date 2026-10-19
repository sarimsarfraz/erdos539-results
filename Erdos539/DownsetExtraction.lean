/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SupportConvolution
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring

namespace Erdos539Geometry
noncomputable section
open scoped Finset BigOperators Pointwise Classical
variable {ι : Type*} [Fintype ι]

/-- The support budget for direct sum doubling. -/
def extractionSupport (σ : ℝ) : ℕ := ⌈Real.log (2 * σ) / Real.log 2⌉₊

theorem extractionSupport_pow_bounds {σ : ℝ} (hσ : 1 ≤ σ) :
    2 * σ ≤ (2 : ℝ) ^ extractionSupport σ ∧
    (16 : ℝ) ^ extractionSupport σ ≤ 256 * σ ^ 4 := by
  have hσpos : 0 < σ := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log (2 * σ) := Real.log_nonneg (by linarith)
  have hratio : 0 ≤ Real.log (2 * σ) / Real.log 2 := div_nonneg hlog hl2.le
  have he : (2 : ℝ) ^ (Real.log (2 * σ) / Real.log 2) = 2 * σ := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    rw [mul_div_cancel₀ _ hl2.ne']
    exact Real.exp_log (by positivity)
  have hlo := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (Nat.le_ceil (Real.log (2 * σ) / Real.log 2))
  rw [he, Real.rpow_natCast] at hlo
  have hhi := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (Nat.ceil_lt_add_one hratio).le
  rw [Real.rpow_natCast, Real.rpow_add (by norm_num), he, Real.rpow_one] at hhi
  have hhi' : (2 : ℝ) ^ extractionSupport σ ≤ 4 * σ := by
    change (2 : ℝ) ^ extractionSupport σ ≤ 2 * σ * 2 at hhi
    nlinarith
  refine ⟨hlo, ?_⟩
  calc
    _ = ((2 : ℝ) ^ extractionSupport σ) ^ 4 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    _ ≤ (4 * σ) ^ 4 := pow_le_pow_left₀ (by positivity) hhi' _
    _ = _ := by ring

/-- A large origin-anchored box exists in any finite downset with small
sum doubling. The point returned is its actual top corner. -/
theorem exists_large_downset_box {A : Finset (ι → ℕ)} (hA : NatDownset A)
    (hne : A.Nonempty) {σ : ℝ} (hσ : 1 ≤ σ)
    (hsum : ((A + A).card : ℝ) ≤ σ * A.card) :
    ∃ a ∈ A, (activeCoordinates a).card ≤ extractionSupport σ ∧
      (A.card : ℝ) / (1024 * σ ^ 5) ≤ boxVolume a := by
  let r := extractionSupport σ
  let E := A.filter (fun a ↦ (activeCoordinates a).card ≤ r)
  have hn : (0 : ℝ) < A.card := by exact_mod_cast hne.card_pos
  have hσpos : 0 < σ := by linarith
  obtain ⟨hpowlo, hpowhi⟩ := extractionSupport_pow_bounds hσ
  have hbudget : 2 * (A + A).card ≤ 2 ^ r * A.card := by
    have hh : (2 : ℝ) * (A + A).card ≤ (2 : ℝ) ^ r * A.card := by
      have hm := mul_le_mul_of_nonneg_right hpowlo hn.le
      nlinarith
    exact_mod_cast hh
  have hhalf : A.card ≤ 2 * E.card := support_trim_half hA r hbudget
  have hE : E.Nonempty := Finset.card_pos.mp (by have := hne.card_pos; omega)
  obtain ⟨a, ha, hmax⟩ := Finset.exists_mem_eq_sup E hE boxVolume
  have hMa : ∀ b ∈ E, (boxVolume b : ℝ) ≤ boxVolume a := by
    intro b hb
    exact_mod_cast (show boxVolume b ≤ boxVolume a from hmax ▸ Finset.le_sup hb)
  have hconv := restricted_support_convolution
    (fun b hb ↦ (Finset.mem_filter.mp hb).2) (Nat.cast_nonneg (boxVolume a)) hMa
  have hEsum : ((E + E).card : ℝ) ≤ (A + A).card := by
    exact_mod_cast Finset.card_le_card (Finset.add_subset_add (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  have hhalf' : (A.card : ℝ) ≤ 2 * E.card := by exact_mod_cast hhalf
  have hmain : (A.card : ℝ) ^ 2 ≤ 4 * 16 ^ r * boxVolume a * σ * A.card := by
    have hm := mul_le_mul_of_nonneg_left (hEsum.trans hsum)
      (show 0 ≤ (16 : ℝ) ^ r * boxVolume a by positivity)
    have he0 : (0 : ℝ) ≤ E.card := Nat.cast_nonneg _
    nlinarith
  have hcancel : (A.card : ℝ) ≤ 4 * 16 ^ r * boxVolume a * σ := by
    exact (mul_le_mul_iff_right₀ hn).mp (by nlinarith)
  have hfinal : (A.card : ℝ) ≤ 1024 * σ ^ 5 * boxVolume a := by
    have hh := mul_le_mul_of_nonneg_right hpowhi
      (show 0 ≤ 4 * (boxVolume a : ℝ) * σ by positivity)
    change (16 : ℝ) ^ r * (4 * (boxVolume a : ℝ) * σ) ≤
      256 * σ ^ 4 * (4 * (boxVolume a : ℝ) * σ) at hh
    nlinarith
  obtain ⟨haA, har⟩ := Finset.mem_filter.mp ha
  refine ⟨a, haA, har, ?_⟩
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < 1024 * σ ^ 5)).mpr (by nlinarith)

end
end Erdos539Geometry
