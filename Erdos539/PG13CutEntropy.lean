/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13VisibleWeight
import Erdos539.PG13MaskCard
import Erdos539.PG13UnionFans

namespace Erdos539Geometry
noncomputable section
open scoped Classical

/-- Actual projection entropy of the uniform law on the integer union. -/
def pg13ProjectionEntropy (T : ℕ) (I : Finset (Fin 13)) : ℝ :=
  finiteEntropy (finitePush (uniformReference (pg13Union T))
    (imageEndpoint (pg13Union T) (fun x (j : I) ↦ x j.val)))

theorem pg13VisibleWeight_cut (I : Finset (Fin 13)) :
    56 ≤ max (pg13VisibleWeight I) (pg13VisibleWeight Iᶜ) := by
  have h := pg13_all_cut_weight (pg13SetMask I)
  have hc := pg13VisibleWeight_mask (pg13ComplementMask (pg13SetMask I))
  rw [pg13MaskSet_complement, pg13MaskSet_setMask] at hc
  change pg13VisibleWeight Iᶜ = pg13MaskWeight (pg13MaskComplement (pg13SetMask I).val) at hc
  rwa [← pg13VisibleWeight_setMask I, ← hc] at h

/-- The stronger value 56 comes from the checked pairings of the thirteen
lines, now linked to the actual projection laws. -/
theorem pg13Union_cut_entropy {T : ℕ} (hT : 0 < T) (I : Finset (Fin 13)) :
    (56 / 13 : ℝ) * Real.log (T : ℝ) ≤
      max (pg13ProjectionEntropy T I) (pg13ProjectionEntropy T Iᶜ) := by
  have hlog : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg (by exact_mod_cast hT)
  have hI := pg13Union_projection_entropy hT I
  have hJ := pg13Union_projection_entropy hT Iᶜ
  have hw := pg13VisibleWeight_cut I
  by_cases hi : 56 ≤ pg13VisibleWeight I
  · have hwi : (56 : ℝ) ≤ pg13VisibleWeight I := by exact_mod_cast hi
    exact le_max_of_le_left ((mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hwi (by norm_num : (0 : ℝ) ≤ 13)) hlog).trans hI)
  · have hj : 56 ≤ pg13VisibleWeight Iᶜ := by omega
    have hwj : (56 : ℝ) ≤ pg13VisibleWeight Iᶜ := by exact_mod_cast hj
    exact le_max_of_le_right ((mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hwj (by norm_num : (0 : ℝ) ≤ 13)) hlog).trans hJ)

theorem pg13Union_log_maxFan_le {T : ℕ} (hT : 2 ≤ T) :
    Real.log (maxFan (integerRealSet (pg13Union T)) : ℝ) ≤
      Real.log 11 + 4 * Real.log (T : ℝ) := by
  have hp : 0 < T := by omega
  have hm := one_le_maxFan (integerRealSet_nonempty (pg13Union_nonempty hp))
  have hm' : (0 : ℝ) < maxFan (integerRealSet (pg13Union T)) := by exact_mod_cast hm
  have hbound : (maxFan (integerRealSet (pg13Union T)) : ℝ) ≤ 11 * (T : ℝ) ^ 4 := by
    exact_mod_cast pg13Union_maxFan_le hT
  have ht : (0 : ℝ) < T := by exact_mod_cast hp
  have h := Real.log_le_log hm' hbound
  rw [Real.log_mul (by norm_num) (pow_pos ht 4).ne', Real.log_pow] at h
  simpa using h

/-- A quantitative obstruction for every actual coordinate cut, including
the empty and full cuts. It concerns maximum anchored fans. -/
theorem pg13_unretained_entropy_gap {T : ℕ} (hT : 2 ≤ T) (I : Finset (Fin 13)) :
    (4 / 13 : ℝ) * Real.log (T : ℝ) - Real.log 11 ≤
      max (pg13ProjectionEntropy T I) (pg13ProjectionEntropy T Iᶜ) -
        Real.log (maxFan (integerRealSet (pg13Union T)) : ℝ) := by
  have h := pg13Union_cut_entropy (by omega : 0 < T) I
  have hf := pg13Union_log_maxFan_le hT
  linarith

/-- No dimension-only additive constant repairs the unretained cut bound. -/
theorem pg13_unretained_gap_unbounded (R : ℝ) :
    ∃ T : ℕ, 2 ≤ T ∧ ∀ I : Finset (Fin 13),
      R < max (pg13ProjectionEntropy T I) (pg13ProjectionEntropy T Iᶜ) -
        Real.log (maxFan (integerRealSet (pg13Union T)) : ℝ) := by
  obtain ⟨T, hT⟩ := exists_nat_gt (max 2 (Real.exp ((13 / 4 : ℝ) * (R + Real.log 11))))
  have ht2 : (2 : ℝ) < T := (le_max_left _ _).trans_lt hT
  have ht : 2 ≤ T := by exact_mod_cast ht2.le
  have hlog := Real.log_lt_log (Real.exp_pos _) ((le_max_right _ _).trans_lt hT)
  rw [Real.log_exp] at hlog
  have hg : R < (4 / 13 : ℝ) * Real.log (T : ℝ) - Real.log 11 := by linarith
  exact ⟨T, ht, fun I ↦ hg.trans_le (pg13_unretained_entropy_gap ht I)⟩

end
end Erdos539Geometry
