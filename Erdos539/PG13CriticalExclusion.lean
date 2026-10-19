/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.PG13HeavyBranch
import Erdos539.CriticalCoreMass

namespace Erdos539Geometry
noncomputable section
open scoped Classical
local instance : DecidableEq (Fin 13 → ℝ) := Classical.decEq _

theorem pg13_critical_size_bound {T : ℕ} (hT : 0 < T) {b : ℝ} (hb : 0 < b)
    {S : Finset (Fin 13 → ℝ)} {I : Finset (Fin 13)}
    (h : IsProjectionCriticalCore S b I (integerRealSet (pg13Union T))) :
    (T : ℝ) ^ 2 * (1 / 13 : ℝ) ^ (1 + 1 / b) ≤ 41 := by
  obtain ⟨f, hf, hs, hE⟩ := energyNorm_attained h.nonempty
  obtain ⟨l, hl⟩ := pg13_exists_heavy_branch hT ⟨hf, hs⟩
  have hcrit := h.subset_mass_bound hb ⟨hf, hs⟩ hE
    (pg13Branch_real_nonempty hT l) (pg13Branch_real_subset T l)
  have hc : 0 ≤ (1 / 13 : ℝ) ^ (1 + 1 / b) := Real.rpow_nonneg (by norm_num) _
  have hpow := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1 / 13) hl
    (by positivity : (0 : ℝ) ≤ 1 + 1 / b)
  have hq : (T : ℝ) ^ 6 ≤ (posDiff (integerRealSet (pg13Union T))).card := by
    exact_mod_cast pg13Union_real_palette_lower hT
  have hC : ((posDiff (integerRealSet (pg13Branch T l))).card : ℝ) ≤ 41 * (T : ℝ) ^ 4 := by
    exact_mod_cast pg13Branch_real_palette hT l
  have hbnd : (T : ℝ) ^ 6 * (1 / 13 : ℝ) ^ (1 + 1 / b) ≤ 41 * (T : ℝ) ^ 4 :=
    (mul_le_mul_of_nonneg_right hq hc).trans
      ((mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg _)).trans (hcrit.trans hC))
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  apply (mul_le_mul_iff_right₀ (pow_pos ht 4)).mp
  convert hbnd using 1 <;> ring

/-- For each fixed positive normalization parameter, all sufficiently
large members lie outside the actual projection-critical-core class. -/
theorem pg13_eventually_not_critical {b : ℝ} (hb : 0 < b) :
    ∃ N : ℕ, ∀ T : ℕ, N ≤ T → ∀ (S : Finset (Fin 13 → ℝ)) (I : Finset (Fin 13)),
      ¬ IsProjectionCriticalCore S b I (integerRealSet (pg13Union T)) := by
  let c : ℝ := (1 / 13 : ℝ) ^ (1 + 1 / b)
  have hc : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (41 / c))
  refine ⟨N, ?_⟩
  intro T hNT S I hcrit
  have hle : (N : ℝ) ≤ T := by exact_mod_cast hNT
  have ht1 : (1 : ℝ) < T := ((le_max_left _ _).trans_lt hN).trans_le hle
  have htc : 41 < (T : ℝ) * c := by
    have hh := ((le_max_right _ _).trans_lt hN).trans_le hle
    exact (div_lt_iff₀ hc).mp hh
  have ht : 0 < T := by exact_mod_cast (lt_trans zero_lt_one ht1)
  have hbound := pg13_critical_size_bound ht hb hcrit
  change (T : ℝ) ^ 2 * c ≤ 41 at hbound
  have hp : 0 ≤ ((T : ℝ) ^ 2 - T) * c := mul_nonneg (by nlinarith) hc.le
  nlinarith

end
end Erdos539Geometry
