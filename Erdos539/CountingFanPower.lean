/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.CountingFanBound
import Erdos539.FanPowerSum

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {ι : Type*}
local instance countingFanPowerDecidableEq : DecidableEq (ι → ℝ) := Classical.decEq _

theorem counting_fanPowerSum_le {S : Finset (ι → ℝ)} {M p : ℝ} (hp : 0 < p)
    (hM : ∀ a : S, ((fan S a.val).card : ℝ) ≤ M) :
    fanPowerSum (positiveDifferenceChannel S) (fun _ ↦ 1) (fun _ ↦ 1) p ≤
      (S.card : ℝ) * (Real.sqrt M) ^ p := by
  unfold fanPowerSum
  simp only [one_mul, channelWeightRatio_one, channelOutputs_positiveDifference, fanOutputs_card]
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset S)) (fun a _ ↦
    Real.rpow_le_rpow (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt (hM a)) hp.le)
  simpa using h

/-- The counting weights give ||sqrt(R_1)||_p^4 <= N^(4/p) M^2. -/
theorem counting_fanPowerNorm_le {S : Finset (ι → ℝ)} (hS : S.Nonempty) {M p : ℝ}
    (hp : 0 < p) (hM0 : 0 ≤ M) (hM : ∀ a : S, ((fan S a.val).card : ℝ) ≤ M) :
    (fanPowerSum (positiveDifferenceChannel S) (fun _ ↦ 1) (fun _ ↦ 1) p) ^ (4 / p) ≤
      (S.card : ℝ) ^ (4 / p) * M ^ 2 := by
  letI : Nonempty S := hS.coe_sort
  have hW := fanPowerSum_pos (positiveDifferenceChannel S) (fun _ ↦ 1) (fun _ ↦ 1)
    (fun _ ↦ by norm_num) (fun _ ↦ by norm_num) p
  have h := Real.rpow_le_rpow hW.le (counting_fanPowerSum_le hp hM) (show 0 ≤ 4 / p by positivity)
  have he : ((Real.sqrt M) ^ p) ^ (4 / p) = M ^ 2 := by
    rw [← Real.rpow_mul (Real.sqrt_nonneg M), show p * (4 / p) = (4 : ℕ) by field_simp; norm_num,
      Real.rpow_natCast, show (4 : ℕ) = 2 * 2 by decide, pow_mul, Real.sq_sqrt hM0]
  rwa [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _), he] at h

end
end Erdos539Geometry
