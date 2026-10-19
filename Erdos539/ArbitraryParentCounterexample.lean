/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.RowPointRetentionFailure
import Erdos539.IntervalEnergyBounds

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Pointwise Classical

theorem scalarInterval_zero_mem {n : ℕ} (hn : 0 < n) : (0 : ℤ) ∈ scalarInterval n := by
  simp [scalarInterval, hn]

theorem scalarInterval_normalized_energy_gt_twentyfive {n : ℕ} (hn : 38 ≤ n) :
    25 < countingEnergy (scalarInterval n) / ((scalarInterval n).card : ℝ) ^ 2 := by
  have hn0 : 0 < n := by omega
  rw [← uniformEnergyWeight_energy, uniformEnergyWeight_scalarInterval hn0]
  have hn' : (38 : ℝ) ≤ n := by exact_mod_cast hn
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 3 * n)).mpr
  nlinarith [sq_nonneg ((n : ℝ) - 38)]

/-- Every interval length at least 38 gives the exact source-note failure,
using its actual half-row/half-point reference and literal fibers. -/
theorem interval_row_point_retention_failure {n : ℕ} (hn : 38 ≤ n) :
    weightedEnergy ((rowPointSupport (scalarInterval n)).image Prod.snd)
      (extendWeight ((rowPointSupport (scalarInterval n)).image Prod.snd)
        (fun y ↦ Real.sqrt (finitePush (rowPointReference (scalarInterval n))
          (imageEndpoint (rowPointSupport (scalarInterval n)) Prod.snd) y))) *
      (∏ y, imageConditionalEnergy (rowPointSupport (scalarInterval n)) Prod.snd
        (rowPointReference (scalarInterval n)) y ^
          finitePush (rowPointReference (scalarInterval n))
            (imageEndpoint (rowPointSupport (scalarInterval n)) Prod.snd) y) <
      weightedEnergy (rowPointSupport (scalarInterval n))
        (extendWeight (rowPointSupport (scalarInterval n))
          (fun x ↦ Real.sqrt (rowPointReference (scalarInterval n) x))) := by
  exact rowPointReference_retention_failure (scalarInterval n)
    (scalarInterval_zero_mem (by omega)) (scalarInterval_normalized_energy_gt_twentyfive hn)

/-- An admissible nonnegative unit parent weight refutes the raw-energy
version of retention when the exact-maximizer hypothesis is dropped. -/
theorem arbitrary_parent_retention_counterexample :
    ∃ (S : Finset (ℤ × ℤ)) (f : S → ℝ), f ∈ admissibleWeights S ∧
      weightedEnergy (S.image Prod.snd)
        (extendWeight (S.image Prod.snd)
          (fun y ↦ Real.sqrt (finitePush (fun x ↦ f x ^ 2) (imageEndpoint S Prod.snd) y))) *
        (∏ y, imageConditionalEnergy S Prod.snd (fun x ↦ f x ^ 2) y ^
          finitePush (fun x ↦ f x ^ 2) (imageEndpoint S Prod.snd) y) <
        weightedEnergy S (extendWeight S f) := by
  refine ⟨rowPointSupport (scalarInterval 38),
    fun x ↦ Real.sqrt (rowPointReference (scalarInterval 38) x),
    rowPointReference_admissible _ (scalarInterval_zero_mem (by norm_num)), ?_⟩
  simp_rw [Real.sq_sqrt (rowPointReference_nonneg _ _)]
  exact interval_row_point_retention_failure (by norm_num : 38 ≤ 38)

end
end Erdos539Geometry
