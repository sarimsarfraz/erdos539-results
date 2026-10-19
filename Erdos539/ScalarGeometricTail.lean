/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ScalarEndpointEstimates
import Mathlib.Algebra.BigOperators.Intervals

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

theorem geometric_tail_index_bound {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (N i : ℕ) :
    (∑ j ∈ Finset.range N, if i < j then r ^ (j - i) else 0) ≤ r / (1 - r) := by
  rw [← Finset.sum_filter]
  have he : (Finset.range N).filter (fun j ↦ i < j) = Finset.Ico (i + 1) N := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [he, Finset.sum_Ico_eq_sum_range]
  have hx (k : ℕ) : i + 1 + k - i = k + 1 := by omega
  simp only [hx]
  exact positive_geometric_sum_le hr hr1 _

/-- The exact exponential form of the finite geometric-tail bound. -/
theorem exponential_tail_index_bound {t : ℝ} (ht : 0 < t) (N i : ℕ) :
    (∑ j ∈ Finset.range N, if i < j then Real.exp (-t * ((j : ℝ) - i)) else 0) ≤
      1 / (Real.exp t - 1) := by
  let r := Real.exp (-t)
  have hr : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    dsimp [r]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have he : (∑ j ∈ Finset.range N, if i < j then Real.exp (-t * ((j : ℝ) - i)) else 0) =
      ∑ j ∈ Finset.range N, if i < j then r ^ (j - i) else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i < j
    · simp only [if_pos hij]
      dsimp only [r]
      rw [← Real.exp_nat_mul, Nat.cast_sub hij.le]
      congr 1
      ring
    · simp [hij]
  rw [he]
  have h := geometric_tail_index_bound hr.le hr1 N i
  have hidentity : r / (1 - r) = 1 / (Real.exp t - 1) := by
    have hexp : r * Real.exp t = 1 := by
      dsimp [r]
      rw [← Real.exp_add]
      simp
    have hd : Real.exp t - 1 ≠ 0 := ne_of_gt (by
      have hp := Real.one_lt_exp_iff.mpr ht
      linarith)
    apply (div_eq_div_iff (by linarith : 1 - r ≠ 0) hd).mpr
    nlinarith
  rwa [hidentity] at h

end
end Erdos539Geometry
