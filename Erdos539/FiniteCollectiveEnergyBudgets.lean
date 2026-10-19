/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteLogJensen

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators
variable {α : Type*} [Fintype α] [Nonempty α]

/-- Jensen turns the collective fourth-power energy bound into a mean
ordinary-energy defect bound, with the size-biased fiber probabilities. -/
theorem finite_collective_log_budget (n E : α → ℝ) (hn : ∀ y, 0 < n y) (hE : ∀ y, 0 < E y)
    {N r : ℝ} (hN : 0 < N) (hs : ∑ y, n y = N) (hc : (∑ y, n y ^ 4 / E y) ≤ r) :
    (∑ y, n y / N * Real.log (n y ^ 3 / E y)) ≤ Real.log (r / N) := by
  have hp : ∀ y, 0 ≤ n y / N := fun y ↦ (div_pos (hn y) hN).le
  have hsum : ∑ y, n y / N = 1 := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul, hs, mul_inv_cancel₀ hN.ne']
  have h := finite_log_jensen (fun y ↦ n y / N) (fun y ↦ n y ^ 3 / E y) hp hsum
    (fun y ↦ div_pos (pow_pos (hn y) 3) (hE y))
  have he : (∑ y, n y / N * (n y ^ 3 / E y)) = (∑ y, n y ^ 4 / E y) / N := by
    simp only [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [he] at h
  apply h.trans
  apply Real.log_le_log
  · exact div_pos (Finset.sum_pos (fun y _ ↦ div_pos (pow_pos (hn y) 4) (hE y)) Finset.univ_nonempty) hN
  · exact div_le_div_of_nonneg_right hc hN.le

/-- A second Cauchy--Schwarz step gives the collective reflected-support
size before the sign-cell loss. -/
theorem finite_collective_inverse_budget (n E : α → ℝ) (hn : ∀ y, 0 < n y) (hE : ∀ y, 0 < E y)
    {N r : ℝ} (hs : ∑ y, n y = N) (hc : (∑ y, n y ^ 4 / E y) ≤ r) :
    N ^ 2 / r ≤ ∑ y, E y / n y ^ 2 := by
  have hg : ∀ y, 0 < n y ^ 4 / E y := fun y ↦ div_pos (pow_pos (hn y) 4) (hE y)
  have hsum := Finset.sum_pos (fun y (_ : y ∈ Finset.univ) ↦ hg y) Finset.univ_nonempty
  have h := Finset.sq_sum_div_le_sum_sq_div Finset.univ n (fun y _ ↦ hg y)
  rw [hs] at h
  have he (y : α) : n y ^ 2 / (n y ^ 4 / E y) = E y / n y ^ 2 := by
    field_simp [(hn y).ne']
  simp_rw [he] at h
  exact (div_le_div_of_nonneg_left (sq_nonneg N) hsum hc).trans h

end
end Erdos539Geometry
