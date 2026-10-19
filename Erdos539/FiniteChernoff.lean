/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteExponentialHolder
import Erdos539.RationalLogCertificate

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

theorem finite_exponential_markov {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (X : Ω → ℝ) {t : ℝ} (ht : 0 ≤ t) (a b : ℝ)
    (hX : (∑ ω, p ω * Real.exp (t * X ω)) ≤ Real.exp b) :
    (∑ ω ∈ Finset.univ.filter (fun ω ↦ a ≤ X ω), p ω) ≤ Real.exp (b - t * a) := by
  have h : (∑ ω ∈ Finset.univ.filter (fun ω ↦ a ≤ X ω), p ω) * Real.exp (t * a) ≤ Real.exp b := by
    calc
      _ = ∑ ω ∈ Finset.univ.filter (fun ω ↦ a ≤ X ω), p ω * Real.exp (t * a) := Finset.sum_mul _ _ _
      _ ≤ ∑ ω ∈ Finset.univ.filter (fun ω ↦ a ≤ X ω), p ω * Real.exp (t * X ω) := by
        apply Finset.sum_le_sum
        intro ω hω
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hω).2 ht)) (hp ω)
      _ ≤ ∑ ω, p ω * Real.exp (t * X ω) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun ω _ _ ↦ mul_nonneg (hp ω) (Real.exp_pos _).le)
      _ ≤ _ := hX
  rw [Real.exp_sub]
  exact (le_div_iff₀ (Real.exp_pos _)).mpr h

/-- The explicit sixteen-color Chernoff exponent in the reflection note. -/
theorem sixteen_color_chernoff {Ω : Type*} [Fintype Ω]
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (V : Ω → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hV : (∑ ω, p ω * Real.exp ((Real.log 2 / 16) * V ω)) ≤ Real.exp (a / 16)) :
    (∑ ω ∈ Finset.univ.filter (fun ω ↦ 2 * a ≤ V ω), p ω) ≤ Real.exp (-a / 48) := by
  have ht : 0 ≤ Real.log 2 / 16 := by positivity
  have h := finite_exponential_markov p hp V ht (2 * a) (a / 16) hV
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hlog : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [rational_log_two_bounds.1]
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hlog)]

end
end Erdos539Geometry
