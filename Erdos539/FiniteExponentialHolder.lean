/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteProbabilityPush
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators

/-- Finite exponential Holder, with arbitrary dependence across the q classes.
The class moment bounds are the only independence inputs needed by callers. -/
theorem finite_exponential_holder {Ω : Type*} [Fintype Ω] {q : ℕ} (hq : 0 < q)
    (p : Ω → ℝ) (hp : ∀ ω, 0 ≤ p ω) (X : Fin q → Ω → ℝ) (b : Fin q → ℝ)
    (hX : ∀ c, (∑ ω, p ω * Real.exp ((q : ℝ) * X c ω)) ≤ Real.exp (b c)) :
    (∑ ω, p ω * Real.exp (∑ c, X c ω)) ≤ Real.exp ((∑ c, b c) / q) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hw : (∑ _ : Fin q, (1 / (q : ℝ))) = 1 := by simp [hqR.ne']
  have hpoint (ω : Ω) :
      Real.exp ((∑ c, X c ω) - (∑ c, b c) / q) ≤
        ∑ c, (1 / (q : ℝ)) * Real.exp ((q : ℝ) * X c ω - b c) := by
    have h := convexOn_exp.map_sum_le (t := (Finset.univ : Finset (Fin q)))
      (w := fun _ ↦ 1 / (q : ℝ)) (p := fun c ↦ (q : ℝ) * X c ω - b c)
      (fun _ _ ↦ by positivity) hw (fun _ _ ↦ Set.mem_univ _)
    simp only [smul_eq_mul] at h
    have he : (∑ c, (1 / (q : ℝ)) * ((q : ℝ) * X c ω - b c)) =
        (∑ c, X c ω) - (∑ c, b c) / q := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro c _
        field_simp
      · rw [← Finset.mul_sum]
        ring
    rwa [he] at h
  have hcenter : (∑ ω, p ω * Real.exp ((∑ c, X c ω) - (∑ c, b c) / q)) ≤ 1 := by
    calc
      _ ≤ ∑ ω, p ω * ∑ c, (1 / (q : ℝ)) * Real.exp ((q : ℝ) * X c ω - b c) :=
        Finset.sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left (hpoint ω) (hp ω)
      _ = ∑ c, (1 / (q : ℝ)) * (Real.exp (-(b c)) * ∑ ω, p ω * Real.exp ((q : ℝ) * X c ω)) := by
        simp_rw [Finset.mul_sum, Real.exp_sub, div_eq_mul_inv, Real.exp_neg]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro c _
        apply Finset.sum_congr rfl
        intro ω _
        ring
      _ ≤ ∑ _ : Fin q, 1 / (q : ℝ) := by
        apply Finset.sum_le_sum
        intro c _
        have h := mul_le_mul_of_nonneg_left (hX c) (Real.exp_pos (-(b c))).le
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at h
        simpa only [mul_one] using mul_le_mul_of_nonneg_left h (show 0 ≤ 1 / (q : ℝ) by positivity)
      _ = 1 := hw
  simp only [Real.exp_sub, div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul] at hcenter
  rw [← div_eq_mul_inv] at hcenter
  exact (div_le_iff₀ (Real.exp_pos _)).mp hcenter |>.trans_eq (one_mul _)

end
end Erdos539Geometry
