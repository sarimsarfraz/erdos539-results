/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.RationalSidonSums
import Mathlib.Analysis.MeanInequalities

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators

/-- Holder aggregation with the rational exponents from the integer
Sidon certificate. All masses may be zero. -/
theorem rational_component_holder {ι : Type*} [Fintype ι]
    (p σ : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hσ : ∀ i, 0 ≤ σ i) (hs : ∑ i, p i = 1) :
    (∑ i, (σ i ^ (1 / 4 : ℝ) * p i ^ (1 / 2 : ℝ)) ^ (20 / 13 : ℝ)) ^ (13 / 5 : ℝ) ≤
      (∑ i, σ i ^ (5 / 3 : ℝ)) ^ (3 / 5 : ℝ) := by
  have hpq : Real.HolderConjugate (13 / 10) (13 / 3) := ⟨by norm_num, by norm_num, by norm_num⟩
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ)
    (f := fun i ↦ p i ^ (10 / 13 : ℝ)) (g := fun i ↦ σ i ^ (5 / 13 : ℝ)) hpq
    (fun i _ ↦ Real.rpow_nonneg (hp i) _) (fun i _ ↦ Real.rpow_nonneg (hσ i) _)
  have hpe (i : ι) : (p i ^ (10 / 13 : ℝ)) ^ (13 / 10 : ℝ) = p i := by
    rw [← Real.rpow_mul (hp i)]; norm_num
  have hσe (i : ι) : (σ i ^ (5 / 13 : ℝ)) ^ (13 / 3 : ℝ) = σ i ^ (5 / 3 : ℝ) := by
    rw [← Real.rpow_mul (hσ i)]; norm_num
  simp only [hpe, hσe, hs, Real.one_rpow, one_mul] at h
  norm_num at h
  have hterm (i : ι) : (σ i ^ (1 / 4 : ℝ) * p i ^ (1 / 2 : ℝ)) ^ (20 / 13 : ℝ) =
      p i ^ (10 / 13 : ℝ) * σ i ^ (5 / 13 : ℝ) := by
    rw [Real.mul_rpow (Real.rpow_nonneg (hσ i) _) (Real.rpow_nonneg (hp i) _),
      ← Real.rpow_mul (hσ i), ← Real.rpow_mul (hp i)]
    norm_num
    ring
  simp_rw [hterm]
  have hlhs : 0 ≤ ∑ i, p i ^ (10 / 13 : ℝ) * σ i ^ (5 / 13 : ℝ) :=
    Finset.sum_nonneg (fun i _ ↦ mul_nonneg (Real.rpow_nonneg (hp i) _) (Real.rpow_nonneg (hσ i) _))
  have hsum : 0 ≤ ∑ i, σ i ^ (5 / 3 : ℝ) :=
    Finset.sum_nonneg (fun i _ ↦ Real.rpow_nonneg (hσ i) _)
  have hpow := Real.rpow_le_rpow hlhs h (by norm_num : (0 : ℝ) ≤ 13 / 5)
  rw [← Real.rpow_mul hsum] at hpow
  norm_num at hpow
  exact hpow

end
end Erdos539Geometry
