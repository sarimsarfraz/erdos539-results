/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.SharpSidonSums
import Erdos539.SharpSeparatedExponents
import Mathlib.Analysis.MeanInequalities

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators

/-- Holder aggregation for the exact sharp logarithmic exponent,
including zero component masses and zero component norms. -/
theorem sharp_component_holder {ι : Type*} [Fintype ι]
    (p σ : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hσ : ∀ i, 0 ≤ σ i) (hs : ∑ i, p i = 1) :
    (∑ i, (σ i ^ (1 / 4 : ℝ) * p i ^ (1 / 2 : ℝ)) ^ (4 / sharpSidonExponent)) ^ sharpSidonExponent ≤
      (∑ i, σ i ^ sharpSeparatedExponent) ^ (sharpSidonExponent - 2) := by
  have hg := sharpSidonExponent_strict_bounds
  have hgpos : 0 < sharpSidonExponent := by linarith
  have hgne := hgpos.ne'
  have hdpos : 0 < sharpSidonExponent - 2 := by linarith
  have hdne := hdpos.ne'
  have hpq : Real.HolderConjugate (sharpSidonExponent / 2)
      (sharpSidonExponent / (sharpSidonExponent - 2)) := by
    refine ⟨?_, by positivity, by positivity⟩
    field_simp
    ring
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ)
    (f := fun i ↦ p i ^ (2 / sharpSidonExponent))
    (g := fun i ↦ σ i ^ (1 / sharpSidonExponent)) hpq
    (fun i _ ↦ Real.rpow_nonneg (hp i) _) (fun i _ ↦ Real.rpow_nonneg (hσ i) _)
  have he1 : (2 / sharpSidonExponent) * (sharpSidonExponent / 2) = 1 := by field_simp
  have he2 : (1 / sharpSidonExponent) * (sharpSidonExponent / (sharpSidonExponent - 2)) =
      sharpSeparatedExponent := by unfold sharpSeparatedExponent; field_simp
  have hpe (i : ι) : (p i ^ (2 / sharpSidonExponent)) ^ (sharpSidonExponent / 2) = p i := by
    rw [← Real.rpow_mul (hp i), he1, Real.rpow_one]
  have hσe (i : ι) : (σ i ^ (1 / sharpSidonExponent)) ^ (sharpSidonExponent / (sharpSidonExponent - 2)) =
      σ i ^ sharpSeparatedExponent := by rw [← Real.rpow_mul (hσ i), he2]
  simp only [hpe, hσe, hs, Real.one_rpow, one_mul] at h
  have hterm (i : ι) : (σ i ^ (1 / 4 : ℝ) * p i ^ (1 / 2 : ℝ)) ^ (4 / sharpSidonExponent) =
      p i ^ (2 / sharpSidonExponent) * σ i ^ (1 / sharpSidonExponent) := by
    rw [Real.mul_rpow (Real.rpow_nonneg (hσ i) _) (Real.rpow_nonneg (hp i) _),
      ← Real.rpow_mul (hσ i), ← Real.rpow_mul (hp i)]
    have hquarter : (1 / 4 : ℝ) * (4 / sharpSidonExponent) = 1 / sharpSidonExponent := by ring
    have hhalf : (1 / 2 : ℝ) * (4 / sharpSidonExponent) = 2 / sharpSidonExponent := by ring
    rw [hquarter, hhalf, mul_comm]
  simp_rw [hterm]
  have hlhs : 0 ≤ ∑ i, p i ^ (2 / sharpSidonExponent) * σ i ^ (1 / sharpSidonExponent) :=
    Finset.sum_nonneg (fun i _ ↦ mul_nonneg (Real.rpow_nonneg (hp i) _) (Real.rpow_nonneg (hσ i) _))
  have hsum : 0 ≤ ∑ i, σ i ^ sharpSeparatedExponent :=
    Finset.sum_nonneg (fun i _ ↦ Real.rpow_nonneg (hσ i) _)
  have hpow := Real.rpow_le_rpow hlhs h hgpos.le
  rw [← Real.rpow_mul hsum] at hpow
  have he3 : (1 / (sharpSidonExponent / (sharpSidonExponent - 2))) * sharpSidonExponent =
      sharpSidonExponent - 2 := by field_simp
  rwa [he3] at hpow

end
end Erdos539Geometry
