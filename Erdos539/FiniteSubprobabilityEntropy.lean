/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.WeightedGibbsEntropy
import Erdos539.FiniteConditionalLaws

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

theorem finiteRelEntropy_subprob_nonneg {α : Type*} [Fintype α] (p q : α → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ x, 0 ≤ q x)
    (hps : ∑ x, p x = 1) (hqs : ∑ x, q x ≤ 1)
    (hsupport : ∀ x, p x ≠ 0 → 0 < q x) : 0 ≤ finiteRelEntropy p q := by
  have h := finite_log_sum p q hp hq hsupport
  rw [hps, Real.log_one, zero_sub, one_mul] at h
  exact (neg_nonneg.mpr (Real.log_nonpos (Finset.sum_nonneg (fun x _ ↦ hq x)) hqs)).trans h

/-- A fiberwise upper bound for an unnormalized reference partition gives
an entropy bound conditional on the actual image law. Zero image masses
are allowed, and no normalized conditional comparison is assumed. -/
theorem finiteEntropy_fiber_partition_bound {α β : Type*} [Fintype α] [Fintype β]
    (p w : α → ℝ) (f : α → β) (B : β → ℝ)
    (hp : ∀ x, 0 ≤ p x) (hps : ∑ x, p x = 1) (hw : ∀ x, 0 ≤ w x)
    (hB : ∀ y, 0 < B y) (hsupport : ∀ x, p x ≠ 0 → 0 < w x)
    (hpartition : ∀ y, finitePush w f y ≤ B y) :
    finiteEntropy p ≤ finiteEntropy (finitePush p f) +
      (∑ y, finitePush p f y * Real.log (B y)) - ∑ x, p x * Real.log (w x) := by
  let q := fun x ↦ finitePush p f (f x) * w x / B (f x)
  have hq : ∀ x, 0 ≤ q x := fun x ↦
    div_nonneg (mul_nonneg (finitePush_nonneg p f hp _) (hw x)) (hB _).le
  have hqs : ∑ x, q x ≤ 1 := by
    rw [← Fintype.sum_fiberwise f q, ← hps, ← finitePush_sum p f]
    apply Finset.sum_le_sum
    intro y _
    have he : (∑ x : {x // f x = y}, q x.val) =
        finitePush p f y * (finitePush w f y / B y) := by
      calc
        _ = ∑ x : {x // f x = y}, finitePush p f y * w x.val / B y := by
          apply Finset.sum_congr rfl
          intro x _
          dsimp only [q]
          rw [x.property]
        _ = _ := by
          simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Finset.mul_sum,
            ← finitePush_eq_sum_fiber]
          ring
    rw [he]
    have h := (div_le_one (hB y)).mpr (hpartition y)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left h (finitePush_nonneg p f hp y)
  have hsup : ∀ x, p x ≠ 0 → 0 < q x := by
    intro x hx
    exact div_pos (mul_pos ((lt_of_le_of_ne (hp x) (Ne.symm hx)).trans_le
      (le_finitePush p f hp x)) (hsupport x hx)) (hB _)
  have h := finiteRelEntropy_subprob_nonneg p q hp hq hps hqs hsup
  have hpoint (x : α) : p x * Real.log (q x) =
      p x * Real.log (finitePush p f (f x)) + p x * Real.log (w x) - p x * Real.log (B (f x)) := by
    by_cases hx : p x = 0
    · simp [hx]
    have hm := (lt_of_le_of_ne (hp x) (Ne.symm hx)).trans_le (le_finitePush p f hp x)
    simp only [q, Real.log_div (mul_pos hm (hsupport x hx)).ne' (hB _).ne',
      Real.log_mul hm.ne' (hsupport x hx).ne']
    ring
  rw [finiteRelEntropy_eq_entropy_cross] at h
  simp_rw [hpoint] at h
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib] at h
  rw [← finitePush_expectation p f (fun y ↦ Real.log (finitePush p f y)),
    ← finitePush_expectation p f (fun y ↦ Real.log (B y))] at h
  have he : (∑ y, finitePush p f y * Real.log (finitePush p f y)) =
      -finiteEntropy (finitePush p f) := by
    simp only [finiteEntropy, Real.negMulLog, neg_mul, Finset.sum_neg_distrib, neg_neg]
  rw [he] at h
  linarith

end
end Erdos539Geometry
