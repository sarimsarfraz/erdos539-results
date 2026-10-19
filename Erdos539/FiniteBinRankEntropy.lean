/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteRankReference
import Erdos539.FiniteProbabilityPush
import Mathlib.Algebra.BigOperators.Fin

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- Entropy decomposed into bin entropy and a power-law rank reference.
The rank only needs to be injective inside each bin. -/
theorem finiteEntropy_le_bin_rank {α β : Type*} [Fintype α] [Fintype β] {N : ℕ}
    (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) (hs : ∑ a, ν a = 1)
    (bin : α → β) (rank : α → Fin N)
    (hinj : Function.Injective (fun a ↦ (bin a, rank a)))
    {s : ℝ} (hs1 : 1 < s) :
    finiteEntropy ν ≤ finiteEntropy (finitePush ν bin) +
      s * (∑ a, ν a * Real.log ((rank a).val + 1)) + Real.log (1 + 1 / (s - 1)) := by
  let p := finitePush ν bin
  let r : Fin N → ℝ := fun k ↦ ((k.val : ℝ) + 1) ^ (-s)
  let w : α → ℝ := fun a ↦ p (bin a) * r (rank a)
  have hp : ∀ b, 0 ≤ p b := finitePush_nonneg ν bin hν
  have hps : ∑ b, p b = 1 := by rw [finitePush_sum, hs]
  have hr : ∀ k, 0 < r k := fun k ↦ Real.rpow_pos_of_pos (by positivity) _
  have hw : ∀ a, 0 ≤ w a := fun a ↦ mul_nonneg (hp _) (hr _).le
  have hpne (a : α) (ha : ν a ≠ 0) : 0 < p (bin a) :=
    (lt_of_le_of_ne (hν a) (Ne.symm ha)).trans_le (le_finitePush ν bin hν a)
  have hwpos (a : α) (ha : ν a ≠ 0) : 0 < w a := mul_pos (hpne a ha) (hr _)
  have hWpos : 0 < ∑ a, w a := by
    have hn : ∃ a, ν a ≠ 0 := by
      by_contra hn
      have hall : ∀ a, ν a = 0 := by simpa using hn
      simp [hall] at hs
    obtain ⟨a, ha⟩ := hn
    exact (hwpos a ha).trans_le (Finset.single_le_sum (fun x _ ↦ hw x) (Finset.mem_univ a))
  have hWle : (∑ a, w a) ≤ 1 + 1 / (s - 1) := by
    have hsum : (∑ a, w a) ≤ ∑ z : β × Fin N, p z.1 * r z.2 := by
      calc
        _ = ∑ z ∈ Finset.univ.image (fun a ↦ (bin a, rank a)), p z.1 * r z.2 :=
          (Finset.sum_image (fun a _ b _ h ↦ hinj h)).symm
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun z _ _ ↦ mul_nonneg (hp _) (hr _).le)
    have he : (∑ z : β × Fin N, p z.1 * r z.2) = ∑ k, r k := by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul, hps, one_mul]
    rw [he] at hsum
    apply hsum.trans
    change (∑ k : Fin N, ((k.val : ℝ) + 1) ^ (-s)) ≤ _
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ ((k : ℝ) + 1) ^ (-s)) N]
    exact finite_rank_reference_sum_le N hs1
  have hg := finiteEntropy_le_log_partition ν w hν hs hw hWpos hwpos
  have hlogW := Real.log_le_log hWpos hWle
  have hlog (a : α) : ν a * Real.log (w a) =
      ν a * Real.log (p (bin a)) - s * (ν a * Real.log ((rank a).val + 1)) := by
    by_cases ha : ν a = 0
    · simp [ha]
    · dsimp only [w, r]
      rw [Real.log_mul (hpne a ha).ne' (hr _).ne', Real.log_rpow (by positivity)]
      ring
  simp only [hlog, Finset.sum_sub_distrib, ← Finset.mul_sum] at hg
  have hpush := finitePush_expectation ν bin (fun b ↦ Real.log (p b))
  change (∑ b, p b * Real.log (p b)) = _ at hpush
  rw [← hpush] at hg
  simp only [finiteEntropy, Real.negMulLog, neg_mul, Finset.sum_neg_distrib] at hg ⊢
  linarith

end
end Erdos539Geometry
