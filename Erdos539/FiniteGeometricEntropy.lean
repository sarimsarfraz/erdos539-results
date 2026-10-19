/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteGibbs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- Entropy of a finitely supported nonnegative integer law is bounded
by its mean, with the endpoint of mean zero included. -/
theorem finiteEntropy_nat_mean_le {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hs : ∑ k, p k = 1)
    {M : ℝ} (hM : 0 ≤ M) (hmean : (∑ k, p k * (k.val : ℝ)) ≤ M) :
    finiteEntropy p ≤ Real.log (M + 1) + 1 := by
  have hN : 0 < N := by
    by_contra hn
    have hN0 : N = 0 := by omega
    subst N
    simp at hs
  by_cases hM0 : M = 0
  · subst M
    let z : Fin N := ⟨0, hN⟩
    have hzero : ∀ k : Fin N, k ≠ z → p k = 0 := by
      intro k hk
      have hval : 0 < (k.val : ℝ) := by
        have hn : k.val ≠ 0 := by intro hz; apply hk; exact Fin.ext hz
        exact_mod_cast Nat.pos_of_ne_zero hn
      have hle := Finset.single_le_sum (s := Finset.univ)
        (f := fun k : Fin N ↦ p k * (k.val : ℝ))
        (fun k _ ↦ mul_nonneg (hp k) (Nat.cast_nonneg _)) (Finset.mem_univ k)
      have hm : p k * (k.val : ℝ) = 0 := le_antisymm (hle.trans hmean) (mul_nonneg (hp k) hval.le)
      exact (mul_eq_zero.mp hm).resolve_right hval.ne'
    have hpz : p z = 1 := by
      rw [Finset.sum_eq_single z (fun k _ hk ↦ hzero k hk) (by simp)] at hs
      exact hs
    have hH : finiteEntropy p = 0 := by
      unfold finiteEntropy
      rw [Finset.sum_eq_single z]
      · simp [hpz]
      · intro k _ hk
        simp [hzero k hk]
      · simp
    simp [hH]
  have hMp : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
  have hM1 : 0 < M + 1 := by linarith
  let q := M / (M + 1)
  have hq : 0 < q := div_pos hMp hM1
  have hq1 : q < 1 := (div_lt_one hM1).mpr (by linarith)
  let w : Fin N → ℝ := fun k ↦ (1 - q) * q ^ k.val
  have hw : ∀ k, 0 < w k := fun k ↦ mul_pos (sub_pos.mpr hq1) (pow_pos hq _)
  have hWpos : 0 < ∑ k, w k := by
    exact Finset.sum_pos (fun k _ ↦ hw k) ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  have hWle : (∑ k, w k) ≤ 1 := by
    have he := geom_sum_mul_neg q N
    have he' : (∑ k, w k) = 1 - q ^ N := by
      simp only [w, ← Finset.mul_sum]
      rw [Fin.sum_univ_eq_sum_range]
      nlinarith
    rw [he']
    have := pow_nonneg hq.le N
    linarith
  have hg := finiteEntropy_le_log_partition p w hp hs (fun k ↦ (hw k).le) hWpos (fun k _ ↦ hw k)
  have hlogW : Real.log (∑ k, w k) ≤ 0 := Real.log_nonpos hWpos.le hWle
  have hqeq : 1 - q = 1 / (M + 1) := by dsimp [q]; field_simp; ring
  have hlog (k : Fin N) : Real.log (w k) = -Real.log (M + 1) +
      (k.val : ℝ) * (Real.log M - Real.log (M + 1)) := by
    rw [show w k = (1 - q) * q ^ k.val from rfl,
      Real.log_mul (sub_pos.mpr hq1).ne' (pow_ne_zero _ hq.ne'), Real.log_pow, hqeq,
      one_div, Real.log_inv]
    dsimp [q]
    rw [Real.log_div hMp.ne' hM1.ne']
  simp only [hlog, mul_add, Finset.sum_add_distrib, ← mul_assoc, ← Finset.sum_mul, hs, one_mul] at hg
  let D := Real.log (M + 1) - Real.log M
  have hD : 0 ≤ D := sub_nonneg.mpr (Real.log_le_log hMp (by linarith))
  have hMD : M * D ≤ 1 := by
    have hl := Real.log_le_sub_one_of_pos (div_pos hM1 hMp)
    rw [Real.log_div hM1.ne' hMp.ne'] at hl
    have hm := mul_le_mul_of_nonneg_left hl hM
    have he : M * ((M + 1) / M - 1) = 1 := by field_simp; ring
    rw [he] at hm
    exact hm
  have hm := mul_le_mul_of_nonneg_right hmean hD
  dsimp [D] at hm hMD
  nlinarith

end
end Erdos539Geometry
