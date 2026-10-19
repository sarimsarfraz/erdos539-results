/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.BernoulliBlockMoments
import Erdos539.FiniteChernoff

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {ι κ : Type*} [Fintype ι]
local instance coloredBernoulliSampleDecidableEq : DecidableEq (ι → Bool) := Classical.decEq _

theorem finite_sum_color_classes {q : ℕ} (D : Finset κ) (c : κ → Fin q) (f : κ → ℝ) :
    (∑ j, ∑ k ∈ D.filter (fun k ↦ c k = j), f k) = ∑ k ∈ D, f k := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/-- The exact product law together with a disjoint-block coloring yields
the exponential moment bound, without independence between color classes. -/
theorem colored_bernoulli_mgf {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    {q : ℕ} (hq : 0 < q) (t : ℝ) (D : Finset κ) (A : κ → Finset ι) (c : κ → Fin q)
    (hc : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → c x = c y → Disjoint (A x) (A y)) :
    (∑ ω, finiteBernoulliWeight α ω * Real.exp (t * ∑ k ∈ D, bernoulliAll (A k) ω)) ≤
      Real.exp (((Real.exp ((q : ℝ) * t) - 1) * ∑ k ∈ D, α ^ (A k).card) / q) := by
  let X : Fin q → (ι → Bool) → ℝ := fun j ω ↦ t * ∑ k ∈ D.filter (fun k ↦ c k = j), bernoulliAll (A k) ω
  let b : Fin q → ℝ := fun j ↦ (Real.exp ((q : ℝ) * t) - 1) * ∑ k ∈ D.filter (fun k ↦ c k = j), α ^ (A k).card
  have hX (j : Fin q) : (∑ ω, finiteBernoulliWeight α ω * Real.exp ((q : ℝ) * X j ω)) ≤ Real.exp (b j) := by
    have hdisj : Set.PairwiseDisjoint (↑(D.filter (fun k ↦ c k = j))) A := by
      intro x hx y hy hxy
      exact hc x (Finset.mem_filter.mp hx).1 y (Finset.mem_filter.mp hy).1 hxy
        ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
    simpa only [X, b, mul_assoc] using
      finiteBernoulli_block_mgf_le hα hα1 ((q : ℝ) * t) (D.filter (fun k ↦ c k = j)) A hdisj
  have h := finite_exponential_holder hq (finiteBernoulliWeight α)
    (finiteBernoulliWeight_nonneg hα hα1) X b hX
  have hXs (ω : ι → Bool) : (∑ j, X j ω) = t * ∑ k ∈ D, bernoulliAll (A k) ω := by
    simp only [X, ← Finset.mul_sum, finite_sum_color_classes]
  have hbs : (∑ j, b j) = (Real.exp ((q : ℝ) * t) - 1) * ∑ k ∈ D, α ^ (A k).card := by
    simp only [b, ← Finset.mul_sum, finite_sum_color_classes]
  simpa only [hXs, hbs] using h

/-- The reflection note's exp(-alpha^4 L/48) tail bound for any actual
four-site tests admitting the verified sixteen-color decomposition. -/
theorem colored_bernoulli_four_site_tail {α L : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (hL : 0 ≤ L)
    (D : Finset κ) (A : κ → Finset ι) (c : κ → Fin 16)
    (hcard : ∀ k ∈ D, (A k).card = 4) (hn : (D.card : ℝ) ≤ L)
    (hc : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → c x = c y → Disjoint (A x) (A y)) :
    (∑ ω ∈ Finset.univ.filter (fun ω ↦ 2 * (α ^ 4 * L) ≤ ∑ k ∈ D, bernoulliAll (A k) ω),
      finiteBernoulliWeight α ω) ≤ Real.exp (-(α ^ 4 * L) / 48) := by
  apply sixteen_color_chernoff (finiteBernoulliWeight α) (finiteBernoulliWeight_nonneg hα hα1)
    (fun ω ↦ ∑ k ∈ D, bernoulliAll (A k) ω) (mul_nonneg (pow_nonneg hα _) hL)
  have h := colored_bernoulli_mgf hα hα1 (by decide : 0 < 16) (Real.log 2 / 16) D A c hc
  have hs : (∑ k ∈ D, α ^ (A k).card) = (D.card : ℝ) * α ^ 4 := by
    rw [Finset.sum_congr rfl (fun k hk ↦ congrArg (fun n ↦ α ^ n) (hcard k hk))]
    simp
  norm_num only [Nat.cast_ofNat, show (16 : ℝ) * (Real.log 2 / 16) = Real.log 2 by ring,
    Real.exp_log (by norm_num : (0 : ℝ) < 2), hs] at h
  apply h.trans
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_right hn (pow_nonneg hα 4)]

end
end Erdos539Geometry
