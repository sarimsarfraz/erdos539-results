/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteBernoulliLaw

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {ι κ : Type*} [Fintype ι]
local instance blockBernoulliSampleDecidableEq : DecidableEq (ι → Bool) := Classical.decEq _

/-- Joint moments of all-selected indicators on disjoint site blocks. -/
theorem finiteBernoulli_block_moment (α : ℝ) (D : Finset κ) (A : κ → Finset ι)
    (hA : Set.PairwiseDisjoint (↑D) A) :
    (∑ ω, finiteBernoulliWeight α ω * ∏ k ∈ D, bernoulliAll (A k) ω) =
      ∏ k ∈ D, α ^ (A k).card := by
  have hprod (ω : ι → Bool) : (∏ k ∈ D, bernoulliAll (A k) ω) = bernoulliAll (D.biUnion A) ω := by
    exact (Finset.prod_biUnion hA).symm
  simp_rw [hprod]
  rw [finiteBernoulli_all_expectation, Finset.card_biUnion hA]
  exact (Finset.prod_pow_eq_pow_sum D (fun k ↦ (A k).card) α).symm

/-- Independence here is proved by expanding products over subsets, using
the actual product law and pairwise disjoint original coordinate blocks. -/
theorem finiteBernoulli_block_product (α : ℝ) (D : Finset κ) (A : κ → Finset ι)
    (hA : Set.PairwiseDisjoint (↑D) A) (c : κ → ℝ) :
    (∑ ω, finiteBernoulliWeight α ω * ∏ k ∈ D, (1 + c k * bernoulliAll (A k) ω)) =
      ∏ k ∈ D, (1 + c k * α ^ (A k).card) := by
  simp_rw [Finset.prod_one_add, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro B hB
  have hBD := Finset.mem_powerset.mp hB
  have hdisj : Set.PairwiseDisjoint (↑B) A := fun i hi j hj hij ↦ hA (hBD hi) (hBD hj) hij
  simp_rw [Finset.prod_mul_distrib]
  calc
    _ = (∏ k ∈ B, c k) * ∑ ω, finiteBernoulliWeight α ω * ∏ k ∈ B, bernoulliAll (A k) ω := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ = _ := by rw [finiteBernoulli_block_moment α B A hdisj]

theorem finiteBernoulli_block_mgf (α t : ℝ) (D : Finset κ) (A : κ → Finset ι)
    (hA : Set.PairwiseDisjoint (↑D) A) :
    (∑ ω, finiteBernoulliWeight α ω * Real.exp (t * ∑ k ∈ D, bernoulliAll (A k) ω)) =
      ∏ k ∈ D, (1 + (Real.exp t - 1) * α ^ (A k).card) := by
  have he (ω : ι → Bool) : Real.exp (t * ∑ k ∈ D, bernoulliAll (A k) ω) =
      ∏ k ∈ D, (1 + (Real.exp t - 1) * bernoulliAll (A k) ω) := by
    rw [Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro k _
    rcases bernoulliAll_zero_or_one (A k) ω with h | h <;> rw [h] <;> simp
  simp_rw [he]
  exact finiteBernoulli_block_product α D A hA _

theorem finiteBernoulli_block_mgf_le {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (t : ℝ) (D : Finset κ) (A : κ → Finset ι) (hA : Set.PairwiseDisjoint (↑D) A) :
    (∑ ω, finiteBernoulliWeight α ω * Real.exp (t * ∑ k ∈ D, bernoulliAll (A k) ω)) ≤
      Real.exp ((Real.exp t - 1) * ∑ k ∈ D, α ^ (A k).card) := by
  rw [finiteBernoulli_block_mgf α t D A hA, Finset.mul_sum, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro k _
    have hpow0 : 0 ≤ α ^ (A k).card := pow_nonneg hα _
    have hpow1 : α ^ (A k).card ≤ 1 := pow_le_one₀ hα hα1
    nlinarith [mul_nonneg (Real.exp_pos t).le hpow0]
  · intro k _
    exact (by linarith [Real.add_one_le_exp ((Real.exp t - 1) * α ^ (A k).card)])

end
end Erdos539Geometry
