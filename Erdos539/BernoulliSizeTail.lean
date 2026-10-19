/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.BernoulliBlockMoments
import Erdos539.FiniteChernoff

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
variable {ι : Type*} [Fintype ι]
local instance sizeBernoulliSampleDecidableEq : DecidableEq (ι → Bool) := Classical.decEq _

def bernoulliCount (ω : ι → Bool) : ℝ := ∑ i, bernoulliAll {i} ω

theorem bernoulliCount_mgf {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (t : ℝ) :
    (∑ ω : ι → Bool, finiteBernoulliWeight α ω * Real.exp (t * bernoulliCount ω)) ≤
      Real.exp ((Real.exp t - 1) * ((Fintype.card ι : ℝ) * α)) := by
  have hd : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) (fun i ↦ ({i} : Finset ι)) := by
    intro i _ j _ hij
    simpa using hij
  simpa only [bernoulliCount, Finset.card_singleton, pow_one, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] using finiteBernoulli_block_mgf_le hα hα1 t Finset.univ (fun i : ι ↦ {i}) hd

theorem bernoulliCount_upper_tail {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    (∑ ω ∈ Finset.univ.filter (fun ω : ι → Bool ↦
      2 * ((Fintype.card ι : ℝ) * α) ≤ bernoulliCount ω), finiteBernoulliWeight α ω) ≤
      Real.exp (-((Fintype.card ι : ℝ) * α) / 12) := by
  let μ : ℝ := (Fintype.card ι : ℝ) * α
  have hμ : 0 ≤ μ := mul_nonneg (Nat.cast_nonneg _) hα
  have hM : (∑ ω : ι → Bool, finiteBernoulliWeight α ω * Real.exp (Real.log 2 * bernoulliCount ω)) ≤ Real.exp μ := by
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2), sub_self, show (2 : ℝ) - 1 = 1 by norm_num, one_mul]
      using bernoulliCount_mgf hα hα1 (Real.log 2)
  have h := finite_exponential_markov (finiteBernoulliWeight α) (finiteBernoulliWeight_nonneg hα hα1)
    bernoulliCount (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) (2 * μ) μ hM
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hlog : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [rational_log_two_bounds.1]
  nlinarith [mul_nonneg hμ (sub_nonneg.mpr hlog)]

theorem bernoulliCount_lower_tail {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    (∑ ω ∈ Finset.univ.filter (fun ω : ι → Bool ↦
      bernoulliCount ω ≤ ((Fintype.card ι : ℝ) * α) / 2), finiteBernoulliWeight α ω) ≤
      Real.exp (-((Fintype.card ι : ℝ) * α) / 12) := by
  let μ : ℝ := (Fintype.card ι : ℝ) * α
  have hμ : 0 ≤ μ := mul_nonneg (Nat.cast_nonneg _) hα
  have he : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
  have hM : (∑ ω : ι → Bool, finiteBernoulliWeight α ω * Real.exp (Real.log 2 * (-bernoulliCount ω))) ≤ Real.exp (-μ / 2) := by
    have h := bernoulliCount_mgf (ι := ι) hα hα1 (-Real.log 2)
    rw [he] at h
    have hb : ((1 / 2 : ℝ) - 1) * ((Fintype.card ι : ℝ) * α) = -μ / 2 := by dsimp [μ]; ring
    simpa only [hb, neg_mul, mul_neg] using h
  have h := finite_exponential_markov (finiteBernoulliWeight α) (finiteBernoulliWeight_nonneg hα hα1)
    (fun ω : ι → Bool ↦ -bernoulliCount ω) (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) (-μ / 2) (-μ / 2) hM
  have hf : (Finset.univ.filter (fun ω : ι → Bool ↦ -μ / 2 ≤ -bernoulliCount ω)) =
      Finset.univ.filter (fun ω : ι → Bool ↦ bernoulliCount ω ≤ μ / 2) := by
    ext ω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro hh <;> linarith
  rw [hf] at h
  apply h.trans
  apply Real.exp_le_exp.mpr
  have hlog : Real.log 2 ≤ (5 / 6 : ℝ) := by linarith [rational_log_two_bounds.2]
  nlinarith [mul_nonneg hμ (sub_nonneg.mpr hlog)]

end
end Erdos539Geometry
