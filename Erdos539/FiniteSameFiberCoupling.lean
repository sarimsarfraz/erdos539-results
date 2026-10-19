/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteCouplings
import Erdos539.FiniteConditionalLaws

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- Two independent conditional copies given the same actual label.
The label is sampled with its original pushforward mass. -/
def sameFiberCoupling {α β : Type*} [Fintype α] (p : α → ℝ) (φ : α → β) (z : α × α) : ℝ :=
  if φ z.1 = φ z.2 then p z.1 * p z.2 / finitePush p φ (φ z.1) else 0

theorem sameFiberCoupling_nonneg {α β : Type*} [Fintype α]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (φ : α → β) (z : α × α) :
    0 ≤ sameFiberCoupling p φ z := by
  unfold sameFiberCoupling
  split_ifs
  · exact div_nonneg (mul_nonneg (hp _) (hp _)) (finitePush_nonneg p φ hp _)
  · rfl

theorem sameFiberCoupling_symm {α β : Type*} [Fintype α]
    (p : α → ℝ) (φ : α → β) (a b : α) : sameFiberCoupling p φ (a, b) = sameFiberCoupling p φ (b, a) := by
  by_cases h : φ a = φ b
  · simp only [sameFiberCoupling, h, mul_comm]
  · simp only [sameFiberCoupling, if_neg h, if_neg (Ne.symm h)]

theorem sameFiberCoupling_first {α β : Type*} [Fintype α]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (φ : α → β) : finitePush (sameFiberCoupling p φ) Prod.fst = p := by
  funext a
  rw [finitePush_fst]
  have he : (∑ b, sameFiberCoupling p φ (a, b)) = p a / finitePush p φ (φ a) * finitePush p φ (φ a) := by
    conv_rhs => rw [finitePush]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hab : φ a = φ b
    · simp only [sameFiberCoupling, if_pos hab, if_pos hab.symm]
      dsimp only [finitePush]
      ring
    · simp only [sameFiberCoupling, if_neg hab, if_neg (Ne.symm hab), mul_zero]
  rw [he]
  by_cases hm : finitePush p φ (φ a) = 0
  · have ha : p a = 0 := le_antisymm (by simpa only [hm] using le_finitePush p φ hp a) (hp a)
    simp only [ha, zero_div, zero_mul]
  · exact div_mul_cancel₀ (p a) hm

theorem sameFiberCoupling_second {α β : Type*} [Fintype α]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (φ : α → β) : finitePush (sameFiberCoupling p φ) Prod.snd = p := by
  funext b
  rw [finitePush_snd]
  simp_rw [sameFiberCoupling_symm p φ]
  exact (finitePush_fst (sameFiberCoupling p φ) b).symm.trans
    (congrFun (sameFiberCoupling_first p hp φ) b)

theorem sameFiberCoupling_mem {α β : Type*} [Fintype α]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (φ : α → β) : sameFiberCoupling p φ ∈ stationaryCouplings p :=
  ⟨sameFiberCoupling_nonneg p hp φ, sameFiberCoupling_first p hp φ, sameFiberCoupling_second p hp φ⟩

theorem sameFiberCoupling_log_term {α β : Type*} [Fintype α]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (φ : α → β) (z : α × α) :
    sameFiberCoupling p φ z * Real.log (sameFiberCoupling p φ z) = sameFiberCoupling p φ z *
      (Real.log (p z.1) + Real.log (p z.2) - Real.log (finitePush p φ (φ z.1))) := by
  by_cases hz : sameFiberCoupling p φ z = 0
  · simp only [hz, zero_mul]
  have hrel : φ z.1 = φ z.2 := by
    by_contra hn
    exact hz (by simp only [sameFiberCoupling, if_neg hn])
  have hpa : p z.1 ≠ 0 := by
    intro ha
    exact hz (by simp only [sameFiberCoupling, if_pos hrel, ha, zero_mul, zero_div])
  have hpb : p z.2 ≠ 0 := by
    intro hb
    exact hz (by simp only [sameFiberCoupling, if_pos hrel, hb, mul_zero, zero_div])
  have hm : 0 < finitePush p φ (φ z.1) :=
    (lt_of_le_of_ne (hp _) (Ne.symm hpa)).trans_le (le_finitePush p φ hp z.1)
  congr 1
  rw [sameFiberCoupling, if_pos hrel, Real.log_div (mul_ne_zero hpa hpb) hm.ne', Real.log_mul hpa hpb]

/-- Conditional independence has the exact entropy 2H(p)-H(label),
with all zero-mass label fibers included. -/
theorem sameFiberCoupling_entropy {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) (φ : α → β) :
    finiteEntropy (sameFiberCoupling p φ) = 2 * finiteEntropy p - finiteEntropy (finitePush p φ) := by
  have h₁ := finitePush_expectation (sameFiberCoupling p φ) Prod.fst (fun a ↦ Real.log (p a))
  have h₂ := finitePush_expectation (sameFiberCoupling p φ) Prod.snd (fun a ↦ Real.log (p a))
  have h₃ := finitePush_expectation (sameFiberCoupling p φ) Prod.fst (fun a ↦ Real.log (finitePush p φ (φ a)))
  have h₄ := finitePush_expectation p φ (fun b ↦ Real.log (finitePush p φ b))
  rw [sameFiberCoupling_first p hp φ] at h₁ h₃
  rw [sameFiberCoupling_second p hp φ] at h₂
  have he := Finset.sum_congr (s₁ := Finset.univ) rfl (fun z _ ↦ sameFiberCoupling_log_term p hp φ z)
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib] at he
  rw [← h₁, ← h₂, ← h₃, ← h₄] at he
  simp only [finiteEntropy, Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
  linarith

end
end Erdos539Geometry
