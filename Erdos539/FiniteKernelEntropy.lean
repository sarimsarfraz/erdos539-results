/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.FiniteConditioning
import Erdos539.FiniteEntropyMixtures

namespace Erdos539Geometry
noncomputable section
open scoped BigOperators Classical

/-- A finite stochastic transition with normalized nonnegative rows. -/
structure FiniteMarkovKernel (α β : Type*) [Fintype β] where
  weight : α → β → ℝ
  nonneg : ∀ a b, 0 ≤ weight a b
  sum_one : ∀ a, ∑ b, weight a b = 1

namespace FiniteMarkovKernel
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

/-- The literal joint law of an input and its stochastic output. -/
def joint (k : FiniteMarkovKernel α β) (ν : α → ℝ) (z : α × β) : ℝ :=
  ν z.1 * k.weight z.1 z.2

omit [Fintype α] in
theorem joint_nonneg (k : FiniteMarkovKernel α β) (ν : α → ℝ) (hν : ∀ a, 0 ≤ ν a) :
    ∀ z, 0 ≤ k.joint ν z := fun z ↦ mul_nonneg (hν z.1) (k.nonneg z.1 z.2)

theorem joint_fst (k : FiniteMarkovKernel α β) (ν : α → ℝ) : finitePush (k.joint ν) Prod.fst = ν := by
  funext a
  rw [finitePush_fst]
  simp only [joint, ← Finset.mul_sum, k.sum_one, mul_one]

theorem joint_sum (k : FiniteMarkovKernel α β) (ν : α → ℝ) :
    (∑ z, k.joint ν z) = ∑ a, ν a := by rw [← finitePush_sum _ Prod.fst, joint_fst]

theorem joint_entropy (k : FiniteMarkovKernel α β) (ν : α → ℝ) :
    finiteEntropy (k.joint ν) = finiteEntropy ν + ∑ a, ν a * finiteEntropy (k.weight a) :=
  finiteEntropy_rows ν k.weight k.sum_one

/-- Map the stochastic output, using a map allowed to depend on the input. -/
def mapOutput (k : FiniteMarkovKernel α β) (f : α → β → γ) : FiniteMarkovKernel α γ where
  weight a := finitePush (k.weight a) (f a)
  nonneg a := finitePush_nonneg _ _ (k.nonneg a)
  sum_one a := by rw [finitePush_sum, k.sum_one]

/-- Literal equality between mapping the joint law and mapping every row. -/
theorem joint_mapOutput (k : FiniteMarkovKernel α β) (ν : α → ℝ) (f : α → β → γ) :
    finitePush (k.joint ν) (fun z ↦ (z.1, f z.1 z.2)) = (k.mapOutput f).joint ν := by
  funext z
  obtain ⟨a, c⟩ := z
  rw [finitePush, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · simp only [Prod.mk.injEq, true_and, joint, mapOutput, finitePush, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> simp
  · intro x _ hxa
    apply Finset.sum_eq_zero
    intro b _
    simp [hxa]
  · simp

/-- Retaining only a function of the old input cannot reduce the new
conditional output entropy below its actual row average. This is the
information inequality used at each step of the coordinate sweep. -/
theorem output_entropy_increment (k : FiniteMarkovKernel α β) (ν : α → ℝ)
    (hν : ∀ a, 0 ≤ ν a) (f : α → γ) :
    finiteEntropy (finitePush ν f) + (∑ a, ν a * finiteEntropy (k.weight a)) ≤
      finiteEntropy (finitePush (k.joint ν) (fun z ↦ (f z.1, z.2))) := by
  let r := k.joint ν
  let q := finitePush r Prod.swap
  let o := finitePush r (fun z ↦ (f z.1, z.2))
  have hq : ∀ z, 0 ≤ q z := finitePush_nonneg r Prod.swap (k.joint_nonneg ν hν)
  have hqH : finiteEntropy q = finiteEntropy r :=
    finiteEntropy_push_eq_of_support_injective r Prod.swap (fun a b _ _ he ↦ Prod.swap_injective he)
  have hqsnd : finitePush q Prod.snd = ν := by rw [finitePush_comp]; exact k.joint_fst ν
  have hmap : finitePush q (mapSecond f) = finitePush o Prod.swap := by
    rw [finitePush_comp, finitePush_comp]
    rfl
  have hoH : finiteEntropy (finitePush o Prod.swap) = finiteEntropy o :=
    finiteEntropy_push_eq_of_support_injective o Prod.swap (fun a b _ _ he ↦ Prod.swap_injective he)
  have h := finite_conditionalEntropy_map_condition q hq f
  rw [hqH, hqsnd, hmap, hoH, k.joint_entropy ν] at h
  change finiteEntropy (finitePush ν f) + _ ≤ finiteEntropy o
  linarith

/-- Composition is performed inside the same finite project and retains
literal nonnegative transition probabilities. -/
def comp (k : FiniteMarkovKernel α β) (l : FiniteMarkovKernel β γ) : FiniteMarkovKernel α γ where
  weight a c := ∑ b, k.weight a b * l.weight b c
  nonneg a c := Finset.sum_nonneg (fun b _ ↦ mul_nonneg (k.nonneg a b) (l.nonneg b c))
  sum_one a := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, l.sum_one, mul_one, k.sum_one]

/-- Exact stationarity, expressed as equality of the actual target marginal. -/
def Preserves (k : FiniteMarkovKernel α α) (ν : α → ℝ) : Prop :=
  finitePush (k.joint ν) Prod.snd = ν

theorem comp_preserves (k l : FiniteMarkovKernel α α) (ν : α → ℝ)
    (hk : k.Preserves ν) (hl : l.Preserves ν) : (k.comp l).Preserves ν := by
  funext c
  rw [finitePush_snd]
  change (∑ a, ν a * ∑ b, k.weight a b * l.weight b c) = ν c
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul]
  have hk' (b : α) : (∑ a, ν a * k.weight a b) = ν b := by
    have he := congrFun hk b
    rw [finitePush_snd] at he
    exact he
  simp_rw [hk']
  have he := congrFun hl c
  rw [finitePush_snd] at he
  exact he

end FiniteMarkovKernel
end
end Erdos539Geometry
