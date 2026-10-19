/-
Copyright 2026 Sarim Sarfraz
SPDX-License-Identifier: Apache-2.0
-/
import Erdos539.ReflectionSampling
import Erdos539.FiniteAvoidance

namespace Erdos539Geometry
noncomputable section
open scoped Classical BigOperators
local instance simultaneousReflectionIntegerDecidableEq : DecidableEq ℤ := Classical.decEq _
local instance simultaneousReflectionIndexDecidableEq (I : Finset ℤ) : DecidableEq I := Classical.decEq _
local instance simultaneousReflectionSampleDecidableEq (I : Finset ℤ) : DecidableEq (I → Bool) := Classical.decEq _

/-- A single literal sample has the desired size and controls every test
center in W, whenever the explicit union bound is below one. -/
theorem exists_simultaneous_reflection_sample (I W : Finset ℤ) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hfailure : 2 * Real.exp (-((I.card : ℝ) * α) / 12) +
      (W.card : ℝ) ^ 2 * Real.exp (-(α ^ 4 * I.card) / 48) < 1) :
    ∃ ω : I → Bool, (I.card : ℝ) * α / 2 ≤ ((bernoulliSelection I ω).card : ℝ) ∧
      ((bernoulliSelection I ω).card : ℝ) ≤ 2 * ((I.card : ℝ) * α) ∧
      ∀ w ∈ W, ∀ z ∈ W, reflectionGoodCount I w z ω < 2 * (α ^ 4 * I.card) := by
  let μ : ℝ := (I.card : ℝ) * α
  let a : ℝ := α ^ 4 * I.card
  let bad : Bool ⊕ (W × W) → (I → Bool) → Prop
    | .inl false, ω => bernoulliCount ω ≤ μ / 2
    | .inl true, ω => 2 * μ ≤ bernoulliCount ω
    | .inr j, ω => 2 * a ≤ reflectionGoodCount I j.1.val j.2.val ω
  let B : Bool ⊕ (W × W) → ℝ
    | .inl _ => Real.exp (-μ / 12)
    | .inr _ => Real.exp (-a / 48)
  have hB (j : Bool ⊕ (W × W)) :
      (∑ ω ∈ Finset.univ.filter (bad j), finiteBernoulliWeight α ω) ≤ B j := by
    rcases j with b | j
    · cases b
      · simpa only [Fintype.card_coe] using bernoulliCount_lower_tail (ι := I) hα hα1
      · simpa only [Fintype.card_coe] using bernoulliCount_upper_tail (ι := I) hα hα1
    · exact reflectionGoodCount_tail I j.1.val j.2.val hα hα1
  have hbs : (∑ j, B j) = 2 * Real.exp (-μ / 12) + (W.card : ℝ) ^ 2 * Real.exp (-a / 48) := by
    simp [B, Fintype.sum_sum_type, Fintype.card_prod, pow_two]
  have hb : (∑ j, ∑ ω ∈ Finset.univ.filter (bad j), finiteBernoulliWeight α ω) < 1 :=
    (Finset.sum_le_sum (fun j _ ↦ hB j)).trans_lt (hbs.trans_lt hfailure)
  obtain ⟨ω, hω⟩ := finite_avoidance (finiteBernoulliWeight α)
    (finiteBernoulliWeight_nonneg hα hα1) (finiteBernoulliWeight_sum α) bad hb
  refine ⟨ω, ?_, ?_, ?_⟩
  · rw [bernoulliSelection_card]
    exact (lt_of_not_ge (hω (.inl false))).le
  · rw [bernoulliSelection_card]
    exact (lt_of_not_ge (hω (.inl true))).le
  · intro w hw z hz
    exact lt_of_not_ge (hω (.inr (⟨w, hw⟩, ⟨z, hz⟩)))

end
end Erdos539Geometry
